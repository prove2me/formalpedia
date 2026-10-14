-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3595
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:12.008129+00:00
-- url     : https://prove2.me/submissions/1a75dfdf-fe41-4d6a-b412-1944a57a5c8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 646402877 ≤ n < 646582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 646404127 1250 646402877 646402903
    0x11030c06040e0c0919090911220b011806020601081c020d050c0a1502120601090b070201050d11190201240e040f150b12010216140c030d05040602 64
    0x145054500540040e002c200100110402100458074110f940c458041d45511400740507080148a601d40381d48038001c148000c02910088404000c5c100e8078144298049003003120030001c18010302d0000340742c0020700a29009581000030030b038060303442005d502c110b42e405803680d0b070060081d80d07041c01c3d800c5d4076100031000031900c0c8000489002d807906401003880c0642c64003516100340c1d1484c00841e418a8040000d1008100c009956100d0764000d10076409800c0d04508408800c407551034220044556141502800c0010b1008000e00750040d80198002c120140007030b100030034004820b40b4000802e030450650082c10210f1088400034084d420311070a40c1e581007140d040c007400d44070102c1e511034000850040701c211003020002301d001d0000f0110814a0268400440000ea41850702d015000c2c08417056420f005100d543c000200006d418000c1d1141291261860b00f0482070070745410b900301c405c8400000003409031b070b55050160788090000c400c0007803698841c1c80d82c691034080024a44a03140e550b0b9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 646405377 1250 646404127 646404139
    0x7080f03070f12181401120501030203060613140103030509010f110606120c090702030c0c04090b0609040206040b030a021305011704110303040801021201090606090305071a1611030c 80
    0x80000c0e03081a55500e201d030080f4080020548204050b90442c24a0944001c0703041201000a9003884902c18021282d00030781e1000031244a443c4c507142039030760038000254150070460005020382040019029003100e80d05020880d843e19500c501c4551740700303800540008000103800003079940c1050b002d80402600d441c04550119110150540307a020160525100b00c82541141c0b40c941d10811400401000041c4089034608110340042e5507039009241503260340c00340c50300340344040c40e1920441c403125400c0b03a6403921039a2050200400824002d00880e131110043c0008100c080200340a503100e407401072401a5241038075082000146100c0c1d100034100012490038400781e040c0141c3c120303003041e4081d082c1c0e58540c810380300190030b6001e0350b040000b05600c04220b021741400b85260b00341c1221900780c020001d003a02c50008640c90707961400b0140c165802500208100d11801105040508100c4619410031502c503480d4400d004980106079040f0068041d40200c600e000c5c480310220309411540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 646406627 1250 646405377 646405387
    0x300c100509060103030f36060816020a060b0a03050a060f0f050103030522120b0411150f0309010207060501150f02010506011209080403020603040311070911180d0c060207080f03 78
    0x8040030141800982004200340204042402c3d82e146107800188426201c2a004030721f20410300c1d548154441d0900040d00b060204e901c881c40000c2041c00c911603070380074000c0e030955920b4210107496a11805504590341c1040000402ca050007000c0282d44180b0001c2a03052840c0c08907021754100c0b2608000181c40d100c0100002504941100ca0b103d000705ca070612054030300041000c007820191f0003d240b60b0000c400003001c10421181e030307900c114450100c0d506010300d14024404105008806121000300410406e8892511a0055644611401d0001d882c1c001c1c642e40d501e059440aa1101d00300c014080d07528102c80f900b081006e0741120b92840204254508a400205502030303840ca00d144240c0d441d409202884490310441c0c0c0590340141103555642000d14004001e00f002107040007241c021104045960346071030240e5030302c0030041d44400b810f020404900c1034880382011011a0320640c0145e4a200242d080407604000701300355005000d41a1604040a040c00c00319000c0d1421a001000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 646407877 1250 646406627 646406633
    0x30718060e1c14060a02090102070801150b030a0f020d090201021b060d0908041706090f12030f070201090501060609140a050a0e06121b1c05300c100509060103 70
    0x8104002100a502c00d420304401d507061403100f07032001516060240c0a003a040110510145d0004d10007045c023a8212014241c1d1490158200c0d003008621107400d8013042c0040106541541c0030703540007001c1d410001500c1c1c402e0702c4070788202e178801483c240890352076407220f01c150f6805003c0c0d4010b040281e1520110844020009521841020b07038004e041540c0320039000a01240c04140c0d4050011080da8200406089580c1940c4203001c480c0760310107210300002c401d4001d01c00b0500050f08003410822500b542c8a0340d0f40705944040043c00d58046650340c120030004203800340501c000404080d11200162414103002440078010740c500d460080d044804c08001644502e2691803c590b40e01026a40e01e450b01e80020341e1645800d402d04850388920010341c81400851030341c080c0d068804403401035a003016460601540505100042c1c0140c000201c101381d900d5021031079040d0200f50700d1b12041c65100e1100360560303039042680900c1d1a90701010108070380c50110310800d900101940020409503156036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 646409127 1250 646407877 646407889
    0xc0302031306111303060b120307050c0915101107091a09040206091801090c030903230c010c0509031b03120a050912060609070813110d0503030718060e 67
    0x40c00070a40c0e036882051141030810070080d2041d00039040c1800300c2d40741e980d041c610080c0082000c040d128070806403400e523203500c0000840d11103e90120140c078508400030300f0800001c03002884c0345555100c2226006107552400401c0c20110310640360705003001040100e95161007191741040c01280d2508041c0b000c0c40100c507040c0515410102c90101c0641d4403840030030010f003d10002d044c0c02003020440204174619010016040e140038000800045900c2c2074220709032002c042001e004180d08602c4814500c0c14101d08542540a148400d0302e849a002e00031401c4400302100c840c001200841c00828034074080c0145004103a085001c4c140c2841d040000a807a403c3e014400800361200183c902c0d6840e000f0303070680b00c0744103000349090605200c010b01d07180c55210855480c1d101c1c04000d400200d0060044140300d015001007c1410070804036039645200c89109081002e0780320400584a5001542c00c10095200e402c45649956201c01a0101c0c03100710840740d04007400344602d18150301c10760b0b1140c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 646410377 1250 646409127 646409161
    0x207140a0306050421020f12040f030602030403030e032706191d0a0303050306040b0a0b03060f0402280807021b0f1903030203092805122503060c030203 67
    0x1400c00906611103190413042511121210325401031817034904d02c441900412900340400082d0103a8141a0490030280c1c40b07031040c1e00844c000c500c00c242061010810a80c091076016109040001e041d010602d50f89155030801103c8001000906001c120000d190003101011f600c4203032151030801468502072101c044080d140001044482548142608401085015058006409140c403503450f41001815580301f2104e0501035410f0138007100450a2046003041140c0c02105194207580f40d6034208002251014a40341d4026024401c1c0b441a448102c60b0410b02c5081007120500000d03000c1010b400c85400501038000d64211001c41c40c50f941c0c00590700c07040c25408032107805007440c01d480007620311a845680e40b000c011520302c010003010740000061500030b0003101c54000c50b507a92559445040c40040c039450040b000301500700401d061003400b07800c541c1c11600503158000e449041036010510f120440070030304a0405330410512101c0d100c0c01b132812042c3e00c0e081d4075503d8140400c40d504081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 646411627 1250 646410377 646410383
    0x1b0301080c040b150c06070905010810031401111903050f040804032d060b01030501080102040f0b0304060207081207080a1404141002040b0c010e0304030320120403120207140a03 78
    0x2200f00444141d42c4d161504200070321010b00d10358032448421456540c07201c1c21100000851b800c807a0200d841c1d805070071414070a804491184c0191030441e69440c500c00f504860120b0503640303903554680c0d51007000c0003610010324078841d0010000346000c0010250790000d054008075910001c1480049080c550407142a69040240c107868040c03d40061660700072030f00c3c000742034410030074a46020469140c20405511009907001d200b1039803103401d10b900f02d1085100361030104151403030401107058a039010711b1380940504801800d0804a80368246c0ca903100c4222044503005000800c01e0094010b05619000803040c07104002401041c00c01c1314140c0001303040645050030203039030541c60440c03c01045107100c002c0141035443e280e44465981094200100d106c0c025400c00007020340b02d41700001990210f80e050760f40d80010f0401c003140e00c0f6012481007080082401005100c0f0729181d94017006000541c49030003c5a00c5c034011410090070205150011010030340c02507419004c59441d00b498100f030f250 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 646412877 1250 646411627 646411631
    0x10609180b01210b0f090c070321020403080c10140c181309050f01020f1c060519170706090611010902030a0305030108070b04050d06020f160b1b0301080c04 69
    0x82440d0050700ca50840d0320a1070700d0861a0542c1c0d0100b0fa515030002c100702441a40e840010300300500030421200c3c422918200c03401018081c40d40131a01c00c400001e00c20703840d49207665820030b90302c002200781d07809a001035403025400100c003410900204159007102a40ca1020402149141c0c40501900805401600303090f4000c00c140410350741c040c4125050410040c4446800d0307118180e205d001e8817040340d003500d05026500f444841c004042c000c440688041d0640c1720310740f002035100500249203010301880840d0380c0d030902050544503050340071038004040f0403091181d440c00d070291940e410100300702c8006400648007005200c2d0001201d030251a21030801603282c030610761055005103010040a580341c0b140342c0c800c105050b0400000c40c1a1784542d000d4a240036101d0303550580f148681c1c030a454008050b03d00c01404520f01d54098000c03400300016113032038082c00d07214010400c00e003030800ba45d0700e01c08a03040c8200c00340c200c0c24418141c034112030700030706540c5094001d036143d4201a0165006039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 646414127 1250 646412877 646412891
    0x1020a060e03090409050138040519090803180a02090403050f0903010609020711010519081003051b120109020604230a0b03150f09041202032502030601060918 70
    0x1110502c02c0e03450600014200b086040360381d0034450b007e019901c42201c00741054100c0a85030002541107030b040c0d42601c035041001400740300180402801e00407c076464102060034481c49440c090f02270f0700503445c02501401d440341421144100006116001002183c0c80f09071007800503100c0d850440e43c440d07014101103482e15034103848a01c540c03203501d050503419480d01d2000300e00348c03429030b020b03000007401190500c14440300300e00103542c0b074030806112020324010242980b10003842509225800103484c0c6184402e0307079032076031200e10740060002500c05084a01301d5440745802c0c03290f541d4104000c000d00034040308416801040c5a07200d107006010283c80e1000008600c850880c00001c00544068513009145540e08407407142c1c1d4006503141111580080c3c00c41c201c900d02000441d400a40090901c0c81d9a111941d54140c580360002114055000501110040d41000b07d1a0081464820703c03100845031184101410504e050304004280000910144920340a505203c4d00088560b50005100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 646415377 1250 646414127 646414151
    0x30c06050306220f020c1005011a0304110d021002150603160905060a05031c141e071103060115090b040e041709031f0b010201050906060f190306020406020706020a0201020a06 77
    0x113440041c0b01860f1840c0000b0790100501400102e0440403059181c0401050340c0310031403540181c1c4055071340c03030070024184049000306904a960304542d541c020305540c21104617501081450540c41d01240258000000c07105070320300760840703c6034850421406000c18040281d184940c0c40040d0103080841a661030005a20b40c48030030b18140503100c000c1c211614620520305241c001611502008002200d012204203c80280425a081b2280c50809080040c0074540700c040d650300b2400064030b6047c1041014400e544041c002c1d03601800441222410750070344075030007070200c0b1015800f035074105000300010484d00903040c496a4005a001003455885406c48503d6030b12805903030071065141c0075202411031200004c0c03a80f030301c20403000355040c00319011080059080710740c07c543c40101030300712000007115854000f01c3c0b1501500002e0a01d152003d801300390f4000384080e0340040303401a03400101401056010030000c8014002c1c0d100502d000481c42d80000e4440c400c00b500100015103621345041a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 646416627 1250 646415377 646415381
    0xd0c02070906030804050a060c03020601120f0f0c080c010e034812010207120e0d0c080607020c0d03090905070e0306100f06090f170703050313030c0605030622 70
    0x209441071051004540b641008902c80e4800c0c07245521440150380700260f4a800f0748050005a0380540151449a2070120b24031413031102e1a0040320881c0e0152511030001f0707a03414210f0340c001e0083c0d038010049070418024600e444080501c0c54188101904901c0d02c41d9030000c0c1150600d00c0d0006004001c4461140c0090300f000540071184941d141c0e142c1142c0040100800c1e42a02c140840b09942500c580c04002ca00700d10941002802403404403035a41c120741c1c090502d0b01039100f000340034500021101d44400b001c840c1c0ca500304070f5031074018a05000702298100701440d8844000c0f5400321504001ea6005001000c2c1c2c4d2082c04034076521346002480150280400306040080941038070300620340402080c000f20b0307050140c4009648105004100a40300e0300030001a200b088401c81220307408e00e00311114a4220294031115882180000305c00201c0c24005082ca161466220143d00d50071841c0142845000b44c220200300300d0140104890382e501c04481503c00303010340204074100107000e500c20f80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 646417877 1250 646416627 646416629
    0x1e080c060c0601050f0303071a0915070f030b12011404020a080304120b04060207140c010909060506070f080705070612050c0304230715020a03080603010e03091e04050c03090f0a080d0c0207 83
    0xb008280d520742427800fa0030b5101c8180e10a01e40207051314825217001b0b0000c8406e000982d864070014030040c241c01c002c00c2c0603a00c0408440e1008210b19882c04509004a003510001c4d8a00c03030403442090305010071802c1084282e409008240003a5061504059448903191a4060f0282c0780d90902c101040600690340d04540c1001d8008a40d01e68012085102a9641210038000c0780001c2d02001c0024a50550340314039819100d0007008d6a246c200b0030748807072158001c03910050f500e81c1410480d000001d03004200140060030715413500810035121400b01002c84100034080c594940c0308004201c0019080b804090141c030200c100000c071010023018107441e1218580100c065030910344104520a40c00080d0074450038425603c2d19026510756041c14240c0f0b0680c3d02030502e41d80b0610a041492400b00c040031500756403881603440914403140000c0c1aa001526140a00729000050041300f5074140149040340740503100600d0503411b9542c0318007186c450300e2400e00c4400c0d59004840151031003442070130 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 646419127 1250 646417877 646417883
    0x81b0705030f120a06060f0e0a0803031006140703020604060e030c01241e090903020f010507090501090506070f1106041206020c061e070f091e080c060c0601050f030307 74
    0x380c54991001100c41c10341c2c840d503583c944a4142e03d002901c451018050003060701d5050741c0d8404008640013090b1010040b01d18140d612030a50040440c111204102841c4511015040e0807401c0d490840040c250503c00312031201180000c021100110f03400151842e0001c3d800840066896030440c0403030700b18094011191a40c0d4200401490340c6161544800e4030043c0d810b401641c103503a40c02280c0011086041c15400580140b5000c022100251f4000400c0d54080e0050700c0c4010300c0005001d0841c0d9040318a003000c911211000d00c034a581c800d005c40c0c00b400c002d85030f4034034018039501c0301c0d01c140c41c4c204801010315045008056103500c9280036100181241c009040c9803500f0380c03401e4000f030f401124241c1c0340c0c0c2c480e090004512059240c4443d40070b2082440c4548240c4030307c10304131401c002d000200b9050140c0300400140440f40310845007414204c00f80600c070b0071420249110305051441a01d0b9202c1c1d0401d0004012694000ca0024115181100c00780302c003070600e8011078250f002d005406 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 646420377 1250 646419127 646419133
    0x15060703080f060d080c151018050c1306080403180b070f1515030b220f020315180d0206061c0606170a0303060501050a0504030618080301080c1e01081b0705 69
    0x52000c0c1140025580e0b80303038010f0060050707240e031a044141100c01251081280049c43d40764403c01c2d45800d944290b4004141303810b000c1c502480b42d080f00a0080315648008001075860081009141e40003524400c13010014051224062804008140714040d00c8006400e0040079080c0c1005c010300c0c116103e10b1121016402d000e80c5c549079003c00c808200380e11013a01c4038801c10303001490201d0801c07440c90701d142041d000c843d0840003540316850040f1b03d2060032a00751048030b030701c00c5860021801c071030300ca144042c0600604408041c0c1c550300b030405408602c0150341c086c0051103115522480519032114460320064030509080c2084000b030611035011203a15022403644d1242941d0225040c003d442c000c0c1c805011803a0780790011502481000c0503500080c00a20090001400582000d00d0f0030780044841c400009094503002001ea1081c1d202c140640d001182d01c00305e90034034241d070b02001c492034000c180c2031240c032000207401d5103001000f00c071000c2800c001200d044121102902c080c0e542000813 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 646421627 1250 646420377 646420387
    0x19080d061e050f090f0118060902030c0a0f081623040f0302010f0203120f0403110f0609011103160503070504080706020102033408060303070f050615060703080f060d08 74
    0x100d0100e210300740191400b030305110b0700e6042d60b8140420030034090042449441c14982c0b9100c0020409100d5440c161411502d8123800100c1c0030050002c3e5005509040c040350b628000340364080c1070f41140760704203814014601c0800100030511455072040c0062410720314900800d850882c3c07512005507a030100ca01801050220352038015003484801e880c802e03240c05038403003c0c9117000d980c0c80c010000d001d00044401000100428440f0010f10340051183c20064501d1100080c3c80d070030003899400320443c6034061410065500030034051001c5401001c4201c0e803543c109901c08a03400043c080380c030b409020000020505451145080358020903d500070b03a8405501e0b404000e01030750041c8c40c070788400308800203010309210254003440b64a041c0c1c0c030013007200c0c520750b64020f40d610380d001440c190b4980400e001950102e40180070103c012031040000e0106803a0443d01021030000f0b030b002c1030340036040600c0788800290300802c03981e0f00701044004907141c507034880c80028901240260024800407021807 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 646422877 1250 646421627 646421669
    0x40b19150305071d13080702040504030804060b0409020d020609011103040305010219081303030c121401150203270a03141c030b03330702100b0319080d06 68
    0x106000640e8418015103005594507a441d110000a440d50180500601c130b010030107054420501c0e074031451003900742c1c07030a144050b000641110380481f001e50205c3d584404100811485e4812040f04080840d8108020712150300421142641c1e81c0c0300070300602d00002c03041c0b25607005041c0495480d090400b01d85d99943c481c50a18080d42010501110046840030025030343d0b070050030528447e9600640947c000c6d10140c4003203000e00015074401050181300060004180c245015a0f00b0410003140062469450201480c04151584014104540083c0000340880301405aa0600600031896605800c142c120010310801526400144008403030f54840084031008503e03080107096060744a04529031401040e400e484a4a0a40d40d244d0444943c41d422552030204002e038040c0c0d40441c000c42c00c5012007001d900310b00251680c2015070b201400d25031402c122801114113490b8250080c0c003078440b1a07150b2503580010418002c000100101d000711700c041039a4010001405e00d28031003040c24088070307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 646424127 1250 646422877 646422911
    0x209060d0e10150b0a031a060d020414100905060307090b0a030501080d022b021c02070302150f0901030903020102160308060a1719170c01140a090209040b19 69
    0x240800100d0f081c0b00301a4044080d03102260700b1501940f42c294604480701c4400c0f0000c0c0080801c46440d0a90b10396041819250301010384510710390b520006a80e1400c083e42d1080c58215140070034403807940c091031303154819402244203088800031380d805612900c6410042d0b80b1028250440980c03020080782d0990802d03816042039040380d440c0e00c00d40c0c2501405407400c076160301e601011840c81c1e41c0c5050083d101e1320f01034551030342e9041c154819941e2412480d500d40c030084042502d4800160700c480414019441c04207000714403203564800301450b00102e907140c244680139580d8041d0500da940c1d031800c42858000e4046500d41c4004048030f13814409589400780c90901c0c143e80b0742d4010800d503d004030300111510080500c448040d00248103140c101c0120f054082d45283c4c0403070b02500300d0b1803d0229410340030060816000f1040c00424245003c0c0800608514001c0c034085015042c1614400540c89000f20580c0281d045078003c2910786d60542c0d54005600b07081001e101e074910b01280036070700c1d182e42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 646425377 1250 646424127 646424143
    0x60c011d071703040512150a3908270a0b06060307090302010311210405010b030a020307090b011403010f150c03080402011d100305011a1312170c010b04060b0412060209060d0e 77
    0x2802c41104d4100349c1b250103a440040c481c0300444942500003811071014060201150b0284503510050103258460340365414070040c064400296902880304481084a141c180640c800806d44129045142150000b8801426880040e042c55543c00c000b1048100c2e1500b282c952082c00404400071400400c203900300300c24101c42c20756080d4a84000c0202603d400724041612580080060100e6810009444000d0418200145c180040d1280e950310400303c08000d50300030200300304101030544c6442c050b00500403460f1305003020090102c04180000c0c3d003080b21580c0181e020b00e0481c0030f000c10742a14241745102e51040d1544079034401ca1004a0942c5030f0050740c143c550001040807955601c840c643c03410b003d2a410404039201c0080144182114014070400590150315034010714441e03c44042c03e07983c0720149180440e5100c4801042e103090602800000380814608149801d251052030598240010002406190000303440b1180e035843c1415580c1e8203044a804019003928202d456659103a8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 646426627 1250 646425377 646425401
    0x70203010e060c0715060504090503030406060608040305031f030501061e0b0315011b02090f01032105030a020705100e030a120c0e040b060c011d071703040512150a 72
    0x20107a20102414001c1100c2c0d0080004003203450510140e50340304400710f0315015845600c590740315000940c41d50740e4000d95100300c0c05074014603560309150904030140d0341d030707900305030705000e0014103110000c0d03031250403260700440c40d00c10f020b5a07070180061308454402c55400a043c6d9803d04001040780c2001c150003c00d81e00c0e0391002088041d55400e00d40242d80400c0790103603684e030a401c060710b030700b54042e40d1401110002d4115080d213207641d91f800540c0405040e2003100c0035501e600018002c000c04000d000c03001c9031203000c205101052020740206144801404201ca840e0041a090308000d010070518906200e0000203015600010031100d0703990708044602d00020f60340204054080344140300d1440341070b10b42e82d0f807110540040d0050001400c89800520b820a2040104500368a0288501d01a092031044103201c100700c54880e5510b4404280c000a6000b4142c1103c0360b001940041194200e41054605410901010031003606007100c01144402001d000300803c12800340d01e601101d01191 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 646427877 1250 646426627 646426631
    0x320060306121903082208090910090f06031401020c0705190302130b030705010f020a0809130c0e0108161d010302070c0602030d0609050f1f0b07060f0f090803010605130e010b07020301 81
    0x6599991b10302905204030250107250f0801080d0360360301303100c400194019404008400001e03614001081290841c4010409080c3e55100520400c94603505111919001c00001d605000d030940389241c40788400c1c42154400c1c18428280d00600c040c1c288982c1c02150014000c1404145c4100b2050140400c0411603119006404000c102580210700c03d140b0321941d0340c0200303410300f1140e807101e200e6070103d448158001d904d00485440c11030680600c890f808143c1d80c415903c0c40300d4000241031544c0c064810721082075030161480c00154071000204014529001c20600380400a0050700207104414000e403e103d021003020850700d40000041160940821080102d280d6440c0ca8004940066513140158035200c004121491004040c01d040d0009074050307900c1050340ca41c445844d40c0d00603881250304c1516016007401d03100c2d2074030a1110342c0400f520280005217466440125900c014080e43d01407080c0071844103400c00c00200004050f12100d0600382080d43c4484c10070b002030f001010204d101e58 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 646429127 1250 646427877 646427911
    0x319020405060d05030403061a060a020109150b2d06160c27020d060b04090c3e0309030a030908010e0c031b01020307020613032006030612190308 64
    0x814102c0c00181026000400341d81072601f1540d8240140048485803080a00240e04082c034070f60b0340d1801000302c020103030000204142146040000b0740280204160800d28100140e00c054a0340d081e00d20340314160b032442c40652480c08142070302021381c407401550401070100d041240301c03c03031940010030540984610b80340c8a03940d100c0d0034030001c1e8a07142010349051908156040780700540103020084d41c83c030404584644c132400000102d070800e500641086807901c18482d42c844d001419410001a81d020003001c003da600b01c1400d81c0445100b00c1c914042058590803000c160034829184001030060564441d49418100202401414001c1594079440c0036801e40080d400050b4044072003202a01404950752541281c035011700003a41b2150560104110030401070f5aa080200b42d0f87e402000042640e9003141000d00c18828580107001c440980340c148032803903940b104140c80c1d000008a40300c1003500c41c446001e5003841400d0f50340a5006040d0110b541c1096044207020b845025070144140c00e107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 646430377 1250 646429127 646429129
    0xc091a210a030e0f03060903130909050a08030c040b0705010209040b0117160c0c1806060c03050708090d0f0506040b0603121c060f0f060801060c021e040b031902040506 74
    0x12100010055030360141d003041000034081d040c6115422001414003100074070b044c0200e800c10f00c0407a42d60710b15400c0001c41507d1541c40d401004050141d02a080110403044c2d6201c0b035841400d0f0401410901002c00083c14040c1c441c81100d000d80950300c10329071035184c00d1604038043d400144c0094400c0d41801d10852042d445088a480c03804040003180c60786031034a440c4030070700c0c00b001400c0c02c0c00c22103103140c0400807071a0759240900801041034000c41307482014031a201224919080303041044001920140425403001c240c0e140b042d000800c8035554066840040c03511807902000400b030780200f081603810301c500411103902c124020a0201d180382c1e00c1508058070b07403428003002d0700d40201c188a41011010b1204001810403004c1c0000512a91510035040200f0083c0e80324580e00f414640040c003071240e000107090b004007418203150351a03560307960004041c05000d2060b6010342001c105104010750b02c2da001804645400b500f071710100c01601d95500e101040020302a4050f6040a0104000e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 646431627 1250 646430377 646430419
    0x170406090b12060103270b06270a0507120e03070209090105070909020d0b150c070f0e0a020903010f050a0207050708060705030f1f0f1806080d03090c091a 68
    0x801c10080c060000d183d902c070001980100600346c031004400c0c4a00b55840e02a64940d0036140041d401480280c141e8070f800c20130002d149070040010448089a08143e0030405a038200d0a60022680d03040031455641d01c03401104d06941c418900b42e04c5038202a600d400704100071008241c200e000741c5a00c141541d03250445400d03504151a403e0005035041d2003040018030a178090000e0380a1890041190041c500000c0c12068824a80b14241800000c01c68114017003081070300c00500b00d04000d1150a80b40c0054690101c5000b005540d0310b0340c001865402e40d5800b03600c030300400c0f5011802009207041c42c010b081d000790448881268144113100010034030080000e910340c401c60081c0d032040d183d560703410410800100090100d643e032506d02e40030200042d90018094000c0e101070322481a01c1440c00030504419696a220f40c034105182c19014841c540c0003007604240c06440d07041c00b03c6c406c030313040c5411000c0c075485600000981c2e190404980f2415075030944001c01030021907101c01c00750304030304175258 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 646432877 1250 646431627 646431637
    0x910090f0e0304060e0d02090906090f0606090402120a06060605090f01020f190219060329010927090f0203062d04030e09040501064509170406090b 65
    0xc1c00c0c0e000780010010036100b50180c441c5008090708034600a0341c1d030303404034444280644111000d03410100802803c0f8004004403007805424000030300c0c00d07080201c007160442c80f000e84064021102590003140366007003007040300d008aa00040c01c000141e95484014100c0c1c000307141e40c41c03160351408111138031984000b0b0218110f4002202501140e0b920280b1104c55200006040382c000c2d540d5210398005440b0490203d0041c02c1540300841d403595100c441200f846403026003101d2030000701d8480c41041e6809501407050780d080900c00d5210038400c204018140350080c2d002d01a190510300e0400030050000e44c80c1c15001c1c0b0a400310340c0c3c55242d070040c00d441c13a03482a01c0c0b00c0d207040407140e011240089025400b6007050190908201000510000c240400800c03501034035180e4440b4130401c0301140b66100d2485206440400300320701e4030003031054802851904040310008080c00b1080107040400d41c04a24a240e01c20040c2e06c541000f440350761200c3c1c002e4401e140220712031407400504180100d081703075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 646434127 1250 646432877 646432901
    0x150a09170c011d070504060b0c150a060807030f050d02010605060d0b0103110403032d050901050c0c0a0f0306060906030f020d030314010b070606171e03090910090f 72
    0x1888480600c440c00326280c0108144501564075080600d031001e80c29102c05500700241c20140031800c0c2084140410748210307910004000ea0100411100c10074003041c0410049120036111425440702c80110000d400c4941200b07186010b4010000100414444501021489001503441514841f02e06030300321029446490340091040120505500c01a404210400342c14140042c007140003004100007600103400c2240462107220482e18102c500d4000c2c0320540c4c143d03040007180100007031002030a5005400c07402d41840404141c1c5803a092040c409000c194001412146250b40d0f2591811002e02d4503100603208107180074004035540f286401000f080d60b411000e00319035034400350309120b81600c4101c429010940c2d560003080052189082440c002c1201c0c1c070750720362100c00d1410700d5400c0362003540c41040400d458a032840032146004ca04220071120400c55041c207110b404009604520500f00640e5101c02c12a040094144c03c03090918203a60302140c08001141c2c01000403012101107281d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 646435377 1250 646434127 646434143
    0x180d050a02130e0715020115061409041e1e0e0d110c03061021020d08130b07201012020901110a051b091006030504081605150a09 57
    0x800d01509012412a0040314201800243d008001c003485040c40115089003481040152107003900e6582401000b01008100300c1c1c8500691030580c0c0504625580c80400f0100d500200d10110150381741c0c0e110003001c9111030455290b480c010051840100f41c0c4c10b4080071240e19003120000810168410348050701080002000c46095240094a14403c13554401440c0e2260f02001b4035a0344042c00140d01846881761103c0c4501c1c2018100c2d15000640807040f2a03419010f1601030151341ca4170030603616070380c01243c0c5c5660340200c0056240d046049400080c0c1419002074003004001e03c0c1e1030700010900c0202d582041c5010410100045c12005039005000128408880a00300c94558010184c80d041418900300c080508022581400c12030f034400e44041e0051069031444a6107441110140801280c803003c0501d820100824010f403580107003010150380b038000500300640102150311890107030003034400c1034540346042580c07081c100701c2404007508114041904083d8500031b542200e0f5008103e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 646436627 1250 646435377 646435393
    0x1407080c040f09060c0f080c0c03031b0906030c04080d0504230307080a0606090f0b010207030b040f0807050604171918090203010f060207080c0a09091a0c180d05 71
    0x1000041c00a640c001482d460380d81442000086091081e013940c0925a110b8031045000540050b01c0340c04000c010440583c000c100030031140c04044104ca510100d0b10000c02910200703480103401c2401a041da040c2c100c070000043c400005400d00c003800c00c40758040229441c0a5220001311030500591150010714240180401c46091242854506d03640014013103c036155a10703614141342ca4040d52080d1100e5650b6081400b0003503c901030780c01c41500c0d8980a12038510304100007569186071344009001c1c04034100200b810440858074031a40316400212042d291140c50500c151500d00966088545144900300c2610009251040c0e0380b0310090303003803008841120341d0000c4d00c0c0102c24204861401c40c56510210344410f4034806540a411600151b8015908111020749040000d81054902da4000084035046a861154410035a45150350109460100389413002d0b600700020304a11031030607210200310306c0040d090040d0840c4030245d20034210f25200001403010b802c0c10000050042e40003013074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 646437877 1250 646436627 646436629
    0x30c13122a170a060c0c0c050a0308030403050c070807031419020a140a120f0b0c070b1501030e100203060f0603010e01060804210e0901050105030f0f09010906050a0204031407080c 79
    0x550003421401c50b01500c0000250b43e4824086a03000f030400f5011541e00c485040900c84201e0041d405040e05540f981c0405007151108a1a03000c0100010100700c800a803110140c10f003817141400a002420844160b29101d20b4126840d00c205070000a55214a0760440c40c4140224504410260041e0200c1400d6042451020702000300415040e0401d00b0504000341d81c1c40c40c13601070b035222402614020324041c01c910b03001c41444005000f0700201e5806201d100082041e17071000c0c94020306288449018014a4001a40a002c014442180e2070084002c4607860a0040d0011803142800310754445a6035507410030030410740002c0c00780034021180000140011401204030503000743c005c2d801406542d0030600c12359403840008040900240b0b8070b10800400d801d044042c0b60150070242409400c5241c0400502c0e0b02480003007400c0821000ba2010507000742003940100e011981241d03052007280340115500020390300030701c0304940005d0301606080c0800e001103020001e85002c68041c00600ca100c3c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 646439127 1250 646437877 646437899
    0xd0c030305071815050c0312150a03030f030f240602010b04180b060f06070f062d0b0f100914030d0c06050a0605040504050d02010c02010c02070506030c13122a 70
    0x30444c1d42480070402c006500ca4100300054004110311206070952071500d0390740d1243e94071295141174040c1c0100e4100307100003501f22110800b0304415240c00282c141100225101800c403c0743d10381d140043c28a00008101a003081e41815614560000d118200da040d003030104562020241407000d03240d040c030301800074400003d0160003080007031001d001d442003400042c40c2071f40079080c1120348940e5000b10108020300c0b40545200c07809174961410070214143d0010911404292010903e1540d521100e846507403541c1d0209030050010384501100c6080c400080c02c0044e02d8000c0e6503014031140404140d528001800000c80f00059030780170300080c05551020098100070b000d811540ea01c8c1d0b50b000c038041e25148181449240548000c080c2004240c0e0081d0171118654062409c40e410010140040d640008148007102c0c41511810303500d542e4084030138014000c004110821582c54000058003a407050f40c0504c2e22400742001d543d0160384010002c000d02410b84519811244460040059050305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 646440377 1250 646439127 646439159
    0x304051e0c220e031804060501120b0d140109031b0302070e0901020c010903080106030507090f06120207050607030e0f1f020921060709050906090a0c0c050d0c0303050718 75
    0x82858120081c02c5004150903200d041c00f40510951002c1030034403080000900101541c80180d5007004a981001c000824102114102c0240c032601d03591010030740d4a5a614041030b0303d410143e84ca0501d0b00040009020708040d031070982c0041c04014403c1c1d611080000100703440d9904d81c0003410202e00c0d002c241c1011030001010112030b551f00344403078284800203004490500d4865969101c3d01d44c1000c0010701240d030050301c140204201d00340c090004081c03078007489058402605000002c050f4002c0580041d10541c034000341240505000c1c0030046030990002c40d02240100155080e0380e81d4041016a03504241c0003d0807544046600303002c804109500074100500301800a4181d41038018680e501c40c00c0c2210084c0b4107074027507420800c40961190700c0c04003030181100c2501c0241071580002e4080c05000d4000c04101d41e40700200c1310050300403645825107645c42010b880c00c500d1340001c090b00780340c020402135011074246800120110f100b810344030599058a00701640c0c1c0c1e0b05110307040c4140c3c806 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 646441627 1250 646440377 646440409
    0x910020f030301060503010e07110d050c07090608010f051e0406090f32070501080412230a02060c071a0403050d0e06010513060b0d091b03080304051e0c 67
    0x1448818061a4034207000641c041c190540304c2e29529450924005160310008000b0300400003044050b401c05800440d200c0d0340d111036480c01c152108006803050f410301125600c41c117052071078170000007036681c819004681c90210404c020801643c03a00024020030032103d103000c540e2005000001d0004910b9400311540b9405600b21100e4408540d030381107124400940c0680c0d10259060707030410b4104200c07000807101002c1d14050800c4034503000c00a4940c2d03002820050111010064040300c3d188110a00ca0089001004a0081800800203d01e4550003400c082005000341400a2202d60b030701001c8030f0310b003a03201070b0020703a01d8456494070401500261040703040110400010303039036100e03901400200c131081d14050000340d45090104015a16810808060b042c14407030208180800d080541d4440400c80030082400080c81c83c1c010210b64234202c0e100214440a0300100500c030f540b1019604c514424801c40b41e222084d80c21982d001d0070001c03c0401c480d8400c1710841380078280302c090381c086104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 646442877 1250 646441627 646441633
    0x1407050102090904060b1908030d20040e0a050c040f0303030902013b101b06020409090b1f0b04170a0204050103050604050615060a111c32091002 64
    0x144400600301210554095416030345494146c01186002d10300c00045008960302812014503244c0460f44030700484168400c55541c8094425a2030340c91880403044809080d007150307845403034201655052005443c0b45100d549071400082d01340d40386004a80c250ba02507001c0ca0071891641d45d0480c05040b020744101d04005060a10780d4109007806030710b113180ca030b403000105182c2d008140022021801d09603d0703482808200c030030241450700101c0c1e04070200c446d0303880c1902c4140c284c18818041d00c965402850780901c3c000c964014001f40150755409104038980a88c1390710400401c140c1c0720000e0740035100a0300410001046010b08010420a00300b617424199600c20342c4075000a422914260b10640742608144100300800905210a5a003d031001d40314400c000c08441c00300b40d09008041f286e4043c040800060b4030281010811301510710701d0340c0381c503014044541d14003c0c204000900c03007140c0405a00f8158001a4415140d04902c003140020b441c100704640041110480c3d0400100042d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 646444127 1250 646442877 646442887
    0xc170d0b04050123031b01180b0c1b01020c0f01121d07091b020d08060a0e0a06050a120b13020607120e1003050108150a0209030703150c030203071407050102 69
    0xa1542d004030350003003007004a00191004d004405000c1c00c00544400b81c4243c0080c0c0d040c1c0c003a05242c02070200341400038a8000208000d0b1426240b400c2e00e1900802080c00c0c1c04658802e100d8000100100c10290803908803411074800401682d0b595603541c012a807146444c1c04004055201d840480801c01600401156041d5605c0201590340300c0301120806d02d400500091100d10000e0042041107010851030a02510030140d0003500d8014000d00c0c50100400600030908564407184144007a00d00140c0031480b03810100c443e0390040c101441031030f0080c41d6400d4001411036410070441000740c0c200c65013158540d2162003c1d40e405908404c02caa11400a10140000c500d00c010340800030791242e2658030724042d07040b040000201c41c00304203e08040c14036005103d0600007080c44250301c0c080f80484150780c2c0700c030040d900190007240350458051196001c00014450090102c0125078140082000000c501c0c038002c030140c1c0b1088a06201180702c00403410540211080201a45402900018204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 646445377 1250 646444127 646444129
    0x70e13020403050703020a050f1305061306090c0908070b22080a080d060b0306060706020304300909181b050901030f02030f0a1e02010c0b04061b0c170d0b 68
    0xe0704903030400c1c1c1e032980c003003070050086051512001001c2c00c012900d44052080020005048040000042c03403e5521400826256210150841a10340b00c142c0240071054403000b41c0c034003e090008209000030310354240021070040104140301560100036280303252035800ca245000703501c03500280514400707452900240304c1000703010203003d01d4410395001d551441401c0c00e8005440f00da82114018100070000d0200d5551390100b12030344942e0140d00076031a40e07a54108040300b0200644040d80d042d03048007512100c84001c00b818664442030b43c5a4011081e1600c6502003160b007100311200782036980d881c0300340124131000003405560f48080c0b0a880115103403001314405503002e910440700c00048200010441c942403002c04112041a0010210003c440c1c41e0f19103040d1100185004101c0c858580e4001c0da441107020f000341607002000c0c1c1c80d2074242403074500000d1458224030824240b0081c0380c0d0003218401c900140d11141c0208055595810280e14803071154011492304045c207690740e944805d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 646446627 1250 646445377 646445381
    0x9090c030c03060b031b060d09060b032d0a0c0e061906050702100c0c18150b0702030105090d0f1d040c120f1103010909020f0909011a0603010e070e13 66
    0x60b41c402c80c2d010603003551090600d450601d5000d40b0302d14181407641c412100b42c90344001c0c2d840c208035445001c1000303042810321800600c4211a032507014028100307240b28a0400343c01c0c8400440110724000b040d8050303c0312098030740b18000c0e4014900c503142c8504110180c184504643c004c400101480402c0351032a03e0b90b85005c003540e101030045240400c1c15415032801e20500245d03503410341000d03286c80415540b400006142d902628070394000c529519002c0c1d4140780c1c444040b500c40382c60181e42c2a511003034407101070341002104038425030070000028620100130840000e2446151250741a20701001c2068502c24403401605401c2a4441c4035034440d0780d00c0c0d000c1c003a200540354035591004404103441509603141e14000e00300090402410344a42d00d10300d42102c1c115200042c002404107601d10008180c68030105035075900c84001c009215104c0410f500030020300400c6052039102c40014400e204907800244556543c504d40a400162914000e6036040d00078031004003200742405000409400b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 646447877 1250 646446627 646446629
    0x61003110c010c0e06040e1303020106350c0105160f020d1101030c11032a01021209010b0406121101022d010e01150513090b040f0203010b100909090c030c 68
    0x901c9a44520741c0401064001c00324600c9a003090b5151460241040c844040c110700c054803001c006866210138505051003035100030081c0c016130502e000c0030070340c034080481900c115050340d000c1e0150000c2c0ca901a00400900122810700603113640d4100001000e080c01c401c100700300c0175170b484118040f25000680d1000c06a81850f0701c40e482660f100282c41d0001400c56400c100003205010046095030b405050000649000404031030b2400155100c0c00101c40e01001c1c0901c1d221305542c00400c40b0250904c8001080c0e1050058600070041f041d0b0b907004000075140c9501c030703001800c01e040c00d8840214908900850107850180121200c81c0b80302c1085a0341e45039070f0000700d14100068540400d10203000e0040340140d144000c001e10180010040100c0000c00d03c0c07240c03a02c120a8101c001c00c1d000302d650408940542c11003080020b901d03150500482124912074100e01c03d518102d424000c501d01601601092980c0b0707961240c0003400c0085031402080400710586802803407480010000f0003561080e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 646449127 1250 646447877 646447897
    0x1206060903060c020c01021f02070c0b2203020604050f04090b070f12050103080a03091e05070e0c0307090b0d060504090804080d0903170a030b130b091003020906100311 74
    0x400c10925506161046510034051501150445901c520540e0b9001075a1000c0025085d016502d60200700d0184009100341c4070014601c031b0003600c00242c1040c080c80900070300c40c205965003c2e092030b407640c1c0c90458504d6010080d805081480140310318100415680d0740c011015200041c110301d261291100944122101c0001034060010f03800800d50004403151780d031201d40d405000550540d50382885900072012103108145d83c0700c0e40441844484110440c3c068805014050105183d040482d102e1181d8041c2454019098010491460440049074840d07905999500007443c00c2c4502046594800b1000820b416100c44010074103030344a00c43c0502040c1304188481e69141b40255950030042054a40428010614000c00c0461103031038564079a8480c0e4120a561344810002c154001d00c15010482c2d00040412220300c84220140d10202c00304804403403112040d036400350740018031422400001d41100c035642c0401c40c6820200d080410140d8281004207402500e9580c45026030081106a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 646450377 1250 646449127 646449137
    0x40b180603091609020f04090c03060e090c04060b0c1b041509090203060c0c120a021507020a030305010e070e01030f0b0607050312010e07051812070f060834120606 72
    0x89080d044051600c0001441e044c002581043d400c0c8100c00b207030380154819080c05c9501d800c2c440c0003043c402e920020141428607600099814820301c010b94400068041c280104d147c00b070301140304240340c0d00780c59060311168000e00c3c6540030081da07400c400d00c8075184a500035480b2003200050301014103180001d040751450006000740d00340101403400c1d5029205054422080103483c820b800c0110380b800801c40c01c5c13505141e4458055008a192005c01039010700003804c0e420902003215070100b110000107009580620660b600d450714120914425952880030840103140c1d0011940241c203d960043c03074420001035801c84000c04103400d039204110480785a00000b46c0c2d23010718810300c1489405000da607842105640f0300107502903d240702c4c070116a5459040d00c5402c08a61ba90154040800781c0c0780001d030342c4404c1da14a00b030f0310008040c2c0030710804144d00400068804024901c039146043c081091945880c225841102d0703020b90001003041040000d208601c41c454043c0104401003c1560758 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 646451627 1250 646450377 646450393
    0x601090b010e0a05010c02220903050306031e030306191e0807090204060e09190f05010501091205060a1503080406171e010e071101150501090b030c040b18060309 71
    0x418482c0c8501c40d19200f402c580300c050009980c4840620043e650507030300850340c681c1c1e490f40c0050403403020342c11000070b900301001a01003680c0500594041c1200350120b4100c0d500c5041d4014040303001c6940c401c0c041c1e00510004016150240f89180341c03c512240c041403071a190314240c1d00c10020404190141044d07205d0400c000d0b03c04010550080920080850809040100007000c000f481405103200e2000200030a040140d1070700c2e16040c19420500812160b0b15074044140230304024826640468114080011240c81d00b500c00d80320315520034081d241b540e0303e00d2540350040000405c41119420b40640c080005880c002c014000340010343c494900a00380b1007000d2010b0a00100001210441c100401c01c014140d6444541996440980004183e4071202c2c100c0d20510011045031480d802d12010225104410380a04142d0754203076500c0f0681501c540c80000c2d540301c243c6442c0e460040030041049600c03c4a80a000c45095500340110010300307940026119030410741d00301c078281d040260 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 646452877 1250 646451627 646451629
    0x70507230f160303030b011e11010c090503150901090f0b0412030903050702150f04090207150e1b0303092d122119080708090c0f1c050601090b 63
    0x400400a0340358000108510042e5421080807081c0c00c0c40000e06268440d440807031b1b9603016021150f03405d42d10311148a182001c6500003070020708048003180080d40317081e5482108610070308000080d5900035004020f03502054407101060f003c0100180419540c0f01040c00024111008905116005103125070a505180c01d1528044c03030003100f200181442c041e035102c0000d030820140c402da1501291702038401c0030725003c002c4c00d51003600100c00007007200107004242080e5581c05054018000c0040302c40615143c00e406080b80d0715800350348071a900041c00104403942c0c2464244194070040e043d6800c094040010072070801e41c80920641221208040050180650002a040c0d00d0120b07411442540740040968503040003440c1e480c001c04c0300340d02c030000c00e14840080710034281c400814043c48070400540140210300507216000000c500b171010448001c00020481d116080082800329007405100c1000006e101e18107007550410a80e800d03000100e00c0c1401b80900802c0b07500004101c440400c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 646454127 1250 646452877 646452883
    0x601053403020f0f060f0106110106092d02040b03010e1518040b150a060e0604050a0905040512040f0e040203011e1a06070b01120201050d0908070b0903180907050723 73
    0x70780c2c030044540c414030400c000b004080c21b004c0c1c116a003a0501d12107013103105401901414468100a258a003010480151055a242c29448001020345403d91300124882c443c020f9120368468003a4054040c0300600240780001552508800000250100320f6580302c0400c0700c1c80500010075204900d41000c1006200b10280620b511101d05030400030700706e5650001854480041c01798808000010701d20501342d80f250012200600001803401e5041584e0700c0b4080e0180404440440b803034000c000045403041203a4050310240c907149a4400c4070107046c2001c1d40e1080b14000e106036410341d00c986400d4006000e00402c0828031310b4411021442c00c45118a01110b1400340c0c4250b0b00801b0708120310004030300c00c0340d05107054500150129038244100d000488140c02090180801ca40c80e00c1c40c0d141c208079103580100070007840f803019241103a03560b004083e1607015000300003d00f200340000b262140e1802c201c40d654044028181a402c10813903440e00c04100d244110780208a00c4040c6c01ca0164035020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 646455377 1250 646454127 646454143
    0x161b0504050f0609070e01110a0818010f0203090915130b010906050711190e0c120c040303082712222301020106211104050601053403020f 61
    0x2124505039800c02e070b404180c4e0914010121020000717a80c076288042c1c1c0c03080303044001c010550822100f812100d41446079542d8010700c850b2001401d1004210000c7d4001c00e0039120100d030030707000340d420b04a14000b44078035000000d1408907108100110050a5526140711480416405c0340005803144108000340045190750820021b200c0140301b0000050702600109c580c1d00c8040d104012020281c000c8051045010b0300a0500c1d0040d500400450030b6525000e0f1910040c0c0043c80040c603110541ca0301154450b40c007024000a80307802c00602e135803c001030210b0100312120040b01100101c6008581080ba080405010001001540c0035140002142c00b2002c91941d0b414181c8603841c041907800c1e140b262061000c20091348541c1d20032a44c1c000c0d0300c90310051841d00f90301454802e540ca1b0541420040e840d080352600100d483d80314180c02c261103618031600040c5c41745031606e142c213801c0c816800201709214110b5420300c880300c42203a890505912103544207070010070a460291684030304100300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 646456627 1250 646455377 646455391
    0x606020109050c0a1406091c05030703080708100b0306010e040f0b030114010b0405011101151706071d040b040e070f0608090f0d051c0e0309040f050903040308161b050405 75
    0x915102400042803040580800c1d42003210601d40d030b4000c7d0702c0482d1074807080720781240188400c3d0180c01c06100c2c01000510b070304d501c00e58030081a603071824000c0d1382c003446c1652401041203d440d82840440701100045811480504142c0c5424040500040907174280040c401801034a40e000710400b8203007400b4501e01e408090340410015814844082014000d9100b003504101001c140c0c100072640a500042400b8520b00110880741d455607171900c1c9108000390815490720816002070b00350b42c820030710724020100c6249195500c00f941c608020117005400390881e13200f540c03800003541001007040b50000904404058008003481c260303003d00007002c0108503c40300e42228818070144440402c07100b4110450703007030154031580c0c2b01030240001c00d104003074a480070b0325001d1002c2e0400c0001000d0070214900311024000310240d90350f1303942512410344840c1d03203a81c000d2200780009000031000e4926581003940000103080c4507203c0240041c0070071940c540d0109660002c1c009030805006031640018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 646457877 1250 646456627 646456639
    0x30b030f1605031b150d09080703090504181b050a080d0206010b190c0f0803091f02160b071115060a060c0807061119030212090c09070f120606020109050c 68
    0xc004c08a00310240460000d106181070075010350945004425141c0c0d10b49450410424250b0500d4020350301e134440c0006802285043d031001517289004d008019004500c1e0130400031500741580d4008420034807211041d000c6207880c10114a13922034a0b1400700420040d0003d1402d0001c0c1c01c000780c18040c040c0c001740c9501c042040320890000c90580d640d038071101c4c0c61810b080409021706140c4110551003c0c018a20704000040c0000001d0000304a4028141c03107603044c4452407242c6104049118145d1b000d0b00f4407041c03100d0b000124400c1e000040c0c0c021136034203220f0010065112400d050903907040781103441e800d5a205006450070000c041e04040c001c40c0c100030300c83c1c50007500c0d14a207500844c031004080175101c2c00000444a8000265500b0040d0700e0200440306a568402034003a402c0a241803041e100303041c0002e0b00b03011002803124221f0034081c04005403074480d101d044800c038900c00703501428452950b26040c0203190b20321448000b81401d03400012054941e2900d1801d081c00e481c1168824a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 646459127 1250 646457877 646457893
    0x12110d0605060f03012112030f0f0b0f060903012712090612091a010609031a010608070c08120403080117011e0207020a1a1909080c0103020a030b030f160503 69
    0x403030f0600449040d90b400c0e807642c80d1000d410700c12000d034683c0c058000504805802010f022075580540003001d1410480c00184004030180708540f00b169401207000303a214a80e8a01c076001070401100815034250058008a0b8035070100a1003480403403440e1040c040940000c0e900001d00003801f454041c1ca01c041d242c0709403541d00c2c0c45801000070080300b5100d0186682d9072503400801102180070004a00303402850121340d82e4070003010b0403140083c8000d60b04010456040991f4090b9409100e050782c4140d02e0704480342e280c002044800c1d8103801e008860f0708800f0014490145400c0e100644550311907a02c842140d0306000d62560140c2030707000101420307070400003d080c01c034248080d60401295102001a1160700500024510030491f601904540e080c000e4480c2217400c1c100020901141c4461070110110380f080b01c00ca48400ea0340c4907003031894016410403040b0f58800d400800041c03110b0710f0007060640c4002c00103814440c1d85ea482c952b0990180301903c0f4010846101940100340440141c01c43c9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 646460377 1250 646459127 646459147
    0x180307230a0e070c0b150301060e091002090604150c08040801270b043807020c0312030105010c020607080c0109060b37120c031a04021e0112110d060506 67
    0x203074000900040c560b02c2080001006c460b81c00e590324850702002002448560b07500c22040701e101a06581c0202903000d516400315540106000b1103e0381440940f10f1480c00d0710346607145400004005000d410003447c01420404108528090310140101e0340001408400341c1000d12206881d80c6160b401e18040301c50702002150382540c0f10350340603400400707000403184100c01016104403e40a0f00742000c0c00c46900d502c95460200700141310394029001c0f03602c0c15081da010950b42d07001040e010201070504000600c010351041500804261025191900700032031940c070380072207070450a40b0b90750a0390740304246410f02200380224440e941090314403402c01905198202c00182000070780803500000c111040b03d0415880040b40018098040311203284001841c140601500500c01543c801500c0c0c110b20321880c40c0c1d107107114095507005265441204100d0711440000519608181c1401110709150481040d14002c20900e554440d805642d5410032100f01000ca030034a82059000b02c0c01401200c1e40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 646461627 1250 646460377 646460387
    0x703290f041e0f02090a1d01080304080304091109040c02010f11040b0702041116150e0105060603011e150c0203060a09050d050c011b030c120908180307230a0e07 71
    0xb0781c410b15100810490b02c1408504003910074114010b1300a2070410001496016651301106541041c00c02c207039990741e0781d1071700035528000c60140c440c864004101c100078425096112100d81002c028240307051800000003d41220b91007844180581d46501301c3c248029194482c80c400c1d40403a00703800e81000d09020300c072401405101c0b0300900859490700155108500202515100081c800000c4035082c2249401000b0258211040c007489040c80e010030b014803418094144111405000700741140c1c03030310040c03003421003141e00c0d500030780c008058000c2100000b00460300c24040340754980c85c0d0700078142d10600d40303440c0004080c160024a4203699500007540030440d10300301100303480c0c0241c031001c10003001070060010700c855100d20003400f00001c8400d03070160004a026040d80c1c4400d02d401081c00c81840c04e80e900048002c29084040100e50581019446590040a000b904171065291511035202e80c1118003143c030071100c0c00b03240d212000f601e0141d0a12004d80181b45140c4818240101e001c0c00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 646462877 1250 646461627 646461671
    0x6020d0b131a150903060703021216140a18080c01021b06030402220e1e0a170a09270c140d0203130501021309150810050703290f04 58
    0x102c6058081d00390f001c16140c0c43c050b1040801c0080c2078803414280400f0240c02540701250b843c002c8545480000c0742c40c8820399a4a660407400d889417480f00f440e00c10a904190b100b00c1c41841400010028034a240e007004200340050020300c4010403d400c044800a89071110007103c215049000403081c5001d510380c00300344da4015a060381c52800c1030000b0603003548055411841041d041d0b00c0c00c2d41c00c2c2c9401c5d000180c918884042c0e0b01010340100030307008159456208141003e41080c040480305124000b4801c0144440030359854422a02525041103280d42c64014051410203182801b280442004900c207400805455041c00103508510790600c072018000c00001c5410781d80d021000030198022241440b0308130342d01c03800071540c40400d00d82420844003240540203c40c0e00e400380219230702c205030f0764074001d4500f044d004185004842940c400a828010001801c240e21005580c1011804140d48001c40802c600601a0600c02a040c4036105100c18051f0703100b54181102c0318040e09140e5600c0c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 646464127 1250 646462877 646462879
    0xc050409020d0617010b040b06091c02040f11070b0114010f0e030a0614100501030509190f051e1002030c040e0603071e170102211306020d0b131a 64
    0x16803200e08040022005201c2a40500444201000b4911180c0c4042d4001032001b44d08450401003c20324405000c96800303801a000d40012900540300f103000410040085041d100810104400082e000c00805480003402503407000640805e480c000c000d54040b9650240c64803d65000001c6031990009000d202217000b94020300080500c4d8070080c0e1418080c248d00580c102c4010b01964180018100014104541c29408004107940208403513109009041c0182c48070001001260040c400d04042d08509240440e03101030b442c90040000390090241c880071046d0740520000d0341c1170203801030b13007003c15180039012424410010409041e221800b510141e034800d64075098659034090100346000c8641c0c1140307440078001416440d0260303644440340140c64109410840c01400840120700780e000d800700d044003420490241e84c400004c003052140d4001c246400d140e60545003a10707000102d900c5200c05c6403800d62148504109403d00300030409444400601c104040480d00f401c0d40b8005031415011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 646465377 1250 646464127 646464131
    0xe010612030806040212040b0907090513020f0307030803011419090c0f0918050a0209030a05030a020d08040c05120709021303120f080403110327010e0904110f0409150e0705040c050409 81
    0x20030101401003010401032f141c885401c0050742000c0628000c6131030841e200302c1c800c40e0900c0c00f02c034903410b011982004032030388804010b0540e420b01c1e0b100d0f032016010450541d0002400300085460740060740701e12000300141107001501042d0004010807165200045400f0701035a080b04108101c1c00032603d00d40d9134050000010a034845070501000791107141d101d56414403550141109025000c001080004000d0b001c6a5011040100685a00708100d90140050754a030750100458100f08041200b904280016901101d480b608050700700d80210a02d82d4100070411020310402034840180701c2d0343c10b9a401d04541406120a00911824004000800308513803075814a501c480d0070020340b000d21145c44041200c12006110304a01c01100305039590000c2d00c08112414030b403e240021a0240360000b101404004451043c0312910f0300c800302803500284d95000f00c8012880d00c0140e103041684c2140d0208142680d040da0f1407400c43c1c0703600568426881c00140045e000e401c50100c4045680000c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 646466627 1250 646465377 646465381
    0x3030302030c041d06190602060c0706020408060a0605030106050409021f210e0105070c0c120c0f090c020d05090303160f050a0803070306080c010801090f0e010612030806040212040b 80
    0xe2540b190055612403400075002080103415408101d01030f62107400c058500d42d142002c440c06d407031350700ca0040c406c0070b0143c6c01800104034515040801405482d001d1007000d85801d9942d0b19013882d050040303c50021441c0d0703401081c071440c5000e004040003000211400d01c1641c0064002440c100c2d030300c43c902a1150341102e60365003440d00504020305050154003103410103030800d6401d80090040000d14404552901c4c0000d0784190207006908101a0040c08601001d8140103407008074210450b01a00c0360866030100046103041c03050604041c2c072031444040f0b40314802c070354080e19003110100000306021041c451100e240e01e00206560100f29000000340d02d00c070090609400c64503282001070301134001c00c0445c0d424003020000a40c0203002c0c6940c108070031541d800e052904c0d071100030281800200b041004000f0b103e103d4000e00d0343c00424001c0020342d0603112020a08584440d40700398450382807680c10000b4180c00c901d00343e60000040d00e0540c60704d001c81001c14404040100024251800040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 646467877 1250 646466627 646466641
    0x120703090b0c0c0303030a02070b09190807030e06030c04150905090a09030c05030a02011401290d1d060703110705030f032206320a1e150e0c0f03010303030203 70
    0xf0103000c0c0a4180ca99030b0504014600c0607501c10039054403041c0203000854810000010300c111440c140b08120341c1020a0781c0c2c1c81342070399407000c08140d0030007180507a402101d40d00d140095008a070115810f940e1946481c0d03d45030318001c1d44004109019113110200640d80351345030000d500c40000c000c00103049082d1b15041e070300001d4580340030b8030501c0b01142c0380e13000d40d80552001003400354210014500d682e0341c4d00c41540754509c10041c1e103103050300403c58807154020803000e4251802c1d01070000ca070000c4044c0504950b614150780b51344040e80300d034041c0b0118136014481da43c0d6206146401c43c4c9408504d0326150303500e101e05100c00c4043d100005c0042d0b00c1c01c480c0c2181c034400c045907010711a4210035504040000d480e440d0358291224045410310b070600c081184c0381400803060f49440348039950b035508420009000c90181d11000068201c2c01e1755a800c640d110b8840a10880b0508000c140d06040100f240400006d204140051007005000f6100c1c840005807070460fa810318000d6600e6a0b42c0b2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 646469127 1250 646467877 646467883
    0xf040f020c0303190b03061e100302120105010f0605070c1203050f040e0405011404050a0b15180a0c0314040f0f0f0302011b020303011a090301150608010602120703090b0c 75
    0x52001c0001e001c08801c0c005a592540705250108441034402e0100502260815480c4d030012303100310380b0201004080880400191079001d5212050b80c0c440b0048960365004a0210122102002841c1c0d559400500c00e01e648415180d016002c980b40c0700381000942da0310b0144514840c01100c1c1c1c56a00382c00e9030010184035904030750892080c0c001d00f82d03c5580d6040201002981511308440e20350920520300322280300340a12074422a000402032682d02000c0d00c07032002085002c0c0c07030343e180181d68040ca02441d49891071a680031014003403c4503194601076401d8412560442100c1c0205402c1003040035000004030202780d0801d07000581078207184d149190a502d20026424002c003003100b032220a03014950103620100f0b1880c0481e50700642020150012600c92100340281c003594605003440f00071000a640142410840280001413075000d11703103004420400c5588840c0028646600500103140e05118614000c41106100e504105056030003030a240114000c5242c0100d0100e203424a03e2010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 646470377 1250 646469127 646469137
    0xf16090504021e04062003070b01090f090503130e13030507031b020d0c090c090e2d01080c031023060f101d0d080711190602070302130203060f040f02 66
    0x103c02950f0b0b2a5103030005032005550011b40c198001100143d00608640401102c03100d552044803d0140d80c06c05880c80010b040f181880d01802c0d80d1065104000342041000701048010141c2c0400e0242ca807001e03907000300a0041c443d4480c0705d4000368810010350072006881d1a107501d4100141758200c00c0c4060301801c8110100607500440c842a00c90501010740707211405da8541c5181402640794070b160546840c1282d1240d4400ca40c034140001d400c5040d101c601030032406a6460504981d040700c0004101d0600a80002c0003d8201303800140d02e038503040001010707101c14843c05000402c940d0825440507204400d04a21100300e4034005040c9a4030f1100007000c02d14000e02200c00c8115100c001070203c45a0b10402d005491103011f00721051a100140940c880d07801203003946000070035519005009080c3d90215003000c031700380039910100300a0400c10081c041c42e40c001d142651460040150349903031614180351140c410000d0040c244c40d81d20151006c00001e03200410a801c448074040002d2140d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 646471627 1250 646470377 646470427
    0x5042303041d070c120f030f0b0109030b06030a17030106170c090d03050d0e06090d090e0a0b0103110406020c040f06060f0807051c02070c0602010608060106110a0215030f1609050402 80
    0x101700c0c5d54141d42c6820440260702c1102c156000c00681c021090400102c2c1c8800800c00c1c00b05a10036001c00009114103042680220b0280c26105407010942c1c6584240ca000801d07000101c40100c0180640d5500102c164100a40d21341c00b0a0b660816282131005881050340e81405a00c0c03160050040c1805403003222180c0c1d502c200700300080506040c1c25602c40a0903200a42d45014289806040b54440c0c6001c07030075aa944880c200480d250160310701e00502e840c4403428181034480340000c150300407110142004181c260080c1104259040410040303c1180b9507080205107040c8040c0041075100c015403100c01e65a050000403600c2d14507040d28580a40240d554084548201c0680085203030340140c29654407078400f958000d51940e0060b401e84485009035032031a0302407401040694450244404a4561101624400034540d00845c000500f001c114080490f00003081c00505a60f0b508455442490340004030350f40300c035440e030007030600c0c80d10303ca15441182c0104100800c1d0301004100c03140620b0f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 646472877 1250 646471627 646471643
    0xc0b09010203072304090f0f020c03070302071a0f03040203010b04020c011406181b0702150414031b1003020c0a0f141c051b0105042303041d070c 64
    0x18000452038041e61086600e14005807910301c00c40e00c0e102034468151003025185101da030601c1e0074202154000d0490404060100d40c503266499058051031004042a0084002941d956182402c02900d0700265501c448100c00e4600000603021407242d094480d030030100c110700caa984c0c5582c000640501808000349500520000700e00c041410158400003000681c120368200654a5400300a10313010890b15071216008804006040f0400000e8030a85d10016501c11034202040c940101c0c0d03040c004c07540180c00d521030020f010f0101d1881d20003007040421084009107403641c11a00303020301c01d5040440443c029039501030755000c120b001b40c040d520b4000800003180c54207889401e10400c24683d40000351003418a406e1003240104020072400c00b0700d045030f48240101842181c044600d50310515a00034460b08248503810035281c01c1c002c050203176004618999003d599041c42400d805545000829198400c000c1000400440101210300007054000070344140c0d500001502e0415094900510120b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 646474127 1250 646472877 646472881
    0x1612021801082a0906010c02060d0501140406050d051203060a211101180312030f0c2a02130213050307240305070c0f060e0a061d030901090e04030c0b 66
    0x50001404011120100300702e02e64800343e6101501c00f5a00c411202e5070007152140018499501441521144603c0a441c99242c00c010102ca441114000c1e0011240981010702150702ca03c1c0038052034000c3d01040700c800340220110765032940d503403d40c2040003140030004800030ba00c0e6584d84044100802075410354006a0020fa0445810764201840c1160040c0c0c40388a602059481400100c07050300c015000d201c442c6045484404008490460100030161682c1c0000d0300da1180b400760700c081e81102e486070740c1034040c80f012608400c00d400e80d601e90546901a442c40142c3e54440c0000b10382050038600503900c04081803034610304010b5401094261007191000610500424501039026003e00c0c1541050700c074010040741641c03c19a178020001d016a42d200022954111004130614458040040c0035003080607028100b400402040d10006c0e9180d0381034100d42c0149a8613866020100c0c007861409910a0000c2c00482c010f004107855808220001010180102c4544440542040050500c1c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 646475377 1250 646474127 646474139
    0x5090c040c090e0a050f0406020309011d0c10030c1b0c0b040f06090e060d020f0325030506100f0303050a020c06030103230d200106050d050706020706021612021801 72
    0x51007284070354000f814003000025402161442154001d1000313020401141e04ca03502c48001070341000c1c0003050255a10f00862030b4030703180000103640a800030b0000d030a00c0070101040105d130ba50040c0070700c8245428000c0007117440e54450710005d00c0d01c4130010310740c18618950a0020034844550003504ad581c1e000640851000c00e8000084103c5100e03581e0481c4040d141c0300300d9031039070200307984d86901b042c0518a1400107103400181c04041703c2c0060b044880c0780791041c1c0c006450b40c0c41d031141e403440080924030030310070300800344500c90780140ca494881e040c05141114070440b1522a00c0050200000810904e030740510a010381c0d68408001480503031256140e0410f181c0c1e242c090020014034001074a0180c40000f800f144444042d221610b80910326096502010b044811181c40c00c2895542c8441c04070340750f5a070051031260f2030f014034000d199080c1400d03006441c040558000b00309550080041c0740f0313604241c4030960140c40103416440300000c000d102061001204101074070b0100e0101c0e0021400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 646476627 1250 646475377 646475387
    0x9030b0a020919060203030604020f190e0102010b12070e100f06051b01090f0314040e010806060f0a030b0403051308030a120b010e0d060c09030510151a03070305090c040c 75
    0x82e06002c0380c95081210300d107101c2e02200c0b2190f2082d4005a0424000a2014501030707014041c942410600645003c100022854020400d0551800401c8540c2401107455a0910801c03503841003d592002440d0320885289954825500c00d000045840000089070300e18829440c200074030215405025258480c68042c24603009403004400c29084507a55119403401400b68031481600618840340c0180380761411100e00090100d00020b41804000c0018040030f6251000e0003440b0502c0904000d080c5142040032451440c640203126441d40c01c0c0c10b001085c0c80d0001c194003c0c0e41420800e07074030794114862210505160f40111128080030441407481504441c04002400c500d480030801000c0440c019a45030202e1400b01d500314001004440000315294090800c8148608140045030ba40350740700d5151400c003513400c030101510350114403918854106080003a01032210f10a00072a8109903072240703404002c020908054540002c109035403024044614900c6002c1c0c810b0010705098100901 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 646477877 1250 646476627 646476637
    0x90a0f0614060109031109060102071a07060b040c121509050c19020106080c0418060203070c0b0a0b0d15090206130e0a0501050f1003140a0c0206090f06070c0309030b0a02 75
    0x1105a00d01c4001030103661140503800c05481e80214004800001d410503c00741860041c070007415403150010100d0258156103510040911240c01c0740d54490302464440305640d02c00301e8480c0168240200380b030030306070800d403a900c500041e01c00004052030b80d54001540400b46601c4000480d00c0e000c184206040304800910100c2c441c2c41c41d00d407a4480482d401ca08951031440ba114050b0400c801020091030141c101e0030410b40307081d1111003014620384488040b6442a105070b030100352000219000c10501004103940001800810407400d6442c001151545062507401007a01c104e021450128021503808100c000c4d40180009845000820540c075203041e0502690f00102004070008409410901400c3d050342c80c0a42000031401800c414017414209150b200814103071a40009028a641495104d20400103040042184456940040e0074442d010349076556680010700e003501c044074001601d40c0c00604d20701d030052020348142412a03c109080c0c10003802d900d80c0e6000d010340c405194002d02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 646479127 1250 646477877 646477901
    0x70f0218091b0103060305030406181e09020d1407030b1e0607060c0908060a09140a24180609050c060c12030c09030d08010801060911040e090a0f06 65
    0x103a84040300500041144804903911856607020300b1000550300100c4104005548041c140420816146d9440d54116003144d00b011002403910a0f030b9800002c0100115002400420a2080344800000c403c2c00448040d014144100390001420805002194021084110102c486002078240000d001300580174540e08030b8407640d1141080b0203001c050824018000800618152400c0c0d2140d03a454080c0400c8541042481446100000d92540a224452040520250010b021211407400c00c41c01014014000d00c01e500c10112000065000c0800c28042030020682c80c08095084501c803014140a032043c2441c0c100d01c40440c020412150803250300c2c01d10034826a02c681c030000060024500968083c1c50b0f2981c0a00c005808600102e0019a0000b04c90400503181054490229251059440d12100010420340041003603440038860700d130250540100a00c01c00060b03104400c101e000d01d008000300c136030455010460001c410407003030216079030120644135504140d00b0110700a0503192045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 646480377 1250 646479127 646479139
    0x7030504090e0c01080c040e0f060a050a032f240c01020406230a02060a0903021509060a0c0207061d04090c03120e0102010b0901060f02101521020a05100311070f02 72
    0x811510b107086d1341501c054030908451041e5a03524160441e80341d010203404503801c00c050b1500030405450701180000954003a03540598410101a01c0446044070b410902d10141d069a0018890342e861074075a0820311640007070000700001030420041c0038410f11552405e02d40c07000400140d61504890081100c81100c0407802c0c1c00c1c102041c0c08c0d590b0f44224480343d030043c1c114100089800c00998800080035000c2d1040f180708002102003504800070640d240e0b460340d070102c2d040201400c603900408581000d284041c0c0310442c41c0440140001010000142030390241c0502942d06031101e0380401c0f50290410b510303010081da2410144103045408062000068502030389810300c2d4014050304810090280c464841e070782ca4810101c400b0b040c07180c00c02045020784100f811199006025034500ea200c40074075030344058580061141e051a0fa80302c0d02e07140252645012001d0f81e13300c7c5609003202d4042c1d0306280000050b0200328014501c0c3d46004004110200e04403003402040784110102c82d1084c0d841e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 646481627 1250 646480377 646480381
    0x90601210e070504020f030103150204051806120d08181f0912050702060d091e080a0e03070e010e0c130905010e07180302040e0f250e04080f07030504090e0c0108 71
    0x44c04141d20888881d504412400c100420000c0c03c081d048200f400c43c00071005043c99100d000054003074084040360800780b10903001388a00e5203050310307070305000380c400000410401400080c081c240d0b000c010b007503640702c008a0104ca0f00d01c0381d091003403e040820344014502440e900d00c40c00002401850025503c0740081980212000d00420484262603001400141444246101070002d072207100011540c5958110b24034045101094006603620b100c0c0328125104c5511000042200c04114403452090303000d00b0302007000e00c01103004181551000c02c1c4021480d40c900c0c400c0310300fa10901d400218980c03044040002d410207950700581c142c0385d03114030303030001780d1100d1740210364418000c0c100082c0407040711410001031901e9480904c41d15a04020781e80110503921100307081c440d00c0184561301240e102ba0300d04104014841231400f46c4099035001c4420f083c5911000c40e140100200d1010302d00000401c403080c54020400ea400800350210248000120205029120300e08041c034140405c5003200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 646482877 1250 646481627 646481629
    0x3070911040905072a170d0506090601090b0304140c030f0a1b05033d0b0324130804050a060e0a0603020c0c040f0b04020c060103030e06040e0105090601210e0705 71
    0x2500c8079410b035842504a2900b8013000e41c80000040b081703011200040102c10341062450740070080c203218422003000113600d24001060000805000301600e040020401083c00b040007010706aa402503080061030034401d0a1040407890401744900050741481403010f1000c1c054400030303100484504c07640b0b900e6022214402403c4805056010b06a81500140e6171401071400d01541502e20344201065603002d44842c442a94540c4103500c6012080303601c60341740031342340d00701001241c01c490840c0c00554034a1002e0020340400f48001383c241c0c0d04d40b0350303020140d4041c0722000040c1e601030f020045c8400e5120b6035528015004140c14841c0d41d000d106113230b00002d030050017031090b00c2c40c7c80e00c21009820b54026401c100001404440840c01c4c10655414569000d82c841344090400300500300010b2229505500b405021209200c01721880b402042106210202182107070604482007581d0400003911480016520b0401c6101c46500e0410b0400803c00c984100b41c101c2c3c00702242c41425030320702a0f1610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 646484127 1250 646482877 646482887
    0x4060b0109060903121707022a01080c0705010603022e170c130f0608061503060609060304060f1a010e0915091806010308071a06130b0307091104090507 67
    0x111404010500d402e8003003003c50340c0313003c0b0100f07031482d245004500070200206d0450300910568134280140c0c8140d440000301104510515034030350181c02e0100031034411100003401c582008080046070704011030480100002504004080d42d03004110404e00307105080800b04500100000d034000182d0079000d0b804540c0101c05020110003141c85001803070303582c90701c100c0c2242e1280310301d40d0303402d12440000109460101a05406840d03d5990860641041c00c1040407407843c601e07041c00110020001d101c010369a1178101c6814080030f4401076101c0da514181b860051150b0440c805800c0d080000d01e144405100b03e01e000a0b0345c2c241c03036580c01e5082103014440300035012610701e04618504410030b44a0700c0d1131901d16a1001504400c04540d18520715420304000c42a030003140d0100021400100700000c5071f100801d40501740004c2801071526100003a001034541c00c03030400c1c466880545900c1501d00348480c0d4007500700d03001c0901000301d107444544035590141c415001842e2a21001c0b890042c410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 646485377 1250 646484127 646484129
    0x801090b0412050331020a230306071b0807060f0609050106020307030507300503090123070305040204020918040210090e07080a1401170708160614160b04060b0109 72
    0x149a0300e40380d02000086030345d00c0580036407009841d0f40c82c103040c0400680d240d400041c060304440100e0040c000021000e6881610480321043c071a422401c00c0103c416071113000c03400441d9003002600071103299410400e8441c0700300072020307200a0400103080c8600c0a5500110112840303a00c003042280c3c0e03900d4082307881e4000d4100060002e20100320080104070848012001380f14400c90310721580740c144000007050b020204080000ca8004010018092030a10445c80341041c020344c1001000108010460f036500c004000c04241a03454010070159202c03641592010203000d402d40b09102c072410604a0a2002100c041748113011695200c40e040348541074040441c1d05a2034442003580b25190f05403060440207226140c0380c0d0383da072008a103c90420082da402048a42080e001c8400c2c51500705085c000690040b4003aa03202c60302851044012220f0801210980c0c90102040c10180280c3d6016101d80c0c510040704801100d0f02c0c50501c4102d0500d180100e12488080210040e01c41c010340320b801711 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 646486627 1250 646485377 646485391
    0x303010f1205030c030a080a15060906031a130e011805060408031e01090e0f01050108100213050603010e06010801090c1403060609090103211809090302070801090b04120503 76
    0x1488004101c103084070801c1420310351180701941c1c101003c91402d030b0700d1600b050407958001800c0c54280070440c0c04501c034100202288031040301c4640c0c10000054201c01580c03150b0340401d0342e40e290f143c3c4a419100304804030f281d00146107e41c01084007a080c2e01070542820040c44035483d0484402440320003012810ba40d5a101000d85441da9440e2601e03040c07900010715000b1144000b00c40c007001040800c0a890103419041c10004540580201c45890050050145540d9a162200500825000140c0c64018220046002d81c0e180740181070480b01142c107901241d0016000300c008520106031010ba10b120300320a90392013500360780c0c1e070558809a401214000011502d00c2e4480403035600f2440c004d560006000c0c01003454800d00001141c28460240e2050f80c2c5903202d201d029001109282c503240040c07129180201142100f200e800322824010f2050480c0c40b82c1e241e4550382094000e0240030020074642008000002c130301d0a008030300803c00c85044034051010313212103940c94019415030780071b0303c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 646487877 1250 646486627 646486649
    0x20f100501180c120f060929040b010e03070b03071e0804021e100806040507030606020c130e160315050f180c0307031a0703060302010f0804061806021803030301 71
    0x2d148402c400100345210300003081100c3c2c150001007400c4a40035010200e002014009002c0740f0b41812042120402c0c3d800800700202d42005d0300e209803d5401e07443c042001207400242c1e002a510040c3c402520907c1c610390180250000010340318800c501440c450811a100d10203400c00d00750080038000c0202480344042409180850058189444042d803142d24070000204081000000500030784030718100000020290b5081045500f081d0003403d4002c2e4481c20144055820480065200ea15807a02c1c2c90050344904c1010388481015000301c00d00038281c8058480107003030041c08042c0342c007680c001600d18039159011400c1142c100d104039481482c0524070000310f82c513002412200b0b641c1c1036002d52402e104505403401203076028801e40b0300541c4682410b181a010b0502d2800b0707400002172110003854a400d0040003d41d030000d10a0240030b8141c1f42241e150b990714a0408000c1601d1250110024000c46100040022036402040c840b0180501c0c40384100b9601c040560b00e01c424050142c80d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 646489127 1250 646487877 646487909
    0x5030d0512101511030f0c030706061e030f080f0408070e0603070f050d0606030602040f050906120d0f02160b281b02040204090203071709070302030d081f06020f100501 74
    0xf030701c07078040444545031100589142803283d0140d401203404c505001000c0e5000051080d00f0083d2500c5800001c100007090a040300c807172815208001c01316480040c00070310300d01e6426400c12056100300c9a1204c1c00000c15034131192140078141d43c80560b40940050b200c04d4001144283c500000d2002c04c9904401b801501c1d141010240704481c3c1003103404480781512240c000c40000d00300d0010304091306041e101174840303c2c80c25040000f05c2002911050044a0340400c2000c02c82c8040342c01000c3c1440c0f400c0104401014400c101c1c60705020a02d03400d042c01c4845030105504000c41b00070f00b809114001541100c460f0305040f21907120007109228042007003403c0900318415000c101c07001450004200505060ba2030341c001081ea0310884803900050840b645420590040d40340540c1c0020461008011250551b404030340c1d20044441c070101803080c82c00c0000d20302e846c0042000400080220400e444640d00c1c0c00c040d42e180420f9411580764020100480a81c11003482454121410795410b001c1d04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 646490377 1250 646489127 646489169
    0x110f06070f050c010e0d09090b091303050f0415120b0a05011101090803131b08030405012d0c0201092702250c030201021506010509040509030405030d051210 69
    0x390318407020440c01d1060520160900d16400c0c0700b9002117610b2038001c0c10b50b4011106d4010048851900005151440c010300081320751a400080b690214a00b0b0002d910045a800d0541d210302880020000f8603000080103d0900510720070640d0b00303400c5448400840c1d0390080c0c808156003490403015049682c000d4104131a40c070552080c00710402c45400000c90258549805096031b104135804142d10700007070541c0c07081090900441e68298013042000210034117100405403684103a00c641810403070200044118203480245140d81e0f01160484d00241c21182d20016006c5001c00000368045040114001841c886040f86420000e866142107044541d0b0101044000d420610181c40d090f0a0b00c0d101020407581041d030f40daa09405448074a180a1a600c0020700e4980340c0d070404119401c511042c0700c540d90704201a00d1301d1950445002c190b55440c440340e00c0c594001e40e4000d0760315110b0304814604103a0400f000f40038045440c506038546994401040352100198412a842d042c0064104505 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 646491627 1250 646490377 646490387
    0x90f060c23120a18030e190f0605030601030f0c170105060f0a03021b01050702030c060901110403150b150c0f0105010e06090414030703030618062d030206160201110f0607 75
    0x80014140d10005107108032444c0d041c5241c103461340440218a4080181020703240c56600c0342d02205061a040016500b00f420200711215244100010f00c0008408100e140e806500841d0501c0704458003000fa1a50070074001f0002d4100c80d1281c4c84101ca8000085a2401c0100032108034a41d04490319290042d0418110020350011001000303000d110b1105118542c405c0c01014014107042d402162529507148900c0d061a0002c4c040700402d03890031014406610088090301c0889402c0321415100200000c000300c00341802040e80e80d44101190108020458450041c0c16400c0c1c43d40100c6503078840307003482c403401c81e2000c1c051180d001d41410001051403500c29140e40e0b01c240b04001001d8088040800c0526541202c1000c5002c6515000b080c0000c0d00d6145441071514a9080140a082c2c600112140f1a152404640c0d034019001103406440f40704004100005641c007901003036403002640c3d101c0e095030303501103c120300041c01141201521503002400c0300c08048100d020b005103465400d01a11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 646492877 1250 646491627 646491631
    0x180d0203090d0602040b040b04080d180308090105130b041502150c091305040f02121504080a0315032306100e19180323180301090f060c2312 62
    0x444540801c0040b07403010041011f000284000b40503030380c6541c1082540c130709250709000401c0030081140e403404442c0c1c0d00504401c04490300070800a990b440f44900495140c4621a800d50b0316420745d11000403940300090080c022598a00c1c050189c040081034201d86070201244510179000a0b0b001203000030070702c0c5004244071000101072000000c010110b400a0b00d100312425180014103851900541c01c2c00348000c0904003c1070f026109420646210003600301e00a000a0581c0310003181060300749005e0381c03000d2803c452042064240d541d89140c403074003000710035501c0c410010101910400a110024403140a0015500030701c190030700303100c0b0b490310314003008104503900188042c004140421610a84003900c90380104205104031500300a0400c3c42040c04100c443c1d40107200c0001181c1d5020140c6440594001d0400d64040d08200041c1c05003041803c0074000c01404d910450811a00e948005140007560320781c141e41020044184480101503000c100d0b0800d010002c0c80c883c0031118000c3c82e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 646494127 1250 646492877 646492883
    0x19140c210705060903130e010302030604060b0112060f03060608030c060a0209010c0210050711030c1c020d050313030b06030c0d060e011113030203120a05041502150f180d0203090d 79
    0x190a00000740c070356603c0c0000a8814141e5908001007030382c5801c950702e000f100908803001032070103a5407455010a594281c01031016044c03540c2c0e051700c1da180784c0c400e071a030f270020341c43c0401c1c01e010b034035194203401710102001e1108490300e51500a001410050100a407850b00c1103041c0034144a548440e08140030b94004101e01c0d04109588603010016076030039031100d05103c0d80740d0394640c440509150207808101000708051003039100c400c10400903999130407407400640100401e40380d00042d900c04180b2041c0b005900418500010900102e03a428071060001103d000d41c80c44026901c4000505d5210701c111070440f60011501047c00000c1001c80d000490403144103c00040e05810a5081e810140c019200c0c02401180800c410420b51034101f01500c0500080b891140c5403440380d140190140c492841030217a0002e190781002c0c1080d000b801034198141ca400c4040000349428912060a0b440446803000d0504100c5131108000c100090740300c0440c41203800440c5882c0030f0707808104807150301c00412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 646495377 1250 646494127 646494193
    0xe0a08060403112d0c190b0c01060f120c090e03070803180a05010209100e09040b040f06020d0b09070c17091306030b04020102190b041211010219140c 66
    0x10340c841004052070008000402c0e84c140071000080c981e050401a42c02c0c801d81c46030020000c40d0310303240d640c8940b407000c0340c0c00b580c0c01955480c0e03902c0c0010b000d000e80764840b105d0302a5048001540c40c54100f03640c84001d219401020495882c2c01f98981202c00c1540001081d500c14011280001c8802c1c000b5038000200301e100318214082511640d14008802c0303401c541c180d4001c55149028100560b40030341340d070b159081c00c882272403803600482c5542c10000c01c044c11149a101c0800c05100d55500c10305001ca030026400d40d5a0030710290700501030048030414501a1892800107488103104c0d4a0308102d00b54031003501c00ea011031101c0403035026080210314590101c550070218800703004078401c20f00218842c0d220b161007440c040c000a400d101c0d103420075540c4200003608500020340f001c40c000754030603803200d2105900411600c0440c0c987c0b00c44030b84031146600c001000c80b030b2001c190340e110008400d10798400c04414410b102d07240303141c002c00340c504030307594000c59008811903500e00003034594050320045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 646496627 1250 646495377 646495393
    0x90903070f0807140f0609010e031914040e010302030601090203040f0f170406080f01051903030f020c0d14060903090607031110060b03090111120f060a0f080d0e0a0806040311 77
    0x611103045400743c00c440551741c03200d14203410640080c0015540306055000070000c1c4081d0080c016100d00c21a8004100440c0404510754120700855140004812079a00f098640342c43d0014060200d2080c0002e81c86449000000600e0108130b0080300c0c40f03a40d226840d01c0001e04140d03a8015200b00c0d0110460b10b00184202c0c81807400e10420242c0014901c6a0300c104003400e0500300d001e9619810380165000d0005041051803000120001038100c2e0303410f15084c10f1144d0000340403411b095103410750740c1e4010485003d50090203010710044545411910a80e40381d91940701600c0e940f07104815000750021402d201150110340031f206550342c01c110b0360040e6003200304455841801c444d042d811581600b4004024820b010500b445140d180c04d02c401b415900c1c0c03115408080e581d22400600c0b001940c16050000b4041351a0012690001c107112072780d80207980e031034909040c5c9030101511040001207495140003d50301d4030f00304110455010304090300c0607850700c1c0c4044550b8949143c41354014030407005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 646497877 1250 646496627 646496633
    0x9120405010e0d11030f030703110a17131a091906140901030207050a05030a08160824030d02010e0c010e10030e150a05040215360603040c090b090903070f0807 70
    0x41580681c00300c034405140d4407412850301800458043c044c5000d22f5001c0c4101074002203d0614041c03d415044010a468200c12440c01414501503041100c0c068003010446401c0d035246801782c081103104561403140701003036504140360840b80f03128900001e10b450802c0840d45900d64020108000103140c054030b4249607480c2d2a02d0010020800c80309644009000f10885030310001c1c0542091080740c4802c0c8018a0031401407503030070040c2c81d45441460075101540d4000d20700300c0c850144080a020b030343c2240703400a40603000f0496540d4045c1c81d40190502d000156104054a1400d04030052580f0026010210210b004200000c50020300b8480c201008002205480e8414450340582c1804208d500e414410b00002125612080002420a004002d1100c3c0f004400c0346610f280981c0d1111070640491b1504885d40c07204031366503000000001444103000d00c895040d4241e4080942c2030069165520500150500c02ca44002071178000740401000200160700c4803141500407251941080c460751 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 646499127 1250 646497877 646497883
    0x31e0807051b060411091e04080306300105010501030b0d06150f090213050d0203100902031608060a1d0d0e0103060513020c0d02062e080d0809120405010e0d1103 71
    0x50f405031141400d1506642e050300c5c010f4075045e8040d500b1000d03030071a00c46200382d0441f884400b5000504d071020100020f480c07030311944151070701002240c0801520b02185003000480c5919a6070071541d55007032200209440d40030b4001c103205580c014080700c55400581e11a10004c0100b0400070540982c04d00001034042e80c912910350192141c03807030060766402da5044044a090060b40300c075028648190314840969070118041e60500314280b03010864504520000742080302c4031168079440100304d078003c1034020000508910440e003180c020031007680c0d0b801869012000343d6101400c6940030012000d0014806d80903c3e42101d018100882c0d195210000580b030041d07111005442c095000c079009203010f0080040c90000703c6036002400b01401d0850403240b0900107070310309003480a41c3c0b51103040d02030301e416075590051001d04296100c10480904c010276443d01038954070f283c2e2040d00385115810b01c982089504480050311848100342c09401406042c810015050715000d80840c0e409042c1e403424 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 646500377 1250 646499127 646499131
    0xf120712030215010608010e0f0a061502151528151214010305101d01060e0108060c040602100b0301020705010504060b0a23010c2d031e0807051b06 65
    0x80d4001d03001c41d0f010400c050b0f100c06816400001003004100040000240d0440c105411015030302d0400d501d55142c14829006d0f1003d03500030100540200c6000c00c20503404181e000341e0a40c00301d403903e40340d194400191031401d04400340b00e0f07001000c6060b403c0b47d501800118001501486440b5034115520848514541c0c0e0008403c40860f0042c200a074192115105822070260a20a200c0c400d50444e190b0703d54400150741c0100c032056807407000d001881c0091041c040741c01c2440300284602c503101d41030307003030440000c1c4141145481044081048007a0b200183c605446c410760080942c0d81c4121001005003c0b2043c2d040d070075541c03c00000000c52003e0040d01c0c499409000d001c03811158401c01c1c00411400d95100c40c030420280404801031501c1c0c4040114845000d281001da08030807818410454003203c40071303800300200d1451082c0500c4007011070322083c4e4004e8580c002d01000c0c0490440b000011514200c00040342600083d0b0414003c1c0060150002d5454803231455000c80f1000314542101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 646501627 1250 646500377 646500383
    0x3060524152d0d1116060c09050409061a060703050d230411030c04090812061207030c05040b01090e0403140c120304050106080f0d080901020702090c070b09010b0f120712 75
    0x50301000652103801509601e42c0c242d4035036817800e41c81070702c04c0c0070005100000074501034507104504011032084d044d18005d04002402000b1420007480c1031030050004a00042e4514810030b00810545030440a555011750592540c0d46004200c00040d801068040016942c3c188050092100c030079044c50134503c1380e44580994100800000c04241c40c0242c00d2a4a0f445181004603d80c001031807503041c0c0d41c4000541d60301590640341e0300002102110a4a00d9841a11910800105200c0e00d071400d80d00300c40c0305440400030300000d0401125a00c4450051043c82026100450001392041580c016001c0c0c0300900c030f500b0260380b00c0c101810002040d41d03403803040502105104c1840030038400e1303c004010120042404440b0303100d079952107410715a5441c041c08580800203100b0b88007034048540755940240016a50318154810b00d0792904541801e40c0d2420020b00051200d1405200d00700c01d10500800745028544020100100c900c0013544082890160420001702c0801181c20080c58900c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 646502877 1250 646501627 646501717
    0x30a1a0a0603120e0109080616050c071a0304150203040b0103030c0f0605070f08060d03080c0a02031312150903090506070f0501061d0a0225030c0c0306052415 70
    0x1c0c0034130004240070403981184085402c0390f0107200700c2001c0c000b01c4104200c010306110303803505043c040c1d01c1e082c800d482d4001c0c0c10304036884092071000440880218820386c03042100c10701010743e20050030b00701d010444004029040384001031010034040c4840e201da00703118001a4000c01103507a10344c001d440c0c05a032043c0200703014844191007160040d0400380d201e20b040d00c41640b440001d860041543c0000741c1030a01c14071002850310055842442121a9030310102c00500c071a95580103030b5529002074403020755001b00c0d000c0c000c080c01d104900030401a03603095950500320900702000c0000750361000c0001c035240460700004d58000340702805098018086442c0b0801048018000395500d20b2005105110031881003000201103060a0a1070389201d51040c50900044074503d0280c4039407403159400b41c40d01c00c00940c00400c0201036080303148100c4104004003030304124011031044154400c00d0310b541c0030030042ea408807600c8114010780403c1401180c0c030103280124114141c81c548030400c9800c0c11134 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 646504127 1250 646502877 646502897
    0xd08090a0212060a0f05060303040311150703021f0b10052b050103110102060702150601050d020d050103031107120b1017010f1a01020a061d1207050c030a1a0a060312 73
    0x10090310031780d9060b22407000144914074149001035100c1c42540030003000088000540049a10380144440240c941050a00c0e5550341074200659103d08a40c03a42582100245981880880c103001c0c0100d000c802034240030482401a0094805400514004883c5030080c1030760740603d5100742c40b00c034044c40d41e0080000c4c154110b05041c0380c1e505000303c00e0707819580000c080c01075032a400508841034a510020444039030700c951004840e00c0c490042900b020030700218002c40340146540c0900d04030f9129071030f002d4807641c080d203a068032103d041c420030310700700816028000800c50312a1402e900c000c892128019454a4490103000030300c00c2040e400030390795100243c243d90443e500c182e4108074803400d5150030702c4032903100003544c542c2c003404020809629007004d049130300d4546119001d908040d5068504040c941403d030000c1c4d0700103800070b40311882076800c050f4043c01c000c111410f13459042142e0484100502c0d046d482004000790880540c5950391200001040c1c0d030005c045000034203a56110050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 646505377 1250 646504127 646504141
    0x2030604180b280207081905190507110d061d0d0207050904020619051e03101503060819030314132301050c040e0f06030d0c0c0308030906040c08030c0d08090a021206 73
    0x700441e01381a02c144041008032112760101c180760020640c10619045607284510320b020805103261901280e044240400700c40f00f04a40c42d0000e90107100359158045d50f080c8a43c6c04039a4640b0041c0528001da0401d8506100c02d0030000020707540507002414862501c40388030724101191407080e107070301c1c002f401c0030a40c61066a0480c00d49543d40c0e540f19106402d50134601600c0750581010b10800c0c402003d002c000201d41e42c025000710300100540340a840c44180c02406803a154a038590b0300f200042d207003041c2503c03a26910081705001d034048280c5032070061180da440c1001110b80d01c0d80802c81e410200d1110714280d00074040c90340309650407403d2030b494518000601398000b20240c5003000d4010799a00700465a14001404200108180b60804160320341342000440c1c203030325400150010310000108004588001801c6024910580b40c12180c1a629100c0c0e6459006130050201581c001c01152012144a40159504460540107560841d000343e400540105481c06550882c0d410800400c248 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 646506627 1250 646505377 646505407
    0x70503071b1d0c0a0e030d02010606030f022802100606091a0306010e06180d21090308070b0c0c0102030a09030801140609060c030903060a02030604180b28020708 71
    0x2c00c04103500301c02c01c0001068449060341c0c000c016504041c07011072503050300c901c1110b5609400d03201a0543d00c9400414000078042c11880c050350020a080101d04055120540f08503001502e20f001110020250082c034000d101414654a404512a14903501034902031031140e9002848140c445440c0a840d0004507040300c6107a00340031031001401c0c410890380c0c0c3d0708000e1b440940360040b540c0d281d41d103001c50100c04038150a00d050750303042090801120100918203002e1140340d5140480080c9000090303d00b180c145a4500005014003811310041c000140803202035a00300c104c0e9001c0034140000d1241060890b003044a20100b41e0f5120300f400310901d078100591502408256400c020303240200d00110f071861041614980c010480050801c7d5078180c103206449915000a041c1d40c01c6040010403003010307402c29140d42c0c1c0b2a900e4410001c9010700100005511168407054000f9241c0c1c403510740040f4800100880240f61005030040c072a120401c0c4000c180f964440c43d50707540c13034000303032124100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 646507877 1250 646506627 646506629
    0x3050403080c0304051009081e120c0301230d170912060903070f0204230901050105101202030601020a170a03050c0f0417010618050106110d081b070503071b 69
    0x404440200f0501c00400c0000c22413521405081c04045803404151802041d54840e1700c030300118050344615101040c00105006100b009c81d0650508481d4558034454012803001b071241c1c4103224188207e50303081d081d240025900b500e40c000c1040042001c2c5485080e402200b5007144007170b903200028049460700e030520046590149100082c1840e141008525a4038420684068404c4290707111007001c55440d80c000701c6024926040c4085260000e03024052616002c1da1429034035405c0c80004146070804201d2081010351964910003501c064070382c114025440649000d04501689120102162026080042400c00c42c00c0c0d181d604d284299000f8101d50010304000803002040007100c0440e5118000d60b0705461102a40d40c142160740c000d00340c0140101c2c1d02c450354010311f000400b451524640d01c41c034100c503100e0700c901e11001c030020170054454105c4049a0046401c403404900c08081c1c11310804021304402800341c0c9003140340c3c0c545910719046500304a5a03090b40400c4e0510003000e441a400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 646509127 1250 646507877 646507891
    0x100605030d1808010908041e030b0711012405011215180b1806030d0212030c13080607021605040c0816030b1c03021612080f0f1c18110411070507060305040308 70
    0xb080c0e440c11030b52b030308000c0d03e0040d100c1c43c02c00c0750700c6070100000030080d072024505504600b80213800c1440004805200c60306e500c1000d01180d10030300c85d000c4600f264019840212000d4a080301e87c1418070700388100842c4030040c0c001505a603025030215603180c41c281031100200e14042900c2c1442e0032020586032100a014540454000d4030b82c200703001c15908140d94200040703c000c16107407402c3d00c816450054160780404074504c60042400116500481e16230903004070b400300c10340e26648400c18081522011150f05000500389000180e20b07603040799488892000510703020440d05140c400140d8010201c0865a918038422503506d000c040c1c04102c101c00381d02031200794204d81445c2007040782c04641041d02c0900300b82c4000810032000350440e03080710401d4a228140075212050603140015112440000d4000b0510b081080c540050761880120305090340032141101e01b040351030502001e080761510403e100c180501c80074001440c140240e05c042e250a0358005414a400e080c002c0c5600000ba0582c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 646510377 1250 646509127 646509179
    0xe10090e0703022b0204020a0225031a1501140c0a031115010e0a0903090e010e0403030e010209060405010c150e161d010311010212040602030c100605030d180801090804 74
    0x650800740349000100e000d139011600148c0704c2544a40c26420408084040509640940c00c0050145604800081030724040c0034841c400b211140603d440300901981d13210743e0109051015880703507204903078800c7e03c101c1c0ba1742c40c0760814590f120030900c0e05807903500840105409001c00034445a04220b00100c003134040d006100b01d07525001104103443d401516840c5c00c1e036100d0454030103050107192040010710034038000020b1503030354080e40340d200942a40d048000030b00300b0185284003501402618000c100042c96185458030302401940e952801c00e03801c0300c0e0a82d41c0e80005200d1039507071007071107003035805400500f1511902c4104000514880d41105d081641e0910b60310030460700d10700e400c505407a4070083c0d2400c41c0c402100140d2a03d000401685240c0c8000200400d0180e80400a04010040304080314021001a0080c0094800310300038660954007255030402064451000e001031413602c0c11541c0c078515120f409090070b496011805403000d000000b2708118051042803074000c154980801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 646511627 1250 646510377 646510429
    0xf020102120d020a14180d05010605060d020c0c0307050f131415011b0c0306020c030c0d050a030b0315041e141507030902030705040b01030b0402040e0601270e10090e070302 76
    0x3c08100c6c40491900b90180140e1f0940c0d408001c400d5120002408004203c3c0c1c1c0c464030f9101c0f00070040e5101f1703c4148243e0050124221040c24001131407030a0b514010844070300c08100c00288428032945038181500d01340c40d0303034104041070040e00c2c940340541881e041c0042104a00e41c0094100502c0780c0c221055000b007400344002056540c00c2000c2a6030740500d015030b54014002003035165010f182403c039494050041c0000845800600608a264658800f40010b0381814205905c81c10b0f19400400350030a008009800520203031918016100000c52601c07031601d0f10b40780c0c0003060b44141d40c032426541c0401d04c510300f0b00c15110740c4564010120718003070011014680c0801d0300e1741d1807803080500035500c540030642d840c0c4c0280c00418001001400071074851395200100103180b0700c00d0381e580c3d020507001c0b00b040318030718030b46000c0300c903a1100713a007400c480c151600358070702c8080e00c1c010240d07240c4502c44100480c001d41e00d8050004180e008100030300b085801d500410281551484084e803c00001c0c1304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 646512877 1250 646511627 646511647
    0xe100e16031b0608390a030f0507030b0303030c0a091503060f0f030f0b07260604050105100503041e080c01020d0b011d060d0f06180e0c0d0f020102120d020a14 70
    0x11917004040d42d40c0040810400c005100300640445403280b84500c2e040128a45801c19416406a0b4a07034180d40401e216079281c0c59407e5045403c0320031291b0b050380041002503500e070440001006848064078000c580542c1d9104117000b103058002d00e010000e62581410005c028600760002c0240c07502d240c40c00e4082e440d683c3d50442024031107400a07c10015100010f82c0c41d80500d038083d030800d9404014169442030352070842c603002c404480561055281800200b158100b100b8020f4824840e9180c0c01e2a40d120ba444849000d4110400f0301c0003241100380c240f00042c03540c000380c02cbc061f16440025844480c0040d20106540c80c04110740e042003001c540a14988a82641d01501c580d0103682d84c599840440301080b02070a80d4440c0e0000300f43c2090400100c01d1a041d121140103050700000f0859084149010782d1981c00e09070304103500000740e0319008003292500890f5420940b050040300c810385c0000f55405001c0c0c200b4030740e6440039640401c96005150700300342c5086107020070703804140c40c00e1500c3c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 646514127 1250 646512877 646512901
    0x50705121e0117070807060912080705031c2406050a030f0c17070516110609040e06090d020f07090e0a080301081e010e100e16031b0608 60
    0x111210105495040401c018600c000c0d1044800d40414000c0d03142580c480030506032202c00b20350403d41520072008000360031100030403c00299040359035819007541c9804480c02170405012070660b00c86504002d1400040d00400c01051812400b8041c41d040445058000003210b00303100c40802c0302600f0180345451507500c410124142d0710281003003a00d07800100022001020080c250308901442d014105840c3c0303400c40b542001c1c10b0941c058910050391801e900f12500e00601d4404002c140003043d500f40003030308841049205810103060b0505040b40d810008055400035840e0394016040f00f000e001d0020420301640c010b80005000805000c5401001155521824420003810355030364401030f500c000d003c3c48031140250304080355a86951f100c8640e07648401161549d40c81103506c0034241f42c0e080c0303010300030080030030b8500b0b0150007400b180e0025000070380020340f0031145d1400341c0c80b1076070344d54020381780240c02541c040d00401402055040501001c1d0782c841e0000030610103100108203c1240c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 646515377 1250 646514127 646514137
    0x30c060403180b1606060f0b04090b0414100305060114010512060f0d030206090106050109150810050307030809090c1204110a0b0a031e020f090d080c010501031a0a050705 75
    0x1407401d006220301c08920000071080d6500040c4000f9030010f800310381c0c8442d00301c016640c607020b00c5040002d1617584a4032815110107104000300450b06102c10829200c2c15072203421920009000408d410500004440c01ca06c000c503002d006903c4100002c0c000d1000410529001d440a180c02e0103119640d000040d00c43d00803015003a84090410340010340503140d4903403a0404081c050f00b601c2070084245030103501c880b011110b0182540ca803010001d051762082c4480d404840c40a040b0507420800c21070300303d0b010840180011000c8144400015241e2000c00c803520086001e400116119222035080040911001d0541051807005010030305d000009001815040340e4040307004d0188654074008162a01c990754040218010702203440c0a0341070b099004409043c402d50807603000220300421010407801611000c141100c024800210182003602c1c0040445024090450130211101081429207078241c01c00c07208809e00104191184101c00e22140d00b021b02e0780c9041c0401d00c1c184200402500131 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 646516627 1250 646515377 646515383
    0x7030f0e0d0b0603010207121d0a1a030603070b0c03040801050c030108030a0f031b110f0d020c060d140108150f0402090a0207021306081e060c0f28120e030c0604 71
    0x1145000c03d1a079a03003541140c605543c400c000c3d040e00700310006c0103480c0d8040301c1550b0220100104602235240f0b45140d660040d184010342e550b5420124684151071a0002402140c05201c0c02da404989068030101030100d03510300300000d40d65a070070071060609442004e4170410041a042c00140426400402511403001c0103203024003104084010407400390400708a00380700760807484c2504c0038040c2d006030450041c64145d02210042041642342e650faa40c2c803c4095401a000740c43c0c50406460060b00500100100060106240c482ca0903400b00a04003a03010040c941d02c0848440704099511044a900041c0305010024038a0260041840f0240080c0040034455001480808550301c040905d11000030f604020400ea5450b100b95030303582ea202e07910618241100c0c00070f1060030000018064440c2c41c01e00215820828000070318211030b00403c2c034490410109030351429000c02c842c0e41241962049594a100c105811601030049443c48441e07040d20380c200300444c40c41d0840004a09130071130b034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 646517877 1250 646516627 646516643
    0x105090c0f0a090f060303110313053102030702070816090906020d050411030f0705180a0e0d03090314121b0910081501020c0a0303081f080307030f0e0d 67
    0x4220000500c050300340f038005903c204c0c079000101840d04400e034402004d0724402d480b03500007000c0d14052599240504d501c000f0308011070401c00c2c4080c0c20549030b400c894031448550004a103403548409881141440302c0240020f901104000340f0590400c0004000c0041d4005040c0f0803030985002e01c0300e4012402140303c03c60303c803541c14040240d07603030403121482084071040100341064a80358406801c04c0c40c802d4400d12858260f5086c0c04404039549045807401031992140758000f8242c2c10080000400c141d501e03e80d6020a510000020303c002d40c544121070360b000605118619010b403010071107a2052f92189010320200c40016042280c054000202500c41c1440c10b02803100070880f4421307000e003035400502070410340200d2900450350b1030050b015201c0e017031039140c9254012a60380c1c0e14010080c2e84240e00b400100b000c240500304082d007000e001194609030840d00446200d00e1011a404600d0560000510300d050603480980c5103209012842c050300004100320004401d5103404501801f006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 646519127 1250 646517877 646517899
    0x3032401050a1110020f0d050a0e030d09050a0c0f0617070e06070507030203070f0e06030d021c05090913030810151d03071d070239030a0c090e0105090c 67
    0x601c00304818000b034400c0100640d590312003030170846d076a6001b142013103c41c1410200804c1203a42d4a0103225052142da02c000e504108850b00701310090207125005072181d0182554130408a500c10021102620101c0700ca101032601d81302d030050140d202465209110410081481340303d0ba0b00000211040d03004130760082d100c0103507081007818012290300c02907042c85030394400078042c2c45042094046442500c00740099546502c1407540f140c007100d03c030700d0040c0c00a80301900002c100420303400b42d0303001901d051420400e618012642c01001070321b948450124101c40d2004040c0d00c04140d03030340403648054003a01646050303207004002c400803501d1010300c0580d005c001d4442c0c8084d1451402080c0c000e040720111960750a03031050040d90440c556451f884124001403005000040050940080382a4400b03014410089600320146042120540b500414542c46084d1340070881c0180c000d010301c02c145040d500d00b0b40c40200b114000c00345140720f641804c041040000e80821005522007040c1c44503103840c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 646520377 1250 646519127 646519157
    0x80402061603020705120a05030403030f050c03030a0501140d11060d020d1406040c0504080303040b0c0408030a200d020a0b0403020c0306151801230f100203032401050a 74
    0x14010280c1481c902008544614281030f40000c0c0902128001da504034418404808929154820400050800c0d4030402007000080e00c107103040b82c0341400c5494198182180001807500310741c01170310310124803902d42d4018041c0e4450003102c5040100119045910701086ea031360350b001413903041c4001c0d100f2800030503030700b42101441d01141c0201c44449c80403c4105156900345200b00001d46066004070b140000540207240a20122010754522400a505594595880903150400200030030341c071007024000040e00c48400c01c05844440c00e50b8a5480e84070941682001005a0300100c140d19540000b8038808202c1d00498200d0390b20742c00c23080101c00b44d03482d030071706a2400e080d040c512609441254104002e080d1011400703035103442d013200c0340249140c801599808109007030103803204070714400c0140c07179605004550102d090513000c0c1c1500d0b51140c0910028004c1c42e06144441c0141e0000000c0140e0380300034440f00303501d01400142003403424905400003000b40c05403079440d10601c400c04101c41c080d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 646521627 1250 646520377 646520389
    0xd061524030b1c050609060109020f160c0317071709060702060f0412121d01081305010f15050a0504090b040210090810021213110409020f1f0206091b01080402 70
    0x40819031000c80c00070707020f540340c65540d03100212130a04aa006520000c1610f40c0e0600840303003410340c50032141d81002c1c0d00d85103419103046030400449191601000000009481c500c04024030003144030880e490318035504080030341182c1d1207070401041c1820080341905a542005855220347c0644032181c696442c0d40604009104682040151120b0301841d201040f0140d102c1202822403551203c43c00c8078194148143d10802d80c003160f022400e4440015041401e1206c080c2c1514020000802d00480c940820070485000032045200d202e8002c105000c00c0c14192840c0c0003c080603202004035603520703241c40e0010707600070740024445c1c510300410701140303446002c525028058000135a00c0c840101e202100c025444038180b0344141c10102c00003020344617020950300415030881140314a292240080000034038404408a900000c15000949142ca9442103022944401503e04480c4414424041c1c500800204442c0f03084c2c1c420f20200c0d11030f8000711441480644203081050698541d8400900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 646522877 1250 646521627 646521649
    0x1c0204090203010906050601021c020c060a0302120705030603010b09160509061309021c1503060c1205011503053306121e07050702030a12030b0d061524030b 69
    0x342c15801c0c20880010b0100b1a4085805840240c089030060070226060020403e0403498920142c4c110b01c502c1080d60030010000c02001043d031400510f012081005964202015140c00c0b00190300030041080c582424420140100c074110341515030751904120f0305c2c10131301900e43c1100801c6400700c2e920440f41c99040640e42103a00d440b801035811a03c600905009401c03c5260b0301e00640d03400b00e400300e160228480e00e40307000b0440441c281c100303080d912900054002d1103103480810043c080303141485038842c031405002c5c7c00c1020400c081041d60103402800d640000e032078460690480c1d0110300c040c846801c100b00c2030382c4001800c5801c500311040080c895001e0320111082c1035150100700010704c80507801102007032051440d0001030ba203461104032150b00a1307020003500743e401121005c021888501c61403071a40a10314020450104c0382c4085a40e1040420084414544401c10b82403c11207112008002d0407510041d602600e0302307201481205944803885c030044c140c0e5000c0c005e200d0b4a414180007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 646524127 1250 646522877 646522879
    0xc0703020a0b09190b0a030e07050a06080906070201110d0b01090f1730090f0a030b16030b060405090613151d0403050919030501090809011d1c02040902 67
    0x258a0355542a66074801e6000c4402544031310403282c0a0810410300710078040c00c1d21901418a800c10071689810b9008000403009494180310303c610001f03d503a40e500e090005804265200103643c10a070414030f103803d01c050128420f69051485600c0410525001c1d1203000c20b07403200100c0d01a4001005072540203258200c8000508059070120b065115034500306000c0c18540d0840c0c0a491070300c0d00f54424042a407010410b68900d14513410205400180074095880004102c0c0136901d0801e000070b0391680701980201c1e0041243d00401018440d10004000d5109181c00d0600112003070034009001d5201b5806418032076040d20002c04c443c2d480c1c0101c01d00d810030101c0d03c200a2072140135010b21064400e4803c0c45d18460b4210104080c80c00040c03150b500603030f455180c003820800410204a01241040b042c0c8411007810000040400e0090003000e14a03070144001581d29082c3c2e5000501c0c9001c3c030b418a541801c044c03040110540c03600da040300618640c00e01c150303181b440b8510008001d000842c0d00a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 646525377 1250 646524127 646524139
    0xa060308031003030f1707030905070e0a2a020705010807110a0c0510020109080403060c11060a05070f02151b1308030d14040f030c032a110a03170c070302 68
    0x7020008403042c00409580c00f03915403064020b2041c0003140c0803605c2c240f111100c441d8000110340c2260203608a1840a481403003a102c6075900c1c1c46000303078044805c41c0d4886c1d69584030361100c0d030311062006c110088000c62500203001082d458501960360105480745a0400c140800010b48003807013810396203084204102036444280c1981440d40842015008551281081995040348140140320301c800d0705611822641c1001c2c5161030b480c0040c00c03c1200700080c458450410341040c04c06011140c450320701c1c4200000d10303040c417001c0100340c021840c005009542c040c1001e00c08190454480303643c03004002c2e0003080450a070207040c002c1d600400b0b1001800c00304994002c6003210002c0068000c004461504101d1280301941c3c443d0b1440042d01d019001c403000010000100f48503001100d0154041e08080b2105481909180300d48000e0881e5621808502c042c61010800030302070000300c061003244c80c4800d10781503495850310f886078031682c14a8082c0005244c0c1c002c00c420300000e002150000c081e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 646526627 1250 646525377 646525381
    0x2010c030e1020010e07031101180905012102010e0d050c1c120201050615090105040b0313020909010e3019120603082205100324120b0a06030803 64
    0x180c42901c0280f144040c0d0349444583c01441841403103040307070303001503040100341c01861600e810042d4501a80034504120501d201e00c4601640f5410f032500a080c1f41d00d00248562500700325021a4800d06190f6403e140d1a011040c09030703030300210a5100c1c64080300c0000c01c1a00e14a061f5180c050422070040d0007600f0074814460b00c41c1c490b0b0b48641c0c1c5a02518040c2c088061241c012403c80d28116151a80602080d910550407030030702e0040c200885042c18214500f64891701c800c84584c0045035481a8459003200b05004c5040c140e49840d0082582002800300e1030b05050400d480e00040c100c000709858001402801c401c001c00c10764001485060340782c90780d61a034520720b11205924402c544000c552502c11881e0850740340c0c4100700449400803282d90138042c2407a40410010607181c0910400a00c504010900d40d5440500b02c42d07003040307510002844540084c0380000c3c94040303156481d1500d0850340410461413581c075a1803110364082400e20181d40c41c0b4950318010850b68102805065011007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 646527877 1250 646526627 646526659
    0x20f0a080d0e010e190b0a020705031615181208040e0403080105011d031f0905011a0f040603080406080c161a0a020c070509090a020d060518061302010c030e 69
    0xa00b40042100a0340c0b82400080904280884424007001950028094401c1000410f43e4000038040004992040d90708e510780d0341000900d0f0800080d00803c125402d03480400205007901d441c1c10f07074a40a1f080c5005411510100d440c00301c41c083c400d8580009e6a0f4501e4801c000c20300c01120040c160485402c10142001e060003000d4403000d0003010b0104002d0240a40034a581c444800c10b0210300400402100346059554820040502d10880c21282c40794159400110203020707006903140810034a9026001c0401000490f51190050600031460940203001040d0401c003120b05680e0542014802e6484171082180301d1b20896292806441c20b14501d0002c002d01e0024200c00319144c06d48203080394841d03061420480c4280c19510805910142d01042142081d80140b17600980d058113607110b08030550007180400211844c12039520765500104155a0318403c03010800c041084000c06a9103010b10994103510444400641448400346001003010301c10501ea1212400c05031194501d007409130 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 646529127 1250 646527877 646527887
    0x2211209030606151c090f030c0c05060c0a0b040f0b010905040b0f0f1b040801020d1b030606021009081e0a02010c08070e012601170115050d020f0a080d 67
    0x2141a8424003407000070a400307240078403070b40c00e41980d480c044911740340008150501206500c482c207242c0f140c4440440002c110b00311142c100d204c0c00b07620740328000b04c0c135490186609401030700264410001440f5900420500251a81d00c01d41c1c4169220746540795418000041140b151001308842c000070004503078110140c200ca400b036413090300c4810003a00c50701600d61410308201c8010088480610009d1242100e180c0d403241c4a40140c482c651030282c40e0a009420f99101c0829107140b10303210344902800200301130182c0b11035012031401300450342c107000b0700a450b00e005140b22a901a294940c4009000c100c0084030703100000d440c03200000450a85080c08103410000c015005940785c04d81c0030b4125401a005588154442d60b10138841c649004015110103100701c441c00c00d41c1914001a6000c08020350341c0c83c0c040c0c05062448100100750f90030881c01d48a100c12a82740040c0d07d43d0080180c0c0d00d407100300708900e92b412508484d40401c0200458000c81e07840d446038409100e50030711400e107203801c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 646530377 1250 646529127 646529137
    0x15150907020f06010b040b0712030e0318090c070203060f0a0e191218051005090409210c030e0d020f040504060b0a0b030103120509060408060906190b010804022112 72
    0x5401902c003e6070340c9101200d4179000b5445401c03446801000400000749894142c1e8010040a040c00240238086000c0c1c9499a006040084070f200003c540c08865454642c040642c40324141d42c03d00d00c0d00c500343e4007080e1a5030b00544a442c0d0002200c0100307959125a0304003940581c0c0c4075040300c50300f4500401ca0b111407110008203a403010814000100014810321018031540b0305503072480340c2d40340b48c0000d101c00918084030307200400005001d10440c1d03a481d4024050040c0c002c80c000641c1e404412460900c00d08042407041c01e21540c1114140041d0308994007010360a030454138501d2114050000c9211231440c4512540e109203807408010800c02c9951002078040b4090b03910f12449902c540801c401c5110a000c042c05000503140f0b50000580320302c0c01011800c102070500703814213030795981075807070001c0903104000b842d0845030400c6850440084039512000c20080203000341c03198480082c1900744042c001900500c81e00c3c00030060300c0c8450506171100c40402080300c0828a41c158224495082 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 646531627 1250 646530377 646530403
    0xc0303141506090d020a0803130512190f0b0f07140406091a0f0304030809010b0612041104060816140901061407020d0b0114090f091515090702 63
    0x141651420a40820424080c424040601e0001d810001a010007403290803498000368040c0d50440c184005886403440d820007058424001c5480b08401d10400d402c0c0c0110b03400440c010f40070700028005004d000114440e06600240c0c44940c144140d00b040f200c0c4c030384c6030140545021004400d0021845802000f00c2c4504000d5980792290468079420303a6452045100e0324000a61030a0140610391350752208012516101e004e903031500a20b10740051084d0421103040d40868403103020020311440a0080500d5101c0c102c400798039203903e54100304c0f0034110103040078001d070782c40514007000c544490b800b83c406407807410708917448007070000c5803895000e00b140a109540c501c001024103881c240b907545e05068400c1512084000f0507000100d00702600007680c02d9a00c00041900c100c080b450302030070b65000e000c81e145100d024900100c01d220a401029000b0041d0007205400c00c8072086010508440891000381040c071180c5800310b0b80329a90b2000301c140399200e0740c03050902c481650001884255174079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 646532877 1250 646531627 646531631
    0x1e0204020a170106020f21041716060c0206042c2d07050f03070203070f030807030509060c090607050f060708060907020d0c1212050411180103050a030c0218070c0303 73
    0x31301d51070100d0711008204a10056a8003228000d00c1c04509820429442e80c4954142d0781820394541c4060003104035001c4210280e0059202c0340b80340d403640d4080502808550034000c0e0110180c1c1e020610510031442602c3c100000a060b00c522151401c0b02d061540c81038004111031401e200c0704002c80038127020500c051a401c0c4200d2211301c01c691a001901c1000f040d11250304010030501c1e0065541c0c80280804114001002000b000400071501d1400080c02660b03020a2446c2020002d4200c82c40502022001e901074810025402c8903401107460000e03081d1070a81d20341c80d031031801510b0101e001407542001e0251000b080319013680041c180d4410300c0100c3c3e0030402511080400c0e84c480001e65078100004140181c5000821161600d1007400d4001d850041c1d00a0019406a0100d40054504480e015800000d4845a01d03062015031100d00c100384103510194590764131143c2d901050007004060203c03408811041d136481c4400121940300d800031580c413628040350010a070841c2030340c045000c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 646534127 1250 646532877 646532879
    0x60a1101143904050108060a0b07060f0501080c03120d1d030c0105070c0302070b03180d0c03030c020d0e190806040b041208040203031204050c060c0304050a09090803041e0204020a1701 81
    0xa0307402c8281a811010709510303514160401d001104e0115005101ca40c03c9211802c001560500c0e040c02441c4540c0502c0000401c0081095a1010388006a00c464040e6101e04000011541d021801005442d19080c6c0e1075a01c4008042c448050500050040c565800d10702610304049070100081c202d0b00307141d00003003203da955030406a428030007420001e00142c1c0074460034880c40701c4c0c80b4011500410510154120200400c2c00340c0e15040300102e915001038240ca456404040c2c050268001e10302460014205001021000901e00e081e0340408a2140d900c040441481c446100c1e85200600036400580300b40d0326141c185000d52580944044901c44114000305900c00e02ca000032500555005029614024a5083e0340b0700301d204c0a40140c0b100e00404100303900c10303520900102041404c06e8003079501e0780d00d82030410503c00d489a005400c0681040b00308000a40b4040859a1081d8003c000d01c4041c040038401e00d802e101d52000c000d400510000702000c40b50780202d00407040c0d08900c0c1c1c1c14015a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 646535377 1250 646534127 646534201
    0x31c0e1c02181e0702100218011707050901031805010212100b030403091707051e03060a14040f1505010605090f0f0303180d05031323060a110114 64
    0x2801c000c94044000799600c0e01c00000781504520f42c00c1d041621441101d50b0502142c40c000101d90240034014201114904a0100c0d035030000741e8182c0752006d060b10160300d480c1c05400645140b1820041a04141c0e803203884400c05c88407556021070054000000315203500074548040c4600034151004803858800c90070006200b2005002c4030b00c80ca034103560742d01c042468424080321185000305212414021914080358a481d14842100d4101c8040c0040e940804900b0500d0308040d07014103601e40e6581044d4510205212900340580c129601002845503200c460408516031211100511420b82c00c00c400010040c0d802809000c9121040b101030800b0000041004001180c6000241d0144c000344096601d411080c420840714481c0038104051103149550b41c00d007151302820841c80c08201e044400d000d281c8070000c0c10802c81080400d211500500000007502a0054422090800688001700c640101080d00614035070110aa8907018034140081c0c68000090070084032500c000c000f001c0c03176101d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 646536627 1250 646535377 646535419
    0xc0d14161e08030a03090809030105070302030a0b04091a060a03080310050a21170f07060e16060c060c11060403110606220b0109050d0606060914031c0e1c02 69
    0x890784100b0046140580510055002d41014403041e5140c401c01c3c407908400f51401c3c003429100d2003003541d00507a030780350800c1d00d10f0403140b420704954001c0f80b41c01080c60001d40c48204040101c91030507440500d540d20840040d40000f840d420082514001105000010b0000b0b010b4100f500c608554001415441d096004a004060403841502c02c15880040001c2516100182c43e0404005511841c04414414000440c0c3c040c1908076403c0b03a8682c0e070309060480500071110103000c02d14030511668682040101b01e051b520001130f2400790744805c2507084078000c0381c51810410740c040903038032079291504028284407180030f8a20180c0c014100094520720380400d0f4a070340e0058000f004007070034034202060802400c0e00d0b101c080c1803125601d80071032540d40d803c050004540c0b145101140c0c0c1800c042005001c6401944010422078141d008110230b40d401140803062901510042c04525010b000200ca8902c051820950011800b903082d0b1494076014800104040c02982e0b0614015490031840c45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 646537877 1250 646536627 646536629
    0x9110c1006030b070f051b01061a0d050112150507020109020d051f020f0a0507060b09131103030315040b04200c01062310030f021206041a030c0d14161e 67
    0x42042010f58a51128018500340301c1c0040e0000103681510f8102c80212803003c0107980242050114bc90480710748a40105409130003010303c00c2e07940c58000e64540c4c0c0205001d600488621b038903140000d5015200350700c0105219001851048200d0850a0103a2540c941840c1c003010044010a034081c03070103442c0200c070032400130701004900e080304580d002c803499084040700700c41050310380600c90741d0341e0340b5640c12601070030701030031465a140704614003a1054040418014006e030000d1040003001410440e0b0740414000176240452444030000c006402085001001c03058141c01040c0c41c000c484140010b0b1044400c2c95001300b21071521183c5804045264002c8501e508003d074070250620700b04851849800781041c00c000c9549480642c42000344c0e0001c03191202c2c140c1c4c00200b0001c040c030380b81c081c04140090b1003c1440c0460007620202e5101c5005941300c6001c0d801a000c604100301c215214400000340e00800d07034044181c66005030f54082014410080c01c082101c030000340001240c10014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 646539127 1250 646537877 646537907
    0x2010807080105031906020c0304060806030d020c1c020d0c030b06030c03010603020901031212110d050109020a08271c11060c0403060f1107050d0807170109110c1006030b07 76
    0x10358013151643e2065044110804565454090040169032300003000500003030215a00c2e81c3c1000d107440000c0c140350062000c1d01c1011580311040309441303a2543c03000c0075501d402c1e0810540c1c080d0524000b040091b0b13000c441c01880b0440b00c41b030020074441c401450034090107040307003a14115500b9004150980d0110300019500c004654010030005451111421116041e401c20302103802c8400c06001c00c54200142d40c1400c04800941020010702512400d80500303c804402c504001071b4200041042100401402544215807036a0b00180c10560700d0a0407051810200d440d088020354440e10300405540c1c980000c6104004503414002c404071328207101d40110103402c0e0800e807a64440d000a000300451808a00381d4509100c5810540b05000304101400b660003441d031565040300c018440040104040c04011a070440d500e1396118032040c99044601803807000c1007590660510140500c5000700c060018460040c183d0142c40e01e64014030108c0740103c600121641d2602429280300d0a45e003044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 646540377 1250 646539127 646539133
    0x6030c060d0902240301030614010b1c0f1d060114061c091208071205011503020f0906070f1403090d200a06030b030106140d0807150212040201080708010503 69
    0x81c008604030394003807038205000503c2c80ca07a04022070b11a5204020088200e4803a1200000600501600f4000c14a007014090490b9100e50724010b051080790103070008a64600c000f81c00d400900c1c40040d040b20101d2169000304011591000070520403d0018414008540c00307803a00000b48400c101e10f40b44079040c800341600d403810702009040780644284039a0212031542d107080010210345520082030407086c0e241c940d04840c0c20040c00c044c1205078030007140729045050000510800700414926000c40b8080d06026854a038184203034000307402a0500301380c01010100340c0c10305026054006141850241c00300a041003207a031072a94591041c0c546058016000080030000540600c075801d03246141700c40d00481d1602c82c200003681d400c0c12540141c000076142c1d8142000c5180a10032007000340950620908250104400300e40c0c0300701601d001405a400c04100700041c025900d00c003106e100e00d1644119901c000e040d00c1c0c0c040c1c413082510700b030340041c04050010758640c0c02440b10b9810f03154002c000b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 646541627 1250 646540377 646540387
    0x307170705061b01050c0705160302060406110712030203121303080609060d0203010e0d021501051e15040902120a2307050c070f080c01080412030f020702030f0c0906030c06 76
    0xb80200c9501201c0300495a241c03003580100c0000d0203200c0c1328010304005035125a02d411509003e49030040c05050f203844641c0c04482000141d5600040b10f08481950420081e0000d904051500b0940f040d80f200302c031803020791501e004140c1c0c0030000303041d04a140c0001400c40e8171010400413498415400040c04513900c0408140d0a00d080b070010303640182c2c000c2074001da102c0c20b0740c0864203407045401482c445912100c04803110039010701c080710202d000941113200d03661600c000904000305151103008600c0d080308941035682c07502c01d02d160f0b1100f10f98020030380e5a030b59454480000e50008103201019605440071a00940e0340d8021816541440780c04044505240303c5004d114640160041003071040c2001940d080010a10501e0000e159100c6240c080620700810103080c10048500207042008000c1040700240250607114042c001624000130070b5000d140045000380b103121006941445642d00ca03450703404000414204a1a0079202004c0d81d84960f410305584034902520750354044000c0c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 646542877 1250 646541627 646541629
    0x8090303070c020402160614010504063525080c06090102211c06180506061806040b0403050c040f020c07030201030b1309050703030206100f0e060a0314010b0307170705 74
    0x60301c864502554006c40301c49199490f034041320320005103041c007200020010007142c9041c0c403c0d000200000b00c020a101c0500180704064190140c203000c0e011311503590303948004901044400319540c004c1d42c1c607940322030b0311400703a4542c1d001920440090b0f2242404c1d81c0950b05161044c0c83c00c42c0d00680003000c40082c260402c0070060b01000e0b00003000d550900503195a1400764501a00c400f1103101c00050707540c00d00401040c85c00540090748001401d06c01882016120b41c021642071044900325560701e180070000086480c807503640090784802c030104021081c00710100d540c084900d4212401c0100c02030110108003170b0301510011f15681d0304007010400240d4025008070a40d84002401c000700282c07181420001c4401c1c000c42928694412041442019010400c2c1604001d803500311031486881d1850f610000013190140b451140e114402141c0c0e292540c00f041400795a004a180001c1c0c644844054000c10304030070014424032170060002000704904c20444030000c2c50030701600740303141090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 646544127 1250 646542877 646542881
    0x6030c20010b0306010f080c060325141207110c0a06030e01021308070e0106051c0902030309041d0705090f1302030f01230c0c1c031401080d08090303070c0204 70
    0x310500095501ca280224a40e9024010207018200d41c0141424081c1880d5400d03180c0a042c055180c00f40408009000440050b400c18000b501c0868001062405408200f240ea540d043c920300900b42c0e03808a25140324114455150f44918101d40d14402101c1d90b20090351750380d8140400322034208034820814041e0a03c2908070500300c1095400241c80c000340301118202c07070121030f4480c0c421038118200501203908501707122030040141f0320b045d50030411900140101c0c800c403044400d562942c0d9000c004210344051064034400d0314014010009170311703039184505040614425250541c01440300c04107031403402c00021401103580d10301080c02d0390b550000d51056055000d0090344c0c1842050141d400148090040b8094075002d801c42c940035041840c9901019480680500040f08003480f9094101d040040c803080582e600080c0c0386000d0b150141c06400804220782c6c14000000034100104103202c0006400031000800d07a0ba035800c5658900c2840d03181d00003600c00d600052020040300300540340503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 646545377 1250 646544127 646544177
    0x9060f1005091903120f110d030510180b010e0d1a0405150109022502010503060108070e15030105031e06010b07030210020316030c020f03160602130806090706030c 72
    0x24210300700000100f0701d82c000319420381d4401c0355004510076a800201d50700a03051a140305050400d0650301e11402405a115031543c0f03020b0041650b00d80001d26060581d414040c0241040d03101d1090017101441c4000150500004140c04241682c1e050441030600c01c80c400a002c0d0841c84010440c070039800e46031440b28010300169807510490b007000c2054a400c20803030b030090114050050b40c6040300000c1c506407000c401010580744009100140c0540d8024081340d0b4000000d1a040000342d503011b000780c40d80404c2c0e0491f550080700300e0000704501c2440c980210f040e120304608982c1c203044404854180003500e000c039803035150032030001001984103040107854000d1080c01900c05940001c9040340c103c2e0802c50f6504421504524100302e100d42620500c51106080d1003e0003c081d0241484c680d240724040c03c400b07202080c046600306001c074503819120002c0c0a12011400655034459040d564201681c070140d00e40140c00000803c60b00a206140d880180782c1c6840c1d10710354102407030505040f4a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 646546627 1250 646545377 646545379
    0x10c11150a09090c141213171201090504080a1202090904032d020d05090103020f0309060f0c030609040204050601020a0501111330031101180209060f100509 69
    0x20300400d0340904850103000807080965403044102d241140502c103443d0707100011428054000c0d01c084040c00500704440406884654582e620b03100d90002d4241c4501e0008040c1120700e80081010b4418107000c003e0255030002000c0b02d0f41030741c840ba00c1c5811a0300a4400414000e400c001c000840d5001c0d04544c0f00865241100504004144010030409001128214002111a84c0090024149848084901880c1e98080000d031110040181d03136040458000e07424404003041742500341c2e10035012a1a60300d43e01842c551281130108109030345500c140c56900080040100240c640ba09070015240303d00002000042583c44175000e0000030507024000c1c50460148445401c0428002d000301501d180502040550f203000e141032423030658065401802000c0c0141c0361205e804410316100410040d403000b20412213443c18581901c11019140407580c1c10b5003403820941c0044820308401041c0b074000d0300d00050316540c000401400c4040800b21302c2d0b0040003d46009620742c400c0d4003408261320 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 646547877 1250 646546627 646546639
    0x5060112020304060c03141501110c060c0d02010506240d06030203030705060a150807051002010e1e1c08150a2111120303040605040c090e0102120105010e010c11 71
    0x20101803100c00d90303004980a1360400d4a070f06455054907814400c0f0842c40606410385003840c217054200c00b001e000e10706002d5042000c84441544070003002d0082e0714038510018903050340e40090021003070704c8010450464000d9440c1c180004c00900340704440404008091600c6001030b082c81c40c550120350800030b00005032942d16080400143c50420042030414007440c000c004c0c0703243c90301005081d1a4001c90b00155010069400c001c94a0005009800d41300211103240c007010f00b05000324010072080790100751034801d2500382c29a0082200b50a00051150300a4408007144081c0300c440007806855039200003441d100c00600e98000c1800b203104202c1006200310701d8150b0703030203081d94104840c110078a1001d008020010401c400100300c80c1007000e080d6030010710f85a00311001c076202d020082024015648840014007089070700d04007080a000800e5003001039007a110450b6000b904904000031340e60061900100c0c480d0f0080044840385c0905030368905141c8220365503500d5110f41d031155140c104e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 646549127 1250 646547877 646547897
    0x80a080d110415030902130209030a020d08070812100501170a0c0c0c0f182003100519031a0f0a1a04050c1905031312020a0b0703020c0c04060b0d050601 67
    0x21050303c07010751030740d00700d40c1e012030180b081d80100441d5940d13658241e10b10750300c10805c12600d5103001c2403451780c2030b4044178a51204d440909020446100c0d07038000410040d0b0000f090300d0b4a048841c10f25024400750b4150365981034803400107645503110f0464003040105031000007020400242c00c208090401e0385004500d902c03c0740e4544915012179041540d441080c02014400c07124250301803074100304030440601082e48011990545042c00200100b500c0e0000400550454030b9a201d0030020800076112a008421604008510b00e5a5000840300849000c00421020303103c214500d00a4520240e102542d44507664400c001b00f4100900d116104180011410940d03039601c41c4070f100d401515902070b83c44001e20b802059168101c0d01000c03c1c08001d00c207100c0100c550444582400c3e50180c4c001440d030410200c01c2c0d151440d110002002c822000d010403000607070580140c6040803034602145c48000a1808205c1604c040f8001e03411200000c0c014981c4280490300f017540c0040041c18031023616 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 646550377 1250 646549127 646549139
    0x20307170a06090311240103030302071a01030b0105010f050a0f180f090b180403020d030f021c0b01030510060221190c0510110d0b010509040213030b01080a080d1104 73
    0x20390f00e90310040d00422a00c04840c1c40451042c040010a9076800c40c4c1000b40704050a684900040b040c0005001c00d40c0c00f042002c02c0050700c0301c0d441140d014400c011855980e50707140c42244580c090082c0750000d5584589800e9550241c02900c001c041582c60300401e911010208a40b01c0c100003a1800c1c00c40c80b004000100740d042c03203885c031340a0041d5150105685111006020032141000c540b00e4160f0400010080840c0d030208410003000d0080c680812104041e00d103002c0a8010352222110030a0003039501c6100d100140d002098854007a2018442543d61000c016194a55840384202581021a02e9903095058035404886824034211036424800941030108044000c80072680202e0b4240317071164148071003000351071200d038181442484100140e41c407940c0b4a001d1502d64041e616124212442c450b03002c0d5003500d00d00c82c4007410440d10f808020302645030042240c8001e90b03c000b040b9002061051000c1021000305400c004190324041070440c100340100410414901002000d110214074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 646551627 1250 646550377 646550381
    0x702030a0308041728050c280c0e0a0b0402090a090e0106031b0303090e150105131a090f0f0616050705030304180b192306130f12020307170a06 63
    0x2d484da90550b041100a009a101d54a04417061241c4051040c14451035500d000006000c003060350301156401c0441e450004404004204c0601c0140901401400800d11480c0081d03007912800d4030740014411340101005000c200d1040012244d044001d03010701b44116081900140b01c2c20802500000301c5a07601e484002c240000d403803a0715030f0248004800c10505902035081d90280c0a01c0c501818103090491405080f034548450007418440c0100b5008401c07180703183d44800410750f58034482000e605c0c21a45115030350001d00310038480ea02d22815000c203802e102e000c400040034098040c81c681010302000c10040604200121041e100745040814147c0f82800508024103c0c02c4d0700c81c0d90303141d60b01400000c0d00d00c10684140100105482b00c440c24542c0046041100c1040c000c02c0146030f05403100c07106090605600c5500204000741910380100410001ca00b124030b9070141c0580191104200032000102d090081e605502c440310a03c8480340d1034001c10308009024044071515400c039038503081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 646552877 1250 646551627 646551637
    0x120f0c060c020312070306140111031902010c1701050303070201050309071805190b13020a3506270c04030f050705030c010c0807080306030a05030d050604110702030a03080417 77
    0x100580004c610490200030320910b4a0b0410b4207401d040c4049401d0071103c3c0c40070251002c680f8104000441008064070060089441e01c0342019002c800c12a68408041d000c1c0600c298420002041150100c911001040b00eaa041c2c56004024504d000c0c0301d6001100c0c0b030340020344030341400d000b80070300000d00441071016840440f410300310214891030100f09000301003505244413000c070750134448507100598840d40c42c000c0c60381c2c010f20016112003d03c50100d070307800714580320303107503030780e40c1e0481e9041e1005600640142c800b407411012120342d500c0200780129000501f00c03100801d1002c118000d0700400a1048030b81c00002d039455203040503500e480d060b4084900c244103079410303000903c0c2071010307003000c0c442070718986070030309024004007603da0790080d4a21071700001a02c10b00c4003201241850303500b0b01c14a0812a0040212034a03284a1007240300180b07829554580b11320300c1e01035140d1480d1210001e4422103500100603200d40c0b00e103900c0035101c03001300030411501c13041007128142d405ea100e0740c081c02e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 646554127 1250 646552877 646552901
    0x304061d0312130501090918021e041113060203040509070c02221a0f03100513051509010b04090f0204050405070f0b07050708191707080307170a09120f0c06 69
    0x800c410700d440c3c000b40c121b20281c0c02c1444250309080307221880780d2008603001d040d254140e840f02400198034030b02810488400340701562103400c080e00c46482050500203403561079100042c0c601c00c655914403d0b60340b403103184582c80e0010002d80025011074004c4002d10507042c00070344584019a481115403120300f0308202000d881a5441007203190030030000090307130000780003a0703142801000f50f44002556007214441d2043e0319900c880014a4000701032a1100015920400315010181313001120120381c4030444904030650b02c1c0014448803480c007406000a240d400000001d00100180c080c4005800018420307601441000310000300803103035408080090682e4017007507403108140d14005084c800f03107038020341040e40100203240107400c2070412040c42030350001caa540801490310070940c503401106405005407401004100c4c1c900d4021484030940c1080c801007102c690740e4010510100d03003002002031700301400442d400e480d042c05042d521402590714100b032041203074560389000541d51580050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 646555377 1250 646554127 646554157
    0x3020c01020f0a030e161707080a030507290417120c090102070504020301030c0b131203090e010819030302090103090503070f0303230c3411030304061d0312 69
    0x6038038610b90601c500603920005d40c019100740d01803400070f0341c44055a03000340348036542c5038228401c0010003040f200000300b20103010741d1224040c1e8100503019402c0420191414260001600304494600941c582290b00c1c1170f000141545032600c40d070168401000358a640644108002c480d591001801c480c8a080140c1a003962040c0503000203090405582c4500d000745e0042c0018000500c038120400180d80e9404452502c40817811609400c0d05443d9006d03203805e0015603c07043c10b1580c4154014281c52440c842503000e82d03692643d0583e10a46401d003160304115140c80c860000380300360028024600e0500d00801c50302013030f4950904560000c18211402d540c03601c2d40000b05605030160041c080b03017006e4250140c00e0607a510401140707000313100f0860900009901800c41c0441150407145c0d0450b07003030490042c3c407139003c203640141403440b0076210740c3c040d06000079039468004101c0d01600d0350b954a00740d10606400c11481000a001c14190380750040c50806000c28500c4405428180e0500c1c0e06 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 646556627 1250 646555377 646555387
    0x15090f0108010f02090901030602070204091709040c0f08040201032a0504080f07121106040f09090203100b060703030b0607080c060117010b0a0b0318013305010e0105070303020c01020f 81
    0x1400342142c03c18502d00d0100390040c4101c0001d41d0b110507206045903003010000d07959000b50b200040061000c14001003c0103050000e5041e15440400071300035160040e1420032000c00300200640340880d00d0401000000c50000001d4010351194200c0d4142c21010b6080349070300701c10410403242160024946000080010504100414041014158419815004d460341c0c9047c130440c0000c00c07900c05800b600048029101c0310451b02d540003224010080441c051603d02d40791060030f8003420102001740d200e80310300303400d420341405284914103540c1c200401c5140380c842e00f40d0302a00500400400b00343e0180c07007440044045081c07030004001150545010306415030501d03042c400c0300c0c101010300b800141c2c5840030101031515074a61440507100f03280d20080d12542c404501800e0078000e040c00050b6075003054650604407440c100c190040081c465200400b0403a104d20400c100c001300d126030750002c1e40207940700a89501480040c04a14040e140c09490100360a418a099078071098800c0d06500b80062 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 646557877 1250 646556627 646556639
    0x8070c1809030314040804060807020f19050c1815040b100e0316260c030a0309081002031e090a05030304030f080105030307051c050d050a090308010e1303050315090f01 74
    0x114594240500512a104d942070548a498150042d80114130034090a500414100ba00030040710900c40e1900c01201d8071803c011691100d5090304010031186031082e08401d921a240a2501341c000528114405119a450390031807440503c200d102150426a0340202c466140c944010104154910352517540b18810b00d1000d052404544090300c0240210110092009846034901c28144800410004210500f0f500e40142010f9030460029850b02c0f640c3e0b4540209900600082c08071031400d82a2456030031140380080691000311040b480d20000e41c022600d481c41d01e02c0c44281c100c5200000c8960310000c45e03a62502c3c5510a03501074002c07a0404100c0080258044003260240900b034000e10708050355a0740c2c46a941c1c0b1112004158181da82d03240403005403203481a12034021110341c0c10b004900b002c1d0000001012800c400360002a01e5200103d410f1500c5400580510b02c98295501801c040f500c04580d65040038010600c0708002100441356a943d58801601841d404980440341d03514000b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 646559127 1250 646557877 646557881
    0x50402031905150703110307020f06070f0c020d0303180602120109020c19081603110c0102030c1213030f15050f01060c030c0204110c03040f08010506060708070c18090303 75
    0x810048002201450700c4000903000310790103440042c81d0100036650f864050003680a4020207155010380340e004000c0280260f80050b0000b41c8440e50401e590b5903486910302103c040c1a620307c603a000c030303500210040c0141480240707014405d000789000900349108600148107025a05019200b49070041007a060590b5054030090040c40d140d4400c500e06064091203a07107a59050340e1070600fa420b1072001c4800d00083d5803c461240540102e202c1d01c4107840c5c5400390620040003003000030f912547d4400c038501d500010482c0c1741c4421440c010700e408001040003030340c1940100d0f505090350110a00010005125100038101c0c18405e0815140d1507030103025610803a00000d20341e01000307103040e0041060542040315007031200c0d0180340681402c0941e00118000e015400796406c0385180003d2031802108012018100340c4078104120305e0704d55030761802c0da400c0e40c80030b46519a01c038004005040014440c4001412054810f0400c52081650b900c4940310019a1961040040b600c60702c00fa410943c0c98 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 646560377 1250 646559127 646559143
    0xc101701050108013002120102040e1b030c0d020705012d060311040e0f190b0f010b04060c06090c080304170304030b010618091515021b10030b03030d05040203 70
    0xc3c644410740c1d40c5400328066007040d196115420910410003c0d4000e03018414110391556005480380070442c0006404c0740c003d5019105261410a0504c040b81000e284e40a00b0041e5080e1003003181d0941e00d64003850441ea0388010b1500c0d40855013003064800180c002c0c05140050fa0811604952181016098007103a00c028803003003807d280381c10301c02d000140303c1c2e207a141c2480c9030580f000910810900c4440e4500103178041d284071f0314070171829090310720b001d0100203030301d00383c821065100c90b5111200d005500039400e0080d03e0b0048401c0c0420301c1124490304104043c10f0240d9030106000c5090344510140c4241500a10309580000600744650b01d00d095440040390450710040d49081e165817905803d00740c040c0588401c100385440110000010b4100d0384000e846884400c00c003081031024884040a100e20501c807404c003586403082030b10303030000c140c6c505031403440b48051002d154114108110388040410750310130300d40d58428080c0e10740c80403c040c00c281120b10000080c1070410b80101032400d150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 646561627 1250 646560377 646560379
    0x23040f06060b0922060e0c070507060807080a0902010909050a0b031218060706060e0c090f01080f070f02010e03040905010906080109080a1d060a080f15030316050c10170105 76
    0xc03c002e1045103442e5040307490144203010440c140c0c4296400b04070790150103564800940810301000b449410911a070080400d5807040f4110b91b6515a5a402a00c0c1203d0440d050004a00c1403030024a05000d41e40001e03840a03c1407400c3e02c0c0540c0c03501110381c00c0701c1080e1280e07000c40740d0300d9004018905080140401d805540584181400e202d80c4520f25156800001d03140500f00101e10002080601d03000b0001800d15400070b0113962038181da200c036040e0809030409100745082c0030f1900c02940503c61090007203490780d840c0c48460741d98280c240c035401105008642159640c04500d030441c4010b0000d48040c0007428800315055260131380d40001e80303400d50030070010b0307900d804d4000002480040489000340035500b8089502c3c20098a62a800720031003040d150009000244000c0c540d038001c055a00c1030192500c10540e6440f0640c4196081d49010780b2203030903034000c00144030706c11500070119610900c910300700c2e0b00c0b000c0004041841d04034100034450104060000b0384c2600c8030000034090140134 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 646562877 1250 646561627 646561649
    0xc01020613060e0f0111120703060e010e1306061e08030f03010e150a1818020114072f1e030627060103030e040e0c060d23040f0606 58
    0x100390070320141e24511810300030066035466405011200e000e009000000b43d65030002c006c000540f400250469003d210110030b658100c200040c580c03400b0f441050142d844217410044039a0030200b00c11280c40c0058401404141c90300340c0f84001130141e0240c04041d100a501c1141000c500701c41041800c0034503000703400d55410521101e02540c8010b07080d2411a16001c4a008180c0c4a81000c008100e00c004440e0b40c00c040a003c0104503040440e180c0000c00320000400c0080700040c1480d01c4035194105402400180d941c04807100c2c4010030700140600ca4000d00c00e0a10707148810800c003404203000303003440c030342e01d00103640e02d1455240c0b5130003440480342826031010048001c070380040d131a00d0703009013548060100700c07940642c001d00e2a00c03801040c15201084400550b12400c020704540e0301f160310140300d2410b25008494180c004034490030b0b03205000c2c040d0350038a5540d04002000d0320098006e15155000312500c080750106c40c41d850750003607029984880d040300700ca090400564032942c1100035028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 646564127 1250 646562877 646562881
    0x1030e0307050c21031201230a0302061b03030a06030203010e0724140d0e0705011404260a080307020c310f090305120604090f1103010603060207080901020c010206 72
    0xb00007007074200349560121440005074800d9008100c80b4000100b05130050712021540124100e403407840c840c10303500b50800000341125001d55203260f0300400c8400300c0c1c014000b09002c00060505902910801441a084011711411540c4107403468000b22070f10170720075459900030825400c0030700c038003054400b05d000600348040c00c0010b9490315a02c2c0101d8412424203018010720326500c968131600150503111040343e95000e09415500103010394aa811401c0d00880c4c50015407903020b1500303007c0d00202810740900345454010402a4003540074869040003c948105001201d02845110b401900c112402c40d102c2c18103c8000f40b03000070740e07800c4900a00100714000303240ca0810500c10801c083d5096500403c0664410310800f0305000c020014003c0e0512411900705038120014001007444946240c240d90f80c0c0c50100019290301d50005009204403410500c086001282c104e542c0c00406000030403526960b607070303140c1203038000700c070640c0e49050200d254002c540c0d05102903071840d03009200500f854 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 646565377 1250 646564127 646564133
    0x507261f05090c03041a0a051e0702070b0d020903030c100605041401090b0d021002150c120103120302041505090405280f09020303130609080d1b0317010b0901030e0307 74
    0x8100c064a034103000007000c40060204035031b1403c540c040d54201415a41c40c0d041c01840381024000546880e0030440c003154040c2c1040d207031902e01c280310341c2099000741560f41c90b00c00c1100d0f040d84504112080113808015905898034100002c012042c1a0001002010581e800510840c0e05c940c1249219604090b80c603141d60060200c81410761303449601c002170400800000601290143c02d009400c20482034032600115008500e2000400c0c086a08541c0f6035102c0c03031038213240c0c401d4410035110010380100505c00f24455404505403419207042c01032800c1d84458a51204000d01035080002403030000710485141002d0141c5508007020740c5a040c0ca418020120302020b0b400d011001e50f0b6207503119400302c101000c5400a0424540240c1600e54031000522031082401e6203020700d1000c10300081c40090045000a42650300080da40e5820328012850034044020448c921b000b5020081c4070101b204a843c04c0310100342c020811a11055a6035504400140c16502502c000603829003007480704e2008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 646566627 1250 646565377 646565389
    0x9090e0d0509010c1506052803030809030403080309010209130902010c0213061a0a0305071704020108070306080f16080a020a0e040f08070b01091b120507261f05 71
    0x120881814078030340381c0208100488840703000a0002e404000d40f06880000702d5a168090001d9406c159400014400c0d00b000902c5a203410303031a105600a101102007010034072800b4601e42140804054900d01a601d841c0c07001c20780c005454000d026503000410061034640b43c210103544521110050004c0d041c2c0d900041e05105401c49d01a00481081300c1d1345071b0030307649a80b00c24054403070b207a980030160349514142c41c801d41040205202091800c0041180760703000341c1a00d0840720300750180043d10f80d2954011140d044000e4050300030f0580300c010108494500b84100c0e07036001e0342200245480c0d50014038004e01818160301220345500400143d01c0940c6802c10035806542240c50000b481d502e6078a4411081c400c03448010304181070102d00c050410000030f8040f4100d40750140c0031b000c01100301441e40340c048074101410000c55200103008288a030386800640c3d12900c2c6040002050010000c40400c5107000f0b0f4041076a1621023042148641a01d021081111007001c8070b0300c1c0013400e010110710 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 646567877 1250 646566627 646566643
    0x3040f03140a020606211b04270605102d09050705030717090c060c2503050106081b0d05012004082107080c160b07060c030504020105033103050a09090e 67
    0x1c80c290655039550342c182c0b04c68114101c3d961503050200007d021806042276518212041100c0160610022403001c11a004400040d6428058030908048401c40351148002e4140e98503801c03400201000600d100c013038818036200720ba564503081d903249080c1c0c0005001100d04141d0010140c1148180b14101400051600140509030303030031903603621900551480c1119601c254075510404a48a03030408561182c000201c0c0d1290000f4402d01e5210100c482c1c40702003001e0702c28002010340458000387e203440b088903610035025000014129640302c144042005801809900140303000178100040181000740c0c54070740207180b8120400343c81e10060503e151086030000ba01c02c013008a051400f802c000e11804034a4045802d42c0c03080b860b5181e01000707294001000a03124213160070080c00d80e881c001d014030783c8503a038140e40c1d2900e140e951100c03204110030080c0c0040191200380c01020302c0c0900c03207110305d0005400380c1c50725915400f001c03a0080291103160840d180ca242006402544001c000403518 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 646569127 1250 646567877 646567903
    0x1c021207110a0330060605191407020108040206090a031b05030601142809060923041205040305030f0408210f03060f130c080105120303040f03140a02060621 69
    0x11403100002941c4d400b055043c0d90203211010701e003440005400d90040000c00104c1c2c0c1d2080701e00410180c8131029220340e9403c02c54000f40d1001040864015882000c10560140c40100b00c41d08140414001c0780c850f04041e00200c80070142e40b25411004d01051040c20010f00084009004070742c1004c900c00c900303094401e080741c02001c14032000c3e071040307946204240c060b411a080c5404d0141da07030503090b400b0f40154429010900d00e01518105805070400f06801d03020003440940b00b19459079914400302601c0c0080203020070100f80004400501e043c0006d00141541c1038100317440301d0919450f542480000c681031403c01920701c191244031181101a00c04085601c010030703803241d4400d404244200000c0c3c030140d42c80305088501004c400d0640c0d00c003000f040c0c416541c19a06030703240c1080c0318004109013651610f640c810b02c00100040d04425186d882c0e00e00c00d00d00a0a150008018031807507800c14140f0f0801b40e0400740400201d8244400a210f011803021070940710100c15201e200d80311000d02c0c0303d035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 646570377 1250 646569127 646569167
    0x506030c0a09050903040302270a0209090601120609090f110d02030d0305070c0206030f091509030414060d0608030c0d0e0622260c0409020a05061c021207110a03 71
    0x80d150f560a001b41c800958000d084502c1046001602180240040714000c604100f52808110044050710a1729002c000180003509161568001541d20380488020480c065480719804145524140a000c3c50244070340102c40004e50180ba2000d0710b941130b440c0d8140510003940300c0304090307a40080c03401944460390a0024a03900c0d44201211a06107006010350010703c004140888140a0702449100d00c500a081d035241c05202407a101c40c00d0800c2c0c0700790021ba0300500081c0503806011002c00d98800000309006c2c9082d0948480c030042c1c0d001a40300b500300380c00114160001600900090300600210720740f0250360003240c00050a03502540c0c065518186418400410b96200d010880b40a050450308104802c0c10303d444c0302105505800c607084060144002072940c40c10700e030040c500803560082286220754208070900480381c010100c3c04031045000010304000e000c0501c01004030004031106440c1514204e00040c2000b20000303100d615662051408d203000c01d50240024144855403000307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 646571627 1250 646570377 646570381
    0x6060703110703080403151404080a050a020c040c0c210c0f0201020c03010e0c010216032607061109040501120f06020f2118030403030f08040305120a050a0506030c0a0905 75
    0x108a00d0081550401086114005000f00c1441500325184442c0062110103119202d0304d088c0c580c01080003034030001c0010500b803218000d6980a4406421320301c0c500d00c11a03d04010180018081e035040c10a10004101c00c180341c18240401507000075034118104a80702440016104003e216005803540541003030360407814841168405c0c040c00c0c00380c14008000b84883c408540d800c5480309003100702c003070261140a2101490840c3c6042c0303081103a03008824240d014000000c24920912045080c844000d8200120400545144605444142c00120894035001c3c1d06051004485041c1c01580341c021510051f180020f046800e08080d45920040141e122000320004081e140500b08016404110314074174141c540f103c20185070322800e041c1499030319140b01740c60403989030700c2180000342c0000c14581082c4d4129004109494206100e460070a01d001d00b0017003d880c201006807820084181c0b54810301041c0d2380f050254a030010022005408500051800980d21181c0741c842c5681554032800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 646572877 1250 646571627 646571657
    0x171c1d01050c0d120c031406130603020d030c0b0f0606070f02030c12010504020906040b01050a11150a0203070f020115031104060503030703113306120d0f030e0606060703 75
    0x7041d6800d40c0b50460480d14481c1025101500380608018600307031aa240c8013500301c0c03c92003400380341d0300050200301030400340d1140b500703112079004003140486200d61076000000068851003e1840d8613402961610100e01c07481c90001c0042d50050400c040c42070504041c0941d0759180d404880d80140c1c86030080d2a280038a1000c01d00303010044101c81c0c1d0001440e00c1c000e000c8941074202c24411442100d100b5140c0d6962800c02003140c0320380c58000d000035030500902a140c1d00801c90040146842c070110340c0240c1d4209140d11002d0303003c40390110029004820320000c2c540046448041a01d09e0000f0b004c9503100c11110f84141446102c05403e00720070120500343c81d2030790b41c4440090807014090360759070559424080d000d038011044030040b910628041140c0c07034603407242c03100d90b24400d81a02c880d60403000b814001b0f1520041c0c440c9612010390b94000c203440c441004030308903808868445125120444c10050210349400749406155080041040441c1c1d45038030840d400e01c0d626007002d820082a440d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 646574127 1250 646572877 646572887
    0x3050130030e03190308060402072418080910090b030c0f07050a05010902031009050c010c11090426030f011502030403050a0317151503091006171c1d01 67
    0x114a07014050913041c98031400d8125404000306009440d080203d03100c65040c0007c902c1058809030200074114401c004950170700d210301164000070800131602d10f5643c01410001c0c1034982c800c50784010000b504581a0420885000c034144e1903003003d681d0146004108001448018040051601d0000b08158101c803a281600c20003500001111001440d03890114020000101c080c1d1091180b0040380c0d001c0c0d0030500034140c40541c403001070140d01c440400103440b0061040401c031807000b0240d684209684070070440c60720407409070300d04540c5c80030490302c4c540c090726801d0884c3c600c0032802c00400699518003403640e8111407440401c460304000c411000ca0071401a40c00090482c020000d541e401d041e44070031410003215400121b5942601c4883d104c1c52400f4102c1c5010f078024444600300d0500510640185500c15614000c1c1c1300d0742c1c99100007180446a05800151140c3e01d40d6190380c0113080204150004102206508074046410105c09081c141041d10030079451590001240313080e134407031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 646575377 1250 646574127 646574147
    0x90a0b0d0c18150602100f0b0919180209040f03110a080c0606010e01020c040b15040b03011406120f0406091707021e0d061a0303070b070305013003 65
    0x4051501c1d840c0e52907400c01c104000d25203010003400ca04220b4542e29500f448080e180484076150004d10a05003140161000781c00f0040d042540680e8a108407103036900d070307044032501c00c8401403240184078003401d25010407100200caa007060014205840c2005881f0200c003a40c000780c01040214000e00e0328541150340c480790041c180d499001d60b82c440d4040002103806010440b4024042d1105681c038000111101c00c10203524034010b03802804605480d0800741e100d480251405440d5803592a41c9441e101800c1d4040e50181486800000c010082400004010450300ba4201c5401d03203822018040212034240240500f89a500c90034041004c003c000d40c8850416540611181070a201103003207441c2d140c20155082e8060380489079540000c25402101d030b54021801018030031089000c1c1c80d9100200400b8005002072030388810038504980e42040602400c1c0d10540d460f4030a4070700000c0040079194182e003c00702030041d8a61641340051020b40c4202c140a41520400130115681005c5071940c501c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 646576627 1250 646575377 646575383
    0x90d0f02030d0f02011808071e06060f08010617060c0a0509100c02010e01020f120d09051009021306080309101214091203061020011103040b06030c090a0b0d 69
    0x110b280c5264070a42140c1405a10340e03803034000700481d0106400204141d01c1440d001003101d0410080980042d4030381400101c40842002400d140d100070396604411240755400c07540801c441c040b02045008000d003d400c0c0980f0000b40c41d907039814002409581c1d0780401a01201e01c2c9003012640401d4148150281d8003044d20003000e0035031f241000300001e0f01e04065040264000350300c03400c2e0040390303500007d10004059000e00c0102000f050305a00074000380c000d010b482c0c0940c4d0b2191000008a0010000c0d4101c4030120080012164080d01c1042074135400310b007500e2452070030080100020b0340080192074600704140c88402d001c41000004903403070300d50b4014902e15a458040600944032020359039501c42c00500c0125040c540859008031701d1800112107603540882c03407c6601600b140b146903030350001c0400740010004100110102400e540d600490003101c080040101b0060080088125070807100070750280004240400c0803409103400100451a4591a00d00d100004e0700e850820b8003040760 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 646577877 1250 646576627 646576633
    0x29070f0b070c06141605070308071b0204060b090907090b0306040f0603150e102d15080f0c100c020f06090d0302010b0306070f0503132f04050f0606090d0f0203 70
    0x141d121a034092101c000c0da28403518001103180317506054007500450783d529415448038407440e516080111a0021040d0501217034a02c100c0c00000145c84500404005d400307036400958076003281c5c10038003c580100810600400004610820841c840344007203d4100300203131404100101c95180010262900e80d00081c8a50145100d08003051542da008842c90a019415103170940d407403800c3c190580303078071907450100b00a8886080400c15410511003480c07080b85240802c3d0000d445801c0d1845001c03941c48114140c01c80f42131094400424000d600c00e42d5421500008411403041004261201b01e080003800360100c0c0e0089040c0380e0340c1809a1384001c1008022610703a00291130001d02a000810700c03c0d029101e08030202d4585801002421461001559a01e046503107100800030000303031a50303040da5046c0d8068510648440e09660b9200400013010244000c0748825047c0402c40380e00412040e100c190517014080240c2e1030208864268900301c2d654250742d10141001a501050403034002e600d44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 646579127 1250 646577877 646577891
    0x301150c0f0312051b0901110f070314070621020306031608010b0f0907020607080a0209190312020601060519090504240e0f04060c020f0729070f0b070c06 68
    0x560f02a1118100406400003804240c03120450f00c100c01c003e80480d009003c20a100b0314060794421080c0e215121450382c2128820342c20b007000030b820200e0680064031110880d0050355000001004068001d04507460320108041c800c2c01d551192106100329000d04540010218640d076400300031095141e1150040080c030703599078404e80d5008021060115000710101142482c16181c20403810748228240c3c1c01502e804e6842d4241141d42e000010205c159031917091190560548880300c06424a00c03600f03d00c0400907046081c201d40b22208071510204650140700103006181e07101c001d840100301c2c5a50307000c1d908411540700351001c12a681115401c689000c2072a900250012204a51040c0c0892003040d4503032500d081c0010510100e400c9440455408041707000140303aa4410014003c161040ea0300100e0003d9055082a2070743e840050401d11110190030140c100c03201149000c4269030b0a01d01d030804c1550b4001d0407419020340a802c00205100040300d1602403104080c9403940042d08010719 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 646580377 1250 646579127 646579133
    0x60d0e010509100908070b061813020f0d17090a090f020304020a0503060408090913060c020c010f0e01020c13110c01090b150927160306150501050301150c0f 69
    0xc2a00b21440002e511507070000c28400d54051007080a1280c2151000e490710703016864241c08000301500c001d820243c0c01c40f80e140000021b0080c140128201502e184420380d0f5070040241603554003107400c0c802d2408452420000d1805500c00410070600e98035035888102840001d124011a5844564035500b041da04100100240c3d0040d441248202ea1504885480d041032644d1050104c03002000c001c8100103800c002e1501c0c6c40780580c4482043d0310002004000d5580c40151603c40d4404409a07002036641d02096811640e906185c08803881c00700903c15100e00001d6403040b080710024001c41c0200c040070480d18094009031070f00e100703500c811981c440c0400c0e8028000c00102109803911185080411050011a000800f06480003003003d80c41c0e0b02c4140c010803500441c0390041e04000148911680001020f005000c05954071045100080b49903040950075502c0300d1202c00d5805410b03480c184102d070782104c1501d056405e00c04540c081102d121005443c50020303000c010301080d0024a1800070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 646581627 1250 646580377 646580381
    0xa02091902070605100b071214090a1e0812040e040804030209040b0403180506040306021c0c03090b060d083f180601060207090c0c08030406061a16060902060d0e01 72
    0x120310717000f5580034840d50781440c408640a0440300a203900003c0c210259070034810800b105000c1581d40e1140c3c5854260000601210442d034800910b0460303e110311050841c2c8011103800600b0020003800d0b07400c001c50901340c0948200d000c1e026081c2c1c1d403c000b00741400b6081d0140d401450303001e044917a81d401c05040802e03200408907800c03800100508020842c00442c11107600840340d02404071418907083d50742d400d019410089000c018a50300c110600c0c00c0b41c203240107407169170000b031701c001400c1041e5007040340b01000000e010a0140a507003029034006444402100c03445c80400a412890031600064103002e2841404510040e9611141c00b81e50142840301c22400303180440e0702002809204035a040c0ca5400074031545015800c048010800c11207076420060b000681e52500c0980b6030b0040d0358000d080c0d001600c09894440c1c2c1c501040c0000c010101c04691105000314031315017072100c0701044092081c50150006c0c0b040351900c242d0b504540f128402d0b14060010072000b0700501c2180003e540c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 646582733 1106 646581627 646581631
    0x20604020f060d1d010e0102030610030504141209040b0108060306011a040b160309050d2a09022701050a0507080a051c0c080708090a02091902070605 66
    0x70090b03004d120395000100004445030315540c000302c2d840d08440c240c0c610b8000c181c0c810000c1c085284c3d41c2001e0540382136914500890780350398500d13000400280b80c01c000c91882c8034240c40715152403455001361088103001d507810804613010800458010b5026185690550800001030000d813020361380001c0079140c5440c8180c54640c3d502400c1c005a400041e040d200b0030401001481010780c882c5010000300001c072201e214044440d201c424a24118604a0a50341802d1325109000d03d40921001c000308610b1100f1519080c496082e071044180100c48031001c00074607c4c3d41d05484d030141056911051496a869007800303255660500a5400b00b910340c414824107000c9802c950500f001d2006103416040c102083d103000d0050054011000505100240407800c000c2207400c0c2d40000d46a0b848940481e200007a40c0c0b0b4051800304003000b2884441c040345c1c00000c8003800d000042e04454 = true := by decide +kernel

theorem cover : BRFrame.Cov 646402877 646582733 := by
  have h0 := BRFrame.cov_init 646402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 646402877 ≤ n) (h2 : n < 646582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
