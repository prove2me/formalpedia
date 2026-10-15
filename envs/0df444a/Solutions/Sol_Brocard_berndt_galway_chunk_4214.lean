-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4214
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:16.027557+00:00
-- url     : https://prove2.me/submissions/2c8459e7-aa5c-4091-8898-a57f3e52e6c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 757733812 ≤ n < 757913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 757735062 1250 757733812 757733839
    0x92e0c1e11010807030b13020a050903060109050708070c0b0103020d0c030503030f01060e12060105040509030910050705060a05060303074707170412020111120405010b01050c100506040209 83
    0x182150360540058001440c01c030204e40f4007846801140b0100400a0090480ca4078668041c4000d601100400080c802e00b030103090210b540500c0318600030f100451005c40e0341e00c0c200030000c1c501d410040088083c401040e130070b40b0110352122181d60550b5416282000800f595040140c45071482d5403004007280720000401400e843c0f0b18148038101c8015072500301c1c0c1d103200482000000d0058a107804015030005004210710b1034950041600003440780c054a140251000119125210b01851407021800c00200041003241c01c1014a0f403210f17150b00304011904003140002d4607440365281c050080450360300b03000c161040c007910100b0031901076101d21450300490384045c1c0482c070544285881c07022254000a9566004080030942c0441900340555965202d98415441d60300301090041199621f840c04802d241041d001803600110500703002d1502d107000d281913800c0d41d039403219503810040c0c00d010025a1000000b42d464001e0142d080200f035940d140c2011400034080e40683d039034007080c1d85800b82c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 757736312 1250 757735062 757735073
    0x19050708040305160608190504080408010c0815040b09181c11010f060b0f0a0c170304050115080316021c030804053a03180503092e0c1e 60
    0x51280c540c0213044240340359a502002d0303d001c10100c44103c002800c0545c1c043c2c014440e40c1c045a4031602c074147e080e040c182c5a03c061400c60312a0354071400803402001c00c0c0112260255042400900201c4040c411051404082008510082c01c4c00c0103410545030000500035060054424201e00c042e103c000e0008800030083c030792011003920300e400f5407808060340691a030701e0280e21300780c800c120078840c80e00d02003c2c01c150140d031100d2804030800400405c01000030702c4800d0712042d85490680c0c13494590429092113401c4504090008881c600180d0041140c2407001c000d40f246504500b445c041203030464004102c00081e0004100354442c0321940c064101034200054500440c015000c0381c2146109140c0c20000395001c040d24482031000440d484a10203001c0300020395103c1c149000318000814994201e1000d8040000702d0341c03a000440d600350b160a0071003a90034580f46e040617000440307602074000309c0ca0300d038203075404c008101000b8134004c14400d01601085008603481d41503900740c480d07406d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 757737562 1250 757736312 757736323
    0x212070905041514060901090e07020c0406080a020d030e0609061207080f07050702210d0309110612010302040203090a0b040606030204140f2a0c0304030213090819050708040305 78
    0x6440c86a40b902c3d4865944200c01d001e0300d015140b00129040b8490040030070415140c0286662038100300003002c01240b00404400424001c45113600200445100702d000c00040e140341303401290080e4401e00c5a6005079461b0f1082d081e40e5034060800300e110142c0900030403041d01c24207417415003081c000510845901d4200d0300741e0b4442d1445507180d00841d1521480c196a030a029520741001a4060011b00c02500d05070304038500000e44c900c20a2900c61940304101c3c100f00c0c2d01141c51001c03d0783c4030101024843d00600d4290300230300072030320365203020081c81c00b10001c80c2e070602001c0d010703039804400980d14200070821480035940241e0031990f24500380c03602901801d12408100d01580c1000740860440002a071000d00444182d40b0a0b2a540c2c1c5a403100c80151450300c2981c030f036204181d450016131705070200007003141a011a01546d91035055006111030900042e548848081c0307807a040c0b0780480c48100c1914087c0065a010506040c0ca01508482900031258003400d90000040c0000401000040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 757738812 1250 757737562 757737569
    0x71203090320060a05090d080c0a2606121204180b040501170d0806210a0b130b010b0c030f0304050a0206040b040602010c021f1107050d201209011202120709 69
    0x4017400b666484441041e2035541459121b8040b88104020510380800b14024085c012020b14040190b0b00c2034000005c00320160704803005500c1801c2c2d00703121241c10801603c5091460070b80083c0072403c1c504140c0301403845613200b51010300c0c400c2c05204c09100c41540000810440041050081d540c540c010410841c81d600400c031001c0c41201d0015240b14001e1105900c41c4900500b10440c5888440c00300c0440b10051040821030b0203201034030b07030000c0c0001d03030001d006641204041041404524054007d520180c0008285c5281400031400070070002003200c907800d1110079050384945a610f40705103400001c4500a520190215002c030f00c0f886581c1c0038200b121444c1e03000f842080c0c0c07400c01c141e8840c840383c4410343c0b10404404609803480040d401801e9911131006003540741a9040d100c050610500e41110000158195006c00394510440824441035291402a01e211642e48649400b0b900c900c4208505101200030801006245941922514598508285014900408000c0c0741c80450301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 757740062 1250 757738812 757738831
    0x10906081f0312090f1401080a021b060708100602010504050d03020a090906180b0906450702010518070e060d0210020d2604020402090d020307030f1707120309032006 73
    0x2c40000302c01c46c0d05030b40103000410603140c40304540c0746c4002e404069400b808580c0050b40d200800f20350005820440548262403550f18110b550401380ba46103001025a4002011681040c080c00301080021030402840980c034140103a4900c2500000c0d17030500c849501c000f000e64680100055030340c000d5a00d0300c044c00ca035a1400c001c5400d03c0b000f001840351054480d250444040213880720040e058141030249030b01e40032804036502032a2814005141d212441c803040d01d455400600810540900516402c130b406204c20703044411403000e0f02c5580d60074a204030094a6600c4d00800c400d034444e29880340400d90081c01c01c071801c00d082e08029544400c20300b01c520005030401240f2800503420381c454001c401211410303a1061f1510340810010703400c1420550703809580040440b0042c1d8080090600442c480c5040030042d00c1c0c14104210089a43c1450301008a4100001c0002421810a100100500f07040c0060090f0031420110303050505443e02c61460900200e40070400c0305d002840341c1c070505690 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 757741312 1250 757740062 757740089
    0xe0f010801050c161b0b0403030c0b0f0106021009020118150906090f0614162003010c0f08090a050d110c040903020a0f14010504031d010906081f031209 67
    0x1090301c61611600c40b400049102c048402c80c0054017001d03a0801000318400d45a415075203540c0f000e8650f83c403940c011804910118001020889078400312940016030b0b401512040d890004040d40f9400e01c081103007000b81d6102c0041046a001f0316804100948860b002520552219403001c603042d001e580b42d00101e00c0c00c210001e0510b2240f0641000c0e2400714003410045450024251044400703010030a64001d4148070380358032252003840d1030300110b00841d15059220340c0c0104c1d04070f09a201d2400f4a00a9040499800b94980c1000c02e066201100e444d00d0900b40c0d50780301c051401c0c08400302c0014142d0140078200381c121036021500b201031041410589001c0b8010784104000c84008070700c000c2c05038204045181c0440c1d040b846041c0c02038010b0b441010b04080464981342100c81c200d500320045008030b0a1805204044001441c9210003828107040d91402c1c240080d0a00304010680f8084001c0c924140c2c0c1c40720100e4410750011030307001016089003a10140301170140f0015000300f6001050b031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 757742562 1250 757741312 757741321
    0x150d080d140603100e03041802190509100503041a0a0b030114070e01170c0c0708030d0207061802131e050f04110a031109040c150e0f040e190302070e0f01080105 71
    0x340e1085c2910325581c8801545440d14100d200031449417100300c084400740d030038455010803514620000440040b07642d00c140c1d40300c084900708150113280710028806c011050042000280361003041c40d401017030002480c803540d902c0b40700035000740c001c2d85091501075003040c80800fa0000d005ea0740c2405440f1340e888181c03c4255040046412759035100640b0a81d900791400b1503001a0032100803c41380b0034250559200d1921200102e18590048002c5d0307240711740c0010300806000262103680081d03101010f000c080c051158002030040c06200e0b007500e02c120395401d0760130502d0301001140042c4c0410750350140014603000c5a40c000c1d0000031102941c800d107400034445943d2400010070000d490780051100f026814013001e004c01d60341c1c0144103c600c0b5a40d2000410190703c0c203c504a8159520303030390030844402fa2410f11045032420040319000354288010b00c40c000c04007250740500300c00d52403801c01061340a418124074100d074070f81c0580c0f1803544460034003001d04100d000d5141a82c80c07060007444039466 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 757743812 1250 757742562 757742593
    0x230c060f03040b090c0913060b04020c0a030f0302210105030c0d0c060f05090604090e07060504060504030f08040509040507171b0603060a030b0112020f0603150d080d140603 76
    0x203400201901408200700050014484903801a08441c100d000c80302400050360200f000f5400603501c0c2000501e0aa400c5001c00000d405000c80b2070005a9095082481c6203625a40d1084d444000905004103c000c024019100380c2c142c1d049112007440c104c10b0403a0705109900600b00030700901d8020700800c01d01c1401c900300410307030102c4540c1c08036180d040513107807503030454200c44a81010340c1009410001d0307944c0399440c800034101605920000160b288160340f5485d2501720603034401818032006000070044aa004070903181200d4110b40c2c1c070000d0403154500313150b040c0b050b034021f15480b1a00364103110030301500207000016658080c5200742500d03407023810315503212040e405331440b40c041056100d040b801d0003005150044005460303012403544942c0c800d02c0303c51090700708211280d500016202940f40001508039032140c11b45103180f4504000b00041e6107000d990401c54007801c2c60b48640410803c620b4121007002c080e407a130400c40c490340b298903c11079903000d403121882840307030100340b869812 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 757745062 1250 757743812 757743817
    0x180803150603131712310c06030c230a050d02070606030203100605060702060a02100e0c032a040b030a050a0c05040506031f0b010c06060e010e010602071818230c06 72
    0x40f0b20303001c0c80d2165070307064601c2960451030724681510f142c068506c000e039070b8614205200441c81264004042d034200600201150840c00c034460800000d22520242c00606d00148140d52b050704040b6646c2e81003840c0140c501d88250000c1254591000841e80d09101d80c0f5808a0296807003103069505544100c0010019902103004159002808006120040ca024402840030400d140144ea0b1208043c0d0303140402c80e04805101785075504290824030f0780346810700000304e810019171940c100c00d21400b181c2105c080110300303006015a59842a400f807a603001c020900e00e80b41e10204a50300d004492400300c407003122920039140221b0500340460f00518000c507080021a00c201d025010f10100000c0140c042d110b020489070520100368003500224002d406840d026041c811700303103446545045141052074070140c1c49001150410756040c031088200300141410382c039444102161910070310120340c40340d40e2411002010710001240200080c2d41240c0c048580d846508141e411945c1010140314003072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 757746312 1250 757745062 757745077
    0xc070b07030e040507030b061206010e04110d1104080f0f010501171b0f120a11030609060408090312040e04030f020303010b0702011103121f091808031506031317 71
    0x4412151684450603d64400f541c0064145404111000c52001090060f4021110000321141d04001c00200c2c0d6000050000403d13400e030380411402d00040c850f2289801012900203c0580f50100224228400ba00782c42c050034081c0c094803080445d0440b940d0b610705204149042c19424200000317601d90758841c003013032452400070141c9006500403404400403880b0b00e04490340040d20714240c41d59621a0b01204511062240091800012508000c807110743d001d000303030b40729500500c10002040400302d0f035144c200303a112408945800d000c0300000c1c248680e180031100e04000200700001d10110444800f4003990003070701c41c0c0d1105242104100c1c4c0381d10003401085441201006280d00552040e0b1401c10250b070301c8000e0707038102091680b4440d0300310000c2c0c51034200604098024100c0402c4640b42c1d000805006170f0410090320200ca0308600302d04050f01c058080080400064407100303002410486140c0c0041c240b694030b02e040d405840c00b9881007003041d0382501d00c0d1800e0750348a415500488464 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 757747562 1250 757746312 757746317
    0x7080d091e0609030320010f0c2a0b130204050f16021507180b0408030a0818100f021614071a0d0903091a030115020114180c060c030c070b0703 63
    0x1154213644041c0c0d40100561a407920342c030303c0a15041c070360000c280309208841c1d00c00310020500c4805c00200a005000340c02000c4c10b410300384c0c0c41181030b805904400d06001544207100b000d141ea035151130007603d904041c0000c0c1d04035003004200311391000d210840510592100e40204083d01416804aa81e03405030205250044000008207001e540034030011200481c06140005105446800318510782c1c0040c0c2c040307070301035101152900100ba0007551031070b8000c030071400702142001048007669071000040003514050b95203403207203a40d5842070b40449041d010051452202491a0720f02400704203803c604007100740c080c50ba0041000c894201354100d19425490542e41026441c0b85007500402c1e20301c070100c0a00065140005000712096070245802c08030b490700645035858a211141d007101c0c03003841901164500345d500100c0110300e02120740c000c50510343c016030004550010794506010b00c03040c0d5074040c0b808910500041c07000001029405580000c1e200026a2584401824068100b00401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 757748812 1250 757747562 757747577
    0x220b0103031103070c24051303031b051f050a0e060f181c0216051c050c0d0501020306040b180a0509030f030717100506040e04020307080d091e06 64
    0x1091045001d010582d031008107a070b20700300c41d075500d251400201d41d00801c2c43c90742c0c1c642d501c0c4041c3c400300168180c0300d06c1d6003091403400c500810b0b807000b4490300340801000c1c041c0d00203516900d40c49900644400c2c59114048072480c50004a1b007401f0a00c9030100f0190b498142130010300b1051080c040c440091b49400020040c54031402000e1003040b400910b5100095108003020056980c100020448090804040446000d82000090a00208203945156045080c20400050700d03140d04004000c0c991b620034895000151500c1802c1c03980900c03203594041500904c1ea81070020640c02140522000ca5040020481c503006105c0f0000091000300c1504040c030f0300040d00c1c076455401c0340b83d1110083c01580d2600104180e4180d03917420565804000411091109842013054280141c10000050424914a250000188917171003213000d141429000440880c0031503e0030000100075100c501c0c01d44080d650401401080034990b8460490608d404034001100d607100c0b81035400c25141103a644070f8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 757750062 1250 757748812 757748819
    0x130b19080316051c0f0801060c0b060f0a09150603180b16030204051807033803010b0a0914070309150209032407030c03110703080709030614220b01 65
    0xc949507640d00050b03610340a214629810308410194904d54413440c0e0b22030994404c401131004050030302c160000c5052003040c4030358801080c0e2102c5103d038405802c43e0100902000040410740711642c6074044a400317420003010301000c0000c50703429002d440d4546d5080040740f050800e00800065181c001801e01a40e1201061110882c10741041c410181414050311f4a071760750011985000f9211400030f0362110350814012416418060261180f0105603d0b00c298900006a8800e01c1c8901d83d5101c40400c2502043d100b40e01c080d04449126003004008884841d0354a14440c058003c84100740a80385c910400a01c0c424000d11419100a4203c03041d58403500d161202080254040e06285a1502c10614414044018140004041d40404492813143d0034010800760a4403211f6180714181030402e214041100b000c04181c2e00383c160545402020354a840788140c41d09221500050541c6007400c0301c0c44441d4851600c014047c4072040d0f95850008010750070038844000118000700120800300041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 757751312 1250 757750062 757750087
    0x206061e150a05041706070807030507020c10170a2007030e04050c090d03020109020a060201090201120f0e03070305070c0614182b0b010e0106020604030f0e130b190803 74
    0x7004000340c1400d0051030316451703210716500c1306000c43c0c0410090b40032104000c180d943c401000d98000c03240341000d000c141001d890180d100c0078211041405030041072000c1825510403200c91407a481c07614440d00701402c11060b5000034043e014081926244c00e0781c20b61028030040811221030315016a144c1c40100200f8080101400f0060701d6a02c4500061101003180c0e030700e008502044520a0300005102400751050160b0313100705600440030359140c0759504026036003000745000b40f40e001100c00104001380c0c80a910090800010007403042c800882c02104046d0000000d0030828050760415181940d01c0000300c2c0c1a80c0f02c0140000c00c408244041d090420b02c4c0c81c9680082903004012800c2d01c3e40383c54280241e1030500940c803040c0c882c0071075034038140030b42c0aa0b083c1c05041c515002c24519030502c04042e5503600302920040401142c0c80613110324a02c80c90185101d07980040040c07502c1703103400d448100500080440c480c8111001880407220001500402c81141c4e0100c3c00365041078045140f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 757752562 1250 757751312 757751317
    0x2120c072d1e0306050f0604051807030b130f14070902042301030905030d0f0516020d050d1113080f0705031c14040f08120a0e0d05030c0106060206061e15 68
    0x400342d54004441c01000040f00f5000c2c25100d42d608030070001c041d00e0501c00704029544081c0c90500781c46142e89803900c4413000070070484180c80e0010035509031510740e0250314101410070400504003040501001e02000075400c0070300561030408040701e004a84414906049208a10a0160000344550350141940358203034004105201414009401e5015840e0181564814004032503400c2d40c4243d10042c100c60b0f446055084162030112410501880d58007942d613203210300c040c0c410700401150440030320300d440d040403040e4002003244a485180e09030004003107004901888030540104400182101000102402142e100800400986003882070648040890552180800c80d00003945525107490710020401060018561a0300c585005542410403088150b00130303402d4400c01c00b02e440c03658824007040ca00c200031110041e0180d034914050340380d8400c2002002d140d500b0300e1800600d241c3c010030f04611501c01610034040c41c0b41c002c40d018088410074001180e0000400c3d10300c1c2c9180380100b01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 757753812 1250 757752562 757752599
    0x50d05031f0e06090408070606081f060b16020d150b040c02060405250509150406060815150c06090607030e0f1216050f0d090e010806130302120c072d 66
    0x4007d1170415540c49160940c0c1c40798010010540c080307071100802c012002c0d6401100c13050000c1c02c000b01800c101180c49103100c6c178802e0030300300b49011485809554070345a05540f45a80104001e044040f5064403001901c038100e01d45200d549008081610940082012132007950300030060034000f04a000c01c50140e84d000d00700c611004030308000101d1281c4800e420b00b80076200c81e00400c401e003046103080000340c86594200720104040c44090010b82519402c100c04000800c5854010044100703405105500500b91240400d00c110320900030075000201d4054040d030600e0b5010700c41070441d50070141d0351368030204801409a01c5083c006006240a40161024803180e02d250041c0c0312158640a2a103982c0c0400303414542c110603407003412030360450013080040861074411103840d85003481568071003000808121448440308100420103109018044a42d0142e035039082d01c0d9580450b00303590303e0619000c0d4101e281e81c0345a0b11108403005060705403981c182c24800c0c81d003842c1407a00038101c0684122 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 757755062 1250 757753812 757753823
    0x1020606101b050601090f15060e010309021509090c0f0d0213050d0819030504110f0d06020412050c40091109130506060616050d05031f0e060904 64
    0x41c5005216142c242ea0000c28500560041c0700c1035040050b410210707051025030160441c5400c0c1000c3c91082c54040c500e085440a0030400e295100650040e4068606510b000398080070402440b842100904042c01e080b030004d688420f2240e4401100608600c00c3d415141c3d2044400d01102c0d65412003074000f01145a0200c0c194244c0070f40e540045031410346480e4040318450030105010140c41440b01e0303100300d0304809207010310180c201601c4564040c00f106084c04c2c010204001c43c071713103a40c441c90710b00a43c4e190f01c10f804542e15a6900b0346050180c1544004031b03468014900481058078082454500c20300c11210041c40104080c0502e02d4850b10b00c51407100603000801d81c4c1007042c4424800e00c030205000c0d0002d0342d59850040104003801d41c004003a0301008151003e09800300d000003030303070540c4100b0a1320350b903550b03c41c01d20402c4003940c40041c0080c02407140c5410441d00d640d204024502507103c10394507019500320800340a150700c04500428035100070301030018a252500d40b2b403507170b0010300a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 757756312 1250 757755062 757755077
    0x301090b090a120f0504051e030f0106170105060901090518100605010806011701090c110f01090203120f0d0b040e0312190903020709020f0903150406060b090102060610 74
    0x140e48580e2440400c9941c2641c41d0000e040500c144051003415403041d1001d0b251100d903801c40298003800501460203041e014080d10015111141628000d04180c030000408490007a00a000b295000c0c000500846030200c4812010100f00101402a030303000300030081400c030150703003810a00001400300a018805144040503c295140c40030301a0f840140e06a040c04560303182031100141c02140c01404031410007140c0d051040c2d05c05014007916065458404011589070120041207512942e40703805070a141c001e6100c0400c1000e01584200e00c2da6100b501501c2c0c1202140b0035030760071070080d0251900b24450400c0440000891a4401080083d009000041c0706582c640040e1450700716403900062100340c40c045c007081c88111004061004140042407142180f41e51b802512500540b007540c0d9401c0d00455034100c002c0440041e94007110002d4104c8854000c80c0001484465050310195402c61030440041813001462041300d040c04410380061071252564402d201c000c0c0e429126440c03c20514 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 757757562 1250 757756312 757756331
    0x7061a0904030c0b071403130203161d01060503040203070e190f050402120606030309090411040c0f0e061305090a0b040c050702041a1008090a1505010311040917090301 74
    0x2001050360103036001e80d03208824122203140c04255414060024014054000c030300105445841003200d41c0407020080007005c04140384046483c0038030405050341384101d00b89001c2400040104010150a00521071850702d0741e075080f00391518401680c02075015000217505000d2a840001169013001c003956842500d412944076003c00c85801070306500406844038107200c103501c0d003045034a01d0a509036011340300e9802c1c030000081da01d2140c810800d0140b42c41a001406100e186102d008424070044e1052025941c0b608006108080480d101d0010480d0a05810f19a0a0030ba05803941c500d80820182c0702e05080c0810000d0814008102c00c08250310b407a8114200c1c0c64034083d000c106403403074550325114199441044151504080101d01e14010b20550345c0e02961400c44410030780c2820304181d101601c82007602c504212440c0c9006d007001104140341243d064603070788014101c9018000d8404100c0140003000107403100d142c005010541600d00040000106500070040c2900050000546185 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 757758812 1250 757757562 757757569
    0x5100f1a090a030317060316180905010203040309030c0f0302010c15090f081e1602040504080d0606021506041a042712140f1e041d18011107061a 64
    0x280c50700104c0c0081c0308800305080c1041e41d4000e00e40c00c24030480203441000d03c03440102501584500c200141c9000a401d04110215207610500189411000030b40d0340b40ba003030a02030a6609284030841c0d403a140c041000030f481d402c001184060b00e50583d120010481d00341c40740440d1121300750701c2070b001a80d69250307440080c6003420b200845c2ca100321b00c840d4550942070403001d500090200700352031040d401c0050b100c8000c20030f01c0711403000c0c1c1d049800185075240c5090a050900600c0c2c800d11007607240074004200310741c0001c0c050f99204000c00f0360f1401d59071860140410b9529030750070142c0c40036114003103003104d1901d600411b404c010381e112482550700d42c150404500800490094411905608070300c0c0115503c402c0203c0c0016441e000036207840d005243c0a511841003944252840800800a0107084480c00490740205950300802d510b182d000e4803080000181901c407021042e031059400b08100c0818014004140f50000d0340904014442c1c44d92800703001d1500b40340e40240700340e03c1c05400c242d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 757760062 1250 757758812 757758829
    0x110d0c05060d05011403210a0201140109052401050a0309052415152b09050f0d0206163c030606051206040e07030206031303020105100f1a09 62
    0x2c4410124080d4908094945594800c0c60001c2c02070b040040c01110340c1c203d41a40103503544000d03603030503592010003c00324014150003110f04080660200001a400300c25003080b40601881c4104402001464840341c00e1005030f4010316004c14004c2c0003662195000f030740b160507414024003d0320f00d2817148166082d014000802c02e003071142c0042d41031161040301c00806902024003590000340707296903a1803402041c090340010014145103920f02103418092240320b4011125441d9041c03202c07841d14078065444d03008041c4405014414506401185480020041e000d9002c038400c41c6081013459800f2a17400c0b14249110302d2001c00034444041800b07000c0c40a1092400310800c4584008000500030b0607035803150305c003808000d4144002c0381816104010780350005408c8400145060541000d203082040a40c0042d42c00003001c401c0000c0300082c0091402c1d010b03c00e40c0204803541d03551101c0d01c2011200d004e62004c19510000c1481018070410f824204241d00702045130a140784400082d0900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 757761312 1250 757760062 757760077
    0x70b160b06010c05010f0e160303051903090f03031b0806100c0305090a09051b070c0b031f18060f08060f040201120e0d030c0e01080c1b061f06080103110d0c0506 71
    0x191f91007226141c114030901004001140c0402e0a4051500e1030301c0080050084c4440c03240b03040122a4244c0506000c1c1d44114001540000300d1301103100b582c180a001048040004040c0403015194144024401c13480765103e2100204588400c900c20b500882e5082031402e0214244402005400c82070b94130700c4104001030031030b440081514a0310030750301080b00c40020500e9150315004e2258100089100386060103440002c20307141d49075515a1410104803144211002c445921b0030704c08201244d0b0703524261079a00d000d40c002c1c000241d503a1245900040d081c0300b003000c00d0b00f1441c00f2903a082007110466802c00d00500d0800c643c14a03485441c01100c5d0704800d04091540f06907903040748140c0600440e607107030710b031400c0107413540715410006407200c240140407106200b80000d030000c1c1420300e0304829052064500c01c840c654078044038102994a8001000505145031000005405200f84c00840c141ca40c0319107070440f03500d1000140181140d510008840700010440045020388844020300b829 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 757762562 1250 757761312 757761341
    0x605010e011a0703050a0c0809090915060d03171f090902040b040204150c051e100605040608030d15090f02090f09070203070f0503130611070b160b06010c0501 70
    0x32545402c1200c42c1e809400010042d008105102d2500070940010035199900c0884c1002c060445d210300c1d00440e00d00c41c0103001c0c0c0c0c0c0410401c091040c060400513010714003109484020380181c55400411210a40130400103001444001c488110a25140038070354002c058110104040b04441035510000c545a401c803559040e03581d0245020b5150a01400081c004251000c610389810486041310238407801680c0403c0c0402914401c0c02c011040040070f40d010041c925101441c010450f601c3e40b6101e001d420a000329040c040b000c100c07442c180c81a0400c44115200641c5046c80fa06182c9000c0d1149910200c0308004081e00011098401d00505803601241500160341d4401001000804128545220300400c0f01d00200084c4503000001ca44640d6084064152940064682245507100d1841500703a950305d10080000e00580110070000c00005001c141c45099448001d8110140100d89904101402c9010300d0b00110f0039058030343d0307007003e1706240414228409446032400d48601005040c40b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 757763812 1250 757762562 757762589
    0x1f020403050d050c0105010504021623060915060405010608160306050916121104091505120c0901060e030c100318081e041a2203030c0b0906061806030703060501 71
    0x10044e020f11a10b400b40200b11811401d00b2295034200c9504990080c000308050804c07802403610480e1a489d28040c06044002c880440c50406075960f12404940648030381c0e200f060b4041021850b1600415058501c039a40702a00d0703664055450070a00ca0408808060540d100004101c5840d0030300f11500c030700d444509140304c0d4101071034000c1800e607103040384540d8245440426501b000083c0c04941c01c60310b40c41004034000c0007800d2081c00c042c00726484035620050b41500900d1074000400c8a1000d00c404272400080c3d41e07030f904010307104449402181a4141c1280710980c00c0c0d40341c10f0300c00c4480301d031249c03600041c41c520305040c00305000150b00741a03c010a01147e803003001070840104068003115480c45500700b601d041e2201c1d117861101c843c4441c50080106011100301da076110303903024003208002070441e0f0346e560b410007600c0c0a885031000c2c2d96500885001405a01c0001480c82c025000a460741d035280810b140c083c602143c0280802c0c0c1c0c14010aa40000811107901034140a405414007040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 757765062 1250 757763812 757763827
    0x2030a021c0f0c210b0a0b12060a050106020d020615010c080c1b032404080306120a030f030c030605010e090405100204080f060912030f3303010e0f1f020403050d05 72
    0x20307411480c003001d034100c013107050b01c100040e4000d01464101d1103a1602103407641958001601000c41101c1e02000da1007403004120000400740c02441c1211215001c0d036003900e50080c4226104d107000c83d0024003070f90850207420055442032100c401018041ca0603142404074020303040b4100350442c9602104045180c40307003000d5140500400c03c0042c2d803c01059566007022030f02010f6440010006400700d02c000c000a0700c192601c5a144941c1d510041c1036825018491602030a41d105911020002a19104050303a040b806841640c040d05c10513100c80c3ca08004010070441c60100040c0200c8031030040e000c00c120300048600241002e48007501c040c020380030041d5045441c04900820720b40c1c01e6401841022507034036a00b800c5941010204086e41c0b00703940c0340096100c40015401c400e000d040d100000d00c0000750700400c50004100130880c000d22a013585c0c01c8456a84901c6010300c400240c0103001c070314013030800d0b01c0410740070300e81d4402c000350070245c0d25151035040c1011407401304d010820008a00c17 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 757766312 1250 757765062 757765079
    0x2090403031e29062101090b19030206032a04231c0501090c0603090620090d0201020109170c060108011b141b0102090f0d02030a021c0f0c 61
    0x14901031411000c220a00500700629200040301c840c180010800c200f11041c99240c0d00125540384c0c118414000c0f40c121881c034040c111800c01d02c0b0b8806150300d045203403d010302d041607a107101d00300400c521a502c00e045400700882540040d003094075040244d03140641d6440e055800120003500300a0868030780e850220b400454010b2680481c4140e2010310380c0c041da03582e4001201c100d03040e610001c482c004642d842c11074014074441c0c601802003281c80a000070061f60681012048501c141000c0c050321540e1004034424003a035020342e41241c9014000f580b8035091071014149114014130020070180c4e002d0301c0703c0206003600045100740c20000607903000351107000c001190040049800800205055281400400d03200c0a1030904000c03041110f01442c0907a00151581c914007900040281d14811341ca96000b03500007005e040c041c004109942189150484e0301517446500500507150307948943c0d080000d13035180c240c1d50701d103400b1381080d024002c124181e540341c0610748101104490181494440d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 757767562 1250 757766312 757766351
    0xa0501020a031107020a06110f01050c13052215030605010311090f0f1b044a180f0a0f0b011418060a080d020a0b01060509030703080c01090209040303 66
    0xc001a0f40c4040295100584501201200302c0340c16180010010b00300e01005030070150300380c8103c0c04640c2010f061000c00030381c180040c11105e03a145000c1c8043d0b5528000e0128440c24401141050325a43c00104a0b800349a00809942c94980b02c003030281d29183d54803007040300c8003038106841006e0340c000040190b040120403039030841e8224400480a28003034540303085005000700f0000d2090040008000d0448600c070a95014250300c102481c128007030624404105481071658125400c6000d59030b00704040b00800041440e003900c0b2083c5440e565103030f4102851403c4030f9218800e4450101d03502c0708801c0138802c000006100f0103c0300282c11040c203100541200c182c22080d80e820301c0c1c10708480c165a40c01888003084006200590080d6128000109220b103a580103800e02c1c018130442000240c0d000c5520000d140c411b141101c0c3c240d0700c800044965000340c8480381d070140d01040041c4041840c040280c01d81c0f0802c8000487e482056a002c14901c1c4030945046004c40d446654080b19014103101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 757768812 1250 757767562 757767581
    0x3181c0312050c04260703020d050a050d14091c050321010f06080406092a030519030203040b0f0702130b03010f0b0913210503060a0b04060c06021b0a0501020a03 71
    0x2403c0d04007420f0621500041c0d400080c0361280c08034422040c11030b04070501c521402140c0080c0310290040035800d01e1500d919464004503071602510340400708403030094400c5c3c45a0b094005040c1d040c0b400004c2800b5418080d501842908064070300c031440000c00410080c90301801401060014031000744200401c200b0603040100062a032540500116601005859005800141c0450180301038140311a94034580c00000b010400c0c0b10169a0681c0c1407540b400c421644100202c4001c280406c8000b280e1501001c00100182c00800040064a00d10401340c00c81c0415080003625000d03c0340d000403094a0303003080c40002d980d101c2c05500102c0c9428031075002180d83c035080030701105100c0320004200410080c180004242100e80340c03428800581c8803400e82c4c518001c00141d5403e2102c90141154000701c400398407440c660003000c21541d03414020340d802c031a041e450320310600f903a03035a503a000394110140540c3c8500889424100c6500d040204c80322480c0138200040c0d641716800d10007000d8401500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 757770062 1250 757768812 757768831
    0x512010f02030a092306040b13020a060e1e0a050103091502040609050922080c1216020a061704081e12240609040506010507021305010509060a030503181c031205 71
    0x94075031741c50400f140d480d5009520115280180c4e41e0a948030f05c0344082588060342107040d003000030803259003180a00040d001d04444680300058104c54000038500400301954000b2403040040046500070f40041036943c0c400c080700e055207030000d8084d0089801c01d0b80048002007404a08000701c1c1400d81c820f68000b4007040f01c14401041c0c1c2c03815010074401c1a44005c00310940001d0140144a0510400003240d0343c0903030b4070343c0c0c850301104031606c069040b10050340308155464000880c603010311150403120b100203040e00e10560f10b0340c65921080d0410310794000303040b0501503640b030482c503141e0007000c0c51503c60300e0900e0706041000015080d1000350404820850781554801100e44c0d031f01040d502e04250031900884c155550100403203043c0602c00340203400c24496000f910074244185c0201d07040c1c0703109a6044007103581d08010402c0c3e0b04014440a042d5801c104000300c1001180120504008005801940744468008a603d00f44140041c149d000482180341008284014007075241c0101016 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 757771312 1250 757770062 757770113
    0x200f0604050a0303061d13140a06061e1512141614090303250606080615031605010c03140a17011205030327030304030f02010c030e070512010f02030a09 67
    0x45401095590143c074141c8501f45041d4000300b0840c51220009004805074140c0f8102d50003803038648041c018500136040c5540c40342d9060050317000c3d450780550454064600c0b0b4100c10240038020340750300f10416240b040c041d80780c140000d0b0350229403540500940d025a10343e40040020a00180f500c400450801d000000c2007200181540d0300009440896140141e1140902008818682e4580000b00c0041c502400e100c1300240000001c600d4030f115911048042c030011880000b05621000140d440420042c418102032005502c40ca0780141d0b0984242803440b00001d20b6002e00c0c0380c0e41c110189400000c1c00300500d19101d850041542801000c00302d18a6030450240d40c0c801380c480c0030040c0001c0f21900801c1c043c020405a41c0811480030b181c11007030700c0d07072402e0a04008204607588000c0324059800d141ca108241031003445030304440c00410025100351400c00c0104013604c0f0182c6c03104000e5640322080602005c00620095002d81e07004100003a108503c0d2402d906c48028256503c1c41c440d410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 757772562 1250 757771312 757771349
    0xb040b090102014208060702030a1403041e081608040906060905031b0109150f1d0f060c0c21060c0403050d0c020a1206050a1506200f0604050a030306 66
    0x8421006070b84424003684c40c001090b082e003401c16014150b9000c110640310300d800340410660080010185a5903955035040c480304521644950781c402610010b0500d8000946e000c170030400d40e258808858419503035245003204c5070030007944027650f8080070f0355841d074002020068205030703210b5600201440c1c2030441e04107240900281e210812203154080b880400d00780340b101c0c1d0f889030400d070002d041940007020700004e4250000b010584c41e41c0081d00451039007030b0403000c4045140c0740408491001003c0d0842d5503612810300030660002c00c0c12451510810201c07203502e0785c407014950752001d01201d00305007128251440341d1a000c4082c00b081c54000c010030040c804200007158800440300350741410b070f884003164404182c050803207910241842c071000003500c040048641105005e8103d10b80207100e8640072710301c6d00c1e0703c007130b043c0c0309000c0496400c100c00080c030080e0b031010b0030321181000f0079a60b090710032061040c1094401c903070485031600265007800030550180310b181c0c01b03028400e0400a14001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 757773812 1250 757772562 757772621
    0x60302060f0705070e07050d1406060a18120b10061e0e030715030e0705010e0607021509060301081c050328110409020403050c0f0603040f0503040b040b09010201 71
    0x103500110580200c0020301c0005003c004c20201005140da107400c51407030300d070440c00104550840c2042d034258505081411240050201c1001d0007802e0081c0030601d0428001010b41d032065904020340f014a1800c0c1c00000e4080404050b0304000d401030404080a2401103102c0342510450340000040c0210f070b10400c0020703c4906042d2146518604009520404070000030780b038190ba6034441d1032402070100501c502558103400509018400c0780c1150b104c80e468a00640e81061021000780d00400203009400152a100ca44041d076440d00040d2107150007040f001145466209804c200029402440390000041c1607003441840f001946c90b01034114105100e943c030010029420444a0f40102c00450207101e80310760122513401d070428403d6580c0c903560400d01019401074130065030306004460390300b0124107005440f042c004400500c05881c6030b0751941c5000d4401821441682c5034032050201044118111009001401c141404151180a20300009080d0740611040600c01206a4683d038403608 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 757775062 1250 757773812 757773817
    0x1d031c03150b030103081305030102030c0c061608160c021206060a060c08030a0c0302091807090e04050c0d080c0106030501022701021b03150124020d1e050f0d0608010f06030206 78
    0xb0b40c403284059a801703041d1f8070b0012407001c03070304841d9040d4400400d20a10030221402002c00d10001e10643c2d6260351070740381105401000d824140d011036020b800085404030184546d146ca0025400c2104654016401042881000a0b41800e8a40c04001408503a00d04021014020102481c00c41b0b00c010301c55403031285601020346040c0c0403640350300c0c8422219002e60140e480900f006421000a40d5210500000c0d5410664011001c64904a40494042d000c00f101c14803440d0044014484100e80b101070002016203090180c55034002444802503411080c0100c100560140c1d0000da220700c6505098010507a54004100c580b007140c0b0054041640c02041c4020340c0c040c2462002c3e03002070602c001c64200020032441c1000c94020f1400403541e09201d0242208141c0d502500c100700c103075448820307a520301000009001154641c1403103c446a22003140c00c6812465203000e0341404180c3e64203a419810242c0364419260b2039040600c00214248140680601d0002c0103000315440c40e0042070b09032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 757776312 1250 757775062 757775069
    0x1204120b07050706090b01030201030608121b03071202030307120603051f020405060d0212070c03080c130b0f071b0501050d0902030c0a030b0a05060906010905011d031c03150b0301 79
    0x14410025810074082c006580000d900210f042c00040c16070300c1d08200307041c02400101d01181c41c120012030408000161802c803205900c007170174a44000c50044401c218001d00c512005403000304401030000d11221420794407000d040d00110f40302c1c14494005401c03075903c3d504110b0894a0a01c003040824000520007540341d48001c82c160403001b040802d079010380b00faa00440e03000400010540d43c0480389030700a0140c1d80511880e8060f54036100d0007114000003903800a000030326440c0118002e41001c4000300301d80200702c0d201c07068190341d800c54284103800007a40f0941c10b4602040c04401c0c0020800d507401a020704070000d4426600f40390001e0001d000311720900d09910340c0c40c154002191820007103020030000040980607401da032468910001c10007114030520450400021aa0905048088900455050319400b40490900340112506648050a640c0c180b0703109407911032a44052294401014109590b19031401011002605440c00d0080b4600a00203901c1f0800a20600ba07003600d056 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 757777562 1250 757776312 757776323
    0x130b040f140129121b0a0e041d030417010b131407080702030f0d060b030108240709060507081621020f12070c080303151e030a06050a0e060f010602120412 68
    0x130313481d082c090001100d0401d51801d8100b000043d1507101c4c0b604031080c201201b8003104c05015000040718405514482010042c0c4241d100340f00a1000540c182c0805005aa44000001e91494424001841c140041080310316107a07480b000c0050000c0d2245103103a11007014241301a15042c20103000356603214000d07424088440100d0128103180c41608044014203541c04c0d4680c0300d5858100082d100c22a09000d030070030803050b4074242c01420013110124495000c588a0901c4d6500e480025070f8180d010281c00c4070410001c20111034110b1000c10403c602c14020031510820062501d400b6603e08840c6200c1801d66118030000004117800141d050401208031944a80390002860003400c1011341e40c104c4a200d01001c010000d010440228403140d14404543c900302c1100306406500c520151503000942613081405400701042103900026004009418005101d000030015542401016140080c10700c004800400411798100f0000c000e134181c1d0540c02e0300c1d081c0340c80e10f5101c8040c008a002443c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 757778812 1250 757777562 757777597
    0x3022101290a022d010f02090127260109061d0f07031b0b160c09021c092f09010e060907030c030b15070210020606130b040f140129 58
    0x114004c400c14030191035403a28024001c02e010b03032043d8070103034004120460000c5d5000c04c0020800c2d00010090103c46044280e0b541045d0070030051010001407040361814103080d494424401e0b000034450600018014400007404460351004a00c041130114013003886a40010900707120321030042484401c0700d1340701905000080b1803c9828403c8180d540c0a8100050040b400b040240054120048024820714070310140315200c03c1d164080303014018145041045405202900c1080c80d48200b01c124001c50380e580132466185030600111462034154440f08100b17560ba06410f0070010209405440e42000c01c5003140b5014010840d0940d005006c08100340d290b02d0b00240580c003907030211805580141038000c80820dc081c550041c3d41c08004128004c0c11600c460f081e01510214031107009a8000780031114000c40303504880007520391040f030b40b070b40266190046082c5410b184950030b10000142c4021480e98980170351242198000409805e41c140c50400c601002d4420008445030703a40c20009005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 757780062 1250 757778812 757778863
    0x10b0108010f140d02190609050d0b1314030414120d0804030c0c1d040311060f01090b04020d0603031701060f0c02012a2307050a050103022101290a02 66
    0xd419038024040a90801019110f00c03006490101c111010f64400388c03a80c8051548e40c80074002c8042840d800500380140160100380c8038007410011604842c01000001040840b04c121070b4150f91055000c2410304000200180e21420300080010b1888038101c060034084400000103010010000d0000341009015066502088034018100010340764001c042024076a135541d45504c4642c040e0380540c08a5618418207580b00000102c0e1840f40307401c507a01040c00e900c0c11038190050301b0240040c81c1c0c000c1c4c003031180c50a454041e1092400a50103552100e800b002c000510141c21351040e04200b0070040c1650b44031401da41c000c160004941d50a00e800c140c820b420341f440008000f80a10410888a0039000100c2800b10000d40728203140401404880c4481c1c6250311a90b84000603c0b070a5046642040c0800ca1580650b028018080910045c0030401c0700d04001d00210100917001000211020400703e58081c52401001c51b0400807051120314040c0c00c000003a55034540e401d00c0d0310300401981e8156 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 757781312 1250 757780062 757780069
    0x10905070e0a0b09300601030b181c2601060f020604050601061b14010905010b031906020c0c0306010602010e1002091c030341040c0b0a2a0302010b0108010f14 70
    0x1c003281c410100800180e4003400203182c6501703080c407095605500b01004500000d0350201920070f01d071016030051140b204c03802c2e8850bc2881c80708103004207100e0042070340158058000758601d00c0440c001c4e51a9055810110003074041c020340051101154011010003000581c00503101c1d054914a040481c0268202814039000c0814880c006090100c0d010486406250540081e82c1c4140311b000203000a20413842415550320400014180294005550001040341603004102100050307044d602c00342c40c60f0011038070f0a0001c1c0c3c01400140e640d4800301c0005031f028000140c46003044002940b500d05a00000760308400f2100c41c2070366141c654800c0d542054001c2d400f10100d140c040541ca06d42c140040794801060700b0005100900d0041c11404020402c00421441e2042d035000c0101d465403414445402d04d1908070440c140140040e01c002c0d000d40c5a541d00d54513400325155058100000380d10f1030000e0035150020140d45c14401810014040b507a15081a03a06a80c0d200030032503404992903000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 757782562 1250 757781312 757781359
    0x1e0b03033001090b06040b180405070203121b0316110d030b0406080309030325080301030b0115030506060901030c02030f040f0e07020a050a0b0618010905070e0a0b09 73
    0x8103040c10940800d0750100646a54075890051144a001000c5a980b08800020f552001c650030b0b5009004000511890074148080c020040140f00e02c0b02c20f00301e444001c0350890310f00760341c1c86016030f20128050b21545060305010380c0c080411340c60401240128002040c541c0400f0700301201d011031600150101d00d12400c81428800001d000b281d00c1d102e4000005402000c96568180c040c0e400e00601080c1c3c4c15000003141c4819001500542c64071040141c50807010f50440890078207403c11021190110b00124055070107180916601d09440d4500140b0b595010303a150414011306060a080060560300d400546040090a090124203400034600132800d51040000704035407000c0106000c102d048903402104152204c080151066403142c907402c1e6601e18203510300a200e0b900c10381314500001d013030041c0541c200c200900107402200c031038150700003040c40076000f81411543d21030401c002507612480401c079846080c0e072a4000b1a04102106051b88641c1190074042c03101511030140c8800074151 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 757783812 1250 757782562 757782577
    0xf1e0f0e19060b09040b0d02090403030203130507150909090210050f040b07050703060612080405060a050d18051209010225051f0207051807111606170a1e0b0303 71
    0x400300078031510f80180c60015049601000c0c001e51620720400c01038184800040320054008244803010382d02ca42e4100c029600040000c3c0c240300680c0340203000501c003088280040d0101c1c5c1207078070071820f00040003050360f074103640a4002070f4100080b034005604c8108a0884c656020703c0c1c40c036507604682032507513043d225603880f640d0b13000000188002480400304172407096a1042c5014801d60395601007800b80c01c0f90403103000d01490b41c01c000c1040740d031600d48003c00180721541072060800e80050386803c03c0b940c2c805100c50722424607445141c200038040c440024000b460840c054185030310140002d5951103402c580608500c7d40e0715888185440c0140900700409006140039000f80c50101e0401d0014000d60740b400c0588622400400c5074540442d842c244d40074002d40031003440d0f80d503200840d01c03050002c811403454003c1001c01e543c0d03040f4a0810101411090712640841091040c28038101d40307005000002c0c2c0341c6452010303008891815803540020601b1103022400c9e80700d800010382184917492 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 757785062 1250 757783812 757783861
    0xb060a080a0b190302040f0605030304060e0103090602031f0503190b04050c1504060e0402250f211d032104080717010e0d080c13030c0f1e0f0e 63
    0x114444040f11500c000c2c401903910070380701440034680c00445541621594022540c0c590414041484000e00c2000d490709003a00500d400301d811840b685561003264419036410241c950f41c030021555045000540400a040607002404100207044007000f00107a641c000402c04002c0c0340215081c414100001c0c00142001000c141001d034502850b1503103544903201d00d9004c0343d0300010740341d21440c041c400e8884080348607640c07079400041d00103140003094001208580e1380180c00041c4002c10058801040c1d20014500100210b90300c54074040c01c03180c50085a6460708a2102c040c0c83d880d00c0c085159244180c900c0f0541c2c0e10652010112141c500644c3c021808900c03454000007120042680c01c000b10b2800c1600070000c101150001d16103c00c40224201d02142a01c8040781c081172680004000800c11030aa13022060707140e64540c0f0324841c20303901100300d400000380706004907a100340c8803610b410386c003645c0a03c0640c40c1c00c401d02000a120b02c038207145075a003200024801c1c070080040f01807000604 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 757786312 1250 757785062 757785079
    0x408010f0902010801060c0206121e010602030414222304060f0c02060f012615150d050a06020d0f020d1a01030204080309060d091b0302040b040b060a080a0b 69
    0x2034900c00050580700e60a0b80000d400c1c400000d0f10034015404084040c2c0c003c3e0515181030801030703101042c02805008031b95110440c0c14821458601d0011150103030000ea400380d586e03a86041110a0312026002d100d602c07900441c0f42010f20301d206c0c40f02d00380240d85100000700d0081100510101480d10181c1c080000842540800041088a0788214511170b8202c0d000c00c070840001c0c02c12a40e69504488010b2403191715401842084d6a00c481d04d0703d031700c040d11110109160044816820302e41502e030740c081c0c030440f40800d000d01d0201c140310031142c0032410307036040c040d031100ba44815540da035000c04d01038607480c0d0000f56201840480d41090805000c007110965031200000d54042c02030200046600b90340c10640364509803580b19000326000c23a00c0c8440254107007162102080180c0c0e01180130303c1030301552060500c0001c0d40c0e10720a4440007604058141207589140140003d481c21200d04038400e5141401840700b9640b42ca013514480e007000d141200e2036a5581300311000612118140e0381d8044c004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 757787562 1250 757786312 757786331
    0x3071802130b09010c1506050a09050124020712170f03040606081c140c0f0708060901140a0510080613110603070c0f06020d11070201110a0206031803040801 69
    0x680052101ca038052070050805555826000010b000304190640080c41c981d42510100b491107078072508001e60385200250350396881c00001c2031071400f90b02c4030501503215001040342010b081c40c8a00107601001c400348108005201c02902ca0074640521101841d22406450a0100e0110004d40300280030814076034840403400c4181058200721000c56005042c09008640c00e40b010415603442d031030342c1d203101401100e40d040646914100b085410020706050154203940413040081c030102c0e541c4000a07140355401c01070f00710309102d001400c400807681003d00110ba140158401e00740e115121202c00074260b1140305205c2c1e2050302650101203030b0710070302d800e000f5501d440401c2300740c0729885526000d40140500051000c10b01013200c007440030039010030681c0080303649900349250240c8139043c0140340c07100b58480002110f40344c00c26969030300d00c085500e00c11035030402280744c43c1c1e081c10070050800c070042d503000031942c0c40010801d40c02a032501d075042c81b006804200b540e01600c8090020300c540c80c01d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 757788812 1250 757787562 757787609
    0xc0304031a15090a090201050705030d02040618050d030509130e100605040506030303040f15021201051302070c17070803070503132c070e0d0b0702061819020307 71
    0xc0c4140021144a9070000ca610075188002c01415041c0240c40c410b0755a440c0000076004003c80f207420307410300404000d52000500d040c8001c01e003402084200680b1103080c03050082258881070008054100204810b00007992074100450001c1d03803614203150380300d100c04045160442410742540300c0c40d0a103040c5546c095004240b40e2248076464074104001c40e9600c040100355503056a82c01d8254004001090108003801060b0703400d907010781706404070031221180031003c0364000000c00c40302c503d0001c010311052802403401104194040070960a1101ca030725200104d02891191070409500144403c0800d01c0034495400202051401d4988031540c03800c000b600d96020186075100d910b40e0100100e503c0c80c00522104072481d282c000d29001c0d440d948003005031010007034129070620101c02c4254106035103002001d10b070280710301030301c1d03186060040d406850980040e100e801e030152200c00e0b0a081c48030004140484055180300c0d140000418001300c1d0405299400c028407035512024a8030f000304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 757790062 1250 757788812 757788833
    0x604020d060b0910061119020402030a2c1504110d032312061008040605040f0803010312110105070e010e0a090606020a0c0e0601090311040e06090c120a02010e0603070201020c030403 80
    0x1652903c46e80200300070040c0407501c901001e0000c000707108128030150054101a400796501601c080e900055010141d200844541300410340907100d01d00c4600007002c1c01e1410b01c40d135031500b4001c41a46046040035603490a0341c80a880c4140d0041d010406100c00780f510030401c41b15881c80844041d00140d40704600038034141c1c080e142081e100c0da00d50001c0340c814100116407070b5259019541e00c0c1c9564813150b4682c0050300010b0416681e0151105072131000c11070750001035008500c2049408043c00e11520040d220419500007064181d1402c410400866042a00500c81c0300c800d18044035031010701c1001444c101003e4000101d00d0346403a202140700350f00091100d000c0c07401101d56292103540c40d100084411000c0750b01c41c2c000307840382d0400c00c001164840c5e0b11038114401840440d805988800381440d024086800107815840301d51038244505024007071421045001028140e070070100d40010b05141d0342c0d040390f03501480001001514151007035041d54035540301603051f290345660328180f100008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 757791312 1250 757790062 757790069
    0x1810030309050d1a100b0a0302030123151e0d05060102190c0b0309010e06270106031e0819050301050a09292b050c090106020604020d060b0910 63
    0x20340809000c50b080c039101e0550f00580350300054a10208041803d104200580035084140a005201000c030348054404003520900c445542c1c016100e41c500740d0900c81703802500380c4480140d0389100c811291901d90214900e8036081280030307030f075407004105604107608440700c051042440e000300300441e0300c0b00c05030080360194030240d084540030f280c4210310402424044100601043d20464100144003807600078541c4642130000004112041240700c50400c002214002082005c1c1c80302c200d480c0c65080c0300000904550785c0204209400d5a4510584505008040380003081c10004041040780380f00840b180c00c490380b8850300b0224900e036000341c01c82d00280129449030600b10004614010244a03207482007548240521000e10101c00551f81c500c40d40c5410358005c420100d100f20115462480000b900756445205c1d1403070002418100d040a8054100e00e200b20700c584010011258002045a041a01282c5069a0040c2c42c60800c0040c8079100010383c00c03050140c20006402e80d0500701000b01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 757792562 1250 757791312 757791317
    0x6090609060509071218051c120911040b0d2f040504211404060206160201020705100f020d0504030f0906030501050a1a04050301050103050f012f0918100303 69
    0x55501d4508024040c3e000b2190040001d072800295403400009402c0004a10710000909a08088544800e4140414074085540d41001141c0c2d0703481c01a440f200000c18500c1c409410090b040b1180c0d605100600c840b101d0381d00c195125841e81c0035641e0341d0030691900c203921504414040031801e003100c9090421190b120a07070196244004d400d41001d020f6584501c0d40080d011a03030911411000b281e044001c02c45a003000f041020300c200781c80900d00148040c1c00690000d080c1498174800f5540701d0603d0084140440e4010f02081e000250001401041004248004106882e514200000038090031800c104414181010320083c5500f1001c00400c4d0300203580c52000c556240e90040c2c0039100e0038400d4030f40040103108100b000c40c00d01103d00c58400454610f151815640714002800d5800a81040ea110b4014854010706003809200301404243c20141440403040d06000060340d040040049000b450b500040701c1c2c0302a95440100c1c55516210040c0c540350382850080b0b62000d40c0540401c901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 757793812 1250 757792562 757792571
    0x1701121b05330708070609110901061d040c080c0c01020708072406080d1101062c07080105100509030a05010609380105090a0f0b070c0b09181906090609 67
    0x7000d0b50100c1c101e900590f0001c0105140c12100e503201c0c80103140c0e2090a0350006a056280c030801da4401c15054001d0817203544031030610b80d0f00c0b2040c501106011031024826890b0865810304150000c14003540889078080180d11089004c070203c1c00791103101e0004111540010781d8408100c031100c00d48000c8440d16405400c400b003450305080072505039025480761940007a50207a0b0300d80c45242100d40d4208003400100d5419580e0034400303441000300f4141003451300704190400780040b0500c002c2e6846185450710120710351511010880c0b4003030120122040210024040400e81c50400036505044d48c490001c0003201d648800c00d10080900714480362054801c0082c01c00d840301c0100f242200102c10301049a0510780100041d589941b02c902c01da038001034100700c00180820f640c507460700140300640d68242d0342d001914010004080da6081a0405c0d00144135101d01034946490704c1e8800c007078880c1c8a84840c0c880d411046442c001c081d08412034541400300c0410714101d16005601152541c120501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 757795062 1250 757793812 757793899
    0x50d0c030c09090b040213121e120f050c1e120f1803011103010303020c0306010e01080607110f0a05010905060c0405010813030516060506011701121b05 67
    0x10250780000124100060001500707102c4580c050303209403844400144010f1410728100202005904107600c40f42c1c48024240c1c407003050084600d4034001b180010308500740030b05490b0703030b41101003103d004200040005108040e0301c0d43d03015100f2900503a41000c11a051000e10400020700c840450107501e1840c000d6181e02c500c0d603034004040d2411501c00115039402d010b40036085241d40c2c1c00b541c8501d80e0540d00c070b46400010542040056010b50300960140c408113107007000345450208180d0154416014510041004400218031103400007140d14050254000b40300e070440c50540494000e1209000310100340d03040040550006600710b110f030040c1d504030703543c001070030f031031401350344145030100e219040000e035225041083c0b41604d41c8039007452801c1c01d9805d80c001a4110280108450340e5035588184100e640e000742511440902c045401d6215604180711001401d00342c01000f020006189490880d0800300c038030311b23400b41801629001501c01c402d0b40b10206502c1001c2100c1d0350040504e44030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 757796312 1250 757795062 757795067
    0x21909050109081b0d0b01180b03161503090c0b0a020f070e2205390102033703140c09060a0f0324232419050d0c 50
    0xc41d95018040c182649581903044034043c0e80d59140c682c0a030300801e40c5d8000036201c640241c041c00c00c850042003485d04419000d0210340010302010b03c240e01a0b040e50403000b01d408500000e40f21029200e01c4401c80151040d4080c001116004114400a04004c207401603860050128510319500b00e4111201c81c0b15519100e200501600e10144003403000510026171150f0901038512038500e00b90500303070fa40d86911341452040080c1c40444480307001c0e8400c0710103248000400d040e540301080b0b1500d440c044000b0b50f60340314202c404d000c15003580030a111001080c10584403100e288a4103842625548040280101513550a1401008140c3c01140581d045002661f0782d00c0b1001d440203160500001003904c2071000e41d000003041685812426200d41c151403483e460000e98000214219403c011040313580141d02a03111140d100422910001e543d91100a4000c500f46110301d02c44010480d03c04407514846e1403c0426504084940d6142850740100144400492950100854402030300304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 757797562 1250 757796312 757796327
    0x130e01180b040201050c0a33050f06150f0309060402040507091203080a020c0a03031a0f0108010308030408040b03040804080105010605040b1b07050307090204230307170a060219090501 81
    0x10740303140703100300004005500800c000c1041c401d10100b203c2c400c81043c0d075016403203880680c40d418002080188042801d510340716820707c245440205115525055000d0601c000004080d18440d1300c80d2084000c0c100781e0b00044404a004c40e144613a540e2501c01c8615560b40420398080340140e2070310f00020307240c80c4a030284c002a02c005903483c0c0a43d03d0591012a0b10080c007504500d08103508220840c2005801c10540362854070a440204041584440c051007080620441b00d014202e403104104107aa4400340080c152a40300e56915142d031618107050200d40195005655680400000d100a00c0001c102500403215080001d00007a80ca0b12030895003030040c0c3c0f250012050061100e44c103035440b00040901c0320441101103600040d03131071002918000e1198000d91b90281c0c00141801041426038802e4948010201c0c00c801407150344020950314280d9100b0709084004080ba2a141c0920078001810076940004003951a624001c81080e4102c400d501794001042045000154a5014040c2d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 757798812 1250 757797562 757797611
    0x9120312100f140609040c0f030f0c0f030e01060305150411100507081602060307051305040501150804080d060f0608090604021f050f030c030912090f100c02130e01 72
    0xb40c664614111242040c04400640650301400a029120481c1c0302c81c0f0440c0c14440310350307980c5003085210f100b01900b21b0f0b25056186070528200445034260b540c10100c1959602d0203450005501d0b175460410500425494000030030ba4012800c9d04a40f43c2e0f002000305004a028800c5c080070b0f18a14010008480c02001c14040803580510001d40450040006443c0740c05910890801c10051580040c045500444030703074021078404115440319078030040e2080084d2209440c01c02995042406542041c52881800410400b45100180402201906640140340034010602c905611880a00303407018060188a0000780e402c80041c1c00c0c3d00300018410700030b82e000340034100c401c0d02c00d0803000c2e01002c41c054100d05202c010016000b8800f0110001c40c4100305848049849081005c8190300341182d000b0380c403072154400d200020895a074001003103220001110000da109030300301800c0d20040b0380030030f01030741c4452500c014000044213504541c5a1241e584000c1001c0c54080349845444000040d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 757800062 1250 757798812 757798829
    0x20c1008070905121f150801050f060409080c0d0c1e031418031c080c0304050d0f03110c0c010f1809180524010909030f030506060912031210 62
    0x81d020000c905203050400e0f240892001645c1c1084000030b40600101c00200e50349130384664662041008044607801e190250580c00000d00c001d051458000c8070888000d040180b14039500c0315840200821401101c0c4d8813a01c4509071744180c0705440010b03045a41c0d444081e6604d0000541e102e1402c0c1d04544010803055064071881c154a8035800780c040b0030341001d03000c40515882c00703c210030296010440d003030441e143e10341103154500554200802c4c0ca040581455030503101803051200045d000b04404034000b4085c508405084500d6400310090020b07840126180038000032000200da40208480c954807400781c0f500000b4401042080f184a1100428516806c840c050b013801072002d40e40115618032071041c0d05407c801c0940d2502d0f03090500322804000070781078030a510340403042c13000b461500500d101c4204000006041c1c9020700300c50800018082096a82c400044080da156070588100300300240070700e034400d420308180965a920201c0304514109901001503450040550450190340f200d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 757801312 1250 757800062 757800077
    0x311090c0a0503041502090301060906031202030412080a02190510050f06060702090a06170a0b1506040915080d110708010606140307030608060f0a0b12060112140d020c100807 77
    0x1600d800500c030340e290f984025465002c200547c031594007400b40001070000c40350005601840c510f41144980c40b6119118199041880100320315545101d0055040d070300540c40135079a142c0403504038200455a071765000031034606559036052203000503d82181d0420000308101c180c50b804048081528201c4215078005030411100700141440d01180307401049419000c00c01d00d403202c403111f1032012003228007602c0382d1003051242d003484000b07441640c21040c10400609860380c820007040d894811405140380c49900c070560002c0f94203089a000c00100364120a9800030740c80d1690003049175904024004d03070f42c0b0404401107204031041c40703840b0844860b6242c04907034104200b1002c4207904000d0152050586c0c8280024402c1e80038091a40b2170390240c4490105494080701c1d0404039202100c1603802040c81e8400310380100d4001800a054403a02c000ba50490105850800b00c8116000101000c5010310003140c41c000340c000408000494080303960310190480d203002110040c40407901d80340040c0c1740 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 757802562 1250 757801312 757801321
    0xf090d0e092703190f0e0f0409080910050406020f060105061b0f0f010507030c0c0c170c030a0c0509010b1323090709030309080d0e280311090c0a0503 66
    0x1d40b50350784001401103080c00000b05041100904540058184403041070b201c2580041c1543e110091a103172400c2410040700d03680c403802c0441d03104240d4107440d60180360713100000c105015216040c1c2d03003c804001c0824040e410a4030008000e50414410308000d8856540d8500b030002002c1522416208042c02da6400c3c183c880e002089c0170400320700040c03424050b6000b100034182d8140b002c0700c5010f100b0b000101e15030811810050446074910244410000818042070000c0e181c1410001120081911544042600845175007040402000168184500c2150b43c0070416948800412100e049411400d181c0c0d8400c2d200400d80f107070600003480054001d0060020151240e020004010140d4109580c0381c0b20300c001c00c10090087da000c001003906035008008041c2d016000101510b8554007505a03042c007200c003d090030350b01c80305541c850907180081d1902e6141000c449120030302e008100c030800a0352428400022107141c54034034007421402c2d00103210072007940704484154480365503892440e40e6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 757803812 1250 757802562 757802581
    0x206030601110a0b09070b040b12060a1701051506160f080f0d0f11090616060207060203130302120702090c07170f040501030608010603031b0804030b0f090d0e09 71
    0x2000301a20306110150302d140c2803076403003080200c80c40d034490722103200141030040007945005200c0d0702c0200e07415801c01c0f007403100b840420113946040e070071032a40b41925107403c00000c80701900c0340c210480017114902d541083c0c484c150441c5004c0c7e0a40e48500c0c0000049006000451041c41001d04154000010700f00025030790328541c0c408203016540302030601ca2220034036820340c0c0c464103007a42038586540c58190f414040b840744840c1c00c10211441c518107003030354010a0030360080072400040c407000401d1080c24001690116481c1540c445002c641d0782c6086c010300181e01d09488000d90062050802094060318001c044840c0c2a8008108410a5640e00c50004a0703901c5040c003102c038480803000b400126219040a420303440004800c4907112401d0500040031030303030f86030b200d103400c2ea0401d001000400d80040f100c00c3d04402e0003403814100009420008154422039000500c69001d0008100403400e021101e81c2c00780c1403003004eaa0009110320421a42010510301c02d44c1d002c0074682c0800d44144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 757805062 1250 757803812 757803817
    0x7090509070507060c0c05010e06160f0e030a1202212a0a0606140a0e0a091703040303060509160207140a090905240f13080c011d10180206 61
    0x85182c80c00b6450704143c1c0e66070600b9103c03059100ba000c1140180090100070081c041c00415189010003440c1c186411500744804100440c1800240844020186269841441e0604803410b01804548203504a4a042402ca00d90f6805c1e00c001802030602401c5444660101c0c003c00d01c0c404441c51781401482119882c4c2c0312030b440c40c04107102412080e5a034044009000b502000c50041a00240c90351520010260302000010041c0c4500703c04d110038403120b5202011241c10036a418800101000b6074600100f8142da442d5092020040c041304010805505401c024291401554151607a4945040d512614400040d411b00560024103060100c68145807810030032001c003e18022196a031941c41100303c0715032100603a00c0d0782202151281190340c420800c00002640002460365160141c001440b005000d40b00b81f8088040f08200c00900800c3c009603501c80f40313104000c00481030040503841060003500d214041790301444822500350a400d1042d41640e40401c0400c500401c02c540c20842c2c2903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 757806312 1250 757805062 757805071
    0xa090611031806072f01020c01080f0601052803230a0f0219050903011104050d08090a030804180605030c01021504020411030c0310050306011a0307091701140f07090509 74
    0x80c000d0201250111406410498400d0020303081002c0305c0c001d01e25912600c004c00c90540d4008402e0030031990340040d600b80d00108000c1814000d45484004031114031030040405050920f186003118480d0b4035459114010006e0384042085004485400d28007070441491040503c2c0b40000080f40000c05400107480e103041c2c40c40042c502506c504400701d119240400210024401103810340c1d0b2030409101c3c28030303680300b11383c03015007442d1404001400c95060140c0042544e00085038001c0b082d1500c950500103960b10002558946444410302c2690070049011f030101d280c01e0900c0040c413414041200410404182d0203000c817103503e03600c405060440035000700e810681c0e420300300502182001c040c60240c600c03003007800e03a24240303441d1040d50456a40c02403842500300d24010072030200d00000051407141242d00b00c1da100e03034885505981c4684198803c800d10700ea440700600c5603e84c1984400b002c1c2c07003040d0030b010003920303020900d40780194200d81070004911080d00030f101500d0000c0500740e10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 757807562 1250 757806312 757806319
    0xe070212121005041a031506240c0a0b0f1602060718080616120b030c09190603050f0708010e06010603020f0403120804110301020712030e0f030c030a0906110318 71
    0x34a0f0340b80d021a04490301d41c00710b0700000c80e601c00c410f0b60f03c1c681480800b0a901e1030446c0c14a19042c0003000421070a4055481c10f10080702180d40000580b1680581c2d1003400d540090300c80841c0c05003006031558404903990718501003850b00060018420060001c110040b56001741110742e140d420503902640d80c1c100b1200700c4150660000b6030000b080207414444d54900c0414500c0c4600704201600ca43c046000c4103900c24100460b035403240d07d002070440700c1904111803800180c0c41d030469844c070083ea040c003050141400c0002c0402803190001d10121071400c2d0030f08903030317105513158420f07406c0341c4800c20101a29009000100800d501c680c01908060100712922480e05a5a03a00c48284448801104002c00c0101c4204018400e160382c5000b400d400580003545480700d10340e00c0c0954030130020103e900385950792400c0e00000fa401c005541401000204403587c030021454050b940b07402c204480c80014548030303000714415105001d007103032a0713981d80d006509007615503c00704051000c603002d0540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 757808812 1250 757807562 757807591
    0x1005040b0304060f0b0621040609051b12031e0328050702010c0309050a14030c07032001030b01230f18040e0c280801090b010e07021212 60
    0x11450340038002035000e01e22511000903d5800700c4072403001c5d250a500200d100d0350003130109030403502800c6084104501c140b02500002e81c1c8902d8070200520b604400a80103104e440f2105180d0356010042e28220392048410240d441c00c0503e104d0f5891041011400381d02541c5840c0625001556001d1500040e1f041c1d1002020800a0010364489070640d03034550060761200180000d154080c80f4003d826034540c9401c3c858120a42c48450743c074401030ba001000c500010014084065060040c1e51b0507408010603140b61659908010b880300160407403040201904452042c0b1641c040d1151404102d810384800601c1840000e188683e412042c0003940100f104100d0a0085034904000300380e070080d0070425500e5040e155040c0000c450007290b041a10b079000790022a955a642d40319030300c00c05542d20340d01c0040d140440030f980f240c50107980a42c40560a0445070020003500014180c160340d0948418040d50351364400c100e03502c090301143c07410140c0d810801a10f40070740900c41243c1c404c0b0400821038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 757810062 1250 757808812 757808819
    0xc210a080a0e0307050601031a0c030601260703060617040b0402010f0c1704030605071110020a09051509090912070b07030e0d1107080f03040501030213031b0311100905100504 77
    0x2c0c155403000c0c0080f85d064120b1401881003000b03030203003440e110b5007000100020340360a08408400d0f100c0034020506000d0b03001ca00c0c1e07640ca0030300d8214952820a110364003896040c903000c0540031705124002c80005c140e400c00720250f28202540120300c00c41e003100c941022500c69400541e00c1c2182c2c940c0800400040b180013401241080d40c8802c460319030745020569403071035170402004951000d08101e0410800b00600c040c00a800690404131040d0072200581d600d858180940d40044564000c1d42c00c03820303100140140c00c00788409001076240903136844a6559401c0c204980301c00403150520201700050101c080400d5415900640c8800b1900380000e001440c141810303c2c090582080c003000079082a11a0011913040c000c090045c400d08000301045040c4540d465101d000d030b40101e0341010350101d40c0701203000781c0507034210045821400c0355080000b006411a0010a94041a110342d41d00c00d43c81002c2c2e040c109161002079001c1d0760389820300c904000c2082810554526401c0c1002070612010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 757811312 1250 757810062 757810091
    0x8090609061308070509090d080103030f05130906031a010617042f030d03060e0609101205010b040b010516020f010905121b030304060909020d200c210a080a 69
    0x20181090300010104c00c0d2030002000451000204113445a80107840c01c1802160002038403070559a05051200c0c3d1220843c0d811155402a10b600320095000914009500c6125a214005580c00b80f100a80410651250014010740a03c078800005110041d500c0c0c00c00d070203943c000e80091240c0e03005140c42503542c0d01d05e014418010112008900740d0045101c0310701c0c0400074481d040110782810704c407e80c41c00387d180d075042000a140c0740c01078415400043d038650056030440d02401000807500303030b12161403c019001f0a84041407a000303d00d4910300101070344c020750617255420b00c1100401c030003241a60078130840c0030220541e175061040d090070200310781c0d85040885061000000c002c2c0f43e1007491111102d00111003402c181d000303400401003440300e40d51007005003090703a01d0325001595504c0003220990081501d003103040d214015110001c00c0b025651001440070050440448980d694182c25031722140229892151000b5000c0041040d0f07203002d000c02646c01a403603100054074012200e03c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 757812562 1250 757811312 757811347
    0xf0d030e0a0c06052205030c1e030d08070f09181d0304120203010f0b090c0a020c190e06010801140d020303090a090212070c08070f1e060c1b0809060906 67
    0x4200850404a105c00f0240101551620901411032140310403900e000c2c0480d4035060590b081074002c1c404030010450300c180503040b040b409030340901181d42c400c07d01500117003800c2040c1c3d42c680000300142e00205486100740818000e403a196441c0c8440c40c07130007650220007001203a81102c0a40310300384401c128640c003440944018101c0800c004000441c0b441058211b5207020110100b0500d04803c000190b00c909290a0740100a0907074160b03126003a050682c540b0710140c0002c0c3e805682090710118100d07640303145c0801c40e00b40b80d031803005030345443c001901e02890900500e800000074002c01e06461030b00c451510640c50019080d0303440c0c80c2c0e5510108a400c1c8954010f4807480d600080c59000001201720303107551180c1545040c4213480c9490340ca1411034441c003000984214103d0f000403080c00b0403042003103040340c0200401400440701785401780c082d080181c482c0e80401d41680c1e41c909106c2c4034500030144268401202450b2203103200400c092500700f814056040740b01400b004602c2905c8040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 757813812 1250 757812562 757812569
    0xb1c031709160806010501030c02070e1314060c09090601080601081b040506030c0406020c01050a0e0f0103020c0307050a0605010b07080409021303020a08010614060405090403030b0102190f050f0f0d030e0a0c 91
    0x50804d40d8107200c0094150785481c0c861208643c07013050304004030b1100c41000d0790000103d00f0340940c80e070b040303080ca11501d400d0315140945a000e10720500480990b040e009000d20103090703d4144080e520b080041d581d48508450103404502060006085400d003904495088207006445a0520b0349400100b42c03150821901d102134010f00080034001540c0400c0000066803007440c03c649040c41014000b0300450b20107030840d0103403030f40c001c004000307a000e90166410007045030122901d903c032031b040a6680c1c081c3c408055420034074000000c15840c003124100c0300c3c01500b29820a2034545044070050080d03110b414000307410422000081f0041c1e8461000400a02180e000403980500304881819904400800c3c1c500c04c40781000100069201c54184a900c640c040c200010108a09030060313080c500713541001040c0345120361f010010040c4402ca5200c1c40c03401102280d00c40509031945560752405c00c0c44040c02c0ea8085d504550303400d03201703811100344140300c28151400c0a00300d42d41d010f0308803a281c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 757815062 1250 757813812 757813829
    0x81908010302090a2a02030d050a050610020c010e0f120a0312050f1005060c0c0406260318121002070305090306091b1509030708010b1c03170916 64
    0x41003585000542c2e070750095258a02001700e40d4525100007810a400c100340710815a134000700c00341c5240288207075951a200303540e0600c11450420009401010100e030000c0c0f044100c80081841c940c0700044480440e03806071100300c40c42d034010042000600c400c051007a41710f4403c000c4040440402c0c41900901c5100e80c58504240185640d1442039034402804403a100e02c00c2c500b00202001c0100c0042c048481c10340c3c1c003c0e561900ca1803441d06060003810000c2d0040d040c21400984004c0c401813544c203446001c1880c10b03401c0d5200364419124400c01c490058000ca4075200d0301d0b42031409980000b04043c03000e0403500b003a070b600c2c80100140c0e00a15002d03000302d00d0228100403541418020b10346c0c0f2001540260403403841010074007039548204503031980541c0441407856403201800003101d03000c00000b41151003e40c0c2c2e80240901a1150b1a80c15005054844002240c11100349202c541c85a254460108500f1a07001c0c00700d0b00305000349184403e20500c030031144520852400b100240c040c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 757816312 1250 757815062 757815077
    0x80a020f0622060518060c0901030e0102090a0312020304080d020607200a08220f03111c26180a1226040f0603200c10090819 55
    0x30310228100040203200c2c0c50200c29034a81590101d41e8072000d0180140e10042c001010784565090403008807103140107442502c5403605000c2e8501069000e01302030f40003680c0910180a201c2501401d0f4040c2110b081d800450210f400e10004e001e01c2d5820071058801d104881c1042d640b02c681c1c900e03002403101740340056044081840192584510080c0460401d0002202c0680c0505541951031100c00300c09882050041840405441c130040c0c01d03d5200c3c22607181c64103203612002c26040e01c00c0b0b603100442e40c034081d4442c2d04855050041e000b1803611414080c2c811400b14684411117035503494076280f02020f880d910307032051031003414001e003802c85445021908141ea600303042c08000501070f042240105040113000002480c84c42d40c48611009541807100007440c1c98590450600a85e0008400c914802d200400d055600d0b5005008030040143c28840c00c0c10b111403060403e00c03c126009400760000f403c0b003040745105030005840c45204240381460b02d44180e010825102040f01d603400000c205 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 757817562 1250 757816312 757816333
    0x28150e100b042d150f030506090706080c160606050405090109020906060f04291c050c1303061a030f070e10150c0602120c07064203080a02 61
    0x1621031250301c0024104009010003911034807800710744100180f1660740741c035801a4049071204080140c001c00c070003a990b600c581e4032850401e032202d10031901009244109440019854030400e281400307a51002050340c680300c0c600810301d00d280b111150a0f9a0360742c072000e0000f0a501c0300e101d0248600142e100005080180d441003004201c800345c045486040e0034400c2082d000da8900464049903c0d0718a03041e15014031a0084c900d42c20030060710300c4030040100d140740d21420302c4241c2c420300072201038003040581e8980e56446940d004080e01c0c1c00f9256000c00d401e000003a40c8d60f000c484981c207035545000024200100003898804030120313004031a00024010440b070750450200c650000f40f26040c40044a04103035200740718070200000e200800c1203942c50f020600c010b540c1150951a10307010408228680705a04001a911201c4101c510a10700400c20180c150112080f0000e900b415161003a00203152030140641920381d8003006040c16901800400500118002d266000307054001d491139250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 757818812 1250 757817562 757817569
    0x60a0b03061302131e050903030403020601060507150509030c07090c020c150909060d080301030f0218040b070e130e010c11031207050a0c050f0604020328150e100b 72
    0x1c001c0c0500c45054400146100180d540740301101c054050032900003030903010111a1603881862040305c55800703180409003c1e0303040d008001188154020740880b081641d84e04e038100e44034402c1c40e43c06405400d4010003c030721110349401264015420504a03410405154261800c0c4403441c0e00040006179a12401c003150b03a014888000180811100395400c05c1c0390a03148034091168008044c4504004400070b9015074034200103240d0311740c00500450326980c4901d03100d001c0008039407061380f0401d1030ba10410814201d020701980300700d621100703072040e0b910344110035912880e514001c1e5a114608080d160003108452054a42c2682c251002140f00d8885d540090070a0381c1220800c40c02e41c00400203019000180e5102039042402c5280480e0740c6c03030034074a04407172201844500402c0c40c000c49030100c0180300001007450185000714107031140001601e80b000c220b6034000b0800f41082c1c200c901000041410f9140d01a84a102080f01040001e8181445810004190b20b0610243d695625142c0c007401c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 757820062 1250 757818812 757818823
    0x6030519031806211104030b010602010501090b1e0f03010207061508210915030a0c021e1207080d05102306040902091906020d11150106180503060a0b03 67
    0x2001c040c0310881507814804002d0011401084250052410001850140700b01d40c0c41010304811285d0926121901c9207020042c07000c013846800e005600307040001c542d80c83e07248030b0071861207401010841002c114420204036400d10038402a4801c44010300c4621a0b2400e00092403141d00c034600c0000c421543d050141c150401d176410501c0305500500b0f080c80b030818452001240c0310f544012917a201c6445600145022501d51410005000040f00303000503040d0580204001000a40a4030150f01c20503002c0d0750043c0541e091032420390701402c100802a46004000c140c12070041c1c00280c130741240c03e4410401d40d00c054802901703198180c0c404100078845000c0111308480818a201114000a03002500c1030045004140056a000800107010b50311a015500840700507000b400c0c0b0150342d202c01a4a0f001000300003c04100301e040e03810005d80e23001c240c0319126a9282400040c03a400c06c80100d400d030303c084107a50a0b280800740c0c0071889903010081c480c82101600d202162403400c0006041c20318 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 757821312 1250 757820062 757820087
    0x108010f0602031c02040504060308040302040f0e0c151204140d02060106210e01140109150806180f0f1c031802040c02010603020d060b04050106080f16030603051903 73
    0x3444514800c0c00225400700884000101140d00329442d08250010764009104a82c030142c2e001707180510010400518002074411a4000c40d0100301c484e6100d9008800e480186503c4d010541219418004034034013502148603445255040c1410b01010b414208481c1c141610107491404400c2c2c0000302c0300204103c640307500310291010f0700280d40f4010f4090584155080c0080e9080001407004111904507404042c0b58440d610013403104180011014003000301c01e0107094483c40c00e15108041c1132203440340640031141c08000800031a41c03107004c141c100c00751414440e14540945810301d40b0b0120204541a40071600c0000b500344590280001d45407100044070301c000703250610303c90b0f01150300703038110b4000b84640580c0c010510040c005412401003045d80c02c025030100b00041210140b0204d98081c201c440015070b001c21550340c032103c064812031011108c1800c4030f120140000d401c114030f5514ac0300c00300c01b01d04010988940f242d88031800c0015084000c40c1d10f07400c481d0764030140340e40310045140c1d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 757822562 1250 757821312 757821329
    0x1018020714150103030e06120a140a0204030507050f1527010f3e07140d08043005060a1406030a0803090c04050c1306080c09100201110a030b010801 65
    0x141c6080040b80454041444042c1c1409158440012540c550100311020b0000c03c45548503985410300c4030400901c65204c00500c02640310000842414841c400c0303405403034018005000301403400d02000812034081849a411465182d5107001450801016110340c00080224105a9500d010254064140c0840c0103041000b08440c0b0348055804c18021100821701000444007508023414280443c00717072004035803003400d00408507082d00b140890007509403078201c0c8140085400c400100b15408464990103040040100420407041c0e81c3e21650328280c004041410302c4070901000103001d5208422000d5803141c01000030000c80c15514440d5040004c2898144030050504e00d0100f961490a06001040c100c0004041501e40c1c80400c20502250701c010824805850b0013402c2c10b0a03500440704100c1c5a240d01c06004c6074183c0903c03092440790f10380c2c4695a090401010801585141000c04c00c410342d581c6942075890035030b541005100d010703c0c0c2e46011030f82100d003100041010f98141d200421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 757823812 1250 757822562 757822573
    0x20304020906060705010b190303140a2c0d0303140a051005121005100501200a11060c10290d020904380a090201171018020714 56
    0x40e59040da000d03801c4502030f42c1c4207440d0318451528900505a4a4529503c0b4006444e0140b141c10803064401c02d172407095a841d9180d00c1c940c40c0840b09409080d540380d0106940c0c441c40031040130000c83e00c280c2c410400c603048206800c09404240005919903003500081c1e16040740d03c900c1079488000c03681100ca070341c0c400c11503071503c0000c0c0d142c010494041e203845161000300208409504000c03802002002941c2002641003e6039074600b110005d12455001c00d00b0030036a4800041400a0348405079070030301c080c149500c11a43c80c204100d03100040c2907403040041c4540a5044000c200e0b00c1d250814001700002c443c0001040e100709079484100e00b000f61000d94249000c02c3e101c07410f00e00c2c18154113581d051250344443c9442d48680c400c0c0a00c6074080100604000858941c1003020101200541e8045649807100fa842030107071005c081010340440d0041000080b00354114012652045c1414040a4515210820f980a0000040000002c0c940201e2000c05000c0c80c001c2100801d40d00750010103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 757825062 1250 757823812 757823821
    0x708300a06170a02030721060f0f0506030a0f02101115070315050a1205030c1207110109120f0c170a12081009021315080403080c03010605070605090c040903020609100203 75
    0xb81e031b5100900403125590b10000d00718184009420302c1207000c40d800801844101c1c4000241d40c0140544e2456440700c1d414080450580c0c200481c0d074034401ca4001400030109081a0203002039103d690001e0820407285502820704424140a048405011200166611704000c540141524100d0050160785001d1080c1044507a55078030700182200d523005001d00c0a100c1c20304110f4194020f41000324501d004d1069500c40108030f1100503c07480c0d200340403040000d01d44070011596080607000340082c1c02c403a51000f502180d0a0310260075440e2181100352415034580c0c0100c04610311401e2009015840b000d000d10030080085034082004403580f5041809180900002d007007142507104e032032041540000c03244640341c50350030441d0240401180b4a03c081c15550001000c02100321815800240c804000c15020600380007140d049917070700e548450400c01c0984070540200005003525101d48a406164000b40d01c650103042c031118069000382182e841c040031020b0904085580d1007102c14810001c20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 757826312 1250 757825062 757825069
    0x1060e131109040b060705030a0203070b09030a0905120a0c12030815031f0b150d0e0a170c0a1203020304030f02011e0e0309090903030a0f020708300a06170a02 70
    0x2100b50440899011500d04604004185980f0964201600c0c6003c00501b03428040d070000700a1540c10305c03a1f2840c103110398540040b1038403402898040030008102d081c0420862401c0a01d0003a131001c800241c1c0c0c01c048943d5a003100c0502554401c0e800d01036002c040b98249500314407081c1d440054111002192042800001d841d09040d60b22402600c3c0d00c01207110580e000f84e4414880c410300646044c216000c02c400c103454540090598118050070302d90841000540421100354aa51021020f01203240c03210b010844c503080400141c0300d07485040340080200340204045501c015954400580d241480e06008204071400070301d00040d681403411941e80d00000041089004983c01400903045211b2151642144650b0030040e50000148003807044810f0040021740c0100041c0c2010054004180400f006a004045000e0b040314414001400007906a4a01c1003c2c1e8055258802c420f41c06004106100c3c8001c1e2030030745501d541d4110601102d04001c21580c0d00058050080001c444550b002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 757827562 1250 757826312 757826317
    0x1030510030308331c02030703110f0604330c03082503060e070f140c01020c0a060204152f0115080c030d051c02030405100501060e1311 60
    0x24104001140080c000155044206000345001903100d8041302e03011340440c000c00002c400d0940304540307100004100d40204030342d0b180b0003a40030b805414030303901d16100c03100c1e0000180340040e0003681034000c09800790740350b5004001804000c0881d0910443d01c000c2044136100103d550151004640c04000032143c00c0b89032841010b03030524107551683c3e1805d05a2103022810b05030100441c042c40c031503182064058021300d0554102d540b03a030760141c2d1008422150010101841d03408a01e0441d801003a00003000c00034842207140b580050715103183c80501a20340000f0440907501698089000e0100250a6140010103095440c01c1c041c3d01d000748248100385e49000322165002d15400500008801081d04114101d050b40302a00c2e4115681c1e011142c3c4819024050318481d011b42c079244000140554182c0d80620a07030003007031005010f0310002c07400a610280080d1424402c04210819041c001d010b40d5020f0125a542c0c0441c08801e1402d100a0807000e000c4009024104070300b401c8800c00300d02c01d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 757828812 1250 757827562 757827569
    0x604030602030408070b0103081e0a1b06150314070b030f160915020732090406150312110f062e091d0f070b0f09090f070e01030510 58
    0x3006036661141d25054003079108007080108140040fa000200340950200900040300e5400015410f07074403032024081a0348101c40784080130499440039019060b105541000b8900d1084600117581214041d580e407489440e50710442c0d01e8403a07249812303034211051081000600300b48a001d0b0950400010b01503010380000d103602c41c1d081030800880b039440d1240781000000e0200b036204044100c2100c400130344840150040d41071800b000c1403400c03020404804909651410103a4240d2013400550402c11440d20240044c1d8860f41c66036400c2c42c40400551041008500c11904880c0082414401810783c2c0c11a0300f00c0d03403030340e040040c181203c4070012810941c41043c1d00c14080c107c002182c401240a40c0451241003500c6241c00041810741d0a6449411082c0c084000c11012490030a005d0b031b91007906101c042d440e50880042007182400e6603016021124040c00000d0074110444081a529842212158030300c88000c0c0c1070240d019085615003c00a00a1034203115520346a601414014850310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 757830062 1250 757828812 757828823
    0x30c020103110d0e010c180302060403121e120b03030711120f2a0d0302150a0f14010906050d200325030b160e04050601030f1401090b0609060403 64
    0x2002c07050044032204541c03042402e0001008001c0d10501e28900808600411201091000f56102d030f141071a2140201100da0040c80149010706595401301c103981c011840341b00340240c3c07495001c9880504280c0707264004255440c03006504600390003a080c1c82c6801344481c0241c00402c40d040c08210b00b0300c05128080320070b803100705400c8062410b0030301c1e01074103103085a482d01a050101201c022501d040d0040a000f225505003406883c000f04a00c0c98410b442c01005030b481052075200407018940c0741c03980034110000004103d000340c0312000503124101c00c842140c0e00114018442c4480a20602001e404196a00d843c22507256031001358020000007400038404c84043c91442543e401c012006031001185448184d1180754034228801058074041210000070300c800250100c05603990401d011411940c680a9052010703040c00f009010181520381011346034041600e1205403801481b40c25282102a82a1513251000305000c071b83c031a4100510030441000b201080e0b032348900540d41940d400c00d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 757831312 1250 757830062 757830071
    0x100605090f0a090c0302031914040312060509040b100b0405060a030509010902120f0d0f1b050a021018082b0c020d06050402090a0e070b09130f27030c020103 69
    0x41c000030100116548040700d00b0741440620490703030360300d80c0143d070181000700840c0403a42c0f007400e08407040e544200034180100c80740c1c10010b40820300c10000d03091810251440000c0250708d0350049403204000311401d6444070005800e0106031028966540003d00455040c0e40c280740c00e280c0020182d102e9080c4000400d0341351000302d00d040c00c1c207521401d842540248209610413035080d803142c4454030354080400c14050590466100c5014504060142c0d05942d41c00c029210050302408000703d4903d000c2e141480b0b0301043c031005131112180303d41c0c0e488a42c0c03a50003007246040e0562034060302d10707002110542c10040e0440158600c01e500400b80740007072401c10f00000f1400c1c808071144c0b415040040d41c001d05c034218070380500c201d580c48640a82c0c000d4a581c0a1a92a44403080c195000c0e2070702610168802d001c00c11a41040e00c0151000c60001082d886003425030741e5001064a1612110b01101343d0f40308404e000d403010b011001515070301e42c154000140310a5403005464200c47c400b000e81419240c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 757832562 1250 757831312 757831339
    0x30c021c05092803061506140304120c0210030b102c0d06062403020705060f060609030a0b06032b1808030315011103040e0411060c2410060509 63
    0x11080d01e107034624541200398010f20342d2030402c4400351403610b00000d00200c880c140031558910980381007203454a8141c040d440c6071100c0c2e94010007010710303000e82c80c10000b40b241010016507424864055017032170b03998007280140000c000c02c403414031841c0c60002880840c8400010300120f00103504d200d4075001a42c4622146000040742951200d000700400c410f1901d0740c08a80c1120040082d40c0407000d04040150304007078800305070101d1181d8040330f007144e801080014a030072880c0d0305165100c003002d0103a600b8007440101013440d0404a00048034052a180100030950030200324501010325030201030040b410341d00c40e000400d0041c0b01701240400813908035602c0901804240100140030308400c44c1d5407840c3c13940c4220501c6004608272400246c001580003c01d90000041c1d400b6103900d41800394440d01c9075034075402000c3d4940340b083d40140b41030002440040003403000c401a107211000d0b18100300540d140311841c0110007000850301a8452405220150f07219003506d050010540c0d190007180407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 757833812 1250 757832562 757832599
    0x2090702210406031401081005070e04020d0203090f0a030c1205160818010201020408070e100e07050304060f02041202060c010908040920090303030402090c0d020406030c021c0509 79
    0x315910340700640c2001518440c0000c00008008441c007aa40400114412644a0804000a1240d00d0307443c1d20501400403172809561010713070061000e040504510032800702040603078129102d400000c40d80802045440001071180c40d0424425101a00c4104c40300c0d6005400220380b2180940014848903000d002d95000d2002c03a0b0700c5019030322000030030300341601c1c0001441c2d0100c0d0034038401d0f803030780c03c00500307154014000e071030580b1004070140040d141000c03070700800100002c11469862691250000341d40c2e00c41703000b1714040c130f04a548241ea24940303030070028155a2034010301c0b841e29204210800120705500000406294100c9000782d45414020b0b0b228003403c851007018100c40700000340015803c405502c4145940b2006001d9142403890b030811512034080c10320032603050313002000060018a40384084c194007250303524015080c400420340e82c008a0304550082c1002c640c0e2000300c0c10b803403030301009488110100c3c030101d0028403081d1040184540a1100c400e4000c00401402c07042010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 757835062 1250 757833812 757833823
    0x607120509093402031c0603060e030a080c040513110c060f090c041505010806011b03020d090b13140f030f070510110705130f0203040b0406050601020a050a02090702 73
    0x1100144030035601d0908200e0881e5100ca024040d44046002c420310f100c0c01c040101d03d11041500c02d401031800c202e003554a058580c1355071494a00d00b01d90700c00e00840003c0440c070491104211400c000c644902c0c0c43e10014100c114042c3c91090340c15400d0104010540c0c8510741420844000040030641c0c1400f4040800c4a00441298032003900a003070030082084003524034207100d21203e40840781922162410f2108443c00e031182d242c5070301e0041d80240002d5000e5410341d90001c034107240605602070281c40d15029403030300c1641100140c0040003c01a035617800a080c80c003070001c40410074030b0304203003000c0d10790301c0c0c8094420398414040303100c1c40c9021784d5201c040400c070307004c4050103948940c40070750500c5407543c83e1400b5003807003000410203139240140b082d4104001d0400300c070024013405083c00d0800c86411480403400c2683d0340c0301c20404804004600155014500c94041b0115505241c03031724034103076080140300078115809003015801203400020340c0102c06805564103031b41ea441e40a03080f070501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 757836312 1250 757835062 757835077
    0x3090f3602030414100c080f0402060f0a05090301050c0a0206040b071b0308090d090303081f03240b22110f0328050601080a020a18080c03070503030906071205 70
    0x300c1c40803007000180448140810b003036100a03426101401a40c983c0340c42140c0d00100300e10005030400f400110f2400715441c4035034115000504a50500c41d4502d40c0c2c1025500061180c0c0c0094004980d00c2202e050900481d50400104d88100d0304001c00030303500a549000040014150540050200b4299400748241015840300328141e4141c102c4c4604001d4102070040c0c07059941d62003800c181000061003180c641040c2c0394143e03a041180d81314041d5144040ca0040d900403013101d24000004000380603030158240041e40c2d1043c032054080310540c03a0302203038000f00046004802d1502045024840c10000801d00e0300f10050001d03181130b140d400181c1c140154500a0302031803001050000e10700c2203c18040b202466030050500030418413041005461040e10594042901003000c10780341001c03a00075003242061032503c1a002403101051101c0d01106034049a415002030903001481d082c20700411015000c241d00035460500c0500101e0854480e501010b00310084404040907407d204000302d5102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 757837562 1250 757836312 757836419
    0x2090d0203030f130e041a070e0405070306080c010816050c01020d0203071808030702061c0906151d090616020709060308041d06010c15140a0903090f 66
    0x242c00c00c02820f110035038403c04810300780d5015503500152800c401c10149101305d52008850040c86c15943e480c1d96800c1001d4007080600c440980000c0440e1103a201c0c2c1f0703100b44881d40e800300ba041d01c0c0c0401d0300d082c0401000041d0420042001700264400c1106c144401040789203003082e50b5511940084e402401401c56149146000209003c400c66000500e00122030390799600e000000d03a26580b01d80d4a1107030324002504041c091029000810005645148a503465280401c8025103561500700b01d0b02098565160241d00c01b4062101e240311040c0500079001c540341342d03025820702d5800380742d850300001c1025520004020140c0c580380c1c400d124070402000314013400e01c812600c07868080d0207074005000318042002d845860205035825113040c07e0084106071a0549202403a480e125860100001a0610079494006110b002c0b580ca50020b48911903040d030001d0b44801c90320b402800b80229500500c0500c6448005128100c00d0328017188141c8005076140b4030940c10584001d07059225020180d0a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 757838812 1250 757837562 757837567
    0x6081009150501080606041406090406030b040b220209010510020708060c030412260405030c100e01060501020105060604090e010f0501090207060b01050a050d020f040806090a0506060904120302090d020303 90
    0x1002003070341440106075075090300c52041c683c0d101404d120581c0250722900c95220780080d001f59550030101e00804080d00301902c0410700c5500c949a00402041c16502200c44075403c9007002250212411048920402150071001e6a110b50f000103041010600410740704155062040e0dc5550080152400500240040ea040c6203048415a1081d401c1110166100c41031030366070503409885160000d0000042420005414580303403115289000300402c00c80c1c0d6031004200050f4894820080d5020b49aa80700002c62000f441d50482c03425078840d41d00c0070781968148014005669a0342094600380e803070340d107000100c0d035074110819805804091043c110451500d00045100d410a0b00104110b45c02544180820036440004580340c0c4602503030304000a00500c144074556980350010252400544036440c2010b40303c100103824120150b420ba149540094801e500301710060010039845142128006460b02c2d05849081803031050071000000c1607400160b80c000d9130707507000a454080b900070b001c6a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 757840062 1250 757838812 757838831
    0x9030a06140f060102070308120901060b18120703030804030810050a060c02190503060a18050607200c0108131a0106031a150f09061209161d0106081009 67
    0x8104a05407482a406060b10001030b030654000242d00044030f41c005407903440c101c252041300404200c041c05465280d5200c1000103000314101d406000074070070703110b0001180c00c100f4081000c1755050008201c8036411112040001c01c0e002044207034080e07014185844c041d942c800c42c040d19040c07243c10040c2e010034440d60200c0c150390700240b0705540710b2082d540c041c500d540002007207801006030300c503840d0f05a205000007170840c01503400204e0b5030520010207075030424455461905080b400ca880c6400904480033112507225000303503041d0241c25606c00390a030440107200003842e80500800b07501c000340b081c464000c10000041600c07181d90307029030320820544d615243c00801512104840c05011444000c002c040c0d85400b994240001011803141440c0c03020241e545807036a000042603541c010014803588081c1e41400d850b03d4071910014025158041100901c0c1800c00d030507820010303c10500580c031103d0200c1e03403180b90f41940d040341480311141d81c590981c0c00e040c01540d0007040b000c2d424540c020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 757841312 1250 757840062 757840091
    0xc11060a2304050c011202272202030405071e060810050d0b092814011103011d220b040c0b0c0708011b0f2d080601030f0203010b0a0509030a06 63
    0x40c001350240d039080b6000e050080c68030f00ba8065840010098200f03000990f103910a81000031248100142002c0d10f08402c00d441c1c5400c400803504050f001540000c00c102c1086818054540600f0340d0ba0310b50b1505440b9a6076000907000c2e1070080c00103004109010034076164449200000820005044501c00c4c4020700d0302a01a1005580000c102d00ca0b4681c2c400c00340d10682c3c4480c5400081c1216502e0b001401d41b2903c001174080341301154155661310704010900ba00c400254060060040d0f1000c140e01e0024113490700010042c50000b00c1d035802c4502170414081c0549641c6880d802c030505100d191541d007400048002e15921009143c0c00005242042d500701150f003c0c111200c000003040341000d0350800005c2c0f119080003080010705082c0044544074002c5501c9850b4842c246a640c150030b02030811100d0303841c00b1566401c0407614074000c100e03142d80e160146003507880704a0825829540341c298448446d002e00c402000c14090046054030440d1404c020114115400610910568070b490314030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 757842562 1250 757841312 757841323
    0x2130b09190b092106040c0806090304060c020d390b03040803180c1504090b1905040905120d0b0a0e150f0d021002100c11060a230405 59
    0x51901803001084100c490003440d41450040b200046042441c01404008118203010285044e03100e60f503038904042e10101c0101310892050f8480e04007500514106800145809402031030560550b01c1044140a4594050800c240e0f160341030300d5011068105140100e15003562224070b210005180a00300440f41581000680c2d914030b02c080d03070070031a4550400159034401110090040001040881d0310084014458213503103000b001512210354910000880b920001034496003404004101400701068a12400070404000c892403030011800800c00f0f02c01111521501d403007141c1d00e43c21002031107004d01000403881001102d242c0c1d90602006441300030300d0141515030040501c0e400c0400c1480340944868080d60b241e206064003416070404001040e042000d040d5005a2084004401170712141c0c5440c0300380c940343d006003401c0a440d08481c4121a42d0130700890070024000c0a02c010800003049607500804028804262002c50134001c0101d1002450740c000700207031130420801808000b241 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 757843812 1250 757842562 757842577
    0x62f031b09010c150b1306080c010e1914040b1807030c18031a0f0106140d0e0d0c02030c01050708071101090503030703030b03070e040b190e07032001030204030c0e0a02130b 76
    0xf000070071001540441b100301c0d142030003903400d02d611025810400c0c1d130003180c507800d100380002c05c2c3c14051160303240d010004101c0c0e075016854100705c801c1c4108451826006100401d40192010300c00d6040c2046401030213940540740d0001d055a030542c0e100c1c801d00c1804110641001421025600e554070304e00101141d10101111b000c1e01e100390301140c4510f100ca48030038125845981c41b04001611014504001d510a0341103d02c0c00f562983c1041140006001411443c843c81e1510942252240145814810100000b81c100407041000c0380c00103e90303006885140350070122284104285000588004c2c1c80ca03045113071f240c0f00201d100020503030f05400c2584207800c00e9043d902c0c1180d4400e041c142450041ea402000b8019500000d1504020a809005113000e00e500220700c1c2281102d01601305106900244c40840008002606c101c0409044403001c4c0d1003885c0031841c151450b240c00c103450a0500420072000c903e44046440b0200580589600c2801036440c1408242e4802da860a580d00151 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 757845062 1250 757843812 757843819
    0xf080a0507090507050f09010302090d030323090d0c06090206190905100504030303150e0903041d130222050c0a0810060f0e0a03062f031b09010c150b 66
    0x4030110742e0304082d00600d8043d9003551181c40c00c041c03005d10780350b405401100303200d810180d0900c02890b043d500c551100301d47d603020351000502c07002034059600361488040a0803800b82c00c110140004c2c090001510241180c503450031154006051416030080c08040b00003079400400850a5107c0b80100d544c6203860301544c0e16a803120342e80d207005000d5090030721055207020036814041000031074080d410421140d054050b01d004925250b08507114034201c10b030381000140d0b001003414014000210391304d81c0200050f808502d210f180058401484428405009000708940b40d03024565404603030101c480c8080508052029140517414414542c200c00f92080014501e0004221103941d5060702c0015907000e030f650242038541f101d40036100041c40c408502d0300510902c00000100f059481010041c0c3c1700109624407104500b0030f69026200d81d803c600c0700e1030400304180328981600c80d401c01c42c895418591542c1701c5095600698013240b00b001c01078080b110041204407210900d07486110000c0d002c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 757846312 1250 757845062 757845073
    0x607240e0304030b040816060b1008190903120e0d0813050d11070308040306020306010305010506190c020d14060702061308032a070308010f120503070b040302070f080a05 75
    0x8040140564500c955a810240c100304418408140400c8000e984603024210203840c0c0131000060746a010554002540c1690340e40741c0b071540501e0540491594011146480304940c11f16410907400440c07110304120141d80e071401c1040070107005585280c55424815002c0007240f001c600f46d01c1d110307040002c0010004061a0001c1c243c0e840269541e030000760864004e0041d0407182d03205481180c030b00c40c031684451144400000000301c5c848018000303035104290141c0c480c2001000981a9036047e000305201d442e0074016044420710038220900d044481d850f214942c00030134001b09034020014000545581d0340718000d40e08070000002c505009090790f07401c0b18a9987c036500703e100140b0346071100a04501c4104040740c58481d943d00010481364000c0c0d00750b03040080c1c0c40c4900301c041d8000030040b0080340d82c49004001403c005950f140007007142c44440088585140e917040c0c0c99100d455001044480100e0200703040c03610030098a030140c411100364110380c0380c58602c404d50b1545140021039091054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 757847562 1250 757846312 757846373
    0x50c090702030d05060f030d022406010c06090602120f0f0a1a2106010f0612060605030703181502090f040b150a02030d11030a0c0e06160507050607 65
    0x1101500d1086903558003560a22094490701400390070041c00c1c09901c42041e4510050320b40c1c042c458a10b110300030390010001200341418010071203021108019480c031061081001507600400d03c42030b4540d01c441d00203601252071420b00000d0003001241000c1d4004c0d1810443d5041d51000070304c0c0074260306d1104007a16959401c0c0315096900c00810004408a0a410f810345400c100111384042004140c00040081003980c0d41450224243d00031101200b40c10700c200800d13502300044408400c2c1a01041c04201e0503d100503041d8480600104201a601c28218a290b000c80c041181e5860780504013502915801c41c406000e50464510304d84201a91181000030f0314162003400f08540e80600305c206000500e480c25542c94020840803001d40c0010000244e447d02c0d40d00c100001004c1c880d06082c0c036410098401003c0b24043c034140c400f44809580c4148082e038a400c02e9500d10b201d50003c1824400351842d215040018aa222682188000c140c2104000c0401002802c0c4281280d080f44486030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 757848812 1250 757847562 757847569
    0x90303020f0a0816020a030609050102070b0f07020a030f02011e1a0103023a14010f050103021c0b0a12050705120a0c260a11120d0e10020c060f0304050c 67
    0x10b4400005204200412844100b064203100d81c030701c140d00017000307041d4031742c2d83e515800c0c203540d802d0b031084070180d5001805e90308018010b0070303441d04144d00c1c1070012040d01c0c0c0f2020180d694840c0a1010741441440c0c241030101c0e51007504440508203405194080360030014080d94040c00440030021a0301e1849108040a54803a200b51800018091030078021038008031050809181034911007c3c0d016081b5000480700190781c021840d0707500d0090540c1465616000e00c9112002d010740110f41014010408003130324104001d100412803644400004404e580c2000060a11801e031f4084541482d020084e4001c0c480040b4170035084650550720141a00302c08003c142d169142500d00400d403481010342441040300800c01d8a481c000c1c2e5403115030004150341c030000d240c54481070041340c00842e1480d60580c9404c11840c500340100c2104000c2044900c83d01001e4401102034400c140100301c1c440401c85400d08c20070182070010740140c0165610480e05400311401d901c2164140c82902c6442c09121140c00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 757850062 1250 757848812 757848823
    0x1a070f1b170a050a02100212120f0105010807083d0801060b070203030301120f0209280615080a060e0c07060b01050301030308061e040203010815060406080a140106080a03090303020f 80
    0x16442005025510115406c1160300240f580d0504e04512450200851543c0a44014644203482c0d9003580c94902e0000c10003069003005030459410002d140050001070703600311001c00d80210303c00f001c69013038140d41d0130030860702102c66618085032a101c4805940034070754143c103101a220703454024400e039a01d41c2e40e01400d621881c0350094050f03000700010420100010003103410144102070b4680309500c01e80025142da0416645901040d42d11034000403c0e0f0a032151400aa601240050102519101d2a0113a00038104040801d019202d000507030421019808100038200283c102086810415101c0c0f0140d0080c600448402d403400c45240520360080c0c1c00c2d6412290305907140417266881c04c2c00d1103017400c003144108041e4200c0981c1200741d40c1e0307a800a94042c114000c0180244194281d803425a08009440350340103a250a00c20700c01080c000c01c42402c82da03000a203800741c3c060005c2d1054018210b5070b1040000740101c0c4099810194010105001ca0b402035085079480c83c081d0000c552200c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 757851312 1250 757850062 757850083
    0x30b030a170f0c0d03050a0b15030c1602030601030308010501021002030415020f1c02091306051e011b03051c0b0d1509080d0e070608011a070f1b17 65
    0x200e4504030079880600003078000c140341c80300b6080441c00c1101d008002890324448042d4800420344a00801c5101c0406c0d10030342c0c2c610324049403030f030140c244407000e80e406620015004001c12000000d0182d0388910494525001542c00b804868640d07a603400c0060490100380207a50042c012604510000025402070b60b005642002e1032545043d1160540e00c000c2d400400c03010310070b0328140000500c3d4503214480490b00d420700d06025a0b41c80341d03541001024803a0154104c1030503e4550140441c0d10f900354090f105400c0041c00341c0c5c2600c0d40c200183c1c0c2d50044402e41c81c1140c0a14003c001c03c250744a8060034090301d0700421030b0000c1450300604015208031021007500b14082e481c408000c00d000e9100080c070010310400010f10391b98180c0700c0d41c0c03180d4050401c0c0b401454486031000100c2000708803c4008009500e8054007650508804030031021000310fa404650300040f40d00d00034004e10300d0449071300300e074086a0000c070504490b200a031000418810707110b1850b401e810802d070031407000c1a407000c10b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 757852562 1250 757851312 757851323
    0x60606260711010c0e01090501141215090c0d2a141b160b03091e0705040207140105071e0804062012150a0e040203101b030b030a 57
    0x409103188034840d0850001032150040018000580801841c00e1080490b900b4140d615813075039a000e0300015004442c0c551056041005c21020030010040207010b441d2941110040725015403510310302840001c1c000035141d40d01c035182c4418428241c0c0c2540c002d003039501e1107140c10322640e543c41c81090310160b5190380c4454403615000c100c0481601c0307032a942001400250f40c1d50300b0700780d2607061300c0e01e40c0280015404166000501041520407060b0b04a0001d0195400c03041c0380d450004101d40e241c0d260040d00e030040031480210100070311406e002c060040c0002034011500c0303a402c0d00b001c0c0e400c68081401d0003110b52038403001c201c420f881802a550b10b114610001d01200035400000c44107080010410343c0d0b02580c481d03030302c02d00703004000e02c07079035188407002d00c0c40c0d00c90603040c070b80000c42e80700505030340c045c3e22800c01d019840d038964904140c22103410ba004890070341e4803400400e007485603c48030300090170326141c0142c1c201c5040d06190184220542da0400089104030141662192484005080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 757853812 1250 757852562 757852607
    0x281502030411060d3c050103081b0c1f1d0913020a0915030201020f060f010b0f09040507180902030108100e0a050609010f0b09070c120201020708030a0207060606 71
    0x140d810080c00900050301500000901091507440051189081c0d54030344d0329840031700341c14400344406140a610345198126082045514558410703500788200020503008502c2c020164641c50740c01c0c440c000b040600900980c040c43c000040c800c110680c4000d071743e4041841641c203003010350511008800000c0015100e50307141d4407050783c1d00d410b0f00441d500c1244d000075040b20204d0300040600440100c0098200c0385c03000ca0f42144000384c00c000700c40b0148d0b446580400c041080c4510701070078840c1180c80720007220759103120717030036590324184581c102240e0820709040034031030801d0707101c0c088084104860002c2014070752607a090700c0c04ea21007885008410360060014952482031503001c0c010603001582150b10fa064283d8425050001c2116100380d280d55540844103412420300030042c141208132401c0c0a00d24080300043c00c6202400400781c44a9500205001c03054001d60407545041e81080025031a131920821f00c0340a0350020070704039411420400001082c0f800741c0520400d143c400c51003007a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 757855062 1250 757853812 757853843
    0x30201030f090204090b2509051507050f0708010e03041a031008070e0f060a0b1c0f0e0304030c08010b1e0d0b090f0f0f030711032815020304 62
    0x4000c0c10a415980400e42d990703800030001655940318100c05540300311800e111602c0c01203108103010381c410310712070307140c40b003850342503040c1a408420b8106886085600100e40c25682118000c42d02402a0003007030f07845000800c140c00c10002030440c0c116041c2030001c2c1b1407140d000d00d040340c0780d01603445242e40c0b541c0301840354407552214001841d40402919114130400c2e0752644101d14003140b645c040350a8403458024454007000e06900564880000c0e40d400c945940317030045000581c410000c6d600c095000d01044552840c00310341040403100c0605100344044268002e210362681d000c0d100c00c45601c09041000607200d101070242d1000504028400310f0b04a005040c06220601c035855065440401520840006412003150070301a491040c0107185a440f20328106242c204580c100c0c903040c1d400741018080c49800042107889050340900462030301c07524030700401d141030180304120343e1b004000407246411501100d41030781803601500400c180b489104507a003080344010346015101085020b00300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 757856312 1250 757855062 757855067
    0xb0a0c0203010b0303191706010905130f05070e040617120a020f011a030607080f0a02071704032607171602040603150f27020105040906080705090c0a09030201 70
    0x200014005400820100c40c003030700083c15540803444d0842d0580c401c200c00e0610940c4030860f0500c850400700c0300c1c0c9150400c030001a210070001e00c82c01d8030851280d9184240e000407500640c1010014550500c004d0500303d002502e9a003079024024000d901e000070004241c1248019001001c448c1b0b0060104000000c4e40000c10b80d00a000786800d40c0714031032040702016004d00c610b1820020745007580c4a00701c40d4130205420140094401c40402c00380c1b100740450030994000f0181c001d49400030040e555001440e011a00211240910034078080200d0000140b0818914680200c0c2642d61010364005031045c6000c018000d000c03018103610700c0b8030182181d030344c0d40b58000d000c8411611000c1a208241390b000030f05071061a001140c0070407850780344042015050085500c401c0c0f0402080c44555080d03041020700003c4c0016000c4030607081d440050175a40160110b601070918200103006190300e0301d000ea0b64402071442014054240302e000100c4a042410991b02e199009a40c0c2d68050362554004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 757857562 1250 757856312 757856327
    0x114010e0a06050a0c0b0106080a061d0606031b0403050c0a08070f030206030406110a110118020d0b0a11030a06050f1f080c0c0307030c0c0f0302030a03031a04050405060615040b0a 79
    0x201c00174041d0340c1c0c42c1e620200c2c2a5500302402400d895803182c403140303081c12041040c0c50295004980c0c280c1c401c3c0d1905440341111003515403202c4241d0356145ca0340c4d0350070451030440701c0c0b07610107411042000ae000b00610101140380c2c2d400070020381d2960311a5542c0c0015a42e00c0d0514410a14080380d10305082c401403900000854009000d00d402050550049400d60002d90003c00400c0c0810f29000d0311500d0091700307000e880b00030104824030303101140aa4000c43e012202c20400105088445c2d00087ca6001099104600703030940c0c21100c03501c80c506144610000c010502031548900040003040341e0340c0c600301e074031004540400d02440c101440850f80907607940c4000b900320002000c3c10700412482ca030080010f07144207400b940e50290392102c0c03400c089468075820741249520001c011410310150310002000142d5a43c185000145084403440840184032840703c210740c013600701410320003840720010380302d030252000b107078402e10207482844c1c0080c1c3d40c1301da4410b184240b0310610000000b203004020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 757858812 1250 757857562 757857577
    0xb0a030203040c2d0b09010914120a030c06060b030105180601020c0619080f010b0702191e0801051e01120f06020a0201143714010902030114010e0a0605 67
    0xd0b40c40e6641c4640300307035012198075854564104208108158003e8400c0080401811801c0c1d64a246c10f451000007801805203000e941020220202c552030540c031800082142c0c04004810f135603441c0c00c14540144640b12100d01550140d08180c404140985408201c81c101c6800411030390f804000c2180c01c08100d01e004100c0350650142c801d91b00041c5d00e6410040408003810504001030414000000c0c01c07499010b8500601500c15100611600c0e1001c41159489601100c66840d0221420b4030710707401c040e0741d030004081001e210065985040c3d156110500b0f643c1c40d40001d01450f500c100301c02c1016032030b07400c1c025181105600100f040460101c2c6400c0054024500204260620f844045c103a0740301c0a04840143c0d5640c1c0712a441a0104071000c0c0c2228886130785030038401d401084511801e80264496203551161526001c40078120761000041103a882c4207104190303511256030b00203400901c01c21402d10f4a03070710003240940c802c0b28015103640b4020400c880d12414842c00b211150403440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 757860062 1250 757858812 757858823
    0xa060f0819090f0506160201050f1b041503021804020304030e040506010e03030f09090907123306030c14090411041e0e120316030b0105130b0d11040b0a03020304 71
    0x34030550108050700c00038000b80b4021070050080d130074540c524002440c481c11401c421a450708c0107100d6401181501d060b001603a4031092504504142544035151045038880748c3760200070449000c41c56003580142000304004400308148296075001e10069104c2143c0080000f103044090046503c3c0941c085601700c00c041c50190338450b440004a4030796804007811440044020078600306904c1c000740021f80c400700300b07805480e01c03901e4007241c88000101040010414110002d58584421040f1090b04410a030480414414042c00c0c002400400e5240810764007000201808a1003146261511101c00c001800709030030f0759195280c1d0b841034007525002aa10589402c141034404640040410341d807500210000307a4803954204503441c01c1600c078101d00481c041070041014100015403402c181e035065080205503815404012a881d00c2030003186c100c216421080030400b425040c0103800d0074104140200480114018054050302983c411840240010440c00d80d540d4800d4014641141c480c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 757861312 1250 757860062 757860071
    0xd092409090f061401020106080a030e010c021005120601030605060d050901110316030509060c0405012007090c09080705061909030503040909031e1b0309080312060a060f0819 77
    0x701c00300420354061420b0406829110701041c007200c115101d4000b01d00909000800c004c6240c561142c3c6c49041c17213440903051028041411a2990007007951035144c540c000c000014010102c0c5000c1c0c0150070241510000e6400c10000412550007486480103031170005042a0070302c5544440e100142400a0040c40155242c50154402c0d0028501a501412100000075400f01c0500002421030f1002400c0c11b0055004030140004008444111402e4500a107014001d165008100c1040820150700b0304280c0e114000000443c6902d0341d0040501c14020f07501d0344581c40e520a0020794600440c01510351060041002c512010070140703000540050314180703842c01c03560f25242c0a0450b00941d01454a01c1d85440f6078000301540401c4590403001400984081b0003120351005040100760300d090078003e4400120130042c1801143c80e10b00030610070080340d036030704000c1c4240c0c031100700c0580b4040d0040491800200e0828003801da020101d0301c060f968084160f8685034110426002914054071140d5607 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 757862562 1250 757861312 757861319
    0xe07050409060902120115050f010203091f0f0804050d0302090310020f04030312090f0323072d05060a050c121e15030a1424090d092409 60
    0x3640140012640100400180c41c0d010740140413418422007000b4401ea407400c00c180910034104a140380a4403400d0340c40400104514005078590700c00c0139240b980c841c090030424080d00360443c1d414042c2005503035600c3c14410300840b05903411a81540c000b881a002500203055161181c3d02074004d4101c01070480d0b0441700f111000c24100e9008003070041218000080900502d508901d41b5a01440b155000b013044031020303110134098070441070008041151403403082c10040305c154807054650345128411560b41b0554941350200b0b6103210140e9041d860501230310b8005426090009152903049806842c480c1e454517040c1000b020000c10100002c0000d00481078070071b8101e01250f1051000c8004202d20101c01000d00c65807100003001c180e0044001c6804009585012038070001ca0b43e0700045c07651105c00b080d080719007802c10b000d00003549150500d0800781c400f81c20b0045503009035800b44c20b4410498100300c0032900310307074940100d5107907400c03441010350b40840c2032088021040c120300d40b031f140681d00e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 757863812 1250 757862562 757862569
    0x100201060321020c0a060809010501050d02030d0305070210020d0f06081203041130120a020d030f02090616140c18060a03060204270b1c0615030b070e01020a050309040e0705 76
    0x100d507000b0200181f0580708001c2c105109214460141c2821100c92007600705a034000707980d6a52414060f020141c4880110b04418000c01490018a0400380c040d03413224000c04120000305110200301c1401420214001400d0300040b541580c800c0c202110149190b99585542d010340003070035459900f10601013902c4c1000031441c00a5010001c17640030003060341e40c801200c9440c050085601402c150030400200a9140d000105004410818100440c0035000301030b500c4000d000310b00c000394120700009540c044500d00841c4034800c1602c11482e03c4c041c040011402039503a154079a059800c1400202e0740805841c0c0340304080da00110080030030005a440e42c0d1840140c1e04154811122040c400e54102c00c140b240041140056030030900030021000480005400b079144c00e00c84101400101101000340860391300680600300402502c040e52540c0c924005900040c02c481c003400080d5641980c803c40d605c04911410780d5500103005600740102c5500700001081e4047c00600c00b882500d40015803502c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 757865062 1250 757863812 757863829
    0x30e0d0b3903091608100c1e0306081b0901060c060b0d29041208060303040b031501030e0102031e090106030209150406060503070504120311010515100201060321020c 73
    0x14041c002e4490418020f03041c034003081488101010700c2d410030180300000c000901030100d44900840030800483c20603040d130f1540001071003c614000c48c0c0d016007071702c40e4140d003181d0202d405200898000bc3d001035544000c0d000c2c01e00da0303103502180c010700400c8402d12034138548040a019010003c0c4440e10303240080c020015004003201c0800224206120a0095150b6001c521200c4000a15103203803690382d4100141010a82c002031001700c2000c1851a00d040041c0c03000f40c0034145685940342032040400c0700046255a0301c48c0002e0502004404c3d41d4418000d0728020140c015002c140a603412030301f10181c8400500101841d942e504001001d81c0d181d07507245005280300b41c1ca039000359031001c00f800141e40003074114a0038040e0810038000c80ba540709040f1801c03540400300050128602d0b1404440c120008851341001d582000d0903c1446096101b03030302e10320f220890300c0b401421011081a4280c6405120103415400380c038001a800f034201c014900401e014a1041d1040b8188010000c1e2111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 757866312 1250 757865062 757865161
    0x90911060c0109170c1009110a030606140a0b0904051b040b0d0507050901020d23030703020d06080c0f0603040f020a06180609030b06010507030905040e0a030e0d0b 72
    0x5030f450f80d0a0fa818065244c00c01040010b1a416051618024180442e9510010100c0c200c1d9555210b089405104054186010300980185482812a56410300c68081c2160f80144844031501302500000c3d40780c2414000f0031580c88400d0607040102c07100c00c100c020000140050b001800f1031100500380c000440c0208003074000e0802941d12440c2c6a6071a0084520080c940c0047c400200000b800581c2c00007045141112a460080003806810645c0030300d91410690b4003500040c0032003407000076501030300542011108510f081020700c0e607030a031241d41d4801c101d000070707000b0f89990a120800d00f800c1d4011503000c1e0040040c00c01599203503010521221560b800240001c41101c4410060314178048100000c10151600348441401c54031840c1100f1000782c004c0c0e060042c0080c03e03208050140306800c0003080020000c024140b49902031342d4580000080480005040790507070201071801d224540880d580010b081811542ca5400e200c500320141c0541000c0c0d1003950407035410542c920014000c88 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 757867562 1250 757866312 757866337
    0xc110d0c061d1507110102030403210603080d0b060f0c03040609120201080a0b013606080907090c020f010908070b01050f0f01051b0703201909091106 66
    0xc0404034203080049800d03410503040741000907000900e03990301c009065041680b101580140c640c4603007600b40e5170f84c2d0f0902c802e04115400801000203041d007080b501a0305210040d0302c150002200d21050044403071900005200340303070038041000d901c1c1c0e15900a81c0365600c0a00341a01d070403004010b413040e58101c0c1d5181480c81d40b000405003c500d80c446000001400c1c4054550055440b03075001030702292005201d4100c1c1c03603460303081e001141c0c03241850402928842d0074000441e080c0b442055030008013020004110b00303500d807001811600c1101018032808088015083d11030921140802807c0081003001c1180304280070504140d07000c0c07080001c90b52040007030a130b45480601d40910642c00590000b482210803030f0258049031140a01043c0e104805d20b8241d03581c00d0742c40c507640d0440c40b440455607081c1c8108180841003003104c0b400070b0350301c00c811a02d10070075030003140400003602d8181c03d4511258122034020016905103410542482c1e104001d0400e07a95014000304419802c81d4406002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 757868812 1250 757867562 757867577
    0xf0f010507030b1e040f1e05011410020c0f0a08030318070e0f040609051207030201151202030712080f0c0d120605011407021302360d060c110d 63
    0x804540602c101d40510009950043c180184d0090a4031405007410500b8025511024501501c40c20799120803460f07440d45080c003031441080b014010040c6000d008403026402c0c00078100d081494a8000d004d02d040309a401008034400c500c040c011940d0210100716000040164080b0b4059424000f46104111860301d801801e000001da481c40c0c81d00c141d01211000c0e45180034000c40740c000044d40365001e0b8001c2008a00c403070030f5203405171924469624042e8607280115070b0f0010036a064100c039070800e01c0860000310f0b16840f5a42800301c1c00d40280c0003503150740207000c100100404040840361550284600e00c3c1088100c504003606070303004803400c84640d00b0428010107091b4000721050380803480e1560420001d810400040c02e0341440440b038151294020508004541e0f03100d0f011480016061030645d01e07020300c41200a2043c008007a0030718130030802600d0030f07140225803410101d800001465007603228104d4540d48002d081c148a070004100350036540c45405a000c1242405c000040d558021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 757870062 1250 757868812 757868821
    0xd120e01051303180b19021203160e030316030c0807170306130509190501022a2a01080a0b090108030309010e06010308070215041e0504060e040c0608090f0f0105 71
    0x84c40c001c16030501101c0c00802d56018007107064010250780403044486074203d0720aa000c54142d240c02003a000700c00c488103001041280c100380c01082030112078455150600d040c00c4c28001c040e22400b0742d110360b0031a20350b03111402010a11807600020098020075810b0710b801c6030b648860602c02e01074a001c07030a0a00000030310a007410440981200b000207804108242e05101e6111501d030f0090f11500c05910040300702a4013441000c0d4111500d03018054600150110b040a0440c111060f0103c8402c403070003000a444520088490305407074036072030083d1405807100c0e40360040d16202c0001d041030300100d503a01302e0404961614941940a081b080c0c1c0210786a24204420b03a0a41d42c0100c0e84000e00e81200004000150307000301030343c2001e035045420301e81d01c52017030000e0011070042c1d5200d40c01c07421500d541100c0041034168030750241c4400703030340034050651101e44941c0c4125065070000c05210707140e03404020403449902180d030040841c00a40360f240140d65541d078a000410007030744d490741e550750080c031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 757871312 1250 757870062 757870067
    0x2710180315051e06011409042405010e03030708041a040b16060c0c05150912040f051c033e030d060f0e071409060c0105190506030d120e01051303 64
    0x9001c04401e0802680c00789000700008004d00321482c840d00c810200811201019035589c0c00a130701c280441c1415504030040f450600703104075030701e05c24140450f00c40304620805080100407140000d4008520501d000d00d00340e10940c03031412500c0446000081800b0104070b90009000030640211f542000c074885815074140a402c80d07240b03000781824440810741e400c001440c041209816460112814401342e40c54401c0c840c20a80041034108001400180128500b040010041d007520020340703102c55050041d00c1e004003491004500035000c2888c0e1800c01400d0362000800899611408440c0d014410420051061001c4402061070140d080403441c0c402a466504c41c81d4010f01c03030080341d154103074a0031041804041001d8030150810011920a10f03403414540200c031000170004e044a5541c420b01b014150003007400380c81c80082100340c01c201e440c2d0012036014160003064020090107015480410907141c00702c1e90201045541c0e20317000c2c0072031003c40c2842100c0c42945449034002c90400c5600c1c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 757872562 1250 757871312 757871341
    0x201021305100c0206031806250e010503060d06060302150c2b050a0c0503030f01150e0a18180c0e0c030717090c090a02271018031505 59
    0x1181c020041c008280c0b160319801038400c00700c82c0d01654100d40d00e4942041e452086524104003241ca44030b030307400748030b5030085072041940702c040c0807841c0c204040724592040f51155044051b003800a802400400e0341440d00c4421004460310402c0c0014425645e80d0204000300c08446610400e141c010410300540b980600c0505641c0c00340403500001401c00a24400c80d080c001e0f180d41d0b003004004207c812803d80600140301c0002d4100b0110381c1c4910b0414000c600309242405039007000d2039039014540900c1c0c06500c40e10340c8040c00030f20300400141808498100701c11440799541410f5155601c0910804800461014184c040c0714070441d104e040c058400800c14000d040e240c8660001c00401404aa218a0740c50a52400095021003500c4114081d440d1408084d08141e00240344001c0c0240506a0ba008110758405101100d144907c80303d48005016040301d0496000b0705d8008070480e800d8841d56805041c040c651824121043e26a01c80102004a00d00450710940d500c506020340701c14490107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 757873812 1250 757872562 757872569
    0x60603060f03032a06021308010e1f060506031509160815040207060213050a0609120b07020111040906030204060f03050a24180b06031c1202071202010213 68
    0x40900c201498945101c04035841e5110142c204584040030710004103000c1d041c10441d1a07001140403c0540300d0030320200941c0101c018007403900c2c00500001d00c025060250342844400000a030605c40f10981407102c0c0300820380460103029940e140c0104555030f074213000d940604402c0100d2800e240c0c140040c005041c5024047c0f8120903084803a4414507640000c440d81c0c40a80b20076503100320041d03500410007038012070300c0c0185420b00105040c50714101c8031401c10100c0703804031141c1840c55910482036698084134003a0543c00110301076804080f42091b51520b410280d94800003501810390414900190400c0d0007102c001c540700c8004100750316090058101030283c2c000480c1080c0d00d103035502c95942481c00d4004000808500f802c100c214520302400c1c1008030188010b0000442d1100d600c560b1149030581111244c100310302003030142c10006241d60301d008a01c0c03461011444494400e4031041602c00624142503000c1000300c0c002000c06000c0300c43c54860360000760300c503151402d003001030304160380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 757875062 1250 757873812 757873817
    0x9060b0c010f15060507030306180207020907080601050d0b0a0e390a18171005090c1c050304030602070b0f2a090a0302030111070b0a02161514070203030a0606 70
    0x40350781c10071209003030002141c4c00c60820715a100032603e4160007820321136000741c2001c03144017100c1280500a800400009100b22049007099945120640300342c281901c00d203000400600038501c540c207103940042496a07000340003c10ba08e588121100000c1c402721004040340c0102d00c1040b50a10280b03125030610340c054405507400c3c025090201da030600070b1a10100810060f1849a140c03400d01440e00c0c3d002c1c0050501c959500c070030f0740784d1055403482d000034a5240103140034005140d10344080344406250100900441c0303a4919021b200d104070051120544490008120000000300c6a200420398035106c6d42e8a08918640800050301e440340003000000c40607001075840d81c4034940004881c18404d200c3c1c0d125504c07a10b000010404454050f04000d403d0740c0b0740300c078644840b45840e000d4090103107c0c10f404101c83c0c1e90000c0035410b1380641c1c01811030805a011160300090b190000030440140030020000e0260007521a65020500a48014002d07800c0042800380864042c0200d5000e40302c0c50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 757876312 1250 757875062 757875071
    0x702040e0a03120501060e13182004150b0a200c1503060a1e03080d06080610030f02151204030c0b18060a02090a08030a030218040e0d030e0709060b0c010f 68
    0x8400380c208044020340c103200300c508c044407c4048100d6840719648400e02c49070340500425034a0700c985013540c6000c0406581100342c42d5024035290900500800f2246498000c4000d443c004006010380c20017071150f4188458400311401c14070405000d000c49548a00040849000e0f88007442012054040d000c0e68180c0104200710080d11698002c0d01211702c00c030500e82582410400020080e11103400080c0040c100013841d2126030385507080383c0d05803034015054489a4841003107160f10600c883c88000d1039000b580c0c01d8507000d460006e0340c2142d11b802c00c1c80928500355111106901001e804c0303804401140c000c160385814400054040c981c844c110828200805845e407481e0b6688400040c00018025000658001c0c603443d40b8045100818900080300e4441c0d00e02d41002d070103504101c2002d1b00340020380180f0140d80c5814040e07080c1078040a0040c12906400002c203c003d000c840c42d505050f4491400005a006550b03c2018028400f6407241034032150362804e43c030b0a41d54807905050b0000d060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 757877562 1250 757876312 757876319
    0x302070620090f011110050405010b1212030601030f0f0c020d020609031b2415011b020631030311010e0c01050c16090f141504110702040e0a03120501 66
    0x1d4201c0d2600c41048910340d80c070a40f140012150349400600c00781d42030250000035040320a403070304014019445030000340000000c0c4000d006400c000d44038001c043d9403050400d800750180c800000d68210206140104214210a0405040c0c62072100da6000443e41c0b103d8201d60b2540c1070050110201c00d91000d0107503400d05d9801c00750f4134003404141c0301503c000280d002c601400200080b41804602107812100700b441881c6210300f424044a11040b00c14103140c1789501e643c45144010702065882003141c4a150fa660207014881d0003514410340650f90006406010b00c2c0300c2c1a4440070404100c200b10030140c01e5190080c45c0b64610142507a840e81070100e603c1794004023080e4104099001e00c0c060380c44488418503549881c03030016680c40e9029801e40e0205010015400160740582c013560203004498460003484000301c421607049540c0070320307c6c00406941c40c0542104001384941d161143c2820300710740005003150400c00009000341d001708000b0041581007960301d00c20101440b03040180350314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 757878812 1250 757877562 757877621
    0x19020708190e240403021519020706020d0806030c1f0201060b040e150114030403020106210b1b040801020408070e10140108040f05010915060b04060507020d030201140703020706 78
    0x2c03d5900400b80742c0c0000780c01048049840305440003180c00404c44060300411500e101041e60100c0b10ba8000441a030f94120542d6000146c60b00440340203600400d41036401840c110360f1103802402141e418003850f80281801da644185100012015882d0700302c40ca110940f019084900b80c0e44250780045081c04100a6000705030741c4142e1200c00c1d503101c00003900020004031810b0807154001c407510303200801408141a030541c00442070f505110340d0054106240700403a240041d08400c01400740b0f440f04009000001041c1102880c01c1c111000c2c1400c15848100483c26a08540c02c40c4145a0120b0f00c2080543d0011640c1c540004038045400075460600d1005109580c04c0c11090b414000395a010408100e10b85c202e07100d585030410000c00c5554000d10304a00300c0958111030446a5003018070201c0c100c0c1e03041081300c007282c6482e224140f80007031301da0034480e118aa56405800b95541c400e02c61072844c01c9091b04c5c0d84141142d550041c3d4984080c58405d048400d446403032516010402c00303440c0e9045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 757880062 1250 757878812 757878829
    0x5070602011d070902030a090b01080d0311070f021e0409060b10170417120f0906090313211205070510020f04062f010c020601090902100819020708190e 67
    0x6204040251b5030350b0390718821202915468100504403490382c0c0c00010082c8001c1142c46100c2003554080c0090040703112200c8540c0546000a003990001d5801240186814615074400304181d100125100d01c020001a00b220700c03101c01a12020740341c0340c903070001d031402d1a40320b85500b105041000043d210004144035240d4028001851a14041c130190b01c500791f00402d031809031341413103900d4115140448509540c0310090720000f10b54450080440c503159004401d6030708141800e44000251864240f041d801e0074520806000780c6c80742c020942007c1201695003442810311780c0c03a0309a5030100d500e0440c1c5000e1a841c1d29a07c00f82c030501c10440907100d80d004440032280c1a00e8090750b8011500301d4211075032030b403001100c0350541800f2009142d543c19007122003014016000d65401eaa62581c2c540d058540007403009504c190325220352020680503003461900030046500711185502d8150b4008200c5e8082c910540351004080342d410070402e840c105602c140c03461352802079240301c80b05006c1071808 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 757881312 1250 757880062 757880069
    0x312050c01021309090b0a050421050712030501050910140909030d0501060306090e070b0f1b1912050a0f140909040807050c01110a0609020f0d05070602011d07 70
    0x400051680d505002501a24aa03c0302040180c056580d9241d1503401032031450000c03101480c254000440e804048d120780c41c420340d08a840741c44418118040d0100044a01041c6820f02074140024170115418806114a00906071000100c40d414401000300f800c800502c81052940660001d00800c42402200101c503c001d540d070070100e8490702c0380603085002e111034090117185010000198243c5c541c01210480e92012002c100b90400c000714107440b01c0f403a004041c0c20b85400c21480040b1001c0d400144402135403003101220402a502d021030814860750400d1040d074503804d0004081c08004c1d501008000e1060500c1e80c6005040000900700b1046105810180721880514103118800d5100702c0350b0a40d80207000c044030345068508410180c004450584481c41100c42d41e00c8694011072640404601e820000d10180c0c07800d5442c20060320303540da0200d0b085840c01400c10116201c000303142070a0361080e80601002810000003c3c00c5582800c00c900102100035011400858003050110a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 757882562 1250 757881312 757881317
    0x30e030f0705090c0403022707030605010c080901090503070801050f22151b0309150506090406110f04121101140d09060e0a030c050705010905090609100308030a0605090609010312 79
    0x651384600d4420802d0003190300c041e4014804008401c44190441c07a12010401168003001090b214483c0c220210b07140350040c540424081c00c50140481c0700d0801a182c0b5405c14517241d5000741d142e0b000300e4104403059001d400141e4440050181010042a8007940031844c0d40c42c0e50b1071092050b20015122107099000350280742c036000a10780340180c42d04030305429001040c0104000ca000740004008050080003502e003015141041e81466036240180c6000c0c640080c120081c548403a102d0200030f041840710100e022400b008602c2a035003400014200a1440060380d0354541054213102c041c1070103518046040020f8070034040748183c007100a80d0110150348000203420102850076034000d0061400415640c0306404c0d5000c201903000e48002e002034071507000d440354581d4440c011358503100389018203a80408101c000034494145000031660200300281d585180740d0b92510f525801c0d41c802c0d0f4411110580f522800c1c00907040500700b0f03540148041e100c44c203242d855078540d03182420000400404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 757883812 1250 757882562 757882579
    0x36030e0f0a0308092e08060901030317070e090703050103060b030a21050903120417060108030409020a2f0c1c1b0b04082b1707020709020408030403030e030f0705 71
    0xc4c1d0f1601d2200e035810985003c02074522242d4036030801e40200c000141440041c41600001d6554184640030b5412643c1c1500c4400c2c1540714071001c8808480010851400c20000f00740400040d5612018280120540d850003d4194158240300083ea0600403455000f68018141540000e030842070300090054200e51f100c40d41180b090040b038082c03013801d5807140d052160341c24624550140e00d0040c012290140c0f121080f903511070101c10b0700c1344000d102e005110340080c002000b088183c0d0300280307a0880070f454001d187c914000d0152444507480c1d68160825002002c5484681804000c40640c0c00340456000030051440715140300d00340450b002c0100011072441c140c7c0b10400408207010090724019035440d403a03030703100d02e03c5507911002e0340741c2d110503274070030030714a05000c0000502d002900304076680f00940d01c64440d07041424070b000075210f00c045128820002640c003801d4800762029100320f202542e5038a01e542401031a0106a04025105c0c0d003003414503002c00040091100c080350400c0d504d04a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 757885062 1250 757883812 757883827
    0xf080901030f092a23040c1b1b090c020a030f032c120703020a260304020904031b11030c0a0605040e0621010905010614010c0636030e0f0a0308 63
    0x11004c4a107030311464411460621405165040d07000c011807000b815201000910a001c0046030840749864051480405000b407900c00700d00680e0140c1110f840700030b082040755645040b24021161482006d60058000d076040e0b070200741e03020160300c0c4051520724051001ca1520700e03101c0b291410101d9118030054101603035101c0300005001608541015002d05034441d240f03410069102d00d112541140c140e0000c42e071050404078480c512402d08003d4030340c05400d680c5c1d15400e00891403009031094041c400030714000c005041c5101d0070501c0842c440d01d481003044440c0c80906152013000c44050780305440300700003400059444802d030b4003160b180c124090110f40340c02e00820700c0204440c0c55002184e1185056224111054010100c01c0d80708000070447d090b0f590604412a00f0300e880168000703490040da0401151171504514008800c0c49460f01004064080681c13281032001d112802c0d030b17041c0e550000241500140c844000d00010b40311982d2094100c400142c5540860000620340c07035000c02d80c407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 757886312 1250 757885062 757885133
    0x1f08062809050a0905011b0e18010324050106020a05060a0501150f03090609032d0203030720030316080a0209060706050c130b04180b090a180f080901030f09 69
    0x200d551781c0000c002c1081050720559260082680d0b1041c401051f87c041c0b40390b0003820004000c90b50744505d091850a01d9086640e060401132603140f6044c0d81d00d011200d11110a9201d00c150341c028201500107009020740c1e45441420080010410449c4900c0e00300100002c01d001944a0700601041c5060010980e4140d4107800908a408010380010b140c001280105900490702d508203106400f04030101c242e8040c2d00701c0e01250b0008041c4016003081c404074110a0240404a100e84028200000e8803034810000a01c0c603081180c0c00240d01c0408412981e0b000d0300070038407580084803000b0651034440214041803c91241d5503000741180e5550700040c034500da1100a07030341d003125450080c049840d500c0c004070702c00c1d820501a40d580c0c0b600082e4140a0b02940d4403a03805002000b0740050066a6000c12200c014a070300c2c618403039400c0e12811510001010b00d0740b911402842a10159141d044500c00102214134120140d00c00c80d20345510540828000c030303480f8a02c2c0c1d0604040c00d03281c1d00500c090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 757887562 1250 757886312 757886321
    0x100804021203030a05061c051b030f06040809040b1f1d0607051005090a020109050409020d080c0708070b0703120c020f011a0f0103021e091f08062809050a 68
    0xc03007a901001c82400140785080d04468082c6004490100031071103441500390030f08100600040003607100c1048000c50062101440c80460f50043c159400101070440507030030503004840031aa81400040c1c8601c0c18035040c8602400981c1c06c0d00c080550403450025500d098081020403014407000c840701071160700360a00050b000141c041c018a40ba07000515181e0303601c10301c0c01c481c0310301c460812000030100000005c0c0f00c000c86805a607000c0f055491b12003400014454000c041e030304042030800401c017203800d0700c0080003140b01da60000c1c4a0280b80c070f8501030400040c3d42000207213407020001000440c0c4d100c400c151500c1440c100c0000d4480e43c00c1c106030314203005040e100d85030b5401c00c1440d8070701c075086005601101c1c0094483d009402840302c011003c070301c030b40100045405c1d20b000721850b52401c2a8007a001d510030190002441e03052200c1d011b078019a0f6040d44c000001c2d02a41007281d2402c090003140b110305449a4445000c100c001500c6400c25002d0064a80442d540c8002450985c4c03290017 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 757888812 1250 757887562 757887589
    0x70f1107030c060f08150f1905030610090c02030a0507080c1509030c070503071d0901061211030d03050402100c26040503060705091f1808010b040e030910080402 71
    0x1101c0740b0030b03035440c006418107008441d81c0e404620b038840016040100c41001495032500107082640722800da204202c01c1080704101c0c4490405821030219154604110503406024912200208146082d80d08030544012051500841d0030900c00c2c1181950882e040c4c81004d54000c980700e840c0c8006840d45403421142180c0301c0c4122100006120b0100c01c080700504411800c0c0702a10220f0391601c0c141a070301c0409204e245c86002440c04182105900c22684c290049102000420b06d581d0381e0b1510582c04880c40c006071081b014a06002c016441e0822a40b98401241e040500244c50903030002040c0301c04004913042070103101d0081c4c0c000c112000c040000f01c0c000010103210050705c503054400050f0081c0c014280680f203860082102d5600800030364070100d10080544004800150380351a050110a2090f070521000e0400340ca41001d441c0c000d50040e00840c80000741480e412400c00090b544400e11083c0e82c0d8004010440c481d440340d0340c80100b102c1240c2400b4050b62528404100707101c400c4071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 757890062 1250 757888812 757888823
    0x30a020a030809011805060729070302120f1e1e0a0603060b0a08060703020d0b03010c11060106110a0b0601020a0b090c0f0a21030302040b040608010302130203070f110703 75
    0x80d004070030002d4050150003510000e98034614484040c004402028429000d5568803c806100780c0d00040c040c1c00120710580c43c004034841407a400d040345446280829641640400d801141c5440030350001c0c519140e05c100c0c1c420a8140d903007804440900c1c0500d804145240004840d800240700c94020500900541040d40c03040e28149058252103008010500003140c003107007881c4988070103142241d1002c05035003001020b0911a10b0310038017a0000d43c0124107082c900c9454a403240201da41c20f124000b081e0b1000c2e128180c00d0500d1008003403d18034140c01a000384200211304050000f80012401c8907654071200c4118291030302d4005034601055803030000c15031042102042894207011030344c10b002d10815511000d4511a107001c102c14841b49000e01c0c142c8030746c0c259444440440000d01304030350030700904005140548a044424407a0f00540220010031890001041141410103004908030b4900e030085055007002c1a0040c128080488a0b1040045104004d00802000e02c0110011544103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 757891312 1250 757890062 757890079
    0x3020a1b022b0c08010e1009110d030c05150c0a0e0a050a15031103060112090212060a0605030f0312010b0a1803060509010b191523040528060c02030a02 67
    0x10b026072620715040640480d6105400c00c0f0005800805000d0b04001c44118800342c401e1880a814150040443d107405a8810512440d000c4140c0c44600b181031007180250f07035507007a501070390030020714180341051a0703042d0040020810001c15403000c2980c070a100c0c5032a008200d00c00a00005001c52030940145074001002c2400042c58040007805070344e151515101807040111000e48a4418001155002e000c1072003104005560700565000302d941d280700030802d41001111002841c0342a104881c092840d03a5641c43c140118501041400c90b418060401180f8080c91503c0107260303001e06100c1e40719900004204501c086008080b2406181c10280d04001d0250b9203040050103004140e0381d03840316500e4140c1c0d5501c1811310058010180e100b16250306c0b0940d00d841507400228191180c42030800080b5541c8a0707200b1801c032034080c81c0401c0c400009407038038101010040118214114030004d02004004440d025400e000000100c84180c240025405090300202e41419000c1d80003d5202c50728 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 757892562 1250 757891312 757891369
    0x130c05090a080115060905130c1b140c3007090e060106080105010302070c051302071b0f0b0403150b0103090515070806030102042306070b160f03020a1b02 68
    0x15845042400250501c410f4541e617650020345a584640c018150012401c540300e610400d0203400c46041416140f506140107450030840400e41c0456900803184140041c81c0c504c2c070704400f08110700010500b11100c0d4602c2940340c2d0076003841c0d81aa48145460040b03144042070880041c055040102040403052249030401036003151140000d0190030301241d206000813840e54400d1003510b82c3c01d030b84070310a5680c5608210401c03070803a4411040090319602040541d0000c0d1000e8070310f000030155040c060750000c1c10440003494446a0b5008803d400034140810801f1600001843d900240741840000701492038000407000307048501d170050b02510070030b8204201d00f003000c0162849119956034004044d00d034882054280e11541c41400c1034114116014042d0841c4108654100da178010059440c008080c0e1310460703000000c6804021f00da400342e542c0240c003504050303000b240c00103510b011031502c4d0380200082c10310904444910104040746110308219121500000c00c079800010b00c0001d102030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 757893812 1250 757892562 757892579
    0x2010c0c0b0403120318060f1512020405090c0a330e0a27020d090209040b19231009020f0912030301030314180904030c12020c130c05090a 61
    0x105100495126a420041002c0c1e10302c80c2c481c462040107085400c46c03242080380ca44901400c003000d02c4504642d80e940070009850000d8290b40b004029240301d80400590600401c02201c0c030090240c5020b40002c0c8218801e41d903415031040c190b0300906200c0c0000c0c00495440381c03110200c7d5280f0544510348070780402c40300ea013107010418140070848041501d640c691743c8606444000c0790311322207124100300c5842041000c2e600544213040d00740600007000c114a800203010064195410303500d4442c200240403940200b2a0350003242c0324481824821802120088010040440c0011410402c807002080748200d9098108005102c541e03000d540f80c080402130f409080e0303c0003420070f00c6070180907803034902000088152070407690540c452032000c005000600c080f41d0701c42c008204c45d030a500000e0519580e10004502d0043d030081d5600102481c0d549002c6d40c050f910000210150b6020224420465070780044000c0d50f240a00c401160526100c0001d071554040c9194556000d031550001203412078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 757895062 1250 757893812 757893817
    0x2010b0603042010050f0a18150210090c03020d060f05010f081009080a05030405070815040314091509060714240f0103030e15070c0503060117030702090402010c0c0b 73
    0x3031600859907640c0f1040001c01c040308074241500d03004030b00c06001c241030780c1420710060801c0300128203244404032004004c43d04040d003540c0201e0140882460a6480b060341006240045414106d080111660740c0c1c4444190012500c070003441000244506007c005c82c0350440301c0e605200c144148161758443c0441d54007910103005a99651280c00400012581300e4043c240702e154005070943d14018428504564076400200700346c8007442031040c0051084005c020640d504000c81c0340418460400b4500107103003110b99000e200343ca20b070500400916030766500702000c0b5080606091a031303c002c1c0c100841c0f0240039800001c0d15894001c401300c41000000f0500c21000f6070700c800c0d01d5a070022003848410100034140c852035400b2690000620009029050030680c500005181d40e40304402000103003015440480c003159000f11440040251b81010020103015180c00300d1a01d0b070b0410010400c81e603e00490801034400c44c204000300e401e42e40104843c10440740c03c0014034000740c0d100c0540702d007280d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 757896312 1250 757895062 757895093
    0xf26180f010201150504180506160e181f1502030301090c0906021f1d010c17190f02070b011d0108010605130e0f1603030905090f041202010b060304 65
    0x400800100c1100c0350700c188100002c6084040307449081504200501c4020012494a408115100b01911000c03800400c5803d228003452401c056400807285001824001880301d106d00540d207030b9841c1c818119803a102d441d8010080c401100404d15900e80304550400c0a5100d0107256034501d5409101c0d1358040300850503681105010302460202d00c004554030591482102e004cc3c005034134007258605500304406940c1603500300030445410040703400e2480c0241d000c481400340c0d0355034a421044c0e9000b40f541421066071001d078140a00c1e04920402c4103280c0100c020715510b0b03480d10a9441d40742141d040e40c0001c3d40190180507d582c690f0724941c1540601c034179500040d407410000040c0760700140225403d5030340181c400d9201e800350041702070180024485221180c05084141c03616074100300070310850705142042c40c10b40399156080141c0200060303042240500100800c0002c00b5100aa501350029405800c00c402804a82070032401030542090840d84088000709000a10000c030341c400450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 757897562 1250 757896312 757896319
    0x70b0f0a02121e030403020a0b012402062202030115030308040c090204080307020603071b08031608090d050a020a0b100302091302030d0f03090203030f0310120f2618 73
    0x8034042c40300d40104501580d40c504240076000c0c0b0b40c04490b500c0c02409160000d209004a80a0401542c0c90780181310f0240c000300c0c15105c04500181612460785800c02a503609400540130b02d007030103890580307280280c1d0203c4860207400031041085480961200c0218940f9a220801d11a00c03031400034107032a4159016140d41204807004645d00249100b00d804885094004506d480c00715400d0040b540c100034011404c2c40700e01c0c200801100390021a060103144902e407d1a900c0c030340024880d204480752404d031800c020742c0c101002088800010b250701e90001e03038103080d42c072840e507440e04926181c03011800400075400f8405002040c4130040c011070039284211101a50380c1e0b510300551203c000032b501c0195040d4005214000241d011f4012081d8243d00c5103000704103841e15401084c03a60384130400c0500501c400004011035210300c05c03000c42c043c01c0e00031103541a444d803545a007107881a404402904110000c21072243c40c0310114492192040740d58100390300e6600303804c00018000540c4004900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 757898812 1250 757897562 757897573
    0xb0906210109080921070302130608010924060602071802130806060f090c030a0504080f04060c141c11100e01020d060819060506030307020306090607031a01050307030509070b0f0a02 80
    0xc3d41d2014171070808180458401803064600d15005c00c00d8002003496521280c5a5581d804101e4010a0142209042c01010505502864001400031074407001c411803031207a150000501c842c13980400c1500440f81c0202e041d0700d41c80400010704009220305550b81318a96090b03200091030110200d40a4401c020441e16459661402d01c20300c00ca4440803551000c0340142040050300c10b2115500094000d03014010007810a543d1041407585c2d0382c8039030020f401103810108170324104098103000d20202d03091900a002941104041045000b1402201409000b0302e0341207042c2072401044003226915451000740200344881a20728002e41c0000860340a46080900114031180b00140c41012031645400070381c03004240e03031180001894050f1199a141c0403c10001000d40c1d400c10070140201c0c00306c40940300300d09259801800b1520f850040030084181c100c05040282c1c3c01c24240c2e0f51107009418040ba180d40d480c54140d09064968100f03002c00600030829184000c2148045c0000705240d408481 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 757900062 1250 757898812 757898839
    0x7020d0c0305042c150a0f0b0f0f09030109030f12200a05040302040207140708060103020303180d0b0405010c0e0603060a291903050a0b09062101090809 67
    0x20340300846980c000e0085042008100104c0c40c00060034000701c5802c00a05600d00c10301189110380c3d05080c1ea508035007904103c260030462410358030340801803006c01c0c0100d8200303141100000440c003414088898022010408a8900c1c0c01c084c12601d070020010001c1010703a85514018000e0220311400c400000d0110885040c82442c03403065881d220744106428007a038039910354411007503111b00701041c100f10082c800080140c40d640050f0641920461512071440a030100b86072614580b940301080d507520400040001d620007204858000c403580c10242014920342d40410b2015108010040004407030400b000240701e0190b211001c00780f0140d58481c80d0403040d00810915020540303c19a005001c0710040191714102562680340034a4007205105034282102e9402c0d44c4d0b04642d0000280d80c1120208821881c1e00d8882c903a409407825000f0010402141c012072541c00c001400d00b8099880451125a99926003c8100d50710340004002d2066803104d1915407840e810070f2071100c0c0559a2a0b0521 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 757901312 1250 757900062 757900067
    0xc0a1202030f0103060e010c20010f06090608012009060711090405060f070905130e1e07030501200319020408010908070b071b0b060d0c030615050a05030703081e07030807020d 77
    0x23034900c00d910703030388034401003016600d5441044002d5058a04965032000003408150341801001d009000ea0b000002e009454100342d0390030349040480c0c41400f0640342200b504a02e140809954480000b034425035101c0b9054501a403004101560f0140d218500c60100400c00c20000380442c4200018640c60005d40c5808000f1b840c0c5903c540a020f90200c4002c81e0520b03080c9643e880113034a0062601114807030000d0625001c9000070588100c900303a00404000e10600009025183c101120351501e40300011104000302d400f40005400c0b100440d41c1c80c0d060610380c49003038068501821220000b00a00013003807414492035408100704442d510200b0340080c8600b4012100e9080c250103523940c1c24940708081e40e030062501c40003000140d210440c06100d074045040604544081c600c10400020b1384686004c202141c0005070380709074400e126018061120b6103012541d42c1c02c49501ca9482c0d510350fa600140003070050414082d0849924000c41c441301496840742c1054004c2010303800340c5030038001e0b10808 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 757902562 1250 757901312 757901321
    0x30a020d0f02040b120402130c02030a02120301050a0302100c05012306040203010b1b0124180c090501032f0a1704030c0f1e060501080c0303120c0a1202030f0103060e01 74
    0x2030707101155042c482c0141174102403e199a01ca48000c1c4100c150f400682c500d0320448045940440042e8400b09411316007580401c0703000307106040011032504562400001900440340390000900030342903064003a548600a620001445520400901482208403500c4e61071040308040c0e18021044070380072400c0c40c03c04e4400c0300c0c1a2984c40305818a040108115540c100e0b46038003843c0703895941c5140d10b14100e101441021461001c440032003208502d00100c0070481d40c09005800c841500c3d01b00030082407a0400b9202003120002c0c240032950118200f00c40b02d8900481c04602e440072206a0440751801e6008002c00515030f8945842c1e40501c1000b01c510038a007002c48004000c00c1c4c42c604c80501180d02054a503c6282c0b2920b0342c0040300c0000614400c0101102c04101e94440d1220014007501c2000e000354800c40034164029030a00e2400003000703400307540180c0040b4200c900011031900b19482088045d203022100182591380e82401c03c1740d46074000003403006580c660315202d0102c1d201e4006008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 757903812 1250 757902562 757902569
    0x9080d0e0310050f09160b1b030c070305242512020301090b040c0503040803040b041103030c0c03071215020c010612050d02010c0836070f0e13050712080906030a020d0f0204 76
    0x221f01e0a010001c1499401c440c2507241940007480300780421010340700c040081d0005140309102501344240c1d0700c40041501d011180d44124105c00360801c019109844e80340000c000360203101c00144400340032400303849600142c0c07980321600d03000000100b444d0009401c914903183d001d481c00c010040310000100c486000955008005041c200f022802240b5041c441d1a00a402403910700695901040001d02e954085181030b515504224403984683c6014800d050091110f803141c20502e20150341c4000703048040034040c140c4564040790541040c9025400300f00902000f21315920841c44070b04215965500b040300c5000150300708040100c40724855050607000700385003201050b04010043c1744d40411a0382400c4001d5180c07581022004c2070704200256401042d01c50320501c00c5a08140b0207110403030000b40245518154800e1280c00078200156a10490f51201000503e8100f00d103001e180d00c2c403a213502103501140110510141c0c6c3e00e00c3e40141b030b101b071281a08029009162007640700340e0042d0320 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 757905062 1250 757903812 757903829
    0x602160611060106120b041d10050c40090b03010204180b03150c040806060d0c062102070804060e01090510440709080d0e0310050f0916 60
    0x401c42203000e500307845103007040c001740411131102c4032012130210303135414100c000003103813006407911045014000d910115185803030900803032030118090101e51040032030184241200c0d03141040041d108200044060303031280541e118640c0f00c80030741c00109141c0c2c014030f02e00600e400700c414480d140501c00c50b012911048400950003001c02c407548000d1080300321903900342c020390039010402d000c0e012031144220619803a090f10f483c20804007914202e130040019000790320368060708000c91444c40b0444115090382c03504210221400208036001e403000c8252a000600101b0b0315020040c01e03001610984600307668422401011070011102d002c254424140c0141017842d4540c0700303622406000c0050300f0500180d20700c01c00401c000c1ca900d00c000c1c606e06920401c00481001024402840d01c6411210b01c0c41c0004031141410801501c4852484041c0144403511400b490b854070305200c40c42c0c400c0003ca600300094078058080058400d4201d40d03940607400b401400680581d080c0c6041c1003a5560030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 757906312 1250 757905062 757905073
    0x8060403120c050d060b1801090f05040b031507170c2703010209130b090c0301080d08041a0702061501170a050402041e02040e180a02091f0602160611 66
    0x3040990700400a5103040c504014040101030a541e509028090044c0101082942d0300d1013000000d00342e007108101002c0c10054060b0b41040644c64a51015050f504201c0300090204034610003c2d28140d47c00e040c8542801e504420000602e8000340a0404403c1c0c034448071229a4a034103602c0c040e07106105030205686e00a400714452003880d6407481c0341c81c2c01d010300014601007280c0005103408607001018241d603925828503c1b418200300805a0304440c54101441c15541810f81c8151074100e00c0707252100300440e40c00002d01388100c1d5400b0010700b1011540c3c002d01420075100c000d40f1808100c8540f418511190214901c95115030300355200340f06000c19464a90300c0c0c1240050241034042c009980c0300fa10b0f600443c01d1030364801686140400c4800005039075501d03101c1c2e00300d84100000c08508003491981c0c0c8107500c0310004140000305a40c11241e0a4060f9640e880b510903400c0030040600c111b81400c5d00124845800080c4c0030204483c48510b1f0f00745543d101021200d21a0050350050550000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 757907562 1250 757906312 757906337
    0x806010603090f14120706020304061404080708030c040b03150102120309191106030108060a050106030902060d51030c050d03091a090415230d050f01050402010908060403 75
    0x54004c0d078460106810155030301d400d0040d070814016004008103a40096000041c48200035040c42030803060301312070320544114501174035507003518020400040c2c00d8510010000b01c007103d4280c2102e000e031110712002920307401c000b5a1481c07885a000502c41c00361180c100329030030510000d419a8031132051400280004440c0080400075020028011140c24107550284801540d4a03000f03180646000720080100f4904001108161070042e840a801d1601d800800d40c05030b10b43c00c0483d224604d0407500402c60080006c10402602e4840401d40d0f901c1c400c08030b103040c42880c20146044050400040c612090040007800140030f43c0d140310042181106081c2008181020346c01001c015000c1e0030100d469075600e052404840b81c40c1031917030602c01e0300000c1c03040c103d1906204441200030840e00e003100c1c090400b204580101c00b10340410109801088407103070faa41c1c9851800429590120903a01500c4003100890f0180009540c00c90100340b81d10b001103402200081c2c038078031640d0180d41c2c2d410704068 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 757908812 1250 757907562 757907573
    0x10f090209150f0f0609090403030b1c030f0e01050915300105040c020a151b030c020601090b0a03060f022d07020105031e1501020708460b010806010603090f 69
    0x2004407000d034105c45d040c01131000341d50b5035004084c4614040e48000c98000300100400c40004010004021401582c41960b00440d40c805a50b203040000d42c00c10401004e8600c0c0142c5203406000003480d80304090410300702c041c0c0d664a0141c82e4000941c00710300740c010b02080ba1640410910300c1075140318000030004000610b4107070131a00c0101683e00690b49200da0603143c02c600c441e00d001c4c81020080c0c54035030601c83c0000c410b80c5407416004920781081080c83d0340d0002916680b040c46100c1c9141e445030b4a45c8800d0703a851030715200a5910031010804800e07880d020401030f4110030800c2240b1140000c030200121500421007a070414240d03007843c41c00c1c100d1760056405030405080700b0030780f02400c20035940e541989e10034940240101e4108007030703403090f1600080c0b0301312880d0013200d01c3d60040c08005820800c0c1e4480407601e80c2e4075041c1051481c110008804c041703951440251004192010b044c4248200503040a040c6d404001c01d440c0c0d61381c0c86046c2a0140e44911000800201107601104003055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 757910062 1250 757908812 757908829
    0x80706050a0c060213030b0a020715020703020c102615060f19030915090203060a061202060c032206090602060105090705360a081207081308010f090209150f 69
    0x34903c41800340d46a0f1035247c00004200da150030308540c0091002c09211f000100111030b0112214158034040190754000d4644507801d1005001d11044522900c08034081c005142d810204410059229018034503243c00d50b5001f0b03251480380c06002d000c440d0381401d14508a60040c13012170a00d5261031200c0c2c2e803400b091044802e00d070041594903a04a1b000404412017001c0c800040000421005028010507003003039000f0346100515890601d0412500b50031030180094150101c1c2d2240d100d00d2844074150440c800c50381d2455440855208207a04903100c1080c00d4207680e00b40e506c10300c08503114001a80e1390704082c0550b6506c0000b00c030010302c8062154000b810500240310001703c00c00c108052000c1c80d05450b52202d640700c0d1013490030801a0900320401c900030195140203200a890780b54069031944141d4002030140440001c40fa100050380001c088001c0030000006c11048520382030442c0180350b4440b04034422824880492000c5450744110054031a00810300c02d010003a003410402003c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 757911312 1250 757910062 757910077
    0x130621170f0c0d030509060f190207110a060309290105101106070305061215060d020109031703040605150f04020a030e0604060f0e06010e0c0310050d0309080706050a0c0602 76
    0x41d40204007564000b5401c1c816844030080341d4402240714100440c550b0b0424100138600381111000c0340c1048914002005a2400c42c2c0c01c00030300503030700c003440d0600d41c3c0c090441d220400e0f0840c8887c44001040e6034164000410b0364040c088032002d140320f03030f41540301d120a4803032234200140918005105502c4e041d504800b003050141440c80c00e14840380711050a140f400c031145008130707944900b0008a82400103a4245480d045400341602a07400c0e00c4040f00c040340580000e005140014250b011a4002d01c0903401540e04010345d07110052000340e03001c9250707100b11400c6940c2410000401d0940b803902100000603180100010b01c0d4002c084d050200a4000c4224030703003016104e1881d00440b030010300c401400f503809501b004c20010705109014064481441000c0d44991003a4010010900300d011456084000300404554a80715020000608805038110756402682e00002d02c04040d04480c06c01c0440b0b20b0380041d103100f0707681c4403800c1d5654010031070048003158a041d0900300203091580100040e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 757912562 1250 757911312 757911337
    0x30b01050405100f02070f0b040905151c12080708041202011b03060f05060913051f080303040506090f03121017030c1c090e04050a0213062117 63
    0xc00d0b40d100e0008075601044001c0030040380a8850002c2019410b00c503101c0a4854a281c5141c01d81c5400a496080d2080e84110000c19a45a02003a050480300c80c8242c442200201005e8181c0020340d2000e0326144800021540d900c04621030a0300745029002c20b51103000c95450341c00d0076941d04d49a401704a503200e10241e04555899403003480d440081b8050304100d0348181e6001518504040150704c0100070342d08114440d80090041d10309541d40c0031680d219100e03403260f000c61140c50f401040184100a0040701901c5580711300b01098005000020758800c070302403000c0740c0807600c0d03040741c854447e41c0450005466070020400b000001e80008030003a00701c007600d08010712190390344a02034080c00741d0940d8001d458000040c01d03011035104014400221040883ea1442400c0c8030782c000d80074241511500c60014045400103080c0710062020b401201e4001d813034548001d04be003d1030b40041a250040c606035809000c0b0080d8950366403589003103040e0b440740849041d103d807003600780203542155440400c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 757913669 1107 757912562 757912567
    0x7061709030f070f151e090b010902070201050d0606090305070f08030a0c15050708010801060b03040b0708100803040801021209010b0307060305130807050f0c1c0201030b0105 77
    0x3010500030300b0704603a540002e00d0804500150f2041c0503180040388030928040c43c14a400c8001c0080b82801e103450486840c140220072156507440140c0f110f50108014070a5030031560050103030500504003503041803200c2d440b42d02030355000d4200c0c50010343e07070113820410010100704c18009400d00ca9030400b007143c00c0004280c3d480c013503095420204a00110360006000f882550703404040b000700018401e03072a00700006803c500082c071800400350300e003220005040b4003843c1601d000700d912101c078440c2c903150b2940c1140c20380000340038504000c010380d10020b94000704000501c001c000071000541c40b000c096052052600c401480b28040ba41032070b01d0550340740c1c2c000c109101076aa260130300041c1c94542c1d0462066806118400404034035000902100340070001031600d40001801044842d038655080c01d21104122f0420110034405a55004000540c0203811001d065031042c0b41c00c50 = true := by decide +kernel

theorem cover : BRFrame.Cov 757733812 757913669 := by
  have h0 := BRFrame.cov_init 757733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 757733812 ≤ n) (h2 : n < 757913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
