-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3148
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:48:29.016606+00:00
-- url     : https://prove2.me/submissions/89b98563-b379-4639-9847-05966fcf0d7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 566007194 ≤ n < 566187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 566008444 1250 566007194 566007203
    0x50118050418020307030b01060e01140a03020c07080f0a020f040e030915130b030405010f0507021c12020a080609010b03010b12060117010b04080f0705030d050f1b0604140d0c0618 79
    0x3149481f858041003810007405080f000940c0181d801d81c0740c1d803241c0401c00707410141c4074495280030340b406021400703540724200094241c4520400060b81d48410040410802080c030090314850b1441e104100c540c180d084041d5114600302075050510880200465000c603408403400354101542c4440c1c6140381c0100303803007000c0441c1250000140d402c0d00754011071090f0302c240002c1004a0352052020f0448205644190050340700708540c3e00c0b0400003010f5010209990f00782403442003a560038200580c0d000003004030000e0010024401d071030800d116250301419084039014215810b0507000803042c0190406070141c0420360000c11090790254034200900c10030071100e243c01c0d42c0c4526403000d0702d910034406d142592180908503400c01c04081150020ba680040240583c06a480700c02c4506030400c1000c884101c3c010464540f24101404400c4c10003280d040180545181130b00780b060040350100410000d0b03030003000304805480d0f400100440c60341da00c00b00002c1c20300b144141074420401c41420040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 566009694 1250 566008444 566008453
    0x305250e0406053103050a091806060f1d010c020604360c020601050d051f0615030b30191e0506010b0319020a050306010201060501180504180203 64
    0x744009070300414070070100302040502d050b49011011340980a030b828001c10040c011811040007920a10040c4101d0703200d03141844965489508441e0610358101259001c00c0e270321f14003080314a800035095940030407103081c1441015041303080395180340707030301901c0c00c3c100140a141c940456440b101510050180d081d8240308004041040e814000c5004944404456449903100804145030040c10264541540505016440e0500740315610440c901d0131911401450110039000410412201c3c1c10500c444020503260700d05040308621140c440420400c140c10306000e01242d8482d2000d007414a0040c1e50300b2240c0c03080d1001080d040c85a12900321509001c0d0310012890a60031002400c10903004504c03803410fa2040010003d0610060180206242c10040040101c010404091980301c0640c41525541d00944802c44049910000c4a600401c42c00720510600b03580c244140c074040c200a0070908002c001031034224040e0708891181c2c2e44915240d904d54070300d1444010040c41556400b80444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 566010944 1250 566009694 566009701
    0x30210020601180f090b0103050a150c09032004090b100b090f06070302010e072306190507140d080403110604031b0219030602040503100c08010e0c071709030d05040305250e 76
    0x41d4a41e94580300944426116001d042f440701d413980328007080c40c82581c55a0750309038610b5452a40c3c148076803010a201d03c034000100401030303c80b80030300c8851500c1040040c0c0c01e40b03404205000040e915030040e141c000e00503c400110340d12103401960003001c0071500280c4a44807864100e000d456100301c10b80e00340c081e502000448480c80240c20006196090041ca01c00032048203105450103114401016002d8516200203410700030301c014402c641c028040c0e42c4145d000d400140e480c01e524440e5040015007103400b00024594000c916034043d040c2280a42800e00340303510000c02c0f03d140c070f14007461490030890902e021984d0300c0e208212a000010000303801140d4a007405030003504144101c5019005030107000d40c4020803032040300150151034a5040182c1d0030203a00d00c0c0c0c94078000b4004101000200501008100780078242c030008041c820b40ba56a5400304811b0609200b070f441e00301802e100040c0010b200241000c42c059805860707562680d501c803101302805058024030f540c040b482c041c00c1e00c0c052 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 566012194 1250 566010944 566010953
    0x31e23090d0c0b09011407020306131509080702040e1f020d15030c240c060b0402070b091c0c08180f1804020f0d0b13050c0a060306030210020601180f090b0103 70
    0x84c040e0064240ca030900100c3e9004044802881780c0d90300203516801031800181482251000c042a15000720700d050071606d002540b038011a282c001d0140d84001001c12000c045141c036001d800ca00800500c007a08200310f21b10842e50032160700128091410342c0101b82e0f03072142c00c00c0da0700007000c016260400c107407003550764108074101003020300404038044d0010307045640c40640205484e440725125a1070195070a49602d40381c00909a8030302060307120360204240008141c00401645c0203240d40030160401d0f003044c110000302880380d4984c0c142880200710100c0085080c541c266003641c0d10621030515800800b00020702ca00d08918841039100c45600106003640c001116032512030340c402c0d58034030114a046c904004040d041e0900081c802c803500d50000d0900072070b105c414962180300300d0450740f03d12041070001c1c03c0d442c0150440f0300000e0781d03004c040003540f51445811640b409280064900765040251194074440481e5844803284e4640f2800b000009035a8840d0710181c2d0032a002c50312a58403880e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 566013444 1250 566012194 566012197
    0x20609030d121a091b0403020607060b0a050a180203060411030408031f0b0a030902032d192a15031d010c09060e1507031e23090d0c0b 59
    0x4040090310f00e80b1008107a1200d49003402240b658004000030078940d030711929184150701503c903031040804240000001602c52074040d1a070a8400e00020903000000d0050000c0c0a41c0c660100d0310030b900140e030400492904618004140000810240c0e4960702c040210f40602481062450803410000810041c08121409540240e07805030480044030001c2a011403125264080c0d0428102c04015191500e40039600030000c0d64409001d40e825801d88041050790502824041030345c454130050700c021188130500c0300d100c2906114254080110507501ca9150708560140080501d01072403035003220b08660343c11400020494803d0412076880341c620014050b140c2c03101100100c074401400c00c005500c041c0030b0501e141c9100d9036408000d0b0318080301100c003686d00320003294002e6500d2103040c0d8407043c150014240c0c0e6000352100c82404440c0e062071a0307a582003448480801c0001c1201103401d620500c0c1e0b02e06055030f4058655102d20382c030800a1141d1a148000400820041c04001110031740c500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 566014694 1250 566013444 566013467
    0x6050a06110102160f0b01060906080106030207030e090109060801060b12011521091202061e060105090d05030a02060708040f0f110301090302011505031f02160206040305010504150c02030703030504020609030d 92
    0x500000950f6a80d04081d14118512b004940100300010018441c0710310990141000a00906d000080c510341800801c11040e0280c00c160401038403100e0074000b01000340209030041c81d100d402c80d45403658101c503290743d0403018020071081d0075500494642251107250030300c0c01c6030007540403070b2081d01c00000d02d50001d1544840850310441090b0390054068004554507100b100c508002c0c0000b82e0031102b02500c6e8101c020700950506c001440150b40980b118055800018420b0004581d1340a6105003c1d00e80b810041c00c0b6001c012081c010080000c0c11141c100024640c4454001151055460f100c21035040e000300b000c4c1c2661901020105146d41500050400b03915030b07403030500440d2580141503d50290300301c400c2141110244550510003594010900c545600600040c584455800580389600590003514160344417400c0c44184404001900d031486196042009101182100a03449004200020341450350724000201952600f200321006000001c0135120400040350001d0b080b0b43c8000e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 566015944 1250 566014694 566014703
    0x16060509030618100f150611100603230c060c060f0106021c0c0f0507081507051804022b020a021c0903020d1a1503010b0406050a06110102160f 63
    0x200468004031050080c0c0c2e0740781c042c0c2e2002d0700e0b07003c40c01d00300e101c054543c5c0342003c01d20655a031600d4811003003d41c2d40300c0191406070b465a407640c003420030b6a8907203e1241d0106440e40d203060002c10003d5004801d191405e6a210100b4020004c150152400c040c0510002500240009440c00c81d1480100303000d803180340c1c4145e1240359a40c0305d4000300e80e07452240c11180f120742c44c0d98076604126805076040030403092240904403024a0280d48041c1080030550080712281d0080d481d01c000d094003901416482400e40c90041e0a14280341401210490100036080c01540d0025881c0022080340400c90100402c19403984506400150340d94000e6000c5111080107001f11035100a030300d96820b5100040714955981c100d0900d00b95000c0250310000d980c41205d00201c94134040c03100c4e0032081003441c07240c1c01c0840e2038030444c0704031004d0600b9980c41140313952040c0d2070064140590340d84d20769603600f40c5d1424038107240b165265a150b00e00a100703002c600c550f0510740c09030303410801c8204030850800038403c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 566017194 1250 566015944 566015953
    0xb07020102041a071b0e0604150305012a0c03020304060509210610140a090518010905060105090a091a090304090203011419060203040905130b1005150a0207171606050903 75
    0x114251755112030315801040a04110b45022038514505500b00b41d128480c40b00b40302c428159240c1e40c803403c4031010311101074514042070b100c00c0345180e0f00c0e0b00c00141c0485406c00b03000489955070007e4891086004090500c403001c00c0241e0310b034075440e01020782d0056002400c0c41e005820303265a5030340d41080780d4144074414107003408200c0001404402044540280449490a003001000c4000d850018680212a54108542c031202c503400d002c1c4c040d00e6070082c1d0240005505140500140d0500140300d2076901c1d0800300d401000a80f810302c47c28441c06c42c001020785c0c0e902c90100c81401c0d0b00c02c070b9100c549618000310001c00d1810300880c58230029003048500e03891701004d10405020030076107880f40da030158000380400c1150f80fa007600031540c0145405060003078140300f952803041c0c1c50810354059510500d91402400780b824540000441d038403114201500303094914400a5945805d401204a12104034214050303089081100076201e01483c842038031140d45600000308180c105501582c0300b03119 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 566018444 1250 566017194 566017223
    0x180b07030e010b120a020d0203031309090c06080c0d091704080c040b0301140714120c180a081e031218010c0e0109030f053301080d08040b07020102041a07 68
    0x10007140700c0740407902130000361900c0e155035001c0102c040030005069805000030499807400c49021208035020f02005000002c21a1640c02c02200190f40ca400a000703000a11007070000c120015002e8a80d034110340e0a001c03c0f11115442d21050b02c1104100070080140c1c04140421911000b00c0d8043e20b102040d5020080842d4140c105420703640d400c44031080b900035031408181003a10815010504c14241c036003261429000d2803202c00c0c900c4003200e41070710510300464034401c019045000d03e2400d100c03c0311a004810308054250391200e569040d1100001e10102c080c0003103100c05e2042e0b4082490010340d81034180b9201900d4020105001d00c00c3c1c0c202e500e4469140740340b50180b0f000900180301a0b40c0d400904c0d0450381e80c821822030408040c2c4051096045c1c0030488624a905c07600360040c400c1d0394241c01410306000c1000114103030002e103440e030003134080c4510b140e6104207a946d01c940c1040350218191a8040c0503802486560010040c2d03000600f08001d81c0728070359004013102d03032040c00018003500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 566019694 1250 566018444 566018449
    0x51e090a0b070807030e03210a0605060d0f0f0905010504030f0305072f0d020c0f120a03140409180c0e070804020f01050c03030f10050d05030d180b07030e010b 70
    0xc40c8280010018039140010a03606440303203c1542d4420610b09000a09440040c040c51071900100741200c9003020000400c104060b00d028001c1e00039540c440d0902c800760800c0001885c03400b82110284400d503a603040e412a80c0c10039080600030b132030001070402c50000340f403e02a01a120846041d070101d152290403114103442407103198400e0650307039114000b0b417028102c0740104203c218900d446088150341c850245c50000d10400b00800a03d80091451214040920401a100404081c894244c1c2d017909281641d001c514030050795403603d0300d02c03c9903c058100c1d5030f49000d50b402000e000c03071416100594580c6162206c0b00b00c80c0c01440404c4480b075030b45442e12409001101c95000190082c4003103001410141000d03202c1d580141840c40c2032101011090b441c1d40c0003202c01b4030b410080c050501c00350303402055142028080907114410828125100c49035a8440d91480e0b0719195540c4000c108041e25a6001d4140d01e5404030a0700f01c0750900b400014090843c0f8211803d041d46840c1e0742c014030b031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 566020944 1250 566019694 566019703
    0x906040215031012030c081207031b050313230106081506010c0b06041b030603020406120b1b040b04080102070c0f060903061a0301050405030408060f0c030f060d06051e09 75
    0x1807074116040302c292030404c422911401e0140b942201800300c2c2800c4c103070000b8041c902400e02079006030030f4594907151280009068840003c6d12561800c070382016400203551160440e0343c8500c2d071041d05146140586418051902c84402c583d4a0340f11901c03160002c0003040d003003007049036460000c9855800c0302200d0700e42c0f1503c0c251441c41c00302c1d900050f86000184800c40d00d5601c200c00410004122101e480d4a106520913060782e000041e0381ca21061085251510480300a41480148071080344a01d690318104081c004d44490000310702281100c00d1201a40219400b0700441780106d9101e9a8030108076020b90403c060440710040a61404151140c0303008412080320340d141d40317483c3c000303140d03880d008014000ca0008011000c409000b1107a02e4400b40200d0740150700c070f80e0081d0760301d03490a9501801c0c00d4010780107a104e842a031062220004024060381e07000400703030b15900e0319601c544002442c0c1800102c0c004103c0be0424040103901403050020700300c1903440d034020251554641e4540740e00c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 566022194 1250 566020944 566020951
    0x708100501090b13091a1806131101050c010f06030609060e120417030403020d11150c0606061815180303040810020a170405010f0b060901020a060f14090604021503 72
    0x2040400d40c200084642040742c0d0180107461b44d000b034070603941c5040010101101e202d116001c1d100041c2041540401c40d00e5807250880b020402c003508160703100304090b04481d140504219001c10842d01100f000c0d4401542c22820f580d041090036602e18100001c0c01c802a001e031140303407404511400ea0310002c10310745680e0f0140c0b4285d519150600d103005a001030038102c060303090712061101000589070303e64491400385c02000310420b000241c5c0100514180444c601000341c0006014221901c540051002e0b004403044401c40d03141c400313040320003002042c0f20311101c5e8031107495608842c2031480900201106511654a065400210010f0556078440c600c00d1101c1e69000c2c92801d0701d02c1e0301d03503406449910603c0c64620605003040c40c010000d10025103068505940d9200d1846410400f44245c110020046d2071030390a0a21550000c0c0d01c07400c1c0341001500a0341c035201d001000c0c00b2140c0c400e000c100702400c0f200c2c1c1541481d82000f60342c0d1800300ca080340140d03109500c480c903c5030144150b911 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 566023444 1250 566022194 566022199
    0x40f090f020901090b0d0f050f0a3c0e0d0e10050a051c0605060f0c07050f01080a1e0204080307020901060201060b1905040e150415181d0708100501090b 67
    0x80d2419640004c41c1c0e01403051540031a6551f802143c0d110010300510380501880c1d503403084141456410001150214001903541032080303001c1580c0c800c0c032041440740c482c15103890140819480200c06001d0802c002d1004400e01075948803090311a040354030381040d0319003030310b00c2e03076103d800e404054645204442c001000301e24240303c80c0e00c50b0342c801c100300c004c051040c1001140555590000c200e082e008082c4c658210040070400c408d2000c07080000000900c41228003420740d01c003070000a068506c0151030301e00055120382590a47d031047c1c000c140c2c51020b000d20f003195180e540b00c030380036225004590203d101e81c440600002d0783c980b05014507010340c1c0780c0000c55841c4c80124480c9841c2e03885c8464240e403d001d000c0c000080d543c0100000c0610400300c41603000380c606910030421046461300300d8015140300c903400080c0a00031000d03810300b07005800004002594070991008144070802d04603000c040d07104030000403c441030081802d04040b14031034014070a603607c8030003001c19601c40100a40c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 566024694 1250 566023444 566023457
    0x7080607120207050307080f0d0e0102030103120f030905070609050310020a0801060f0903023f0d0c05120309070609150f03110d0e010e07090504080d0b01090b040f090f020901 77
    0x5580d110710b5004240561165080300c0c540ba8180d0380d107240d10f400c51000c07003441c4100072034400c4500c0080d00a40464180da04004c600d0b560441d500c0001e40322150002204102c0d644040004e114040c2e40811051600030b412034000c2036490710300800750313411402994007a0245401c1000c0f00c2540e8005e441c5400c406407118001c581c02c1c200119012003406a00200b023106181c0e0000c096154084490302c3c0b55602c0040048003504401c2ca00b00a140880c40f40003100d0301c3c83c01c5ca2036201c0c070105291090b026185800d031208008c1d81001c0307140c10701d403410003043c540000040c0301038104000344040480c0c0450b16048030741d44d40c1d0b00d0590b0f1103a00a0001c80301142c2100300e90b440e06440703503026003e0a0b00702c0320b002d400c18080702d08601c11507080c14071254182c1c2d520181d0784109081084024003c2841c414103002a00e0070307585a58403130240d00070000007035460b603080d44843d0f8001d481e10303400f81c25442c01d42600c0740d43e105615054495503101e520340a900c0c121402d078811110380222550004103031100c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 566025944 1250 566024694 566024717
    0x6150412080c030f030c1306081521060f07030b010206010308040b0304061107030201140c0a09030f021c0c14090f040b191109150304051209060d02030f040507080607 73
    0x605503a0200502c0c4207140820003191000c40f00034401307103000750080b5080303503128000c0c0040c1c10a0901903410a6080c4070070320040000210f40000d82c003443ca17070160785881c0a00843c803550070041d1401120030503203000380020000800d804481d0944a0608c0360707400d01c0101080d40040e078407510280409400b16108000a00c10602c082000b1908540f14080000708815801c0b50300d01d00750880042100140d444040b1000c040c02d11441143d04044c620807000c2c5489040200941100142d2100600025a90740309001b95a0341c60494020342106200a9034400b6092400e43c142c400a8011b10b02e03a060161215a518100b030b015651003604940340701c0346191610385944e010344200070030f12544010500500003101c4080d006e11449072501c5101c082e103a150781c10410901c002c05c6410011311035170900420001c5030000801c0e420840c0e5015406585031803030b0300071409034070480708401451070000085c01400300e1468020361203203004200740c0b10711320f07100c1501a84840f0103491060010340c040003107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 566027194 1250 566025944 566025953
    0x30f160c03050c070504180218090a1403092116060c02130b03100f0501080c0d02060f04120f03020c0411250c1412070506030a0903030b090f06150412 66
    0x902c1042c3d0321400311980341c1c1d983d0002900b628541035407004a004080300c0c83c0110705003440108a000c101d90030928003450190185544d07142d4000c006030410031800300407030701c1100900403108810b901625913400101d0800322181d5104801d103a800640c840c440700114000700084403d826203429035a0903a040d43d183d000c00810054107401030030362070b0380c0322007801240c2d90410488040354007556010840c200c017104044210769050344068090703000b01d0305102c2d00d50b46081d40d020130142e04440300c60b01d8000100814403d0702036074200b000058081c2c0d64a40a014401d544041c10b80e10035070803151200c0d0340074140300a8a000001c540d4814400307200d40304074001c0d1140003045031f21800030710620403402601d84000341c0006510200f0800d05a20300704081d13040200b00b000c0b112207184001c055092900000c240c251000901100745c003550b034101b110406110740c20941200000600143d003505060a503410a48003c0d00e049101d43c2042c08065400c01d030310345c20b4504844a0b171000c0d072170b5280191503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 566028444 1250 566027194 566027197
    0x111010204140405220605070e010801050a031202030c070303030f1a0d060b040209031605041b05040308030c0423040507090b0301030f050c1309030206010902070803150102030c12030f160c0305 85
    0x4010310843d28141903501c40c17000850b0681d031140c0900300c04a02c034208080081d00a500007440d5604015628005100ba9100c0700d801c0411294480c0340b0300010300c07068504034254000c520200440d80594034001082c550b15412030000e5608051081001d0f040f81034002c0d944004041c0c4284c0c000c3c01091546000c2003c59204a55001014202500d800f00c071400007410801964903003908180624003d00203810036204200c01840c84000090082c40c040d0320152481c01144002401e03480d0000001d0007410658058400521103498603860340e04c413400c04058a143c0c20b59807075005900c2d0100040c3c01d9072040b8400c3e81211020718810346142d0075915201c0e404030b20307800c0c20350701840740f500c0f101c0311512441d0b01501c203060240c400103040740091400900301401a807100c58660700501145000c240050201d0742c00903400c130180c000c440c4045006078218021030a050035140079404001290310050001984600302a9888103681e940d9042c1040c140b041c501c41c0d550000d00090020000a40030700d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 566029694 1250 566028444 566028451
    0x7090216030e0f0d0c140102010225110a0b1206061c0f1d060405010c0305060a140f0915010305180a080d02131203120e120702010903050d08060111010204140405 71
    0x40c140300c82d43c642100840c4801060342c1040b600841c81020402031000d20024811240320248004d519208252000b41c0c1c50030740c1c500c4041519460039000c4401c0000140d00c01c1d6881c18041d20749000c050b951110346c081c2d13411800c0103210002c00340d0f0003c1c00516101d070842d1041242100042c04615820220794020807180085400e903940e21603a01e07480b0207100d890481d0102c09000200304034501443e207582035074101061700d02810306000c00e001c810313503c128515040d035482c0d0440c00b00220044001030503024458440c903030849103440500c00129030803152103500420a0705c0501080c0c580002a03000700010814001c41504101c02023000180c10760001c01ea02e4859200c003500384813524051011420003903100d0358502460104001c10950403051030741c03080c40c00c14800c02840f80c0074194181c854020482c41000c4038000114401160b0262240e40e01454100044032040d014429010342040400d48509020840000003110035500500840301130320341000701310165464403c140009400040c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 566030944 1250 566029694 566029699
    0x3030515310617070305070e010506030a091e05070510050310091113080102040f06031802100c0804090b190303050d050402131505042906030901061d0907090216030e 73
    0x410001600000f040c00d40c0e0303200a64500a0440c161651808038980140750344044e1071a2071100040006070341d401c007a41d9210240b40c0b40482c021811b850510301044034502031210010a1450410a0060000d6a00c082e00e03030582c1c0807400c010780c002054595000072110240701000340c00e0184103800c803c0e000a50700400d080e80d000d09040d0044112540d405403500840ea26a6010404014078503580910b00007d2149080801c0606408101e5220244005401030b0180f40310555014050780701c1c2e0300a03d240342d00827500c40c0c3c030f454440c500a0f01801e5041940d9100d00250f1144000240e0f2003410b07001160b070f154680364a031400f07961840d8050800104184c1c1e001c2180408480d80c107100c0c1c02145905102071920001490600d0b0802c0110750079100e0014110500c00200c1c05c01540006200312404807c0712141c2d01c0345d0700c590710340f40949410303013000d040c0c01c8184a016440044001c603903401901000159402651900d6018049004404c0240c9440502c2caa180c00400d008401500205001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 566032194 1250 566030944 566030951
    0x3121503070f031a010b0703270b1c0c0e0915061b060a0f0c0c020f0f0a0807170102070c050609010c060608030c0c0a0302090711010f0501030303051531 67
    0x1282c44025000090b40d00070740714030030707580b8400e801c000710181201c2c05412000b420505100c0c054800611160903144140301d071800a5510001044000d8070950040401c203220560b01e0f0b101c0348040002c000301044258229017402c04420300c1c82d0090b86e0180000c00041c1a4004a55946d41020305002912201c0781d0070007000c008107a0700342c0318501c000c614a42c08100515071400c2107168241155110001c0c0c1d22541e2a00300301c1000c040e40200302c4007045804a80740b032000501d03d800a61002c001011445d40300e100c402000030f00c04c0012482c00304031008400e0410300049101b0040d8282c0c4114800100140c80d100c409014524220019000c1d0b002c062400400003401950380a0840d40180c00140340c43c1d0010450b100045804c0003884d1048500382c030740b0001a03146601040ea000c1c806085070301800302c0039150760b151140c01d500004810002080510040d652801c0250080509448031009002810302140941c1001c514080d0741a95808bc51003850485051041030040e101d994101610389 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 566033444 1250 566032194 566032199
    0xa0b0301050c0304031b02010210020f0903010e010b180108100906090b1f05040911011b1b0e0916050910090608250e070c030e06180a0501020312150307 67
    0x1001d1040314810a52503400035500d00b85400c0203889020b070f0a40100d044042400e5090050f40d02203110120445003c0740540c03141c104080451440c000c07542d0081d0158030701100810034120541040c92103c0090303400811600501700e08004050003400b59a42c50740c007150000210305480d40c2311400d054010b600000d88c4000e15510078a500c8429100d101c0c010113001d2103140a007107007003071380c0c0020902100d04000354030f11591504d40c000d00c4c00c9612810310500c00e80706058688003c04850140c2d5002080c500300480302821961108a02c3c003c0c0080b82112a000840e550000240803134810801951504032902d01020003410000081000c0c00c218420741000031904500c1c020080940200e00241c8850a03000c0344c10340b581c81645d00980381a002e02d00c410005c0c414507c06103600b185103442d101001d4401410305854144004031081e800c0000001c040b481400740c110030b810b2901045411301c0c1c01540d24401240d0b00e000c0c195070820320302c9502000c121400900c4201121080020341518016039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 566034694 1250 566033444 566033449
    0x27030a0b0c0a1106240d0b10030c380403210f09140906060c01020f0910030501060c03050901051c0c12051e04060905030301031a0a0501060903081c0c091403010c05030f0a0b 76
    0x21410340d0028423600d0b0107031081c410000040448d901610032901070389148500f005011605a08650000c110920503054045040e1440c60450f0055034224084103001d204003c405441c0c0c03001d21100800007034440c02c19a5815105118420031113920040f55036201219a0400411050103400303a544100300b000700d541107a07001c1c009803100b4009900c500f900d030440d400c00e000d00e505900050404051401d0014403042d0303004401c0c000201d4040c5005522418001c0042c2c2300c5200c0c2911680c1c030b0a1b00e010048550311802d80000703445d251165102518240015064002da8505179a941c8090b001c40c18540714450412500da0b038442d0165101042c03480a5072500d608691086e00203980c91080c4861503217000070040840e5401c42480c8004002961400800814811141c04000c1030710f000011048105183c00d085034641242c4040200426100027402400040103440f680c004545091a032200b40d01c0d061042c1d0b103071948252525469950740010801c0b00940003801420010b039140000400c0c0d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 566035944 1250 566034694 566034713
    0xb0f130f0b10030f1109030715050c010603060b030d0807020705011d060d0209150705121606060b03060103200412050f0102040308030f09010227030a0b0c0a1106240d 73
    0x51002e44000850132100010780c001c0c2c8407140d440c200310380410450700845880003d200021681d20b0900e0800c8011884421111131041201402480d03007041c40200900040f1341c015510900d0890480e0714126081030280c500d00c0007120b1220242e00200700400c0326501a0003070000c031480046050a482c0602c074000380e0150007480e000140c99038003250014a0b400c140102016150513a00e030079080c0030681d5100d075034411131000141c00c000790103d485c03599550b400c5104401b07140c1c000700500c20703661101c000d4802e94000b12040e80c00281000d01c0d0019819016102c0d040c4066110620303850720b030a1211111000040401c2150184a55200100072203402e202400146114078921650b90600c90b8200141c40ba01424180060744100b01d502d4000c0b91030300203038140b400721010090181074036030000303802d00031071000281c04440c03154200525642543d005142d18141e50300c0d010100074420907016070b140000c075001907841140806008144044130404600583e0007801c0341008002552645c100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 566037194 1250 566035944 566035969
    0xf01051b030c07050a0b040603020715020a0f020c0f030c090903070b100510030501061b060b03010c0314010e0105221811011202030606070f0507030f05030a030b0f130f0b 75
    0x9070400308081c0d660040c14044480100021103034550f003c1e061400c20410340c8078901c0b400c81030503400604081005210040e465000c5079803041151a400c40c107801905100c154414080103000d8540b000d421450506101b07600c030403024004000301c0e00c2e40c3c0e0034052807400c06000c1381410300c01803052000040104040c10722400040c14414511440c1c0800e0001d55040c481402c0141801c08005005441e0300520606441d01d606001c444442d1903410914020a0984108c0b42c140d400c0c14220345c56150503801c41440a1015000c0303000b180e9840c161215200000c2c080c0e50340c0300d4000c01c080080c018030542c0c2880781c1a9038101c0040c0742035003c0000d400394450b03600101d6002c03084070310400d020341c0c012600d6500e080504d10190301e10f1414500140c03e07442030342001440c1610002c84481804800c2042d2000346a0200f880d101c007070748500b840c80d5a81c1211021600003400e11101c42a9400c105a180c0070119000d00480c08100030a00003c014062425000425541e9402482c40c01c3c1d85d17244207410b2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 566038444 1250 566037194 566037247
    0x1030203151e1f0e0d24111801110c0108040206130f1202030607080c030c0a090b0706020408060a09030c02015c0a0b1321110606030703020f0105 64
    0x2003455402e001424030144016298032505124044001084428a41c035080b00404031040101030400740c0002d0060250604500407c00085241400e804200105406070402600c401d040c00c0007000560b9558400d4a40e5a400248598081801420120041c000304030f00108017500385500c5510034909902103602040003051581820810f43c00e0901201e60001030030315118083d40b424035040320311844050200c1a081c1310014000c8115031194032508080c00501c0c901d25130341c221038100a400394100f40500842c900407140411141c0340d440c880d0a0000d6030644a14003442025001580c070540d80300150f010b082c1003060380481a10384401402e100940300c04044403040d081d101c03508506d150b840c0018038102c6070715144110790720300010792021580d4000d800301d0a07652080f8800c49404500c8100611080c800921404d107092507001c8080101f14540d543e0700209071582d05103554500031f81d1200e03055000716005101605158917100d038181018144145449599001e40405001080c2c0008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 566039694 1250 566038444 566038489
    0x6071704090510052106010b0a0c0b0a1d0a050c0d0816031e020a0f06050a0608030304030509090f01050f040905120a09090b06070309150219081801030203151e 70
    0x8401e1a250740744001d40d108818101442c58070900100791b4941301801401c0818030b0210321000380e54415448800381540c000b104511a05004440c03c000e812021300b944042506803c00f1130014600207110038841d50007500420f202442d200070312a010362080000e4606c072104100c902c04003848480e1000301c4a100703a0780c1107101c8030800c1420400e03ea2440c1d400085401401181022400820002c40710a030402c0d00017030f00c1d885070302d5010005c28044d0302c19076a41c0400720070001856003142c040e002c0901b043e6003000c290343c1c40c5d65281c01804424040d80742c0c0b010408040c0c3c001402c1a40c0848174282c4134400b03d4a034500c1000320a81d0a400c03801c2c030300b00000d01d03000741413025440a0250009040090721700b41e043c006240d502800f101d102d4020700f90780311180d07000344401c9803080040042d8400039500541c00c10a19090807616903000407481d1040c258207403e9140c980d4031038400c80c0c0c461803604044000f145c4a44003000f0b50072116120a00580c840003020170440d903248507489084149400885 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 566040944 1250 566039694 566039699
    0x91208070b060609010203040515071a070f021f0f0f02041404060906080d0c03140304080316020a0c120507031401090b09010c020607034205030a0206071704090510 72
    0x810401100501c128015a4244030078010b1740d80000c265016600112450803c0c1c20038071141030300302d000d008e10140c0700400c40c5026014503100365820901078031950f0303103944a0040814090380c0e203201070030005000310b00140f42e000c03201034541d011086440341050b000c03428184050807102640c0064003c2004610880f40b84022850140300e09001004002024421549403808480c0c8030034910407418184039009216908051090300c0c520385e12106110030381c1e240c0c2003e0404180302c4e001101d851245a09020301240003600024910141640c407060f1101900e080c0810b0212013041316200f142c06205441c2e000c4000f070100b2100e018040040e4000050f15030182c14010881d81c0080c2222007940d00d80400381421680c0481e4017a40090107080c08580c040236108090010440034050240c0045c03a503214980a2244030b90300c1d41c0d001110220348141c641c41c0c0007095207810380322200139400541000b0b50400111290404143c0100000c103039400c2c0380d541c00c0e1040c20b0b5401250f405a184000c00d109 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 566042194 1250 566040944 566040953
    0x902031905010803030a0902180c0304020f0102190201120b04020301080a0210090308040e1e101403121b03040305101b0908100b0316030308090d050a0801120309120807 74
    0x240000803458280a010700d500d00030300c040c1c881c8000360140d4181c0e0380b05c400355010364440340d5550280903040700000728103140261949070a90030a480880c0300da410707918076204039031002900e00102080145070304628030751640103640b0349041d816140391044c0c90b16050a00c950f10b82c80558002d104140c040c29180b48984104103030704c030286042e0801d000941a00340040340010080d01d080d40e4204030b0380107807600c030700814140800010010800d604c40c082d0070801c0303809030004442c0455400c0350415008051980c10191291180c1c0c20710084c000c2c040c01480f5412070600100381c0304510550036245010348a850b400d0510554880401c016500c5130100b00e02c0074540c04403088095018501030180b681404100e27074469140503549054a9103481820030b1981e0f09014492151512074048040b050b920316000d0400001111030190f1030150450000c0e0850260342103035041c0e5525541c00d112a8208035244801c0200b0f081c0581c100903a10314007040d10b070440310003031308010b010340000303501c40506140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 566043444 1250 566042194 566042221
    0x2121b0909120406050f09090c0706060905070c08090a0b0c150a1a04230a0e1002030903070b0c09150301090e070e01060507170a0807020f012304080c07090203 70
    0x41d00007164040d242c000281c001c0d10742a10b0a0303912618225a4990120348040d985e8010a04600da01c000401e080c0a060750b460002040c0d06446200d090110a55a40d076030f8045403c110707100c60102c1c0700300c030003440060074620003400c031401c004002d60300039911f80e03560076683e8000302140f80c8030fa400103c81e61042401496002c0d88100d9500d01030207502c134450074400c10f0728035203160035000d2611440104894030107450030f0240d040204079800c07494942400301c58041e182211041c0c0b200c0c003480c0d100c4400d131000740c02200d2240340030b20011803801449075600e00c0050130080000c84540800d10604082d42c0c1e412481c03450071852080460b44950510103e2000c803140030340610a25030005008001030b102c0c00c10014115841d50500648440301c40c100705102c201d09a01e034100b4440005540d03001c0a410048041c01400e25608a548501031985254200c0b4401540321490085000c9801d0390340040d02e155644c00340c0718a0609003003204641805280c2405600130356007041c0c011041101c0300c0741104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 566044694 1250 566043444 566043451
    0xf070807080a081302010e06070302010f09060b101d090c1603030209010f02030703120510090e060a060e04081801050c0a0506011802121303030b100203031b03091902121b09 76
    0x8503102c07002900e45e800a46090812020076002e00303c040340350380c1032600039400740e0b40c0d201e040507007401400d500f0310b072000c01003c1601c0014840c44604224040369441540b6100100407001c10403251002e01408121a1010052100080c1c1504000c100455000341065100c3c00303100781c0b0090388507541c100c0050200c1c1e511900390130840d442407000d90040b0360301400d01a00903040740000140750303c5d500000c0e001c403601904100981401d00e81202080c40d00040e14034412080030004100254954165a40049041d607000d040c0d89414007800000e82242880d0400031501410b005103404c0b480a034003401c00700da2903020b4480e900540010081c4803008680c030220f0402c000c108619245d00c541c40d03900440d0340603000c1e40304407000850719401c1501a038464440c5040045c0300f0070b00c200241c0b000955942c000c81f40303008421810320340c0b8148800c9030019030b4000c20064003d020000e0007081d4a808210440f40107030380c0400d0224008011081c00c0c008401c4078144051446205410b4078203102d90080c0c0035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 566045944 1250 566044694 566044711
    0x2060d02120a11030403180b0c06040b1b180a0306060312030b0301020906041a07080c0607091508041b091b180e010302120106031505040510060b0f0f070807080a08 72
    0x101c2040710883e0018202c945c4140d15003445a00314541880340e07014200103070000d851081001503401c01200001402d0b6110300d1140004140c2c960b100c030301030700060f9074510300054803203010720219000743d80121680003144800703082c050321540e494980805542c0360b0341c0141e0780d8034092041982d8042c0d050280d0348074180240c000f540343c020450041003140c403907407045042800c107454641840b2040303441201c0b0030a403c14041500d4154030005951140e80a58108020800c0c442000410310010240e00c14400075039121003c0d640c0d210344800041254040c5414a4650b8100022440ca44c2510a125148801d1030010a0140b181180507002102c6038070900500c009001e02000011144000b01c0d0540c0d0b8143d41c0a003c4050321142c40703001d0311203504001d24400d0b8801202000703502513405580705900640807610900014203241044880368002e0b02e0200000300321144212244800800038103011803080ca00d0a161070310f07101c8845d003298508803010500000c502107a0f83e441981650041280c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 566047194 1250 566045944 566045951
    0xc0d050703030f0c0e040b030a02090703150f030b04031d0409080405040f02090a1511070303030504030f08070206071b02031506040b0901080a06110408010e060702010e0708120d020702060d02120a 86
    0x413000701408048080f840c0910407070f03c03030030204c00e1903c041c048210301e00e5019101e000319040103e40034000c2d0803851341e09000c0241541c400601c030039420112100300d039000151042c01e61203030b49003202c6104005200c602c1c0b40d062030314203800715100ca20a414607580030341c26203a1240d003000208025205d40d501000c8116005002211a9684110101c2c003103511101c0511100313100640c1c15070354542681025803141c00303941400000c2c103030503400461150340700b9a18813071000e2444605441040301034070010700603407004001801942c05043d6141c11070b8061000c003502c040195002030310f42401c89416100e045210000d01c1442c0c1080c0c01085402c010850390102c031503060000056940b07084c003001500d040d440d42d11590103207181c0401c0710040d14184000740701d903d003806441690345005683e40e0006618004040e40c0032140400c3e4441a90800d070050411084074002c034003c0d80e000301d900c25400e60742c200314070b80050b13840c00000c3c81c145483d04800368940c2d0f0183c82c96560760380020240e9041c00e04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 566048444 1250 566047194 566047211
    0x210d020904064b0b0d11220605122403010c030f0f060503190c05120105090d0206060f01050d15060c06110708160501141906170c1201020c0d050703030f 67
    0x43d000d40e4070030360f41c08501151311342041e5003403540a007807001080c18500800260320030700c614540034115104440010382c07085440e0798000450f00c0d845000c00d50001e180c0c000c0040342d06014140705c0240003e841c640702880200844002a08485804a081012a0342d5250340640e800050192403c0c03d407002104102140c542004070307403034900c88a0050316490200070342c14200059140e03c180540809000444102e0080c10101c0c000d00b010f481c2e556252081210098040d480010407503c501406030000101c22400c01c01521960410f8a1800305d458a508080c0559141c91140c98000c0000c3e54401d122401d1600700a01150100048c1d1a07404004010030000316680b0300403075181c0440c03915070b0760343c007482c034244ad50040c050103400e115203031846820300018065614040f100c8450441d07040041d5a5100c0407080400860880040f094011841da041d06242010710340724900040d4001610309040c85500c181083d0804003403002088000c5242400d141e0f15201e100010708221004004021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 566049694 1250 566048444 566048579
    0xe0304030201170703111204031701030c050d0f020424081506011b05010615030e06060f060705150921090d14030d11030603210d02090406 61
    0xa83c0c04a02c0a10140c0c0c0480c00b1144654801c61651038484003c0761682d2280c51110740300d420503901074000030700350381c40c0b800140c071180d400604980e40f058410304603528010611458000a000039940140800781c15005603d45000b14491a10a40e8010149005240240c047c028480d04000125400f04001c820800150460582c00c54001d0031b0049801c001a11224420420081c00400d10b5082c514000355808250b080140c4080c41a01e06100d1112200030f075a51344c00c0110780c400c5e44007003601103500a605010005002283c040c2056601d02c214a000c004980304058440040d55407000c221301c034050500600400c20050402d112501e088005000203403e02140c0740007800801000f114814070407802c000315022610201002d001a4941c403c40000640044903824003d0040b044041d6402c01140d40031480c0e20010761031581042680144040250042c0c0d00c115000f0740e41d04000300e100c114242078201d0003c01d503400c0c07207014050380d02640c10b070400c0494080c1038900c00304c10300720041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 566050944 1250 566049694 566049707
    0x3050304170d02030d18060f1416050313060e0a0f02040c05041401080c0c0706020a050d0203030613111c05090f1c0c060b04051042031118040e0304030201 68
    0x3c094100d1702007a10380c2d80a5400c0303c0d91342c4502004100620b40104283c440031940c202c4044160b9441c2508220741c3c800004a010303141c0980540001082000051400d40201075000340c07071070149130700055000d040801180b422115900503034001d01024440c2c401c44c5000c1c0201004441d07149821400d00d850b0124201c00680300300d03280c9041c449682c0000700f2020524042d42c41c00c1d03883c0320403101d003107503280c0000e501c5800c4584250303481e000d00c3c41d012a140e4000002c4078040d0070013412221220003010380400050202e010950403110042000d00841c0e03008006900410045a80019050500490507880d16014001030501e036000301150350f4038100032003131012000780c1c2410400ca041a2a00d441c6000300420210907a2040c41c20381031100c0c00c034040781c0240c00d99a0045400d0340007910080c1003c100c441d003401101099109840c06810480c0c0b5000303c0350562042d00340840c29000c984007044190704022010a4a4020032482205a10b0310f070050121080c0f80d900590f2030030782150002440c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 566052194 1250 566050944 566050957
    0xe12040f0f1d040308070e090709030b01090c0f12020c010504060f0e0c030c0d0201090e04030206070f0212030606071109010b1e04051503070219030c0c090b210705040603050304170d0203 82
    0x1d1000d500001b841581c05100491219840284400c0c058904020040c060790b01d680002d86803054042e0021401648600c10030300568202c0c0c0f00c010031643c501c0e4086421345581c00e885000707583c00b40400c00941d41c00b40182809070340700305008100340366943c660b407080702c60000001600b54041c0600c10070907200410340101544e410b580c42c070034103001800186c070b070300545a0080075075003003510821050640c0030611500866017540e0301c2c56044501b03101207070f480c01c0c0903801c2d85801e40704001140a07803619500070002a841540c9148807000f0040010300b5411003688441208000010320f800c2c80a4240004801c607a6003052440c01c050500340840c058599a410b141c00600700007001c120b805008002c5502083d20810842803054214500204002e590b41b41c1160b46001c3c004022178540401d004640125001130031003032030400031014410f4900c414042008140c00740100204064583d8010392000d140940c009580d11458040740c00412105e4003040303034541d04000303449074040740d02000311441c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 566053444 1250 566052194 566052197
    0x40e01090b010203160605060f090103080a0f2a0f06020c0a02032107060218101e031406091909030e18070c301106061903060e12040f0f1d0403 63
    0x2003c8d0381303000214810b04486c40e07003545d0240c1814000400c01481c01d005090212150341c4100040c450703008181c412103014145c03026041403402560501074480503183c0c4803540254070006854419449800c100d070b01192813103005400c01141402507040400c0381c41c02c00d40034a180d900090318160b00c807401c10f005444004242d1500041c200d4006001010359a80d00140103007401c1e032826200e14064481c60003800c040344003c14400f186a00540644107040c100e05202d40040d809607a4030042102201c0c0080160a100074800304240304540700d07105003074046119442d400070700880041088100e0a00c1c0202e442c0913502c0100b00326540354170080c2a03040507030107e00c145521440859810380400504000001d183c511801788845603844400c4000010303150f81540c8031500c0f01c40c08d00010380d920401c0c40c00000c080c000c00b00002000c65000da40501011000c2c1c80b0b28850300c501c0c1d5881036000342d21211034481914000d20002d5114042080200640001e00701d038541096081a241c500041020f030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 566054694 1250 566053444 566053451
    0xf100509040b06070506100303031109150d14090f01060801020f04030201110f0313090c022a0d0b091c02011b050c0102120a20030606041703040308040e01090b0102031606 75
    0xb1050b11803c0660740100c4d40300040d1080c0d80703400000b07014802d40c3c3d84070a0340001d05168401e902d612105d4101c0e840c034032004d0700c180141c0c0801d044c203e80f903074080700014041c955101c19041d214560300c010140142156805009100c4081c0081c2e400e580c090b0b0480351617a4030400c40d0701d051106070000c5808980d42030801c4d40340803103524040c505145403444030207410701000604210b1018160103d0056401c0408200b10881d0403046c200c2c3d80f243c4c01240c0d0f0640414130301407414020803d2140c3c0c0e0503400014248910800a55200300480385e041d40c1c22582503000640340018020042e074120000b4070a48001c104136001090390706201c0d1030407100f038410700c2400125040304c0c44082d0112489040f00c46c20f44a12400d0005501009213603c03403100d0b04510307000481948840c036003001c8a02602c4010091410982040810400d140b0741c160301c6120380c0b0041100000044090300036200822403400e242d01c8661500c140700043e00e001c010101d0440d00204401005000d10494110b141c0d40c1110002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 566055944 1250 566054694 566054711
    0x10e07060f050d060f1701090b0c13030203030f0702031e060703020d0609090c05100224090c150a020c1005031501230408120403052a041a0f10050904 66
    0xd95443c89950807144600341400340100c0c0c0307140052108400c039440d00c062400384e03000c2118154202d6400c1740e001400800301c20042041c460465003d4005915503084e80031080d0342e40d500080c55680b00344040c00d1142c1001c2103810962500b440300411031110b143d002da88040e00300e13440544820009040c1024140d002c1202c2d0b0114425601c41c50140450420400000d4513500302030307012400510403244107080c00c07089901803d1021440b03603000e80c140c0000c442900003d0303d0b4a0b00f4150010700c401801c3c41003172003265007556010f4080c07602c0c07100300303101d5540d03070b0401c5900900301000340e0341c840c0c0154a420f4450300c110ba07214003129030020000c100c10003400c001c8401201c01c0301c0190045007050140c081c0040b41818502c1c00bc0c03084403014000c5603075407003102c024041c190143e44005481074001200e4940301c0541100304107550740c0400f450180c3e0b5801c1e2800501160303040114860880b658103041d4103241409101c4005a10040b07581d015440000d080082c411301c580424180030700e4031040c52 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 566057194 1250 566055944 566055947
    0x2a05150f040b0a090602130b0c07060509030d20120408010b18161107080f060a06050d2a0f0509060d120f0905030109060b01080c0702090103060207020609091006030b03010e07060f 79
    0x1500c514003a00000f18a44582d548c1015030707150403000c00c41031240581d4071f000410fa8050740c101c450031503000e0b001d00000c0201c5541502d01c0080c40b07200e030000040c5a603a18600e5201880a801c0c2c00e000010119140e030709090344c5034212030b005070300c4a000d181c041c41910400e20401c82e83e0341d030285c041e2040f160240b082210841c0c00454203da10106449208030116004002084524a40a0b80c07003c886550b6101d00b100c10540f102c52003490b0300800108040000f10b00410540b4441e0313000000200d01c0404281d001c104000c1c80ca91060452030100380d070a100300c0c0f034240121030300320750203c4d40b01e0003410b1285c0701c0404548680c84c2d884144030310403040700c4461340a0a042c13030042030010020010020142014070141c10101e030154000b0b410f03000000d0100b4010420340c1c040c04d8014050422503030841e920360009500c1410140c0c0c0c0580240300c000200c0e40c8000026114aa0100c48040e055140180c09420b4610b5002900c0c130903410040c4645003800000b076058102c81caa07103881c68080001d01d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 566058444 1250 566057194 566057197
    0x220302010e30030a02010e120702190e0901020702010e010305042307090e060109050f0702070614070203030c0a021c1104020a0e06030103051b1f2a05150f040b0a090602 74
    0x34082c0607610b08442c80400c40310b012001d0036503503043d0740080c41038425541007107482d01c0d03140c8808100640f00740320040250900c8004180109159494002010344500c202002104201c07485201c80e074000641c201113592003419840394210a0030207020340e080c00d90755001ca481c121000600c80100c1d20f4030610101e0410030865000300f103045c07010000c264a124170300b03440f07403024062039004508080100d905800c1c44c0c02d041344500c48a0f805001030070706120003101d603181c602d850050346440a00c40c460150f907080c0001e11907071442400030480c20f1000d2043c010031140c465010030b1103049848014021a040121a00850070202e6005135a030008040a886071055a1107080d00541d022001100300800060380d27a1980d19940c02c010200c021000c10080d40140d0303001c0c031807c119903070210b06a81c3c40c01160071170701d0300c805c0b6400e400719052010032a110304039507040c0665007603214041d0340120114000b0380a4104180b00007809007490152a640116039001d414003071110340d00c0c1a64070130310aa039030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 566059694 1250 566058444 566058499
    0xc030123040f1e0309031e02010c030302030601022404031e20030409061205060c090a050f0f041b09090603020312031b03150102160602060115110d0302220302010e 72
    0x40048284040c10304004080060602003151502002040d0002247c2c00100c0c800903030b50305075101c200e40030341d80c1d0b01200a50400391141d070543c400c0c80e04454800c4400400c0709400004000e017a0030301d00d014200280f4401c0700e001502404002c100c00301c0307501c6a11008003400004200302c552000b154020a9924600c41c55022144c1d4614048000c162040c84034240f000b0319005400301e4000d03440d445081002c520920303110380e0740454400c00800c941e041519a90002380030041268951110302000b00e420380c0c1d021500c00e11030700d000080d030300d4003940c00c122440c01400c0814801c01c0040d04603400300c0e55a48000100020680012000401c111601440080341344d0301108415100c1c00c155254048500d8500c1c000c502501424428403242c0001c00080300c02c403800340c0d0060440b42d2030b2980d854080c20441c0c41500810913104944440c01c2e8082111985007035140d0340050f034500c000580c1c04240c2c2c8500501811043c02505c040000d40c1e40114140d0003028120341300c4601012412038120102d6129 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 566060944 1250 566059694 566059733
    0x8030d021b06100806010905060901122a1a0301050307091d0a060501060e06030f16020309040216050c10120b0a3804080a11010516050c030123040f 65
    0x220b04112414507000700301002c940d9039008640c2c41c0c0e40c80d1321049042c0d45003105c616402036944001005000101d080044440d8000c401081010741c00041054840075000c00c1030b0700824007d2002c000382d140d00741c080c041050300e80b00c415045504010009032107501c0da02c10701040355240c0412b0740c402e02511a04108011110044840181c40c91406c0b0002c4c04d400d00c14070b0302090031051403542a003450002c80e1311416840036080000d548241d443c400d030010100f42c04046200034008060142c5451000b0954003014401e00c4507020340d1803504c0b030300d07090020402c507008880c860000413185410003103440704461a0000071420070b44950108a1004141d4000302a000e910451802c200c0120360402810820100c1440311b0910341d14540a1f03140b0840c414104150701400501e004152549260000344e141458460b18181d61015900110000c81009840701d40100807011860710b82407140340c1c281e686000d201507207144e11050118001c41c00130005084003007030004040810218170b00f00001e80c0303c42d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 566062194 1250 566060944 566060953
    0x7050913021b10050108010b04050411040507021e070e0601050a0c0308070c06140604060f0b09040b060403050724080f28020c0106080705031209060d0902150a02100608030d021b 78
    0x1160894004e0a82882468699460700c055408030341001d009051145800041a04454660b071040c00000c0000800c50b4046002e02d181890b0b9402c003c3c0200041c00496400505401d401c3c400300d1815031002a04581c10700c0801c102d000425904035007003643e500e4040c142540555a0902e040ea03001185000c028449031402024070040c0f0412520f00c0c0c000c10003a039082003490b8842e80408410803450060a8085c2418022183c1c9031802e070f0000e13000c103680540642e0400c0e6a82c0e4448e4900010381d046144c414404444107600d4001e44510443c9021142c60300142900300203a001c0340301303035010b03008a001e24002500c03c48030362800b42c98151640520315003150750301844d94400b8004c209a0040d0201401001000030b41840d0005082440210030b0740f02900c1c01c042401008141d91201c2d0008282c00d4440e4a00009641d9920803d40c0341055007907000c3d9520301844000f41886007035008413b42c1e5140a905200a00b07001040d5135000d00451001a40d03030700300540001503400310b803040340854070a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 566063444 1250 566062194 566062213
    0x112110904301b030206011403070f08010203190207170c150702062a0f031902070501020d1803080121050f07060f05040b1c0e1009020907050913021b 66
    0x3501540d03080302c4401907a4240c02d540c00040012a0036021450103801070380120014041a40da140c407070207682000408a402090352080f0755500c5a1060740002c01c20703580441040145040005454880d0300c01e800210301c0c080e41c03550360100f0810800e00c2100c20b1b0380301042d241e051080410000b000d10f4040c1c1301181142c64000720003503640c041204c0060072071008920030000c6940d0880031108042c130411a403410848a9014400d0030780008107804c0000c200c2090990402005100901c402030041c4000740c3d0382c105048940058810300d61041d403a0300344440385c250200b0341c400c008605503042c01002c068006a0954001c40160384040d01403c540903800e0b01380052580040c00f81e00715100c41d101c40616040041046d252400340c0d00c80e016841c001004054102c040401024000e07805e44440000d00441c00d1160038505601082c003010159502c01100f001e51512242947c2c1c02840e500d0441d20744500f010200c0c41c00344150000d03100c160340200700400212150301050f490791400c107049804004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 566064694 1250 566063444 566063513
    0xf0902091519020f01020c0a2d030801080105010501110a0b04110a0b0d0b0108040c0b1c061806080f2e0903020a0b01080c060306062d040306050112110904 68
    0x102803480c2c0340c0162107200d4002c500d8104c18001d6509001f10312014012401603500e8207a1800300301c0030b02c5001d02a203408001201c9072240500c0010300c3c0aaa03c1850b00d40c1050b0351242181d20607048541071251400c2e000e000c0500000701e0111655000d12090085c0c1c80b580340198030030348031500ca00e500502c0c3c0c9034045046081032014080030429000301344241e030f903010019501c2000569010700f458022107810300910030030200820031320711900c843c9540c02c00100c1011040ba03605804c041c2c40840c10000c200041c508601505003e40507150280c8201c0c0784140d515603860501c40b50301e0088803001c0000e4880b61f546844184000d442d805001d02800d00c00d480c000303464148c0c0440031210011500b00115003c24001107000c40103c4c0508614950340b1450100001600010400041e03d5006420f40c01d10502000408400340b1001d0745040e00c5600b5880c0038000c2d920141c02561504607408e51101c08110b5041c05c4c9101d84400360f0360302070181c940d42003900b00003610f0002070070311070700c1100e1582150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 566065944 1250 566064694 566064727
    0x20d030f030b060d090510020c030f030403110304060c020f04050c19030908040608040b1014010c02040b0a0f1d060d1e06060b13060314150301060e04060906150f09020915 75
    0x154030035410b548556040741f0140049000d411581603c84d0300034011490355143d458001c540141c02070600d09000424644e50600c0e55026400c44000140861030200440c10300030b01c1030590190460342030290307140c2103040904a01a1442d92034142d02e40440c00d00740e0398001d40c8240b1f00703540c000b0402903840303844a102814601055504035004040000028240e0143d08051000c2da440c1d5801d000c1081c6004e4011251400780e40010f80c1d0081e0340d6103038200a591440303654002842ca81d4000f600241c500040c5410308658120f42c9003207107132031900f080010f0382d5420348551030130b500c081d2200d6200a6411000d041d01c44c8203074000c0c1001d262000210341c40340c910b00074280e2482c91107030050145460350401c41c02e0341d02404030500b1030185000820080304000c040e00b00c42e10000740c00000d90640d1103018219008060360251038056442814400740007044c003c0120382c0090502c82120f40d403804605a040c0103461040805c00c0d940491402d1003591644440c01202c80034640664072503c0715803407841c3c0c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 566067194 1250 566065944 566065961
    0x1801080c0c3a09050f010e10030e160302010801121b080115150c0b0c0d06060e0901090c0f080405071526060a0e0402130c080a0c0c020d030f030b060d 66
    0x9880c8011564494981c0c0c90980d1070242e2880d9a4000f2201d24000a10084003a40703d865410300c41c0c0492500c0036501c0d1905011302100c03484c2c1c0c0c041403038480300851a0030a550303540281200e040c900c4040c40544d800c440311604503601084040004400b0303007801c81401c10340711074001d090000c200740003941c1001500a56111102440d00f50002c0ba51050011b55041005450201003044c551000010814050999a0203c034905299240c20310b1150300c04100d80c0345401810104110f90b1011255003801d4282601505205400308050110000302402807130760761012604006100307001a00b042400c1c000d44005101203407920394000440b1034090206c1d000514030328564604913526036044804814071a028540241c0030084040c2061070300d40070548010400d0360007070410355152141e80030601c0f4080d1245150f40d41e01c4424100301c5500000c1c0d131001e0300d40303400300a4a121202c0260f510b0070400541d00b941401e080d52600aa500143e000d020703480f200903400000854400c41485850f04007001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 566068444 1250 566067194 566067253
    0x4060207060e150f040b0105060c010609061503060e090a080a020307050d120e060f070c0201020114041406010626040311070602011b080103120f020307061503030806061801080c0c 79
    0x1504e90b294081c801465004550250848114400411280c2004402032a8440030200003084003500c0780880000e60f6074990160007103145403100705102a80c103214240141c1144c0094800c40e0401c11b0302203945003450900503204034000502005024002c000720f0350001d0f80f10307041c2c601e0004502c40c0509090400d00e2031000860400c3c03504146404041041031040d01d81b094041d5450301c922208030b88018200008034199965140480c4210015903e024400d510803000c0300c4031001c7c1d5500903070910906900c004103010652210108e00303100d20702c0021051001d0813001e5042c3d03403242022161016925030803955801402c0010524541c1904020046801ea10004403200082202292890401d10002c3c0880c0c203001c402c90f000e603200f0b0001c1c00d0145410700c1182e081c003c1a48514084500c0008031460006058070100304044e003162220b603100c441201d20b18240400c014030f0b000c0607c4140580c90400c0b26400002c1e12401140080d108088034110441c1c000303141b40b482d19000170084580281 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 566069694 1250 566068444 566068483
    0x906010e0903070f2402161101080c03150604091805010e0c0102030d0203090705030f0d0f0305010b090d0204060801150509010509010312120f020c1c0801120b04060207060e 76
    0x111810740c00011902900d504c007009030610340c22611007a2030f4040b15210302e843e1017803450403020b2541090003c1e01900031541e944004810303581c6400040040229405814044404d081083d0f00c04010141c941c0600c030881c0400304146480002204c511940e00480321941c03400442000388040344484c0d20f20144180001c221a280d288001c17507480015000b80c500692003000510403801090300030390740106080b81100c01c0c8545481c0024142450070003541c10650040600b88020756011001c0f2160180c6030078100040e50410014003403500c20410310764050300504c00c03507030308548856120f400140b03c0d800c02040056100e01d02525640118850a845826200300115480ca40001e00f141200c0d4081c01000d9401e01201040d1b031401404004000c110307a0ba00c03480d0070080790500052445540780c01c09400341001d14171820544400725054002041484c038018442091103d100202154006106107120340da50b15018000e885404001002e00b820f0042c40c1c07043e0b000c001052415080e60002c02c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 566070944 1250 566069694 566069701
    0x3090109050405010b16061b170c16030c0302150c04090b030c030312040f12030912030608033a050402090112050c04050618010f14010512041e0b0906010e 68
    0x1050380c0c800c0c0030f80417640b0030070030490074a13400f0700900e003c011f440f604011a5060701d20484071811100702e03122401286a0b107408016100114168a82c015003004019040012900c003c44099000303032001000d10502810718800d05000f00212100b012100304200100d140240121b80560402c0c07080c03c3c034090800a400000b45404200003e082001400960800121180515140501501c240c1d000b00c1a01241000310b01034801e1035024081c152404640110035203071418007541c540b4580700c20546031450501c05010b0106c1240c1245031201c18001101d40e8000c1c5110722142c0d41d890301c0c03000c00e54202112003400e50f1078001600c10380c001c480c1d001c0305aa0f10150140380c001c03418802440c5030420fa8900003280783c1540701a410a4000d040c1102c01f05a40f019010586000e8000c1180c035682c410717040022101c402c071802c541100c2864402d0501020030790300135485501420003049941400240e6541c09510030303803410020b401c41e988054074200003000b140c9484d0280600281c4e400c2c0c06000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 566072194 1250 566070944 566070949
    0x2010c122c090411060708030702030306010e121c020c090a1506050a1215081009050105150901090c0509061c050a0e03090f06310f0f090203040203031b0309010905 72
    0x214000700c107020745010038542e0380ea41c6402c054440021084c1e4001c0c0140720810100710f010000d18032403480d0303800039562410300200251074040600c0302c1a2180c00c11a0640038085408100c80d02900e80a43d89e0101d180c039006020380c10100da0103900380e04414400200242400183c014912400130000114440c60f19104110350700d00c82c0e01c035100042001018070290050007030f84800302c600da00c00e07031000342943c03241c11050525000114946803581ca5500c4030b000e000f0203218070f54000c1403081d508518001c1003400b00b4440c890501c504204680d64411201007140618212402d003000180541c2d5034005030b40503040348035940b41d43c4038829031a103000154010901c0c03140d8140100200c00a508150a03541086150110290380d01d0b0020000c2c04100001c5841d20444c03921403201e110280941c80c2c40e4103807a10040304d03503072114444400c20a0200701036110600641c0030f42d0111480541c0c8c981e52400400c0c60b510480351003086000944528203034604001c0041c159010342641c400c0340103030f560000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 566073444 1250 566072194 566072267
    0xc060c141e09090c0c0d02030406020a082a0f010605060f0d0b01030605150a1403060913050322090507020a02090c0702010309150204150903031b02010c12 68
    0x100c20a80408200d0141c03241403002048806a200441d0a4900a405008281105000d46024030066400702c0c0d91405003209010f504c180d40c1062000b5405c192402e00000d40d41d0540750300160180c080000c00d148135001c1201a062080440e02c010714a031a010000903540f00c0072010100c009510b4045c0104141ca458400c6800c4441007108145c2080140d0b0481401170151200c024141070340d5402c005595243c0c100b0004400c4510581581c54400c542d01c00f405021440d00e0007144a5010000c1010780e50340c0c42c0119402030f50356802c0d42c50b80c000c0d07440c1c61442d51160916942ca1070580e00c85c914188040442c0c04000d5038000c41d001c4c41152204030f4140c3c0d84100c1200000d51212040d00000c11264200d40a885003c0c014500400d49aa2035280c801d0210700340600d481419800050503c400d105407060680380400d1071400040061858400400d9000b1a2140c0448068405150700942e031160b406002e210b03401c965840101030403100003406220000100c10f51090464040050340d10746042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 566074694 1250 566073444 566073467
    0x501080402091e010b09121501031716050105070905011e1d1809013602130e060108071703090906030a1b050a050a0b0d0f0f0c0c060c 59
    0x849640054440760308124000b9002403440e80800701caa100055001c442011080c02429181c9003a95141102024080c80c0160040303541d07680c4e800b41c4054900c00181241240c11207401034065054140c2050442e801840f031210134102c440700020302181408810b6010500500343c540b02e03610b61650b220019150060404003101c503894450980700390480c0509d500000c42c11460400c201452442c000044c14000d00c4d144035542442c010040040d9032800748101c48242c40240c401440c040c40ea03203151a890405891034100060b2400e0802003151142000c017039a41046c078034240701c44a0788618041c1c0d50f000900c03403048184280701b40010000c4000d80c044541140500217145040c44c40c00c1072050301c9002811141e0944144102c1001040012a80080d61a004441e841c0c0b610300d808100041950103410003846412060400c200711164a011510104070110012460b051a90f4141d00140369802c0b11189407070a102400300c055901016074050207210341410820740f007441400310346055015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 566075944 1250 566074694 566074697
    0x28241802060306040e120c0303091002090a1818050a0c1707030f081204120201050606040b0301060305070c20120109030804020603041b0f14100219050c040e0f160501 73
    0x40010450900341350f08515418410b1904440b071883c0b102140711540c1c0c2c04040030001c150000700600c5241c09090141f000300085d00364044d410301040800261074000d09200d104c1c062908200705440210301c0b0b4015020300b502e200c1c07150390701180e030f800d10700d46501403480100c1d900d0540c03001c01b2400034211910481d14000240040005a04540d0385002456001c03270b0a5802501c18481c4900764910006e40c07510030380c031504188180c555a444003130300755a40901001e2288500340024003100c800c46082d641111a1482c02040980703c9440903601c0d04074000c400381c2201e07241002200403001d01e4042040810081d00c9190001c0c60f00801c0600b221101103000300059a100041409071602c10040c607007060081009408000c001c4e207100c40002002c0d0700151410311040303010803281c07450514500104a050b45c48580240c04d51400a4035201111200034040030034400d181e0030701004100883c40301c80050001c1114003003242c0c1a0b0391396007090209004512448800800c00c2c07610f20034240460320306 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 566077194 1250 566075944 566075947
    0x10f02190c060f2d030216062009090a2a03020301080d05091c1a07020606090106020a0b19060506070b010f1e180f09031e0e032824180206 61
    0x6131943d10120303d0300e0300e0301403040503004d0101c641c20350200c079509441d00d4410740d0001400048002c0a84188405000704106020203208441c103a8580182c3d060b801f048440700000c437100d00d10400c000c05000e000030a044280b0801f034040740d1940580c0190306a505404c200c40c6c14102c500d90031207441c401c1360810303070308912041c0c4964241c000701503000d50304a10503d001a007500e2130350001002ea00c0304544100040c1d000c401407001a0620703240c054003500562024160840342a29108026900605441c540d61900c001154101c1c0c030a9101d18040c110041050766102c0761410810000e03002030041f1040d5000130403000884e441e1045c07041d190080d807003400d00317001d600c1c0c00754014001c1002100320030320711740380c40d60501049414480c120840e23102e61210354800181002e010180c1c0070120350281807081c04564250160350016544c480909403001802d501d04004d115a0024150080001c0400746544d05101d007007a107520501c031a034010000100603e0300c5000301090039030300e84d14029411500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 566078444 1250 566077194 566077247
    0x1090302040e03161b060e0f010e03100204080c0307050307151206090207060e01050c0a0e060c030d110304060e010908040302040f0b09070c0201020c0d11010f02190c060f 75
    0x400340c00400c010040031007524203101300c80b5200f24010500400845240500c2480e001c2030f00c68060030300700a040540342481400c01100040f6000340b0f404608a4148015030507000f2561790b0410100c14200500402075423905d0f03031910010355482c4000011842809001c3d404103203800e00281031411200c0103200750941d9442c090341910096038114698600c03035103070000825201081c0c0010301c0c0d01c2c2e10400b80040d084007030381d013640c2c00c60350090700455542c0d4040003d03139030f140e90098443d1103002e001c481090f42c8030061000d85142d4883d803000380d03803080d007802c2d50f00d540c69045d203000d1840389000d04414004040400d0070b4030300700c1e540d000000303200d084140800c1c4051f003850340c48031292100d180c000084003c180000180b030702404403281000128001e00840441d6418428010b006a0980c0d2048080009588920302c5614039035525042084078a105200540f00f08a480c0d03002039106090703444d040241c1800d1014541500603440801d035010b1034070350480d10400b0700107206201440420319103a03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 566079694 1250 566078444 566078449
    0x901081207030807090902190f181403010b03010e0a030212192f011509060e0705210c04050a0e07080a0f140a0b12060f060d0f0506072c01090302 64
    0x3c401403d40010000c04010104020440d4401440c1401d1099400ca004100c060b038001c151441139650311080010b4441107540c0030125003800c1e42680e440420081e50b4031450700c00300b80100348803211245e0641c00d101c40404400070101e0240082c5000e5403d036040307003140c0c070b080c10058441d582d0070240c444040c0001c903109501c03800d00304010802035003034400c0c00b17513111003040c0d078003071140045c10200e035540d004010b815201203144034010550b4100a00c8040c1c80d0042081d5018002080001408800100803400c1c80e03014880002d241a600350f488150304008500b03640c280c0180c064036015501c00c550215400304540c640500c1032aa41c3e645030181d94a445580d0080c01d10401c407072006603101c211038124002a40c0c0507520568034094001000c2c410362041140c0b42c0c81640b400d4645401402c203014034050b000403510390000041e502a110100310b49025002030941041c0070b00f40340103000500010301d920800c0010f044003030702c651019201d2007141d94200c4041103503c0d540441d000e43c00400050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 566080944 1250 566079694 566079707
    0xc070603051003050a0c1404111606090c08100507030506033d020d0609050f0c0c100f0903080106080618341d0906040e0106050618090108120703 64
    0x10111007569a11183c0e41d82e502460030301c40e03c1003212030301544c68062000e40807240741011030b000c0c115814400c8030740410301c2220038814403183c0d02031018006003507414000710f074110f082455449040445055684e80d280d6845400c40340c03000020324100030105610604c40e0150501809000f006803001614507a2141d26a1840014502d516214232410600c100b541c2d400b0b1100c907100c401ca02695843e4145140c4003140c1807900aa802c052401080c4140b840c0a0942d240d8060010f001c4240d440c02031070425450829604100102c082c10320301f80b4903010302580c01c0240b10910980312036038183d0b20758609a400075001c451413504613620300b00c40304004103a00f480b55003201c405001169000d000309039080e403000303280d91155401c1d5109144a100c80d54032001c07822442c0c501e191020280e20340840052800c403005401548100c0c2ca405051000000a50082c030043c00001c0200d40e507500b40c1100e00003410310510035039100d030003004000140400041801e585000c4030450641c682101c1d507905540c203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 566082194 1250 566080944 566080951
    0x1302090103090b010f0303230f0a090b030403030c080907060f05070228031a130611090d0605090d02010207050d03020c070f23010c020d033b10050c07060305 69
    0x101a12008200003050b0443c00b1a400307030100030070074524117080d82030140c0a40440081c20034440d20281c0c280f007800b80300109070341000e036058031140d43d115203810080718560061380002030300e844008140401c140c2c0584c0300c40035103012030f20b070302c0c0d03903652031516240c0c0700d409520074180400d40007050780742c0c80352064008208441c401001c201c0f8800700f18090041000a004040005020841c011310a00c4441c0b405030704000002c1040400b94900a500000f04446004000b01102c0d1100e248141e80f003540401d807400424003a00c0030400301c06508122025000569014209003c1d60003c0060580f040c000c40760701c2c40d08000105498440e6540441c025400051a180700b0702840d200400c0c841d4440c18010010004a1901450201e07400c803010007400184072840d061040055100c4016202c000403514416090f0900781c41102c2514503040c000514404050141080113290402d5030450602e4440d482e0300c15074003045e6111003400f040d0782c144510301a0392011760100e1000c00886100340c018a50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 566083444 1250 566082194 566082197
    0xf030a0b130c170711031303170a1e0c140a1104060e0c07020d02060c150f04050d03050a1e1a0108041520070f0317070c030305180f15010603050613020901 68
    0x10400c0d11380c885c2505581204001d4054034218600c10414050b41c07240c041c0021103030760343d4145081000304000e88503c91480280380759400d4100c500d20080e0180f015000003035000740c1d048200c2c1c0302ca11100b54964075104001c03903c02076804804810741c189482803100341d81c107100c01049544c40c0c003010140c190b0050b09040740d000085000c8140141c555001515030a030540c0c001381007a95a442c4a410440342c001d052039260605141048049140083e0003080e000340ca04000400c0e40b0341e20480000f8105101d000104440c4c10018100d00c5a0b050780701011300741c0210072521002c001d010044441e41d1050750060503e03100d42d10841340300001580301325030b0344121018518548001c24002c621940003d070040c0ca00001010300e481c02e15412070803440480e460300000301c040f444d00f1003000d041440c40020240825a840340003840141c002c21412072203141010848400c00c1843c11040c0e03460072402000d1000041032000090418001c2c01217034052540101310341158442461800000d4100d00f078440e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 566084694 1250 566083444 566083457
    0x40f0504050a1d070f0b1315121505090f01060c03050a170703060305150126070f090203092107020d0203240709051203030f0403050f030a0b130c1707 66
    0x210b030943e0320540e41c20104415028001407803400070040410006070f48406c05440040001403c100310140c6110280d40d0002c8071030701d10101880d41140c500501d4618807080500d04100040c000301c0e00076040d4100d0701c04480d846820b46c0c0b031040c402c0e0013a000380300b441c000c105510b1183c1c001034000c1c0044c0000760114601111121107004820541050588070003004c83d640b41d80600030700c1401e0040010522034102c11078029490003240345019400710442d500f0b00f070882071038407182da202404400014042840032030003840d101d101850080d40305988010142c81b40341d090500c03d00d00e0711405072a5440d0102c03544d05101d401d07000c2c0503524690010032a410300070400e0045108200c100c29113440900b1883d121000e15080c2c1c0041c080f02040d4014074440c1600e40d0f007540660100108882e4000382d500305c40e0090f503c8034503043c1c0d518010708140180005021081158490035603110009000c412110592452a560480422646220344000c00121201e00414403c0c0c0c0700e440594004402e0724006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 566085944 1250 566084694 566084711
    0x2210c030f030f010f050d03091721030f0115090303050a0e0402030405010b040b030a0213020a2d02011a010f140f0d0b0a0905220f0212150c040f0504050a 68
    0x1281d1550040703035100c1c034a180721001800715500250411014010070388410202d00c0c85610041d03c00c401a109218100c2d8038820030380800c0005210344c07a00d001c0520028022620020a8210541c100f1181c5000000001e400024001820b10b00d40130401c0281d02d550005d5811030b00d0407500b9600c15141d06041c0590003c511120380c44070300c01140304138003e400000d950134001c3d00b040b0941d41e8561205104c1c0e03021002c8940580d403502e0403840e280c0c0b690200180d564850724802c0d140e88e11100f104001080360300407807020008409080c1c0304075440590080003920303200506402c4145a01150b640052080f03c003540c51036006204241040241424045c1411005600c3d000310b584000800d0070030725281c0c0b40c0489913090407511034000d002140001d21a40c40c024100710603070031090010349098804841650240802c1156a080c5035030046c1c201c1030442c12580241d940c4041d030701d4550007400e010b600000c40000265081d1020b07101404c40101d1800e03d01010000604000750411420b82d951b80000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 566087194 1250 566085944 566085967
    0x703090209070507021e1c1a040f0c0902120415111603090b0304021f050d051311030c102a06140c070b0105010302071406180c0102210c03 61
    0x141c0d8403580042e5a1980d0b101828814009403024042c01d10a800d101c4211900c16580c655900344807006800d00c040800d0310550a0216002815901900000076414140001d0081a44000c08235500a102640711541c0e2500110200e1003104114000d212482e400b150010b050700e900b120004110080c0071401c820280c0609a980e071050403a11b03d181100c103441c4080582020110300200085e58403607003036140c05c0d008196640b5030403416a050140c83c8456250b054040c0703090360310409084c40e04201e10b10303107928203070804000d02e9810742c0c1128800f10014818500010882c000c0d400241c101200303c181d118064599030207a158046451096002a50006407440c180031400c9000b5000401d18514400c1c000c20b51000181c41c52400e541c00b040351001280400b508181150b5080c41c0040e40c511050900c180305071580c400c1d0004901602051003805a40b500e141c0c56003a20328022749036034005540042e03070395140c40d8051b58890000e126984962017200c202038110391540700d082c0c1e490900315825 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 566088444 1250 566087194 566087209
    0x50307171902010b0f030705030c01050f0d0c0314060402070c1e0305060a060f120302071e051c0507090b090a020d140103030f0f2f070506070b0a1a090f07030902 71
    0x101c040050303543d200100e20a26141c1802054090140c2c05000344c14142004aa1118030300842181440341c00215240040d0511085804a8044120812080104803401009441005040c10b50808100081551460300b0300c225a491540f000d92401c83e05d1070002003660711100d131514005205401140080482c00c03c3c050648103082500780001c0103070408418104908803034000c0000c0100403049140060707000603071003003990210b89400c0402c0d071040660030440e111503003085403c406041c101c0302021415540e00c80e2203d1281081c0c4250b42e466002c02c030308455842903504d03401001100400e0f4008541e50041508101c00c0d2800f04081c1c11000c00c0f030134000000c0e4000c6000a6205c0241502d06a001c860824144038600d0b04d901659491034101d420602c20b43d01c41c0403400c1c1510750f1b82501b403204100000081c080900b0341c51f00c0c0c4650342400302c00c050f0101c403404400c4d400c00c07194540842d0702242c1a119000c000300f2045240d02c130911080d07100b00e0010066402c0c10790354160100036a03214407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 566089694 1250 566088444 566088487
    0x311030a0302041509180b1c0f1511040306051902040e0103050c030c0a0905180601090e010e0705010207150e090c0403051b1c020301110c0307020114030405030717 72
    0x224056078651030025071805268507842200c0401c03c10981c06c1c4804458030700300c0e07010054011404201000c0c4800000c1d44080010320716810001940180c1c42007040c0c034054454a140601c1d01030079844140362906050700e510310114615010100f009000041080d840700d5041911084030940084812040c2c1049900582041e0b03007080c00200100108201003041c100307080307c281c4c05408090f401d10042100d0220300d0040c1c0c200300c0d0716480040c01c3c00b030b80c0e4035010500000c00000c071006940c0d681440001010030203c0b460302942030141d03800403041c0005441d001c460042e401405224640401c4420001d809101d040801c10806030600c110364880701101e0040b02d810744a580e41d00d1851426520701001608044505900008110003d58800c0001c601c0d135000315000300e03141c08040c4000780c010301a40d50712074501e40d40440c0c01c40c60f00c880000a80b0441c0d2007070301c682a61283d441900183d6000454005146d580300700710b1140002c00c01d9005050030441408030a050141c05108044026480ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 566090944 1250 566089694 566089697
    0x50c03072a05010b09100303050409050a0b040c030c11030c031b0307060e061005010309170c032106090106020703050c04020a050c0607020a0b0105150d05072d081b03130311030a 78
    0x507103507403044e07140994070b4070703085a001440d1080c414038555010b0080c0c0203d1041143e00c0341e480d00002c0b5102d140750800214914020310801082541420140041802c140703a000001c40321146d25000079400412549030070707119001541808048105800c501d4900030000d80701d40000c0c404000081c1150003242c0401c0120809001145080b10031203401c0f0070320b907006034109414500e241c00420000c04024220400b00f201c41c9540d450305c410420300d50702c1a103200d4030f0b2003203c6002c3c0c3e120220148042c00d01415003104d9100059903103044c2242d440a90f800050889d420048400d541d40c41c0550040403410041d0034420708016a0319111814440c040b150900941c02800c0d000082001440354240548400c40d4000e6440c0c402c005005030074080c201550480315aa8404203d845001e03010109141c1c100f01146080042605490528804030b001ca441c04101100e000c55081c007004185c0c000c9a481c43c00f4054196581c1030b0302e000300d2401c0b0b541e094050010020310781c0c04032032042c0000c100c102034a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 566092194 1250 566090944 566090951
    0xc1203060603140403170402030304120804080c12061807091b0210020a020a0204020306120a120206090c4b03190b0705130905070e0112050c03072a0501 67
    0x200100a000c1d0341c0304040e420000303c0d01401308400690050003c0c10305620707122100700240e98034804a0314500c55500075801024150542100b00110240204140d41d43d400c01d03504032040040910030076850400000509812440000380c1d540c0d00c00b0720079050040d01c0403c885003999549204402ca50302d02040c4050740e10000f000c081d650340c0400940400c000090011031030421281d03402500c03024034034002440b454001021a046035141c44200a241c0201070a4400d04121f0740740510111095640010142c050140026034440317001c00c1994030404090f055440040f20719040c1010b0079401c3d050301c0008100e1301e071030030240c1c080d4800700c41c1c1840d048401c4000b8429014200741c58090b92000310300d80040c62241910014490080540d0441c00d40c2c1072194856084035011031100900b038018020031481e100400c41140ea0004006007012002e80f02e5420203a0038100aa040c0e0300308680a03040c1751300404c007103141e2500ca9040100da40300d1416145040200003c03910290700112201915182e44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 566093444 1250 566092194 566092199
    0x207080d14062d060904061205160e0f06030f0a0308150402130909020a1d0601030516020a1202030c010e060603010e06092a0414010906140915010c120306 68
    0x361107a5041141218800000741c107640780c403071240404a0040e100754540440c80d1010b51035807000d40c0c0307a90700000c0c41030000c0b0b5141e4840383c0d40d0908801040d10b00b0b108100c48141007000c2d2281e6502501d42d9800501a1581c0d00001100090310140c005909407044442c0035070180410b01502244510035510502c036410511212024044103100151107181304202c01c40200980f1103009046444a01010901c2801c41c00081c0c02504644c1c04104115000c402080400040b001040c0c0f141201762000c010030b45030030b0400f8803100e07030500c03a10b40980d025100c2c590118018a652150f0b6900c140b040340d1604140c140351070700b03586040b8181d140c26404070003400707500d1900303015410801000000901d40b920705555001d5542d00300024640b5a113655041c52041d04e4000c00d580c2c0c4401002400501611003542648181e900c002d205003003509161910214448c0201d0202c4404010000c001c0d20b16500e03201410a81e041c1c01d408054184a41000810000307007140d40212211203964900103001413 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 566094694 1250 566093444 566093471
    0x50a0b07081602060c0114091218120307050d030c09080309040504170d05041103030903070b070302011506021006060e0d020103020904060e0115080a0606080420040f0f06050628030207080d 83
    0x144081c094208e40d400c4001c0704001c0c42844002d40d034081400c0d0b15800c104501034004510200c040100d52034035808001108802d02400080031424075095950800c01d031000454112010041401031101d5500304102c2da610600e016000a90000e01508003113444407410188032a06600410a15411a440c1d80c100000e01403900d9803100f00003001c0e4041d515054400d00044e448503050300a08101000106000701450b200f58403064510107110891a021a10b4110180d43c0b00b81901c1c81c107828034200900464020311441903445207400140c62580524a03d40c010360103900504001604280e40d14000209551140c2003a4002c1107004504240042104002450104010310f03e4403618100181000750a50182c000303a071140c3c10840d1180507584285400500310564034a180d4003e0411490641103841940301c80124080c2e8003041103244d40c1e40050286901454402c3e402c02d25085040191f001d0883c20500140189842c0041c50011309984801060300800490400140d4031032820b001038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 566095944 1250 566094694 566094731
    0xc220203150621011e03030c0302030c01090b091c020d030c12090605060111030c0604020f04020706060b0301060201060f08030f090604031514091c0513051315050a0b07081602060c01 80
    0x6001007086009900311003440f1907081179180c440182080640c0c03541200b454405c0c41650804140d890080c1b10303214203420584032010381611050902e000300c400c0809131030010301108490307422a4018011010618400303900030030100d00800103010743c3d1084079800f901103115034124503114110000c2c01d401c01c2d000060070b80307000401c00e2504c1e40c001c0050306120301c0000748003030740994100c940300444240c000c045000383c0503200c00180038070305000000c520700b00202c0c003840c140c50f0f2580c02000511b64481d0504941c596900c109551504100950070205040398001c0001c20400707400300b0300d00350303076680c403400c800082410503441d10380e840250a642e040e8042e180c64221a0000041c142080c4480c2d54013080c0c2e24140c2420b090060010b2006500100360340024000d00c00140700212040c0c58080b06005044061094511000e021801007114540402504262040c444460342170100c11340c0c03451407582c0306110b000c04146d1417054490059907580d0083c1070900c03512001003000d6007503241c045c1d04c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 566097194 1250 566095944 566095949
    0xc11070803181203041413020307080106034a060a02090a060e01050d051b3c03131b06210b13150905180c22020315062101 54
    0x207100300554240e9010000400d417810b4840103811603840607441c2c4001190803502c07400d5512820b00210811002c3d90f0040740450480e68951070501440a031404a10005081d040280d41d003504282105c501100c40b91000c211044408031052103010b903800380751403512404550b011041900002c1c80c502074104100513900601440c00c02a5086074000d0002e41240a100b0340888230507030b900001105a01030750000b085584400c1c80070341c0e550140c000084035012607190304c896051414178411000040543c01c101d0a401c1481445086855640008a800140030000e5926454138002071801007409400440200f121761515105c140ca000c90649421490b880c44200861601a21044644600a601c0a017042c885800500d61800180d45140400c694100706960f518280800680700c952030f09561600340924200c6801c1c121110401107030042c140484891542c425002101c5002c2c83d401554000f99520f00e01840d005840c0080b52464110580c1240010940d44c0c0c50912444c121100c10301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 566098444 1250 566097194 566097199
    0x70b16050a050306090907050603070203040f1406160501270203063306070b010e041a01030305190215040305190203030411010f0903060905070303030e0c0a090c1107080318 76
    0x2001e40608001c0d0190200401d403a01810500000851513501401040082c1100821450f168100500002c1d1340e500280144c45404000076004181d1503003010f0380c0709111800800443c5031404052440c1215030201070100c60b150349071078a14090070600302c1080b44101640700e440200c01e11a0041501d0000050b280d5106200c1d00c20b5109000d441d1000140c01d042480b07507144040ca04510013141c0c06102e640c2c0c0241a0404900001c55808811513080740110301960200700210060950004184020710000303021440c20021407114602c0303401c980c003554405005880c00920a0710034254402c8049a0480006500007a0209008068810800e040005100a41c103500c0c1030350360001071581100c001418440703000b0140700b000b0310400b445406950b0105040c080d01c4440d14001c0d540c1c2e540c0b0b0204502003400d1162840c60028000340a140f044c60080c0601c810314038005030180249003681034441000a2002e51140c4150704010f020010448030b00110b641d00064021240002e4503101100d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 566099694 1250 566098444 566098447
    0x15060608070f0c11300c03010e06070807030506040605040e0d0305090106060206010909081b0a0b070e0105120a020904090c05030f0d080a02090a120503070308070905030318060d02070b1605 83
    0x12441d1807130510000c06043e2040b01800c00d002142c1790010b1700f0400800c1d102001d08071031030325520300410325020201c41a8001e011070340800d00c4241d1a04421600040094085800100c1a9120b40c1103280c00c03a40240001071102c2c0c4030340c08901514903407040c200d0705a0008001602840d0b0510440341d02020000081001d07509164009403110300c10300c40d01e0581c503210120b42c4203010142d4101c4d0043c00100606066044500c8a09030700ea01144400390b480d00708140001d1070190145900740101c410580d91680b501052000c2503120f1440604949203055007400134015907203c511494175054007445515a803603103000c04051130b1000c02034a20301c071604013100c13640001c3d420614a0b9004400d001001d03803168100004a07908070032aa12498400303211520101c03e021001c00240401402075071000802c0c0d8501400f951503039454800ca84d0075500420007203501e4107001501140340980101b0203460144071150078002c0e85c20449054802900083c00c1c0440f000c030309003001d004240582460b5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 566100944 1250 566099694 566099717
    0x3090a050f030d050c15100e0106090e0a150803130503070f050306061c051e010b01020d270308031e01080123041401060b0310050406030809040915060608070f 70
    0x30b0380310b0200a6a80c02401008120344172449030a20040b440ea2075680c1e00e0036150702d0030b6698051141d182d84138050100002c1c0d0004245139100701051425034904901007013071600c40c100760b00001c003078011303124406000c0c440010545d000d080c0001d12411440c00d1000c0b201034205001c2508016980d0300000d103c050381c0904001030b44021800d1540980122200c000b400400c0140700c2115802c00d000a1803409903250400360a100200030b180284803c0000b000202e0101c001039a965500703d1525001c00c3c1008030342d00004100500c45800d458903844ac1c030031043e5482e0355a510a40080e562562910303005090b50076185540790001c0e004191900c001c2c010307518010314042581200d02000100310404c4c00025042c03281c50000c0c1d90802117100020446a5511175456106400649000c1d000300c0d00200300250078903240c0105000d880c0c003c5559031034506188108802410101c0c000c64010347d400b107010072107482e81d1042d040206038640301e44000d460301480040c4243c2c0400b1f0400240000303440d90 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 566102194 1250 566100944 566100949
    0x141002010614010e0d2a05120a0b100b1c050c040f03110a1809060516121d03070f1205030f0a0f02090303070f1421090103060f0803090a050f 62
    0x140ca00b066080c20400c1450b0300400125110740714200020b041c0e5142c000c0c81d503220580100c180c02d405000c218240802940307510030020042207106000200d54442080200441c80310300c01c807900610a40c007080961079440d60309107000c3d04030555103880343c000120109203040403070040d60340c4031403a0307203045280a00300159050007100a00010b810045000d00c1c404568480d003510401409034030700e03403100300c0500754a0140500032b040c0c401c5880c5410400450300e90b0300e103011816000e14480c2c445201c03c1e030001c80c1c02d41c01411001c82c007241c2c50b04070702d03845241c3c49070078401040c41e24018140400b0034229420100e8201409041032010030404100704040702c41c01551480d00205c03888004030f90700709034004c460041d00900012a81c1400b00003680001c00c80d6140b40e4441d01441307000c1a19440380c040b5840ea8a92640d1165840740203a0f8004184144584200401d4040c80504000900a8842c4481d00402949401002d07055000080c03012942ca40750030003030000c0c0421100e446a1740d461401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 566103444 1250 566102194 566102219
    0x1404020907090f300f061a010f05090301150602371103071a04030302190f0b1008010c120f0911010e04020d0c1e020c09220506011410020106 62
    0x4c0f40d48211885404081d4001a154000d00400341c1d2044031040d50290309000780e420a0703207507003241d400f4035000c14050301402410b011000d070b00303058440034000103004c0000d540c2c035404045802d501d95640c5031050314120344010040c01410707565008240124000070040b01040030b0b1498001e540440071544d96404030321401114020303900bd00c07154001c0302000046480d140c1c054000e03001d50340080309007400605141d400b5000f01d90082c2c2c202c0ba007442d50b007141d0041040064002501091080850300c010640040046070080312121020000c599034803d820708550048985600060b401601206c00d00018007c01d000c4003803143c002c202d110303056a1400322281403c44541e060080030140300c041903803280e050307c40514440f001440aa5482c84006000303065400800207888202c5030f0310345045100041d80d0a1398580913011004603150028bd40b404900c0c0c1d10300c80c401070840080c050300041d0092024500900c0110382ea03201030b1a07680b04000356810768011110031a0b24184003007200e41c00caa41c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 566104694 1250 566103444 566103449
    0x31917061c03031d030a0905060301030c1e031406070f0f0206150409081b060c07050706030914190311010c02060c0703031104030c0f0504020304080d0b040f1404020907090f 76
    0x78000304515840c1c030b415005000f100c5010381d00003800c01400402c0140c044010040300a1694408058545544c02c2002901083c00040d110900442041c0f1a4050f100181040c10a50030032501c04142c1d0796a80d41400307401e40420103040d030030031014031518503000540c021035003442d4102403207421300c0e0840003503a4042c010004000d4542e008640c11490300c4a030b01c21540c058004601c1a0f44200190507082680b02d5030080c2d030464400c0c140040c035120418400e4a0b507503035021010701a410720b0103500301c002d405009015628074440701140b0395000c1d01007103d10142000c3c081a1040ca000905000d03044481004079903540e0303414241040d00603580400c3e0140d02c18405020241c1701c40180c02d04400600b49150749c0345401c00c0009001c01800807030252802125070b40d40c00003a507e603c6905020507804150b900404008007880010a051642d0b008008181c001510002e2001c03182103505d81518035400d01410140c1c21802400154140211541e600c8500b07401d000320042e281c9104d0109070309051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 566105944 1250 566104694 566104729
    0x50603040627061407031518060f0e0609010501030506032e020309100f02090922050105131407060c020d0f050313170d050f1b03191706 60
    0x40300115101821802da550710810a00300d20310a1031441d1800400070000203032220b001c204800c0002c0d405a20a01504c0302d0546905808050145012a01c45401140c403264400c5152610b03004996001c4400d21840140742c0c1c0e4189000728101903091110003032068105a04240c100010002603850000b01c0c50410701100c40c0061139801c08507505c820010b491450401400d00002c00d0100c0004000340f01203111104c40d400700041401d081940e8200c0c4240f64080d9082245000002e400840821034021082403446002800000f40ea42d080c2c02c4500855440c020010b0401c9ea0341e041c40450b20010340c1203080c220041c1246800d01002130071044803818020700c510010400042000036a403501004240e1040840341c5917040310461200c50042030049103446000202000114880021120412096130300d40a00c1d01d504080040354030f522460418802c04030900c040d09440b4401c0000f0400300d40c1e20600d0100c107a0401030010300300d0341c482c100c00000c40e189400f48401c1e6600c5808800300c00005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 566107194 1250 566105944 566105951
    0x30a030e152701080f0601091502160b1e13050409051009050a0215030f0a05060d0507030c030b06090906010603020a0c02090403121508060a38030709060506030406 72
    0x801a01c00c0500c00e24014510020301d800c01c503001c5403190400c040741040c0036210b50b0f4040e03540c000d60b100c200000301c50721400610202020403207140725440207a910000e0b8810307101c868801c03100c0030a400c42141d2100022050000c0c0e03412010f42054200389560070707121141854055070f03012603c4400e00b00e02500d44a05d6654280720100201046040c20000303000009010817006420400c2d110340324014140d0145004c602d81419076100041201d01c180b0301485180510340716001e20000822009100b607800c24503205140000c600200314160085200d003030340fa20f420742145031103c5044006004a8001e6080710b00b886402203002c95454192803403890016140c2d900d040c1d049890055074030019412840300305c240008d01d41d020341c05020306210044240000e41010b10703440324800040c403481d8501d8005801181d1a2040385e0000941035200680700c0c41904e101004040c4003412041010580c101c40991801075802c09005030002001c480004011442c908008641e0b940310062004015550303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 566108444 1250 566107194 566107219
    0x907080f07141005041e0509070e012c030a0602090f01020102040e010b1e03010837030e0a0801020a050d0c1713020d0605090c241603051c06060806030a030e 69
    0x401c4c01500c00800058440d6109403003568034100e0740c12002d0290074090b220301c50000e4240c50003270701203812814041e52100d440f07040c03054400d421117140c6490040a1103005229801654040090490181c0103030401a5144900b100f000b102801c16500c0740e040da401840200020009005020704541c1100455665184210b44100c25550703c3d81e8451001c520210020441d0340f4000f607204004846151005000b07400d0064054010b510220101100203030740010f00c0c0064490414902044400340500380c8240c3c85944642c00c2e41c210358090400038402041c103041e466443d026001e114252400d01610071090040004c1390000000c10042c1240c003080e140e60215154604241c002d1a0000c4040040d402e00000e05500c404c082e0b00350511504a140300d10181c0c40d07801005948401c0c00d860380b02c1c90b1500070ba54010300c02c1d003030b1074055050090911483c0e00e100c030400d030303802e4002e110000005032090130004040c1c111900504034500940c409818400069004051108c4004084981350003074003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 566109694 1250 566108444 566108447
    0x9030a14090a030f0b070c020307050f0d060903080f100f0e061207060302030109060b0309030301060c1511030105010f050a020a14013911120a03140907080f071410 72
    0x800d40346401e4201614030310020a01c598103002074138a030310820100c0038649480c0c1d13048441140f040c2001e5859042108104001d240c00d26600760008006081e0b00c280c1c0301540c50361000c031a08908180c01080b8908104910494410031003a80041051180da02113420704224540ea1a038900a445c0242c0600020601507903641141d0320304045060201c4659680751b00c0014042e4000380300c0c11142c40d04184e0040382c5407003d48141c0e0720802030400114150780c608042102c001d04043c03002c0e2441d1841c102000c0c02c06d249802064500240845040e40d294134010004204401c16044442081014440301d1049640440d01d40034003074020b003c01d02c414642d9580c55004002d0064880401c4d80012603001c203060704024070741509000070802020783c044601d02511a0039442840031041d0700402400d4091316054809000802050301d00002e41038600440c0798215102a00c50719403950000c00100940c50040012801038014207001d007500ea031030541d08030601d21103c2c21061084656a02440b08103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 566110944 1250 566109694 566109697
    0xc20040e0d17041a0a150b09032a0a090e0c010804032f01020c07030210090f0306110f04030302010e01152909100f03060e01061704050c0907050408010b0909030a14 72
    0x1c1c013882c0000c250504158500d84001e04052016000035030700004d00068008030075013501c440a102074090110314803c1c0b01c0c60800c3c0217402c0203800030226248010f42c6c164403400201c0c030141102500000f0751000c650031840c0b90010708110320381007013841010000020380c05100c0c18124000030002103401100c072031004504101c1c10a042d4420342c4086142c08100e40d0020394202100c1c001d681e00c1220510404080344c0c12550b901444881c0e000c03540b81000040c5640e8031401c40560711009050410303002024180069205500550045c6e44510704c02641d4882880b811920541003a600c6c1810703072a005440c0c03180f0b29441640c808a100750800e08080660060445001d00303001002581c00d4880301001500c410b04603000c03500002c1c03820701c020504c44001694241070310b41c5602c8200b4031104240020040300b5000300300b20350354080c40031050781c107031902030045026503040e84506807150304110070f05084500030800c1c2c501c207180a00522115410210484404036040d18146102852040b610040c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 566112194 1250 566110944 566110973
    0x4021806130c2604030207060f0c05010c0c031106060f01031a03070b03070f031a040b0d15021b0715030b010908100213050f0f060a0c20040e0d1704 65
    0x15040400e5100303943d60004480c4040200764030070103201ca1a0907502003860700110b0b401030141e80306074014402075009420f007864181345c920b003146904e0b042c4e41d42c0d942500e04200505000c01c0c404c5543c4030406401ca084003039030b4544c2c14028481441c203c40051007012101d4038a5041c0760355042c11a03c0030809500281000700c0150440322800e590308c4400300c0551044400c1d000040703071503031039050b500d1213400741c1c1b0070040300d00083d074018901c03410401005148001c1e00383d52001022500c0c02c0003c0326000b4841a8501d00c040060329109400c2c10074140d80d081c04080f11164100c0c0005000703070319403ca03045105254910300012158601401601c90015542200da01b034410440038005810302d0b034004084003030841c031654016a540d201845008e480c2c0b41800d6034001440b140c0c040d001e040540240c83c005002c1e1415000803c2980c40341ea12341062104101d410075000400701207107007020300651000d0802d040c000c03c03120594440040c1310015a2650980d8520410041001c2c4000148084c41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 566113444 1250 566112194 566112229
    0x903032a050a02030622110402070624080c0a0e0915010806040c2103030e121b01050f2733070203030c22080102120f0a020304021806 59
    0x403540850030a00d036503110b858022807082c4038100014441e4400c800a40181403408111004e600d1002d94800a111044548041c3c0056003840b1200100e8180d0003a69641c08014105000e140d00000130060b0050351500701015130340c450111555140c450701031103c211240000c080e001d9441e0000250b042c05603521210b100c0c4030b030300b0001185041c0302140c071600891044800c841525078420035100c40400780a982c1340c1e03208509092401090003030700940000d600420a881000c00d2200f03103205d15810900328036019905002050721a000244289a00182c3c21462181140350544c03220f440160801c004d01200d814100a03680400c03030410030110380c0300340ca81e2448103611500040182545440003003405000c0c5007000304039014004012a4040c42071044142d1400c064403030b6a03080424846c44501c0e101401e240000b170007010070710241c5031007840354110307020505100f0100a20500041c1034090220710400911005075111101020103a40c4140c2c1031081e42c1c0e500002401c5050031608070030307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 566114694 1250 566113444 566113517
    0x3100e09070b040f060e1f110c030f0705040509060c0304030c030306030215270f040c271d01060c02040903020a02040614010306080610292101060f090303 68
    0xc440d0200c03140c00d0113559440e642d071460300500d034080004c140344000b051a00c0900844412482c203100340c2340c0e002000d5070b01045400000044c0e021925000113012080308541220100384014680750144503006034850700200000d080002e81c0f01424440904010709000c0d0030000314003014000d800c400010741c1c00400c4901c100f6010b0300c0c150b1081d40940750042c0400d0443d00140092011007161100b2a90060440c8071038a40010902005000d0042102c042c0030740ca1409903a00c001240c5000c00850341241c402c44c50524022a070030844240da51803400707100041c40148200765000070200d2584d0303012900401c070000241416402d0400090b0040c1d04a0b007480307400b0400b562669032840c092034081e40d00b003108558230001c15440f1401541c000340d581114000130040c11a569541c007040f001c076103180e0b8003500f007051822041c81c0d0180c0240c40c072501d14406401840c02180c40003e005180905001c20007a4860900818040300f80c0001401e124500800c0c4c82c50f441204c1e1a050030100141102 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 566115944 1250 566114694 566114699
    0x7120f0c080c0c040b0303070f0213140c130608090c0607030e0303071208010b04050105030f060609060d05060a050105040503031c0b0414041104110a12021603081b03100e09070b04 79
    0x2d030b440b4521120703018020b50510703800341c0c00e609001040f81c07030045d04201c01e0303030601d110f1f40d080110190407291403c1003e51908901e04c07002141c071050354090410f02504640d01c0e100d00c11340303102d008150790104050080e02020454404004501914801800c0780c8484c0d40301e84a15042c0c4545681c2044140c041c8004a0f41c6010003866110810407600641c442c02040e030790350b41d81a4054481d0f4041c0310300051050000c1402280580303441c03500050001c1c41c203400d0042c1c3e840843c4158200010342020584c9039028421282803001d0f02401810007843c009103814180008255a8402c082100101320f10820701a08801e000358092301c20f400000380140444503070741d00030054080c0162410382c2c03200d6030781040c4000c038a4603100c3d10182c6900c001001e0704241805a068409400f500382c2e55000c0340d001c02030101c5400d80c504920075517030312030b803240c3d001400c00d682c0c0c181c4112401c04016480e00720810174825149865010f031001c880c030510170019142ea802c17400d1410702c7c0159110100040010602 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 566117194 1250 566115944 566115967
    0xa0f15080903040f0614040e0c0301090c090e040b040501060510090305120717031905310201021b010c020307060809060c070f030818060c09040e0307120f0c08 70
    0x1440818199a95212059240da250341d03500e030f102d24403070b4118002d40650100002c9024400103007040d4034040010741469078807440812a84c404941d202030b0f11500000601c8191107510541142a159107000608903013030a1844503502000b4002a0101c84128002000c1143c00d40000000e4000546038592030408484013a010b45231500045425024100c0174642a812440681d001d0b0b90300301c0c80801130b80c1400160726069900c0544141ca0503d1070540c11203622820340507150049401141d00740008600d0000459081410f004602d2181038510390307440940e9000440d1031001042d100c8480c81240b001c40140d4905048100c020340501036400c000848503001400144564400d00550300690f95011401e41144a007600c0102481000a00d0380c022a114450f4240d10021a030710146414105c191441d02e816002c41d5203d0940200045000c50b42c1004d001c0d03040c4901d80500190705080749940c1d9104580c84181c420030420071301c1e501c123031260b9106080342410a50420311196851403401e14 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 566118444 1250 566117194 566117219
    0x503091e100305060a03060903090b0301120606090506090c0c0102070515180f03070314041206051006111207030e06030f091204031113021c05011a04050a0e04020a0f 73
    0x20124401c0e07100070000307207200d4083e014480c400c1c00e0052504668904507a00c51006003484030081e420083c4131400803a03c690030000860203020740e884002c0032016180340c41010b851098100c04009414081400b040e51580c1c03406c2c607082007140742c100e61600d00c41184540240600302c0701a00b14418500d4441e000d03a50010014023411840c2010381c0d01000384504190368010081c4034841e40d0740100a0003002c40d02c1845441040c189543c00c5031300e4507980e40246040c95848030001c0c1c07030141d6a2000d024070140c1d000d603c00010080f5040140c55070384512211500d41000752403a44a021300020004c0405d842030803403142d8260002c0c17801d51282031810819145070000c82c0c20080318401c04000203014001c89050342c0131039600802c410f2840c0e1030181030001007070881c40f0079a440354082c0903503a4640c62503800d00000603900100058035614004c0000345c00385120385495040d00c03040100340b200d40c40304600c0c1d8040d10005120000d031a00c41d40b020510328040d1394018840a440c4100110f8007445100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 566119694 1250 566118444 566118499
    0x1051914221d06011502151b0f190905061e0f03011205070503120301120f170a08151503040f02030111030f0702011a010e03010f050a0204030519020a0909050309 71
    0x102d510903038a070244030b801040c18507440d00141e1f1002681c44001c818514050b50701124907020040400880d10700d44000c0d40000884100450700408c8201c0d0010042101281070794003032800304000c0d498500170498a115285c894994420110f0f0000251119502280c1c3c0c0d81900f407440903901c1d07948003550a030080304480202d400d0b000f03a5500140c10300d0002aa00700c4002450f07092440d6918107544064544c0a900c000c40741c400c1306c80748030720100701c100000211912504c20071030fa8400c03495500601c6076070001c00c50103011540d00c00078001c1c1e444540c01301c0c2c9128851a600c81d0f0b207440c0d5081407039280d9601d9000075455801c00350900260410700700034500801481010042035118500d0590a803400d02c2c0c4601d8110f00c1d07080c0b83c0007081d0b10401a044520002030000100030002d103244505581c030440c1c010122640005003001042000c100f0500e8403c003c0440e040340d501c640e4002610089540706030070100d51100c85c1c07001404824000c840c81180002d160a140c1c07844121f40748a52001c44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 566120944 1250 566119694 566119751
    0x120e06040f0212010506060405121906050a15030c06111c0207140d02131a0409060e0f0313060f170a05010e0a0b010207090e070510080105191422 64
    0x1d03943e510460b18140a246d00480009240d241041d0410091142c4030400d038000d00824455848200c014941c42d880c0050007501451011503185030040d0034000ba510110181142c1c01000d00042010030703041d10080c1d050300d0407450000d070741f5020924094548071081084d85030080e10840250a0a600002c05004075145403000c600c80c1c1102c501008440700790b4200284d0440d02810220785550910760010840071640e000103046102c1e4000840e040b1507a43e0030488140b40d680e0401c40070782c1342c100400038400b400040158a0001c011141c4441c55842d40714902c2030181c05600c900546000f20b05000c5081005080e1104902c1d000c41c00c031000e41400c1c42400030308204074020460f0074009001d0000d540c101030f0010301c260b41c50881c42100070812406240080d0080200c0890746603142c0e0400240c00180d50f9510400d94149002c1014002180e401340101c5d00035080c04114030000300720401c039214400c032840010b031202526030200e1404400c254102031447c2410306500300a80c0040802c882188 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 566122194 1250 566120944 566120959
    0x1701050109060b09241b030403150e0a0b0411040911090603010606020a0b0604020f04030b0405010b2409011205161803050a020d050304120b16020a12120e06040f02 72
    0x1164840012071160f4044d0707540051000c4419119040307800c0160a82038589000145031041c14828044008000c45ea41c0001390400602002070054072210210320304000d1000300095200012895a505161800200007281ea80c0004017448899942c40105d14006042400300f0032039403400e80c02403200702a005115403515804100e03282014030488081d5103840d0010842c4920b25103c0c0c000700c90004082e1688203400304200b01914164801070401144180c10903429800c141c5009400d40703007200d11043c0285007105030081d00ca28105002407010b100f0030703036403540d4a41880040350a02030740500c3e405424104420b200c0603030a040711050303848000796541201e94400c40c00c2068944081d10024007960300903160740380903140901000d00d0291042c0300701c9c0e00e400d50312000c050102c0310000c802c2e0348058402040002c20711220f10361544000503413019008062156550491911072151250100482c0645c2c101d900c5000350321000710444081c040f543e507860180b800c201e0100c00c01d2812401140d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 566123444 1250 566122194 566122199
    0x303140a020444010f060f052e050306190303020607020d080c090f270414030910030213050d120201060e0f0604110d1404060e030a0c020415170105010906 68
    0x11561034003068060002c0c503c0f1588030052400f10b511501407500402e079542c8000d0030b40034401c9407292030020030701c520403002c026182c68100401031800c82c121000c040c036204030180c8400c00781d40d04011440407a06200f40c4907111800425611165500620b0782032080801c04070905400007500351184101c0d908890034040b14200440b4402c000b5604041c007103c040c4014030991800700c80d0105000c001500242d10b1070102a0201404140b00e0300340c140508001c8140720600c24140101020894072a00070761034208220041034812105000e190205075001c9014540160341caa12040240b000806078020700e8081d08068801c80d83d00d6508401543c6043c4c8006044803940c1c10750341c8100451071a2410710303503c2c04103100141204620300051518200841c41000d4420f1050065843c6888140103c1749400c1c640310b000c036501107441e40555841032181301c10140d840802501c1d455415100403802c00d10701000300240300442d4020103045c009041040c0034003601540068103e42440c28140213581d07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 566124694 1250 566123444 566123489
    0x604020a060c0b01050d030c080406050c011b080f07050c031b010b040c0c0f020a0e070305040611130b180409050303040507050a1203030e0f0f010207020f040b060403020d0303140a0204 81
    0x1c1c01001c009107240300c1032004002c04d20b0700c1b10000001e603020703081008140c82942d542d47c5642e8002e411000c0803820110306a98031f034000f44110140905081d601c45128424560050529900148010410b07603c0e4000102224400c80640b20490241e50480b521921400c2401406041c5041011402d61030004080c4291030705005268048926844d4660040515144c0c1714080030044800c0ea00b200a0120008680d03141180300c6203d000280d8001a003400c2c03034500700c000e0300d40d003090126040c0010702c004001849510441403c6500c0c94011790303515045100c2c4810208440c42604d90320a20b480705401c148000070000314801d6108000b030b26110f5441b20304200d4034910038020805c18004426050b030019000b940b1240d20341c50044100e401e20020344224500c3c1120341d003c000e040b6500451140c1c00c6040045480c5040d1004403814427510400501082c1e0f240141c0c80068890128082e0600a25000f41d00c03103583c100c840b040201031468a1002c21002c2d5105100d5255101c8102030a0021380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 566125944 1250 566124694 566124707
    0xc0c07180225081b0325050d090e0601120f0507020a0b0901020304081207030e010c020f0f07081b010c3503070804031826010b060f0d0203041505090604020a06 70
    0xb55002c40d0f41400c002d400e00314071324115401d0344280e000d803004104d50b01c04107013002d1180c4691071103448038115004072860b21a0400c0420b40741101130000842040c4040284416616401107081c030301810700b60740d1841c80002a2801031080c010301c500e005c0503c458182d010407048100c500038003080c0c0c001e855917031000f4200e200485010f010a0420b210b10003079074070364044c42500301440740380104d00c00c940345901d5402c403850100c8440160703114001c1d91546a02c10300c4640c40480b07180003d032a44501e0304005640b602204102c032a1905000300760384001342c3c0600c070303090f10403a04600c580c159041c0c1100040e80c00f03400b062280e00c24142d41e140c20000800400101c4e4403924280c3d0b1401d4154460741d0307050724440b010500c070030008407200401142020220311104a0441120600c0307030200205a200790031215100c107040d0003048108601d03039800340304604a44603003040c100c0042e5a03a0b42d6003484800725030642e800b480c5071801c007428003c00d107400240d601d0155000b210b2600d10140c4d45c00e019160f0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 566127194 1250 566125944 566126017
    0xd0c020c030d0f05030c091002012403020109030206070501090c0e190605030c1318061a0405091c140a180503032d0f1b01110306090c0c071802 63
    0x250440c1000590b06200b00055030301b1840000c0300904021a140006081240f4001002c0041c2c2d950200c01f611258051507007804078407140788040e8500c0c21600024140741d01404080e006400001d862003c205c400d50010701450f40041404c02d010fa2a412a86603004050300c1d20903009071780b515032045c1010700340701d40750440300028002e002c400d40200911101d52603c0741c002102603924040d594044138040b8400d0f1a65102d2040092074402171945580706c1c00c000003950303004610f40340410000500000d1060118a2b0403801100301c02407069088508121340700502030450030204103001c074a038104441a10006012044a43d919283e00900d40da034080d4510740d075070f252021206180c120104200c030754038000001600c0c6241090b070315100a41c0742d0001d02000146d1214240794080b070a02803152100000b0300d2206c0c0b9196042200c000340448401400008013202e0000744140900800c00881c401000010350400d0108504806a402904184009002d400c103140100c2c5503030441c2c0a40480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 566128444 1250 566127194 566127197
    0xf1a031026120a08010b0304020a0611100c0e12010519020f0702041401030c0b0f09040c180603020a1b0f0605271e030903060412140d0c020c030d 64
    0x8031441c014035070181e180c8024080704200160001c000c61400140481e0300e14040302c9001d90b980b00300224000b042040141d11640361854240309010040e42c40354050002c0314007d2071310138102010300c61418207100400c545a40d04900d4943c18068254004503103581c081c00c00c0b200c504844141599160a80c1c23411601490056650320a050492070070394050040501c0c10b20742c2909000441e0b010038119007900880d40b16042c0e03035100400420014108220241c802103a1050034243c0c03000211119018080580c0e00c5592600718002603180b049804140b5204080c5230b12b407940780d403103001600940c003d8a200002803c8801d40c4590100c0c1c5660411032541d020102c084441513540b5264020700c4080d29100181e4400541502044d40c0f0311046e41507030884d10042c2468103003d05a641d8100184442d80c80d8070342003440542c0455401203055580150403203a41c02542507a00021107038014400c00c000380030007000c01c070311049020540c09810082c0032174003140c0e03110f102c4034200350391503402152100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 566129694 1250 566128444 566128471
    0x3070f030810030b0a06030c060f0f050f0702090f240607060518060a020415080c03040b0c041806050a140a030305090103091a060a0b030c0706091403040f1a03 70
    0x180c400c26840780e02c00c02042c040d814060f00c82d95180341c1c04209403800c4c11001d49806c41441846030349410140181806d0820740c003000f00348440a450701140301a00c1051000204941001c0c12510040f40c1c840c50307000304203000e5407609090003d000c40081e5511103c003010088980400d098001d90000300050003011541411b402d0f6480f40081c000007012a6654295009014051030b0100b210b0340c040c07280d0100c003580729820449081158624a40d0722010080d003001445048190f4108498102d6040581111035030380e0600c40034920720032a405508820540141580700240710f80c061416100d0880304900381c42d5603026101a544d06034404954440b000000800010340150002e0240c031f481814041101d12080d100c0112130415031a26511340c1c0c01500801c03807649010183d07540070f801c092500a0660801420301f40306801070340c000030071080e80c0e505a01c2c1400701e0703c940200b074000c031a000c4903602d548824090494801520507015040e05400d06d104c0040e12800c1520b200c4c000c0700741d054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 566130944 1250 566129694 566129723
    0x9010f0b030705012007030f030c1a070e13061e0e0f0f060111010b1005030712050106090b0a0207030c03060c09090504020f100c02030607021e010b060d0c141801030506030307 77
    0xe10010445089405507100321040040098221071080d01d00f1402620ad41d9404000c41c10b01026210001850090f1101d00c1000c004080e900403000040c0e400c8165076240440140c81001d00041c41c0a07080921603c02032200090640580c84041d000d441c5801050b42d410b88602003081038449003902c0340800c001c2a0350002c0c1c02944180d80100c0032840c080004160b1a02d4007002c18617000c3c0340340391074000174400020041da0f288c1000600e9003003152410f0420441d894035a00805035020f44c05030f0101c00b280020103175100f030302c20031020000e5604102a845115075038904800103102080680020482030301c0001441d41e09442028412900a0000d1050301c0c4c03048108a030381d20201000e030092000d0145420090b032402c0141c00d01c201c4030b503001414002440030404103404065482c1d40c096070b06040400782252100006e64800c2d640e1810b000c642c0d05200131084c0d0302001c1401c000818140040b46801812815090645020400b80c0b0200916102c01003403544038031501d4405444480140c462 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 566132194 1250 566130944 566130977
    0x203060105091f030b041a19020f040b0f0702280317120a14090a030504150905032b1409010f02160807140a081005090a020909010f0b03070501 63
    0x290340c071500f04502480c0000303240c000e102c1c0742c100300c0d001940c00f101148200010003101c500c4180324038540d48245a0035142907080111040403a40388206c5d8030303402141c24010040c19a0959001c0e129104d000343d06c40e480600c406071340340c10054090f07102d0882ca400740112031900c1d1150444240380700c0c0c030110b042c42c21522034110700c8048800c10703401460704003e024003000c80c0500741d0b4094100d0307680102d241482d81c03041212010010303102100329040039490400090300b200c22582280d040c40f1041041c005c1410b0159090070035940850b4150095841c40c040516001184261940843e1111020750030015800c5a00e084107c990302e10b1007004000e88003c0790b008140030458a5610710444013440c03104100c8101407125603220400c180e002c00d0060000500800c51002e2821090700d07440382080c40d16030703115601d880d9510300e58001c50741c51002c103030140401e005441c00c00740c01804401c80d605044035458000c080900342c000c0101d142c200342e080316140100741b210450740b0507911540e0084048c100b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 566133444 1250 566132194 566132209
    0x1080304170a020d0f0219060e010305090a02090906100b030610050711130207030e040e0303041e0b0412020d03090b07031d01090515071115062d100206040203060105 73
    0x210005103114615030b42005a45060b04e40c4490340c0305503001c60000f040d500c140290b05040d10140b010182c4203174020310550707511814810300c68100f4a00405c0f50780326a19281d041018804020b90801e04a50410811010024006000c0c2c41c040c00a442038035500e00360007040d070000791046a8442c50401024505038070803409030203514050710352130303400c04c0c07600c40050460003503045142c03405034011a801c418160840c180070303041c88003504c044c00401c14858070247c07240b0000300300810140342c030f0407002c5c0201102c018401c48264040683c1d071480c2071508103407403007110140401300140325920200d00014424001d40f2040d0740d0116104125031180c1a0680280064151040142090140c0107880083c02d004000d00280200044c25150b0341c02c42c03041040900041c201c0c41813040f44464180304120004002403540d0750100e410f070135912403600003071a00d480e400510181081c11660603404503540c2603003002000e01240c112100c16809001681c403070804450295141d0000001041107082001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 566134694 1250 566133444 566133479
    0x203100203040209100b0406030f0216202205091e0a0209070e090a0f09080d090b01050105040b070209070e030d0905031c0215071e021506060c030313020103020d06030311100501080304 81
    0x240541401c084444044450185800c1035901c18603401c0dc0040340102c1d0303619140b0669040d2028010540765452107483c0c0100c2403400d054241e900c0e0b00241d000070b0b062280c5880910525000380003800001c4d0060b5503802030790301c180c0c42201318001141d00d140c001e2240800c400c9001e00340640a60780c00e89410b004019064807085a81d8944420f880000c107441c0003000c002180000000d0840300504101a024805030851414000104024000c0302159421b0395039290741181e4580c1103a84220080f1480e140e01104582c140c45a0b50041c0701d03658000000e0002c0d01c4056085a4100300b01c000029480300c407003a801030258200001152030031001c2025907901580b9810504100714031b26003940180412042d0410060300714440800c0d007000110780560304007204950040c1840801c0305804c1c1c503884040c200e602c81c0c07925880c0c0d09007164000d4064070203401010f00c0c104000c40c6d490801078000c4084480d82010760180485164881c03055101e01c3d03060710b13071080046003000d003480b20400c4c01c2ea0085 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 566135944 1250 566134694 566134721
    0x702030a030c061b0c03110c06070606030b0c0c0a140309130c020c03030906070605100e010f0e07170f04022b060e0a0b07080a0f110d0e060c0d180203100203040209100b040603 77
    0x408d901002a16842c1c0200720313062244130002102071445c11310292995001c2c0c00050004d20030440d4102c000d0002507180b8480e60440f06541071005809085c900e1407180d10031311a081850402c0c0c003c0c0000a030350118108040680035641c43c2c2440100709500e070b03c100407025a000030148010300c0410140d90003190302c4a4500e0003001e801d070f103174100c10080020036400300041070070b6007406118102528080c20303009000c90500981300c0604001e03007042154014600081800150001002c0d90368541c0d141c02141c0d01000350300403204000900401800d0325040503128103040c240140b004010008030100c2e000d4010742c42c0b50040c0c03140c0e03508840d0034401421010390b170790702c030301c0c3c4a02512860310402c661032603440c030130702c1e0b071101c5003070a034016140d0700c2d1009060398020384200200006a00110b03281c1c1c50813521700088000c00b40c0031015420040003006034062007403201c02c017690b49a80e4021802640200d425198030340d521072115910342940c0c007513080740c0d840501c03080086900a800c42c98032121107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 566137194 1250 566135944 566135953
    0x110d0f0605060c0706021203010308030c0c0109060e061605090906061e030f06100810060509010203071b0e0f0c070f020a08010c02211614030702030a030c061b0c0311 73
    0x41d8000282d0b1500f00c0b0a05043e641c0201c00104141a01040000c951403c0d4541440c115171440d140e100d207500005280780310820700010340340c0d00b1280c2940840c103610340c414000c0010f011420440da40d154030855000c0e500d0030000344207040050080c01603841e040d41c000c110b1907032036075440300b88030321030300104400c015101c04060b044081044003c0950300c101c0b13450005030903078584501000343c3d82414040300710a000d6488240301d05c142c0101c144009958150400030303950070a0a00403441c5100d8040301600d00c102440c11122071001c04030021040300d031003c0f04000b240d01d13091040c0b101600d05503a00801494100000c500143e801c041080159000402441c0c0f282e0ba80c20081c0d0949282c812400c005800840c0ca1041c100140506110180726403481070341041503c17a007201444030410000b070600915180e10907548401007044689056000c0d060310401d41c05850040e1044400100c1124bc0034101005200f800020500c03200d000c04242e030702d10032480b1864a091f500a92112200d0400e40078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 566138444 1250 566137194 566137199
    0x12020c0a06242c0702030702011d0a0b0315060c0a060b010903060e0c011701051809032a010b090717040c08010204140a090c200f0601031113110d0f06 66
    0x307a014825000300b00740c6056103c0b0310031503291601d10300040046105800c1c1c1d4041403240e0303e42e00006540050386e080c00c00400d60100f01620400102c001596190302110701d80c004078202e1a850701842c0917406400d45517000030b10781340c20042c0600418291010941c0250421008640c903034011051066041c1041400e4988984800f4107403924210f0310b03802c0d139108042800c15540c0c411442502c40e14602084125541003400141c185100c6405803005645000007203004d4003014021140c0d100445d000c241e5030f242141c00c0002515204081406030b6510304211002e8605110f0042072280103290382c0c22041110540b0101828440174005451403a9a2a00440c101d1003d1004002800059805000202e4501c08005400240390000ca1400d401c200782ca0100c56007110035082c10080710400c0340c05104403083c01911f4041000c0071501c0c0c1348540c000000a11040d2159440000002d481c0020641d404c0c4c15110f0580e002c1440c10f05200c401000701c00a0b900c2c036644003100c20201e42001040c21035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 566139694 1250 566138444 566138501
    0x30705120a0e061306080a140a0b0f100906120c020c12010b09040605150d020a0e1e1905010b1201230d08030906090a030c02010c0c081c12020c0a06 65
    0xc0144d044d0404902400206205180d00084000c0d0700c440080c5081c8502c05100c0400300300f100020780b0144255480f0486414159500380f0320382d9080380058003084540b9880140140b501d0681d10034400407581cad00d01101d482c0640d0340121003401c002500100800c03840340e010b00c40031aa10a12410a075561041c032a20781e41c1c0c0340343c2005d02641c0205070200d07003410090550118041c840074030610504282146c14010f89501c86d085040700d02c449040d42c01c3d95500c912a2144c400c0c0e8102080c2110a040200f0501440c3c00c41e42020208681c001007003141c0c7ca9107010350252148440c0c04c8105181c80004002c2d0039800b806040c2005002d07005007408160300c6000c00d00d148030710841244c51050110421020100400c201940018110020700d145040c5440140070024039038400b80c10081c9040d030400900031003421000c000c0c0300130004c8504810b0b2030b9013600551010701925a002805450990245180a0081e9840c00c28028050022800d180e510709000749050400c82d1401c1c03c9070f02c460074091 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 566140944 1250 566139694 566139697
    0x180913050d020d0207080313030b04020d15020304060c03141308040807060206010302030d020a20030a0206040321030501082a03070b0a09090204182f130503030705120a0e06 76
    0x488403074000f001514068500a420a82d540e04604119801408200514001c00a1413804c4980004501c1e19907102c0d4008038640c0c0c1021000030303004000d14440b011440303c641e030003184118041c02c420080e00c400420120217070384204103080f00d5100c103c0c0218008407014500501c0080c8600b1800785403d079100c540320305088040d84140090f800c90300c010010749c10213000103030b03e85000341702600106180d5507071034a0301404650080f42d400b0640c0c1038800203881c00c1203c010043c0e0010310302074840d80c0d42c2c41c20310350a511016000041c81c0701681039102050190141505030340031034004d002a608480b01000040070001d02c2c0701c9107221020b82c0e25929890500c40d00b0b000e0071030801e58030356a42800e10b02600012103584604682403040004200d0301d000c104125090400144010601503058483c518418840c403d03000d000103921a480b10a4240c0f62000b400700c944a02c8520002d95550010140c480c050100c0c0070300b80350040d01d1003000c904805001441074012a0603c61b4243c00d120011880c02d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 566142194 1250 566140944 566140963
    0x90b09061c2306090303041a090c03120403030e09071d03010f060b12090d0906050a1101050c0c0706020c060d0b12030d051510120506031e011401080318091305 70
    0x3020819002d02c03100307000d22250758021892030095146003802e035281d400464550140c1c0303d484280001003610f903401482501b044003401012030f44c5003540c2c4401c03e0400d51041c031003100403944c80c00003001c00d130600c0007190b0310582d442d032156070f00e62080002c18061070308182603540c0d042d56120f503444c0c5071101030b21502e000713000941c3c503441d103998140046000f44040505184020340c82801d600c180c542d4084000c40954034079203043e03a21003141d08010744800090380c14003441c5500b481d04001a009510b005850411000c6088801d066511041641c403186540b0005030081010816000d164019130441c00c0d0804014000c0d00c480c2044071000c60030758003c001e100100325101c034103010f016041040c82101c100700482d0503d91005101da07010300040303c424a523078084e54891000800b41e603414046032403107180c1c40c802c0f00d01c003811f01c000303da0080c1000120041e1000c034180000c203148a0000607a400c00f140c161507220b28610074010050007981c0200310030030310040700740200e000443c2071204001c0e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 566143444 1250 566142194 566142233
    0xf0b090a0504031737050a0b010207060f0801120f02030a0308060406140904061104090c05070b01080106030f11210a060b0f10200d0507030306090b09061c 68
    0x151420203240040107a102c401203403c1c05182082031180d454400386206264001c45c00c401a030210f5003400c80841350003062444449640341030104121402c064100c0d1000100982c26582200e442c0c10b0151816000e00e207284000a50480044c04501500c21850010a00405d1040d80303440d09640068901003d00004400040e8440180012410316016140c0a404a44020b40d100341007000440c02e481c0000700041e1030a9250303841002c6940544013100d0180c071640303000b0f100401000b0b001a2669014000845110410384000654000d040c8070b241c00f40c03540084100d4580c1c0d100e032115502e041c40881660f5104144003202d4075944800c440071215484c048002d4446080c00382022001c55501401c954000c0400c1203c210040d07a6552024001c94403606100e401c040d40c07900b41c10600341060980042511034400b46001c669005005422070324801d94007030014a0302c4030441c4042e10361840c3c3e8542c00646401c0852032a00c4c11001c038040040c441c0303c00c119103500b035413104010b082d0100182c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 566144694 1250 566143444 566143451
    0x111030f07020307090e210f1c14011e08060f010308130b0703032a0e06070f0b180d0306060c0308150a031511091e0a08070807060e0d020102060103060f0b090a 70
    0x5c810702c00b000400a00007801c000098141001844442100d1090324981c260700c070394491860b0f01e270315040c3c0c7c40030840300b480b0400d042082d038481d114000c44002c451681c0080d201c06520000d1300c3e0700005865803060f1410400c80e03505e40d20f50356885d040781d0001140d5000c00b040032600425038203085070107020114081c0d94041519600100c0c1d0300b007440360f01e400308650710030030300d03030510f01d45410212240000c5801e03a4216038844042c00d2660840018000080003a101079051180c1d4800c03a2240c038110300b6211003624080c240c00c0780c040c0c00f200e0451040c0c5010031003a5140c280841d02400413541d1001662810b200f40314011800500c2144031a0402c481e500007440c030043e10a88180700303644940070061211840d00325504001881035881c045010501e00403003280c40090b4030740323a084c0c0000700000e500721018652100305482d260402030081200151039401910400e00d002621018465010307000383c00140d007140c0b0f9590142c050340044c50111070b1140002d40da9600c1e04440303039200c0c495280300003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 566145944 1250 566144694 566144713
    0x3061210020403110d0b0c0f070f05030d0501050a0e0c0a12152907080c0102040b0a090509060604120b0c160501060f05010c120807030f180507050111030f07020307090e 74
    0x34401342038040b0050248040b0b010440c001444542e1980d0071000e41a42e250302d802d403046c0300e640c0e244a03120303004080709003104000e420040000701419003c15105000d02030341c0e8984041c020540c0360f0f8407402d000381c00000c000c40c492420820003001d61380e0f0701d807030b00c0c0100040c1e0500007020740f95840c0c040700d40c800c0f00c0181000220126007810300d00c1c0101c108a01d204c1000023810140600440c0b10180c94002c3c001070701e00308007009604640c0100b40300c083c41a1a01c0500c44054140b514600c07139035000301178110004000745880070889007034800021079000458400e4581e0182c00f81c0c0184802207400c0204250f40c0d4002d4200c00039002144100000305030503050590800403a0507640c401d5041c05141c19015002680b102c1e040003541185280540711a41d50810440140061702c5040401e9445c051011245040300e44188044074058400ca88401ea60384004603210091a0080002c40d04240040b40d05a050300c002840310b1030005084890240d1680d150404543c00c0000607602540124400e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 566147194 1250 566145944 566145953
    0x201021e1b0309220f18050c0321031018060305120408072309011d07020606010e1512160f02070b0409022503091419030803061210020403 61
    0x201a03007410a005903051034403030004513204400704526080000c041c0b0402c2c0080c001e445c1d106038868400f0781000e10021240d03202c0c080b10600f4400069403a80517142d58841c16040c0029680c41d6809429000041002e00f120003410941019011000420000d600001c2d00c5903544258600d0710710101001640c01d145140441c500040c011810040020900082000c1800412040211410f40c0b8004401d0041c070105040003640b1a01e405500c410340f180049000c12190130301c50802420802803101d00c5c1c6540e40c00b6a652a4101d9030350b8000703000c044035905103003840c0b164001c01c0c1c1e502c140b00c41d04108000440145004003124114003d080b4201118101a44408a22000350550014200142c00c11510460500c11030080104040d0009801c05e101c405644941d81440d054211580f91000c80380f8009000c15003a101380d4480a80f85070b640b4800e0310741100000d1340d0105041940342e1103880c1d91b076401c0294100803d0668003401249151902100600c0a8110f60442c200c0050f41e590440c0341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 566148444 1250 566147194 566147227
    0x318130c1d0405040f2402040609171b06090a0801050f040506130305070b13080703034b0b060301030f03020d03092402130902041805040201050304060c0201021e 71
    0x640602c91030074241440080f4813120301074a042030b000203103c1034031031101c4400c00900c0a0602000c00319440040e001035444d501080041c281c507a00c0e070028500205a5540c42c0d60703004401608411140750090012251901d000202001d0390050f0032954035a69809034507007143d20803030301c12904e08400410041000002d02c21141d005000b140303c0402c80c05244c800402c503004a22008141225000100c7c00e80341000b94018240c0d0341c4618195a260308514000700601900c0d0400300c4525101c40395105030000034440101c130b900210f03942e54031210007440d05040f012204486848603075502e003c0300c3c0103603d034035009601850194502c20b50000b00740c5002440c080d05c1c13458240c1010700d02002e0000181540100036021400d10312420012445400c002000744a840100a00801c00a00028410102c0c2c1c000c1c0080b2040c0c134118085c0050700030408003e65104450090001d5010000500066070507441140c2d048250302c001818640709440c10003510b90b035800c0700ca0f000140840c00c01c201c10759414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 566149694 1250 566148444 566148497
    0xa0b07210f0c170406080f0112031d030a120507060615120203150d0c06020f01090b0601030504050c0307171c050403020d060b0402040b0405130c0f0f0201090b16021b01020318130c 79
    0x800c507600c020f01d151802090300104403141d40c8020be585540e8000c6940821650704416002003c01050490300d4070003400c10340c0203400494242d410450b0005c2e18810b0480d180c2c8103030380e050315070524035010703c0098402540020482c81098600d00000b481c0f5446292421072518801d0100b50030003410600d02900c5e1410101108035507a040c014200c00003890254882e03008002800c01044a0321103150003420040ca0300440c9070180b1940800045040350102d01025400c0c0c0c036010740d405601c50702d0090000000b030500000210b0310410081005082c01e07501088071500491001404085c104002401d82e401644902610200810280107510301543c05140700301c2c6a4030b0401c0306801c2a2070140031505954020341c00d02034124001c10403a4001c0d040390304d456501c01c280d48540c1c41c0120004082c0208202c1c03000051141404850b0748035041440c600c82c00c50140c00850a00080e046076041100100b011141c00200c4e11810915103240c43c09840c0042c1d000751615103030400e00142942c80c444812 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 566150944 1250 566149694 566149709
    0xc09090e031309110d0c110d0f0f09030b15130c020307060c050c0d030c14160c06050f1c06030b101404020f0301030809030c0a0b07210f0c170406080f01 67
    0x2504c42080b102800e0868203200c2d40928081090841071300180c4107171941c14040143c900841090000da00c0e0b00102d003000b0300803d074442d07404ca00701410080303410085030301004090810402c0485e182c945113040510100b40c0044c508900000b8140709413040d00c1405d44d03600301590011030381d601045107074014200004200e00e099400e043c82040f04594404800c8429424541d5039a04021000e00c078210122030701c0b10040350551703165103030420100b0300b10f40a50f0a5400488003800420f085209404498102500e150314904007001e8501d00150140c02080501d1401e9031f03001c00100207030141c2003440c82070300000c1007206464617101101a0345000340800074852441040b035403845e503000030180c90560b60400401600d82641d040424034000c001640ca07680680030217800224998007800818141d44140c500502d0a0f80030040012800e0302443c440f0041703441c40980b1540c003031048000800b4a801030042000107251f6003000c809030b80c010f8200800060384170040044542640c54451b00500c1070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 566152194 1250 566150944 566150951
    0x140d18050d1d0f0f01050d060f08011103040b0f070203040e01030303140919031d030f100b040c0c1b030b13021e1018050901170606030f0607030c09090e031309 70
    0x5540005041400451031284564245180d0b000130381d20543c1a00c81c0c2d1600000208070540d15a0941d0481e40c00511900d48e0700d600300903d4510001c3c83c802075901580c2d00025031051919290712130381000e54001c00c02c10440c4418400000c40c0d00c140c03030403540254029100054910141e43e00e56046e03440c001d1002645511148911000b4035445601d801c0040e018039014403d440b1a000000450440f405442d43c14420b90700c04070b2043c0400706241c000c031100e10904001450b107205c14002a80d079400034142c00b144d40d41100c14081041c80010a03804014804400c070001d840c6d0f5602c10200303205903036980b02c0700202d9107a4011414080203030b1a0303c080d0480088820708099000480fa03c4581040008000745051104410805000d640c2c014140080c42013400d580c4401e40e01d0400025003680c00c020344139440110307500341004196440c0000030000a480584d0342e9560542c00740c00600800707820081205400604c0d00c14a218010303441032a240650354440310b481c010b19481c0500e4000c2000d2625 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 566153444 1250 566152194 566152247
    0xb0d03021209040b030d091d0105090c030a14090607141903020f04120b251403101a0301050126040213111b01050108030703140d18050d 60
    0x100003510341c0c40c554a44508a5444061502203000380c094403181c070303800d407144076050904039030421007070415549020500144050000d0701c4050086003842119001426200400d200b184031034021684044c2c0c6441c0400e41043c03084415100310070071901e580054000d54240044141e015996024500d8550300c40707418000b05c0440b200c2607124000303040040c140c1c00160041046109420f0f40c00900b0100140c0c5011221400c144010150440d207131780080785020680003503100c000d8030b11500014a95500001c030a203001d0501c0850b40040e14188038409540c8001a0304055440100ca5250314110a2516940f40c80f0001d04580d68690b0306408003030014008590015868058a41c415011507190007240c0c12040c00d00020f0503071010500803440000307600840952410280040b0401c43c000802ca2680d0340d00301140c4034007a0040c01000140104c1c0c5c100800d0052501804100e000c07842e00040c4240e043d10700c44a0381c2d070542c80484458000007ca801e140da00000340c2c5201d052007110b180c01124 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 566154694 1250 566153444 566153447
    0x705041a0405040c0b03041a100b07030e13020c150a0207020102190f210f02160e06040605042c0111030f091204090b0a081504021e13060302040b0d03 66
    0x4503404045008075592400034003804803840c0b514004100c2c071a0219034a04050404d4462890a070301e44659010302c0d08045141813121300920002c6511b030318a07140c103000c0165811078051590440d0194464103844954080501901c0141074084450300100643c40b0701a03550b03a4041c10040101000605c1030004002513600411401c201503a410200b61040160349844c0c401c09113054000f4040040c40c1003a000400d405202c928466aa04d07164100d0200940d4000ca0b641c45410040c00e214a20200040003103180b00d108054000b40028404079080d6100c2002c80d0441f0003078508581e54110035151081880468880c01004245801c0244608899202450007520001e040c0034414803a071400070320358000600c268945115540280c42d0365541c2c820f02d031005042080140c510031034641c0c00000d0b000000080c4565034091401554000d65142d0b02003041c030100209203c0c806101ca90f00c06582d03562f4030842d41086003810000000c640c0d0440c010f200456800c40c040c24040c0300c40c5c00c40f11000c01e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 566155944 1250 566154694 566154731
    0xf021902010b0411072405070f0206090708120705071503020304170a02072c1603060801020c280b191d06190b0d0b070e010207151b0b1503070504 64
    0x413078120030403910300344143d0002d40c500c9101c0406c8102c020700d40700c288070700e590b80b10072844c0080046500b10703842070304c40850b4152903480030703c500c0d0f07080c0c5d000c085101d54030b84900028100c03107405402643c2c03150303079503000d880c25a0b5150311540c000640d00000f0001000300c1c0b0491780c540004014151421f203002140003070350b10307400360240d91000051070328900c00500c000c03122040300445003101d151413170034640c960f002032903400d07280000884e0030150085500c02c814402e84190034000300080c03080d0040c500850101119081505103109003506030b400108981544580c06900210b219501c0c00e05000d4023082120412400d402d15452010900c005440c400103665810140170400000132100300b1084100a043e000c001540080c0d807014948184082c40107021303c9000c85494031812001290012a2220924041e5902e018000846112010701c1890002200d80d41e680115032081816244c5110040d0b08070341020341c9004d4614810306a04003800100d00070320041d03400f4496103400d143c840192 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 566157194 1250 566155944 566155957
    0x71806050f070203031c0c110a080f0c070e04030f0e100305060f0301090b0411040917070c0f0b0702030c011404120c031205181917010f021902010b0411 67
    0x100030012a080400141150884101c00d90003001ca07582c03100c408081c038403070401385544844564504030401c0c0f400c5000f14940304c01c805c41c1c400a0325840c000b03070b923610703090350400c8a889069071028408403422400030010207002e801c0b40503840d21705140510700101411706840c0030804105421200c0000741d2a007541043d4480e00301d05000c5020303540c4002180300303081e0702e504595240d0700b0400800d09101110110a00983c05001d006400f601e0000621040c0c1d000d004009000c42030240e80403c0118058019020151127442c1c0d003000343d0355039890f0400b5800541c0000241000000d1450304510703042000203c5454203081c4181c090504040340441402284100150b5002c91042081001012544038000c0d503840048840d012103c1000100544c0041c503840250000801040300c081c600083c44005960000e04c19880050034200344542d00c00b0f0320034296000d592100486101c412150014004c045501d00b8043c0d002e00c0740030402400c1d144040e42c560b000784d190580e0040103e11510031500c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 566158444 1250 566157194 566157197
    0x180b090a0507061e0f0c051212060603040203060c0d020412080405040509010b0307060e01030908040603050f01060207140d062a090504180308060612090c121c1103070f06060e071806 80
    0x5160070101c0035100c20f41210b01c000c2c00780c00746246095110003400040c2041c0219410307803027156070368081440640d10003620081e51681c88140086c0c0074a403100001e04042c04007100c058140b03a520741002c0007214401008071200d520100703003800b141c2031038800c0c16442031a100003131127408001d0010a40325182ca0083c2d0b0100060030454603056406a04030041e6030303030b0000c401965150340300d40c024020503042d20707809201c08031540000390041c800910101959444507e042c504042036040044c0f03c7c4541c0700442e07685441d05403101560b40101c40081e03404921a0004c40d0b96807403040004c000103941c4d00154440c502e450b01e0b11115001450002c914540c0c5401c105c0c040d601c1c1c420004d40c0c0c0b03020704030505610f04528002c0004c00c0d0808104c1158025041d102112450910340c1c181c2d1301e50f00782540301d803c91102400e014100c580302e102c0c141d0400d0715620a480c5001d4058440c4007881043c0e490aa0790241c40381c01c20040c4407048040e09512003c035213001d40d00501c022000103107a41c0c0f10301c43c100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 566159694 1250 566158444 566158457
    0x120102070c0b090a0b0c0d0201060501020312010603020319020c0a0201270b1b0f15010f0e1603020903010c030e07080d05070b0613020c060609060f030c04180b090a0507061e 76
    0x1603d51255010b803005030400155031a201d14101c0415940c440380d580e005001942407980000d030307550000081c2c65a281c90510007900a81c20404103c00940006180c0302d102c910782445004640b08920040c103c1e07000030780180c42068600c0c0005411070342070211140054540748260b860f410b00c801d1840d0217950780c552803d66203a070440005440032a00d00c032000f2590150b00d0001c082c2d030b180025204001c00c024401e80006131f80c1d50a84610030700161103508103900c400e5001030080001d900914000e8611400c0040c2440100c1001c80e01b12004000c1e0040401d68419003001040c500b0080180140740140023480b044c001440010701d00e0265210080500c4090000b0558540d03629104d180c00c401301e030724115241c5036a0130b5217595514094480c41d0190365070300c01203404c41c10000179a002000018004011201c10b11050000030565680b00744404007428400d0300004e8001029680102c001500901c03240205081542c200b040316840032088c44003c40c8a400d64203e60740705041031044605240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 566160944 1250 566159694 566159707
    0x1020a0605040206121906150e060703140d020d1103010510080702010e03161e2d0606030b0f01080a0c050d030507061b0e01090e04081b100203010302120102070c0b 72
    0x82e0315405001c17420b00c0400c00c1d44081001405844690701c1e80c0075683c0800307100030360381c03000110103042c1c0000b01a0001003021003c41c4071814401b0040007414400c1c600a944800e00b81d441002c5034108160b1252150380006081001641c03600800c01050000e4045c146107501d090006501d081c21001481c1c140b10b525000155524002c0d4040e4603000d01000580340d4401c00e800710902010f1180b03a04461840188200045140750358400780c00c040e9200121b0040340300700100000e109100701d42010341c507544282950000800a008820065103c2c00a000341810114a1801c41700c1050700b00d0506940500c4003880406d50005150f0100c07201520380a85144041c20100c0701c0344101c00e000b034446801c090001401a0603071345003d01411040e500d1385807103410000112a0403480788070768009940388402040101d0342c06802480d00000440c0400700300700081100c14100120307803001450243d07010004006600b0f1042d107038010102c5c10002103252034286e543c0d50351804051701400042c4400031030007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 566162194 1250 566160944 566160949
    0x7030b060301121e1205092805090a0e010e0a120c080304020411090607050d030c0c050721120314010e0c0a211406120303040507090b0105040b0c1e06010501020a06050402 75
    0x81385141c1350408510141e1a00d402c50242c15503002071500f500900400e1001c61503840000d4075442d0683d403c4103c201c000c1d18145c2044088007001e0503034211180c0c0c40c00203c3c0d070707160b003481941800c8036020b0142100400e2418030f082c04802c0000c405041c4490052958005100201140e501c04d030b045400003038407036a0201035a0a0300500c01241d800c048005440000e2010000300c100307425001d03a5003401703146200c0300308070351303045d6101d0005140340d010b500309010300b8082080b1100100d012007803541541c0140d407501d9207120036503a031603c040b9a403041f0b4801c1038401150900e01514030180a40d1490402054286c100d204412010b02003004502001c2c3c1503510790320400311400f400b44024403a03000c0e0107c0da2170762401c0560b046803040b001900e2000c5002004019a4401e0b0b42201c00b8280540c61308201c2e50240010080250400c01c0c20400807a04680c04009801c0400710100106211940c0c29520680240034401d2880c2c5588414010031045ea80010484074843c2d001c40045015100c0d48007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 566163444 1250 566162194 566162243
    0x21f0503130c05090a050612030c0c04050a150e0106030b04021903020c07030c0902090f030111160507031718010908100b06120a021e0301050108180f07060201020307030b06030112 79
    0x1106900c05141c2041c010380004941146c0d0103420211400c4003904402140c4545d6482010007001c0241c01c182c22089036489d003070344003580c003c01c3c9190200b0140d001400202a0b00150781105510361400700050003056418400ca075411081a141145001c0c01095170300c0e0044d20b5100302e48105600010400b00710304080c02140b0066038094080a00300340c507481044065007160111500800c1a11054555454140031784103001c403110007054504900b9812032000c05204000981c0d25100d44040080010354403a0f42c0e14244012030038844d228242800d03590040c0c40c1c3c18030401d040001050b0b040c0030200d0003080d41e90405614041c0001c0d0461941c01041d49030003a102c0d040c1c4070a005070108440d00c03440d41c0044c08003806484841d440d40400ca001023440d0701085c01141d0014075131000003098040c00d6001c01454100850032104001c84580740c45180444135006000141d4011040c00001e54060140c110046402c0740c00905542c14501d414010308000301c005004a41014104800c0007018103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 566164694 1250 566163444 566163449
    0x7030807051c0f020c0603130807020619020604020a050d021e0109030206040e01081615140f0304110f101b02010c0203030d0204060e0406033f0903021f0503130c 71
    0x5901501c510024800500741c201c3c0c020b0380a015001d00c2a481007607140400c101c81c46000000e00c10400000d10383c4480c1c036142c000000484e0044010820a094a1107a501d003804c001c41581c0105003500c1c013807050003003a002e01e0307000600400b040407103000182c1c0e5403034011b0b21014040d40c2014041c5081001218030b501560300c040c0d00311000041c0415000d590f0751070350b8117071201e88084a114802c100c1e802e2091550034031803d010340c13110604401d05213208094000b40b480004e12400c0c20400d4030552040542d10584045500400701e61449116080c0f8000c5104460030450f00301e140001140303000b1f48000c141082c88450304205036101c0c1c0440e80034403101c401607a00503040302c1e120800680ca00000354000e005040108000e00a10040ca00d042c2c01144203880c2e10040f4030704500c10800796441c03081c210a800054200d1070300060708104a5218007021954816130304c60b2150380c69401880301c08940454603614141c0b10005408205401500300c0c0e40044480c91400c1014045061501c070701090f54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 566165944 1250 566164694 566164723
    0x100915180f0e180613080306010923030d030c27030507080303010801060b07021008060d0203010213060305090d080105010513030c09020315091014030a0b0a2c0703080705 75
    0x300d4010440306000b0701c0c800d124003608851060103e0b580c0c02c04955030307a812507404c3d840041030103002c0300060540e800f0b1034000c20181000c20b9070700e031034411021b8000030901d03086540044180c5c440e0024036003007001c0320701d0800c070f41810011181d0a40000380b142d00000440c525001403603158055040100c2480801181c0200641d0b035040c0d200c040712500e81c1d00070b03c81e0f5030103036087c08004240340c40f40c0d204032044158010a403018008100d8404d842a11004250303e41c8116841003060141c0c5003800103040115003030340f40c0814181030880c06022101d01a10b01c50321030b401003003c1682c0c1d90300550500c1c151402400c2c0140c58032903200d100f112091b120741004008c502e054030000b651b0000b40d005140110000146101a0018a028840207150481c0c1001c002103001808006d0a12251070181e0355010260039600782032130030b8440c90345100c019070f4003c000c3d03a030b55005402001c420320460008841d01c0280110294540341d40250b807800c50740000307004540005020010010304006034104110007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 566167194 1250 566165944 566165969
    0x60f090215160f0b040318081005060303190f030c0305010e0135070f0603020a200f0303100302190b070b07031803080115090501050d091103100b10091518 68
    0x703140c13040d5040b109a908401013151072080c515034407c5060b0701e4050b80d00040040075800714440808000c0d00d005002d01e5018002080020341280800c40c0c0d0009010450315102c0341010900d0000302282c1001682c1c504051070440140841008044d019044524001a9400b41490407026000540c4074444c01f106102100002c51a529808075114080320840041034a0180d075030722094040e0b2142111010020b06000980f101500d886040e0303130300410003801140d64486801864502d19801610400c10307088029104101714648041845414862050150805403a12040341e00074052148001c0c6105040000111414883e0b4080f14286030038074098408040141000703080800203009032003880a01e10034200f80c0d80d001e201e0000482d030042c0e541070300e070110a005002c0200700100044540910ba0700840710b040d0b800300a91b50140410710070006006980504000d00c460703114102d40c0600605600030012000c402da00e070800c807600717810600300d403c081c2da1000211225540007032850170384 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 566168444 1250 566167194 566167223
    0x140d060212040c0906060302091f02070b0d0b040b01050a0c06110909070c03020f19030c1b0b0310080615221802030f0604350412060f09021516 63
    0x403542243c089488202d02000095280d01c81282a442402d924980000d200c5084c1400340a0b808034105118110344150781c940360310b48800004592000d03001a0000d9210940740342c05203080d11806040c1802420710502d80740360711760041d020300c0707a009018202d03a903110400b091003c418011203000f0314004111108a240841001d40007040342001640148034251000c0c01c100b4000507540c2001c0d0540c400004010300c01c1d5801c880000a490044400c2010060040ba2aa400b0b180000180081d1729150740c9911b0400119846040150300c10003096100d4000d000180d5074110192605042c1921240600000710380000340d0300a40310441d50510f0b10300381e0400e060381420000040414404c600741c42c007090101038042d64800090754050b05d04071108a42d1185a03011614004a820041d6001590781c0c1c4000c0820303440d900603610110780300420340700030001c2007400c4c4200f0700000d1407403808002515940d0007040850101110703001500c4000901502a0303058a80320140303032a4403404410341c001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 566169694 1250 566168444 566168453
    0x106030804030632060621011403100603080d051302120607110703050c0d0c03050a0503070c0815070e03100f060f06090b07021e06030a15050406140d06021204 70
    0x9604110008040504c04241240c015440000060078580ca459400c99140c003010007509501121101c03464044441c084072a0310300c1c03028804e00a1038650401c1c51b041401e00d05050a210380082001ca00c0c6290800500015001d841030300d42202c0c0c010300015550703a40d44900c0c1004045010302960200020095140e003540020b0340f41c1c400c9855640d650703101114010b0070303507843c8024000140309410941c070400043c108800d11030350300e030b00130b04041c42c10a0780c3e83c4542c0e04112511034140c65039000010100e09024010340440000c180c0340000305940c3c05e951001e900c207080c026180d030003040381c0d1100c00301403035904010b10301c80060f0711001000302c0546003007450002c03c03c5102d030f2590307044040b0f4000348071805013410134115101801414035082c141e5007003081c5280d204802c141072004180c2c1810840c1ca40c2e0005e14801d00600400040411100450b195218080e9000074131450a1001c1445224014080408828002e403014680f814040c5401b4000e4084c0c011a904990088000c010900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 566170944 1250 566169694 566169701
    0xf0d0c08091e04110a0e0d06020f0a05070318031a18100209030c0603060108070309020d0b091501170d08090f030a0207180b060f0a03090b07121a0d0b0901060308040306 74
    0x80c040f5010440d500e10f0602d90100c41c040c80702180c1c00303e0000030520000303040004c09942800d116020052612421b1061a80640c00c0061444001403001c600d00e01050742000080001c08100002c2c044001c0c6185c0d920743d00e1920210014290710721100204558414020070a00d91503001e205581c0c008480680c424000d400c00764000d8841e1090f035111074003504240d000c99006080c10b82d110400c5503034200c3d059014085c0c40004a0f0000f10500e22000400c05802c2c49501071086c4d034025251548040807042400350040e04107040b200c1c03249a400b04920030000ba410150300007824040d450b55500400781c1d0500e081005000b03400d000000b0080c06551340401c0c803c0030750314040760a412030321002840b08104c072422240c858100008011900c48500c6e1003018080c0e09030149004031701d4940359560b07441c0e2408107540c5000492248101d00d01414114050760064650702c0501d19000d80305040001c40030500c1a1010f0b20420503400820120b0001390030500103950090001a83d5595074903099004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 566172194 1250 566170944 566170999
    0x10e0d11070504090b0601110a06331511070f030c050109090e0d03020708190815040e0d260408030406060e09070306050901021c020301080106080f0d0c0809 69
    0x11070003401404119440e180c420024a00d400811501042e030b60580103654540848a404040348a80401400081e00600481e11205e00d402803020002034aa0038011a0032149094409403191010042c04500030100014911401c20b01d4400f07544030b88201c07550704155082d040f0001300110401c01005020f4082c07682c004485081e0307201d94415030f4030601300c0c080b90740e000d0500e50b880e00946004001c0da403080d006024560700820010b0701d440490542038002d0100f803204500402c0b015800c1107181205000000d190790382c1039409000c603041d50401641c446d42c84010401c02c2c40322042d45c0940d14000180710100300d031495807602c005030405051807902500300b01c03401c948032418075101003141c0390b021040b83d01600b8503000030b1203028211b50f501e501816008008014030741d401e00020910441c03080c801040c1018001e4016500c0d410110024259001c42d0440d00c156070101c04a610720740000104140540c08a10300b400d030300070092501c2130b000d1142080140d488001000c40014411003074080300c2a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 566173444 1250 566172194 566172227
    0xd0204090509010207051903090b1c050f01061404030f020d050f06040f050610051305371b05030c030702070504020309030d0b0916080a150803030a0506040504020a1403010e0d 77
    0x40c0d10203c0b181d4401f00c8030400000a002542c0c8880810004903103401034090ba40500c80c5070341d000b03070110b441481224411120f0411620101004100454004682103a5402101d451502d85411525184041ea104140081c050010b8401203000d21909120202d0035403a071005030380742e40c28242041104d640e4881002c3d104c07401030901042e011020168043c0448001429a09468180001034401001c00a082c94100201c014004650310803c0030038170f01e641c0c1e2005040e80030040a03582901159480401c00402e80d210020b12541c00d074125081c2c03076000c180c0806050341d954400404034200541a441242c001c1c0c004000e0110000b004000303010120001c83e001c00061a0003010017101c07080640e2901040b49801e881e002010f8400c8050382d52002d8559008503102c00000c0106130b0a4010342d000e0f0556410103c00c0c41100c0c51075000340c40e0009401ca40601140c249034001610502d002d216540202a044144d01c400361001e410082101c154002503607041a030416018101800c1c1c15072a45 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 566174694 1250 566173444 566173453
    0x12304061d0603040f0f020427050f010c0504180f0606050909060306070509100c0b090f060f0603032712030a1101111b160b13060f080c0d020409050901020705 70
    0x1d00d18144030003540e00c582d070850106801000317545c881400c2e8005980045c2e80041e1622141e0402c2001a0b010115030b45c4002900042c0c901c2e541055070820840c280b05511590414002028240d40700301540d086e9001d18800c1400c2005407060341c4010690640ba0301a03107400d203039002031000e401c9409003001d44816200c4092960326513040503100c0c0421108500460000e00000c0954244403558003030b00b0010b03040c0107020800c1500d8103c00d0a0301202d400845a2205100307112000b8107014035500402c02014071900d60600b500025120b0044620303a98142c0c040c01c2da180c3c501c002c00350302004040d201501c85411019110441900c07948081c0d5064042544d090090448140c1485600405400b0724559410082680e1842c001c1c0b65500c2181070291140f032000301d02160f2031141100080c400c01040b60760b0b9800d164401c88201e010740d4001801d100c0f28640d014051a0407200d86507202c18111240d0f5500d900b80300e0b003a0000c1c00346400104140f03143c841080035001055000701801ea00070012203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 566175944 1250 566174694 566174747
    0x51311010c0209010b0c101d21041a0d18050c030c0a0506030a060e07020a02040507050408031b0f0304180624050d0b090421050a0e01230406 62
    0x66a0614000784000d400c5000000104000d4100401522079074900c8000c3c0c1e011040100c4209054802d00c040c60000c081c1c1400018066441c01c2000901f00f1690580005400c0640c0408210038000c5110720003034400c003c1010008610f1b12000c460340d40a80c070710308004e210110030400c01019040d00040340d03a441114001907980c900058030628562000b4100300d00d15082030140005c41e0400303024882a151504400310396a081c0d50b020501c20644d6900400d001c007010300402042d2100036024009125041005001d00726010045481c1510101704c1c1c01c014040c00a6405c1c82e1500c800c00c580500d000100d00854100100350400c486018018001c3c4040341d110312200602241c0b4121695101c0d101d0213604140c3c0c0d0088002e89111225250001000300103071022451058040b00e0440300a620f10710807034600c1c0c1d8444102a2219200d28045040034815100034120101d148009410701001034109000e103401706a0b00c4d030b11290034801494540c1d40d00c0758048d0644048001c135142c43c54254149 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 566177194 1250 566175944 566175947
    0x21f061d04050d09230a08191106030402010509010e030a0203070b0c0f0705030d0c0c1809051b010203031f08070602160b2d0c070b04061107050904080a09030605131101 74
    0x451050b102c19840941e4134000329924045d40b804c03003c2c4c26035040101120002000c00c81404643c4900e1500220902450502e00d442c40b51041d050031001d00c40ca00510500001d0b136404000d560124000303090860f017250108000924110059500a51610072400041108118500507040200202c403c4072019450020341c1500c880c4c06006054050b4060b409044005101c0c480c0c060080c0c0c0100385118ae8141c90311600e0075180718a800140d1442d8803008500c0400808011a5009003030101c207840c604070003400000d44030722018010001061240c0d8001c941a42003100c2140202100c00440720496650100603403520410100500c081c4074400000448014960071250040120302c442c121700344615000e551050b1103950600d841c400180400084030904200e50000780071031021090301c440c58007100400354a2a819601b6981e04202010801d0b516104032290700a94001040c5881e4079074400c00301ea920410b9800074040c0c3d07007050300380141409842c40360140c290041403d082c505900000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 566178444 1250 566177194 566177207
    0x804021906030209030c0109030f033b0a0e060a1a0c150103141c0818030d0501050307060c080306090916060f23030f0a18080306190501021f061d04050d 67
    0x8003074504ac0c606424100081d105160340601c24070961146ca01c0c90fa003517001c2e0003e138203082e03008c6204000076450740c110f1480c085030000014003001070019440d291410114040a000303105070315601d0300081c0368040541006040d01c4100406c102101c21042041228030320381031081c40141c81c0c00ca030284503441035030f10200300030040c59041e04c1c00c1d840040c1c81c0e081c01c882c002c10041810a80d402a80c0420251410034001040740003c1c5c410081829410a8100350412540381d20810a1240c800710794000640414150703603015000b10313804245540c031f80034050f08080c1080c03c034040039016000003203070b140d420a08203c000201640c4d0030242844030b00741400101c600f0914032406440600020309003011003510b02d5440301c8c3d800340c0417401891100819100305041d42d400c6819001c04010170070a4140841c0d0408007032000e054900b284e914180001c1c3d211070b95404001d0030044400c42155070344065811020045c034814002c1030048030106d6440301460340c20307078003110076016002801804520404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 566179694 1250 566178444 566178449
    0x3070302060f1806070f0c0b030712022d1207020a1e050a0203031c0b04090809100306080a0f060c020d091503110a0903020a061e0804021906030209030c0109 69
    0x1c0071185442c1c840b82e202d04181e08698952983c00800881103191a140c02000c4d1080ba842450159017a07181844c0c8604030712007035007083c0d840c0602441081107081e0710240001d0042c031400c80050743c1e4600d800c01802e8140080d01c6c101e40300d43d04403450240f102c89000082449420440b0008026100c0c001b040380c0360010344a000c0c0c109514a56210500764009044024541c4200102c60b040219a170110b405c41c4c10940c05494006103003030610b02022040c0c022034030310380411281001000d41c17030340d100743c100c0c01150000d03070054884c40c00c460900e5010380c0c030250140007540226001d80086207844212403016100442c0c0b00c1e0301703105c60300d41e120703000081e00719400c00152140c000c0f003418008a41d01c07030082464213004054403640c503891a4040a4000c25010400e940c56101240c00c40c0148420b2090560118081000c1d030340c070540102890109403500d270010303031078491015296400010390039071341504141440c20b000306001070101d40542c01040d80110550507940c640f9940070040d01c0c04076152 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 566180944 1250 566179694 566179699
    0x608070905060904020c100f150e0618060a0801020708030a0b010e0a06030506030a0b010f08120c0c22020a1d0a081002030a0e0703290105032e0c05030609010503070302 74
    0x9102c0383c07210b45031680150240e850b0742d4084406900d81c0c2c002e0070003610300304800440da20740d444130141d040d0344041c04c3c803201801a880c108036490403c040440c0d80310a5101d082c000e143d403c940422440c2e620045076100400e00a0002c2d501c85d812400c005c0000d038000c1d64020001854450b4104e455406403c0380194040d00030f044104842c9060800d0303010300002426a40d050240d01411030002c1d80c1c00703003c64080c00340c0c4140c01e0110340c14403150320b02d0030103403d800f01440c44050100d2101d125000454014580081d90701c0340303299607201481c120200c1445403118002c1e0010070794143c2940d100c844820780341031035501c7c20301c02c10f0076200b40303d00f5820074011080950460071020704410059001140c2002d1140c0b40000c4d1280f640016908010a41e041241c80c18041c0ca15445200c0c0100c0200005a4000c001110740b5450710000a5450840c0782074040080201212661600d020040040341c0320300200080c824100d000c800145142e00840d1503920402c0c0820001c40d00d0308000840380b0aa9602 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 566182194 1250 566180944 566180947
    0xc050702040e071805040c060806030a030e13021803010506100e06090d020402040b0a4d03040f09060e07091a0705010c030912110607030f06150504060807090506 71
    0x2a5001c1c0005040c20309a0044207100c1d100b000a28605813040281c0002840c440002e041e05181ca007082910b03d95078008020000c48034280049550040756844a40d5454107008007111b0041d00407403c01d801d10b88100320350f20710218154007010240e110b01242118218001c1006036140c00402a5045010a581000506d01a0004501d042c48002046c400d0802084203800c002c0a03400170f002ea921a40040c1800c035000728400c00c0c0181c10606d80c18050140900c0340c500010140850b02c02e0ba42013129882d15000e40780300e032540741846048100e0300891080250399459441d6a500c10103038040d4884c03c0003041c0f400c40002203101f40341d0b06a60142c2042e030350f603042003480e01d1882524601020b09604031044108070750800540700344207504034007246842c04078068100f8240040080e48000c1108240086e800c000c000c0b0500108030982c1c450f007141000501d0400c00e2007110010412a00b000800f0030b16407400503c02504003001c2d100300c56150303940080c141c0e900742048440441d28031545412400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 566183444 1250 566182194 566182207
    0x12062702030f120f180301020406020307020907080c0a0f0c15050610030e0d0507051c02011a060a080f091024241b2307050307060219030c141f0c05 65
    0x41d03030001045c3d65180390005880050014000908a0380b050388010056400003443c0421410040c01c4558000c0890504600d2407a1003c403901d12807003041c1145040210007101500c40078017901c5201d4926411200d145100114450440b00604080e1362071841440d0345030071500490b1007030140e034200e10799510241403041d5050000740d909410090302120180034280d0751144506040b280c100b001e0819030700101e0106803070300b1510060a0041413160096030204802200150001c003207a0300000c42d0018036101d03640c1c1400540c00e084100002040e401d0038038444841400382003482445031503258070f4400607150385042103648450b64101080010f0403081000290318051082c0b406034074102c50581050030010307a0b4002d51401300b2f0f001c0c0317400408103c520210381d29041204002625080d401001c045040071006980d80c0000f82080580d01041d42c2d440d010580324203082c0201c0381d800b0101c1d0019a4020141c59250341c0b07a1440701980c2d2103089100407102e0001d000f440d41102043d100c1615000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 566184694 1250 566183444 566183467
    0x180509010b1516020a05091905071b020f0109090216020906010215011203210e0723060906040906032d02060f032502010e01060b040506030112062702030f12 69
    0x400760f50b8180e03444641c03640001120b03204c04800ca40300d0350080411107000034400410104a07080500b855003000001e0106003800038940b03a03824107940e01101e6441b14641c0100049540841076000382c0700c030900200b020900701307075060030041216208659000c0a40d445500490307440018111258203003000000400c58141c14607000b07001c0500034600304c0c0f00e02580c840d680746584005510010720035611044607442d4039080c005136002c1c1103140b118030040804818001641020301d40311a20a000000302c181643d070764601260b000f45401e8078207101090380c0b402c0101000b034580176814582103c59506c40700a104880240c1042980282031505090b4100b01c1603a0b1074000402c0d80c0740340291b003410b04852a40320035086542e10161b034000306410000e211503d003991016807128010141c20310050289603618001d990559541601c4c47c900990700b8113100020b440c104d145040b0b41ea10100c00d4108910028120421107402901214120b200e081c01c51070390766070424034009551205002400210 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 566185944 1250 566184694 566184727
    0x30106030f111309054005190201020c01020604030e01030c02030d050c0310120c173c0615060c03070c1409060d120302030a0914100e121e04180509010b15 68
    0x74988000f0414130210580c0e21f144ca880d4000d14060721109106042000315030341000040900311080c030152284d8109130354040e0400d0040d40035a030516448442e2200314034420002e60307800c503a08410501c001d0800d228000101d0380300b9241400d24548034100810800f0031031082c1d502080d403201001d20341343d03e0328030036880382000c0304510400c0b0702500c4a002844014150038002c82e02e5402440058141401284103880d8110039000805421090402c001c1c40c80c1c0d176500008807a07081c0e5485940d0900309080500b54403581100071f010444014000c02d449110b01343c1c06030548410703a6100c00680b00c040c2001442c05104a0080400705e286203003070030300e0788a5009075030003101c440d8011602d4600c56548401c080d003850f00c000b44035448424400d41e841c12a00602d40c0038004000908591070300a904030311980b1031404490308030480d610381d5501d0050408203c8004007a03401c1c0c281056515250020054441540c07100555130816060790310381d00c0d159111a50a11468203128505840401890101c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 566187050 1106 566185944 566186041
    0xb0906070f0e090f04211806140702040e16083304060e03040b03090a20060405091b03130b090a0206030106030f11130905 54
    0x90b03482d07aa081e00c1e004103d03510310039600c1c5d8a80c00c140c10710100c0101418030402d221150f554006a1028107602c40b00da071542403180350741d40c8660448480300300d201f41581c03d900070861b0750018a0503922000e840c00061040d034001d242c141c50b040103500d01e5130703100d850035400c02e4500c4c0c10071104090030386d022181412200300040a0ba80115880b00d480240010001503603110490800001041913600601400008681d44c0c80d284491a8481a000c0c0040307406141c0032603489514200f03403c214003100006042c4608181c94030040100c0e940b8081d04500003940408804541000c41030000c5114040401c44c00355105014030b42a01c46583c001c184451039000600c1074001030b0b9496040f00c3c111000d518010a2140380c44100c03000920b0b03e041d26040c4444006025554600134003060403c89071055020890b90303030751a05024046426001103d0113903c00760789044c40c4084600e04088 = true := by decide +kernel

theorem cover : BRFrame.Cov 566007194 566187050 := by
  have h0 := BRFrame.cov_init 566007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 566007194 ≤ n) (h2 : n < 566187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
