-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:33:33.269062+00:00
-- url     : https://prove2.me/submissions/8616f071-5e96-4f07-a3bb-30fe1d5a9c12

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 907014388 ≤ n < 907194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 907015638 1250 907014388 907014401
    0x1808010606033908190c0e01020f07080d1101061a031014150306131a120c0f1302090a0f080c010207032103090c0326090a090c020c1201 60
    0x121a40c001d810030300f0360000384502c03000814407041e10070304585410f110641c2c00a6019000c004040001a11015500e5960240540740031007603642070400e1000c0c000181c40c9c25950203d0070030039004010306115001000442004042091400010f0301c214205514010902c523040790382d01d022154948014041c8100045004040010103050241d41d01d42c07904610f0204100c00e5584002d002170b5100d00c0c481850099600902c00030326007001035450700811f004a564440d4007103890078000160a045140c40e2103058420f40300308001e8500318442c28001126610004a210b105240c50b0b00d07000340b881183d905a0700401c2024000141a0b0b03101d24483c024614184200700242c80b540510890f294804034484040700d0780000604898180b0f1140141c141028803040001c05070745d503010744049201c406015000390301410680360359640200440340c64840d0b461148040c07840801c04e806043e1038070840d0004960383d4010000b41c8c182030410882c24150b000701f14590211071065a814101c0d810b42c0400e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 907016888 1250 907015638 907015661
    0xc0c152d020309160608060d0303150e060f060304020906120a0c0b04240c1e050a110f090106080420130b0f0d030c08030705070503070503070b0105090412180801060603 74
    0x35030f405003590400709070f404d00d41d02a00c0d001030201c0f000300303200d13007080c507244403072a8420308020400502028424804140c2a40103500a007620400e002090420580d01c10307496205641c070f1451031a2903004100a06400390200d0b00455000b0340501d40e95000f40100840b55903c00302103000140e0740d00c10038240b0342142c0100c03514103090304064441c400c40d500050782000c406489001c88043c5988a0946140c1c0140440000c0c0142410b403e00140e001e0289000040c8204411482031081009000c01c10010644c5280524030090051180b160450412507016a000403a82d01c1c0c50360140401c2c02903e40c1001d865013007192030140707844000d403d0704600a43c010a490102c2c6001c4140f0402c80c6c241c208080c0070313010903c44800a0046502d4400455119210b41841d0b0f14159a6a03282032940d40118410b94041e000480d68104111000340028010241111103401c1414551240004001d0380940729092102003080e001006034600d8018008150010081021565841028000d840c80d0710b510b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 907018138 1250 907016888 907016893
    0xe010302130e0c15090301150f080102040602070306050a0b18070216260708061905010902090112090c08071d0105030610051003060302040203190c0c152d020309 71
    0x14a1144030300c2000302c039424201c000c2024449903010301c80000321a0303041004100f0100001492620240192400455410400b0300020310703015400c0c0d0081c449420540250f40104010001c05030300081c1c43c0c0c1600d401a90005250320b40104910080c6406200d42c3c2d004200407038850000d503c5101c1951207603559409950803180703103a6000792852100c0c0540c513a2011805004d030118034003032245000d0203040000300d8150340d131985040303842d01000725126141c0c1561451100e040d103125005250040c44da46c002503042110000010385220351940324000c40365903600302e0354140030050310b1400040140c502511110b54544a043c030004040340c42120b6030522a20002966041c0000c405100707441e500d040d5122903003080c0c1048890f00d1140103030f00405440d8240800540e070b5a100950158204800d50822100d8400251080e50003168429041c0448002c40001140c54280e00700d841c0440d21000007080642d0444e03c03503c0311170208840f0381000d00c0486010700084070b41c3c019400781440d0303400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 907019388 1250 907018138 907018159
    0x702151303030309350d020f0d02091003090203030403021e0a08061e010e010605030910020a020a03030e0c0a090c03180605010f0b03070f050d0e0a1a0c0c1c0302070503040e010302 79
    0x2425200092417025100a8090558450b801004c840014003000d50020501500d0410145480f241603041a6454401d0a0b40080d01017110b1800e60049034100c003040c14284200030648d00001e0b01d030300a62002901030a03c031102c41c00b080b507102514100300c200041c101110b40b51503882c00c03551030808540c1c103141054502c505840400449001a040305d04100c40c4010036803d05900301c4054001400c000d5491082990914000245002030300b15981694018546012a410020190780d41e42220f000c05170020007040c00d480e201c904400e02540c0004401045603218020304600030244050910103201859030300b030317003001065000301d812150701004004101d912a03049003214401603c402003c503400d481100b0b1001d0058000c0c00c0261080e041c000380c041c4d140400c0074188a0602c07070407601901c500802246200c0c41c0b01020350070060480c10942490084041c1c159039405880165090882c05109031064031300c00d030101d841302580001074944982e502c203102040d40500b0700040707204031950340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 907020638 1250 907019388 907019423
    0xf040c050d110d26030f0c0c0604020f060904090327060807030b011803120807020102030910150f031505060108040b0a0905100e0d0201060503120702151303030309 72
    0x1402150440024052107811204101c3c81e065122411501107400d4000144074804480d042524601c601042e580d0b039291950b0040c1010310001d203c0080c2e840103202e0502e807d42c00285403540550305860310b082502c210400a440380c0a12101190720504003002030041507801419070012000f044075040840e009007100c0304645c42d290045600081c1c43d0b60003d14094801d8000454250f0706051107807601e80306c080184103d0701250820703602c01d803080d121034030703a10b90000c02c8943c0825144021030850902800c41c9894080e0b004000c00c44540f2481181c0b03410003a0700c0e0120003001070b040b0035884d203030b0740c4e19003212899082c01c0c02844492502000031001e501030380059210315400642d0a80b203030740320014a0001e005120040e902d40c4640641246442450300c118010540d425000302901c01d80308400900751015904042e0294003c02043c42801031a00107440d0382aa0485240c409510740350b52880c0780e40030351030800343c2e0980602000001e0680540c45082018000d00300d1500c80f20200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 907021888 1250 907020638 907020649
    0x9061109011106011208070c122001020d050d1a090702150a020307050403150f0f020309010b03030702030a1101050706090c05010f03050f010626250f050913140f040c05 74
    0xb4420300d175150000c0e40e601800545030394010054a88174130b00105119440e0360300e41416008000044414551107510b8900c0420b0920f002d41012209100410254101403801011030080001d90f03100c142d01e90300c41c0c1240c2000c0440d50604c40e4006040340780685840c0744000d603907802c0039a05c40020207001c1c01140c0380c40804e008603446081c841c0c44940c0b0300391455070740000308111850310030001030340c4034580141c02c8a28016a02600780743c140c0581c03241841c81d8101c0c01c4649001d81d482c0b003684208006c2005031400701e500d0764000c1d04170150138112244800141c03024030620500a0140346401c16040400c03801c90520070a50310203a90f2100ca40d0380400c07040d011107009903001045440110010050300e0300c40c40c540700c900c404084c03070340d045042d405003203d5900806494026800c2d2401540940e20300b0304018407026202c003072030064642d03085080007400610032420303480e0107586014801c003003400700c42e0400140c020240391210980d242c40ba505000c0c803501642c00b03d1b14805074000008803403411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 907023138 1250 907021888 907021891
    0x606043302030a0c15020412060e0c0a05030a062a02010227010e1917030c010e0c0108010e06180702060a1b091202121509010f061409090109061109011106 68
    0x54460400c0d56046490762200d4140881800300925000c07c00030071050b443c90000303a01c15110340070115800c02030b9641d0605280f041042d05e030096035149010091030383c000403455103445c0c00901c00a0030201707060940e500d400b440015007003034041000c00c0041e079981c15801080c00003aa0240c505015459a40042c12003030981c4005000074995001c1d0348540c904400c80c04c118103103000c041100c2a84e1b540c1c0c441c0c0100391000307002d210b640020a03402c11690082c01801c030300309400d4010345101403060001900140c018025418000c0c0a4000594035454039003000040320074103008858945004074000355525030441e00c2c40d00641c100302542040b42d481d850541160885a250801001e01740340c500d0203c90703840d4400344e900440c500c80850760180d0a100000d00041403030b0300e0340c0c4245003034140d10742034030b800e100507290300c601c1c02c202000048444001c24010321811682400c10380c4a10000c00d0140000c000082d000742d00c0c1c940b04186800800008009000080e04c4078401e10552110064851a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 907024388 1250 907023138 907023157
    0x2d0309150f131401140709060909061d0a020c120a0f0807020601210807030503011e0b0a0324090b0f03120d1107200111010c0e0603060604330203 64
    0x40625650000f061000040756140d648400041e80441c0c00b5051030103007009490000c007050710514240800f41c0d01000002c003600040b0400c1c0440307440c0800c013442c000b40d600301030840c08c20180f01060210010ba012500c00701c1e54101218803c00c5d00ea00084881d41c0714601c0c2c1e801084c90240450b400c94011050148904616005881d240c0c4ca840350025000200711441043c0780c141c186004002034449001d84006402591a1354403507040c009504070703410046880c00b26911003a10100f003c41d0385d00c0111602c010325490301282010f4808a00d14030b00b083e40c80010a802250040424618014dd10000f0032102c107c0d2a0030940040310140740e180c01001c81904070a510406c5000c2d440c012603005130040426004a4a20f414010307107031030180030220650b04100341a5250300c41c1c010360b400107908032406042e6008101a184003800608003c8004c81442e02174800400010100d039269000d5500034081044a6407a03100e800e07084081411003000100b1000c2645424428071074800000e031004400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 907025638 1250 907024388 907024411
    0x31611130606030f0f3e040305030304060e061b0703051b0a0606140913030c080d060f0b0a080403120e010e0601083d092102010c02122d0309150f 64
    0x20146200301c80c540308440e0080c1034651b13440e4151031040200c0340042000794010005140c4908040c0303404c0c41030700c8134401c2d48030f601d910120a01c541030b0a003100301e41d240c0851159181d80c0324500d00d0142c0da24000e5202603411800b04500c0c0c46099140803d22000481c460003080006c9078981e1184414071001102142c0c1120f615070028003590b00345000d080c6024000e00302a0804601d5513106081c41d8084226012604d07100c2004000211100325101c0286c00155600c50404403103c00c000d00e030020080001d801c0058440e44503e100100d64000700101ea003c030000d1000e8400c41505070703681c0c00300b0321031000144903418462542c400248072500910702c41391078040201075450205503080d610600040c000c0c51703480441500041c1501d9115405400e42c503204800401155806030846207040c000f5419034204084000403400f00c0b10841d2066a0100c607064400b4158408240c0815441400d8449640e00001232090110b800100040701020600e4401c0b266564560007400c1c1e80b00640d00003e412 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 907026888 1250 907025638 907025681
    0x170c010e0105250f0807030921080d021c0c030e10050105030c06030702193912050a060c080f010f030b01121104110901030e031611130606030f0f 64
    0xb080202151070302409100081312503002c580307601d0815441070300c1c11008a80407039020000700380d010350203c208003007600d04d84642c2d081c40c0e154265507204010810142a5000034403425190403481401540201070a00300700090404101800404009050003861f104850411406401501810703060ba0300240240854031011000d209503a0005011740d403d500448080244e4080f00d40920003003a40220900c1c90040c003540151140050301c040e9110b00702c0300021800514070040e05829003110440340118482c900e150803d50304040045800829942c108041c0c9400b1560207800743c0d00450a80f522400181d9a80d1403d16071603081e403000404220360354004200301c1410035800c1003124090031030111012759840000341111080c010006030200040703503002080d42d0520a004408001d50000c5240540c20704050303002c609010b000409403074054460383e0340c2c2d4481d103512000c2c0c68882075080c00700d1602e40134050080c14821880e611458500000c8001050303440c0140882082043c00c140002d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 907028138 1250 907026888 907026937
    0x80615011b330501232209021503040b071115010b03060913051002030a020405120601380901140a05220e1302040b030d0c210f0810170c010e0105 64
    0x95209041d0b4140e44403104400004640101b0740390414101d45800e0f0010780980c0c28410425080c105002d0504030990500c00c01000564220065400071800c0c104102882d0140c00000d203030182510081074502d01000000440400810240d070207960f0132a442451a0741d11401002c1e9800b20882c00380842e80421681c1010b071400f40e00035600203511520261800d616200450310b44180810300a055510440040100f0b440718a01100442000841001d0000c808151440003601c40b242c541c0d030010002840c4801a0300540c80f15900d200356040c816100c034510728014101e07402440c42c0c0c41c124504506001e030390030b034500200020b0720403132544a1041d84406000d05151b03103011100f01e0b001580c6e851a003c840d40d040140e800786001075583c1746110b060760b1404da503020750501d41d8418071010b1188803d40e016004041168404403030315084540f6640c0103442d0358003044aa105910104091f00082c4c101d0b42c1c0411000c2c5402c0e000e0301c0e1200d0540c16030004450314460300040541000c280d03407801c00c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 907029388 1250 907028138 907028189
    0xc0c060a05041827020301062c1f0602060f1612020c10020c0a0c050406030b070c0c0f06050a030e06150d0501060801020a0c0c080615011b330501 64
    0x141d4803a00760b00041c014082c841114513110824105510f031200e02c40c2c8640c02c500c0e00740200c801030141d500036000a404030200780510f0400c030105101c501116000016001800d2404482c0036881304032001500d04c2d9031720006034403944140c80310b140c03070b01030200020300b002401d21000280103020703900c0327004045007a0300c41c0d80290000c4001c54000c0c0030351032400c07070400041c0c000740840003404c07400342c04100400d1500796020400c2d80e204a0007281400001c0001c504005840c560011032410000b251040c5840c00326012400c41d048102a140e1004001c9800da0f8410081c00707520903292010800310613101c8419a44450446044c40010f000c050502c9650900101b5140400c0c032a20011a40944820096013640c01144510340000d50442107581440100030340c9d1401014800e01401541c02e10440070800359060103621030520652004404d03017040b91619100015402840b100d00d942041a480d201e1814500e00000c9285030500c03001c11001e00c00c0c0301d160b04803030840d2020720303041104079031401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 907030638 1250 907029388 907029419
    0xa03030c020f0a0b01051002010b090c160803070903020f1c080a180e09190c05150f0c0f0132070302040806010618060e01201e01020c0c060a0504 64
    0x2001c5001c0c94040455680e000c025120b000d52040d0200071a41d0b040105000030301d182540f25804680c10201c3c21031480e00c540e6103c0343c1100030241603a5a490701c0410704080c070501143c00410380d4100004100302c4035444141242500d100700e0f42c0e021000034070020441d40c2c0016100c1615000a10301c8511300040b01580281700240300340c01d100d8070304500000801d080348000c0c2e000141840900c030801c070303050300c0900400302c4c0010389030309024804002d03450b01007a2409a020341c5000340b00d02100308058104100a42d10071164503c07006035141c0002c04a5500c88400034001107496081c1070001c8400c4c84094226000000220b09900041c5a000c414145441018001c4402d060342000089032002c024040140a8409511040100d0003452000c180c001615030100c41008446038205201d0381e8070807420304000400107a07c050340700425a0a50904402d800300c600e000080001ca6400f100c0103401824040d5078ac602500d9a000014060040501c039030b0041070009041001b00340301d112215210070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 907031888 1250 907030638 907030661
    0x513120218090115081b03030c060a0504060b06030108010c030b0f03030d090c0911070b0f15010c02191d010b0c0c011b0b070309060b032802012604050d0507050a0303 73
    0x110700c0fa000322a80740c9084c107903500203d402da00010150070034820316061880080da4194011864040040f410765200c4501404881c5419103503004a418428584c010140d0210010180f540d2941d50f003090310700030a010030b0001d0200342000c3d8a01442c0c90000804c2550b404041e020310321302080e142800c0003d102206044820006403000803850103424820200b0100408102991700c800505020b155020300030082a058002c4508100002c00c000c07113004105182070a02208003c0948005003c0095651201c100711800c8840014440a08180d200c50941202411403040c2d8907983c140400b803180e0800c107140303a408403140c140076501c03580e102c080742c524520004060600c07540e10843c0b0b044054680303400007510740c1245018003083d4420102a90000c400030082c041201008404085a0002c2c180c802040d00d1050820b590117100952116801d091102d08402121100c100b1000380945095400b88200800d58150f80e000c1d10440d0100c03a0004010b1a003d00d803075600310048c02c240f4515 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 907033138 1250 907031888 907031891
    0xf0c0a06050d0f0c0f02100b0a0506030402010c1406060a0605040b0301050105210403021006060804030f120b03030f18030304060801120f020301180b0606090a14010c050d05131202180901 82
    0x803c1c6888014403803e680000240c0d12840610814030000f13150802e4403c0764040c03a03141243c202c210340e44120303903030742100c0040d50f001c0d80b80e5a0314001600c45040d413400103000d4180c80c202003020203e001c600316201d444102d8041003d5612a0720031500e5001c0c5020340c1c0b0402da000c00060205600640103080b2884403d989441341c3c00032581c0c04018454140d80480c00760740031510f8040c0400b01c50140101500741441e095525180544000301000c0c0c58426400510419a4014040680d2600300350441c2030040c00722540c2c0c00c60440b4890003a402844007040c49400c00d80074130300515001c42220112111540c030940e050f400c2c6480c841a00c044000304a4029544c83d40000041e1803e020350500d146000d00c50080400e060308000c0801e0200400b228480c400401c4100465503030502040309803030020075000c0031030200100503241c4001d100302c090214402e41030007100e9103030b22a0041c800702010841440c080ca5542c620b007440d00e04503030f00007907000320f4005500c910250403508041d80305111500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 907034388 1250 907033138 907033151
    0x5030105040902031c0f120908031303050c1905060c040b0735090307050a12110a0305030313112220030907090b100903120908010f0c020f0c0a06050d 66
    0x1d4681d0f1703080d442040000810700c1c1200300d000142d04641c5a40c4030f4810036109100120007542d4803103aa102c01003110400c40c03005034850040c50310030002d5500070800102264100c91f000342290f00b4500310010300b120188243c02c0010f0b00040050145d40c11103031424016400c0c9000781d600e80d650620b400130560312402c4c0b2116804014100e4182d00c01341310354220041c44c1d0300c00381e003024542026500d4100c0790040007140e1701004154a602060740440743c20110040040d0351141c0004c0451084c1e03170001c0c04600c40417042c040305103c40300d00000c42c988584609040740c8580001c3c84101c14088481c00103a02c0050440070034400302d50400c401c00864103a10610703034494548030403400d8105458103034859014010130306c81113031070b403045100714030381258410302030007203400028135600082c00b008040406c0591108a283e0051201e1406000c0d10f1009001000c050340d2490000c11a0b9042d0340c00500c0382c001c00d5442a200413520b25074064014040d020a1402e11806445561007400c0c1405210355440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 907035638 1250 907034388 907034413
    0xf0a17030d1104081009020609060d2a12050f0f07170403120c05091e0307080d03090317041a06011b080711120c101115180d0503010504090203 63
    0x125502c81d100185515903201d40c10101c203945441c201c0081440058a005028405681c40c0020b884401c0d0040703a049596424401c6241d000d00600000d110880980401d0003151084001a21104062640d502c81e480309d0200000d0302500c5041c0c4540c8890501c3c400418070405491005541c0108075003480c1c524424003c0e50b40c1c5411000321025400103090581c840040700713480c050700000314000d141203401d1044a6001071403142c0c0301c08803110030000303c601c203044907181484040c00400317409051f030700030315040c40020300a000e032400120005855100044209607443c01024060b41e041000c40d0034407400c0550000b1030303c901600c142d05100c0b001c40c1c002e403028001100e6680d002d21410005840b03407110b2401420b010121080544140959414400202000242410800c10455078080040841c60056810794500b0100c06001d000e0080c1c0310f1110401c140790b040c05514040c0300c00c5d0300032514400585d20341042e0780e04400061000c100410203803800f40c0221a13110b0000b400c1d0741f110030801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 907036888 1250 907035638 907035641
    0x507030204080f060712020c0601120629041401030b06092a04031a011a0f1e0a09050301021602042004031203050c090d0201032003010602010603110f0a17030d 70
    0xb0050750700144e11040030008490362000010340341c2a103180e800c1d402c2c40e40c807000c80350701c6100502030f14405103400903030311061082c40d8001144010404c2c125031464999044111000c0303176010f905a000e01d040482e20380c1d1120321503024034100c81d081000090a903c42c0020800607201c003804c800304c00740d240b007164103e01c00d0074401101d45010489105686900d50702e44408107540e402c1001600d003e0560041200d604401c1802540c14034800c840c0d0341e1400c2030000f14407103000300f40e1810505062500b0340c0c0b10b000a118002c05034143c0c1030300c80040069480e4205400c0c0d201c0d0044100600084910410050500f038000da504c4418900c0c0400401070703203c030b1822094125074402c1c3c4a403080c503450114029014880d85420811541d10203140c0341c0d00c6004101184200d1500a04240d80c40c0440500c80c03910200d0400c900840a80326603aa50351031100034068200340c0001c0c0c400307441465550f2218a4610044804908080c1400001c0740c9030424040040c5096402118140400c02c440c40e05950303103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 907038138 1250 907036888 907036903
    0x7122a200616020c0a14150c0106060e1f140a0509100804231b031006061d0f0d06240905010e010e1005220608010b151c050703020408 59
    0x1031042e41120a96494000d1401a80c9aa107600580c00724400344100c2a0200308140c0301e090a5a0f0004403002d0000640350620904001083c1546891004161694840400009024100d905850101045402d0b80c400c4420580f600c001c02c110018a8a40050b82c40141c0001001420018140626403021841e200b11000303100300050360303050411013000314000c0c0c1c1e9001004082104902080030020841d43c410f043d00944d401030240b1342d01600666810000380c100d03100070540030311080d0790300d42003c1c03e45801140d289a198040d141403010a08080076445440b03a40200210841ca00c140c0740c0000500060340c00394100e403805510303804011000b0a0290040804240003d99076260102015000e041a0010490b624443d8144034101e145860004140c400440c0ea450205081c01507040d4907040c80d1010300342160501c0b400048602042d400b12a58035815941003400d03c4c88100006c1d982c6c85407012006004d01c001002403860041603100d95444000f6043c0180383c1600c9408203480e0100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 907039388 1250 907038138 907038151
    0x1e0609080d021c0324081603050a0f0f02030a0f0b0a0207082d070c0e0a18061104050307080f1c090b0d0207080409020306040b040b0d030c02130507122a2006 69
    0x210064100606c1c141007180044515440307415090a60540d0b48082d104c42c4c01520103440350380749101480620146000c48944150f000b0122000b131a0146000050481c40364426998850380500040640301c59008a0b0b0310f06501040a078603045100b010748101948100104d0146500f94003012144503080c0c000b4650070b4059003500415610b405604028880010308803800141003511060003040c800c1050080b8546c0080040303802181c89641056074001c43c1d00c038550611420b58001502c140c00b00341180302c007214006580e0194007688080420500031504c0c800020441c6100f0008114500060101c43c40720880140c40c001154a81c842c464000c1c6e006004850381c00400d0110720703e0144202016190240c4081c00102180c0300003c0100781400d00c0902807180350580c0c00115603450040910100d040841003200e400c0c01000141510003404040070114985a41c82d49046042c450301d03442814064a0709043e900c030510708440c00c104420020b8a01d99100c41c106d208a0410b200c60b921811 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 907040638 1250 907039388 907039451
    0x2250e0106110706030c0804020d0f02060a0302040f0e06030a1e020406170c090c03060d030c050d030501060f0503010e06040c030b0d0b1e01081c0203041e0609080d021c03 75
    0xc0b8084441c1d0801d1401d50080042c0361803c0391942c2044d401042c4140d025070125002043c03200181007401c156030001d0402948120300103807609070580c1642c06041614a04034a610415456403403e6103034030400e40e03e01f070741640190341d8030b00020199011451030f01403ca0040d40c596910f030b0301080955655400a40ca40c11884c400a40d038003d080015500321b000c202e9602c3d019081c2000142d0480c403000d08030714028501c001406080c540200804032105901030111000185440030040c010482030007503500058002001c1c001c070130b20600950341600d5072188611503d80b20f100400c0010407a861044050640f103140000843d542d41c0d001c18030321809649240d17428a44190381c11406001c000c410f4240070300020041c410f0000001d214030314a0242c2c045075010441c47d10099255000c0c03a4417100710000403000310340c80142214441e8044030301988178152a2034840207a5601d4011194110740142d01040710090f450340c04207080907884249090008505507a141186103c12000c5800e482c0c0c2c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 907041888 1250 907040638 907040657
    0x304020a0803040303031b020c0f011b080301030606030c120c231f110304031e1406070c03030f0c0c151b03020306120f0a0305031e0f0708090c0102250e0106 69
    0x4403022001c841c7c449034588050300c41e42d0030703d900148038501030701081030400002012180c04003c11400709180030f40c00640040d2203694a2610300301401a1703000c01c68000348500c800048941e41e0300341c00d440e465804400c0c080014106031f031820b0480781501076190210790101203d0300c541c5a0010814007075060100c003014189000318003174904014141503a106500c20001000411512a03500b42c3c248219600c3d0069a40542404d86071000e03a440d41000f580541e0040c40b0380a5007040c0f90300209842500c051011000881800045030004025100407814545513100010001d90008000f5141c000e1b00291500040c40301042c055184220340300400e90000a001081c83d100c105122154900340040044504c403024482d220b0001d14001400d003c0c002c004100d4800700c211030204191680d000030444d5240100a00b8140c007000e4a0b81c101080701100450505000881d82034280071044e0001c1c007115010841c0315000c45104035201030300036480c036000300e0103c0136421100c0c020400c55840703658a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 907043138 1250 907041888 907041911
    0xb040504060f0c0f050d020d060503150106020c010509092a190801170c06030901060b30010807060f020f0d0801030c0b030907060e030f0610090c11120304020a080304030303 76
    0x3c83e00710518032800d2103040d01d00480c100c1d0f8004100c0d99135481040e40940c032905943c02e56009803c10f904a213030300d4003a1a081c1c2202207685903a01e07040f5802da85c220307603108000340d0054803540b01e00017046401400c00e50010f01849640c0244e05c20046000d80755064484012000141c40c1d040400010141745294420303000b0780f58840f1f500e901500110304d9240d048084600c406540710901d99405008400210000300d046d1429445403000342003440080e9a10221500300841055045204101038618010920207525004282034141d03000304000308644d9082c08400e940200c191f202a80443c4100600c51400034000d0000341c2500c0d400c3d0320380c1c0301c95506601d032001444016170030a0546500c144100091110006007000413038200f070918042c800c0c0076902290070700d05c14800e59030143c0f00c1e400622101282c00e110103001c44a0310070701000710f5804070900322800c3e05850501116540040c038580c44c0d45600c079008681041c40149128031a50b074528601d42035810907030041d408640e840e00c45010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 907044388 1250 907043138 907043141
    0x181e06140f01030e1b06040f0605040f060509030703061d010e0303011d130201051b06310507050f041b020c031b01080f04080f0408030706180b040f060b040504060f 72
    0x8000003d0a040c41550700c60142c142c0e40c1c004180e00015882841e5032078182d5074a8030021503002e85211481c01c00000d864117000351007648580305090428482000c001441407061056600c000002800f07068070510315120b0030050440c1c03000c2d40c0305c051440c050310980c25100341706469240002c900516100d40c9004031000e86d1000b1000301c0300231081d6200800400d601d004070007800c1c2543c2401c22640b54030140a500b00080d4000c10010303054820f110503c007032580c0524424007111940611001810412079071406a100e00d03540040c5142e000a03801d104626000b0242030309400c0c05070001902c1c1000601c140d5030449010001c1015822112031704090741021700c82001c048805198185000d00084002400c0300d80c000d043c41000c01858003c901001510812100280c03805c0d003160742c41d02c0c0c0300c0c60b5480c0c50781d211100c00c846951030407980300a95520401000400f0343c01075070b0104645d8881e1910f0810071355542d130407282d80b569240001d1061f590351040d41d008900440d00003d0b008020010b050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 907045638 1250 907044388 907044409
    0xd080f010f030203030a0c080d090b06120f120c0c0402040f09060b03130807230c010314010e070c08070b0c040801050601020a2a030b010602011410181e0614 69
    0x3804901c541814409a00e001086849030342e02d515001300701d0581c0e030820650320300424900503421410301d21010140100e8092981c0a40011a05640b21640848450b41d40e000d480403202419000444203150002912019100d6104000c06580e46d10703d1b500e0018007240d1080c2c126181d000081d58040c0a803500c0c40c41010301616020103441d203035080c47c000300d421241c0c0803103000340301c800700003562007c0280c40d001c0c1014058042c907240e080c00045481450301c0350b610f801e12034002490b120340c50000090074807101d4101ea18907001ca40054039071020481b040117003040d060310b0140007000a407001414841000c1e201d00c7c0302d1074540d5121070808a02d41d09580b009007900d411503110001110200b680028400d0322804881000f0300c6c03604841100c0c3c00010304c0c2e81d2024011800d642c000182e8145c064200b855034408c0700482c034040d90343d0260440d0f0719590f140a5601955624010400400d203980c1c44165840f803042e4014000ca150002e5034015244240c22041400014005079026418424580d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 907046888 1250 907045638 907045649
    0x1b020a060f02190206030a0506010c150f0b03061605090a0b0c0d030e060f0708270307020108060a0e010302060703090e040c05090109020f120402010e100e010212091e010e030d080f01 80
    0x30100c0426400080042c00302800d482007e654650110391568000d000a140c181c0d440301c11b202503885000101801800c2400d00601c80b5401e0459806842c03501003031442c41201840480d414000d00028103c41542081c0e01658001c0c43e031ba44049072106000c00900b4040da61000142201d110b0094002d0030303181007000d0202c0540c0451b06000302c00c190003022035800882880c0c03411966071950010500004c403401c0c4d41c5441c01781a00241100d21011001f480c0007070003078940c80f00a448940520818a038544a034401c2c1480d904014001490a03400400b0242d01a00e03102c80c41c1510781c80d110f158106d050310101c0301005022410005401c24280140c0102203c00d01182030000402070413045100f8100c0480c0180000000101160301803107021461880140101c420420b0004024155094019070030b409880340d0290f180c0365299203c101c466040c40a441d2403c071a400f64840c00d1409211108241841260201005980c404219042d07000b08255030306c600a0500708a1140d4041c01030700700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 907048138 1250 907046888 907046923
    0xc0e04020720031e30090f0613032a03030504180b210d08270703080f0c070806010510050306040b091f0e0108190305040b070b090d080411011b020a060f02 68
    0x1409143c04045069480014043d11101551600c100010723034540f045035000c142c8140348500c04014030040603800c00698030141c0ca142d00740305020340400303880e0640303200080024504010610800a99004560700010484004aa5010100c0000303d0525014003100703c10b1b180c1b48003480e8400740030003002c2c5400e600b9050040403418071a04600084619500380c211242c05e15901d000c266104000c2c410045411055103922400e082d20403c03290790201e40342101d244161140401d002c103011a881d03040750001440440d10103064501a21290030003001180d10503550400c0602c65242c414a4030b2140c5c015440c0c91110300f06034080c3c0c4076208040c0d0068000500350200501803201d0004850054007103401000303460008620381250188159080340b1180d0724003251107401c1246890002d401075081c203041d180000106101281c00031401c54024003c4c05425140c90300302e502609001c081d03500071000c9403c2c0c1d255070342c002ca24002c141c0c1d4030440000b210240020071007030341440003840101440c181c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 907049388 1250 907048138 907048213
    0x604050603070506071407150207141309060b0301050a0b030129150f13030204050603030702012f011a030d0c15020a0e12010c0e04020720031e 63
    0x300303541d03401900645020b084c000031500c0501c594040d03165860009001254503803034813800710a44988105c6021409841500310200f01880c1200b25800301e1071001c0c1058002219080e042c40c042d00c11a10180c41e201c0c0e840c1c41840482d14280240c030b00c10820303a000460820160320030b242c216007550803c04011020300e0030208000141c26044150700c0d0044030004000410554201c1d0302d8403680118001040b000a034814000313025444510849000311010009079a0710b0003450f03101c1c440c0b08002800100f103600c5803081400e01c00c0070f0320440e1000040c41820701914581450848030031003a000c50310001410058403510f410402580c1c0714007540340c6880c02d0070780b41d0740c1c1c6e0013070b0441403004101c03858000c110406400e1043c003074941c102c1e0004181042ea000308a034040d000b00201e0f24030f01d000404a0248170521305046c000c848005034070030000030f00f201c901c00884131403000a00d800350341401804405082a441840c00041280b8088050038100d0025031250715a84402903480703460380086803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 907050638 1250 907049388 907049401
    0x90503070f05130204080714040609020901020d110c04020f071e080d0c021c0f11030a0905040906061a0d240915090f0608011505060703050a0c050304030303050402010305060405 78
    0x8401d07404840e0282d0300a080c1c07031100003880d40a402940c1060541c0d214013640010b000a2001000d21704403020f40702040aa42c80740a03140580c4140c04603107000d03030300c186280c07003910b4425540902d0096540c0180e803000c40c122000282a68800e0360010706c0303000c01096410910619a004400c101070464060130442c0e481d965545482c010740c641d0b00c0701103552308140030405000b480501305580c440c4502c8080c002a01d0780240030042801104000644800518024542d000040309d007250407944038041c449180c54100005044180d82c21078240f82c60b07d074001007030601e0440364501c625884445130340711a4401c0300881203808241147c807051000310002501c4110002c3c44200307541c24413601040b00c0c059105801020740140d4444104030b403070074138410701c8404182d0104095941c0780c3c0090200541d4038003800454146406000c0d4040010068100002d01130401002b4142d05801c00442503611760321820b007181c0140c0c0c42030300825110340030081150b030b1600c42d0716405070b4112020400c42c100365 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 907051888 1250 907050638 907050659
    0x90112020c1509010b09011d0709290c030a0203071e020904060504021c06150b030c04210f0305090406060503100302061605060103110f0a0b09190e040b0709050307 72
    0x9046580440b2400020500840302900110002030001d000d04525581d1140680c0c07235001c0002940000103c01c50201d40701e1441841040210791140400d10500e03100c640d00c48015402c040703103085240340c08010b5281444001d101074840386055070041e54031107105061202e09000103030008454006868090700040e80c0c0c0105181c2c1040d000344000500350b5071803000c1040d5042030124000f060070060350407010041141c202d442245007111042c001c1c60307a1030314004118081507a5400c14075100384030a00c20b41d0080c0020480c203c17115800c26100000755120741007180c414070404d400007140000d4204182c123150040310001c03c41c80c900b03140b9500c0d241c2c08800c841481800000d11030b18000a0308a100300c00300408910640e00f2000b900c000d0b503501d1030001c0d10800041681d0b401088000d6880c0041c1ca0021204812a00188040c0745014a01010000410001c00b0004900d4000410104070f60072050304042c865031082e1040e00e03403424402005000b10a280d03000ca482903100d4001880001c010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 907053138 1250 907051888 907051903
    0x307060e060c220e0f060a0b0f03040b090a08030c120112031b060209150702030d0203090112050618090d02100c090909060b1504150f0905010c0212060903090112020c 73
    0x8035010303031900c009101403d8402d490f860380004c81920038030092014501080c0d507520302a0070211651800782c0d960707668845050241e5030215506540c00c4c00044c0205400c0b4100307540c0081c502c1e007034034081d0f0682d6445610075041502e06282c28800030406030300803031088a6541c054200f01028103828502968020306240c951a2a038907d440030200e540d00300500c0d034042d01c4044200401d100c244504035482000660055503081c0e03c41d1084030f1902d00100d00201c00c03644c5010301a0f40b13020042010300c641c0005428003925054000c2e45e10407041100010380b00507070b03016450780d0020b0030281400c1c0b84000d162002e0007111080061030a4115100960000c1321441160710084002c0740c0c400060038000300801c42510175542151000c00c0079010000c00200510548144203209844044007020850300700c001071581001044048006001542c0105d0010710941e20080c91352003d121200c00450401000752000c00d12613201182c1d510503076800a0800c0d00c616045c5400711b003016141d5404550300d001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 907054388 1250 907053138 907053157
    0x20114060a0504020d0b030d021b06090609090403110d1e080105010815030102070804080d0f030212241305220c26120421210201020d09050307060e060c 67
    0xe00090320070740070384250407006e41d44000609aa6039900b4221010b901c03400101c00c01c404a4080c0d42d108403441c503005058900200010f00114101105d15044c000b03001c1001d40103034140702c9d11031007915000d007041214107411041c6545102d10400c0a689503103520190300000c10074400c00c10018015a64020340070b9902080b14111040409040c1c00400c0c020300c00d2a00142c00ca000000300400c1d0400002580001410f0719078034051034403034680d000c508038081c485d01042c0c010008000314002c0301044060043c000d15a002d68080d0716403c03800542494000140240a90b80ba0010000303000174101c8440e107030110014078900f507003290313946859400c9414022090700459501c0c4a840c102428070310031000c0302c400022115509400c0e20000380030341152249440200c10315400000112103002c424844950001c60b02400e0b02d903032508001e05240100c46241159070038416050414890f000b9503100a0007400a165201014180070043d6510148484e40380d074042010720811103210000c0302d040c0318 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 907055638 1250 907054388 907054391
    0xf110406081504080a09030c0f0e070f023c01140711070e1008030f03060a06030903020d12020906040608010302040f0e070b030a060306021b0729070f02030106060807020114060a0504 80
    0x105d2100944460050340c00261410145200201c0c080802400b11810b491a401e403000103a62002000c9171004212401d40e401a082500d03003840c070000e18040000720b2002d84404a14458180441e0707a01d00d08054110021a9100c1101c4407030b010401020941100b4546003054501c0340103078802c3e64034210389c403445151044000000e26031420b210a0040a07000110076240e1300e50580c404200d03070350420b032a80740c0700c0c2d14074032030014643e0302904c0f64007030309949600540340c1894491070554600f490300c4c104904503038003005100a2692402c1c010000391402d91a17035602541540140030880c1c03c0c0c850364030707060352508203d840f00e0b040005550f0200d448400055640342c0c0da1f251110301900d103a0340002c108074004103650b858601581104807842074202c04440c0e1595a441d40c054001100e035072502d40c90a003005110808290b660000c00d911030098480ea0703500302c03055002c2402c50b03900d98040390019a140e400c1c02862642805590a061000a6190002d08064000402040ca00e21990b032043c4e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 907056888 1250 907055638 907055647
    0x2090411090d150f05130b0601051c0c030b031f06140904200607061a0307030c14060408030301060207240906032f040920090402160f11040608150408 66
    0x6190fa8205404001a600d018003413800e140e84100d00e011b200a400b2621800303041d0001c0d4281d40310710282c60000354481d0411500200050381306001308035145a41040603101c4a002c51070341c40c1007011200d40c1c05903075081c001078a94010301404032403c9411034810007100c1e0036040c941e46c0d2248030f44d9410580040d000444c203007a0503004c81803044260800c5822120100300c0301d06010aa0b070140d0307181d070522001c12280103101010540c964115000c02400814104001d00a007112001105480240546501d107010b40301c4800c40d2458109034800b200507030100078103101141e2091810b5030b0b0110030403100c0c00140c0308400f024010368641d0080408040d51003103004004601d42c420308444002c0d01c11100803118001030200002e5125010310000309080805801007031119007181c4c40680c0c3d00018190401035070b1002c00c00a54881c44039882c44072034074890000407a540180c020f900500c100303400520b540d60141448241c4860354030110150b0410560300c00021900e00355243d00c5a0301201700c40c2e46 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 907058138 1250 907056888 907056923
    0x30b060112060b07060f14010e070504090204240f090510050f130812270102030c03030109060302242d0a0527030a030c030504050402030a02090411090d 67
    0x489208a41c058010750910200040c01d042e04002050220f020b540c00b4080000701c07401080035112482074030010103420100402001c1c00c05007845400040364584146056640c078900e4080c3d82054015420f194681000110f6051004100009585641c00c01c102e42e5005118050b01d5100d091103038500942031003441d0150709120b04122000500084447c686400c8610712600304441076010b0701c0c0e4107118195842d481206003000741d0300100060321442201010f0940c00301c146070b110303040d6a0f065200078800c1000d0043c06001450181003002c0c1c0c0014951b146004214134110044011035482425141d010f150000c10f02c00c8543d01c480d48402031b02600e130603009000c20a8104402e10100040c0400c1e10a0140d502c10000c00000360568143c400c500c1c81e00740d1030100510f0b4075903082c0d4560301220308070300028060040d105099000e4100035040c20780e1040820183c0e4012124083c40560010340d00c00246041e10548036505c5010018505042800c0042145c0d501c204201400c1e98951491030b401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 907059388 1250 907058138 907058147
    0x10b070b070e04110d0501091104210f0308090c01050406090b0306031507020a17131a040e0717150310020702040e0111041505030702030307082a0a170c04030b0601 72
    0x60b5800b001d882003000c0741c0300911040c01a00021a42003080381080c0c00000d81000c14054443c3c107401c4070f45c0c810714191138a02504810961059988800030101682c03001203001c100009036414042c0d125107441d45011485107040c030400f107181c9414403006020a000e01d40c2c2c80788040041d16034045002c0d6581d00ca00001a240801c0c850132000c1d0140d4000404c0749003135010130542400c0c2d10607085103107504924480b185490085070750003118040140d40420901e201c1d020102612405c401020713107410703250081b2242800c421224203000c2030240030a900f10840544c1d0640d840102c11810821681c0a000002c2c0c540c140c5061840b06150042403074003e641c0c030f6078008101108c246008000220703500302c0207290787d0010b07c80c034041c903909200d0140c1d445000703a003100d100c0e6245501542c40d5645884c02925500009046c0c01c40030604030404003802e960040f440c03c02e500b4400c0030140c541c0e1013280c00501e410400801113000103840006d0000c0c900061055606603603001e8107041d441e03960000100c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 907060638 1250 907059388 907059407
    0x607050c101107022107120b04020103020306010c0b090309010e060a0c170408061303030b03030f03130f0204050403030902100e06070f110a1535040302100c050d0b09010b070b07 78
    0x29405886030300000f40358085407034903885d075400903010351702c1943c1d80d008910841c0460b114040c0c54075103a01300090041d8401e038001d6601c038205040c00c0c684081d041e15500d100d20022205000c103035000180ca1401c5680113402400c140c9411100340e4542940d43d44c005040f1581c041005000b50f074000c15040c0465080c5c0140c07405030124000b141c4044c900a800c8124440030990150046490018003000238140072080720501d0035000d0145e45991108006503011000c60401136640150700f03240c840060b1368902a4034050b9010341e6006c00ca0112500401501168500c451802c0c00380d51420b03416241c65580075515995002203218000301c0c81400c0040c1407141101c500c951080f4409404201200403103541c0d4200c0c5d405a90750964107a0740c0f00c00c8519180840107400602c214580903d244800030400c6540c091312a1042d01e1454012034110740070741d5014514a004218003250306000c14000380700700c50074400304860686c07043d458540180240d21031648041c01800d51480014000da02442031403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 907061888 1250 907060638 907060643
    0x1050f0411190215070201091e03021c0c0c0f2115050106050307030e0105070509040c02010e01020301060c260a0c0c1805010e150f010509190e0106020607050c101107 73
    0x62401c108560b500a48a0b06010307042e034041807042d400302c0e90386813052003040c561aa000400441440550f10785804501403542c0840c111b00c034100d4804052540070195207640d80452319119050006d0b07145c03040608509800200c03081c40491410400380305445445030102c0a61100e01c0c0400e02281004498100c3c5c9020001c51a41410300000d81a07600c07034000d511130309080d50100082214050064245c600584501001500074010100385142a071b00c03142400c648d9000000b9210700382104242660002d0b805040031031030041c0c0020601c158580515542c0080e48401c0c0381c0548101d400ca0114000c2241e45020050324900f41c10410100f05270241c007600000c50286003003000034102201518090003141004a220b0b404600700001c2030808040d481001001c021100303600000440341a0031011895900c0248040440c220207035141c0168040d111100404016605015000e0f1034040040c0c030f141c2c2004000c0280300e10080012511405008265801007680d5944400102c060b00840101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 907063138 1250 907061888 907061917
    0xd0b0301050411090a050709030822080615030102071502070507030609050d2a1403090d06060303260a0203060a080312071d18071b050606040b060301050f0411 70
    0x303210622480c06400c103c62841114200c8560b0380c0c038903001013540d405542c6000421103425081c80050400d40242c41c0050441059110180e901003240604241ca40e00150180d00500300f03000b00c28594000780582d41c10260001c0d842d08109940d10490940207014407400c0642c0031400c5800c110b42806240000e5810240c1401100650b00700340b5114040d2400a40118511418034061144102ca04540e02840c0166914100090b5101e500000c0d00706841c581c0e032070104002c092050742c0c500c0c00902145000e44000030f400390851a0181c00f00190b44d10700d074040c3c06141d500103008080c442c0442d40c020041d400c05600d030f45408020400502258000c2c00c000d0001055a610060400004a00c111115500d042503400e20940c650748131250201b11a811101305420b166000c0e10f42d40d6088d8114107145403041c007041d4100d00003000028000c800f25031540000c814008246040d02502c0c442c1181120b2551955240c81c0000f00b180b600394411034091030b03c031444c440e5920100019140b900042c0d002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 907064388 1250 907063138 907063141
    0x20d0905060901061d090a020409080912030c01061a180409080a0512010918030305040c03080c0f010c0203180d020406030206040f0e180c0d260a20120d0b030105 71
    0x20b500c0c003030a5280100f4140e0448000710104648a00151030300800d800c9014003007912050b001c0c8406411503400c261140202009880c040b6142c8004c2c050306c541141c006940c41e8074880908030709460f4140d00c002c0b005000e41e1580c214407200b034403c444a05921180d0030613100644800300d00541080d4001900c400004218100440c3d0040c0003000550344030064101d0503070300c4820000c110384c00416240c0502915002daa00003e020364000794120b0b016500c000b80c00c940d217941e80a8035a1104c403868407960003500d031303a00c404203003400743c20403020319800558107050307143c28a4021561005100d602c14142e6801740029503d8a90000c40910340181010f44d5440c1c4401c480905c04080c0d09c64805242807000000302d4404072940400380100c0808040c000c403056050410180105460b401d0781e00010703501c042c0920400c4000c2d10a580743d40d500c000c6480e4500350001400da0b07843c050040e590181040107642c01400081400102c00b0a0f8518081d200d00040d00b200c00107000c000c034125015841d050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 907065638 1250 907064388 907064401
    0x2011b030e100603320307060c0207091109060721030209010905030610260f0106091b080708090321100512030a081504092d03050d020d090506 63
    0x42200300000c1e8000121a490100402460102c81c8180b01c060500e4510070452104071040d8101c0050710f00c20141c0302000011001000c0b8115070007910210782d00c550319080403003099018030401c001000c4450b0300b00b0211400c0b503040f294503c542002a80b04410000e600740c1004480c00320300542e688101d001130a82442c0d640050001d51056034420f000c1035564000181c281741c001001c0e4407540e00700b40103e09030f5140c070791404004c1c2603902d04031148644540302d60100340f10030040062150200c0c00080340d52894111140102c0d4500c0c0c8003008a10200c01c0401111508281c0b1190031400078a40304032185d8030030050500714041c004101300a2240c0c190ba0b0702d81c00c3c14038060580036218002c110a1602c0e0f403801000708040b46540301c015180c20912160000c2801403041075400011000501ca9501860001808a8180680031640c005d030804441c2040035111485803010a4a101800c00b45561902d002d0030078002d90742c2d0409040e80009041d03a103241709800544c600e0303500908554290030b249 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 907066888 1250 907065638 907065641
    0x131401121409251505210f160807180510020703110109060f030504110904210e01020a020d02132c0d0e09070c150209181506070302011b03 61
    0x141e918569074400d240100e10415100c00403c6903100303040d0200ca00c1ea92414803840854818640110280501481100c04003c1c4000003018a2200f481100c2074500d41303e542454602c501809a0341d081000d0340700700390b002d504008808d802a146040c0040c2414a001a885c00d03e2150780200b600806211901140b030b5070005865800e42e842031081da07080c0340600004684846c00c1d489500001613a21403100c2c10140603a0003c0e0300a8040c142882d205600000030944440c0c05036000c0326070444a07a84003c03e111b40c18400e407070408261410100038034031940000d50b00c040c041030181c884c6411000010465503041c0d010b420ba40b60300e0344280102c90000d2810007007002c8107070300384214806041d841900c0300b002280050060310280c82c0c001c03c904041d0140448010020041014400312141d0356012814105079160102900140507907102c0501d001c0c0500303000b03100396926042c1c416100f03200d203424032017807000a401d205403040d41d2100d210f030504a000d0000e00c1119000b500307405070000c1000794036 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 907068138 1250 907066888 907066891
    0x3030902030f1b010305090a0c06110c040c09030b0708060a0939080108030708040303120207061104050a050a080d0c1a0108060103030905090f0c0d15090b090c1314011214 75
    0x90300c040041c0e47c0c0c0c0084094844a40b40300040400034000720520004d8021110755440d004244119650421840b000c20b040324007e09148010680b414801c004000170340c0c0a65521180d00c4c60b212500b03084c0540800d110850380c0c00740000071a150003540e101c140001e010103881031603d0849030794146100c481c0c0c0c111006207401c4200003c0c8058000325111100000b02d500c4d0700c0d800451940303001c1c95600c040314414003010700441000e80801c46c0c280410040d000c3c00c00d003181d840000703641d030368644407c1000f414441e034082e90007401060802c103c80382c4041190292070303000d8104a03400180074030300b2004d5800070208181100c0300030400030070501070000d10305060300c1c403a484442000e80c030f420400c00710440071115a40d1048001380003501001c0c42c00060700f032403402c002c4081280ca01c5542c5194500446800074224140d40d03042808851a05c01202c0d500314104001c1a0f160803048e9401c9442d05010380a0011159101c0f00c8500c1280d22602c0041e41d04618950208030ae81c0c802c4841303080e900d20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 907069388 1250 907068138 907068193
    0x1415031212150d150c1b0605190b0f06030a0b0d060506270402100e0301060306020d0b040b0a0b21040f060b010e0a120f0530041203030902030f 63
    0x2903042a05580d0800c02a034404440d0080c14880c8540481080c034000b4254440030b083c02c00840c0a030701c1c50100f0000301c1c6c035004584106400302e058506551004020034140c881441c00608000b02180c10307448605201b070f00154103660842e039940d110202d00014041d4160850b40040c0788070b001405022543d40039070301031441101c1180d8586441c49100300c103000d500320a075803842540c0010600519001000d00c1d00843e00c1d0400c24100c00240d00008c0c2112466401501e90f103070006035102c01d401c1c10b84620800d20303400300d90030080b82d4604000b09181c011980a2082c40250000380000c50054018648841014102c001c2d1481c0c6400d140413030301c40c5484542159610b0074207114483c1d941c090310040000c1e5402a00c0d1940b03642c07034115004d04205a4190507606078030908031401c04124140642c01240c10a5000c148841030b121041c0b05500d031618a145420b450b00f413209102c0040280000c8400d141c041c0360100b6003100500019040c80c040b02180031603807140900d601004042081061034104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 907070638 1250 907069388 907069411
    0x317121f050303090f09250c05010b060301150f0c061805150c03070e0607081b06130c0b07020f0d030806120102030f3418091415031212 60
    0x1d90340d0081c582d40380030b1404003030340c0400150170008290802c5000341d0741c05030a020324a14443c941800c1065042940944040000c40c0c1da6100c105011090013001301d1401c09803940c9107150b151a024890b0800718500032400c00c112141c1a41d0098071840041081942101003081880a84120f0b070a0800340b0ba00300703c8050240c0c03104c5441d13100120001510403000a289540b6694812400f11100040612002e130f01c01030511488012658002c00741c54031f130780c071070f0a4070302101e00c01c0b00d90134604a00149402203040e03807803200c040043c0d0404140c000701c0d078110b00d6207915042c403440054101d030074500c0070b00d401c80721010481041c5544526002c0c05000c0980f20345000c41030300700240307080c0c3c031084a140d01d541410f040440c0c598a5a404d40e000310302801c00f404070b810313032015030500a0545010001000648000c00c02c101692119290b203009118403801088011040003405001200080c081004021142b807420307544d40b0188041942440000141a175424400d258505402010703100f080084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 907071888 1250 907070638 907070701
    0x15240f1309020c0a0303020d060e0412030e120a0e010908030c15102d0b0d020304031403012706180905070e07020304090e010b090114040e0c0109031712 67
    0x111441d10858030091070300f10180581000d41d89080d8040d42c000b84018a002d81d5946c1d00141501a002440f40100e11581c2d0b10081c15005480050945000c00a40c58054019612481c40141c4041c02c4a00140180c200720180d05007480050f9040100ca43c004c100500002881d01e600c11404104d503003440a101c80503030159200c008029100c0040c6000303091410080c140000214809403c640903e0170101003018595501c4000841c547e130040303011150401e8000c400e010400d600700001c0001c600103800250300f50361401d0b148010382080f01d9030a22100035a010f06c4114540c4070741000c4003074150311002c1c1e1115030030f075955040200303c003040598440c042d0840c0410f4150141071164060b42069000714280b50403c00c4100c01042680002c400710f650382d0305240003984a001016008040e04050248071010510071b010603100c42050325403190700280b24504483e82c0044c044819a80c100c81c6000e05807281c5000c1d80c7d40c078892040545070030390150041040310000a0b800c2c80000240e0142000903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 907073138 1250 907071888 907071899
    0x15170303070f0e01140f070804060c0c060314040201080a090b01120c053003040306050c0d05150603070c050a02030a0506101a0304021507020a0b0417030315240f13 72
    0x10b883d100f40b041070005d4008150040c02c4103044010b0180e0340050144989888159590a04142d00a030300500125980000010070b0100c2c068005000305600e007020301480004034401a0400300092000341404417040c08142242ca590303102000b40341d4014452031076540c413840362040344ca03002002241c000c10109004605410240e1404542c010090719031500c0d000b003400310380355001c2c6440024a813031000340000408503030a802107600030100424810740d243d08130131f1035a041c1d034030040c02c0d400c1170444480d041507a80c44d040100c030707441001071070807044825041c5001e508042040301e0280d454440e41c01c040c0148072000c10310074090090680300380d01c2607549915480c2480ca83e21038009280c00c09100141c09414070045050f148940e00c200e0904d03081d52940015880706072500030340c1408401107018041d61040000c0c2145000c450340c0154110310b420300340481c112203640c010600401c5000740100300000b444568503445110a040140c541000b2421303a00f00740c2081400d0564081c000a00194 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 907074388 1250 907073138 907073147
    0x5070f11100201113c0a030b040b0307141c120315031e02220c090909020918010603171305011403070309050c03010e011d0c011215170303070f 63
    0x114803800707083c541809000e44560a90f00c01174803070105601070305d1507020301c104a02e003e00e04001c41682120364941c0d48001006080300c0208002e1401203191490074504c41d46c0000e010307422144880101c4e18811a42004140303121491006424401d808035909010880445640b40cc0c0b40a15581001080c8070f0b6081d000d00d500d03d910000c1c0c40102d048940c1d02c1040d84407510141d0700e90003d0401400d4980c4d20201c02c0402c5e240205006240c1d55610141616650124418000302452281804001296000030710640406080e05005c15642510703d401c02c4420b4000100950300011203d07005194454900728a43c002c1070501c96401c0a0b00000c1180d40c000d110181d64200d80072010790459039001c4c0213600070a032940d020b079868440d542a154403079a0900428140c410140008900c500030074504103502c0d900c0c3c3c14603200e0b80d00046080d503c0750345c0c8010384005000b03103a44041000009815070400702e4441e41c2028010400170346942c1c4410b4000401517000d400c8c242d550340c9640050381d00494 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 907075638 1250 907074388 907074401
    0x2a0201090516031a1b0a08090c0901150c061d150a060b040506070c090608030d0501150c12140307080f0601030b090c180306011712040501020a0f0305070f11100201 72
    0x42010802c02000b04c00070311450601a80080381c950940100c009400d601103454020124840006028000b0400b45100c00e1081d00341c545001d581d554075a5060000d50807450791845021800c010140071410240080d40c1c01c0035071000009440a060001c54017030b5661504485c0ca6000103602640007c140d1880403071080000300c6810700825400c0c9401c103820009981d00c43e40095400300b100d40408610b0740700b10301c2800c004041d2a4015661241580d210070192541680501c08540f45904419440381d000f58203400382c1948580308490000c4c007244141c801000c3d41c401070320820300210070004880d81025401d030040300314101c0071002d999440c0045050b00c00810346160000864404101d0710072603400a02050300d41031050348850200c1402081c40d10303100b42c0c82620031303000c9a03907c044504424400040c5d5a014280b040b454207040c200080e55a1189030f40090080900c070100c0c070107241c484c0050b60074940c0d102802d424400d82c00c0c20000f04441c10101058410142d075024002014014030484 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 907076888 1250 907075638 907075643
    0xc0b01062706090504090809150a0f050c06181e0a1505160302031803071a0f090706050310050d0302010c080a090321110319150b07062a020109051603 66
    0x1021804c0906110161500700401c0741d03102001d001c031402d1503640d10a483c002c10745400e0a19203030107010f0801801521070b1040303882070100400075050703c1d481c08245198000031521103e00200c6c0ca01c00300a02d0a040400c1c0c0f00942c038600034800f006076a001c54a00c0302e60740100c2d00c03690403d0420303440d10300b1039000769140300c4803044030003011200782c0c003a0300a507600803d2a042040840100728034182135500c000000c0790120040040f001c0440c500d616003503003092441200038007a19115212590b640c407a40180700034003502000084200c0c0880360740d140940320240c040000500742c0e1a0190192001940200115130402d0010316400c4c0f6601c03540710041c3d0141e4610070b402491070840054070100385000e00b203c60301d6032114100049000d00650045548007c0e4a03048205403140704100d641a184141ea000510f8a040103034250040c159504241c210100180c0c0e2100d55801266465004441c4180c0d4103036041c16640054042d8450001c0034006c10a4440810300009115513880d520b0200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 907078138 1250 907076888 907076897
    0xa06060503070804060e15061f0c111c030e010f08070903080c01060f0e040b010e06090a2a03020a020705030604020d03050a0302040f090605040e2b0c0b01062706 71
    0x140712502c02e0210f075401030700681d0001208035016641a0074201c420515002003150380e0700380034803401c01c9001d0000c51100100c41440c10048420001d0000f05150005440340512a0760500340d9602d8038054100030b80e24009002d162911803401800d1514012600c5000c04c4201510700c4425004d001c44030303c10f1580c3d5464180c17044c02c41e0382d80d0400d0703003017107070790041940da03071903001c43c0f01c02000e400030717024141d881207183e60303442c040c0340a540c801e01c141c100c2c0340786017045014030850303484001145801c00b00c0490b02151000d040042c010508107031141c82c915070742003090141c0b01182c15500500c03400c2040d81c01d0f06d21007078882c030078541d0342e42e819180250000449171192020a2240d03000e40302c0c0c0200c0c1d103005403401e5902c0355000700b03030003494002200b8296100420031261800d44511490180c00901030f200049007a640142890141d5484083c84c000d2000400b0050b03208810fa860255806590360041d561103550041c0041660900901003c2c030000c0309260b0000c0c000c010004891240d070303030b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 907079388 1250 907078138 907078141
    0x6081f06210506013509030c0f0312071209050615130e210c060a2901090504200c06010602060c040e0a1523131401050d03020a0b040309030b0a06060503 67
    0x15030805c10105144507103107050000680882510b11880d0550041103114011515048036400640c145a215254200b580e8410400d4044a0b940b0740060f55010b1854100159000020740903400540b0201ccd400074a140102c00070000c810034007840c0752000c5481a1000e00340c20b584220070340101d449010950742940c0c849507110500c0c0c0140c20324001c68800d08001c60f802d201c0255401450705005075012a601038648141c00703108400c0000178917035071a001c40f0a47d0360154840c0064a0203041d4041c0c240035030345944426101140b80241c0e61440c01c2000b6609588580200549440d00d20a02804006029400c00703d2503d10041c0d098030140d030700020b14109161074407000b2030024140c0d0100071903a010040400a001a56286500e4624900280d0300500301101c50030072010510820010b6202d42c504610416002d1510101d241500c106403480c0801102c076040c1030389821003e880003040741d441c1004200826901c514900104d92040c0c0448506465a50081066811500038980090b0b420300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 907080638 1250 907079388 907079417
    0x2206120e0c2e05030403140405060915040f0e01030b0a0b03150603190303091406010b090103090807020a0f0e070503042a050603011d09120406081f0621050601 70
    0xb550081c003a29040e1105040001e5000021100b503a22804000c40c90100802080c9500220082045400340003402c0c80c2a0424001686c41c0c00f03583d0760b05009521081481c19641d100300100c5002d00b5503080620607890352036030016003c48090004541c100f0012011917500c1300309004d0060f56a0740140030344241d184c41205a0f1008000420990380740c030800d41b00d405581a40c030366094405000303903008641c1c0081800c010b280000001d620707064035031242004011401042054880701d69092174040b50f450018200903820b8010608081c0d489014840002003000109501000702c2d900b1400340603d6580b030032710550320f40c00100c50141500600110010f103952680d01c540403c409841101d81b001c948907000308459400980208440f059001505005001003900190b4010305100c000d100c60008404004000c2c0254030400041c824a20003144d480c2c0c441d04456042c04050241b60758240b81e956400809540c03403a10b03002c01054a600114089036818014036104241c1a1100c516121405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 907081888 1250 907080638 907080649
    0x1005010e13170417010510211b1205070803160f050307050604080a030b030303040c06031508010e101802030c0112091505010303020601081c0309082206120e0c 70
    0x1400440d58140b000b21212845200c04001e00007070095080258090444840d007142156030250080ba90203030142410045180209100412016440f003842d604421900e003080340e6059202c540904080300100108020718204c0741d44401a00407403c407022117584850107a2070344110300079076252a41c22041000440c0252008e007a0841c420000c0701e00e000529180d5a00340035059a0440c0c0a110000c0c5a46a882c3e05004509000c9403c50207186507080550311100c056403117110300000c0c10385074107200320900b00c0591640c0003021080d00921509402005040d1039880800030324003e540303026402c04103604101e100703e240c150701500130a41d00001d100103643c030701c0e003c50382c036504103880321030180c005541d0004120b440740c2d0203003001c1515411440d01030b00380041600601803d0344628000c0d0584000d1100c1420691810b060000f5104140d0421410740d12415981c01482040091492080100d41070740380f0840e0043ea880741004542d00322070300c00f6610007080c5c0404950002041c0c00052600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 907083138 1250 907081888 907081921
    0x80c071e050303150415080a020405062b03031b12111303050f01061202060304060b0f0607051b0f010203040b13030b09070905060105070209072f0d021005010e 70
    0x540e14040403211a40c81a1071548122048a00301c0c00640c0003200905207401120000850000c2c00c42c2c200c2d00380740d0b45a5031a612444040e2003180c5503030216115484030440011b48001d00300f50f0010040c0e0110701302660070100c0c2e20440002c0e01e4901c0c590b0007440c10700d890341442101a652040f00b0300c000d10156015056503006e2041d0b900041102050203140315081d8801144100003804044609491280c21581c144c0d1045420b606201d4240c001a640c1004030ba42c02988050002610318421012841192003031080d00d420800c0020102d00f405000250300341c0002000020304240d2555a0a210750048000c00d00d50150b4020702007800403100d205c01912403640d2080c402e504690341c07a11400300c400350643d244015500040c1017808001da83d0b00420382e214000b82021846c00c545540031031942d0600518110070442c0001d840003070040e045d5080c100031032901c841c3c407003581342c455101c0d074031a107034080414054451217400000d2983c10780503007812a8401100e040c0c1c10795074200b041423a881c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 907084388 1250 907083138 907083173
    0x10908040302210d0f0e0d1a0c070b040809090907050604061d1905010f03140703050a0e10060f05010c05030405090405070b040803301501052704050106080c07 70
    0x3c28240c00c100c04041041034800f0980c0b03545d9564040750340b01d500a4146e20300b40002c540201d00b5407050f9000308101000c56042c02c0c600e581e040da416928010048540e0086c802d0081c032400d141014001031011100180c60903401c120b6002c040d03500c50b4000300f60344962500ca40c80e085642444100025405082200803e45000302c0350030000360a003001400280d81700320a000503008140042c070107940d0050424108811506041220704840b03068004220001821102019120800146801d0341c03600840c000401c080300303d07544171585c01400e5000e07107801d00600c81011200000040c0d95071203180c21003403140d040b002461505d81001e0a1141e940c80003081030b1554424100006407811061000303200408409014540703407c0ca00766081102c1021202503404a41e0311032010b8030b94a1200c0703103075400503042c80310420744500000c0141d41901420003018051207140c0c0c1d032090f04036485041d1001900044808121607038840b807080c1c1308001c098446000ca541c00b4800702c4005400d000300005d0610 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 907085638 1250 907084388 907084429
    0xa081801090b160905030a0f03032016020a0e0a060302090a02091c0c05060c06060102060a140a050a0b030718050f04170a020718020904060f0501020c0634050609010908040302 77
    0x517140c1c0701003880d004a290040765003102c048043c00034107034544110740f010400022181c0d1068902580300d007840c01520480c0100848462040086523212206140145a0900c0440c03440c03420301a440014125440b040c0d01038088c0400007490100603108a440000e0700810359506800348408207040511884401c031840300b0401408509965580c02030183c20401c10001c051a24200d40020300308039020380000d509034185502c00b102015410003035644081d10b603800040541e18045400e025240d40000d00340c050107800e0000c11001d0200e0f400342c01c0c071601c41005001e6030b164240205210307001110f0240269482c1e00c00510101390100042541456070710490b40d0b55a00c1713000c07510345620340c40c078401401980021a002c4509090082c400289200c0c0003500306140303000c00213502d980400c001c2ca4840c100c0015a601a40d00101070b20904a24141c0f401030088803140e03141a0002c1c0c8468291410711440c0001541880c05004122180394001c0b2075034282440c0d5401c0c4004c05211541459040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 907086888 1250 907085638 907085657
    0x33909040b0f06183d05160b0709090e0f0c09010e04150e0304090c0e0a06020d030f0608010c050702091b07021002031e19030b0f0d0503040305030a081801090b16 71
    0x51140c038041c80740d90240314007915030714480200c040c80d544034422029811b1004c1404004140541e040c014503000360001282e8845e80d0321500d08881074142a0001c005945c074000328034040c50000190701e02005909801c076445200790304200145607200b48104251102001c001030300081a690080b00c11001104010511420200842d4259041508002903e603036546c0380e11912540315038100c082c1c0b031003600c0301807403070f130400100139143d0200718540824584c0b100c074207404a0106070310100081c0140341c000c200a01c01c4c0d220003021035202d508241c0c820b290300008200071205100e0500d1490711840d440760300d00340d015400c1c055080c04091b0140290b000c203124441c44040340e001c04645d1034445400c120341d5071071001108000711140b0700e00281018544020552642c99017080e83c0c0c24401c0031540d10190030800d140107032542c41a508010164040408c804d00d5040c1c010303c00c1405440c1c0d041c04032550601e02d1600a080340c581d0440504801c4c49200880d050300700703008600f02c0b4981c5501e01800c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 907088138 1250 907086888 907086919
    0x161103070b0a020a090b09010c0308130c0305010f0b18130812040f150e06191b02030403031d0102062a070f0b0106030e03033909040b0f0618 62
    0x1441194218a0290005015107605030b0105c980e0000d0260808907600f0240c0d100700003046404081c400406018614003c588104860b0b84180c08040c0d000d11004842c40c0c5a00d0114003074865407243d106d0b402d050420412092921840305400c079404d00190100701e035500c101d030050245a41406844400c0100494141030841c801010b00c2140103694004102030b030703032402d0000c4021074200541f80354500b0220309480c440109010350032152071010b220340b4a0407285042c0c000c00c1c440bc4548606500240b038100403079004409001143d000341c441002c041e0031074140044500c1000e8080307005801290002d10300200311001d24203281c4040c03242c0740700c040b803003124a0681e91001e0302c15100a40c0701c04075501001144405076024201a140a0040c1001e41081c10340da4000900303110003000041d040c80c5000301042e0104180d900c82811210745031035684110301420750080300c50500a508000300350f03486081880440e00400300241070a0f26220810001c40c8030740140022280d44040c54600a640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 907089388 1250 907088138 907088153
    0x91b060d0c1d092404022206110105101511030a0917010b09180c030a0b0601110c03030301060c021906200604030c0308041112160e16110307 62
    0x1c0301d440540300c500100d005100c40684080342c80721000c2c895400041044024140c00700380701d1040c020180320600c2c01001000042c042e0180780039441143e10010030105200340480354600482d0455125003680d6022481040e098038421030302469050001e4008100c96541c015045620044a01e0f100749500b0414804509590144100e0307000980969400c0c003405424082d50240780708600d00800544500300d01040c902000184005202d0030704008043c0030780700034810b81d048071400509a5031291185c4c039200404180039210b00d4005034481d0100c040e0814001001c503a0480700400039421686840f40c129544101a80102e81250417410006030781c01400030704202130100b90f102ca652544607202000070a45202407080502d0f40b003c818000402e0300042440304143c0c00d40303010038283e038076800c185041011901003a50007510f086041303003407110040303070200000c045c403200c0d507503620b60318200c1481e04070081d1400c000c20f00c2d2015007000c04900941080d0121032b102d038241c0c3e0a050541d00d8010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 907090638 1250 907089388 907089401
    0x9050a0b0402132a05090901060309030903050319120506010801050907140c0a050115120609080c0f0a110f06040509150a060905041103190509012702040c0503091b060d 74
    0x1c4140034120348003200d0a0108004c0d5100f115036207041401d083c03188001a04400c030620440d8181640c5010030014180702d001c07420051600b001c1180e42d00c0802881402f8156450101d040018280b21580a200c05c000d004460144105070f60f000900c0c0d080ca4100441110302410940900041c1420401c0450000001e4400381054401030300000581c1d003003241c25962400310404040d498103006208820310304400b8070740326401c2030001036140722a2801030344500c61802e40c00c00d248a035402c1640120300c0010744d4110b041c4a052821112170110041c0100c0365a4808000d0788050f05103c28422410b000342420341c40a01d003807849417074000f44004504070010710781000000581e01c600074001800c00d13004c0c0444d41c50242e80c40700d1840c40d1540c1d14030428040600030074901c1c0d03203807004100e00c220250003c0d10358803906d148079000350f40820402d91540044c60b0303049014034280790250340071314003803000d40b4401d0384140042c220300c0c26542c0d0f180720400000c1283c190312040611040544c40720610911 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 907091888 1250 907090638 907090661
    0x3020f090c0732071d040b0a0c05090a1509141324060801090507020d0c1b030209101a0301060212130b0f071b03150b0d060509010501051309050a0b040213 68
    0x21300c1c1290505144400922030f0b01050b034400708041c3c0c1403000280da44840c859015815140006144480500448007441000041680601000404180c9000b100c42a440030f98580e240d090f80d8942d1505400030120301550125030160541c40140c0c00d105040d000b0703115482c050b4070980360103c800c6180300115070103904005c3c0051441c0c401480000307001d200f1a0b4000c40ea50008088464000700003c1028441a02c000c0c01e4000340c03c510000403d0600d2180061a8000c0070a5101d2504500581860350a4840e080242e0080d9500442644612044038169444c070380c040c0440c2c43d60004803642d00d030b01108003041e40c03400d440c20015804c1101e401030301d9944030010300c030740c0c4d248060b04103102164458141e840724500078003010400181c8510b502424001c40000108860900a00083c0101158400500320500b4139041012002c810362005068078021617507032940500381c44111040700e41c2624018415480001b80c100070a085108050303005100521801c20207501e10112030966a042c040b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 907093138 1250 907091888 907091893
    0x111010204080c1e090c0715050c0a02070e0c1206120a1101030501080c0f2119021f050412110612060a06021908180a060903020f090c0732 61
    0x1aa0000e2801c6104503440160740c80030301d502c00e4a60000030351700742c8019095103010b080004800c0d04120f54030b0100d8041560856081101d80f4000a2070012070f40b1100101005014050000c0ba040c800c08800324065204090030506220046e80074044124011303021944c09241c240842d982030008100c6400307014071032007a0100303c160200015003951010b80111201c0d030002122807000b51240c2403880341d90b0078100c402042d000e40c1c05226030242c15200c0c20322500c078003070103d00d050403030401e40e8810b6055100303039418400d03191a2101c51440c1e019110398a13001450400080200028051131000103c0c0100d0f03a0702d412044040000b040c1d580580519000302d5000001c0001902d44410004000c00c071a0010f00300540e0707014005070340d4080040b0010401c100200300d0075000404000500c170150320140c0609001500c91101800d201d080f480101e2080c00b0004030100303a8180045485e000d68154620742e81402134507501c40481c051600c030800e02108402011814154120b80120b1462204c00003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 907094388 1250 907093138 907093153
    0x1b0812120f0a0608030c0115050906010c023c150405031207030302130303080f090f1203150d05100c0c15051302190f080d090e071806080f0a09031b02011101020408 72
    0x523070010300704045e4403951041c1c1030401004542d0341c100786041995076040b510440c0b00782141a2a0b10314040c810004407007103500342d105859803140c410a0508041c41281c0d071b50300b0707401d000d03c50607074921641c001c0030f8041d0080c404030064484910702500e00148242000350038030b111200c0c0701c000010180c0c8160b0008642d0301c14009405420405a50001103000c0580000d01500e00016560700ca12021800c440000000250843c410300e85c1c2d0b071007000c41c010001d1861140c6810425a50f14402e000b4003402454101d1400c1014080c0d0041d2034480e6100e4540c100c628a0801113000400d002016804480d02e43c0c2400001a0794040d40043c000c203442007039042d40b50404076011209100c5420549855100c84014000306400c10001300444101850760174407644c4a00e001ca85182002d401036040b01c89804000c1180c0b03030440842c030b01c199000750380c240c41070303550341b082030b0642c3e841c01d0000d030106025161201e00110003039981003034580103061403100012940381c0242203034002e40c0920075039000030b1f2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 907095638 1250 907094388 907094411
    0x3030c030604141014030705060f12070804030215190501090c0e1806100c050d03020d0c021f0b01050913060602011518090f1b0812120f0a0608030c01 66
    0x4a030400030820340d04040d0783c0e440d0103c801140da10480c0107202848806180061040d581080b60201410015101d180c44d109440450b4032039401001e242d50307085e00d8041c0000e409a1041c07140307512031601a4010321114884040c2d03240b503142e001d0000600c0c41080c0020411030113683c09128004e2803500000034030f82d00481d10007003c1c0c1d14403841c0581f141c42d20360031245004110f10f40c2c4135006035085404507141900110191a06100100001c029020b183e00444000350954003400303071108400000d1044450200040382c441448210b00b49a82d801420042d000c03031026800345005070818101540b8014a02c000171fa455480030121001e1a6102e24050200d40d40c203004d01201030f0201c82c66412218100000c00d260b525071070003403404450755070740d0340030510820301c02589026030402c05400750004108031800580b9a10700813203000348070b01c54074100025044022180201c0f514070030701041741c80d0030181c4207411a000d080c038504140c50f00d1020030000000e1005082021a00300001401341825 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 907096888 1250 907095638 907095641
    0x30213170d1103121f03050a0813060f1e09080708010516050310060f0c14030c0d02030f04050904020f0301050907060f1e0c0f2103050604150e0901060803030c030604 73
    0x941c0c1c92500e58009008600b0700c820201c16150308a0040101a0785c0c6110302000304030590455440500107220350400b034004d00031820010009880b09000580d0595107821041d5443c0e10043e04010001d48400c0c803503a4146901051b051740c6101a1500040690742e54241c01d19120381d6800c5805140d550308140007240712441200f61541c01e11b410820709600d844c044a20384080184583d405025032240070140a0344104217013854154822000700f1861544890180e603500600f1700000144100d0222030422400041030b560700741e81c1e0b06c0f0503d2825003410f05101d08880081d0040740c01a03031190110000796400c1c000c4910501c8850001e2a00d180f4002c0e0040c104405141d00304240402e858001c0b01d5100c104540d41d250828a007800c940074000c80c42c1018542c440c1d4a4058134054807001d181000e58011500001c500b16560350501498803040c0400003100c000c2903ca001c00d02c900701c400c210034040821425488001d540000a046503910714142c19603208a4450540800000c1000940c1c90326 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 907098138 1250 907096888 907096907
    0x6030717011d0612010e060c040302120703110409020102010e1b2b11030f0109030806031002160f0212030301030f031403090c0f0418080a0311030702030a030213170d 73
    0x1581440b08001040b44000c910203200034004a0081006600390036500e20250840020f042081046450b18075242c10011f1442c3c00c80e0100302e01c505120041d11060840000d542400d0f29000544024480b00600821004280c076520803030541d500c40000780120503040c000c3c400e50098440440392078001140c200294440010300d01c5007040100000546070790034042c0f41c000c440307501200e40d501c0d0240d01000030f441c040b07081551040541c20411400d0030103601c40007190180006408881410b0300982104c401e078050072102c0b00c40c1040426414002c644100403480740035001806c0001600c0559803064190340c000d81060310100c008074440001c00da400406c00c58641c15140b2040c2c00c1d420010b00e000d07168054045c549220b44c00344012880380303594650004a0110000c0c05c940c0002a09181c10300b003d8200d050320901103840c00031030b0b0703c94062840031248121117580c05145080c043d11825802034202c00f00d011031f034030904074020031800d42824141004258420041540c010a1100141107222 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 907099388 1250 907098138 907098149
    0x51602090a0b100c0f0b061c0c03050c0a03030c08030408090d0b1e040f24020403060e1c08070f030603060e03031510020c010809030c0613150501050901050609040b0603071701 77
    0x82c092010320200c1d0040a410201d21b510010700c40207500e41d20b001a103025404103c140d1304600d081c440204000140103500300712480b903000c0e240482105010004c5502e0548000750110b074041c1101000140944000d5600511900b02039003882d410401089400c1280742e001c94100381990240480b00340841500a420003444610b880189805c2c0e0345c11401d1840340703900030004506100318220005c440038880c18076800d514021901c40c0c1c0d0341d060680107456008000076140c0146543c04005507850030305c000050040707440385100d945454004032400202500c0e460100340d510140400050707114061001d20044160040d81c684c01c0400c004014540c0c6000410310035140900c000300801c0d00860383c24103812003401e2442d0170b82d4420760102c2c00c52080100802c518001c040400c1010100103418031052400707040d18030740d507070341c80e44029045038000c0c05041d078000341d000c004204500d0840020300c0c0352140540040303030b10b0189a003c207165030000d070340500102c3c109400150702e004440d19028010503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 907100638 1250 907099388 907099397
    0x21c0e07030c141305070e09160e0906010503071404240f09030b1b0f0301060c030f0c03081302270601030f06030209010e100e040f0204060602031207051602090a0b10 73
    0x103d8800040c4200b10b00996001c030b2607803203078002140c0320700811418074002000b52000d1043e03e009080b122980580c1c1c0c200e440407458004940c00c45080c903020103446400180c607410318584420105a981d040301d6642c08a10481c01c11010901c01c0500340644481c4050030329a0411401100c400390000c140c042021040110b40b4104001240030400000c1c0c02080c1361409541418980c245c5501900c1190070f50341e00701000100000d4080c2e80599200d400c80d00030303500d02c11082c0289104a60034140000003500081106001c504001d1039a02e6070a00144010982d00e0714201e041c24001c01c0002c06220450000003c5080229658250080602d5a100028200449030459001800d1608180160180e13034000000046405e6140b602071000340c011082e8540d800c1c0b6240c0341c4980c4114400c0800c0740580d00b4201c002901c1030000041d580a80b91140220380d055880072001c8170307250841500007031078125000191015880e41c5900500501e00c0390408656070700003070300b071110140801c0e040c0401c11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 907101888 1250 907100638 907100669
    0x30b040507120e010f020c1509030c2104120c050f010207030b1b040b120108100b010c140120250305070b13021c150c090504021c0e07030c 61
    0x1158484a01010b5545110000076511560100140101940b0302d6500d5100e02c002240586400000740c410507100d40c25801603003a9407030600b101d1b141c0c0211019400c2960140c01c000c1e17151246288401080719000101c18141560751501a8408110203400d90300c2d54942041404141005482200405004c0c002400d81a00d150344003001c29100138085541600310038041d900041a640c118ac5c0100070100d83d403170304d8006240711401c86000a02c501101c51050100c10350000005016510b41004140c46240d803180b040d484984a030400e242c42c00b481956140c2688000301c5154807895000300c422000aa210041240361140746c102141000302000c49070029400000d910034126406158005041c4245407900f103000950b509803480e00961000a909000720191509040100c442e4055030f03981025006940751107003100d6410310441e002540328941440581840d400030124100d1440000b503082464410390710403144a51101000798126007030030814010700e001c85002a00d45840c004104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 907103138 1250 907101888 907101901
    0xc0d0206090d1817070f0e040807021003150f030203060c07050c01140c010c05210615160501180c080114011503230108070b03090312040212070308030106030b0405 72
    0x703a004502e001410811441028490348030341420320001086043e0b02c400b4044000340070f10b920f50181c0c1c0104111000e12080000d035903000b108039a0301854110300c00c0e514200554007030114803000032000130305250300c81c541c421000809440b000018440c0070400b081550551041500340b00c030140800140c010288000408034034007145100c2c150509080170340d501c3c504084402e007107000d81034040b0103d518128680071403903009401400440e0382442c4400300d07040051540d0241c8402507c0ea60b030404134024a401141008030000c0211a5640e0303c008180c0d0201c1e0345450954004003c04c800369090951039000f0450b400d68008083c101020080c010104812842c1140000500c10b903900401c48c1881600428003a0380020100c0000210200e040040001e503150700b0402803086184e94816010700286480c0080140c1e800b0301e0150f4061840d148000c01301c03c028100181050764058920080403401d010100840c1000714800c203101a1a58581407014040307850301b0720030500542c10503040000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 907104388 1250 907103138 907103143
    0x607020f16050d02180a05011401050a020706180902030928050c150f180f060909010b180303030f07120911011d0424090926070204110c0d020609 64
    0xb0b440c81543d03041900c207214000500041016406030a03181d0180051154051880d00864141c1d211498012225101040119500c0c4100c880900041c0c120b14014082240b00310903100ca601d4100500081050711611402c04a0340192210395032580003140000441c002e00800c01c0b07414418600e2005040c0c15511110703200c0c0c4d4403204251060320f4200403141c08006400c00c0d504140070000c0400c3c1c84003c8403500b02909108150424807880d244182e6502914040d42100e03032205001c0c050840c0c50b4680055502039821940b032080b9521110340021070035403010000b5612501c054203184032a130400b070002030440c41d07a600d03800c21018100820743d004a2030440e0000c09404081ca010700314410307145c07031000c030b501c004400159010f130900d0401c0315202c1110100c0c10548810941c00c84030f05a56883c26030466035000c5000740442101003e880000004502940b20030121165181c64039205a0003e0304448103d117121102a402189134409100100305521468802c0d00042c1440d0810039203455 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 907105638 1250 907104388 907104433
    0x20c03100f14130308130c0e04030216080d0507020616050a0c08030f090f01022505030f062a040f030c08060a0c050d200409020a02060a02130b070302011d0607020f 72
    0x40c148100c0d08049801e005041da1006c0b07100340c00c036055500c09038440005000c469000c0d10241d0051041c000300c0c80c200000c001181c0b0884103100300415001c01050001e0700c1d036402590069074071180074006040040050b030321606400344250054040c2c002d007894001c2c059009600283c118ae4401e000856481d11170703900700c031075034101103985a6a410309440100d203030003a860180c1c0d01c400381d490700d4071140880d8584400207131081103055071075880013803d41c1a55094115604000c0101c201008505005d4801901614100b1107020b54542502c0d41d01100b01000240c0c41100c0860780600104170742c1c40244121034011390110014803500c019514010600e00580c09080c0c0c5d102d655289281c8202103600ca805000702042c07204035160f55944001c400290440401c81c80513014242c0042c0900c02c032442100c0e01d100b61080100081420f20b0007850050b04020022000e5668800340804010b081d000b01196035841c02004021031320b0700302c2d4002e0810275007581d030014a900690702c00042c2d0301d01d8030307511 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 907106888 1250 907105638 907105643
    0x408070906030210030b0409060c0207170c0901030b1008071e170c040e0f011d07050933061902070605130e04020411031911070b0a0c020c03100f1413 66
    0x1044146c07010300081e000703000c50070380180b01c80c4c9014a000112600840c03050700305c40700c103190014524207c0c0ca1060f1602540401d895012614000500001e02d0301c5004980050000b501c0c4034030540c561088515101050304140c08403820b41c2e50f080d0740f1094941030400071744420b85221a00c10401c541050740c49003800403541c804c9484201c441d81410f001c1080c011010f090400900c048003107101395400125401d60750b00d040e4011510041068141001c8072401a41c0d2018981e580031014405842c0e0b1895800b01500c204d01e5040445809a80301006456131050036540f0410b083c0003444040e180841c2d45c0d01c0030003070020900401458485030f40c00c1400302c806440508000781e4442c03000900621682c0c0f00048840408400e21000510611000c007011410701c02c100800103c2840c40440b902a0601c021728610030303140043e48280d02500005003541840c0110b03908079210750b0001e41007401042c0b420b611240d44810300220f42603036000d8903a2454000b844904542848195901c9003405607001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 907108138 1250 907106888 907106891
    0x605100c1e242003010e01120f20010908060603030a050c030c0a0b0406060503060c090402090109081f051602190f020a0b07050609120405010e010e0411040807090603021003 76
    0x4001c00d101014501c00c484825824500200a200c031641c0401031070000c0c400ea44046112806001000700711040740d040e42e01820f40300000368039003461000328952010044600b0f4048902c3c89001980c20144100d51080c1075050744162200c003000100b6440e81c95001008660040062004a440c0881190f0201105180260740c075038040c0e00e064518458040f80e41c0591244041d018180301c007064030580618890745007480b01940c0c0380100740e03640c1404d480701e01414000704aa201586400d900403c80d18030181081030745075503590b8030141401400c5200315040c0840400b5000b880c11140720352603000d400d41d5038081c5440d090b1180250355441410f22141c0001902142ea424858041c108020f096802402e100d07220fa100c41c07094000c0d070005041110319209040111b80d240002144591112504d2020305003058500001110903031031500c0c0040c18003076804442c0c886910340d80911042c1d10515042c2c10380c1d0f18030704402d0a2400203c0e9102e210784620b00300050006a072485281c581a5169150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 907109388 1250 907108138 907108193
    0xf030705090306100f530601062c03100c1713080319020a030b09070302071520070b06030601061403010e07030b030a050109060507140409020a140d0605100c 69
    0x180e0803030f00c150a041b49591551490740c0140c10b10420310207612540750340302d460b021500640386030384e50361a42800341d5401301e84040030341035446103250b000030b41e88255001003000000204000c217080c4500742c07071026a07071500c1e008041481030300080400e600d03000c01107a2041500d8856034802e00b002d52071030f004225490000105040c1101c074416004018000d41046680310b801c01c801400600060741c0c42c0c0e00802d41c0340700140000703010f8825601842c0d00b00e8500000d180c0c4000d00301d0010f0404184200c1e840c8046050203a02c8501c40707002d480f03058810f002c41061400c0620400d0300d4040160321800411541c035508900400940302a00d0441d42c00d20035811194a074003005030044c0c000c424981c1d03011712136580e00800f0700005401000020b8000c0310100f0543d00c403050115806d03000e420908d0000d007010070080000e145150f0003230072204200d1420603103900365445c800049510056130914070549402c0c06101c24508000d1817807540441d0304203000210322603541d034100030510a0b0010282003140c036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 907110638 1250 907109388 907109429
    0x606090d11010e030607050307094e030c0c1403031c0908030405060406050609060a0b030408070f080a02060115120b010e04020d0e0606030309010e10050f030705090306100f 76
    0x3d4010319881d004040c1c544510f09100004c10a40080714110001014820002403d600e1100c0c6203c5481141045d02c00001c070802c42d10700c0030307040802c2d03030004072540100b0385010310742c0c82e003203078002034802e0f642e80045030414204510722240e29000080b14003d6018512202c0c1d0300002210b407c48148288127605a40801c903000080400010240c076200002040000b0004040740c021b205600c10401048142c460070305100f0303482d40031920f15401c03040201c1c0a2081c4000d810184ad0710a01c0381d441e0320f240440325600c040c0c1ca5020b40c00d04960038100416002c02e460b4050155501501074015081101100c0000060004013040c4469003641e0391026044080d034410106950701c0c500c0a041995a041c071b00c42400020290521500c196010b8038002c164a0318001c0111148210140d42d4080e4054844c01040014038545c0011418807108010f005e002c204000b029510844041c1c4695494802010070715040034001008001496020070040c0300c0c000b000445202901c1c8402c10740c418814140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 907111888 1250 907110638 907110647
    0x60105011d0406090f0c0e030322050604031a0a1512062a090503070503060703050c190c0b010902070f15090b0f060f010f120f110c070e0606090d1101 66
    0x8030400e82d040740c104080483d0342e03010382c0c01c0b00d00c0c400c9401c2c0c010010b8000c01300084801114000446a00d44c02c100b10307180c0885102038110011780920005800e54958400001c0c090b135001350700842c0c03140364520900380b020781000c1c1e009a200f00711490a015100b581500408015500d000b0b01141224500c11101400f60700d80c0501070b030f0900c810351000c61040e004440e1a04c803440c0c0303040c0b00028a81001c0415207080c0071030030070229400980240f0742d41d190701c0c1041d400350000401c42003007281c00344003034101e664050051503140c8416071214074000d011401d1152203074005801c82c0b01c2580c010003c10001420103038074028415005100c1c0c0403d03221084031030b0094001e8050281402c1e0b0440f046c171000061000b5032030302900048801c2078401740d0703542c0150364268140100c9800f140c88286080180300b801d801804006400c01c5001404545903000c0035050b4105480035041079014280510840000d440b01e00d8201d40100d5080b4140186a0009408400801401420602d4550000b0141d9004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 907113138 1250 907111888 907111937
    0x105040f02190305010905061e09040201030b0a060305010e011502030a0c0309091119030902060a0e03070e09030c070b090d030302090406091b020613030804031803080a020f070905010806010501 85
    0x494041c11844184200010f0190000b0b02500840528040c003144c40d80c070348800c8201c80d0200c0342d02e0802e00d03175840000304180c54200900607030502d03440d0740c41c0e01c0381a55140c410401805081d1000039095040c052400c4144005810030140459a095030080f801d400005440a0f1049842e0460746d08807240f401301c1d04200e65510009055003032030903041d40e00442c00054000c0f8075400c0c14030a114214420101c040d80c44001001e03411920811a83c1c103224402c0c00400700311400075046444c942d0f40c812841074514402c0320001055013010680094046051103040f004040c0598914141050f24000a6030310313071345200040616a001924a050352126040032005290b4410704014000304250300417100f000e1041c4600041c014540004c0300103100020b1055559010b80c0d508807103903950f6400740c0e911202850305003449240c1400000c00642a0801010700b40b410754080c10160b01181011031030005a130708041c50440c10030005000c0c05d000024690304451003480c003940056074031446d00120b140c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 907114388 1250 907113138 907113157
    0x140c01060512071e0f030b0a09022214060a0618080a050703020102060705270f121e0109120c02060c01060b0306120a1511122e08060105040f02 63
    0x68429620311542d80c04510302c0110303101c070212481c032400c686850003204105405409000411020188081800004c241c0e0340a2602c1c000016402c0c05500055407070798a42440c00e85d14120102041d0541e8660700424541c050220404062400d006c03000820084443c0111410071625401e122030381c040182c0020300902243d0103881091f002420300340e864076110302090380076114100c041603c1600c100201d5a0f00d03442d4441c0c1c40202600300c8515000c250440c900c59900210036800780200356030b981d001002c1415004020000f4144c9001c050a01d0040000c41c4003059242030313068030200b1000e031581ea404c49003918004000c4009440050a50f00401c0e9600080d0361038014045801040d01c0300542c01404101c9000740f4290003240e109588070307881c9000604500e0681c01c19081034003240c004e09a2412041540d41c00c0c058200c040200045084900d429043c0e030b00d482a480032001d24181d000a04010003400700d100341403050b240d544031018454035001d9585d81200d940c284043e541034650012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 907115638 1250 907114388 907114399
    0xf050d151503080c10050f0408040303140702120106061d18130b0106051e070305071b0801020d020405041a011e02010f0c020c131a01030504020409171b06040201140c010605 76
    0x80c80c15a0312540c1e150901c10004000d8a001b003c5410b0522500280b8071881c0c0c400810f0385881d085560031200d910500b0311748402c203c81402450010382d00d00301d660003901c1038180001075262900320001e00003812a0740c8208030554002c07000c10540c44580250300300d48100550420940c0f91800c2003030010304901800f41c10311899030000300f8032962000080550b8841c5181114a00d4010f455006003071140690060218800b00b000b0000234858801013170041c6100c4002c00709090355a0319103401c0ea031040304015070f110ba00042c10b100f185014803e405807098407030501c0560002e518000f07850186044015040014810181c0100c00d100350084400a004108284640038510300e0207540c42c104000c10340c0c07183d1416040c2040c5c0710418428402821042d149041c40f08480c00015401003801610a907000354440802101040c212400c0f03030510132807000304c1076841c001061030740780394034032104604a1608460144000750b82e1101000300c00c0415040c4030380c6e96444a0300001e00501140e0301298100d0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 907116888 1250 907115638 907115647
    0xf080c043507080115060c120c06020c010c090906050f09090c0a06030b13200c16060801031502041401050d14010b04170102090907030b0d1a010f050d15150308 70
    0x448041101c0c0b0032601180003e01031104400034036034005610740030f03000000e040304041d000400d0300c0c400410581140d500308800b014805441c0d00c3d0690f806007104405c1c50b9140c0c0d0f082018142d00c424007a004042d400310800c12603080600286e0018003490f00035102c0c0e140c000216850000500800c0e85c0c4400040c0341c50011640c4420241c05825032f05841c500c00c4270072090b034040300b6069026041400d02106d42242c04e600b060342280b03040750491100d0007144e20882041c0c04400311240350b07c1018059945440d40e103989545050078454206003400400d01d40144010031540d21030041450100d00242821605d500340381c4000700040880d91000301240314100700002e428400c0230001c10668044004011040c04000929420b038401c000400e600301e41104002000244a80c0c004201100c004004080403403850302d5018407a01040c41480d076031340d40c2070b004101a000d04400c8400500c0300342c40041c0d40c201c850b1540140b09101d90b1084c07821545030140790300541d13000d01d1340c003001e558403840190b00c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 907118138 1250 907116888 907116989
    0x708100621051e010b0406051f03110708030c0301090b15041203120c030b0f0109030b0103080310080d11010c0305070503180304051003050405060a0b031f022502010f080c04 76
    0x41c2005817000c1e40218a0140c02081a017880b041404900c055042e402e01d04207142d0200302d0080a440081030a0390005001070b0340050b512200039400b40c403800c0440350f02c0794141030200044910300101144914424034403405003609807420755046440103004509100407a00f420790b100020902d00c144100c0ca011007002002d9007650002c00f1044080c0c41100e0700e4401c0000640d00b69035540405031980030b02100410000f05000d00540d801031400b01c0d88070a00d40d940014900e80001c14600501040c06c281c41848150000d2083d002400c26a2030213000904161078050503900c8094615100380941d5605c080403400f007042200c00801000e0501310380040316000c004c00501003900c0856182c01204041101c2e45d80f08c0c0203102c1c480070000c001d0402007241003081244604014154140c2607001d1028400c2201c3e90074640c00024482c001c000001307921840014031441284513a481482101000d1081018142b0180d5054484400d4a91140e001201c1004103407426034010380f1203407014407501d1a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 907119388 1250 907118138 907118141
    0x1171b1b0d020d0e030a020f0303210910150506070c0f0603021c0507020304060503090a0507060807020d030618090c08010c0c2105190e0d050708100621051e01 70
    0x12000c0750740c0c242e4808010022046482500600e02154036601c1007003804090314190004000c007103070060440340b0785200c1ca203410200c0502d03000901602081c04041000000042c48100080d503048041003203061340c0c44c50070f02c01861a40c0034680c05100c0100f000c40810682c010110080c7c00281000c04030a5034484005021707611403c00c00c80c060340e01c010501c1100d406400b865003c0c0c0c0035a00518202030600e01c080301c80d600014281c03001c0d4422920403030041a0700384a01000f6190a41c1c0340512850300160103403a04989044503401c15141040410000e4000c03e4580c1d03614908032804101601d80c1c1c1042180102030740c01c0700720310354030300f49640311943d820004d090a0940705001082c1c00c8403609090070342d000300a0300040c020032010840a03074151400710801d41280c01d2030030301090002200300810702e55401c0042c00c44540c0d01150060094000800041c02003156000041c841181400d504c55103001154402c00c8400202401c114100241031001c3e08424490512400300703080151040b50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 907120638 1250 907119388 907119403
    0xc040f0f030203100b06040e01030b041101020c0a03030e04020c010626030f0f1b01020a0c060513050c0d03021504051b04091113060b12060301060501171b1b 69
    0x10040840140004a81011100500c112034004000d40950038404a441300645002d10760560b010004000105034000c000c40d0b030501950080c1c041e10418541450003402c240b0048941c58155070220501c0b43e41c0c1d5545c08416400c1e01c5d4540790242c2d0541c41c450104020303000310140c00c45107500b0070001241d110340c3c1c0d030184d20034111900008014402440c011f2901c0348100d13070003a20003030001c0104007a40060312000f8041030f00c800003003d12005203000041d0032a0404103060700003580b03040360241881128081c103600407003000c16031008a50582e480d80d554280e1214500c1c020081c5100c40405d060088c88500d10701184034003100107515182c5051074031040f22480d52541d442d10b1201900c01e905040c0b05601c10702c1c4c4c0c440c1204c10b041036604108407208104038558903c0a860b0b00c000b041e500700b102c1c01351648045190000b20942440b0b4101400d4415075002035040094000c039007039000d4401c1c540140c00040c0ca951a00541d000081d040642e482340300e02c3c80019072020030110b1900d10700040c644 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 907121888 1250 907120638 907120649
    0x91018120c05040e10050c0706060305030d0f02030907090f0204210b090303072f010c1d04020c0616021c12050619180603020901090c2624090c04 64
    0x110085840302c08010849550f20620742071507100c0d03005000b200481b90f01c000c0d003164008170928140040c41d50ba42c01030f203459800c2103030aa0030101d1000c551415a01650b13050000c80c460a504501c1d2641800e552084d2510a40b14116110581c0e60b1a01605504440182c01d12a140c0b041501640000283d400c800100880d5014400f00014407054408801d8070f01611103551500088043e00c11405440705000e00c1114803d03003007540780c0416980074071803001c01d06010785073300c40180b4903a410081d00c41c04000f60103000c2c82c0100074414501c100840e2150344980420a841d207400d59815007286081040407122400c2100c0c01c41c04008241c110201c18004601d42c0403c0c00f050755510305000e840882c0e440340440544060000748041030310000c2010400d0f400c4100010301070b030f881c1c002628818083e402055040e58403c001903405034400022180c0c01903d1580c1548182c03480031500c20240f0060051035071031a0048140300018422110340c100400040c51907189050107124503240360f0040c03042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 907123138 1250 907121888 907121903
    0xc011b051c060312020309210d11100e1b09100303030513140c0f180f0703110301260313050d0c0512060a0b0f2b0f060603150b0609101812 61
    0x925a288000e40020b00c100349808c010301480d41308420150f4180680004021443c080e2010810081515205049542202d0b60090941946110b503114510084a140c10301402080341000b03c034004994050b002c8039807515000425544504100000314074004000703000340c64030358524120341d5002410300d0f840305007240e6030304d420b051410402c1990319041c1c10280c507415209001a801c0d00c0302c0c51103160710000301d08000c85d00c400721100c210078550098001301f8900c071003600d1420940010350401841c40814400842c5440c0060400300343c1451184541d0744204580410a01004030140ca1a0020080600000d4080c0019004507803200c60845024a40500d4114100780c0c0340703406248899a05009802180c500903c8480381c040018880a0a08440d05c24419280015013004c1c070079002c035020320030002d0010b00318270344800c42d642e40c2a001a0070508001d003e1070b580d23690310704031121000221180904821150310a4a440341c000c40524007a0f4440b010000f4512043c0300200070481c4903048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 907124388 1250 907123138 907123159
    0x3060f0b0402030f0417132702040b072d030e09070906120e0a080708031801022b1e0c0207090203090309090c0d05010b0c011b051c060312020309 64
    0x7444102d01046a000e400d1001c2400841c0200704a10300902c240306007080101e1800d18005044000410545e00c035449140f04c1c0214024502d5400000884010b02e00b00c05514082c6054211800c50262390130103001e04110403080704070351250102c0d01c80030320420f0b402940049554240600b400b00c51a03d00350045600f03000140b030b881d10887c0750006448080d184d01000001c2034440f40c000b4403a802c030100951158004400c04202010302400c4c02c41d2041145955a240507280340e41070215050058165a0040c0321200c40326241201c164000f12a0b203411504050380c650206c005401c24507d654a003103042c3c1c410002c401036a4000d000b1508058080350302a030b581d11000012480115940c0c00d0a0700207004a444a21703001103401d401c50081910f042c10440200c822104a034000e0380000c0030410001900440510207005990010000b98040603100003850000380503841baa0800203090004032640410603000b82e4800400f0310303040381c2595215603109502a66070303806109020b2140590f182c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 907125638 1250 907124388 907124411
    0xc1a0d06090f0f1b110f060c22060c08071e290103020d02040b180708040308090d1211040b07080d2009010e0d050102070609020f15190e0a03060f 64
    0x2c1c0002c0c1042c00440542c007200b130010210b030700a100c03012204081c086c56000c0c00c000241009001e000d900b80362459070f0344400d000705181e6005518420766440c0200c1c280100101d40d000400d403441c480c5c00903001c5640d00050324141646040840b5007101240305c0034600424404648100c5284103500e031000c01440000c07040820403100240700095210241c1d048003001400c1c07941119182e80805009004808070703044850000800440d001000a00c80170200700601d54800380b030a4200b0b0b0083c000c0c1c180c00d02141001400c0c402c03140a00c2e00c10036110000d24114201b034204403801000c8070020300303031104090300d4040380b00da00603001450072030705001c0080200e20308030300354000107440004064600904a001561518100051941d01010f00003440c0041042800100020742c0b0480001410310310600c10011b080c203020160a0085103d02c0c86840e10300041011262042c1011102042c0320b1402c034001c88102c10800c039201d4100305020000410000140c02c014180794910105101404004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 907126888 1250 907125638 907125641
    0x3050609070f170109080318010c091202040e070b040306050108070602070f09050406020405040f020310210f260d052410120c020f010506030a0c1a0d06090f0f 70
    0x280205104031400030300411a860728a4420700c4040380c03d80001c100ca800301c0d200d00c0003540045601040d419400d50507072010b40b000788205041e61003a414080030381c40c18800c0c628009021114028010760f515060302c1038203481046060000c1503004103040d03940b9128074000010341b0007841800c64910690202050781c0d070010500b0070985001144001d80c09152110b40d0020f05005002500d14903420840401c0c2031b200c1380104201c001d0320100150b070740e042101540c8070803046503020134a2508a50f000003020320080706110350168100f1a0200701c0d00c00c50410250540340140005990040030f0204054110014050004552400740400c181d55800c136075441c100305109001c0ea503542c0300c4101d0f441186801c16018540b1021031601000f056030f540c1c8800e00300d0350606101070241e4481a18424050801d01425a0140041c2d01411200f00740c0c0d59641c05100440c0102c40319007080307080c031009403000d9130191020000310803810301090707954445120040c011035004401ca642001066424284507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 907128138 1250 907126888 907126903
    0x30e0318130603050d0f3f380d0c120201030b04091b0f030201020a03080903090d0c081b1305090a060606031a1017090102090402040e010501080f0106020a0b061f02060103050609 78
    0x3c0c1c450a80700042e4520324070150b1f002102195240f56450007042128110211402603200b90005215101205c00c1e82080c0010b107041401072144808442c500300060701e2076060801c0703a5144460329001340d5540300603000b41520b065502e820a240c01820010300807420480001820081c4148500c56190045c040e100301039800083d015a124442c0300300003d11075100b86a1040d0f401d0280d9043c001c1e05400030300841e04a00c0c00791000b002c40300c000d00c0300d10014003001c0001e840c42606644001d0300c03180402e508a918081d0314016544d60303400546d0f90001840381420721a480700041100700c0c0c0307a51024000f03041058242e2943c844e0034259031824141030660103d844c1143e10b07416200d005100000a034000c2c0100041e0055400340501016515180042c10160039145104141d03981000001442058010854000380b0454401000b1a130b40218000c44400d402500c04c0c1200d64842d401300781400c3c208008090002d91079400d404c6d003d45d0110300c55060328428400c2d200640c4541d0061942c5210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 907129388 1250 907128138 907128197
    0x90406120b0c030709081504140106081c140f030901051311042007050717070608070c02040b09010803280f121b080403030e0318130603050d0f 63
    0x159140442c002c0a039040107036a00040601e000003240761210032450070801d410a188461003c980c061104010351801c42812030760040e4000c2000f5498281d0607076a40605940100c140507100424030050b500c5040380350030700610900c41d140c0e600203208500348140d20072640c0c28102d519183c00b242020b040541d8007190140c000038080c4025a900003000001d1401070b494110751910481851448000390b0082c061071401100070f45030703003440c04084190148a02ca001406a040000c003441807a410a842e5a000889450b182020103400e2000c1002048800b040071351007a050b4000148000c0000010045142007410718141410306141c0d0301000a90003810a020400000c01241003a02c034507035543e8100141c00022522038050380b155200c12009081c80400601c02c2c404200034103070107011b0250680c1c0721000451820000c64541100500b60039640382c0b043c4800a8230a0000581ba00031202540e00032040e01c0756818a850080c220b030071448120800724020003901d202285c01750304003408042c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 907130638 1250 907129388 907129403
    0x706020c030105100e09100f06090b0906060f0c010b06070c060f03060503030d0c02120a020106050918060f19050708100b090a170a0c060504060816020727020f09040612 74
    0xb400c1c01c0280c010b0250041042d4054410714005a05451f050700504107030b101600b800050544c1030401380b20036101e026440c2409480c00034207001480e00e0300300803a43c1910030351500e01e440b01042900180501341c0b08140540c800008140003040c45010b50040080740d2144d00d034022049200102902919598414598103400501501400c0100303a081691003400034819540e4a030480782d440003c80e0044802440180e54035035081c070507803e00b860741d0368004461410300140c03100001801540d4102c01407400c03400116550115518000c3c03400c02a4403803800341c00c14861807030840c0005007280400c540110b000000c0707550004107400860200d450188002d810030b00014100314580c00c680c07460802c02807140c89004490000304082070070304030141407179640c2c0d540d5a40c41c1040c018144140a0700d5215801c490f40c0c40241c0c8030350009181401c0f504c07070b07072000050280940f00390741d800c0f80fa5500c030007040c42c00007400c0245a10004020303e00e88000701d0b0100600c9469200c007136440c0048510090002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 907131888 1250 907130638 907130671
    0x16061b060e1519050601080c37020115120b04110a030b0a0603120801050d0b270a06060e2701090606030b0f0114010507140705060c0706020c030105 65
    0x149030350700700004140d816001c6a00c103000360401d03011034040c2111250b04040940400c030400890601500d40c00c20401d2800d004a8140a491041144982c424004c201e2060402d504403d90078101c5900b0307413081000b0020340455403040c000c0d003e00a41800c520814070304100208401030700d03a01c0c64007481e0304210200410303980d6039242c44070034456142c49540a81e50580000004146a41651090384c8600300403a045144d451301841c0d03500104005002c0c024100010f1086450700301958812580083c110882074965032240841c0e20416400049035522566800261003400501c2c1242c0f2031064100f044603583d20b000900c2d11140907110f084000a18011501c600e4214100d0100801c00c41e000020b9400f589540c0c1038119102e1303610446050217010100304c070000c52151690f005040b0b6004900e0b9103100e44c0d0000303080e440f40040040004c07001060002070302404000000c00792101500181e030380c011807800c40d50b031958180700d22001803043d4042120306003810700609004811140038102c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 907133138 1250 907131888 907131893
    0x506041b0c030e13062405120c0d0902090a09140a050d0507060b18040308060a05060904020c0f0106140a0b1309020a0c02030d08100608090c0108180f16061b 69
    0x201c4104250b49903001101084c100e416407154880c043c0103000c008200300032550b031a10306800030307058090342d8018401c1c184000070030045121076003980141d11041050703440701d48980b80f03402459100d601a400014482c20801d81d00c5c040e070b2050034098080c00f24a110308000040b601d40c0d80d181c07106d000701b0b141c02400700c680406001d036015108440c400d0801103a81d0105a0103e07804412449101c5101001c4c041800309154000070325980210301561503a4a641c101008039506100300003009000d50307030020742120b42c01e40070f020000b442140c000091040b2560341c1c20030601102c40e501c2c214441c0700704603000106005002c0c00ca83c00c15500324010b100c52890900650300035002100c0203001e0000344034550005907404d010b010005800360704d0f0f1f103000e8200243c542c864000036070044c0c030610943c4400d20580c00000034550309600e01c00d01c2d041e8107658912507050061543c83c1303200c0b10301d8401c03026110008900072400703440202008031400c0e5150b98440040f11000c00c0d0400d4003203031010411140c4007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 907134388 1250 907133138 907133147
    0x3070b09031305220545010e060105061c0e06010305010b01050406080106140f1b0c06130b0d02041205030c16180e030405060403140601291303060509010506041b0c03 73
    0x911804446c05080707000c010400001350b110010107500107100e1015440c0e82681c0280541200800086000300700c4031441d104600d90312101030040921943c00820451802c0002c44410107007003052600034030000390006000ca58405080c00f04036004d5003045004070340f41d440f40099400700d801d0b5035910704140c0d280c14026620028804501044180e080000c084e545290000401c081e400440402040c9281c999001d814003010000a6110b0501001a211000d5500391210150380380c41091075581c0c40616420f4009100d140d1141c072215542c03a0443d0107200c80400502006e0f0005402d8500f1411032100440c0407c07a94020f03006003844005445008510641c84000504802d01c03c5900c0c064595000032031030f07002035100720b40307050752075010942d0300c10709211440c0100424810450f25000307106a006c00c2c526400520744211502180070b841400c2803180450055401c10000c01c600d00f01007540a010300821680280158203014104401044514020b10007118540d03132803610803015031701280c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 907135638 1250 907134388 907134391
    0x30613051207140601081b06030c130f030b060406180903030b091003050f210c0102071502030105040506010903020f04021810030c08090304030f0602070503070b090313052205 77
    0x1180d40c45211044a160200c54005108040c00340307000c6415481d510040d6841d100058000a1042c4c000500070040003440d041808842c01003120150740320781c0c803192541c000380074040903812400326070400002c51209100200061303e000780320701c1403180e41e07000c103220036039009116a2040b87da481c400101c0d0304480d0752104070713410f110340b03400300c0c0d26101e030400a143c1001c1507030900c030b44000108042080080802c9004e01c0001d8400c09401701007030305000741e08450101c00180034003000001d450a9805400e60443d000e1711b510410290922421981c100c00135002402504e010b01d2800300440c96540c01220314100300c0ea40100300d11100c2c0c08800500000e90004010b8140c0c80004240c1c0300c0b4203540315108011400031aa40c0011410502400103010b0072000d002c9080e40e0308100030500100d032410500c8141d190304081c004d0f9a6200b1807400c1c5141d4803650340040c1519401c00140650382070080000d0049410001801100740d8641c1d041003803580c202c441a125484011500814510203600040d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 907136888 1250 907135638 907135643
    0x50f15060403032a0302011b03090b070c030908060a15080a11151c0b1c0b070804150203070207030302060106090501050d0b04060b03041a1e072007090204091802030613 74
    0x200c202504c200000c15040850107046026075100d4041c0e601040160800c0541d00c00c1c0c6107024485200e95469040f07404901814940810020030324000c107040c01401d00c6401800440c00b1620240b52028180008084082c801d1000102810000030002400030ba00e900b0035030003180590040c9009410400f84811020204000310002c0c021041a25914282c60005458002e00490701c02c41c18000c025001000d00c01c80c82641e0320140300324012811142c4101d5105005013080290b503102c5082001c26001110071849030f1070700000400443c50303404aa03c0c400c403486030b000c6500301c2c3d80307030741c03003503038524058007400d0f0004005001c40e0040b0304440d00300142d4048007030030004046480d541240c0c0d265004a60030f403140003a95030360241d080110040650310000d5a00403c6403030b601c00c0c1c0583c3c4950b0001c0d2030003040240d080e886c20112200d00c8121003404082c08101c40219030383c0c1b480f80010b034000340315085080e80b8084950158255012445401035801005485103a84454030340b6442072540310301707 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 907138138 1250 907136888 907136927
    0x20f0603070f2f01151509060309020102031318061a072301090c080c18040f02040b09070c05060a06030807120903080f040e09010e030301060f21050f1506040303 71
    0x408918048248a22038084074410000c500d40d1501e03991010444000d42c8401e121004481b00b00c48000d130300114400942e000c51601003428042400101e28500600c00ca03481240d290b140b00080340c1c1c08262010382d8003d5080403d1014559807200c0c100741055400c44030746100030400c2401c00248031280c044074454520301d050103804c000d0300019421070741c540c14101d9400b000d0810034070800f401008205503e01c412168142e40380303040710310a0301508019100030f242607100c500e282c003103580307507004005003113030141051a6500e00980001d080b011008410380301c07801034001003224081c084c01000e0503290440c108074039002e100c5c1d940c05002d00c0c0c41007524040041c604004800900b401e80244004441c0c4141c080d20b540c00c10403c0c0c124048003900710b0303545a1406c070701d0844803d030100c150780c1154483c2c10103034149508002c1c251005190031003644454040c2005021075510558450790190400c070048041e2556040c2103e41045250014540d0014091000f003000910800e0340030400e240c111107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 907139388 1250 907138138 907138187
    0x30b070e03160b03040311060618040213050708070f08010f0b030c0409090503121f1a39060702121b01021207030b0d02131a030307050703020f0603070f 67
    0x1d103030b0b0304600b600900250316000007440b00349580703e030412404101a10203000349040c0070001810652841c00a40c44042d6450005429541c17643322100350300b500a40140311034a40340c0c00042048034112000c60200e184131a040110500c540c8003d03059540b409003040701c0b01c0c24441000004c0d00001c0c44985088401c000108030b1818a005844545200d03200442d140c440740070903400c1c00d00006140708a19000c0c4c1000085408481c09944200d6400c9840f691052814080001c0107124610004449450701c1090302141014100c4100c514203880301c1c6c540d81c1800741190b15450710419141100168000b06121080c0f803060801001c910300c0340e0501d40303408551400b920782643c00c04003100c04c40d03000031020001250b816014903e9400b400302c41c00c00315043c80c0c4d0300060300318083c800010805940d031541c24580d0321048c50840704800005045907164055403034141e035109410702040340941d10b0381810204074202a410342c1c0c0115004d0300c9032003020114080032524a80c00303140d018844a10340c40d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 907140638 1250 907139388 907139413
    0x90d02030f0303040b1503061503012003060423180c12061008030405130504020406051908070b120105100c080c070e0c09060a05030714030f061306030b070e03 70
    0x18144000080c0081c0d80c90b413520b8242441c1609000300864400d600701518001d5039540031803650707404184018400b0007032480c900802c3c014440c20404a29507000c0c0b040004c140903101d4069845410200c0d01406509a4015400814084800c842404010060202c0d200d816030500754051910228200c0b01e030002e2080000703000003a00c03200542c4070340042c41800717018030701040d4410107014407000440ca864030f001c1c0803980d110003030521428010307601c0012404550708c3d508014018400100b030314400b03908486c58401030331054400c1421070321801100107025000102519804201801d940c500750303180034144403408450b0040001040012008000010007801c040d0401122170002085040d0919458070b5900c1405032040550032010320200b1070310765941c4201c2e0b040c0ea03903501c0d05603102e1701c03901d4080e00c900ea501040324140e5203002c810072003401c910302c42c031906c02c40c0c0880d2490210f10300000c4060440e007803800090300b0700f10c6140022ba00c40b0f002d00f0390400510000360840b8070108181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 907141888 1250 907140638 907140643
    0xc061c0504080901020607020c0139120207080105041a060d120306080d0908030417100f020d110903071703160b0412021b090a090b0906071b030203030a02090d0203 72
    0x40341d04a030070000c08900b00d6038650303040003078541c000424002007401d51096030010b400380049400201d00144041e01c020314401804040c0e00b84086240c40c881c02e2400c452810707100f807000c000361020062241110000c0c1d003207014000d0501490b002510503800c400c0c035040c0d81c41c1c10b00f00142040c1d006403208504c18000f41c048640d50302e041d1070b165000200c1500744210b05082800c0042c80c2010481c40402c1480071900110448040711140410702c0003062140310250305220440200c1c020707080c50081658840f00c0300760002c141c0070100382001c00001041a0030342a00e40180884203416912100041c840400003240510088032a6400c0301c0c00c0404940401034506210b00088503038513181400d0108029040b186544c900d00700d400900b410880090005a00c01030710b94081c3d10400902020600340d140075031052241c240c02100343d1a480c54a0b40410343d03525001e403520400500300c0c54801c000704e151250014207055140e4040c62454449a0a0001940005200507400700340b2466900c01682c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 907143138 1250 907141888 907141891
    0x200607060501090b06070302061503010603120909060b03070e01080604021b0a121e0c0c050405090d111903050310080706020f0c040c09030308041505070c020f060702030c061c05 78
    0x28840c003040a6041900c88826a103190002d80c1c000d12080c45900e0000b500860360a034000002251540c1200d11400000d024216660018103c42c000d080d415a44903480925031342500c88000050000d25940d49800e00705110895104001404042e884000396100319206504564024405070070000c00301c08041010010b84001c40d00c03075100102c01b008000c10f01c015411500e4040c00c000c01141c030150300003006810405036030710401c4204071070302040208481505001d050003500c05c0202d45020900c4590300d5821040b0308001c01e0400a0178507900500042e000c048200f01c0380c52400c0040c0d1641c00b620741e500082c0640117182ca51541c085954103003046a08000c101ea40d0041504641042ca601d003007641850758240520b0415040c0d140d490381050190045941c54074007a171040d0780322b00380741c803031802d8041404c12403034102018032404c1c81c5c1c06901503515500031210145140a10713020448988960000290035401c6020100000c0c58518041d0400c0c1c044400030356801819180303902c0c00c0743d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 907144388 1250 907143138 907143143
    0xf021006060513050a031a0702010912080f0f1017120a02010b240a0e131a150c070b03130b0a09170702090115050903060c070b22200607 60
    0x400300d6052006030041c0503610013441e043c1c803682035180c29510340600c803140c51112110015004c2d404143c51901c03d60120407140d41005000c0e02000345038000038804142601c0f00c548552042d404902800c40c0380480c24041c1c00d5900800d0b820074501203011070902c0303110a40400f5030054071103444103194050000c00c494201c0ba80000340c0d800340241048074072440301000d0400c40c600314038080c0d41e1002d01d400700e605001c41c6007403034420540640e000400400390002c503106200d0801500007800d1884040180c20580107c0e05101c140000e14601c14150040c001034a04652015400304080340d04c80340115006440860b40110311202c83d00d9460301600b090750352403103641d502d4200d54140010040c0d603003001d12503448039910b030200c40d0300000c1c110b0506010b11070086181d1014094000d0181d81151005940982920414505442d2545194000d00000c0d1004900c0d0400251058112071743d991300c400104100c02c0030b8a04980b60130840c1241c0c042d46501c41401220744003110360b10b88010b0052a40b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 907145638 1250 907144388 907144397
    0xb0f1002011812031b0f0503040809130e0f0c030709052706060a050a03021f110f03030f0a0c08150a0e0a0b01030c020303060a0b03040507030804170c0f0609010f02100606 75
    0x180b0f19907009040717031020045401c2d0440610049910a6800721404c8250306d07062500b0f40e00c9440b00c1c284040c90b48103c600880d80464624603c00c01e080d49904500c0c000c038a60301c207984816124908464694048181159041d0000b110600034510154840c581040c42c006616802d040f038616485581c005001c0f21203200d9004000304801e914140160780e02610054030070f1100e040c5554007180c0141d0003981c2144007140d041c590380d858144299001402d110341c4100300c440004c5c2541c20346449605c03c0d00d2040e41824900002415032400e4018008103450b640e50382071242c0c0d50f084007545050000010a940140f8419001900f004000912402400c00010002318000600001340403182181c3c05070b000d54009100b01300d0f40d95122000c44d000c50300341d454442d550707075254601103042c5041d41d080108101e4022402007a07041809602c0c840e14000e1500f2241208400020404085468841264400001c102c810001d5116000c499421000360044844c0c1a0f0014002c43c241e40fa40e820107000107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 907146888 1250 907145638 907145663
    0x100e09090c090916290c0a0c120b0a021201060f0509131a1f0e030a020d050105010f080102040807060f0c0f12020114010b0f09280e09010b0f10020118 66
    0x404844c0002c10041001d284003024143ca43c12040d1204800c03401c10742c011070310114200c504804113200181101d1b51000070811066103640e0619405c085071602501c4410b00305000800041c580c4c401c0300e903000d1300e61707807074034003da1808000310f40c51581c1c000c0d0002004018495882103031211806031212500344c0c240070490051a003041030081c800780e00003038401c4200510700b4000c03409030075424613040e40919101000f4841c1001181c40c6c002c0c2110020f410541c2010204c0900c001988905d0613520010610842250780d01c0310503090f40158001c4541d00d4100032010020180140080e290003002400c010000e0070709511284c041c00744904080d0fa091100b10440806503034288248020601c20040c0c0003815410482c01d614240203440c07840c101048002a0520a41c0e9a5403481030740031980d00b0052134259551804080741540d40c41a03202c02c141c03200c089003c1d1403043c001c207407881c0009002288040d00b4502001400b010f802c0300d04c0c055544e80c400c501d0040c0e500c03c620303024480c001d0000d075041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 907148138 1250 907146888 907146913
    0x21c0503040f121104020a1211070c09060509160503071d18040210030c020a0f2307090c0905030c0d0c180506090708010303142802011a100e09090c0909 67
    0x520454024407407180340304100780c1c20000d800c00d2007102382d0108030100140b1101c0318400020b01e44541200540194000000001c007030b1120f0700400181d074003d5030792100e01c0e180d4800c2804c00d05070341c0541001050081c03000829091140000504012998164003000150000417844011184400782c4403103c100d400c100946c01c054059440100d03551408015172560950000d485642d11040200103084521058003400044041510502c0030041281c401c02c1500c0c0761599140e9261058103811410624411003a134002c024803411142d0240c050206030000c08100185890603001c201c641c800001c03404510000e5000d03420200014038080010341c1c1c10b0540c1045401080201001c0030030203008010300000750b0140c1d0300402d000071001a26280e0394001d52907400d403164042144c55810346008106006581500140450388209148108802c03c1c802480101102071072020003040d242d0380d50040c02c1c1081d401c0d00e9440440340040d19030b1601e2000006014650075614000b0551100304413055 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 907149388 1250 907148138 907148153
    0x30602131d0603011a1503090309040507080f06090c0f07060e060a0f1812050a0509041401030213050106090611102a0201021810170103050f100207021c0503040f12 72
    0xe1000c0c00385c5054869156210004200040003203010203802e1012002c030f0003c840800954220306c0c1c000f0014445480c0000300284215401ca072141910b030450300c0412054201404003034020307c42e50008500c3c1c2501d170742500d581da911941c01244c19a0342c1308a094400002800070600070010240007003400200707082410143c91301d96021014000580390b10100055000c1117100307041c400740c240541c0741e45181405466501804100c42e40260404020800c00122104241d042e603100322203404007108910703251000c88409010b002d010a10700c060602009000e030444107100d0a40d41d00311082ca40e041444030341078801c00c069103d079940513042011903d05018011041000240c0300860800c0f00840744140f1041c512480e0303c1c050740116840c081d5092007841e8902c010040c410414146507940d1800750b030780b0035a590079118640100c3e034200e02d88110034000c0b02c10b030f0764000300650b00031014894402440401d4503022034040c441000005008800032080c440105002600201040403074244403c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 907150638 1250 907149388 907149401
    0x2812030b010e01030e0c01181d041a0610080a09060e07050a08030c030403060f060b0c0a330e0312090a02031b1c020a2607050604080601030602131d060301 68
    0xb0705060404418001100b030002c1c6c40315501c0740900e0024000d050031991405010b500360421501450749803403151954802022090145204a03034040c00601003100b001c194190540380154817202c0000302524a0f88070312411500854400350019a45406d9518042241c901c210144001c0c0c00112080003945000c400200003010708002540c03902d8050113249031244140d00004040550f01c5199140040e400d50050002e445515550f50b55009014405903840d0000a41142c1c200845d062100500c0f050309003202120903100b058203201d00784d04404d1405030007581841080c1d4401440071013501141e04242c40e02071400c820282c041d00d001030042c10700b803039140f100c10389018000b500c1c5185151030300612080281d0740303030f4026500c108071840041c10351095075108a40d42019540042e01800751021640c2000000da0102c1c0c415617500e90500406000d1392103540301c1da0b000b42c401000420410f40080c90629804c078001d84409848400c2e900e100ca0b110144e98a1450b05001013000a0400340f0400703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 907151888 1250 907150638 907150667
    0x1109120a12020607020607080910020409090204061a09010305131e0c06080c030a0902010207091a131a0111210a11010501030503040b0904060509150a09020306032812030b01 76
    0x10481c13403a0100d4081d40e686c0380500309108100c4110002400d85500344a1514980c8000c80c1c1550350359a00c0c40c1c000041d0100e00c40a030700c5246096400a4035210045211803011030440a03a8101b00003400158000c180041541f9480c420392200003000440500c5600e5000d041400e40711104a003070306100c200031030f80d60000302c1400700b50800e00414006600540e90320001d0b513000880d100049100403414071019034403000d00141040c604454010003c1e450300b1098000399020603001000031001070135640700d0754100d01c22155001e401c0d051075200d03002c409480a0b83e802110103004040280060101038110a000480c2000c6084418564003130740110b0042150402407141d5411038580989030712592080031045000082d42198548030b9070014001000c00501c41d9441d86030500b034522a640c070104805209203085000428900520320943c1d006403030140c0280b0303005c01703203110075013903a0451754101c0c104883c5038002d4800034140650f01c005a141958000c6400400c00e000980754040c81c040d04e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 907153138 1250 907151888 907151893
    0x1d070b0403050f0d0801031218090605010e0105030f041115070f03320d0b06190e031b0607110d0f051204120602030601030e120705060711030702041109120a1202 71
    0xc070842107a02c002210706517908160b2941c10120b011000f601d540c030308086c9d04501d44000410024221006500c00c1045072000e0300c0703105044403c0d000444440c1301c2119401d001d440c042001c107002c500c000002000f0ba0030b000e092880d00d407842034200c0c0d41d66000341c03400322221f44c0e02c00c00040425a0092403030403140d2800800c00403203a0314805c50042d5400f00c803800a51118045640000200160002c080c10507000c1d05032955885103d19500300025542d0008000c01c44030030320003005050000e0641c10802c1c08900c40e03449080c60204000b040d9124901c02e581008070040380303542079a07a6030b64011071180b00c0c1030108000740385458020301b0440c20804c18031010310240401c004141c80d4402003400554800b60041c0c1d030707030b035410f005030003c12610320000704030310890b000095540071050080801d0b900890032202d55680311001252010a0300450380c40c1c0750010b025000c01801c20303810010400b20740c1c01103507003002d099038007003803444540654803200765100341200000c0c086002e80c5401da5000c0380c4007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 907154388 1250 907153138 907153153
    0x132010203030f060609150304210917010b1008040605100602031629100906050616060906020c10051501092106050a0b03060603070302030706031d070b0403050f 71
    0x41d44a000c01403018002c3e0810300700049103561490119443c4010003010700d1a18032043c0700006840d00100d50803103078040c203045600c0a0000c1d808060410700100c2e565400303218182001c1030040f098244002c0340c40e64a8032000c10069442220000d0a0402696241c21618007400c01c0402c1d100041c051f10000f0784400801c0c40080c1e80070003260342021468400002080b414070f0010020ba140c030501c59005a0140343c4682181554888540074454803403000b80c22036252003580003124810710a841d8001c004210302d5104040e510341547e0102d000c1d000000d880303061921602c0c242c0c0c1c844495404a6044800440000d070958407820f03820082070001d14000c98010b10020b0401389150144002c0da60401401d4446038030420803031041c2c1c0380c2c09075083c002414800300510281c40b1703000e4a40e03c64083d000010b00e0505000401000312600140140402840c05509500610801071a0541d40c40ca1004180316204100316820041100340101c0343c2d120301d0740c2040750400500d0400105035801106 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 907155638 1250 907154388 907154489
    0x60f060b09010302071e06020c2b032406030b041a09040209060312070302010510380409020c0a02041d15070e0915010f020a1e050a05030301 62
    0x81d81e10300e650030700700141d8034907203404d04900304032040c5051501140c40c20030040c01c2003200d4001d8185481d140c012598034102d4402c006203203022205215000384e10b07011802c0080b9100b0340095a04c0603080f03c0c007126171514444040040d221580040700465181c80346101903082520641c504d0001c2c0e11141450582c6080c0002c00845019001a11805081010440b5079a0600044031002020b62100d40e4510003490064060034007122544914058110f000031000110342007003194101c240030343ca010074400b0005041034030900b115407030303058020300000c25007580d5880104103103404503000b44032078100d81c41000191003c1545800304d841082483e0007012400144440c1009c2c010081c01e0440d030307560181105c043c0801003a0640c45113200c07003849407800031881120292202030382c1e055945a0340303c1042e071b40d400c0c0d000c1d0010840c81c4961001300c0307519041e14844201900c03c200342d8000f4031142d101d6500e9600300b03801c500c0000d114400340710000d100c249410800c003070f10020f10200640c0002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 907156888 1250 907155638 907155659
    0x40c08030906041a160606080d08010510080403030b031009050613020105160f06050a0b040c0503070f180503060f070e0d0b0f040609060203010801020403060f05061f2307060f06 78
    0x900c11030711314013152041440c00403409000d8a200b0150b0a0f080b0340004214100380d000b03049540f0a05085002c2c00d07036544078281c81000414140c680280105400015082d011140442c004001f42c0415684605402c1c86541c14000340100f620f0083c3c0200c1e6407012410401c0c08c10001800809040780000320041c0144d030001c09881034086070f0748218801e0545400c10051030051030740007c00d402d140204018480081d68081c00c0b400c10b0581d8204050801c1e034038181c4983c4000e5410790007084401c3c0034445224840d190000100842550019005581700702183c5401c10a903400850480020308101c0b0300d41c0d1241c40c60394044811101c080c0078051fa40c03200c000412010b05082ca00041e03600003e0280f1001e5001041e03900c5d4004003c40d900e6948000c0107000390014003080320100d003480c00c14940110310f406170303d004640007040b0007200c2801103c8462809900e058103000d20240200322005d205090f6240072481c0d0031048802c0d1303540301900d4090111040802001100d80c03428a0070301548002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 907158138 1250 907156888 907156897
    0x2150f0c07031101050c12100b0409020d0207140307020102210343090501030504020918100f0504120305072007050a0f06031506080402040b120a0506040c08030906 72
    0x60314030342a514221410304590f21200080810071139820f200a110740071200600030f080d40c0004400300c0800b510307102c038001c4080c58244640300d901030060009000c400019401060840400303e401417a01103a50380d814011403214003880c0b115000403404c0b0080d5601402182c00d03159400c070340898032400441d0001030501028108070b61003c0c00400e0400e54210102d5036450070740e109105020a003002c141c544035110b80040c1101c0003d50461400115940030307003c1e00c0c3c0074a80c014581c8401342d866000361801a0024000d80e440c0e841144150032590101d48a41110340c0710710340010a9034138040c100003a01c00c64008508040514210421501c1a48214041c0b0401e40f00307442c4207074004074910340501c0c224050f00016441007420b1000500300d084111043c00f11855524144804024542003000f818142d110300d00200c0c9600c000217006140c10750140307620b0704005002d2900c0020003101180b42400c084011078141d4428014402032003d0100d000e001401c11343c00540c40d03c4010000315259015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 907159388 1250 907158138 907158151
    0x20306280203060d080d090c0920090f0d05030d05061e0909030d060906080c010309050706050904020412060e2b0c05010f1401091406090609040609020a060f02150f 72
    0x5000c00031409031390703584075070102050300900070303036259403161525100030300c44104210744c880c6000030001542d5010b170080d100c2c0c001e9082640241c840c07118030b24036030390b5012510540d4000e1070943c000c01c03243c1d1640c01c0c5c0400b01e40200015a01e810071000840101c6030050300141c410001217603580c00c000c050170703824101c1c280c0a40341c03407415440c4d0740041441c41c0250b4952102d11403c011000c504618140e018504440880040b20021503440006508942440d00003074500d411103071050180307a0127007000b01014030003e840145029612280d05035091700320310b8115500368031800c0700210b445080012400c81510b00d61002e151000b005480740004140f00240780c24400c103004840e0074000c00b940300c643c1007160400148054210300ca500704290f071090042c4a0981d00d07003010140c847e030500d0141c0c0c0c4200c0e0054070101094035080c00308607031500014002c449403500c821103800183c441102e048000c3c42e485d180c41d0341d03620881c400a820003c100351407801284801e0100f01d00000380210a0390404c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 907160638 1250 907159388 907159391
    0x1060621090c0302030123011403030f0a0e1309020405060103060b04120609050a03080105100503070203030f0405100f0c03060b03090312042303040320090a0e0a0f080702030628 78
    0x1c035500c2c04008900c4154006540b5510b09a03080555400c0c4003611040c42e42a98a9034046a803070b01e00000040c00c0075910f00e901a4402e1020100003c8a000101b01039441400c0801440b04414001640e03080c0c08841d00c0003807034032400c41d05c0c11030915004080c1c000c00700742414000e450524000321110302691095a201106240e45401405056440088125080b109444092481d8100540325500a01c1000e0241c00c00d0b0405049040c8108107407030196146d50301951458030740a035520982d90b405082a00c0c940544c2c0400c0c041d030101881202c130103104201e008100203003202c070702030200c84490784641c07180081041040300d50000401110b0340360103004080c0c24261074906180c0d402d45804d00b0780781d120110190001801000000103042120b1244801410303444109042c180b40704503080741e250304980c00c5000f040b690441a04144044045801102e91101d65610303003c891030710000c41519241c070000358400070f606080c03118580c443c0019402044038002901c1000c1803045440c818000769 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 907161888 1250 907160638 907160651
    0x408130905070f0522080c1c0f11130207060b090105040c120c0302070506190b010c3302130f050d05030d0f0b28050f01051c021e0c01060621 62
    0x45500d02d007000700705d0f01d040e20000980345c5c43d00211581d800d034513049a403189402d1030200301c20141c11402003a089a21412003440c1c0b10f0726540e0720f0340441c0108641680500c01110032124024a07101800c80c0a010f01d5001c00c00c080701d031341449524401a00658002e5090540300702d80950080c0e00d04c030082c45602d4001031000d0030250224000d0268920044c950302580060202e00780f10fa02140200600681c4204520784010b00151841544910000c1c481e0183c40c0080c00020400b0043c17503517103401e100190701a29030340002001240d11421100d020001c250030705009021070643c110000e00402c0e21420202c527000c0d2521544e0740648010708804a485100003a140c0b40f180d0003048000c4805880300605140c242030101d03240d030f00c60220707142d60b04181c0c00c00603e40c90802800c02030010103071161464507042107000186d0003408500b400c0040d13002c0156021160b0051061108505084089034941c0002d84110313080d00c0302640702070104042c02c1214540c3c401260725884000071007000000c0d10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 907163138 1250 907161888 907161907
    0x80601060f050c16030c1d13150b270c0c03091002191a0f070503070e0a0510022b14210a02092b0204020c0f03030408130905070f05 58
    0x10704404c80c9905480c5021440300004001d194000030050781d041208200106000200c1c0c0301c05100d0441c0d40c0101d4000180c440404120b007ea40300c18550701c00d80010800c0031500380441c5000440075480300d83c41050102c46d9020381c02c14103801c1d4000340381e003402526064101e0b110a03070700c1c095220241c2c890a5030556005816000300400003008101d00840b21a14089040414407196100c1d641184049100000703403480300001c21540c407400c01030300c4950071502c1e90a8211192559040c040d5080a100200840c903503a441224940400c0198000c0c0200c10551003100c003101082d8410901c241c0022100e030704443c2d000300140746140500c00195850300c00b115810030807209813990a010102200007030152980003a00248031124041c0e981e10040d0140d4441c1110f13035006107020b810048200b42440d03006162071f80050016140e80000c44806400c486145170070742d482507408407500d40740001c2c204800310070100310070020030002c070040010345085070001c0e154100c1032250004002d00041c22010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 907164388 1250 907163138 907163143
    0x111c09020a2d0b0a030507030c09091a04050405280f080f0712230406020a0609081b0a030f031a0d031e0e0906030c0d150209090f040c080601060f050c 66
    0x40c0d16142c4440816182c1c2e40d1000b595540d440b1303840c5200080e0030440004c189034040c1c0601c400d140381c250f0713800402c1413030920141d00420440b15142800031728078042507003d0740c480c02118000d0703003e130015054034581070b0304004140900d014003903010b030b2003450780c0008201c0d88a0310b1200039400804556442c201c090600c2c4641c4074540c40140b10510710b00d6600c04e055440110042d0001c10000010018200801104858003991103040010f03848401040c00040003508500d01003845000e8950500c0ea01d180b000d0802c240c5000703520015848036854405240c0d10a00608011009050070802c40d00401845064512451079481c000d0301c2c800311003010113101da05000300b110404c5000701c00d40401408010304581c43c18400c4c91149a550b400b0407000e18020070012010300303000301540c0204010340c2d100b40c49030101e0103e12510356824000324a85803900540030b4807550088442c03421518092505441e140c0254000d0303032050380088014011290025101c2c01c0b0301507581401c03500d40c46503460561 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 907165638 1250 907164388 907164449
    0x2802070203190b090d080108070b09040204080d12051003020a0608150306010b0a03051e13060b0316180506010e06070c030f1217070507080a0210111c09020a 69
    0xc0c0414030b00c0c15030040c00b2a041906008960400c00c0d100c00c501c60800407100c2c43d00c02e006014039900301ea10100046000c200041c00d2100e809007001d82000e549005003400c2482e100c90420120340c80c00c0d40402e568a01d031246540c00f9201c0505841c05505580104090014601070981445144800b00307100c00e002030000c20520303600500301c46266031a40c0d6100b003186c00481c02440401d09000100f4589480d0046124100e0f01134812850780d41d9840b030700c20340c0240b107041055031107559621a5041c02d480078030481440e00c0510032409206842d186138044000614072403102414501070610481d60f030300900b00300501008541c1c0c542c40e8201418202d480c00c1d0f40e58001082204080a088108150302405014800c22a1186d15800c0b055041003403c0c510203c85010010710100302c900c0005003844060880d20b0703c01d01c1200d00340319071150554210751821003c5020b5110104d03100000b0b00c840650141c2410300300006200340500e82e0f001c81c413480c1490040c05940717240011940801d6503078910b0304c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 907166888 1250 907165638 907165663
    0x9050907021c210c0207081203011a031f0e041e0209060613080f1c0f080610090504052a0f0f090f060d02070615180b1c0b0f2802070203 60
    0x401842134038280180d664000c40c800d40045014281361000c00043c4041502e04075440c40e0702004030701014084140e550307840109594180700c04002400e28020b40000c0d1071018019600445c00d0a003403c1c24400c11440c0e2102d070400d0744c55000b00e01040161100924150420301c00c0c1d440e01d84410400c240300340300361450f4000010900c12103850300b00341c0a002a5114032a1160904186000e00c4c41c1401c44809005c0c007203250224005402081650501e9a0481540046480d01041d01c40d00c0380c0014041c4c1e6010380d42ea03c200100201400601d05110700d00000700b14061560610704919991200014000c3d0b03400e000c201c820104007650b8a84808005003040e0700e00501c000c3d0b80b07440d03e108201c001c0d00001d4007039802c14a00b1048110240c084c055001c195425290109105207068001d800030b410182c40e0395411040c11030226116441500a0803a002d1040c00800210302d4441110840410010300c210399425405901505a07840c1c82c4000300000300f4884056603d00881c00801d10308500d040c0003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 907168138 1250 907166888 907166891
    0x150103200c010b18040209011404090210051c15060c140a080d0b0409020607151d010609151d07020703083007121a0603010609050907021c21 62
    0x80d41948206500550340325030200c0d074150a01856020300c04c6104c40481e03009410a101000500801141a503070b080c1c80c4400802c0880e0380710882c1d000c10100724249403094040340d00410310078036110308a2081041c5c1036101108001802e11074007544040c01407807040000703024a0b85266018895850000204070750800c00b2140b03130170038900c1d02040da94001e942046006281079a103044503e083c1c0101903100b07070003d15060506482e9100c07816080c0c803c801140d80c20340c0d5140b07164030f2410315072800250203021800020b40e0a15100d00c0005071b0344030888810255603019018841c0b440305004a00c840c883c80050804070355510541a85841e110350005084140041909201e6a03020068202d00c002a9244806011400300042868013000e6035154041004242c0028446080b039100c06003100a50000e00f0b16048288081001648203800150000d001003006110301e090510505410141c1840240007115605640c02291000e400c480e01c00c0003000c0280d207803094004080081c450002c13100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 907169388 1250 907168138 907168147
    0x10050f0403021b0a0603111317190503040314031b0d0f1b20040e0109170f0d050705091905101103090402030406021b0c03070e15010320 60
    0x1544198012142140144594207070f0421006402040214085010b44419009414070b0400ea02030300308508500161201404a01c048a45030300701c504c0180350580b450314120390711401c5203003820865000308000074000c080321000a070002045408a0f40c000c1c0c061014021261002815446892130810800e41103e01c00310946002103050300612560f80c85040e10700174081030a844903042a040008080f40030910700e408550201c00b106001c0c45000c0d20304041c2d900c4e0034002f40840d2012400b50000369964030b500010008032a00710045890b14640960800421600001e40b0340700304101d4141003500d40d80030038441030103001a6051940018030044a02002d921084024906441003d01c0f03190001d4042811300d0241c807030a1106007920020f1450421740c0401d20005c1d520261040b9111a42000000e55071288905400c0112038008080c1400d00c0203101051318141694000d501c446032004140314001c081101c24051440e000e00703011410042581c40c0c8035003e0310b4082030305080000003d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 907170638 1250 907169388 907169401
    0x10c050f091f210b0f040b01031104030b04120806090703180b2a09010927020f030403170c16030207030b010602150a06141c080a0e030c19171005 64
    0x2550b501c0303c415075a6100540840c2408258140d40d408055640c00250b0344d000709101c0e003480d41000101d1174040c100407682c441900070405459001d43e20981d211400c2106008c00c20194405414000c80c551404504074201070001940d40c00010b0140c405040c0e58201800101031000b4583d0840354110345807490340c0c9880080b4002062903000d080e190360848050001c85044030000740d442e1802c06a550031041414078000d500c84c000c4098a6580d0000c404c50840c0c00c01003c0d00041007a070f2001130700c80b41c503810503140c09040012419450110111b9102c10404007c0101d0f003a00c5051111004144003500c0c181410380c180015500050085504680086040c5400040102c901108081146007035500d081540741200c5d07540c01086d1400c0240545e400852404a1483c4050218500001594400d60340e030b241031a84111500d40c0401c28424000005280900000c0403440044e10302c001540a45c100d5100c00056900404079a6491302c400b200c00d078003082106400ba5020010704018609010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 907171888 1250 907170638 907170647
    0x63004030f030b030105090c0d060f05040c17030414060a051b1b01080124020304170a020103051e0c1804020d1401080319050d020c0d0917010c050f091f 67
    0x2810740d808070741040c0000d5510b00b0148100e901c40d0107060003401802c0354400800003030880e901c1d030656415032240031507040441240b10302c0d80101c1c03145040c0600d5514141c41c0041400301c05944400c00d401c140000c01c020034066140070100c05084440e144c0d103102c5044251154001c181c6404480c100041c80c43c1c0c6000c60014003804a9810345000001c0d0304280001154686030074040c00b1850034031418072300c200f0428005010303032031842030040d00d08060f110048992400712024002e0300c3c592003040c80000b556014810f50341c207e5414000d80d56420b0984084003403d080140610f0f00002000400802d0460309101e003900c90340000303205540d11850000e8400181142c0740c000140140f04100005018000204030341ca10641c1c031910050b6030030fa00c0b00640341c54001000d4030040301d030200903440a4120074084440c500031107880703000701c43d802c050304100a00304030304048426030300d0700315084992a040020348075080c80080c0402c1d581c04400001c80c100c1c031886103c0282c40c1e56800d10040080d03802 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 907173138 1250 907171888 907171907
    0xf0a0b06041e050906030307020d1103120c03040e010e06030a030f18030609050d03290a030b0c0c01050702070812090f0301060803030906060103020a0e061605030d0c02160506300403 80
    0x22221503600d0780b039117001c240d147e1040d400300951004400e006800052520381001c051100e004080c1c2c1c1c100d102c668425100c5600c13244010301903800010701400f14011801010380941201000640b1520785440401d989544452000d000d22180100400c11144074202111020940038001003060b0303582e10345080a41520780e41114180543c0128aa42038846d100d402040c407590008005400700c00c081c0c0351400c0301000303003280d0030100d5454084040f0304002c440030700030f000b200d80c0c5540c0c9240f501b074400d00310355014013000115004658200808080001c0c005401d80100c0d04040e0748084400c00141e01c10b015440464240d400e043c00040c08100102c00b5510401c4d00800351046645d8603c0114100d1080d80e99080100324128900300301410300e84041e0001d07a1000007026a000c095480382440c2d0f4000311303104600c40340c072214803042d40741e410300400ca1418801c800c03040d00c0c20308110000c0c042d40103105e55130604004402d0f100b40305e041c02001c09907003152a2100f01032541424140281485c3d130 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 907174388 1250 907173138 907173149
    0x21315020f07080a03080f0901020f0a0507060c110d03020a030f0908070201090f0e010b160c0e190618050702030f12013008130915060201140f0a0b06041e 68
    0x191030b20000c2c03034143c041003105002d03074181c2d80c0e8105c039070b603610180318030141c01762800405640c00c0c04420b1100c035142c801040c1c10030107030f00c03100e85500c90b928101041e0780004a14030304200c8924581501e91034002017030181c070800c9040168541810141c1207005100303080940c911981010340c10000c1c04407a000030311141e4004e036074054106403205494545554075104e05290595040010030102c8142d0300684600480d0103a1050f9100c096100d0345501d01181d04148040300c0f0f1b5405100780e4598403815080b00c00900c0b0300070f0182c070340b03002e04104400303c0c034a4403000110b44410000c2e41640c82481140e44182260400c01d8507004c400850314080030f402d000c1d40107c4586442440b82a070070320b8119801040032141103680d00d480c1c5565640164000c00c109081700c108a00002c03c0508440c0100302c20300c425900816202850003100074250382400104805460711b50051241e04044d041074140e000100000c0070440400d2440492414841d6a1100c0b00400360020410840c11640c1030f464220741 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 907175638 1250 907174388 907174393
    0xf06051f0e04110108010b0a0c08040e160f1715030f07080606010305011211010e0f040606170c0c0615010212030705071a24060d02040303020a050123010603021315020f 74
    0x1c01e19401505c01c00028042c0024001c0240162042103120f220560540d170b1090641c182042e546481e401c0c42c412041d10030344d134486007040002e80c0550b801003100c0b2800b0f05074900101068502c9982982104000e407070291103400124141c56a528104203140701045800d0441c0e0003643d80300c0c545500e80c5802e490140c0080d040000004104210301c40090308242c0200c800300f00d039640f0100541d03000fa54135030203a8011140448901c15507540380b00e850018525504d542d000a03078640e43c0310714092002081681229000d100250390700b0b600040c99035010221900d0f400100b00b01070f0051307203058216248260300100000411030b00302da01c0000b0341340d00342c032801c40901d42200c104000d104c903040440341c041e9071040d1900107010f440815000101d00c2d40c40503000503d000003d68040d0182da101da0810360241c0d1040404108000c0c0900c03482569000000488911404407003800c94a410184079490426030041190110042d200454100800b90b1700c0341102c4070100d40c2c1010352101d01c001180351460 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 907176888 1250 907175638 907175663
    0x31204050d14030403140d090804090c080c040e01030305030703150f24020303060d0c0509090a15020304020916030f060f0609080f03090616171e070f06051f0e04 71
    0x1803295007568001ca916807280d54242e0707a42194140306d50016500b0034039442e112405c48001c1011800280090140c2e080040b658031004000540780c8100a405061000c0003000104502c000440030941981da15103400ae560341c0f54071000b02c000d4201c81560f100c000b4500c81c0d000402d0106c1d24840f504a81040b0a06400c10808140b103607540d41c0444802000742e0010000252680340c85100c400515102e80e4840365416103840c0402c1c1c2c0c01c08111800c00e0380d1340c8400350b501c1c00d0224441480c403000e071500c0d105502e140740c50b5010800c115005048040c0c8445181c0349046000c1c041d4118101107245200104a11036503010002e44074201480740101090003860082101d01000c00c0e407040482503c00114500300442081c805542e000400380c0544c4012009454005201e03200c1040d059102004029103d10101482c10840c0c462405900c1021208102c0303440050344501300088226045000000c5550300c020414020100510000c6a289a000301c042500701c0c800801e54087e83c0150580600c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 907178138 1250 907176888 907176917
    0x809180c0915091e0a080604062c0a0b0a06120b06010807020c01020c0906041506090906150f080c160f1b0f0b030408090d14150106050409020705031204050d 69
    0x461103050456900408412135030301820301d1021000c4840300b00544140310540d903d42d58241882016a0708a440340c2d12100082401083d0100d010010442503c101000d050001030160740d4020300c0301700500705441070000404451095009200416880401d00702d125170915051440384400c07100c0c40c0c045121700300410080342c40040c2400002c0d00607001003102a102404110703c4450003041c842e801521a0005000c0c2219126903e000b044191521450340c3d040050f00c2e400d071105030b08151580ac1c840e040f55042d040e03014184685a8516041040050f156000c5507091071013803041440030761004072038140400c46030030140c1041d01e000342c0441d1540072900c0c004c03824a40302d901c40c080042c207000d0000d12484072544020754100d8440c0e00b0140c0340060700004200340c00c01c1c000080d10a00384100120030509414410224144100c488045287d818000090894012401030000d5254007040c0c10040000c10412106c2d0700b4103428402c5918a4285012503039003401c140704800107410305104114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 907179388 1250 907178138 907178179
    0xd050c0117060a0504020f130e01060f02060c03070c0c0b0c030702040509030412020105130305060c09040c02011b123c0b06030612010b12030d0b0f0307030809180c09 73
    0x401c001803180c43d45510301000c1102030b4006001120b4080302c1000210040014148510014102c03141e0000381503151070b401520780d03140e80820304255042201000700c2d401000c1d0849500c80c1041c1001030281405080c15420740000e500305102c0120300003019844c81300004044c0917107510848041c01159101e080303054890003036104203000040102c0707880b801580544013030461107010182810754035075280c4031145840001e4070f41c40060500002d43d20031700e04003402103c000151600080c082d02c01d00c100c0789140790744654010320030031124140f00000301c4195006420b10959030003101c001c0d5031030b402c901a1140c1c01642c200340d160150010040001215000d600c0d881c040003458582140d43d4081449004c1190200300840c6541c2d408103803845903a20646138050780e60400046803540c410200040841d440310801c28805c01400704070071540c1e6070005500091f80c1d44205d0b001d85608800300890b04407845c04030400b031602400b10400c2100c0f138140d005400e864004880c048441c0e00c0072080d039134 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 907180638 1250 907179388 907179391
    0x609090807080702060c0601150e010e0f010806060717131a07240f1d010b03191e051506040908161401230f060a21020d050c0117 57
    0x308815414001c0d4000306110601501c0707500d001070b00103442c14040d8040141000000d0300081034908402604e04c1e200c90b400071201141000078201035400c2541c400008041040d411200c904001c0981c00007262504c600c4140d4582580c00354070301901c0e801d110140344003504400003402d103010a00f01c002480003800ca62000710035040070001e07407070b2403090384410300f55400c11116608241c1c051911003003006254480c002d090401c7c1c3e5800207036041452204400d03001c00070304441d45a0b050520034042664007140c0c0b100d4080d00c552030742404198501d01000580c24842c240e50100102d0700040c81803040100b08c18055556071801c049240e514402044111420042c0c0500126800c1c00456041800280e440c8105406542900c15500c40c41d483d060130740c0e86018015441c2c0c00e106103d00e401105690071a0740100c110511108140ba00801040300c41c0c287d03125000210111404100d9440d5400d550565500d4010300b108501045078103241355201002c0e001e0710300041040e41c45a01006003209c0b00da = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 907181888 1250 907180638 907180643
    0x70c03020f370f120201120b0a1e0f081c050a0909021c110403020306101508041415090c09010609060c030e04092919110903010c02030d060909 63
    0x40906500d210031074034036015070b00d40c40310307a6096407000451142c800c40440401000846100d525041180c0b00040500c0d610754210103001d400e0003050481940c80084800a41e64500c404508000b200c1e03c10548101d03080e801520101c17104040170a001e4800700b0038801891122155420041c11130314111032502c41c0c035102c000081c038102824003540c14141c0003007008842a12016001c50000d2400c00d04481680007110fa43d10000101042142000e020080d0b001b02004050b070703401c5180c10b01001041103a401a82c0030040040005010481c81005070382466450f1800c40d0f940041d40a503941541c1402d450030000c911a044840707072540f40400586c0d041e580d096480410340b500d0081c090320084900d000403030602007076402004094440c1e1240c159294080d2101c2034080c1c0b01c10034032640c0c0c1c00e811400340782004003540810020300a084007031101200103100003d00b1100d40d8000c07110740e0242c400820f03415400c1c120703c0381c03226a001011342000001d0303000401030140e69182c018122600d0b207800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 907183138 1250 907181888 907181929
    0x503060708070f0e13051602010b0d0f080906040b030106020303041e0c051003060923060d0b1f03050105040507030605090c0307031b0515070c090e030304110f0402070c03020f 77
    0x20405901d100300c444c10200c0b08083d0688052000d2254480240c0f6021503200c070104030702d403e8071204660b09000f901c00640c416250400c1440541c1c880100c00c442040010382480c0000480481c035450b2031040740d00034801c00c46d01c642c6079610f0b40c2000351a07900c1514280c5000e03056004101c1c6818440c8008504a648058010250f51900c0e091041d8a10326000e08001d060342c2c7c3d280001c04a4150240f050b0641030024148201c0c0310041c0b2010144401914507406800c00d4405180090642c45031107411a00360003032601c0c20140782c60701d40b4400c030041e00010160f50a12081c4000c000f400114101903034400e203000c0c80380360355800c0c0490b40d5008500e0919855808130300c0c1000230a01805454400150510640c40080d403101e0200b003d10001c005200d24040c8002010414800794011200c080c005a901c00d014a8000d90f407140e5590001400203404031051146440f05a940c0a2100304d44100180c429510f550981c201300191050a210907070180e86010380080340392074803491500000462040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 907184388 1250 907183138 907183157
    0x90a0b130c020304050a17010c020d050403110604030c240516150b06030106020f01050a0213050405190501091509050903030115090308030406021c1109060f041509050306070807 78
    0x104103000d025110384440c10760204010104e0b0340c1d200c00c110300c3d004e01602848951816040d0700d42a0868041d85003208c00c540003848172507009540402290112074004a044180c0801c82001170041d11450744028250b114003080051000d501514000001d060200301002c032a403101030a03182071049019404010707482c5206c0c2c100003801d00141c0c2690003070840c1c0005903890f0070001300e010b50380281c001101503400855111580e42c424000d00f64030200d90001582043c55140172102420b07060301486215544520014031002825100904003080808041c06503503513560a090040080c4502180304484031840411b1055180c05050301810503031004501d982e1a010403190714a403281d5882c0100031110000002140c03554003e1402180500743c01655a41034440000d80080c044991070b020390b04001c1c0c9485900c1c900c005441c0081010343d511a40c841c00301594000c0c034807468010f07a2010b0581c2070100d21503644000010b0a603441507003214007686a501007682e050720100c6041000607002d91 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 907185638 1250 907184388 907184419
    0x703020114240102281e060209030d1d010309080903010c090f060320130b03070e1e03210d0908030906010614090d240b010801061d04020a0c0203060108010b090a0b 72
    0x55080807141c09180c0c109000710f000d81000306c81d000f03c410162103403a00802c91024524042c001034000340035904040c00005080800e460254059004203410315980d001b005060250f070700100d45003e00018000c000c0041d8141000e8021a181d000e00340c012150910080703a410f000780700700035180d585082c40c5e45060303081003083c44c5507074480c0c220041c190701c206400003842030006e00075500618064459850075080c903000c1c03054a1816240d814500307518000603803c036840102d542c00070010038036250007007085811403182c1d861280d030040022103442c0601010510005502a6002d04a04d174295181030f640c0b10001c8500d42c0218048000d850410016001c03113103000165000307920f100b12650044041c01903a0846419084188000c246403110400300c4c0319070303214009038007600590500c502c0c03d0340a82400d0886011108989000b039600050f2a001c3c50701541c01080d0b499030040c100e641640e1544a100d001c2e140300c40001d4014400c080c04251055101c2c0142c031064040902075150600c81d51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 907186888 1250 907185638 907185703
    0x9060c230f1902010e07090506090a0504030509240a02011b020d121e0203090f0d020f0705011805040c09290306090604090503031509060a0501020d050703020114240102 74
    0x42d08280290744d030310b0640c0095a441409004001d0180420004113440c1140501200703042c010540f0142504d014200000a60414290b8036140001d0f1042d081c400c151100c1d50301d0300b83c4441c80300d298040700450303c8030155034150003488000906d81800349040c1c21100040e0780d15002000c40e000801d5510b0300040c5505569032204409a0540000007607420004a0348000c90f40143c071110301c0f41d00036100c0408a50740410040c1c0c1c0d50b81c0c40d07100500c61000303480030300d0b600c51300706009841c10001c4045401c1c1da500e08101c8080b01824004101704590425100041d00c0c0c040140304006030443c400440092070f0701c40168041c01d0980300314050f85550b80d24002c21491510007011558010ba441840001160b01000958071403411000407000310301402040015458000385000e00c608840c04040c03045982c003080040e0b03d4882400c00903200e01040c5000d9000d00003500c0c041854121420030172958a02451101031100701c0d90034500741495003400126110a00402e400a40c8104a1003850800440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 907188138 1250 907186888 907186927
    0x20c01060e0103020f090901020d0207030e180420030a05160f060c030c0618140106050414090304422606010e031f05070912050c01050a0309060c230f 66
    0x7d64000500c0d2040130b500282c126003000790283d002403500c030341412681c1003c030121076420348a103002c2c1c1500c3c50155600b03c0c1c0301c400422104c446c206c854280c02d000392800c0100140c1e03035a001003500c140044083e0848042e00c00340c803403c03000b00d1911400003141801102c040860a4055864180b051800d440300c001420f044514121003803000300c40100850b11154021321100101c00001c1200e40c078100400090b5130703034030322100e407034194010a01c0f00c4800000b08680450f41070b466410842852048080c50f01c4040c504d003540944407260403126185413043c40300040d02c0726616030b0b100f00c000700c0325480c041030800c00840861a4420020842540c007030301c564160341c038009084803401c0e04101c00201c000c42c4007100c0340e8001c540b5082401152908010214007038181d00a0400c801421626100d83c0e4000064000d030511000180480e8401d100b0b8000a100c16042203090101600c082001800c41c0e40784159581b50303001c4c0b60905010028110108c411211401500c103081c40440c02e00d45614403003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 907189388 1250 907188138 907188151
    0x2405130f0206090a0e180d031e051b03090c0102190b130206040503010e070906050102150c0904060b03070819020c120d060e1305100b0604170c1201020c01060e0103020f09 75
    0x800510020700c0196410302d4500c101c5000c28400f0104d0071b507460031854140710700d0703000d401e050a0004569490656200450300c00c1951030000c40d0070349984001502264904844804a0b80d001003004074074040001e024456070001c0c1d00302d40c00c0402481003c5034154075288018840001c050204c0c2802a07503035040c03460750340014001840d0941c1c400009007100c45100f40140c20f80c0040804101d030160600c90170300280400c0c0054018412402c0645020300d40c000c181005108000c2205080d40d10355a02c160040e0840341080c0d86e5900b0105800f030a1010708845024101e905100342d895800c03054020f440341c0c0c40340311009190040406a6031f4403907412215100325566520000091b0034062403407160b02030f0b0640113080c802c4400600f00385081c201181c00c295504e5046c9911f260080e103a620880d4100c80b203081000f407241240ca05202e0411480f01582a80440c845120b01417055043d40104500c905c2e543c000c00c1010f80c0e0308500c1e542800c09104c0039500078443c1c00301422508007440004d50081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 907190638 1250 907189388 907189399
    0x3020f0a05091801110304020303040b031305070605030a240b090d050304090903091d0609070309020d0308011805041211100c0206040c091a040e07032405130f020609 73
    0x640711400310300e00800440b5401946200a0800403400c0828810042d2408025040500d0351602c4d801103070b42e9105911882482500020010310001800c5984031902540541600c2d0758980d1004003c065030010707200c0c48a0146061030000380c8a403007201d039045004200c0c10408581e464609004400d400c9a07011680240c00c901400c400a101803000f84098403500d040002c4214039820001e00d0f8603001c0d00b0490301d4072502c10303801e44429203060740c031030748a07604864107081541c03003a20403400f4020301c4130000d4000300d11214910070141c002c04080c0c107032070300c8841445080c82003100020030350b10190b601500c034401c803081c0b584507240302d5079150003d4000d44c021107401d411904800e0007210124444180141c100d20140410001d049600100912030407009100c086180c0f60080010413101e400c85114036a140c0000c482241c0a1021400554014031600c0c999400030038040f1644070100d580c1c0e00c9003454140010b8040004d078582030f40c1541c101400d505109900e500340302059003e103e02c0d95005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 907191888 1250 907190638 907190659
    0xd09290c0d090503030a020601260105160e0307060509040c030207020d0312050a14070c03020709110c161d0910050a0c080709140910151106160903020f 67
    0x48405002002440e916000030288012400c1006203049119040b6a1090f002044104030159000a9450644040881d010a121036901c071802c04d41e000c2c0c00500c50b465091000f00440c140d00700c40d0300c140c1013095072a18401c0c185190100740c0c40302058001c46021030028002410030f82000e5101da80c01c0b5a02c2e040040c6800d0390794000501100307110008400060110694403000ba685000b61900452041c1e014000c51400d444050300600c0001e080d0420059000c01000525108010400c01442d100310708010046444d2601c411541c40701c10b01184900c50400a0164599000700c1c05084400c0c4214201103544513401441041c00301400200c850300c18103410110380c144038072401d4041d034110304001440c03800700080075060000040041d410310a003140c0804c032510f00002c0e00c001c2c06d0300c01c46600559035a82c41d9100745c000c0d515001038906100b070400f05e00e0703c1a005081c840030001600e0849900b80d640b2030341c0e008440110944000050641d950820041c2480c2c101d0f010007080c020f210030f46030f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 907193138 1250 907191888 907191959
    0x30d1a041d031b190c230607020f0103111b0601050306071b080702060a0509122e0905010501030c050a090605100c03051228140705070212030f040f080d09 68
    0x1101003030541c1c80180c880420808006c441861506aa200760400100712812000264850180b2180070340101786455080107980e1086d4000d58003200704000c82500c40b4042001800792148103104000907109850001c1414980010b80920940c4075541d01000004012060007100c1c0c1c80e0081100c28100a01c160801a81c9100c00b6010340601c0c2d50340c4c580c03503086820801251002c0b041c52158960049084517070201c00603955480c035100210b1000400c503403040382c40e0004114040020f445946081c002004204881003114101c950450f266060b540d00d07512450110b654611401b5401350300b2506201a19000d4078001d00c9075402400c1807800d0940c030058001d40c28808443e0401d001843c20054258034031400010002d2107a040b40400940084441a140f80700d0007800c918140500420200c0456139111f003400003c0a008040d0303500c90280504420346a0414042c078a03076808680c801007182d580014180114051a03030354000304d145080d0060104103d80100342c2c01400120110002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 907194244 1106 907193138 907193173
    0x1030c26221536050c1206040b0415022d070803130507030c080d0306060f0e130f060303020705040e1518030d1a041d031b 54
    0x111a02c0707030f00900501e8880c141c000e5001d0540742c00921500022492150941e520800442c0c40c0c01d2144410000d034030000f90001c0d00705a0000c00080c000c1404814059013150184011564201d04031041e04141c1c2d11540d0328031852001100e000d610516130741c3c07903001c2ca4800d8418450418113184d41e00700071880041c0031461010613201022050003002e1040340000c580c452600180c003a40e862400f9207464035044940b0100b0b141c0180020940e0040c0c0507000c04a000b83d695076001c004640c104408403121026010a56644814001a241d0ba52080708013560184e00188800e600d010708010640381d0310181100e940e00a100e481c0c855840e44c80c60260041340301d00b1040510f00700820018a58022001f001d02c1702801d06139400c140451041d40c0e488403250941d0107010b8442001041d042000961b42076904640c020420002892101c2c42d4844580b070703802c001c1d20030045001a1041 = true := by decide +kernel

theorem cover : BRFrame.Cov 907014388 907194244 := by
  have h0 := BRFrame.cov_init 907014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 907014388 ≤ n) (h2 : n < 907194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
