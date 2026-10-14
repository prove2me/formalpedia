-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3286
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:12.575865+00:00
-- url     : https://prove2.me/submissions/5cd28632-ff87-489b-b3c2-2d7ec61a5d69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 590827338 ≤ n < 591007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 590828588 1250 590827338 590827417
    0xb0c0d0e0f0a080601060e010809060f0903070b04051b030a05061504020d0f0b0f0117070c06110307090f060c0506190207140102030906070e01020a0308070306090603150f02 76
    0x400907800800d8450400c10320140a00e0002401150315003d0010300c440a8204c4107070400250000303110b14040005026078110038041089070b4140d5038068218610b000d17242001e080d15101100340001d011010840908000c0e9088843e554140c5580074145c2d04c1d140c1200060980e4040381c00900303681044100140720200090002d80741c641c0c00c40e0408140e90305025a0042c80340d440040c2e0419141c0020003a4440400303003010810414603416204e084000104104148002c0c40d05100c00c00c05107038800d0305801d006440c415100d080144004000303108600515564804502003c43c0742400381c010708803c507600000800d41075542e8001070094030703a0240107a8559809005400010f04010320340510b01040c240016244e10b07100060b42d24100f4050250018810702460841859a0200700c08903a1609401c01e508140c6482c1c10407002001300d64030110b211440d000c0d0101c200100002403c030642e01c2c4503403d1202000d8181210704a01c03801c040540c11111000358540c840c02d51b49900700c520308 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 590829838 1250 590828588 590828599
    0x20c031e1905100e070801020a1e14030408161424101e211e1703070e03010507050a03050c090d02120a0b07030204080f0a0305030c18100201150b0c0d0e 67
    0x15910a4131b90b09903004202d888001c00c01c5c03205060f11454400180181d0014640b512a4203406241d20b10b90b820b10010384043d2980000143e90040600d601004c0d0300ba282e4420420703012080038607449511800c55800c04200c0c403902090748022012920f100c0c034040e00a548100d40060703d08034111940140c119601010188a07200000c0e80d013203507845030011802c80803207154541105140441c2d41000401d403007400181002401c401050354aa404039481403800c080d5a600c1e10380d01c0081d9032500b650303001c0035815800c1a0400a44c25030010150541400300d803014031068446100c5c41005000d611001900306118042e258054900500c44501401d410010750721980e620b62191070304058101c1d40d0f038001c203400050401940d081044541d00c0d03410b10750301601e00304c5600e660040091002501a0702115000f25003405541d205000060000c8001803c80741c2010103050064040c01080a010607018406140000d6600c4400c080707404007140301c40035203007038808240c040d0b510b0051182e0003038005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 590831088 1250 590829838 590829853
    0x1090801060602030901110f0a060c120f0b031e06061504080f030403120309020d060b060c0109060506010f09060c0807080c01020a0c050120030f040201020c031e1905100e 75
    0x112080c440c0d0000303803001c0d5003e1360307440204400151240c226400041103982c095070803040b0f0710f04085035035900613a01050204a155400307900b1602a04480e100124051900750750000c1d00301142e1003407002c0b030025030588907038500f40180c00031141c940c0c1318025007640010b80054a14500707a424100c400c0703c07800b90a420a03444103c041d1401c50110600210313a40300080c2441484214403402c0d507030401c5071400740706010581c0e004c51a40c403c80500180b000da169054200b896540c1030641d80000e1100c00200305030100d90501c04098002030b20150301081c801d07000303d24803034803411400701990241d482da803003480340d81d5030b60380c0f8164000e24041e10492000c1c0805071003410207000070300031100683c0c0d031002054500d007800d07821220380007201114242c5aa41d20741052840c1000ea03540002001c007840001e584030700060b4203041c0161034144c6e15000741040d03501100c494084120902603044100c462082003865000b4001c01c0004020305543d20200c1401800c140c20b406c0400c840700c4640c240e9102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 590832338 1250 590831088 590831099
    0x619050d06020f04030b01031a09030d111b070504050604090203061819030203031602010c020d0509060c0105041b0509190c0e0603070207140f06190201180c090e0615010e0109 77
    0x100d4000345c008403008402c6c1401002802040f95071072520090401d281c07880c0e410000c50320380e5070f80b255121104d4039a440f81c0c03100507000c680c070f003d86a00040714041303101400d00021006890b903542c0c0c05a180306070300c1c0c000410203605151003030362142176010700100351a0700d8190700c0400300425070540b90124402e0302420240f851100b40d01600f043d1180e0020758580c2010440b02241145107004901168509a80011070507400510200000b10310b00742541c1d01c00034080411076078803500800c0c480fa5070802050104000740005503804514401c500300c00541c5c2c5030010001250002d54811141c1c042041c000060012554840b15046000303080c500c1403159901e010805640046030000c0140c0c000400c1003001d000c124507801a0200c0850b545510301c14a800000c3d028010500480c6900c442c00640d000901e00035172086c0c10417044c00800d440c40c224203113860b5205104a001c0c00c030900c0c0c07c2c01519200100300054075405030a80e643c003480d08100c0b1000454040110410036030400c1100d4000007030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 590833588 1250 590832338 590832367
    0x1306020703030504060c02160b091318020a080f1b060c0601031518020a0b1b10060f091503060b0303090d0f02030c09090a0b06010c0203010f0c080619050d0602 70
    0x1486100c2d880104492815041031400c9481701200c400954001511012280d1480c03503a810540c2c4040116640303c4220741c010484140c1495116045140b800001c107512551200c085131445108840810551352030f03442031902c40c4201141d011066001900d60803080350604e501d007041060142500d0704214000241e40d180c50000c0e4000d88100240d030700300500c0b006845c000c8402d42c0704503028403180d548440e4041510f002031482206861440443e500180846070303814900321902d00d07070858500b8040989030314001d000501c1603c900030312590000580e000240182e5074183d40d403c011105580c9940ca456015001200315268540010491181e0942e11092101640d0b405206103d00c0b40c4000d00c14035140001c8502c00c00c0c4141c0c04842003189000c80055500390507030380321700c6600661710b4010040c3c4007141007040c000c0d815402c2c440380060582103a800394281220650b5100150340751075082c00009860f40c0302a000c18048480300b8085410701c3c200543c402486007200502d0304890115011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 590834838 1250 590833588 590833597
    0x4020409020316091b1d01030e0d260c0d09080928050103060510030c170103290603030f070f02060708030106080108030906031f0b0a1101051308040e130602 69
    0x441c840c90050500c0020214070a13017521204450148803101c0d040c02c1d010b01141c1c80b0320b110200c0c25001108880d01c1e0391280c1c120400050701c40c0200d48040c0440000070b0105050040b410034968101c411000e5400e00500581e07026515504001d0300d00b0b03240c450303100050b000700502903480440400c1400e81c5074403840303030b0705007108500c541d440c0f030950b101100d09041409580c442410907082020034085079454100b030a42c452107900b00007400803100341040e42e0b100318003840d00030801e111a000006001e107545100d00c800b00140c480c0d8065110490f254041540183c0f45140c0550043c003499045804000c000e10190340111001c140c502d801c1e90010301e40e0b40c00b43e0011124043c001c001044116040440d046c0540600006582060200c501040c581c0c003005207021108103030780304280b111454044510f0302404c001c0c001155030710000900a000c80d80c2d8400d11407a60741ca4000010080321603403440d0b1b00c1036030780314480354601494102101c01001c4d014000268440a40c405100095403a10090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 590836088 1250 590834838 590834863
    0x20105091912032606060d09060207061d06041707050705040914060a0c0c0230061501230901050d0606020706081e04020105031302040f06050a1d0708040204090203 72
    0x1815035140c5190040011810901080da06000c6113034480c108003140d00d040780e000380207840302511400d8450840d03026100c284000360202d4400107c090505c40d0a420215004441d058802000d45005d46202e545160885024018072100d08034007004108020050415a0040341160a0261540001011104c01e00c03800c07a14055041e200040c007071401d000040e40908030300010031410381c0c04a0090104000d07808001e2055200300b02c003c00e00e070b119413814080240c101a407441280c2c8000e91f180d0b500d10040e500f01d055000c0c10380e402205988242d600d0507502411901031000c0028580d24440c00350412224141401010320400c1402d120034801c540040103545d00510840349840c1380a0112040030340300c101c00c00005107019100b0b0410380f403c1a0055428602550780e0358445e401041101042c4400039882410986600d40e1080386802101c2075440848003560002d507503005c07000c00c06082149107104480c1b0f00c0f0004100c0c600130185d2a80c014005003000c00c09035950380c0042d0a03d11141d181 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 590837338 1250 590836088 590836109
    0x609060405070f0b0306041e051503070f051c020120010c0e040c0516080f0c01060518040b070804150204151101020f0904050a1103070c060b0303160201050919 70
    0x10882406010003a03030380101104410b075240c40b4140711307802c04180320003410035006a0300e806900749074200200c0e90f005010308071001088142000e80405804600179a070080c40792207113100118554102c140f6400441d60010320003202e50031240100e07646500c101c0816030501001c04100000c08852000b403603508041c0c10700019481d2074100018014078400080d881c040c0f4500244140c3c15a040070849110400c8801c1045080300c1c03d00c2c011030a4450f10601604440000c217600c40d101c84150010010345200b25001418107451100c80c4d01c0d40038044a014020003801400309100c50301403006550024081c20204185002c0c40c00d02c0010f1380d025602400c00a40180f01101c0e04503801a0f81c03031302c1c090b0014004d41c544804c0402c113001074001c101c01140302e030341e8031340c0841e07082401603000c1c01400c540300d4a0b46843c3d1406600140c1032085401003500d1a80c24445851319515000c411101700700c0b0790039480e10348100288c00448003600076a1205800c03a04480103c8500070303090b0701c135a0003850891b02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 590838588 1250 590837338 590837341
    0x60d050d080a06150912110a06030b0a080a0b01051e0d030806040e0a02011d01050918010303090b1e1804051611060f070f050d1401030201090e131205070203060906 72
    0x3000b9040340c12560024a0461030229240d2145a02c200210308a400d0055040d00c03110050078543c4920b400440782c02c3c1d0043c900c28000500c1c0341c040c1c1240c0d18030b03901140c040319569a505440d82d10750102c0c0800070400000c080050166180c811000c0c030400c000216014a442d0454000c00c403e04a49007041d40810a201c0403c0340074900342c040d00c841800040c000c0c1c002c5e0b0050754000b074000f1070303604900b03404401040202c82c21a4070407000c1e201c21500041041d500b03046c1d1b01d00d000000d88000e000a50010b1108203000c5540501042152a0345604140c40b600300b10450785c800c0000c0c0c0140c10050401104071032241c000303a0716805140d004900441e6040900400404007034240481c6501c0721419030003d100300a02c0f03002c1300d0070040d404010b44c2004180d9540c0410201da0500c9288218a0321914000128850142c080c1c84281680d00c01e8803405070184d1950464061030781f0854a00540740c0d0341b90000000070740603504056038584103003000350070100345600280c1040c40864000c0e8080c3d00410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 590839838 1250 590838588 590838601
    0xd1407030f06083a030621051b0103090b24100c03032d0e060a09050307020904110a06030f0b15090d0c0b0703020c040b0f0312031e0c0306030d1404060305060d050d08 73
    0x3107d048103001d2010204181000c251340b8140c403076409040303000b0640301d00f90000c40301c1c0e40030307800542001e640b0051075915403030103040c0620400005030302c17a00915a8128142e80300d090502001100350500d450b00303440c02c1d0413558201c1c007408180c2a04e0b0004012b42241c202059000168210090640070340800ea004451b00c3d8640390000040c6010051800c00303418102248010044ac1c1402d90151210f02142d515414a0507440c032100c000290002c43c10503000960381d42c15408071190400c0a803040c05a034655800300074076403800c803940d601480010000380c0c100346844030385251818402c1860005090744d602880038103030030120303081d80580c02010084540d46424490310942503030844035915580a0341c00400d64668041d000c40c0d807461000000f140e140c0142202c5110031809101c00c0400d00d1401142440709900140c4000b402441a050000d01c0c40e800740015101a0b1140018141028130b401400c60142c213010b080d1a0304a0a04401007020640900200311201c000344c03103000710f500380310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 590841088 1250 590839838 590839859
    0x5160221120a1d280602040302060c160e07120b0a2304050112050304030b130503181201060602061b070203030703020c0a240f02030d1407030f06083a0306 68
    0x3e0f500c502140c01019508010074102418010a00c02d201441d102c0081e042c40c04e40000d110356080654490783c0465594011140020340b0503940c0b5001b00c40508540d43c07100e0000100000344c8001001c0f03503581a611445a02c1030740000c490300d90040548440c00d40d81c02500911807002d200302143d0f40c4048412015a04041c040d683c0100011070311080703c40e816071140d581380c0c0203d00006250f20718a2021507088520391011100868001050702e540d040d400d55050301c280913a54515000790f49594094002d10410b200f034008032622500500229a00c40001401c11030364558013240d088410700011001da10200084c0c1a031b94801c0d0000c289900e500300412100c90156032103040b044070310120340519008415040002400e090030020010329104005174198042c3c9500d203a542441c0c594003141e288002d00701280504280e4a003001303c905030a100c80c043d50000c4c080c44e80d981d030040e4a10021401d5440d0f0943d40030101241007910b0f082d0035000840700803142c15200000a03110340041c803644050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 590842338 1250 590841088 590841131
    0xf030901050f0904152c0108070303030b15040906030605010510080a0c09030501020d050105030105011a0906090f0303030f16020a030801140d0c06030e0115030308070815030a1505160221120a 84
    0x415480b10541c58501015520900e5010040030143c5410310000368ec0c851207907480e92001c49d410016251522000d14400500da0340c07100b170b04c1150520000081ca803c1402100030b4030f50300b079074840f001540d0740e03d0440043d140c9204010200440c10710000041a003e101502004051000204042d40740c0820942035440c1a0456221100c031582d00c034000c0c410070700444a00110580385161681fa0036000100c0701ca5821002030f4050100008004414880340955071003070035114040720303045000140480e917070407a0070b0004011940c81c10042c40340700c0c0780b131401c900240401070000030160010380d603164240e00340354401008a51500b520103032006003801140c48120041d03000780115465614020410000074291b90103000311240071a0150f00e48040c60620340401800b00e0b030b81c8034924a0042e00d6100800c90002c0418a00400301d05007190480d41c80c26405150741c018902d445000d1003121114001605192070104204002c80c80c07840d030034145510414001ca0b000070041802d0301084000c840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 590843588 1250 590842338 590842409
    0x1507050d0806010c150605040204060809060709051e031006060809070503150705030a1b09053d090503340501091a07060513050f030901050f090415 65
    0x1103071000c10459036400211107601d0b9411480b00e100d0303408070b0700c2c0700d000410302034104507001800001e01190064009840c0744c002c8144000301c031000d130b13600c0c003080303400d2040743c000d4551150820220005008000c4d003940b1143e9001000d4680c840c3c4103890b10703002c5502c03d41c48280030640241c10008080000c0c0454001418160b018040e41c140090b002e03280c056008000500307110300032010410880d03450344507001d00c3d000c40d400780481016096010b00150a05e104043c4101c0700a4804841d100000101c0d20100c0c4860b1461070002c0b00c0359558208030340e101044c1d0410802e002000050b25a020405d070300c25003c501c000d44828170180c1002a02d0704180c512451900440d0070000c00490340d00c10702c0401281c040303000da0411100c103ca00e0290520807906c002d00a10f0600040c0065680748408003c03800713105100703c40e0011001c0c2b681c1a103e02551050b180805d0003480880d92452a0700b00501c6e0212005200180d11043c54004180c0000542c00150414010050300704c03502445281c9440410b2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 590844838 1250 590843588 590843597
    0x918031407080a0309080705100f0e0106080c0103180b0c19020c030a1707170301140d0b13020406170f06010914130305090901080a030210020a0806090c091507050d 72
    0x40c0c00c2d1100d403424401e83c01038400700741e40c8034040410300030701e481a20034450b400000e45031003415905446018122103000600d8082ca0702c2d1082c041407005104000c11920b0120180c418404198010740c020140c0c100307640c1c07a00701125414000206001c40e0329220b040e00f40703205070300c580038850765031014044cd250303010555112074949406030340c0014210f10800d0340078541c41d403006003140d00b160035030140c0003006000080ba4100c00c81d14104140c0554180c8008801a00c003400d050010406441100300c4060802141e4002040d1300c80d21401300c02d685640040c2000c941d680e81c0742c240f003412044441e0440100e420203100380c07401110030b000050044c10313103120034010204041018400c0110150401c0f5186815a00721000c06000703000b0b0300c03800900148600310640e5154080d50315044280d10880c0140a4003811402d8007101e482034401d2402965a00200c45d81c50f00140141400d000e0004a1043d606000240e110365904900402203004c81164a0b140d1b2103a14200c1c1ca04480401c1600a11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 590846088 1250 590844838 590844847
    0x3250305040c1a0d0c05130f1805160302130b0f07021f0e0904020f0a0e0901200403030c050a020303031f14220e0607030207050d18051909180314 64
    0x4034a524140c0700004038030700700003421040390f05091b034080c41001d4001c000260340c8040090500d2a03400c0b034a080300c48603000960382c0c0501176080000c681e01200d41082704a8412042c1180078801d902801d00500309803003100059807038401c2c080c1d1395045045001d10300c0400003150011420f1404c0c41940002251110594000240001510142c0c0ca034001034003498815001800350369961540700c0b52260081d0070104105e8903070010303000750341041300c0100d003e43c20b0100a040940c40c145112009010903080103080c01d096990840747408040c11400c0c0c030303240f0074408202c001d40c1d0309200a6004038026000d01121404009003481c1484580d40012140c0482151100b01c0b9104c901040e090404100400300c0201d585100d0380004126110400f00c0d1841800304100c41035401d03500601c800c501400848001e8015a10200c602120900c4401e513824113051040049040c02c654400392400040c031800c44103a15000c41204403107038002c1e448103492101c002d01041c941c100c9010103810040c0c80324145031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 590847338 1250 590846088 590846129
    0xc0403031d030319031b0914190e1803040302010c121e0203030702160e040609050f150a0b0405060a0513020c1902041401060c1e050a05070603110901080c03250305040c 74
    0x1c1c9030503101d0020700c0000814420351710740e6271481d8042900100300108107060f440f10444200510101c8500000c5516406175100ca004000140ca0032240d059458181003c5a503a82149044007076240c4070520500441d284500141c0e28044510078041303500840d00c924102c80001d140c20905075900050030f9039058180882e0403840c0c0c1259205800c8107020075212901d01e881440c2051035183d810490180501c60340c0001c450717503079450145e251141d091129004800030401211000d0303480980c00030b4075030380801050405000f44555690103110040c20310803c03070030740743c1820404841c501039046445020030441c41c0610951036608414a2802c10f1507040000c05403c142d243c0310094800da0030f1152170f00c25422401c09050f80f02d5400700503640d502c1c0c01031800070759801244c0648008a8100341e1280d1511501406a0f016198141d50f000c90740e482d9111242e41540c005441c0c4844812503d01d9404d9004528810880805d121307500005c103450f15043c807400949958005405000301c1c00c500d40326 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 590848588 1250 590847338 590847347
    0xf0b0a0b0a0206060d0809150301050f0a0e061e270106030e030f0922092001020d0e15070c080706020102030c090111162c0c0403031d030319031b 64
    0x91004c01511070072031020a500b84078216001c0d0b44011a0b00909520702c1401414485010754100c800c19514406105000002c108802c0b4060148034500c3c148800080d52924184803030440240304040c4c070102e0320b10b0300c0b0041005203421948040c12070b500f00e4115080072040545941c010601450200b110101243c030781340e160720860000303901d681004110071006a84000b00c48900e6101d0340d800540c02c0c90b0300700141e4042c0c20402029280c006e000c0c03200c1903500600003d090454038059002d0710345d400c2c0950083c0d4280c000c03800c60303a030451a00d600700040101942c1c01010018020820004054034206c5618644507664000008590041c0180a003140c00142528428030007401c041340355580300c003205450698a0a90040ca66452070b00006203c4041c0305800128420400b008102d0b60020740b0295051500ba60b4500c000007003004100b000c648249412420845000b5484024070324020000b8956040b044c41c21600418007100004055003510600c4d03444074841100400340d0780c92040140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 590849838 1250 590848588 590848591
    0x606020114100608061207150c121107180905030c06040c081c11100908090a0f0b030604050402010504030506040317090d1d040603080403050c0a0b0f0403020d0f060f0b0a0b0a0206 79
    0x14040d0306c00c4020b0804101c01803207044084d0406c8001002030f10646c103001061b4010404d02a02c142e5400308555422511035105801001001c0b801002e4052404034000c106030170b48824001d083d0b668114400020b10280001c1a0031408200100664245400d010b440742480e80d11465060b441001c051451200648550424078018102026041d075459146030516481c0314941ca0698585001d010402103941d02502c901001680d4510980c1d44540850000307001e103010380d0917010018070001d030b010f103815040681e0140c0306140c0203003020740e00d07510140b40c60002e440440118681208207004580d103044c0e07090b0b006035294010a007004030340390040c1407071921400010120303c4407400d007140c40e161a00030074015641321a05554450703590521580380c0451005a43c0f241c101d50788002100c4c1e829405840c4041e442d0240540760515590030400740c0c0000c05000c5508605001c96100450030502c6040ca12610030341000c01c0c1041d120302000350304540c6070030010300c02209100b2126065800123455 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 590851088 1250 590849838 590849851
    0x90506091006080a180c03060c0e0a0579030e07030f1101050913091704031101020f011505010804050a020a060504060801050102120a05070311010606020114100608 72
    0x820741e54072403820b01c00c00b60019000340c1500d1000300703105c0c504010081c00900d00f224001c0c413040203e003542040c1112141160315502c0e6102070002c805200c00d1034090030300c40703001e900042c0101000340040e80d014030038040581036070040c14401c214245000300f090400c0c2c04511155800c60030090312418010030b005242120220000c2440c80e02003061800f0350310400c800c424176802c40302c101780e407841c0003c400c3e441030404940e0980110700c2c40003954040d00075a0b40c0300c14000c06175100884814400b00040182040c00d4898030980c4911402c0c00c0c02c044000c20245009503c00b0410310004d0001900d0001030203104603e5130300d8400358404402118810301c041d03500c2481e00c0c00407511181803080c03070245000780195201d0210100003681c590400020170480f1413980f600d490a80ea82e200598850140c02070f44100160304000c90071000344030300c0041020758403d00300024036000d110320f07085c21070340316400400c0545c1d0354444443d245107203501015445646034035108055400c0001c000d01a10025010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 590852338 1250 590851088 590851097
    0x608030f2203021e030f01050c0406111002030c190e091602070314030a09120309030320070e1f05030d080c120f07080a0e06010510050c0f0304090506091006 69
    0x8004600070840d0380e08000315001882d0705440000f182c240d001e40034005480c1e511900c510140c0c2004074206010f144d104070903002400c1e05007450100141e43d03a05440994115078050701200340b8030300480e440618001c2140b0027180d030300c94100c0462035090b040c1030700e01e10040c4482d032141c240547e503541680c180e0000c4030200c008442400280240d24000e00c90b040109501ca03100016000d14000202034101d0340a69926410090381c0d803000b8800c10741c112440a000108010403d0020034042d60200a0a9003002410200c05200c1105642001752a8100800040b0f8400601050611000820749802c4103002c00c80d00b1f143c501400241e5950241c08845c050182c641c0028580f10307140b1081d0307502c0c84446035010000d40341c02007d060a40700202e89400100d503400000ca085041d40d407140d1030581c1e542c00000d103020f900b402d042000e00015001e0710350822008101310903d00b0024042114009145070045071928204100041981d40003070045000710b1075502086800d40c0750040072011100715042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 590853588 1250 590852338 590852377
    0x1b0103020a0513140411070b0406180b270d0237050d02150c0a080907120305091f02060408030402210309100f0c03120e0f060a0608030f 60
    0x105850394081c91042120f00401014005000411000011a12001110200b100c0c07410785900c8101030040c4070024103610941390000d00010025481060500f0b029071801d1500e958a036181c10b0030380b000300d80c2e10340050028220104e051103010300c1840003481c60b0026001c01012080002d585611715051081c2c14201481c00f80d0ba160000606480340c901d500d48025050803e60501565440005034004014400c1c42603c4021a00c1c00401900519044800c540303848030326042211119801340c5042c0081c000c6400c0010000700060041a0301480f0391519a203800786074003004284001742003441100c00c18039802da01c600e50701080f81070f440b5600014454694464dc00410648070b0544408178003084560002141e00710000090711042c0c03803c8501c80c40b040a9064204c41c90712055403030401042901d0715003000240110b14084050800c101e00050355510560014071b40104241451010740103501800b41450850045401601e1a10015803904880705000c28540c0701c1c5003085d940700c16100b40c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 590854838 1250 590853588 590853607
    0x1021801030b0f0132070b0708100b0c280614070c120e040f0f0f060f15021005040606031403130603020f0d0903030b0f030109080a030903050c2d1b010302 68
    0x806150501174400301d180c2001e960001e507403031a0342c8060420f8400c0c41c4088005071040e8401c0150a100300d10348039001d407540f8980010704890790442c42030180580182c50002c0010210903142c1c841050000008502c81801e40c00e042d022507c83c4481070014820580c2003003021a00030240904080e8014400900320350700d00c2c0204c403024200e030181c6500501301602d0004602d0503030842071150b20092030401079840c00002d400101c5a26200383c800602d8455010000d0281c407120130542080705006455292036050410301c104c1d80700701c4003115041c0d42c5800901c280004040307085417150030040114a0280c0782c8500c25681c04284c8500e40c2007540024100b600c040009058542c046045d000a01900030103203005000381c40702030203290241000100200a5280c14001c211805410118080c640181700b0004c4010740740c9150242e0500030100080708580c001000514000c04800d04880411041d899020360000706e82031f05030a941d800744141f440ca07240032541c06810881d0034240180d480c0281e8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 590856088 1250 590854838 590854877
    0xf07050a080409020706060e07120b060d051906060807020303130f0506091005060631050901030b04110402040608070c03120f021b07030f0f060605040e01021801030b0f01 75
    0x203410041c09103a01250010740c2a40603009042c0091150005102c0075480da14122141c0c00308407442ca00050342c01400c50001c1d015548960080140603040030b00d0540c14412600030380b00140d0342c04c20025030b18040380d001000d0903c03505015012a1525005600309040001e58901007d0140f40c8024220300c0900300b0041c8244602d286681d000040c1ca2851500c2c01c070b100d032078031812070b144221b40d03042c940051980c0c03074858115004c2914843c4040038094010001c2a030343e10f0501c1d010f80c44450340345008103d950303600c100f940c002e61017408034007039a180501d428009191801134040c003660052200f031048581165196501c11404d10b42548100c80c242021030b150300060003141650352800800e088400740c0368000784014485190300c580300c000c409060540d11800d40c030015040341a14410390b80090014003100c8031650080b00c003c1f440c81d8440703002404682642120a2080e94000341c4245002d501360364034014000700b420100003420301c02cae0100d0504a00c09648074100040c7c41514a5500380c030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 590857338 1250 590856088 590856103
    0x60f1b0c1009060b01030501050109060504140a21030e0415060305040219060e0901050d110616080301140f1008070e03100606051c060609090e19060506041406060f0705 74
    0x40720902c0700d00494280600101441500c0c03d00007410710b0008216540140d003a001111185d5031100d01d0705142c00f03862100d080d002030703807194885100500001c1c1c1020810702c2ea030104514180a6031329504925018010007503601c10701e0302560805d1482002d0802c0601c41c10101e0b4840c0c18007040b190380b20720003e5060546122901c07448150400049011648143e40301441034040d00c1d0015141d032a0001c10484c0302c0b00d80c200610807070480001d07000b0f81c100700025103000010300300000300d60306507581c82c401e0340d070000d07040116848501c00c02c41050740742070003074103280c0401560000f40e04440d1010082c0040c900a00007014014a490421450f4800308485020205e4014081042036242e80005000d030b8007203e00448204001d1107a024042c03021b00c02c903800c492040d1580703001e282c41d00288201501c034419183d00c00d400344000c2010380c889202d1183c41264815100010b803454000101700449018500f44c80e180402142049002e403100000c4500b16001285a182c850510346499480c2002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 590858588 1250 590857338 590857363
    0x501020c041e0e07050301110c031b161404050c0909010e31030e01020f0d0f0c080a030b01110307020a05060c01060503030c0a061a0f01080403050d020f0705060f1b0c 73
    0x1400182080142d40444d4036802da41e0200d009014030505e0240d82d00c500c0c040c0818540c0103400402801907094010101004010014021b81307880340070208040c0d8004100ea4041c0007100082a03180b1080d01e42407064540c00040c0605950a000803040411540d9a050107080e443c1e4450380049640c203820b0980d4002160a00c16040a1000c0744030348008009050020440106450224001d10341d8000300d5002074103541040204140880440102d403d140040940c0c814001c8020344403000c20b00e800000c0030303408541d84000c0345140c1107400040c614014100c00400d542c006004403801a03079034840300b0703080f504200ca80a450340c00780782d851130060055074021a41403000291104040c0000300e4000c0419020f203404000384215100005980c40d00400f002e039100b4017880501c0c5440d802107a40b01d410600030310b0650304041200e000f00c0100d0344008420025183c01068400c10058100040b070380c4144071103c200c110742009045860f8040e0340780c001d907104000100d800c00c65a082008044d0107610b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 590859838 1250 590858588 590858591
    0xd08070e040c020114010902030115081b030108010912050c2505091303030e030418020d090501060b12010803090607170702041505040c030b060307050c0f030a030c12060501020c041e 80
    0xa05140180c001d02881d0202d80035191070702c0000900101f94420399049410001074203488010200c021100054001c2111a074402003100120003031407903802039400b82420000000e106142d60a01000100300703c4050307810407208012140003443c3c040f0364001a075882001e07146031802d110032050301e00c0289801c03036a00030200c1c0007007000079203140d81c800a405000351410012803110360005034036407041d40155000c1c60601c581c04d501404103075000b4509031415041c0000c16030704030340e034150a685a40e0300c44544504007007100b9481c241e0fa03104090050401c000118940381030400852081c0c080c141c0f020300b000c84900041740c00110380b642290714656000300104143e10f8001c00344c80c1c4039100c0b0301907940103502e07003415107040034020702c180b111040e03004104604660ba0880100c0702c56200c503611b88040e0040000c580e400c040b08002402c1008141d2f140030891440c103600c0100030140f21459441c001d418404100a40c0c0d1f00030070580d07140d8009490125214a0103039061820074030080f1040394a5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 590861088 1250 590859838 590859851
    0xa050d03050709140d03140c0709020901111507050903070e010909030e030303040b0a051f0b1803070b03191d0a12090b0405040504030903050303070c02030d110d08070e04 75
    0x8591503030019210300c2c829100d040c42591158110855030380200100754110200c4180b60001c203015656001d03180c00d440c480f152820001c1a45a400c4c02217a52203c01c2c00760b00401c00407025030300180381407084084c0d40c000f095039480078019103c3c03000002d084c642c140b201c00982d03040d868405018200142442c00c04541d4a235940769101c00c01800340310303020342c001174100c40303130302c02c0d0380f0b404401c4900848d00429054403503129120810020702c0041d151110074003c01040044c2c2d45140309010004103d07116920762a10000c1308020601d82c075408255101c0d4000d42c0e018440741d00502e09036a000b04000740a81c490074849101c7c4001030102d80d21030401040b4039110440d601c1000100314010070b100d14030b0824103200408080c0c4e214211401401e40c0800140014482400c0c42d50115030f01c140030380b4101d00b805540342c07189400d60f40700307540e5140001c00f400002000e41c2820411040791494501d03021405408000d05a0380b22420020417004100d100d1000c600050306c00e00c20849400c50041080014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 590862338 1250 590861088 590861113
    0x14040e031c2c070e0708071202091302040509010b0301030f0b04020109030209011401090b030c042d0f030c0501020a0b04020f01030b03030a260114090403021002120603010b030a05100e0a05 83
    0x107150000701c107074881c42964000f141950b219403007180244c1780c0c0c1d100c8111948a450f07007990b418610894001805e40e081c131403040165030714207455680c12200040107030380d076007450240244508160400d2a03d0481007004200181000040b03680c0d1940100d6404102d490b03900c0101c0d60070040760b0020750301c400c480d800422414240d098030380010000740c0f603001446070358601d80e010038007007254115803074003050004000040c1e4500b448810b00e0140304140c42c8c4c10300b402e2046007d040d065000620a40008603040c000c00000c40c90303401c00f52000340014a005459592801e10001d00280002d001e002400083c88060b4040d4001d0440b154004056070340710340002000900410004034201494203134100c0420441324600c1c44981030f01d203410f030012075040308402404400000a08201e0441c4548603c00491900920140980010910032034032582020010103081d81c1c0c0c040c14562094100101c3c05002640c0040d0700d2480d50590200071400b05464003c0d00c0c2490030340240a000303400b070030001c07056 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 590863588 1250 590862338 590862401
    0x32607120b120c15040e01090b030f0105010b03071b12110d0c05120a110307210e2d1804031b03170604020d0e060114040e031c 56
    0x40280c0c10344410050714085400b00400b0181c201c0103000325801544042e122810322000c0207030b483c140a8000d40c179003991060f281d2070118090307000341c0c4e200b545d0b0b140a400a1030309000320480e6408110091000d275041c4002c42c0c0035444042c1c40e401c01c1c00240c540e81c440e00b004a820400950740c012020f00c858030030840015091464641a0300d144d401a4070203015814002d24150707001300e0b000002000e05040311030490380d81d035010864410130f201c0c1801007401c00e10b0302000140702d001c1c0b007903010043c009400460528032403041d0651800b0b200e818502001c4d6a100c8036002c4000b001e2515440c0e628648054144220b001542e01c410b8000c52a690600101a4402421400b487c400d955002c9500002441401c00007004d8070010002501519001e40fa9290314110390f81203180204014036055002c000081160911020a42c454001c1c10040020040b0f890480000ca0810389003800881c00c48540185caa1080c0540c4009040310305160510344084c59015501c03501c001101e2014441c01400b0414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 590864838 1250 590863588 590863607
    0x20c06060109050a080c060d0b09070e090114011b0224031504060b120718150806041e020309010f02030c07050708010b0603040201030506010c1704140d030c032607 72
    0x41c00702e07881000008490510310001012101120058149031902d20b04001d0568408400b20040940f02c92400c41d150399084403090151081c0e480d82c1c2c50f03080c00744040c0240007005a01034801400c90903505c980e41d0340c100c0352078400c50400060004010010b0b00c00a125010f260940f01d00d13072030340c0c013580400341842c5000030750181d03000790350700c2c10000000d07030401041d2400750040d5511448140100c840c0710030290602a0024450704000d01c10300d2100010075a60711040e80001d0300c02001a010804180d0015a5641c111106484c14003c660004522001c0929402c0326928500c2d40000080e00899081d0312402410081490540d528100b404039001c0d1500b000c6010b5900b07000301200040d203038105200d8104a03050103842e440c15a65180c00540041c480248601e05101c01d050295001440740740b19014038140705c04145403a0b40c102480168009c03440d028450207001003007843c0d40840e8101a218034141d0345840d0901404e01394480043c02d035070380c5d840c201306004194414421840c1c1c00c00b0f000d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 590866088 1250 590864838 590864851
    0xf0102030a020429070305131814090c01020712060b09040f0c0617160302070f030323010503071e03050f010522170a050c071d06010f090621020c06 65
    0x1400c4034840c00c01c0d01c0701402c4d60014422000e4000708200d20000740508080e06a110b0082e103103d2545075900c1040da500f200011045019a035201c020f061601c50351500280c01c04803070001050701c052514000f0f50740b841d19004610b1454024075601c1c04103c000d41207a80c09007406050080c03c1d081c83d262841c0004d040103c201e541c4a40d0141c0422118440c0a07501c5440d010600c0c0c414032519000080c0c030608001c02c40344002c2580800843c000700e0404141896901c0c4030341d078000b50090001c0c0a104400101407208034004074104010002581c0000350300e4180c03240c1240b460480c03a81c0740342c14038800405a000070020b002d2400b401d1200c0300c065100710f2080307140e242482038803a80000d54201d55801010000d000c1014a41500c00e0300c00b8810203071100c4d00b041d0034544c0c6800da0003201c40f45440d6003030b4405960103402d0407005184054913403403541c1214081c20b0007102140d1b940c0d4040c015803401d024903070802440104072080c0004140103c010340c034020704210360320031003602c800f40c656100b150345 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 590867338 1250 590866088 590866109
    0x2d01030308090d050702130204030501020310080d0c030c020609010c050609011b0509010c030c020a090207050c040f0506031b1302040e2a0d15031406090f0309100c050f0102030a0204 80
    0xb540070b8002091550882203641da401d17140c84102e508100c28032514040ba0029103509100200000f00244011401004c482525510f461314100c81149060521008441001070707079890000001c0d004210501c00c640d040b10800e460b440440c004860800200c400034001e44111000d000c2c03588010b40c050205014085803061a0380c0a0400030b4a5612a48808a00080c2c1284041020038403c40254034018401030400f2860350f030740c0f52004141c3e00034100c1640e003508034101d0110640740034403c181480c060b0352414040e070300d8880d0001c0c3e107034402488104414201c210180d042591240344080c6e81c00800707841152129182c4c00c0f268240c580031100c030500501c0080500d06152641031240100e0090041002d20307080f020314030540680014820f043e020041402d0100c00950801d00d01381e070001d5004020845481d00446851900c1c04440e21011a034104000080e4280c86007426143d080c42541444030040302c030b42c58002c0c0307044900084181c4a5101005010000c0043d40050040700d042045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 590868588 1250 590867338 590867341
    0x1005130f03240b060f090f09070c140a050307030f020f06161b0501020c030a0917030f070317070305011401051215061204050102030f01090c0c0b2d01030308 69
    0xca000c404456804007400202c95880907410200609240c26091500da900c04621000500046055a002604404410903020903841150f040041c06103417103000071100b0742064204210302030325406088001405142452a165880320410490b14071601da02034101e80d076a0000e410011700c15044940c540c0014010080200200759002a11030300940d02c080400032240400700055900c119140c0c0703420052141c2c103e00038003082c420b10140c41e21007000c01c055983c42c000503400403c200c1154100314001e039011034100d40c035540000150742c1600700c9096010703910f0310542029248495010640c6101001d40010016030a5140e041141285e82506003400c04010020045d5024000c980c40c5012840004c0300003203041032085042d95100e00c000d4a15407900180d58043c0280000855040c1c80302d179000070a0000b00b2450b0300041d40100030410342000501d070146402084000c0015010340002c01030300101e000c000000d8074400440b41d101100300741c6911004030b00c40004070244000d0b00481c42d041d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 590869838 1250 590868588 590868599
    0xa020f030a1d0d0b07110f070e0a0605060c070b09040f02030a09030201050a02121f1a0306091015120f09030309051b091308271201110406030203040f02100513 70
    0x1000001d8955000400d11380595a80c00c086070029481c01c00300c0440d1041194004007880f090041a014040440c1c41d1645854a00842e6082d1180c40d44142d0061b5410082c0000021000c2000001d50b80c0180905955008100000e000350000b10b1012444520000034404440c01c1c903401180c41c18440d400a1180f5540c03024030b0406c900686489003801c2c9002c07000558090054003059007602c0c1d80c542d4500807551030786041001055126000e2291140c0042030016034074100046550041c040c1000308100b50400d030203030003103111a030704500c244400e00c0079100c80e9141d9900309103155481c3d202c00300407698035810010003502c03891405840c41c0c0100c008035092801c00e0b2201091149010b01115895111040501003d000c40401501c580c0000c1c0030106c100d19221017034045020b11034251540c01c041a0003000088030000b2070040980e032400d81c1c800f0081003404103442c1101d0309802c00585960f503e003030944001d00351000c025403190004034560303401900000601001c9141048141d56030380c40380c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 590871088 1250 590869838 590869849
    0x10b0a02070b131a071202070f081603060c030b03010e07090f05010b03070f020a0f120f02070f0b1309020a03020a080f1003060902040b0d0b061302040e0703020a020f030a1d 76
    0x2211110030342c0341ca444080c09901e9030310360301d42c03003900070b0000881c9040c0080e150118454946c4814000603005948100240803840e41400e01404124024024030b80703401800a04540280c480108400d80b10a90040c07403074000c0d1321a01290f103004d0001d000c0300070356640c6282c0700d0500f80a0103006510741a00071480782064030504c0d0690700c101c452945903031541042900c611040721030030001c621034015000c002401d00071803c081c0d5481102e04502c0c0b03494901c4050544650074900c40c0444d40021400c002643d60094000e0854041a008941e54102c034109613061103281d401050f00c5500000e40b0110f0359501d0345c024902350b11707181d0301d0404588480244808030003099490112a04440f002800403036191303440030160030b100800024955920700c011600311121a08141c8a0003c0607080024500b0302d07100a0f10141e4080e0811840c180c1408514949980c0c050140400c041c0d0104605001d035000300001c542c00340081003207a884a880040042c001c0d40120340701ca060405208040c00300c0c2c2000b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 590872338 1250 590871088 590871097
    0x4302210906040302120304120b0613091208060a05041517071206050a27030219031e03060f0905100b0a051e04170604020915061c060b03010b0a02070b 66
    0x10120741c9010300d582c08000752102800c5d030f601c5807808104400103a640306590100900351251900340c101d40742402c01c00a4410104405031446803c0040c00000200300107424400e0494a0030032842030b03120503001ca540c40c45e4030381115410a141c03412840701d01503502412011140582400c4041c60b18040041d91200b2207071240c4e0788100312103000c2170000345498025680c05500100005252418001012440440c1c00e02d40f100c5c90f0391901c1200249541404000b119030564000700c1d41140c0e141e038008080280c0b04150407001c481280400109070b00c03036041400103191a018018190b038680e84910000d0100b80d170100d1f64031030030640002e0a0301e0fa00b01a900900c8003600e0703150500680d088034030003454041d51907082c4a50100f0021407044d0114456010784030828008200a1601c0e105122a003c03028201640603140f6101e0711242c1d54070340084402c07400302440a80300540d411060b000c0504070b039402c01c10317020b04040001316650703184c81c0140c101040d650b0300326042656102c401001a120303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 590873588 1250 590872338 590872357
    0x2b06020702151c020a120903050d0606030501140405091510141806220516031a100c052d1e030414030f0111071208430221 54
    0x30119070314180f40c05250f002d4a6211528200202030080c006061000c6034000740d8220702146d00401c032102880c446104900c0500094203082240b075040800194581d1381c200201e500c50754580707000814180c0244010700b8080745140c407255503410002c00700e4100403c607006070703030611044100409041c0781c1180030461040500c1454952a114081400340304150381003440c800010140d0316040d1304c0110b01c295441141c01000b1032519984402d40101a82c222903c8800400132605241205607200500010040030b00d0810f00485619840c0403810220701d010030214030f42d584070347c985900b000230100401c2d500c09003040d5000020380c01c00c0c03031040c0d51541000700ca8642c4280414040802c85620389038001030018111129100c84803c1c80e070030741d403400c10074520540010481e5001c1000b0501c61116101060a1211103840c0c142c1e43c040004e492900030740d090103004c0148140e207601003c0302d50280a1801d580800e034886c040340203982c44250000d800144031318031009207603e000507002d980c030024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 590874838 1250 590873588 590873617
    0x31214010509130f031e03060b030c09010c0609030915020a0b0402060903071703040f0e07170406090f0311100b012f0601030f030201110304112b0602070215 69
    0x2420311042c015580e10092841090b80c2010401101041c41aa03240c08018841c0e50350070124589980c4035900b000e0845040342c203150920a00f8450441c01200b0389a1060f40c40e030a064031a0240c50048800020300786025089901d040c50407014181e000440da41943c0b561141d800c50700004010490b5170740b07011200540b14046003c0420010316104e4020321200100500b141d0b6401e4503415030326511462540d40c01c456600002e400c2204000705075021004040d40c5c41030440600d024440a03020790709039685a4501003503000046c00304162540601c140395040740307010f1100714a80c98050034612011242160070b100b6420144002c8109000d280c94a0106a6400c89101070300c001c1c101083c561881c10409540c40480ca030300c44c8a80401005009501034800412910010704010f400c44500c007410449000040040001068003ca41e04541d01c0c0c00b9120f0030701c00c58412070040a0682103410905142d094080da4000b0301c122038003c2c08a850080354501d40d40c0a40e00408040b07849925a140d0100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 590876088 1250 590874838 590874841
    0x60203121b030f0402150c0601170d05030c0c0a0b010b090f09010b04030f1a04030537120e010c0903050f0105130f0f080d0914060405120702010c1a04031214 69
    0x420b0815203d6400510240c94481d0044c5040f040c1c1d469500040e010366a40d81c460401080b03195081e100100202c031060002d04502018030400810320f1000410440c04202e00003a42071201c3c0c41004018100c83e04450127a0643d42c47e8002402554407500c1901c0c8240c42611111040d4030b0704009050485060740801494140340d9500ca81550580340025031300c1155002071036407416031046205104922a59a20341c1d950030f59500d4206500480b03030a007143d6008840c1c0f41464603586038105510009505090840001408442c1e024000f41c07039000c0c81650030201d00a200f10341140007082524425429600c1c0020180070039801c90710100c50300704c51744200d0300788000416424407180c000755000b0742e14800700d007107075840b0262103900c06035080104079030301c1d044801030102c007010b220812041c840c090a12802c4c0394640e01d55603440c0244074915210300107401d10841e8015040c09240b0fa52015406c8048081006034588a4504840680c0494140b440c03441841183e4840c0b032040c2d16401c070269046 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 590877338 1250 590876088 590876101
    0x6040515090a0c050c0307050d020d050403050607050d1b0f030b0105030606091c060212160e030c1e04060b04060941030102070605040c05030a0515130c060203121b03 73
    0x303046440b0b64070013401010043e00e041200c09000500d4014017400013042621500350b0f00a02e4101d9503410b00080040510041c000981c011841079005011071810304d03100c1081c00d203044000e0440090b042030760380106248403c155000546080d01c1c03259500d00304011a0740e240159418401241e070313264441c101f0800d0314003601d040314003012120003d29066410704403030b5543e1402ca034000d003004010a24030408125400340810800c0c050b5599914001007400c2c2c0344008070380d03240c8140d00300500c00da010b0f49200300d42c3e00c4c0051401207055401041402119552200c500e410390040c00341100003442020081045511810b60205200c02d00118030400316880307180c074075910516021102b1400d020080101d10f5a02400a00a0207004120005050070a4901140c07031641d95407004d4000d811200080d0086900450301c50701408a0341c08406582e030781c491a0307425a00310984001d0195408180c0400c4180c1d0000c040d2000c40348001d00004e181e2104c0c0c2c00205a01031052411269200070000100f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 590878588 1250 590877338 590877341
    0x3122a050403030212031f060932150931140106051c050c0910020606150304050a08040803040906050603040c05010f0207170c0915030c0108100305030d0506040515090a 74
    0x5220407076a0a9104802220ba131047c1d0925041c0d100038001034101c1018803d03410000c088948a92050503091040300c031542e4080d00440903001400d1003480b4001c0b507005900e0140c01200c110140040c400d03940104110320094035a804606404d40030034803e004d41c400011280b0030001481184c0940c9035543c2e2901d1000c51b00c80e40081ca450f03004100484500b0540480ca0144170702400b4074805c584d44074504001403010084400380300c03008561040040c4181c0b43c0740d13401030144003000040c105549550f00c1c24060302e4203444100091559800140c001618000030001d4410b503408040306000031aa594200002408151405810b41c195207000708048c0d0b004100d500f07441a07490040e0303842c9a9450214224081401c210310f2120b0b04080c031a803589281c0000c400380c0c0101d004070701e0f1090b10340c00c401081c6d549000350b01041c1030195910114091000c0342100c900290303445402c580d9a9040b46600c400500800d490392401107003400041103a41c40410b0b0131745205503000e400351135207a032094441d40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 590879838 1250 590878588 590878591
    0x2060307050f161407151202040b041403071406121f1502100612080c190606170f10021c0e070602150f0402040903122a05040303021203 60
    0x101802000c0110003090300e80d5101510011210404a00800d4100d0404007100325203011900703099001742e04140310211510380c40a8120802e480c0c104000030099480000910940e00141002000490000b8a0100c0520f0f800d01c0d08000f64285c50009664064a504120b04100e1581d440342c000c2c07024048112194074181d82c070a01c4200364000b980020702d5070101c10b0184e80c0000d00c80b101c0c4045c421340d07080e4042014642040442c032080260b103192114103c94005c00c0b5900074500080011040c0628030200000e0b588101001c800003545a90361505100604403481031084400d03451041c41d08559010528440c10701d051400f81c0542c210446004000703612031400c001445d114040054803000e4144589800c2c07400c4d000060090504080d00030746420406224080420401d008000003100343e240d8994002c1c1e819140442c0211052030150b4810700420759043d2440d00d41900c401c00e032441c0c402c0f50031148025000c45004503808000481300342c4964003014016030701c0400c004902c8041d040046 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 590881088 1250 590879838 590879851
    0x9051e12070f05010f03061706040605010b0406120f0608060c0c0d14030f100b040f03050c0f1f021912120509071e0503120c07050d11011803060e010f050901090f020603 74
    0x240503884c1c10a203056029044c0003c2302c0c0e0fa0200f01040200721291040710b0142070302c1522a41444c0c5003c0008009503294200b840c212034840c1e0903000200041c1d0403000c0034160140c2034403824130701b0201d0311115420030b46440507d841040da0b1122010f0180070b072280803901c800034840c42d580d907091003010303480c0028100c0b842244410900195500e170300e80241003d040802c000d00303801880e5040c8146410300624070039210b640042c00040003540d40750f00d1504401440442904044a022420b13800c0251aa0400003900c60b802c10340790800503a0301c1100d45000090300c2e9070311a103075401609001ca640440310b114141e8000d113800e01c800013100d02d4001c1c840c01e031500c0d11305240b030716007021130704005201d0184140b94a0204140e120004244445000f80800ba102000c41d0034641d20f603042c0451101d403025041c000b8846030b0104d00342c00f01c00920045c5400480600040c00e980f55254000e12002585d40b05031403a103008908a400180201c0300025009281d0807209007251f020042c40b0b0340041c005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 590882338 1250 590881088 590881091
    0x4030206040e090f0f03091f17040804180219030504081b0c0411070309081504060c0201020c1b27040303020a0507060606031b03020c0d0f09051e12070f05010f03 71
    0x3840d080002017052040d80c00741600590388807000041440364105080c45424110210300150b4148150700c0315500081188002a010b210740380c9050040851080b50441d02104501c2402c0710000110340d0010700400e008541310040c400440e1504a00315070065400605a00080120b00c980c09c038060b10101c1e5007420f10301510320620684000408071103000007558400c0c800410b5000c01d15810020349402010181d0207130500041800c01e07015007001c014401400e00340e1b1500200303023280c402d60503a00071590340030071038100a0900009031020005138110170300c100360b01800450400490400c990010f00d422042c1d541c0c03a211542c0070b4001e900410201020403100f0701c0b82401088a03030140038001c0860f40c0f030000354209507203080c14100b5070008011042c107004001c596801040025003480340303101f9182048810100c0802114200010b600c101d51020009580c00f0148112405d00c42e680402114881c8820700611000d58544043d8850301c0518080700104000b954014070018014031082d190 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 590883588 1250 590882338 590882353
    0x2060f06011214040b01030c0b030108030f1b0a150e030f04030602090d0b04060603110f010503271f0e010b0307031101030b040e06070216050a0b0f0c060c0c070b04030206040e09 78
    0x11080d9000d07404c84040d0740d4000711100410501c20700c0c4884902604a01049a20715810082c01964070700c6014040d1281d0708000840c240e68211202d00c00420003030300b4041d034140b840c0b00d0070078101061640748403800c01407600d840c0351040400081242e8854588499040c20140f440d21518000d4000d140d8240e00310450400130b000242e040803401d40700b02d100d160006001d9095080c04501c2c1c0504a6015001c0d418a51540c000c0d0380e0001c0940740e020902c41640707410b002e1600340611155210500c500301c1c0d031050703107610040c0c0540311180c2c040541c122070341004840c11181c92039082c0c581a0b1401c81d05500a1041803012440c1e64403002100304060402084140d13000011908880c101d241d258055001001072101440d0706015024000781e003a0014000981828000f074003a202903c40e0714034034000000e950341200802d9068038400c040c05425580f0504d03012002c180c555120320302c0a211f90043d400f0204541c620802175405903034014008a090600301030307c00c241060007a0075050780b44161032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 590884838 1250 590883588 590883611
    0x50d0807060f0e1509010606050313021201020a030e33130219180e0309061809070206040201020d02070315050a0902040510050a050a0e1506040f0b030403090602060f060112 76
    0x42042c01e040e040001c00340b00c035062054565205015140f4045c99050460400500358440c003600e8105502c4186044941500d01c0007600e1880100b120341c1c00e80d400441c02da5070007501135000c1e004031240d050980e503044206120149004041140b0300001602c900c2e44c18106c188015412640309102c1c0c076406c0c001e07254680000d050002845513010f00403140319001d01082d01d41d001940b1005041c54020b007c6183c0c60b5003925140d004078904140101004a003010100300151080701101c4c00207000c0281c14100b60300000c0d1202403c4030305902512a82003492036551001900f10116500010074515040c0c51100040c080d0901800100c0d6558403101c45502607602d174882c2c0d60088440c403901d02c0340716103000d090008502142e40311510403620004104200d080c0701c00b0080e07020218040301a0291a114001071a500440d000032141080d40c0c08041040000d03180210f000d64082d455140741e943d5580703422030b680e04080300e10100003039500c0081805035020f555103144201070300d54003051100610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 590886088 1250 590884838 590884841
    0x207020d170301140603061815130906050f04030c02040b01050c010c1d0d0201051806070b01080a15061215111201031b080d0c051c030f0f06050d0807060f 68
    0x10310601040a00020041204e84041c080c501c1c0034403c02e450050171403410b4000140c04048814440b800074450000007040400c03510316134002c1c00c40040081c0403003540c2014400080100e030341c088540320f20344030115400f681032031000d83c404c03a41a81c0d820289081c41e400e21003e4110324481380d050020a21060544140038064a4907011b103640e24540da401c9515409000c00078010345d6030b03002d650340711801c00150b41d000c01103800740c08001c901250303100a94008212580f059000191101401d8130011900e1000820b0710035a46000741403180380c0b24040118102210721902c9244001081d4407152000240b00642d04200c1790002c0d000042d80500c4141410a5036202004aa00d100d0403000103004201c014034031440b00d088544425603209003007221082e6240c3c03445404000307100d10f045a00e01000002c2100b07804c1440c400442e600881c81100d005800f6002900320005d40c18102802b600c00902d080c81400100c5100421a00c0b90326090740381d440e040d40c0585800d40c1c85503214207072640d0541e0b0705d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 590887338 1250 590886088 590886113
    0x9090e0604030825080c0408150406141003031209080a0e030f0102040e0c0c011107150b041b0c0309030c0e0118020c07090f1803080108010b0d12030207020d 69
    0x14900504003a00e000d15000309081001011074040c11548500360710780c0704000c0440e40e0a10340f103003004450350726a8a103600c07442c006d035403191840340318041e070314101040301351036907805548210414040c0c1c40e807120402c00b0f120011500c81018136501038040020030300c25401c04c04104801c13180001c1c0b00105403500c00e055805000620045004502918002e0404001d144412904440214202400c040c0f03410000a03000c0d08240140a01150744e0303500c80303000c1d4428901c42c1c3c0023a02050b6207822924110725144420504090014078100070b400003802d060040085c09404142040c54aa529180644100850f241d00707604203c030302c000c0400090008c511b007001402001d18215102c1d8034100d900300c1643d16204403115150b0040c801f0044101e40020150250749035171102107110800c82200c480113010007042c0004280141c003003d4149604404c0042c16901420000d010385056601884a220a9060014032464403503881c000113030310030780c041c200c00b43c40101008450902a240c04036010705 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 590888588 1250 590887338 590887361
    0x406090209030c04020304021c03140705010c0915081914011701050c0c060c0f0d1d16030809062503080a050601030606081807051207090507020703020d120909 70
    0xa0001c0e5811452a0030450150480302c01c480c01e61075481c20341d01140d100002c10544000b02014862801708040c0a003040b400d042c404500c0c0d59440c3c801070709000703000c0c2c03080d9480701003c11099003001c5550b804820841213031881035103403895191036107884010f100c0102c124452115545185004810851511040c001c010b410398021180a0300101d01f404c58034090200e0700c841204002414403000003103146076005541b4201070751680f480c0342c0301040910030000304c14240d80c45c00d582e8903001420402c407400355640d180b007222441d40d0702682c0340010100d5404043c2040d60144407900081c50144010304245c200c0050b80300c003030600712119202401c6000c0044002c0303003140b000c004403c100c520516610840c03d20f0180120383c9421405410102e0142c1224a42441002c030241c04840401c441002400b0103082100c0926110380000d0310351b212402004150b80c24480030841113440020020183ca400804030110003803e9079132540985101c000c10010310401d61400507030701c0781c18800d40030540ba = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 590889838 1250 590888588 590888591
    0x9090305090306011220041b031508121204080408010c020d11060c090904030e09150111030a02070b0c070504050a0f0b010c08030c0a0207120602070312060506091c02040609 76
    0x8942420181007680c140c00690746110800c02c0607000c54022102d04440c441b150101c20308150501300424040c1189003400c0001c42061150100da0a900d036001b20030f000a200c0312801712075110008a9101c500768244440492010300c0760200c0c0f20b03042d0011541207441001501c0c6060754440c071090035134121143d103c01682189610411450704940100c46500420300a0007507440d000d51030180038003642e18500e0003118504005020540201d0ba00240c00700000e150284603c0c0259120b00d03901540620f15000920710602d9200752080003003602d03030044245d005815558245242010503402600c0018080d12030070f800042d150711030f03118190040881076408520514503114000564080011480c10001c141c0c0350140491501c00540e6000000b0a4400c2d07038840d070f07181d0100d1601c503854001c1d00303001c5101e929034020844030341c0c000c0500e00d00c40d80750740207869103c0c0c038080d0485089120741904410304002e8a030309443c0a0ba4500202420304d000407914110360b0300450200ca9041d0813020a06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 590891088 1250 590889838 590889847
    0x90d0506010f080a080a03020a030906140a0e03190c0302071e091d10021e04180507020724052a010501080a020a15051c091205040b1207020709090305 66
    0x1c20004501c0070f40000b80c014201c8103d01d5450000500c00d220b001410150301150700c0080f80c0c4243c01c100c00003078100100b072041c24514400301d51a0031041e60071490841ca4003041580341040401501e180304403101da004c0c6050003000080c1d60039004540f0032821401920008107030040500815000300c40000102a25181030030380b000308a0f40910200202c40c1055003031031000c448001b810f00780482c41ca89000d81c40e8030307021900055521004e8400381c40030304086008102d8542c6030f44900c0c02500e43c0042400301c0d0711884816600c2d03145a000d0942c024855001c808420546512034460040385880d1040c9880140c0b582c8914040d44000b041d401c18a81000c05191070401740169409407a42101415000c44d8a0780010b0304c2390400e2280401d4010062000154180100b06640455080c0508200300803c0c0c42c01c40785c002c001420080750036508041d5000d1115102d401a5801d40350260100c616203840c0800d071100d80301c001803c0008522442d140401e10852070b009041c0d0303da100380c44440d20b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 590892338 1250 590891088 590891099
    0x170708010513052a0c07030821010e010e0603070302090c030604050708010501020a111813120206040317061f03060f0911040b0f131d090109200105090d050601 70
    0x804142c0e0703181010500b44002d00c00ea80740346040c0d51030210f40000b41400e1080c1d600c0181911402828054011401151000018401d00400900d1220306560000c034071580c039078000c0e01000ca03007030196031501927a600041c031000c101da10010741c2106005007241da00030350f01d0707000401c480c03012200c90310086804802d01001d410b150185c0f0307400103040c0c01c04085035814500001c0d030311070042c0006054415480c1d44221252107452010340c003204444a0b4246511303103036181d0580c0c441640d101300c41803040d05a18191091012030000d014640c103659600a000c26000c0007041114050500340e8480354805081010748455921070350041d806840104600749000001e82514603580d0141e05614200400010700c01125822102900d0880f050383c0d03103c6011548400c124011111003144420000001154590301d090394500c2e000301001445c1d2066840c074203464283c8010b1f003030040c06070054091302e041009050125041920044c0360407400c003140800081d003650a000c034141c982d4bc10001c018040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 590893588 1250 590892338 590892349
    0x4080105070c051b0402130b03060a0815040305030423010c1b08030105010507051f1505040c080a02090d0501091406071112090409081305040605010903020d02040b011707080105 78
    0xa001200342414a1400b0441d00d9480c3c407014020003001481550744140360080e525503040e104482011121043d07001d031903900c01400c65205407a41c1c0d1103643e036a000042d0705040011000b1081c20100f103440360b00e0b20740360b60542e02e42c0c0000d04201c0e02e5011a140912078401001d800d94220b186810000c129500c00d00d00c0507110503090a40d55941c058418003174030200d030503841141d04403a028038082d90340300d19a003030883c140510601944440c90915509070342c81c00c0c00d5088495034101100e4014481941c03641000100c44000c0d02d50804a64100000703140d0415a030b010306500b000107071040350481465542c182c00c5a6003c1422110744d03425100d16003034207004101055006004d400c140d0100202400c000d07544200803000500150340000348ca006d07540b00c60b00082c52440e845024640c80c3e0340032403030109402c02c80740280e80c000c52070309000040b90340c800c68051040386c0c1c018148041400f45902840042c0541c0c100a0707043c440b850210f01018104055032034410b034080d070354440300355045c4000c01c00d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 590894838 1250 590893588 590893591
    0xc050d0302060601110c0f09100e04081c050906060d0203010213170f07050303030a09050109020d030f0f020102040f03110a0b1314010201111605070e010603060513020f0a121107060204080105 84
    0xc0d0030380d01081c1e000c0070a440703910f011f03407211074103c0303200b41540d03211442e0a11b484090b81114081c07080b901c05000c20002050301504c010308001e20703c256010340802c040800c580b000c07110307201c4690150700861141e00f0003505002c0d115001a00262030300c411080c44510034030321903000c80010f01900501d1130f003d40d8144958186d40052401400410380350000099890001400181e152595440d422040003800d52045041c42d40c0601f00f4090850282030142604504c1040c00000c205800f076080d07003c600c18030032a4240d40e91114101580c504503120f03404031107a490310f0603400690503c008110b00c02045c018240e82070511320b0b070180c0c0e039050070074148005180e0420103043d681010b01002d420034204065030000c805001c003e03c2ca00407a410113a10f81030b1241d0012501324040c01c000b00e0b1203549a00448155482034600c080064a980f0a4200700c4c850340c0c0200585840502140021900c114800710704000c0d1404042425103a00788204943d62181b034040340c83c00e82c00941000070b00420700940e07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 590896088 1250 590894838 590894867
    0x13501120c1e030312020706050c03040b16020d1206050405010b1e130b0d02070b070e040c050f0a0f0207240f0e090105060327010c0216060203090d0c050d0302060601 73
    0xc2001c214100070031000b0740030042c03d2000d1102a0046070b9501c0e4140c500864002c02c083c4551b00707000c4800f5599500998080e15861084030000b4511141c1d01001c10340c0042c56402048040e8000c00c0880707a5100c10003200d03c00a0700c80c84001110b60316802003901819071107800503941d04c500355603035400440340700600c1d0350300c001801444040755140d144c403000c5540948001d0354494503030a20a0007441862001403549140700300b0701c56116800345203642e42c640180c50030402411801001e41d5180180820614000000c00194071114811415101016410700440e04016107a041130081c1e00319500407821001e407000103c6465075484000e4908841c850f01300b0905201e03108004c1030b07810707005006050080030000040743c2181e048ae4250301c100c04d040703160304100e144801e07102d0717020381422442403005118145160f901941c3e003c52400454076903400462a01c1100800d01094041c00e010030740c3c040c151042c00242e03070380314800050803140c8203902070200c619010340054008036900210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 590897338 1250 590896088 590896109
    0x105031e060a0f020405090f010306050907050f1306080d030203150d0f060e0c120304080f0c062205130f050a0204080a0303180203160e06010e013501120c 68
    0x3040403a40c00070848540080d503900010990082e0049080040d1042c0c3d406035030058800e4041148041d840074006050340e00c140028800e036203400c07a509a8950245c0500d584c00907100c1c01c201480e00e03002c0404924400000c0d0f020860310340e83d036401c900300710502e43c089011030b400104000540781c42c1c1c0c0c03141c0c2800c14202c40003541500d8940783c54803c1403243c24010036440c0e454500140800e030804c10040381600c020724490104004000045e280c2e0054460fa40003440380e00b225000d14400440c3e000181440a0442420418083d031008010404498260a404407175000400c0c0ca4587c561a4103c6030191030011130301800c8014a0411035074000c00b0480781e2481840207001200c0081481240c498052a0204070841524a2618501c182d804002e40c980b03c1d041155158004528460040f111198030701c01c0203640302c00054451002050856000840c41d000a0343c400c030100810108c0d03482580303070342e0181e0b917560441d1803200002a00043c2e0800c042c03110100c200201250b0f080054606e041c007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 590898588 1250 590897338 590897383
    0x2121e0a2106030c090518060c071509031e0309050a0804060f080402010927060e040b0a0501030803040f05030d14011412070501030c1202030406060e060f09041502040e0906010503 79
    0x81348403608406019402c0101d0300c07480410989551402c0050104000500351200c0f030030301c02c003800c0481d03118882c01c84000001c1503040860851520a0741003164054455027940006400d0741c0d0100303026141c3c46001d06646002c480b010800400822031018483d2031880da40c0c504002e0301901843c000080a0304002a4200f00801070760300c601030008a40303403400742c01506082d124207510365160740340c1040c4040c0d01c1c28000203919100300c0002401a80510b40303031440707510b46d00d05101c1070781d00034040640300600030804500000e09220f00b80e118203008400342c13810040000c103041c090341d4070103540d000800340b6000103121200c5040b1b000c1280880c201c0e018800000780710020368030350200e84503403418036036501480d00302c1d1801102e6521240442030011507491504c0c0c1743c694000c2c0380d0740c0138550356102c8000020f00b03242401d40020341d40400c010080140340c1e481c0d64a20a8007040712040384040c5400380b00010311040820100760141e2110b501030b0203103604107018540340c11580030350b4440c00c0702e0120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 590899838 1250 590898588 590898593
    0xc060a060e0a0b1e04240e1303020c0f1309110306090c01020703021504030b04030816050a08041113020a081602070f060c061e0905010606030c02121e0a210603 70
    0xca0324148414150740124040200c000000c0c0140060400ea10410b86092850246d000510000ba815164000400d020700d4450101c010003201000d413008016074424030380304149140c080360300484600001c1a0402404000f109501610025403048400f140b4044151605250502c41682d1206010006156804030280003e55032003080c400a4058102d0040c04003c00c4a0541181c02450f0440441540f80c186840d008014034021903820382c0c2e00c030701743c4e6000c0705c1c6a03c2042181e9040c41c4d195640007607902e48d6120b494090200c940c10b10340c880c50418816a070140d450000d800484100c0d02c50b1040c900d440c4031852030080b61100c012085400c103400601162004142d502e043d520395240940214915250581c000c2c2904c0c034410385d917052001c2c0303e03001a038021380000e80c40900c40c40088c1f0200342d65000c140d040c0c0c1d000700303040000b503000501c43c20b10186440c4050540147e9422a86085900040044c441d82c2d2003950fa80000403000c40c00e0042d902210000301a1007400710310104070551071034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 590901088 1250 590899838 590899849
    0x180c060c01330b07050304031415090a0c0603180606150905090603031606110d0e0f0d0e01030b0102120316140403080706050405240901060f140d05030c060a060e0a0b 73
    0x140108410f041020070201d003404010420307200550303801105c43c0e04402412001a55440824110310030386407003280002c140390000304e0003101c0da0381d210561101003070a02c04140e0180c00703440e990175204c20a850050000c28001c1c0140001014800c0034400c607034075030040081012084d03402a50144051500f880006c0e1800000c581104050681d0800c04022520b048800f40203000e02c48000900d000c00c00c1c203031411455003e00d1940c100542140d22100f0075604c42c0340c4441c100100400403a1075040d00d688994007a80000251020500c107a5038441c0c4558900d81d040c0d001a541100d4080c2144c1d03801100341c5d003140c10004480e40c1c0441850500340b07144e40390842486944002003c40b600c41d8049001c20001700101c1d140d0001d0a14072804000b1010320060b0400e00842c0c0c450741d95801c00310001020750504098205892100b00017008081e80c020512684a01031301084510744810071441c0141c1d40240240e50003401c1c002c9002c22030f589001842119964050810000360b4074042440b0500d542c2c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 590902338 1250 590901088 590901191
    0x20c0705040b130e07051018091802031b0102060105010903150902010c0204051905062b1403040605030106020d030515090417120429180c060c01 64
    0x84601080708030a08010524590054000d040030f2400c10b1410710601c0b202207603080c26100141c03540414044c1940007102c0028040079a1043c4620303074481405031a10640040b0450864990301c0951080c9590110346481c0c0b403005e071314001c0401007914400c99a414400c450042009103010b15180d41103841d500d01503450b0350003030942c4503034620181c13086900404500301d4a80d00107108108030b00d0111406021070051500100540b0310b400700203241072402005124141642c04c2850040b440700b10701000902d17441d00d0040d2549041c417000b40300301c440108000d00103030400c4e0395440c0e203d516045001e80f500140ea079404e0b00b4103040604010b00d012201d5000030400404442d071058546590612a0b00802252812544042c001a80a42003181100281d000302e120300c40b00e0040c20481e0341000c1d010360101307080511144101000c6465914082c200b00c228002d000c0c03d07200e800c51070030001006030748410046181651a1206900d09460111164011b480c81c9046000784084a81151589295 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 590903588 1250 590902338 590902349
    0x906090e070c0204090b0402090c0f1206031606020d1b1a13080a05070b0907210303270218061f020a050d110d05160b09011b050d0c0201020c07 63
    0x10a40c001080940b00b04400c00ca02d68000d4420812001d550034245100e40084500340d02902c8540085040f100d110130403690640f6030103819905241001c06038040140703018003d9945803280082c0780700c060b22b5103210070340205002d400030904001d00303900280860a040640744007640d81441410042a540e0948401c245408006240e0716134807610002c0084248413000b605100c1c0203d048105aa0048001c0085501030881201e1075980e11078500d81e035030070b203000d81d02c107410030110802d1042014188403100c492180c00c02241060201c40d00301910901c80004000581c2c0f21a02d40c400d604180c0c4000d004212000151104d51501134081392000c1c2d500c0402d00080c0c40ca400900d020640300344040c1118940c00302c261403420082c1c0c600200024003151041c40c00c0d006070080c90525034041c108545080002400c0b0318003405031602c030500800d800815010040d5202d40c0b14040920882c2442c43c0b40d080c541d12003685a111404056007262510881141560f01c10006850141d20004e550b8049a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 590904838 1250 590903588 590903609
    0x6100c02060403171c15050f03070308030606040e0421050309071502010906110d110403050c010302030c0f07150501050a03240e030f07030e0d1e020a05060f120601090609 75
    0x5400a000b01564451701c00030050040515a441c00d16000319003140e204100a490080d0800c0c2d1114204061040c03050f200650540c400070003000061103860255070f1203100184014285a558101c0041c1550201d40440301100c4030107058664082c118122506407000303141c42ca085151201d28070765039a01d2030050400200c04002200c9039035100750802c040143d4000d805102d408215041650580c10065a4400a505040c03800361194080c1c420380d4101e0790040c0061400400c243c005500075031000d411a9201e1000700002d080c145000001401224440c40c1075880c404000b13034a030012544181c0045205071929003007040415050000015407101074600450301001c64903000000384050b40d4000b0007800003040f5811100350300c0c80039101590181c0c07178480100041004000c41c0241c050001084c1c000051046c0d50010030101ca4081c1162024011501058490002620f190010b0019151204001030180d0768403002c03000072034203d070003800c028242e0740c1403041c05004440d041c0222032011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 590906088 1250 590904838 590904863
    0x50604020d17120402030705090c040905060114070f140c03030a1206080d020a1a220c18020403021201020f0a052217011a101209170306100c02060403 66
    0x7020a00d000d104541a00740da56a488030b042c415000f89084606030b10a0241d10b80c006010304094240b28880c0242602c81482c0c1420180040024040584028104580c0c0442000c0307020101008018503401240c0340c070052540b901c0c0100701600e0700500d0810b6038120320051110b584000054445200007420104840700c1c09070100001048541d0100c3e0312445012090040c8540110341d2591013070060200024510403a168010300300019510a42c51071070441c0e0502901c021402c1400d00d00348207101c00d580300755540360fa41811101c1c1c1000840200c1c0c3c006002c02c01c51a01200040c1000b84c200000d50500d4884004644a0300800403000140240003800c4600f41c1c484075503c0e825800c102d2508000281ca0b8000c2074086428203015841540c644190b00c00f5840c0d080c3d900c1c0d0403020300240f0b401e52804084004441118400d103044106036107e141c007030000341801c061410b00c0c0d0f40d1a000180c4901e0001d003001208003c1144010034481d183c01d1143c09038039514100e0b8292504044004503c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 590907338 1250 590906088 590906093
    0x6070605182a0d06020a080106021c0206060f03030d0e07080c030601151421060130020c01110313020102060601090e0c09060706020a090801150501020601090e0703050d110105070507050604020d 85
    0x748180c843c00107203010b100042c081e00e419040140d040c180c40303417542241c1c221307843c000414000fa0b032001c1400780540e02c44800285a1300d0189a045003654002e801d4030300f00302c14189070030700340c0e02080c622102d590000364007401107650400c00c1036420f150440040c0b130075514150f031401c02c0d8500e83c0b43c0d9400f046040c01040607064100c00c200c4401c403030a5064a19802082c840b0680940b501b92255400940c21005642a07421004038060034081142581400003201078042802035010080303040700365480701c0c42035020784403a001843c0700f0706c40380180740d4098480340300082c01c00c1301c000c110740c0c103020b403500060164041079160140c0c80180220340c182d4a804500010fa0b403409294402003040b800043d00100481c1e02151940407140740c0b400034800c103204001088034220643c0180346c0168000c0340100300b200d481c0d0300403100445215003918015900c80d212207041c5003020b641c0102055102c1d2240f40100b50074801c459201074580303440c6041c00034a58032107031200303c0500042d1042c13004014802c00d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 590908588 1250 590907338 590907349
    0x109030522080607020c0a091a041a0d052401060819060f090b040f020306060f071406010f06020c040606051c0609051e0903160b0403020a0206070605182a 68
    0xa4051076040f00c0143c03402100c001c1d07451038151109070044050000c00240340d0082c0c046c103003002e907090001200070800e03a001e010003030040c104800c0b0203038044e0f50460b6440d100e05101c0510940920042d00300d100b10740042440d0200001d20820446490300010806540e02100c455040f110021010f11a08040e405076000f8100d00c0e002290381e03c0660038000751090840c2c1c0301070841107060b0380900010440320041ca00301d000841320540c2004c0d08000901024545400400352184111003210743d0b6885082550b141000036002549c681c148480103000d49c1ea0104203070b0b15201c0040310103004880c100b003030007041402403401c54901680304030007a160041050300000090030140c44100028945242010101c1c029940501c40d0001628041041207001003b07c944483d01c001500c4d0134002c3e1544d6001254a00034816030850051102c0c0f000142e4405008040c42401804041020308110300d600303c5946610b80c0d601200d500c000c29440950034440039035119000380404100f080e410b1000880d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 590909838 1250 590908588 590908657
    0x3140a06050c040611060f07050c0709050a150909170a030e06070915020a0c1502031b0a020103110c1c02100e0105072703060c1116080d0201090305 65
    0x346880e0030441082800030b80d282c040c200701c5407244c0e51410000c101032401601c0d14410348900c0a8003043c503002445050246009184000c0d0038000c84084507a1139a40030112502500d81c401e0b029114007882d00440c5070340f0402c0010b4a403480040020900300d50341c5068001d03058900c075640c02c4006c55140403040c00382d84030b000900036403425a140ca10f05080024808081401070754600050401340301201c41c070008060301c1c102d902042c4030410710b081140083d80224421000030451000b0403424014100f50341e001030f82c0c018000000c00384c1024620001d800d80711400d00e00c41d80c81d84140202c68404200060410703a4001810781c144050b204610120300f0f04101c12107002d01c04e400c00c040001c280105512041c884c1c90705030b8900d07454902412125a0041c15112021202c0001403020f001140050380149032a1405040907089282007000890400d48546410103400740c28030001c000d07040d42030003e02c51911061008110050032554080c01c18019078817414042d00d00c440c0c1489000368800d0b00807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 590911088 1250 590909838 590909843
    0x5010506150a0f0c23151f03060f0204080a03050306040c170a0902010e0d080c01150302010c1b0e040f03020c01020c01170606041d16030b09040602090f090129070203060103140a 78
    0x50122a01c440c01d1381395208584107110b0030040e90040000d8150f0024084401410340d5440100307c0c091458407280c01900884003240543c41d400c00000410714804c200810380e41c1c0c425240d441d16407804500f00801c45466280042c284400203100300004803e050465130b110101c04e400040380c55040c00103c075240281c815003034000c40401650018441e01d003000c0c0c500001139000a005110400010450711a040c1c030000f8003161088003240009560030300c90110f844891908103044d81e5a0300407410801c20259030542d54910842c510009040d0b041c42b9107051080c1c280000e060b41110308000070858155207800301a1000384a0102e2401d5032900b04a40003003e00303402402c1ca008c102000302d0b0310400300b61001010601a07001030685d06000340110070190340c004100c81681d0f41c6035141e4001075800707074548036402802502c0411003a55446a03890117041850345001000150300071009100003401c0b2808020041800312100607a4001a040d0549501c0000034445c00203017008a4986480388200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 590912338 1250 590911088 590911133
    0x6030a0e0a0602160b130809090403050f19020d0201060e13060204090c050901022118030313080c0103061205030306120a0c0923041104020309070e0405010506150a0f0c 74
    0x1064061304001c060f40000d8024400e80e5071035102d520b150f00d540420b5400007041103c0c00e012000051405640c00359100703009040c070902c1c04445c03002c0d07a44140c0c0604009100c00130f214540809650781006882e07082c5206000030030009040580c030b0096441d0081c80440e0b89407442010804101040d010380e4000c0c000d481e01400102003101010300260000e022090051183e9034081c2c00041c07028110110303812481c44041c2c906050040450f2034032041c80304030f5415105c10020340400000440e40c400040c10f100e070140520040c01000101502d000d030780310140034030344650050b0201307034088101c0b50003010440d034005140c070860500070b0409000c0e070009060200143e03c00100034041d50001600c0c01007031034400090364082c201e20425104140e0f030103007641803a1035008105013070a0380110340203000300e4211007681d6500d509440000204440c1111140d4607042844004c0c00c040720700f589100c00004250707050651020008080d018200041010020055848000d00c0344500c040e4644e030390380020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 590913588 1250 590912338 590912347
    0x40c0509030a0b0a2307080a0605090a1410060905060903160b090405131a0414121903020703081b070f0809090705091503040204020d0615030c0305040206030a0e0a0602 74
    0x800141145040340c92050aa0805100b10100001d0365004580c4105c0c2c2080c0030300c40e842d0b100e0700329181e0800521903800d0301d41d02c54012400c1d40d1505290317407188d40074030000320740e42c86002c03402040c082002e01102e1015205d030b08207000b426040050803013550000d580e516210b42190001910308071407041d0041c0c6011007083c012540b41c0f44400180902101030b20300b4056038403103e001181d1081d5800010300101840280c200c1e01d03d14010100d03401600070500640b4003800450800c8c1800c11030890302130303980400030345010101c1255102c43c00354030050800b1814030340c1584010382029001841c02280c022602c0340040740c10000d0b030680f100d503078019a129481d04101c1c5800007841d07100d860702c64800c256810000303242c00c0c8240112901200d01610200520780b184e52020802e4001500c100c0e07100d43c09200340a5891881d100302d4005010b0f070a150240c001c0402c070054111040324030000c081509200800000da1280030849030050640200021030138030701c41c080f500702662000c0090940e400082c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 590914838 1250 590913588 590913593
    0x30b190506250c0807050307060c080c100f0f0b060337020f2a071401020c1f1403090613060f05010b0901201510030516061d0906040c0509030a 63
    0x601081503c4d1a2800c9031070007070701c0d00100340d51180d0398071a1200050b41024004000f48083c0e02800c45815204200d910021a111134141928000010101e096580b881201c14441c9980506601d900b000d07980d80d8a503003008003605400c82c0898060502e1f901031150640502d40140f03481b0003004441c400c0440d1501d90001d0344200a5010640384120904005150b1281084a412001c0c2032140407004144075807034042d45145841401d001d95040d03010303412600d205030704c0e0003540302d81d144580e40c0c05050b0307020f05003c00b8020070840304004903c110103004020545a0016031590010340c0542c03445100c080a1a00a01420900d01039020090030300e000000d840d02c40c0b4028040d0701c04241c84500b101d5007042020104012403d4803011300785e0100c10070b1541010102c01007500941c62a40c44000780761a520f9940c035020071004162003403403c0314001c1000c90350046107180d8150100300c02c6440404800001069400080c3c0104d100340d59031925071100600400456008000c05426180342e00d4050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 590916088 1250 590914838 590914853
    0x3040503030403030b0301021602011d0913030807020d080402010c080409090b0901111806030406060e0c1e03012603041e03060c02010513030503060a051807030b19050625 75
    0x1602c089003c04c0c10040480705a240c1802a02c8142a506c3c035485414040f9800440360780041e000a1084010780c01140c14030703030700e40164451003014500d02d0851021150710f4020012940200000c04640000c03500114159112904035045a02464440003081842c286030809101f26440326403400d2a0080c07880030884042161881510100020006642c4108032200e00307208100c0a04d0382c2d506504600c1c600f030710b00b00d0007440d00700c0d001d480c00090b20768841e030901181090542d40ca1082c16000306207144140012400e2051003901d8602c4a829945042500002c00000408500e080c202e036500b8071403901410070039a40188544c0c14458486415903100301d60340c10780c0b4002950501c0c105504c00b640035005003c1c1500940820304c00d80c00c0186540c9003101e15400150403a035201360030200015443c1d40d11549009000f48403501d1b60384506040c0000b80440f8810078049008034103800e030001100e100f852b0401b04803a01507a80700c0d84c03520520b103008500c0c074000040d5841b0300c190284090501404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 590917338 1250 590916088 590916091
    0xc01050603060f0610031a03070b0301080606010c211701090c1404060801120c0f030812130302060a1806060303050415020c06030a0c05070501050403320906031b0304050303 76
    0x1542503400d541c80c0c40904101010f01265030982181055a180ca0890f1080d0300c250142c04a24111429040000000a007030000c80d900c0301d20304a10110040c00290014045240c00079003d00781f200141500d6605e1480c1c1481a44021125540160b42d4107202030092600d0f04840300c0000c5404030a68407002410010304140c3c0b111400241e01c1e01c164520881c0602c1200c044e9807154803110710303a80c603201c262070030740c0d070b041404075244050343c03100241ca150700e072800d10040d5116222864442100326414109050000c105881d001440322640c000300b50082211030700110380f0440071845081ea043da111050002c03440040516161120000a060b0f11001a10a8610b0800b01041c14440000100c0c0d41c0c003c2210419071110081010604114483d0300c000203ca815091542c140303141500c585007101e40443d0160081440c0c1e0740d40b8652103030940c4034004480c810005040110500b055980168012030350fa03d8050500000490f9807605055840b004411a01851942c1e91030540740039500ca400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 590918588 1250 590917338 590917351
    0x3020711150a120515040c090806040c0614072004020705030c03030109150e0f1008031306030c03090818060909010b07030816050702131d011b020307030504031b0b0c0105 75
    0x503e00e10302800600c1802490f010748a0700b601d0640c03a02464081100802e8420b082a09001955500098030b0105100d082d100f60301a0448a01103840d2440181620983d0000c0c001d10000c20800003000401d40500e5451503015140c40c401d10200100c0403030024858102d01802c1c62001103070700704a0403000802507040e41e01401040c001d6900b01244604440100e010301c42d241454403001a040d10652420194025031034123682d48201d030b03a1404581140d00c0311030040c1a03200e80500620100c3c1d058001c428800006185c01c12803115140c48283c40c50103843d8100540010700828241181d40300410b03600d00c080028141c00302035039178110303581c6141e01000d02200480c11720000a07500d820b6100140b20342c9442a15000e1402c040703a0b0030004510206100320900c0341d41c2e0a03c80c0340d0407114401c0031100d140380d0000040c0041a210b81e0340b01044211048404540c401c1151100199114068a0489901494100707540c50f49451100504807981c00030b401030800410500314103d41500b1481c0500c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 590919838 1250 590918588 590918597
    0x80f03220806041113050f15060415120204080106231c1217070c02130b1c080403020301050c0d0515011b020a03050703050105090d0f0c0303020711150a 67
    0xc02000e00040000c00c5486038548940045000602250003001c0041c2061001001c001500161001d107408841c416036040d0020b0100c0742c100501e14180350781c00c4401c100121021030401d403074030f00d1401807944c1c501c941030f00b000582a102e054104541d01a1800b900d0088000c0c407602d500d444034a400f0300d05034000d400c283c2c910251480c04900f40300710100250180d0f030000c200d1040954036aa0054209800c5a104201c260203401c1d0302d541885a029000d10056907460440100e00e004110304149041003840041c1e20f0403030440c403e1303580c1900c0b9912900c0755503280307440a4410b00380701016014503071020303403d5401c00c020410082403040c02000d21241c0424104007540318940119159042e85660381d0101e0800030214145064a80907241c010780300428000712183c50340e0b40c80341041ca180c0d0046032540c0d190000d0001d800003e109ca03038003800940c9070140643c1d44caa6001000418001405030516600207020010f001780d103e0f52618800000d0140003001d681020007511030782c001d22680c0000b9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 590921088 1250 590919838 590919877
    0xc0305040b0a0b0a09050c03100b070b150d0f05031b06150d050715030b150705060a020f090406080c0102060106020d020c10030e06070f230306060a090302030607020f1b10031104080f03 81
    0x142d92b10300350740c84a07401c001c0141e00c681e10300c00c95900c904017101c5e4070303580040d02007401e000242c80f5035100440700d403240d00550b48501c0b18990400d400074082119180da5040030040104007001a007030b42c00a200104d400c040a02d100d8204507082c1013035900100c509151080701605440d4042c1c000f4001c010003991210820706e10b1030b1031030b40380380143c00009010307406c18404070703108080c07d030080d03e240c2a07540c03820352921160000184c00c07903001d540500d4a9070801c2115840719a0180001401428940040d000d5100d81c28030081d00c91125050044c0b00358040601611100e210741d2100c80072815000445005041c64003010b82582c840300b5406000500c00300840303c5849880b2900300c55a0b055800590843d01c0700400c001460b086817481c10100f060b51a00000583d8040040901603002500902580c6241001c90344c00e0202684400c40a40d81c0c80e40014503685400100800e81e00b010b10700060707440440250741526118070340c44040325104070311012009a00100003481076052055503580381 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 590922338 1250 590921088 590921099
    0x415080105090717060a080a0605010f09051003030f0512011d0705131712040b07141203041104110c0d02010e190b13021c02040c0305040b0a0b0a09050c0310 69
    0x202c421526007002a095600b8a003140040c003200c1500654010207400c01d0341d071140062842c240d40345505581c5507032980010002c50541c2d96502000d0181103e041c8894a0090210b082030b5240d440b0017010410100032018080e0700c00c90a5a6040700c80c9026449156503520058003401c1e0200300c01078035900c0f08404140b0b1240540c04844a04280c6030202035610700d08103030b482c40c04018400060050188080c44600d01c0404c40082c000707031100c100a20f031501d10038280341000d40788100500c000c0b40d00090807017a0240744401640e5200303910bc031b07580521702440c0010a001c0d11404154989816000ca031010301d2820104404451750384990080003408107070302d01e0720b51301d002c141c088071203a1054002800c00b040303074040d2150380000d0540b107410034894140e0203d04402070b5114040400503c4100450440c030f000e000b00811030116107010f10250030191201c80061901500c030641c0c07255103c810300519207607050044003c1070715003020007203403900380400c241c01c2e4811103804200e0006804003192 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 590923588 1250 590922338 590922349
    0x20708030f19060e06010c060603050601082505130b04140a0b040f05040b0a090503041806140d0b010936110a0f060503060f03030a021b0103022d07080415080105 71
    0x48403039001240310291117560066840c0ca0b00b48070141c8400d520f8080204c0415410803c050007400900001c00c0b450000034041c071038185401c00e00034820340074588208101d03a80c602000350704101410001500d940307940006402070072681040140d5420381000c114400002c5d600c040f031413440c2980d09200c441002e0f481c240449100300d4000b000310b058030700032403115281070b0300c28102a0300c10b00c202ca14043c1c075161012008411081d10f4070b0510346402c0280401183d0740e1505404d41e00641d4071060601640c0c1c1c54050552050083d103200642e40e511f1910848004400020000c074040b850001400c041840300f5030b507102e031020988190800c0c0d000e0301894100b40d55070001300c0704021107802c01e0506103078045445034005400e099200c0181200ea103159a003d100030700c4028200d800400b190b4034000120080d22104034440d40c141f510520501c2818844400603010a8041d2240c10090f000c03034031a2020140142000548400b13403b1a021400c2012042c10340070b00305d42038841e4007081e030b665801c011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 590924838 1250 590923588 590923601
    0x160501210c0e01110c0d080906070b090c011e050a230409090209130812062b060b0a0b0702040905070b040f06020127020907201b030a17030703020708030f19 69
    0x140c0113003042030b0b5040807c114030301501030440010829031824180743c541440010f016a5a4119034010540000c555a00184081c8000c1e54107000c6441c4a114424050003a000316070001d024851034000804070303004461800000d107180c11841a88990f00c40c0c0305440100b034521012802902c5a50100d49040d02103c0d05034103203540500f041c2d2034018942809020444040c01d01030f001b201121418030401001000c200011642c0140c0c2c10310307580c0b1401c0c080107646039038200341d00034070100e2001e210581185046540640d0143c0c0c010584943c1868040d2602c49950b0100d024060040f0340404e03c0305070060384004448640e8024000e01210941c01029000040a025510800202c408005080003107106d40d0003501342c104041c000300c441580301c1310a144201010070680004c001287c444656480300b4180c0e85080e00105044070003a80c1d5020b2603183c89000c40342c0440c0c080001040e50b8401d4044500e056400390606440303081100c040c0400000507070740a038003102000703103c400002543c81040c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 590926088 1250 590924838 590924863
    0xb06121c1d100c1e030f02010c03050f2a03041115030705071101020102090d151107020307030b130f0302060103061a09070807110114060111160501210c0e0111 70
    0x50150b00400e500a0300c00341e0318510100d4600d411125850099410104500c46403030281d00c43c07010000c0300640c000d084545080c2d4000a05282405220f042c500010300c442d4009140c02210034198080d91105400311803e81ca05003514900004020400c1440728aa1106000c161416820030361442c140705201c0c0002c9a002000500c203210303030000300c0d4030b4001400203140180001440c000c03000010a03003211a042c000d0b24201c03442d41b480070b01581c0702d00c1140911145112814200141070303000030f465401ca0711000d0403015021300030074100c866242105400d203034041c01080401449180180d1180000d220a41da411300d040c41c94508070310000c0440600d14801094289240d80740e60055520750300280061041005010300c041404009226084a14482d0080080c3c2460028001440c8820b132640010540d004000b048140920798a2400180e61090034071081d490080f100884195060b1401d01c0b070502e0614204e0603185400c06911201e10100380e07119100c1d210101c141c290342d4a10b00015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 590927338 1250 590926088 590926099
    0x1403071502100c0e06030406050411060c06130314070b010f051203090103150b2a03120a09150f200a0516140604150e01180b06121c1d 59
    0x403025150030710307032156000071102d0400d03405100880300822416082180c1c11220141d0390310030700ac04c0c01315543c2a62150703a401c54143d0700d0308140c03040340380e01c0b81300c082c110441c219090300c01c101c10103000d0700700010005070b1482e20549502482c2132120103000c007031042c00c00c1c0d4003148201144500f003c80c01c80001003a004010362030711283d440110014108070302202d0700b00c900c0d0b21003c603051550200402031658440482002c140b206500c103003228105050f07042203075104110780b00c8240074040b41d03a0707808180000d000418282c0c5003800030703004884603e0803080520745a60702c04895a0341d403244903942e070000c001600c00b04444580900c140b11307850b403e001040c0701380840d141c405486060f010ba050701c101b0004200c2e075401c84d1101d184c01e00a840c125918001c408004c003100c04a8411500500d80c10030082c020b01c00c01c8442015204542040503101000d40c000260460302c1e001246503000744600d0840b0000d10100d0fa1405410000d0744140000400e0103003642d1200c05021106000030000170300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 590928588 1250 590927338 590927353
    0x30609210801060c0803190c02010902010e030601030b06090901110f03010e06030c01091e0b04090e190b0a020703270f0e0c03060f1302030901050109060b07050d05221403071502 78
    0x2c68000c5030300003d050568040034141d800001014034000da48c900415500081416151031001401c0d07407822201441c041d603c640010004120180301c49504001709640002641d03e0302c41d5024054410744484643c030380c90000d0b142c040050f0240041d4120303020101045501c1c1c40d400d007095240c801480500e800110101030900007141014800180d1a50800d00b502503266944048401038101b030703020000060303984100f0801c2e10070910010102c2c034194540416403100d103607107032004554090540a13610344c1c0403852101b054040c1446080c910a960401c8101c00d01140242c102401c60303001e00010440041d0b0001007100c4604069400790362020a01c1d41941d444005100034840c1a20603503900c00604108903092111620056015102c0c0c800081071960502039503034151510f0b0b520441c0d00e1003041155602044000c1640c1d0441c0043d441d11035a50244200b0300312803200f9180e004034881c0740740c00340081c010107400a00100668103070180c40c406955450f40342c40f10b121b120010400340e0080301c0e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 590929838 1250 590928588 590928593
    0x3150b030a03030b1909020706050105062b0b09150102070803070201080609071e050a032d1d0f01140601050c070b0705011407050306150412020d0c030609210801060c 73
    0x40001c040c2c44000740917401041070031030b541c00b49a01c040e880b0103089540001d0800a2110030300450340500007d0385c0051a05050320040840314141402401703542d0b182004561404a468003c0304680c0c1004140c140c0ca070811191030f6517010403070040d180c0540b1981a0002c9ca0040100a841a00360161280d4015503240740601c184100000c00120400c01e50304800e00107105e8a80013162110380c25560030b0340710068040041c0854030720000351003020714000c1d0f80110609022992507044904458041210050401030f00381d408002c804e50009402400404800c09031305610120846400c1c0700c07030880c07940b1a180103403002d101d090701c3d600098000110501200c200c400081c00024420400050009040c1da0031024440054070741d1030001d00004180070b090302c0c3c5034151b4041c0c00480100b50740340c5480e200610068001c41d050080c050103124050f10140008001c02070001e582080c0140b00080280c9000c610b40d41032400e01d0381d81074000800d0740e000d0501c5090518140d5155031a070000184258 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 590931088 1250 590929838 590929841
    0xe01150e180d05270927010c020102070201032f0c0c03010504030905010f090e130f06020403050c090a0605091506070c0f0617100302040c0908010203040c03150b030a0303 75
    0x400030102010703840304036100e00340204014900c1c2c2500359106903d50101002a1003101d0510400c0d1400c44903184450303201d6901c510707002e50400101c1100034851028a1045602c03102d4030382148110754030f010812410550190010815580f01340c1c0d080085520008451418803d00c401c3c040c1030300b4040041c505036120610081c4002218082242d80032000d446c002403d64404940c01c07400200e10340300c10802540c0016030105612824203107846414184620004c038980000c000f0440042040001c41c1885503c90f407482409401003c1995510744900302140d842d00c1c02c10742c10340a1044180054189241480f07800d060303440081c942c0786c00e6100c0e14824280e80440c0c45940c0d501500411008000407074914020008010b41070410300d810b450200081c00880c03652a808105500ea071040060424400c16000107503541120300080d030750f01d020300440d103414071b6801040d40c03503200005101c244100d0540b0541201c1c420701c48000022260050070b0180e601812459403d0b0740080c1202c40020f009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 590932338 1250 590931088 590931091
    0x90e070b0412150f0902090a050906070f09081605090c0c0304030605040804090f050405160602060606130b03010f0f051005030402011103130e0f01090b03100203070e04060303030e010e01150e 84
    0x403030f07020031004905800c42d012940141403c12080765904803010460a002d0f1001d5440700d00d4081c200400d151028843e82c4411008007140e04001c1e07090085103000e401640c80101a00540c4222030540380a0600b10005552074022244074a00000c00140035003480740403100610043c0002d1030405155a0b500005044040c2040707808400520011440389494401c94003000328582012403035040c54100a420728501038080400178015505c14000650001a015004a001d0b54025942d0181e402c140080d20b1107a0002a4140800400050100d800c181500241c2300820340c100040c2e6503450412888000701a154404a5001c1c07002a0266014100c1844044c0050f015649800e9140d000031a20140036040201303040342100500c0380080e14064000d0141414180400580440c01c2c0040e9842e139a10034510510303600000060013051080c0b01c0550b203980c0191090080907164038019001d000d8540b8500300a40c40e0400851110405024800941d4030020b603503912503080240710030a071b900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 590933588 1250 590932338 590932343
    0x60f080d030b0102010219030504030914030703032307050f07080325030309050303190f2304210809010c02010c050d020702031f200405150c01090b070504090e070b0412 74
    0x5081c0006850154800300c5100c200902341e40000703062074186405000061640c00c24201c84004981c00d21454800040741d005494050404100d2001c440030600c040b0185000d83c91a1a08085041010000d0000356401d411a87c2415144010b0b11003481c02c0e0399014245030024500607044d03200495620320141d40c2071250180c5800b04076030490340c035a140745034410780c1d600c03c507040d4544484009481d01e101c2d960220030055000d10075400b0390070000518100840701d100c083c40010001c18200b0060b202440541c922007134000e0038080860a003d80348400840700c081d81542004c03d04140540f040c402c40320340c0b4546440701c6042206c2c40405a00940142e44120380500c580c0d1350b804c034400620a2100c45902131241c1c0400c2c2c101e0841c0080401e0003031b240040107106000c0c001408581d455254020801e031303005107040d45844c800c2c00c21034090010b209001e40344070340a40500c51482d038403000038030550b80407074000d0108413200e032140b980e2403009104000e414507040c002884038504040d9820303070103030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 590934838 1250 590933588 590933591
    0x604060c03110607050d11040b030114010c0f050d030c0c0201080f0c0408010203090715020f03042709050606010e0d030c06050a060e10030309141e03070b0f0706060f080d030b010201 80
    0x82e911001c40c9400e606a400201181c004656258009941e00640c0c60041c58400c0031403c1604d07100d442841030106000e540e029a8440d041c3ca2400e07442a61603d00c459003140310b603540c0c1c0c0000e0501c0303611070b2200c100041c0041d091802c207862407400364220f851050341c1a522a00d641d5540343e140d08184a01911421010300304020000d0903180c2400034500407014000501a054500400240b4000401d50f101082d90408540c03000d994030048240c030100d0b02885100541082c59950a015141800260300007003071a00e8601d00c00e015000031381c0e80c410002a00c440c0072507001001084280010600c0042c0010006030b000f20020305d44d500910b0700f2844a50b4045129601c0303ca80c8005401d0031507806405c07000b101010000d0503440900740b0001d0020f98044c56844c041c00c00807c91710a40f0141a681140340400102d00b5510300300490001032040720100c03070315900300082a02440d440b22030140d5803107017480d0010a4902ca0a4600e0f4200c5005800a10b52010030074406e80141842000050565 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 590936088 1250 590934838 590934857
    0x301140904050d0f030209130e0c0d080f0a030204031a0604050a05090d210509150705030c04060c0c0b030c070c08030c0c0111070e040c15020c030c06090310090f200604060c03 77
    0x64881917a844080c840504009c81d0201e1120740061500c40300c280a10b2241000d1400d61012403405401c407404001c0600243d5611411520144d02a120b594001000d001c88207240300c250b0324504c00100d01a420889080c00b0a85420a90700180c400560308641e160b0404c480c0c100340746001c0c43d06034601c84074624441c40c0c9840074403210011140200c4080d40d00340c104200ca02150000290b9055112085082c61070a60400d0800004640190302501007884540c4000c3d000b44040c200e9004020040c20742495924581005030b0502600f00b51012221006110f002007090030021080c0c4264055900040045050460044991482003503000020b40034102e000b2400e0a04509074500c0b882c050020003603c0c40c40c0c84d0130700b80e5845444000804542291901c0b4019035008110040c0d0070000315011502e8881c6900041d08201040300070101051800450ba410440800010802c0500411122001d9440c40300319081018002024039400070081100381f00040c010f034103000704a8000c1c504000039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 590937338 1250 590936088 590936107
    0x90c03060b0c150c1303030804141b010e0d050c010c140a0302030a0f020c0108041704121a01061d0d0804120f0506010602030f0d0c110d050301140904050d0f0302 71
    0x590340b0442d9a5051a00907159006455602c200c3c1150042e1407000b5141c50130101e080e00d1640543c6a00006080002200c085401d00000040c0f403507100749400b0a40e40d1810854100010718103c3d810400e010800110342d958040c0b514207000c1e20202c1d0810060040300071600300455150201c4001241d0603102000d8200e4464010002e01c1c003a540b00c1d80003155104240c15020705005003030b482e070b0811540134003251460350f40e02c045001e400c143e1080c460082d46800002031240c3d40a40d40114280e043c0701880b00081c40085041c02030048403001445010f030340c0303e040407225034044869491122294903a104514140415079583c50b6000b02109070810303813505e0021104060440003918a20f84842580052240c1800000c0c01048036000851511100384058170580c0158080d1146d82543c69400c02c130440c0c05026001c0c2e100c90a481512981112414060100e030400e00a0401c50700d100d0b40d6095480c1441c4a5040c069a08240280121a01d4503c210f4040424078602c4040540070701042c0700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 590938588 1250 590937338 590937359
    0x60207090c02031b28021e0102030a0e040f0c050d11030603030f0a0c020604030b090610140d060e0d0807030b0a1a03040f061802030c04090819050f03011401032301090c0306 76
    0x10750301c0c0070114044050320705004006047c50500d11001303c04021030000b03c00d80c0c1e0000100c0e108082282030542e056200c182c0006c004250307554400584074104540b158a00d5404401080501e0601400300001d01c008200c410b12808111103068141d48100080e21009000d03a0240c88041039504e00718410070429404203400b03402c254411140901c62a060040c1e07001c061110396407213031070409000100c504c3d1030006103a00d1a41d886040c0100e218034000c20034001c1c1034201c48c020280d81c1c0700311480414101c070001c1542c4011039807100007a15001052032a8500605614100e030140c3c400104401c10341c090359070103903101802c210380c410717200f401d0f45001540c280641c610845100c041d2404c6505036006040c1040c640c00391032485180340c1610540010f41c0401551404c0001c65120040d07080074040c02d0b01c003031088203180784400001100000d005c0100102d80c41c2002400e0343c061201206580d040100f003140e480e0222241c205840060010a040364402c0c900710768186004101107650301c2c01c80c0e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 590939838 1250 590938588 590938633
    0xb032a0403020f18071d04020a0206090708071d1f06090503070e0c0d18060905071a1911030f0409060303030b15040515071407060207090c02031b 64
    0x801084041030030410340c5820140390306141001d4814112110a41c0e10308440d60000070308103401d2041a00c00981e0321040d0b03030800244480060811907a8040d0b022000c0d580301300499642d0098440d44402203125000880c0040c22140b01682d0700301c0103081c0003840362401d80d008000161003882501103104070079840c41f05100410b030f0307511180c00315400c080c203040c20f0101c140c0204140d0030a000500178026a203000b25901c04d1000d45002500301036001d1802010704403044080d013554200544031052040203c0d1031030895160041c2113001c41c1c0c08503008070490055075100030220711841c505001d000d000c5c03241084400450415039140c0007488480c01811340003a001a0304490b5155424820150184103020143c0130845501025540900800b01a40700d0b0b801498007940340704848150610009044d203a410781d00403481c0c50a200c50001d680d666440f107222302001407045030400180343c0980d00c2400c410420650140d032910425a6440941003003c6021140f940318180049252500114540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 590941088 1250 590939838 590939911
    0x2a07080904050f0a05070504050109050d03021501230a03030c02090a060b0a0207080d020f10020d0b04051807050907022a0a0e0106140906030601030c03151413150b03 73
    0x3d071814284951028200c902c014581d106100c1c0402062209a1b00048800e0480310121080d04034025070345012410481244019020118010004900c4541c248800d4020f101c91340ba5144092203000304102a400c00761102501181d080c030303000405030414039446075010010b0b050100c1c8255aa01c100003182d4814000d810042e000b045042c001402d00b840a4090304480e4801421070300740b800320860301c40c405074a46420040e4001040100680517400100190800402c00c1000e481c05400402c07000d04800050822070140000120300c900d407542c0c80d1405880194002c08130b10cd4080e050b848140400518041030000065110920741d4a042130030000c5d1490704071245840d450558040c2200d10312041014401d00d062002180d90b8640505a1764052001d290100d180ca40c003580a0300140000c8010041c4000d05000118083c1c0380091080310004082d00c00340e944000340a0182e040302c03e81e2006134940401d1a004000703194051010319040811150401c4005000c035488003608081031850 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 590942338 1250 590941088 590941111
    0x60a030804080f060a0b18100b0a030204080d211d030a050406090b04032f030708010509160b16141015050405040b071d0915092a0708090405 62
    0x202c103050f6400c1c003460760000001d10f81841000035543c0001d5048000551098481015070000b45c00404400091001801d038401c10320b5403020442c0e001400795005005c0c0034164440d101850600900c1032400b0780a0410822071800c220142c0c1249502402060042542121b01424245c0c04800300303100600c00c00e42e8a40f10681c0d01e0340742c480301609485682e4801294000103200407c04902c485040d808000080d01c1006003544100e5441c224601d440b1840541500c110f03000805c07240015400b035405807120008541c074910180c0340203031501d400c50042400b940c03c18441c4d03103c004101240700d60524400e2851001c1c1d00081000315103051b0512480d5842c40e03031100b0304101c001788580d0281028042c1900c06000615140e1101c1842c5c0034054041e034104000024161041c0e0840f0090920074100240314803214201420f07814182a0301004991141748480003051072402080451114101003161007103100c003801d00c80b1134442e0460803041d60707942410403c1c204540d956128580c8542001000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 590943588 1250 590942338 590942353
    0x1305030105090f0a300c1b080a02060904110c010c030b15030403110c0604030501020c0601060906020d0302090f0a060c05010f0605030703290708040302100c080708060a03080408 78
    0x406007514406889060242c2020001603030703448010403d001c220380c1200e0700c0b1007420ba40803680c3d4103450981d02003150035550301010a480a0340701e001c003a030542c001c08101d44031155002c40c039020702000e03100c1c0f581d00384e10415080c001820b003103016004002d0010000200b9186146146400c0d522461035001183d40d20382c0e2a038a2160944241c2100348000d4405040304540860795031503600c0003400240c1403040285c62082c112008010b0f005c3c8101018018984480d40d900d0658042d402414084481d07008880010591622030f004c0f072421241654010b001c481070000703055000b5440340802c01d40100740ba03000500c0984070000e040008108a556061011450742006402c6402c214041034500e07003041001c10042e40c0000b000410b898000100500c40e51310070042c500b0700300c201168402c02459144c1000005508058414803681c025000d40740700700c08880e603580c01c88001c2061a40841c103640049403145100f02602c951100c006007000c2c400e01c1d200d8544190a8205502c2181140e01406 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 590944838 1250 590943588 590943599
    0x5090d1401060b1b03030606070f02041d0c09060603100315020c0d050c10050105130b220b010f09030c090c0201090b04050d090b03190c090f0e0a0515030c010e010306030813 76
    0x2e20300c1340c503201c1c1d005182581040301c0004d0721480740c12070181417905034124440c299901c9910000100070a440ca103544249000c1c3d649440e01d4079064142c0c41040d4102c0094564249a0101d038070070f4a481510b401c07114155500c403944811f03400502c1010703990a00a08900400822104038041c1c41511615140e9403207189041ca4490a291081c401e241000d0041060b5203c442850100840f0341d440482ca41004c007001c070b00e500120300c6c900080d00c0f03403c0710340b503420145541c852891600c0aa03110b0484008425050354035000f00e2200814804040c4410040c80f03140b0b0740150404180c070b2001041c0100203484214a1403019101940c1a80010204500c016048003500004110a80744281545444c548640c69282c0c000d0101040d20346402e40114507500c100529000b81810b000310405035500d0f0302c0301c0e5004ca04d084903e013802d10310b003070081a541040740c00f0383d01d01080002c0050510f190581d0044402201b409000c60505440b01d1000c000601c14402401c1503220444607480490f1811 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 590946088 1250 590944838 590944867
    0x8071b060203090117060613030b010e0106020d05040e060d062910022505030607050a0f0e03521706040b04170c1f0c05090d1401060b 59
    0x961180d01554030401c6040090b98111200c41026900898007a0a582e619804201c0905c1400c5450060810886000c0204000703500e0140c180c0f0081c140d002e41030780c0c840c0300903070395504c4032a03041c00072440c04d000810002d03180c1456036600c45030240c04040b00600300d50f141000c8d03800d0360076091514141c6140000e080d040103000c90802c580304690700c13072646242c1c40019481d251798409a450400c2a80c005103171000042418034020f0801a045a40b00c0c941000c0040c2150041e5285c4000241e0034102c07003080354030510801c030303207030400902401011505000300c0000301102d03c030300039000c0048914030740d10300c04200020700070800e118440d00300b88101320702091415189400c502c00c0e8001c881c019556060002441d42d07270055119428140c2d645403800c044010260210814041c1352000418044000c4081210009100324050001040b12202804c005807000300d4090000580c0c14410601107140000c00c008180d4052488690740d50981e4403a03e082d00c5640d0400d800c40310b000140041c02e01c41c503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 590947338 1250 590946088 590946143
    0xa0c0b06030d090308090a05102703020616170c0106030c05060a08070f180f0603140105130c09090e06010302180c030601031d0601030308090c03011109120a0807 71
    0x8401030a400c04882c00c01514400040c0005030039460089039142c4a5120a10217201070807000702a11b03148400240c000f003400110780104c4d0042107903c080041446072100584d401d980c0d00415103810500418030b103c80c1d0b8402d0035826561141c80480203610010024014440806048000b150550460a180b09200344550003030b8006d0700e00b008082d24040c0e028103e83c1d000040c40c68104248002d00d04c4c204d0b0140b6100c610700d011400481c1c8005802c1c5d6425a003542110025101401071070340d031140d440103e100920507075800c84141e00d00100b04070416031003d083c0300f02c0c80c108508002e444138140d0301252040120410036a010300018400e5140404140c1445080c0e014400d54074a040400c5000a003c00303000c5505154403503c44401001214800315506c070000300884001c0c0d80e4a040080950100f0740d100f91030b0b4040c0c00403010703680c01e0602980c5440e00382c0010a601c8c2c1440d03a024040800614241010700d401200c10312800980c2030300041c0700f424021100c417002e507418040c2c40072600340c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 590948588 1250 590947338 590947351
    0x20d060b0316081e130507152d210f05060f0307081c1e02010f150506040515091003090501140910150510020304170102030709031403040b0a0c0b 64
    0x581c1420070804c485462220704441c0d078102c0000d00107480b00c2c22120900359014074024964001c095000c50020b09103d060481040150741b4551000e081d030030404900707041d409400300700ca41031030b43c0d456596000c0c09080365064000b41c04443c4c0003000004220803580700102801c685619030b01404201e01d05079102c4046400e0071409801003501c2d004603140d9407092121008600301c2540c4400001e1400744001c182e00007070703440354000b2916400c0d100a000300242a5003c028602d042c0480c43c162900540c814255640a0015480d20742130504001640c0c80b074800840c0c00351001c0083d0402a16104414907030b1f041d40361000f048452035440e005081d901c56a115124100c802801c02c00e6240c00003550702d401100c06503001179003070b61045030840101c030250801038203d140c03200b12000c0c0742da00100410440369202900c3d207130321300584259801e130321042d51440005064080c0c140f0103d00819040110b05040c1d2044901d000d0380c882031612140c111184e0440400c8014040c0c200740807008500c01d0f0300c00c1c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 590949838 1250 590948588 590948597
    0x3050a0605151c06051e07271401080a0e121317150a0c14030a0605100c0b0c0c120d0605040f0203190c1b0f02130203070f0206010b0409020706020d060b0316 69
    0x106402560001a24010100c80c2046100342c10001580d230a496110100c802000d0003a90058071461200082c141c101c0700e150002da03544002600b41d00142c070079107910449841c060400c4002034007400d0610303080300c100702166600181001440d400d1310344040c007584110002404060301156081c0701d6500006107080316950401c1c0c0500c680990042e0008400b550500949071a0388072250554000c000540149400803031034200b080f03445400c4460a90464400d40054490355244488003500b4002c0f0480504554080441e040301d00041d000174140300e252200000400e1035035500010700b0351b0b44001124403038560000c14080540390310345800e001c4501d1094240800405d03e1001000d0003003000c00780e4511101c82c0307030a008020480b1030034036407107800400a617000764100108078000e60050740c141002c28840340142c04954008500c4074100c540800c1207030304091034181010060350041c04211103a59081000b80345400440c415032000c2c1c8064404541c5a1a0200005001035007044c0b5110510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 590951088 1250 590949838 590949871
    0x7020d0f0e060a0807050c0a0c08010b0105070f030807050c07090506010e06031b0d1e0f060e040b0412050f031501080c0f18013c0903050a0605151c0605 67
    0x20740b0351808551104120703240a0443d50350b895022a40c601039490782d0440350158100202c1071060480f4061b0542e1002e00080224000c10401520755100e0303604020603030343c00f02000740b01107406903864030f5210a85040291825450307508242c00c01115070020a0f8490b50740090240340d5078000c0c8003c505482c2541cae144d20350b080200d07402d506099149051060340c80c00054551810314a034202903244403911b64402007400340d41069202414949200b82000380c0b07408000607411030900351990195401c100312150f06d0f15a919504030500001c00e9800502100b00400210401c04400861242448248800d03004521000041016401400e0011140001e0203000e020301d41c07140843e08000c80408089100690b1140140c0303001445240b01446072038002c2502d420a425070741003050101d4646031118071035100302020350f8281140e01000d031065020414a03070018540381e0207640c010f00300c2402c40320f01c130342c0f04d50000342c6a0400a0b038040100000200005c02c108080c00396907088180c1d40d10341c1186 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 590952338 1250 590951088 590951117
    0x8010e041e1104020c0307022707080a1803020606090f09030a200111040e07021c0302070203010b120d020601080703050a1704030f060605030c3309030607020d0f 71
    0x101c800340714001810480c281005410001c50710407075810724001910a6440300401c5245a480f0703085950268090f89412418601c24402c0c05000160050240604413040e11001400c4602c0c0c0c0005203901030081d90354111a44208840c26030303100013407003035000b4a90b925005003480103004001d1b1450310f03681003203401e00003070b84400300a441906041d85009070400500c0c880115032030041e000c0401065190041c41d100030300700714008200f6100d007201c0f100342a4843e00350890780e5000785282c0c0403a003007205206410462103070b00246007090008001080e141c0c40c110026000302094004480b99900c100307007880003282c05001c2c0a005000c1040a014410316646034035403906d0a40f94020b11a11000300f0380b00040b0483c0b81581c01070340e0482c0b12080ca4a60b80d20300f0700b009066902446209101c3c2114031a9245070000e16603a90300d011017090124002500d000d182c40c0020758021541ca0b1205001c1c1141544041105910400059008060394500722201900050b4007001d0300301085180c0d40384412 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 590953588 1250 590952338 590952353
    0x1020d06051804120c080d0e010e0f0606030705090a020d06080303102103080c0f0d0c0905042d09051b1f050a050a030b0d1109010b2502150705010c08010e04 69
    0x510200d64188400c2100c1a890500c1b2240314164000b6407891a013400f070b40c8a40415440100d01c4000c00084518850450240781d81d207620440714640d140e0701a0300d003440a804c1040310395402000d410750140c1811018038880c41038130039036000951698008404c001528880c00e07440401001c0700080ca460444a0458a01020040d4980a414000e00c0d0010800c481c050900301c81907140781d8190140c803121040d642e0005441c240b01c0300710010f20301001c08121b070714140c4150061000c1034180e11600d07410409114030002403009070f41c50000d664003912004a041849013100c9424002d400d000d440c20b03120b08000c458034a040407044a11344c86c484100020f134100c0212030511f80c0d10304200392a02e0321b15000320040d0500e030312015001041c0c450408104085c00520f000110800c0300c441d09503a80721014002d10b40246110070301c035002100501c06041e0b0760f02d4010050345001521465148080f20441805680600e078100c4403695038840e0060413030361241c0c8284c0034001c02c9820380524105a100c01c02d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 590954838 1250 590953588 590953613
    0xd020306010e04020325030c0b0306131d0a151109011205060a0f150f02010506030a0641010e0f0a1d100b0405090a0b0f071101020d06051804 62
    0x2c500c8810311021030159030342042000408000e142407582803451564109038034003103a00c4200c811400c401e0003c6101034032201038910405014000803696108002d143c405090704070107100c80c0c0100310201c0209540148045603500c2c0c0111051282e00c40e240e010b50048914801e12440c91800c10300100d28140c1e4005240804804407003004501b603140c0c01e000804006a40d48407400000340b40f0300000d41c08010340c02030031580000e40c171132200c9040b900b44144d090743c80c2102c50380c3e85600a48540720014806034030200d015407650441d0320402c400c200711040d000d506d8071140104a07443c8020348000c0441b1a40b4540544003201c94041ca5081c99404108014405022008107589403409442140a00b08a1030640c185002c21200d03c1000602c01130020082441280c5c003a90800c00000d004203000100101c1c82607002e401c8051668a0200c5108401005001213041000b030b50300625001c08240007410811024420006a50b49044200f01c4000244c66891211038048020440422007121515 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 590956088 1250 590954838 590954849
    0x80607080c071103032107080f061302041e180902090c0d02091005030601030b0d0b04120908030414040c0c02240c2b09081009020d0203061906050d02030601 69
    0x11a00d4607003e150041040c010500035603014400807900e024900031000c05142c000540c080c4806082d00c0e58201140c100a08032414400c80145401240c50b500705601a0020304e409444018181905c8280c92902e070900b168030f813800c1c122800c4080c000d110f644c201c6420300b6214002c0400c00e094040c1d01040036508010010300e041c902c04244001420b490f6011a040e00c00014100644000d002030301905940080c2c072038034000b9203000030084050030900440c20500f07802c0529a00c655803956281070101014081080401c0521003001840c2c03182040540701400725488034040c101e8494041c003086034041d225840400c5160303c0310f40c01503140c80c000300c07801090f40d030903400c003008a00b002172003684103140d06445144140c640c1e0014200141441d0781d9090302500791214401540030085958020074092821107410140fa203211840807035000300405440036100d03000c07000d01c640010b4200030048500c1136400d004440010103001040c81801c0241c0400ca81c103000380130f5039401003540d0340d034140600d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 590957338 1250 590956088 590956111
    0x319020901050d1d1207030203070b151c1205091e04181b060e0618130515030c0406060c200301020f0c060c090f0d02041e0605010908060708 62
    0xc18a80d900c24011129400c00c1000203022899070340d07007440003d090102c0496403500490f10b151807007940b902c1c00c0f1038421b074140d40114202059600d03481042e800150002c072000b03000c0f01072141c064841d000d54251f10036608010550030a00d41c10000c400c910b8003100d032800c01204022080700781e0340c2c980c403284a20b01c0211500c3c1e1522003810114005104514120141603c40c0780920100304141d1480300ba01c3d1030328002c08048540e00d080640340700404000340c80e4850f01c28810543c084070600180300e92140002d00d00c01d0001d69584000c81100c0e030507135038110391441c085172001d20390a04100c8510b000406440800010b4541540202810440c002c0102920030034085840c243e000c2d01c4003c101c24a0040007199919061040e034405030744842100c1c01c81d0300900e13000a601c050194180c4078000c0016044140c1802d507001004182400d403802207070f015039110401c07040e1a040c0054610f681051020005544e402d04001628030700080c0d1000549902c41000c0040c003c0e07000f4002034000241004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 590958588 1250 590957338 590957347
    0x604051506010c030c030917010204060905090411060a121d1c05040b090a1e0501090902120a02030703090c03110f03070807060c1707030801210f030e030f0601031109010b031902 78
    0xb007c8500002980c00702d10750742c0090082c004404019030040c011905240c403111509541c80007070004200c02114094001e000560180355203040500081407a00d20358900001c0c06070000000b0700c2164402203400082d0714960041100004080003980901c40750303020601b00295150500824510075806200785e09200480c0409041e25011440c0000d001d49501680b1548415140c100c1c59036800d10039940010084100003c0d201c9841c42110340e00f0224040c11455680e030341810700061360004d058a400c00d03a03620341100118070005c101d1800740d8422040554816015001c00032040d001c100200d1107504140b400b04444000000c0c1c100c00c0ba0660b06003005048164104407804010a4403201341000c400038a400406d031b407101001d4186d030721012110203011032240d440c105564449100800300080c100d50100468018210302050b8a4014100c40c100c10480082505104080c3e100722084075850780c0030402c1e850540106405000b85029103415481c0080c1c8614080360700701c02c01000c070b990005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 590959838 1250 590958588 590958593
    0x2090a020c1c031104090c17070509011b0b040501092a0312140703050c01060b04030809150c19060c03090b04030e010306090608030711120c040209031606020604051506010c030c 78
    0x13003001d01c02c0d0400740321898417a03958050602c0680b034680107080000d1040d46000030310b40b0502801501030181c17955094100801c50b0f0041d07540320b0071b900d07801c105003003114039081c0040c510320785c11031003a03200e04004214032030185889000710050079058600014000480b444490750740c6800303411130350003130390320308082c00710480c1501e8480d03058107201c1d402c100000343c281c1810341010007006007448220080141b1170352a2010a10f90280e400001c2c02c0c2c8100304511042c5207084004482615100b0740481d00d0014003500c043d00d00700b03d030400030f000440048242c20078040588200c2e03142910328241801190340e0341e0744400000b50000c00003401c0c4240b140e041072241e4801c0c0c0c48980648201d0380e00f00041d0762606240d50b90303604440412600c0c0b241c00d503822902401e00d004c0104181c040b140090000030404010803001c1e4201c01c080c60342622880c8060503040c2007801c441d8004261070780203071030706080a0408904000805400c0860420313000e052001d545d0380314441f82c1c004c50300b51809040202162 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 590961088 1250 590959838 590959841
    0x60907140d02060c0109140f031e09040f06121514040b070c0c090501051f0e04090203030f0708041707031212140103030e0a0f051521040605010302090a020c1c03 71
    0x48143d440351b00e448650030400400c00d001a80b0142101d0032030321403000c81500c41e0b42d01d200e025001411990845861400010490050011104d005001040c0c140900d00c0c041c04841d450303400031000c850b812140405024504140d00c00000f60001c080c424402c00240800ea441030240c00123020452000004820902c00d4850002c00c9610110460784070b503036001850040c050a00425203e04c443c02010f401c141e000352810302c0e1010550f142c40c2e100041e0402040010322036050103a03054041001700100c6101200010028507211300b40d0152070300d040c4401c090b9129015036007400c141e40900030500100c0d04c0c2e041018824071592600450a0812010040103800c41a050f00d204c0320300440040304041e0040401482c5d640251a020401d03641d40f006810007030300600c100c9412070402d0014924400340440141400380d1600e03031003420245500c07121031744c039081100d069030301c684e50381d00520840c035220400c5030301b08060f084150b00344220503580c03e4880080b03802140b07408030f00036030307010100e4003e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 590962338 1250 590961088 590961097
    0x90203011a0c0a0b090a03030b01050a17070e0d0506090609030705071206060506030711010f33170105040317040b060409020a0902040608063a0602120c0705060907140d0206 76
    0xc142c1c586030381417602041d5910100540c0c11000300c1d081c03084541403948164203980c4100e1700303641e2b501e02c9505059061003031080080c1022041055030824552591503180050806501c6a4020000342c50300203109414035002034501c00a541040001c01c001ca4000122841510541c034810016115646059002010268000c41c0c0008011017003001490b000661150380350f940200a0103012000076500c011a00320248244042d0030802c100ea0962041803004070b640050001d03034011180d1210340d00b6002c0c51014494900c144e4444c4c0c10041010f034469800c02441031403940000250400741e5580364111801018140155642d107509800d55480010303190003403040010465a0700d4440c0e80042004008882007401860354100e500c1200340c1107951485034003400003809520002d62402030310459000007080d03078120303024031110710007048502410340124402200c850b50b60130f043c41d002e0b043c600020018502030b0424201003007411440072030310031481e104568021980e4031034400103090b07005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 590963588 1250 590962338 590962343
    0xf080d0e031606020102030a0c030204120803060303070c0f1805010303140903010b04020414150414060703030204050301060f091a0a150c0506071808010204050d0807030e12030301060306090203011a0c0a 89
    0x2c2c0c2c010024046030107500940c000c2c00c54800502001d1142c0f00b00b64143c1c80ba5108061142041c1c44103007001c540180c02031a000500101a80d10f012100c2e201c0840c0d00741181c100e0b22107d08011400c000201080750703050300c1501c2805051001e0741c51618090712455203540c2c80003862800240310b5006540a40c00304641d4a0002d00442d00c807a2105030343c03140190710912443c01004e524108024210201c1d0680d01281c12510703244140780540780920429811401045050503001d101c04a9079540c01e016a201905100181d0b03907900d071a00030400c00351203910a0690303080300050f59115598850b01b0380035040e6901540b440911966075031081f41c9200c0305140251450085c1400d1040d050f0f0301c040501050220f502d416045140c492400c2030803032007184500c69001c0c0080c1207941c0054060f001034003e442c003d05041e110007410b5804030300c0c00c405003070394903407603410000060000d0394061040002400480398118290741c100909001c0e865850038100100700408240c1c07515078a01000692442c69 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 590964838 1250 590963588 590963623
    0xc0d0501021806090901090c0c0b070206070806061603111002130f0b0301080a02041d0118031b0201050304141911040506150d050a0e030a05130f080d0e03 68
    0x141001030003034201d682d007241c0741c5580e030440742d0b014604942070f91590f2200400d54813180e4039103000540208507803c007071003d1011000c140700c0410321015400b0b1258949401610081c503100c43c006181c203c0041440384100317002c4c0301c800d0900d2000750903043c07242e502d400c040034205245100e59107041c204070310150580d4000202e00c441080c4460340c0350202c5490050554186441c2c81030b04c04280408d0080e401c02c2c0c0e200108100241c035154102d002d000a040419000d4801c40b00c00c13241c01c1d281c84041e00c0d50104c440c00f4540c0b00301036020859104129a85003e80b05044147c0e0000b40144405040076101c442128507000ea298002d008500d8a1500a07031204a22640752400101d801e0000f901d480c441d0345440000352035818140c0051f1604031011618034644034104100c0402002e0141c1040c40143e5a40e900d0300160608200401c100c0038940c903010740b5203080010415400f00103400c400e20160101c041001105000148011015048e0510501407440300011030300c3c19903000c240700c1e40075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 590966088 1250 590964838 590964859
    0xc040905070e0108030421030c020603070c0c0509060d03180e18011a0f04091716230613060b1c120e0f100302040e010f060914210c 58
    0x300024040700321500e60680e42401e80e600c04149840b401944a44203100040301003202c100004e00d070f14010101d1007401d00f90628800340d0081441c54004403031420105800c4010a0103100483c80d580e002001c00700e60f82e0485107130403804201c1c18610400001c0c140180914180c107004242c109000107481484501c20701c40c50300b080c0c0603070f0304101029100b07215440c102001260602c29104501c1c0344201074130061510fa022810701c4003d00b2480030682d40c107142200541c01c481748000042c14461502e8007606500031a41c1443c2c0e0100c100e016691030394102d031041d2040c480c500400c900341e1009005c40d0781500c03c4d00c03905246d03010b8030300440f81e158490000000721300c25101d580314884405004180c00114113103030307007000d80740c008a00b4811980b00b403a280e0740d0342081c500801021008105881d026080c00d44e03861180b4151031080c1c01254400d241700c5028008903501296407002446c80b02c82c0403011614080115000402200e00c1c80d01540740c80c0304101010340100170101c0e4900c4090010704a2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 590967338 1250 590966088 590966093
    0x40f090e3a050c2e053706061e0513090e03040f0603050703060e060d02091509092103190c030b0607150605010908100507090f140a0b120f090c0409 65
    0x6502c820808412918900141e0300c420b444e8603c1101d10808100c1c407403600311000c060904000e150301c03481c541085030885800c948902424062000100326031b48541214a4150601103044c11203c2140300c00c000051208a0002d082481d0320011136235944400291058400d82560a503c16504058543c4219485c0064195415402540300da0741e540da0411420381c99440400d10074200b603980641c4910400d108001525100d08115003020f04181c501d44081200c2d00441c3c68407204464040998021111038141c01280d1402c000200d070030346000a00e0340c40c10900a00c0e840c03107041c1e03000e03030b125507602910044180298060000c6540003401d4a4590b0710f1490620001d580f0100d02c280741c0ca040c0390b80021994011100c010035100200044c100710450140060b000740401841a01000501440002c2d940030035241c8a018081802106002d01420411701c4000343c260f03400540782c0c0204016035642144d0705200b454000c0d400840c00d403003545600c40400e01e4050398484040e03100e403518211104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 590968588 1250 590967338 590967373
    0x150a09230102090a030308100f060c020103050a1b05070516052b0c030b39070c0b0a080f07020303010f030822080f0c0405040302030a0c08040f090e3a050c 68
    0x11541e0a117018050103920340c027016165030003500c600c4020521010b103c0e0015030190300050f0384039242100c00200300e002c40329400d9140c4000d41c8500082800000c4910a2103014000034105400383d40c046c104581c9804c1c0411800f041d4a1040b45101c60402d044080d5103c1200d407218a040e0040c0c500445640c4034280705288140580301238034052000b080e00c03100c41e4558108546561410000320040081d0341011240a070b22102c803c40e61004620300101c0c80360303240c0001d45000c100d5030381d03090301c24038040c8208920506c0c050081419075000340010800003031a54402000d0f01c1c1c0c02601140c90320600031108038190710303501e0640d4039580c1c00c040115200500203986a900321008007104c00703400011040c881181e134151070180c0140c008000402e200b9025203986407219202e0145c044c42c00303540304421503104255401c405401a12000a862502c00402200ca8003940500011110803482c0d400140303058501c0c520b103031004c4040a54a401d20340100265030001c21a40300f03460844500610b0740300e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 590969838 1250 590968588 590968591
    0xf0d050904150b03130215040801050402120609070b0a02030c07060201020d0f050402060306101101090501060905090c0a030b071110020705060106110712080714150a09230102090a030308 82
    0x9000750318202940e1090104140908202c1c1e0702c0000705407450316415110805401300000c10398210403203040121500100d00c0003440240300031030000030982054410842c241403082c0c0b084000c2d91101d014444050008900c00080303038001c4521039514400c405043e411070050810722260350107483c500050300d80d019001403c1e01c0310b07691800c220b14255505002c0803a24152400b035040300050000a034182000141421a520607040031044400041c0344242911041103007190103946444003001181d28030f028894000e0160800f800212202c0300c0820803074002888042e001d0400d000100f00668003ca100c4c0c0d488001e00401e85500c4031200074100b029500c00e01c2c1c122500d100701000000d55522401008001c01f42c240040e01c9a2850301d00407211003c0c030594151001603040004100007000580d40d0030502c0340e10009403020009810722604011002001c02d0f240354100b610701c0c4009158240c3c101d0345040142c01030240c0c800b03510b006a00902410000c680c008851000c0031040c150000e02c0c40703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 590971088 1250 590969838 590969857
    0x140310050409140f030c0307060b010311040b0705070e010b030a092a030c0e0c04060c03121b0906050a050427020c060f060102010c0e060d0b060d020d18051e0f0d05 72
    0x8540c9280902c108a659106c0d420304000950402d1090701c0010301c4c6030308246c80c5000c05142c0403450444117400d4450550065004e412604000501760082050901540c0300038200300362441c141d50301d080d451442c00e11000f4010210259100c0d400410014200d92803003011041c0b070362003101c8814055030702e40c02031a18001907071900d21800c000145000b021001621403050044e8003418a894400b060300c540102a104800707111070f5005841c110304d0ba6204900c04000e18407500441026074642c06030544031a0b03048002000b204102c03c40b0400e8115007103808a030180c09841300700c04000c4482007864095007004408150001820000003417000580500500440380d140160392100001682200c00310850040801c0104d80b4064091070948080c0c008043c3c420b00224000b00c681000940903405201400c0742c05c0d82c0840c1545000e9124490400c000c440c5001c1140000d0841e02c0755036603008490b1191050114040300844c0c85041440201c141040081c202d60058900c0b490180c00c0350000e20300c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 590972338 1250 590971088 590971093
    0x90109051009020f03010c0903031101140a060303030b0406290405030a030201020c060f0f01060e0d0606080d020712020904020904021f1e0804030915180b04030b1614031005040914 79
    0x1c2589514041c03044150214052301e914088500e113640030b550703000381d10450705d4031035581ea18003003501000c590600c0d11460000100041d11030441c5006400c03143c0c000318040c001c610b8a9028030290361404111019410318460300641e510340762265000c64031503608515014011001d03240c00f010740540140c02c000300c1000540303001d03545103c00107901c0d40046451480d01916400104074143c001c4030745071a8500003418101d14081c043d1a100d0a441c03040d8400300b41c540c01310450700840c03075060240306e0203030002c2c4031800b01031000c130f400082281c0800341c0040c0c800d100d4032010a04541d2650320075081a07a800a48032818650141e0280402c41e0b0880b04c10300c801810108200e81e0392203042560703c04c6d43e0544030182280d00300482e0300241e41c0c950001f5810710505101c107481031000803030280e000b4103404402607561421131400c500c1904000d000c904402e81c50740d60507800185c000580c00007a1550941d0580c480d91a080c0c2d9414031032050380616000343c078000c1140c0500a01e02c02d81e820154102c001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 590973588 1250 590972338 590972359
    0xd020f070507051516030e030303190c0309050309040510050901120215030f2707080f010b0609090f0402060412080c010533041401080a03120c1709010905100902 71
    0x184800610140048042c00104100001c2174404144103201e0079070203440c241c19068040404249158010344011b0b240512806012862088600a40500418034035007405880102c0d0345030b0340c1d64001d1480c2c2512458641300020010187c0018000052000034184042965078001c001080d2080355410f80c010406010751120303503020f44040702d006405070030701094a56541010b1880d604440380c0344a18000340031081402c90a0308002800240c140b40c0c0c06000254270b2611441d00b103d0048282d2401101d051201100940d500380b211130303012100e030440080079521f0744000341841c49642c005000c5030100030100d40502c0b51490152840803114002007105854200c40e100c81090034045160513240001c40101c640c501038407480d00c0c805000303000443c600011207202310462200b6041701915600140492081c5544081c0c01c1c1810448414100160342030f95000429100001c1c000c40c041c82070501c08201c101009510a800c0c0c80e40140998044640100f43c0d64054030241100342e1082c540100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 590974838 1250 590973588 590973599
    0x11803031d06181207170913050c04092316020a150207050c09010b0f16050712051c08011215090501020a140301210f05060c090406090b010c170d020f070507 69
    0x282220155a000031b45468513144814406601c2d500c4909070b079400044095903004000c25501459001e85040f0920350b45980c24a102d03101240c00c00c031040c1070711a0304811428010740c403c400c055001481d082005d000d541e0780000603032400d94030400090005801c007030140700d440e102d40d000d0440644280d054600c50036446081000c44082070003a10710b0b49800b00900e40440070800001c01000d0003a80d2035a05248542e154a418060550b1182e10400c03020f41d1134100f004000d014003640d558250b60381c4501c0103005034004240180501030300c5410045500c50307000b4030000e003080d40b08a480800341445490f01924045010350805002c08000c03500c861030b151512100352040d80d040e5100c6401c41c2c1001c0019003649940c1c0c1d0440340c17081e50410380c2c103040c54000c524140b101c1845580380488080c0c1d07c0c0c103201c040c0000c84465034042030036a458800801c4081c0e900005080303e09422601002403000d280352036215034450b90b020078503580c0c80058107840101c101005846420300520a44406a5454 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 590976088 1250 590974838 590974873
    0x31805192001270f03140f03030f01210b0a0e07050d03020a02090c0909091b1f0809032704060902041203110c040606030b040b0102011803031d0618 65
    0x100d820300d0100f548074001e030321140900b2004440c0307804590402d01d040d0b0303920359a910303480700302d9042560303461850600c04035400e000300000c1d010342030900c00944c85c600d4000718141d6110018003540c00b9a40c0c12a24011a0f00f1801c19450740480c0c029088114500381802c9110084c0210200b00381c140c00f5500000071a4600080e840303440c00d4161f0007404a06040f0b81c00c10000d0f510003041c1c44030050040c4085030313058807500746103445440b441d030040400007924041d034035114041c681c800b88507204881a183d00e0801900c03404001002e42c0c142101380742c42e40c0d00c1182c114020300e10a001c0e0300e00e003440d18a10190111103440311202055a0030171806868500c0b0b2000e030b1040b800340046040c03420001c5070019104482d405d484c070000f5816914105c3c81c640001d400e5440340c0c0c0c001400240c55000034061031030680700300d42020000340020080055036540401030510043c401406050b943c444844007258912680d0f06484805800d40e0501c0c40e20b14a944200a03298182e00c4180c42144424003140742c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 590977338 1250 590976088 590976143
    0x60e07120e19060506120a08041802041d18030c070e0a1b2a08090910030c0506220b03010f1401120e0c1302090f0a050d020103180519 59
    0x401490b4841c50181d12107002030040034044582280c0308446034406d032041881100c2070035101d14030a641e214600b4141403840003206d002611058030400c001c0162413000b00204626005014100d03405035600c65800c04d00030745001d00c881540c000060301c4100200041101300644074482c420001544800e20050105c0d8010481e1366002c5c078407d10b401604500640d811201210b5400f4810a600c2007000c507a000b0341603a00c0304465031400454199202d2801141065000c00c40c00b9180c0521840d5845072002e040d92031207090702410000901803642082450b8203002c5c00240001c0384442e95171740320000daa13a40244108003500c2c0d044030300410000110603400060700c8050307641b4901031244806481c0180301c4640001c0041c0300b00790521240b03440c0c8254080012000d074400684440002c41030191200440f10014400c50b6101e1060110b6034426072886440c940a02e0002a41d6902020f170b0042d000b840b00010380360344656140046407036402802a82400d100f042407080c0d016200d100948150030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 590978588 1250 590977338 590977363
    0x706111b1b0409050f0a050d121a01050313060e0a060b0a081b060712030510050d020319060207080f070218090613111002070f1505040315060e07120e 66
    0x81c490031000141c80c198000d8100c2c00d0081064620014081030030f2468158a0903003240d8070340212458400d41c23070b0080d070410301000c02400240509113034941d02020214850034640d041c80804000302d00755032408103180d20740e0b07607124004000c28040c61034066920020320400716412070074420b110703c5900b41440501d0031503440074010a5204c00c080c20705030350100e005000c3c031b0304070f5028003c103000b00c2d00c030f4060803040318420340300000c0701d0504030450150403446420060060320140342100068400207244940840c860800f01c0342c80c030036881c2040291143c84000341c81c82c0d07808241240000d20100040c04114400c45501c92880000d00030181400e0007214482da03140c2001c00007881e00489000d0366500d0342c0c451061400d0b016020000507808210324100c080059104030380502c50750050800384c0000d00300944511800c9040b000e0000c1062095020003409011402c1071031078081d400b604180d0291800c0d480035083c928041500410104549052801c1142052212064507001017a011030074031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 590979838 1250 590978588 590978623
    0x1030605030d03110904020a0f0f111002031308030405070f0504050c09060903070503060c070b09030f0f0a0318031e0914041d030403030305071403010f03030e060706111b 75
    0x4001c42c802d50003019a0072040e14803950403c2001c0140d41c8a00c01014801410f4940360001190f03100d000300740300300640b810380600c0040641891001000100700c090100b81c9440540e91350350f001159100d5410000300240039950100c01e200803c4000304140042c0caa07481c2d22104c605645500300f2098071802d0f1401c15008508101c9000182046d0005102441c0041c0c1107071081507889012034540241241c00e41c00010002c01d40100300710000ca01550031003032030070056040421018a0f2005403140000d00c0360841000a0700720500c900a40181907855001c003140f0720368080a090151100d00f03800100d0004038001034503002c01c5070246190740e00b51214290280c5d00000d804043c00002e24a20603116442c0306c61000903000b5171000c20042c00607600c640d50103c0e03941012840584440c03010301199100000520060000842e848400003c0366010316003c21441c560401144542c481c148010f088141005804070348094444010119001d800a11034643e00303010301080c0c0ca803c400c01b87c0d0100c06 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 590981088 1250 590979838 590979853
    0x160e060105090d0510050916030507140a03150b0a060302030403080a0e0114090a03021c05030403140c10060e0705042402120d1406010905060703031d031303020307050103060503 78
    0xd510680c0506005200504100420708a60315242d103030030510000300d0341444e1243c04001c941c040500c041e50b404820742003116080342c01d59943e10b403100042d01502003820741c114642c1c102036071141298402541c10600400d401029401a540a88036921a8900500e404030001034418805e20071203100e036816a60750701e05600c40c0c0d28000041d01030b4400304c015542d00d0740c10451503030b01d034807444070701821031440240140441498040d0900b070740346014400700c1680d00c4101c030459400404a9a029505161145e604000f045094599000d008284162403044001c154103c0d0350b15803083c0b064070324801c080b0845966a800132211489140150503052104200500c0b03102110bc00384400384919006442c204400301503c1c50b070741e4204622101c001c0e03450340c0005410720b0000c0c05058210070203180c100c0009040402088292141c00402402c05550f440c006c1d11914041c20f0400c0c4a00900082c1ca5650030b903031000c0344141d401404140c1c030074001c10100054541c002c0c4101070480740090046d0100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 590982338 1250 590981088 590981101
    0x42f01030e07090c05120604060b0d05040f14060703051612020d0b15070605060303120c090325140a08070302010f2106090c080402060301090902130603050609160e 72
    0xd040700c0300e640c40040c0b003004400704000705540107004a00600b940d505489003c0c041344548000800f82c0034030300551500d241440405100d60440b40c030045101400b0480f40c07110f00d0005100d5105400182103a1103c410701100104042410b45c014100c1d50303004e104d01d448107549400c61000c10808007000c0ba441c0700c1c80b01040b00c0b40d5009040c61b11042500002c3c001e800d0360105202200400240241c1d42001a4074420002d0304d1007540e03007004c4e0a400035030410135843c07150003103074001800d4840b0302900820801c03a1560100213000c1901582200a05480e84400c00c500c48520607004a00c1245000740984c4440d00b0900c0241080f00c2640005180c040d280d500152048210f081030302c0200700103400c2c112111700484810380c450742040080010241c1c41d21741414201d81000848030308020b039120038030002d6034074901076a040da41000400030303c03001d40e840003c0c003001141041c511460305140e0000300384a800304006100e65044001e80303e24401e070390b00100301c44109014200a460f41280441c1c417 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 590983588 1250 590982338 590982341
    0x3051501140d0c02011508030c1b040914010e070501020133150207240c150f0510030c0f06050a0f0302040815061009050d0f020423042f0103 62
    0xa0300c0c1210001c0380c0c90a5a030001d46001d4511034150800541e442d03044881118800000702c0d0014001c1401560a10706059007003911080000c10b4900701011443c9100515a0749905c0100c22960040d1161103070310103415860b01800791001080c03064000c0800005855006000c0d0250044044d080850142ca40000000d1051201c408240b40211880e4000c1460703862241184600690754004001081c90034901da02440d440c00e0501407841d12034403003800b04a4009a014080503440040c06200040001c07e94008003000784064850b5801d01043c017075101c4d1021210010303a8011040507088a44803122101c0f1019180324001c0000c90800c1a09030182c803da0710804d0f44011454054a0180e6a920071071510403041c40c0840101c052800b40211403400581c00d42d40c41c0480d0401800c0c80c1d1820000500c41d04410174007070400c03d29140001c0465480c0e501140f00d1205882c0c0240b5490340e007198400490804450484441804020303800810b515102240c0481456041c00848a408d2800440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 590984838 1250 590983588 590983607
    0x220b15040e2d0f030d0c14070228031b0605040503190204060e04030201020a020705120709050a0f022a01050f040f0c17010209040609060305070302060f040b03070f0f03051501 77
    0x2100300c00c60724078501840100f4400280303110000c03801152035070386010606040715040c0b00005d040c40025204104256103205c2641c075070540486840e02c0d11000c0e811040c003150749215511404521100000c0200481100c03074068800300b6241412031703151103140070b654910442c02255459880701d0b25024060348002c2d4030b1190244003600125034180e4a4500c042d203000e09a80450150350007180701c0348142c0e410400c010007041d0441d00c000c21a9402001c09031074098901510810720780f02c10004d008110305802411700700031552401c40d61420982214120601c080d10000b11040403407104080c07008050081c540200c5104070902c61944903aa507292a4842c003120466100c5c101c040001102400707000c461441418020025030f480e211031040000300c2e190781c2c1121500519101061021540000745039080c1c96054400d10b648020959001c4e42c43c0c01198410181707890008208022140e0016001c0840344254440d800d20451107107054094a81c21104103151850320389901c005588182c100e80e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 590986088 1250 590984838 590984893
    0x10e0601120f06090203010207060c12050709051908030d09170430060c0203180a0f170715050406030507050c060c09040e030711010f18050603220b15040e 68
    0x5468400745d4082401ea800000098800b50765541000302d40c6070304424400e1420384032441c1000b4628082e0170150000d40302e4000c442c000c4200c40c1c0d1581c1c206684201220151601000300c9807103440a821071005000113900489031a407075440550311a496401c180c606980c1e241008100103135000151461110340182c1140d010310544924030003041c1d0034810070560700010ba005d9a41c0d1b0010702c400c04225030040031001c0c01180003881c200a8490000803c00c2945e080d407814900d00c1c100304411510301003950300004640c4046003000c1120786e81040040c000c8030220348080c8460340d5095816200c5000700b403000b00da035030440400078200c01d441200070841814010800107590310110010380c510b81001100300e134080881118588d41e0742c4c1211501d44204c04600e003c1d80c082a4a040d0300b10031281c1c41c8038440c007131a00030001c50311442c03603090300280300f00d1012411038401842c3e00b0303c04003d40c01610907460948030f4048002282c141401842c1c150021000104910800a1102200500001c0d0701e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 590987338 1250 590986088 590986091
    0x3160f020109030b0a1b02070b0d1d032b02070203030d05060301021e040e0c3112030f030605030d0c030507020d0209160e040b1509010314070c0302010e0601120f06 72
    0x4000103a004c1e10180c00381d0b08501000500000300907180318a48400d280300d40a40d800840204a18400070045034881031540002241c1030110b50364802003100d184410507a00d00002ca41b0351286440c095014604010f0328001841501c0c1500381c0707000305d06c00c4510194164100b00011030b808000c603000590090304c003a000510b00303d4501d20030f0114010550103008070200c002010408400140c10450704002c1441c02c0c54a41030b001065666200e500480c1c02c4500c0060031800e0744110100742c2c002000b0024062100d212040600d00100803864040d00c04002c01c1c035100002c40d0900740003c04010384041925070318000415600c040da500c5c0c202d010226030218112000c0e00c0180c5803c0703d450300402d20003000281c4042180307000ba01c1c1d1140308003410b000b03a00c0c021499515076542c15545000203850b001d401d580b4581040100d020304040f050280302d41100d0000c1c00001540048880388031800b96008000c8100c0d0701907066104e150078411027a558203510442000306010005c0385801c648190360 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 590988588 1250 590987338 590987357
    0x4021905060d0e060a02160f05030f0d060608132f03070b0909070e0303031b1908010f0e0405060c0a09170303040c0905090a030f030207020405010311011103160f0201 73
    0x10920307404144280702c041c0d218848100548000c00c4201d4101c4003c0c0c0040d0b040c10b14007449448034241260024010a0b07603800042c0034448240200d07101c4002c0d080949503135010b03c28a040181400d80300709030000340c0b01e00015000c051055401c0000c0c9500c207040790b00001d10301160b468041e48043d02c880500031000100c0209a030300f0824140105032010140d40c980b00b04104000c098100200403000741b0940c0c64140c0002d0f900841143d27031100001040e4582c0030072010307501089000720411201c0301c1694200700280580c100c40c03518101c1e0320380e0900001c03080e241d50110000c0442034030300800f6030b400080400e10701640807000e4812200c00f45401c0e501255204075100d8207111145040340306800001c02c1c401401410790002016044440092046041c0a001141d54490f0010003a0800007441c03c5110498482e804689a10790014070902840d40c6900b801d05a008000d0010341c003160100f0401d15580030048151503401e5501c3c480c0307420174006500c0b07001d10aa0548000ca04000d440310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 590989838 1250 590988588 590988599
    0x312220f030c0522050c0708070f0b0a090305041a16060f0f0c0f080c040807060e040c030b012a06060e060f0303131701020d23070314040219 62
    0x1420a00815880d5140c1805500e541801d00b0550855044079014100f003102005004d0449011100105840c4800040d1544d0364100900350340510780f401400c02c0303000101c400c01d00403602c2d107440d500c5000e4203c14a1545800c941c480840342c06840050104400313020800800b034080075010181c2440c1d4880071318143c01312123268080c440a40b001c544841d520014806c0914480c4652000ca120f0407404014001803c80090500f6040040e4402004200400079055400520640c1c006200020807038040079121070b800b030b000c1d200211040340074030b140a0040c1101351090203100107110040e100c81081000400c04480c60407010740400c20320200c20281400041d10600c684402801c41940001140c01c01c0000c20200004811800384a5030080c0a003046241c0210101c000b03d0302c1ca8031002d400b0140c10044c42d800380c0100043d003e8540c0c82c0001e016502038411903402d05070340401308510002d981e41442a82143c151103818914101044005801803d0080d900a80d100300012801d6001e42d80b003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 590991088 1250 590989838 590989897
    0x1060e0609060d0e07031a06060f0901020109060c172d070201020903191101021216050a170702090c0408060a0f09050a1103010c08060607020f06160305120c090312 72
    0xb152010358517481000c1c20410300207032010b0124803402c404521000b500346000050041e01541401c0c51110000041c41501a07000358412064141c1c0702100344520068501d019100e2002103003904050380e140f00005130501c401d9542003004400d003d9864042d0101c814250f4503402005044a081d59401c03c01c141255030204490120221460b402c448000381916000740e00d107940034541415035000214200426040100390388080c2c030245030341c1c4030201d000d00300075203052441007001c1c1041140600242c0f800201c07000034809240290741c030058984400c4a1490188110710802c1d14a410020114810609681059510188003200410350041d5629860f00b0900c0b15442120044c6994049208030b0a00307018000d4480304a0a04c505c081c9080004100d0522030600c000748240c0422441c640b165650310241c80054803580c1080041e40100e10700508680e0145a415180c00a1500018154440d20301154811100039015250400c1c180d414001240c203c01101c6000d00340d44220034403d45900c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 590992338 1250 590991088 590991101
    0x702010507183804080a0c0503010b03071a160506010f0501110d0c0303090b0f07030c0e0a1701060305030a08061801051825050304120305010608130618080c120301060e0609060d 78
    0x9080074140e521ba1616240f41b4034080c80c0e010500076410080120040d640204450b4101d4401d4a00241031076030590802c44a8400c1d08510303640002d0582000051020001d0f40070706840c03499043c2400e80d0340341c070019102209c5a030343c00c40b2254401c1185200d014845c0014042d011b1280c200841e4240440c3d40d000c00080c411650348070307121510802c00c008960303d80034009910b403041c2420001d0002101c003180b4140c40a0140c0022044c825802102c5058250b11440045401100b62511180890001414500305451651280010701c1654910b0541e00e0040c0341240c0d4020003c501c0c1e08401280614001402021003c04c0c240d082d0744480300d0350005039030120b83e50780c594541d940d0340351600d40050b0756900340031f050303040600c3d00c030043c465140c1200c0d606400c001d2404059100e100f0600d0000c014020306180c9a010480c500034a004119410380680450342000003580c01c844032061512119000c248944c0300058200400d55a4030300340480149113034a0040c000745c0c5040120014282074900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 590993588 1250 590992338 590992349
    0x5070206070305070b0c1804021b010507080414150a05060103140109061d01030c030b0408040504110901021e03030c0f21041208040206030601030b03150702010507183804 75
    0x9000841c1300410100107092644483d0f07441d052410590206201088401d00e411614056540010441030405500c4a044140002e58000340002c0c80d0080000b0004071090341d040b00d0104400581d000e0752103000c60118540703c2c0031203540881c1e5464483c5040a010050145810703d907550803c034070090b007280801d03400303811040c40c0030403901d1820701c150b84950b144410701d11030740c101d0b44014030000e90384001680469030004600c0005031a10b0629001503c21a0700c1190300c00d00d0200c56100100c1d441010300040d0034240c00303440c01d0b4060003082e0205601d8205100300c0039003041001030100d51100014000f410440325000e420119181b0f09020007403030075154511b5a6009004106c200411f040281012070041e1401e450381e801c1c01d50109000d40000f8010307078181500c600c3c0119480c1c80030080c40d400c1101e012a20130017410000380c0a4000c180a440c40b50000f40800d00d61889610b40340c2d0444212511048200d1443e0501c4404a1010921701f0740801c40d41c0840c1511341400d000301c00030304080c10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 590994838 1250 590993588 590993597
    0x6181509270a05060403080c040902070b15010e0307051c1505100b0a020c0f04090501020a120c210906060b0d0e0610060c0f2901030507140d12050702060703 69
    0x1c51405911054900e1200520800d90040c241c07a00001c40100e0f5540e081503050401113042e45a0b650941ea45010b282c12490300c1520104680051044031342c402c40c043c101c1400b130703180205026801121030390150162140c16034001c290070845418104005141c4860603209038030020003554400401083d45460800ea05850304184100b036000300300400018030b0258049440c103908500040e480d042401401480391440c400d107181c10362134942045000e103038000001c541d201840c40020f880d0000515400c1501490070b504011318a020311600040ca100941d620100f080c3e118035064064961954119101c588130b810025005100c031000c1c1c42495551800810403c0072280c0c2c00e4505000184042c40c60b55501c40d007003104a410038110070501d9000781c0820400c1e5100c3c02e202e040030f03640790044100001d6141c0380c090840381026119040c0c03031094083c0e41c001e0350340e0781c0040c0c180d410b00b5a00360380c44035000c10000006841c1103083c0c540103905c4c0c2012401e14115030000307012500004c0d41603022a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 590996088 1250 590994838 590994871
    0x6010e13020a021e03070c15020111160c090506060702040b040f0c0c060f0b090601050919090b120a080909070e0306180c040515100e040203040c051806181509 70
    0x9103456540400040284401541860601e80b030307c11110110784518803841e00043c1c01a54158800c0d00f2000308440c10030b440c1a42d400b18032120010340500c441083d140d800141c1004108860140541d03801850010042818803515800701700041c081c0d03001c81d40d4000d03500c00c102103001e00280038003d219251070325100002c2056007052019107601c003011000091034a21001d18955486034170641244080c44c000d070b1140700078008100784c401c0c000c00c011800c40e051103000800c00c0b11600314041f10078007580c0754009240d20b42e96907a9290010b207002803a00b80305000341d012900703004143d2507220b41103181c800c01070311160021900b800c0302603990310a07542a03540c7e402507510040104a00300e00043c0ca0402c154680f201d0311004070404002d980e8800c2e060100300c03600d034501c606840100490003c00840d503d080a240007441c0034180e03c01c09000e075008160341d125400c29007040c28490f078800781c0818403082e6000448580410024850080c50000340d071280b400c0c1e200c00040c02c2c4a00b29609054460 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 590997338 1250 590996088 590996113
    0x180a0e270a03230a02150703020c010501090b031605060a0c080d11070605011e051e12030703030b0607030801050913060f06080c030f1b030a02120106060305070e0906010e13020a02 79
    0x40e40e41c01e000310f07124200100089804035600007080d880e071100740300d03c00300192181c1004034082e200d90084c51810350700304000030412820a6109881c103650443c115101151840500c0c00780404500c20307541e202d1030611401c0c0e41035004c0c42d85900c85c103204840c21442c1c4090044c0d49002c80708000560b01d000903002c070380081080000c0c440d10740505016254140b800c00303201644601410607000b850f01600851040c5001c5c1100d1299010a4810042c2010700c10f100e01c1020640c0c0b41c120220942c00607080182244503418a01c040f60391003074056803100704e07a03800c050600101d014043c12159003d40e00416000201c0c649205202c800e000151021400c24036001900e46003603070002d55284250801480303903501c98400a03030001d4200001c64040c00e060513440000c2d090030000d80c3c020303400580070441d45c040c015040d4825816103209440400441e04c524504481c50b2a00400c11904406c1034004144998090b603034000590000806000080300003200003000e0360030440314080946d02c00d401115030b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 590998588 1250 590997338 590997377
    0x70b040303061a09091906120b1632040b16020a0501020304060e041505060406051903020a09050118210b0a050c03010e040804050402030c180a0e270a03 67
    0x800c1103a1860f0900b01400c1000146800c2c6021b4031000e00c3c1041d020702a5078000c183e4100703030000c1028501000c02d4400e24104090001401c441811241e41441d150000540c064544d0001c040780340d40c20300c0201c076000a000703c00c450701c2c02446500150140800207802c3d0708940140031500d503401c034180701c002952051220303180c80343d00003c1c10b541003480300307200080d480b000d4407041d10703000c540120f40140e44034214461495580c00c6290800000200414000e401000503c3c0c0f05650b55040614007440d65012012400380040d1741000440782d1030200a10341c800d00e5100b1481301032503050750707030a580c1c4c68201558070030014680c800e00400700c007084140040e24100c2540710302c201c803051055203004890711f1050301c0140583c0b050850b034000454240803c61090300d01600f0054401c66403414800f040150075002880015102013421210f8030a5080042d6004110b03a121008006162034103000440342019092581050074064050012440700c100a0705611901945840c00426904600c42c0b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 590999838 1250 590998588 590998619
    0xc0e0a06090b03060c0a03090218070302121302060a2601090c02160b07021c1a241e010e0a03110306070912020d02010309020603040501051503150a11070b04030306 72
    0x14031135003104081211030343c40750b011142e14440e14940000c98140d0b510001d940304000e1987c00c58802c01c4081000802d940581c0142507681c4242003034030480da21070000403c00041c5070b100940000f030a01c4140c83d802d01424032a103544448030344490002260007184842c41c41c00341d202c4403a5649500e48402c5040d0148540f181c40c403041030143c400f02c6e04201410b051803181034402400b6000c3c0c035000000d000250004003400950091640404044040c100307008100142c5541c10007550f004400c00d0f480194000c0e505d800c0602030010b4062070301e4402400e40f00c18942131118107100600c083d100c600d03a150311004020754070960051510740040401e042c03801e1300052900d000d1141d03200342070116a85540d21168942e50465501e8503107041880100e010305814100207410880c08401c0c4405c10006401141c030807010942c008003955200400c05170303610071140e104942c0c4000314000c00c400b400340d0f4002c4026010311440d454030f4090159070b03004e19020308407401e900082c0d039030b4414041c003245940644c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 591001088 1250 590999838 590999861
    0x1e0e0d0f02011103010b1308030403060504120e13050403030612060e07050f0d1106091e031c1b1b081515060313030c0c06020a110604060c0308040c0e0a0609 69
    0x2c02c03928003194210f881d10311060107080401c11000c0382c0403000c682100560400380c0106005e9a131205e6903840c00101400054030221a05001d000d03071101c42501c1600d0001c607038a402841c0101c036402c07040d545ca0041401030700940c20541c80e103501042c000c08480c509039001d482903600141070609075030b000341442095049544075000c0a07049201603560f8a2903c3c500d260014042003e212090000501c00c4c80b42c0c0221306c1c0c20031040b80580d038030350201c0c000c1e41d0800001a4152040402d00c01c605c500310307089262000000c1448080d041c8003801c0ca009402c010760b84100c1a85490310766403001c0c00015040c560003502d1550020342e444c0c400710400c040440c0c205080c8a510350000e001031700020f03800d000080176001620000d1a441090500c10002d105546070402c83d02030086442d03003002500d9003803010081d90702d02d0b60201392658505080007100d0890302242d6640002030025541140c00c1c0d28084d02c1a103540780e2042c0041240c0060620560041c1494900000c0302071411007080180e030b0020030708 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 591002338 1250 591001088 591001091
    0x60f1e05060f01140a0513030c050f0301060302150c0f120421020d06020306030a020d0b16080c0318151f050907020c01180b16140f0d031e0e0d0f0201 66
    0x1000740e0390b0450300001300702c0702054640b91586180d03241221a8021404003003880130b00041d000040c001d01c0d00b0510280e840540d034882408904c8000c0c5826680288402500300c8240c1f00c0e907000c44015039000c1c2ca590001d0005440310010a0110140351440000d05442701c0c05c4001400c00c00000d02e450700d099400d00b02c030001d08071215281c0000710610b4015001900154000000078030355501401100a81a4000d1801070712400700e081c0300601e2070040751014888409a070041c40c007280180300e500e04c01c40710381d4445490f59891520f0610002c1d550765a20300d840c4510f00f2440d200b00607203003c00d4810244900c103c1c1881001c180c143c1c5000b80c0d0340e40045e000340309013018040d44a41c085100301c00100c1c20309203241d0840301c0079402c1d90341d520a0b0740012280040071a4440e644105040385c1590785000700301200c84645850301035600c074043e803043e40ca842d40c04034260580c03c500a4000da91041b0380b61481c0444403152078a40400c1d07a107450031107035940c0c01c68002d28100d01d03000302c200b031740f01d040c140300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 591003588 1250 591002338 591002359
    0x705030f13050126060a1203080a0c02070803040b0f09060c03090913020d02040e0304080f010506090603010b0a03030f03110408100c0801080c12010905030f0c1b0105030c07060f1e0506 81
    0x22440041e880303a0119130100f414800000d00b45449280d03000d001000f0301c61003401d814005003070040ca00c800c2640c141260318189568954403c0c0f000401c0703019611060061490240b0342160040c1c9a0710110300307101e44030030600c18519030b99100340c0035000320000e010207036039288481c000b00038038080d0007004c41c038052070300b01e000c4400f40e00c90b80e13402038005e035041e50005084011540454614011a4022000741c40361006050300c040c0103402c854002c180c180c0700c60600b515000101801d0354030111105401000b198020804244900d403021074070400b906002074024803280a100f1700b80d00a40081a00303500050001014840c40d10076011103007401c2c5854841d0f0f504284d1029207034584681102e100d21805549504801e00c20740c410785850342e111040380d40d642090340c0701c0c07807030703600031501851450041044c3c8001e034014070308400040c40c00582d1390030702e1580c2d0094003803659000550300340c0f0f0b00c694504042c2012a07162199020b4086120140145840034503c40c0d002c6d16030041007980240010b10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 591004838 1250 591003588 591003617
    0x6050d0b2403061305011112042a0303090e2401120e030706061503091a0a0b0d05030306040b031917160f02090c181002030705030f130501 61
    0x34a26042410250305050041600c9080352420700c520369226814054042404035074011011320304000c911500091040c0184100518500d0240c010b07520901d12048000030b00043c9903880e50041d07041385044500150391002840c00c00c224840d0021000f286900708180501403186400c9544030100c0d00e0201b80310040d4074441000080c80d040e1950500201480350301c4003204640001901c603941c2e504a07a110807540c10320501510161003640c41c040c0c0381c03043d4606003d2107801414107054000008e4000412032410582041e140103104854140d511103c8550550311a070b07000d62907600440c0115200d0604004010480d4403258890f440b070350000308046084c104000d041880c090300320100380c1c0c031000582e60380c035800c0c811101c403010101002c036003010030003046e0703498504914001e942016040c0e481e1611041c0c0c6119441440312645800c0800000b5460712091401c1c3c01c0300b051042c0c07800e100c0945e4070030b443d541140ca0668244140030501320300500345180d03400b006050921341003032518102d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 591006088 1250 591004838 591004853
    0x2090111060405030409141005060c100e0102120601020a1a06011205041209090b011211040e0103150b0612041203110409020318010506010c060b210303070207060809031209070806130606050d 84
    0x30300c6810300882b00840d072850707800000d00007005080011101405a00305030200c0034002d5009081115442c498140070031203d51000406000c0705601c081c403e141240d00d880070608101d8002c10990400411000c00c81480f845805102d00031840340311030701c4420709484400b4213542559008004c00380c0c0740600044490780e01018444c10008562030010314035024901700e040702e12654018041c110403a0000004004c01c40c07042c180d100c0842a01004440040d00c10800c0911800512412071005c00c408034000c43d0542201c04041c0d1101c0c20b002502150b441140d040641081d81b00384005503000c030400c10740c42446201904843c166000820081c0b400e1000a40011020a0054001fa1366588100f074a81c030b0303001c00081400303d04800c11881e0403455070041d0f074a610440d849001409401d0001405601440c051030041d410a0055420310601d0032490701400070042803034145101d08200001d44080030710410f80641c4003402c1c0d0003201c440320700b4140e0540d03515500142c02031014100110100354030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 591007194 1106 591006088 591006121
    0x30c060a0504181104030b150a0f03050f0304060206011a1303080a1d01050a14040918210207030f0f05060a0e01060e090604060209011106040503040914 67
    0x110b04042082d580810b10031400304c072051100303000040d02c050304650b1000e0030685201c220a94030b0009880d140641d4000103010151241c1881400001d110150038052000c3c019850280f50000c0203560744d1051240c10000c0301811048400b08100340200d030060003503040c001c0c0c2142c1e120306010703070180e001c442d0a90101d070340740c00402010010303085c11070310014058450500300360700800f0554040c11a118030701e210110030040818046c40390301c6034030505031681001c214003095502c0d2580108201d880300a400e110440e4000102e40ea0003e81002a80c3d813013500f00c902d15001380782408c02c48100c0100140a406500200820041e141e44030007811012a0700910005a07907107181c9100400c2a16451a650442c00009000c41d04a8000b0002483d041c50001c0c02c0040c212592410640c0a440440301500002000c100803007a901a4001a424801c5e0038400d0782080068691481403 = true := by decide +kernel

theorem cover : BRFrame.Cov 590827338 591007194 := by
  have h0 := BRFrame.cov_init 590827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 590827338 ≤ n) (h2 : n < 591007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
