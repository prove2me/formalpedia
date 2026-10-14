-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0395
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:35:47.28482+00:00
-- url     : https://prove2.me/submissions/87d8dc2c-3b3b-4af4-ba23-d1e8a5efce16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 70863311 ≤ n < 71043167 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 70864561 1250 70863311 70863319
    0x50604020d11130b070c06030e150702010c020609030403080f03040303090602030c03180606010e060904060b0d061e03080307080903070c0b0d0b010206010308030402040504031106040507050f030118080a020102040302 95
    0x1030712400610694603040701c1ca503040f51141c03601c408102158404143d980c04d50307020b80c0e000c2c1c20b41d080800a40c05403d419155505d54400c0141031964144040000340c060056a00006607400c1c1441009040c118001c01d54000c90348100070400005100a040355041e05189003030343e03200d840e2413071300302c026215551001c0c3c0081e00100c2409054038402d0021406582c0901d41c0f200c1120666039815101e00c42200c0c1240414180c6d40d044901d41000d02c003d140c0010010800103029490b0b0445a00c65009400301e10345d450303955001400010649036000400d15030400303280c40c9140c619601c80f0201d11008040000704170702c800c04106174032020425151007940c07288444c8582a00c828400c0c105401c43c18500c0305c49400e015030002e0351b50000c0f5045040e030b82c00003002446d690f100e07006e000252070080d10031400c11a14034248402d0340310600c081170044d44100007078502c66142200300015521600141d52103039260009030781e48030a400c044400d4031603110090b15121840710105038024000c5500103900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 70865811 1250 70864561 70864571
    0x7172401230301090501050d110418050109051509030316050d0e19110a031e050304050306010605040306110c1f020d0609060e0a0903050f0d1e090308180d03050604020d 74
    0x70700080d00954140c03108003104003c00da90300c808200702580320841c064035107115421f02100302d0804ea0000051944420349080b4902480c1e501c040c21144005401da680750051018100c40118801207190040390320b80085066081c040740404443d180072940c0418001c002814030700e0510150088503800312003409803050100700c6241e0900c49001c0d2441150080e0414040b54003d240004400060301d400007080780d2185240c50301e0310700983c403814042d00d4500c0300380720010391950200076040c0a41f03140d660f03c4e0b4455166140c5001a600460350b90f43c8008820301000f410712200291b80000d907108104009001700400e40a18000d1050041b40b8420301d04243c03010885107080c0e04041d045510003100c01c03c4581d0341710003950407078200b0f0744010700240b4104482e80540c1c1c4004003034111211078001c00906c40c03030303c1000740b000800600104030100d40c4490b40317007003410b03080300d20310b6031011000c200f00082214043d200340d121001603641005250390748022a40315120317641900c1c0425101001001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 70867061 1250 70865811 70865867
    0x50603070b03011e05040e1f150620010c0c02130905031305120303060603060915030a030c0b0702060f0a09030509030f010b0a1d0c0307020c04110307172401 69
    0x420021013010b06041048090740003d8500b0141300b0320b51741884c0700c0043d00461402000d01c00e481c505075845410034603141d500085244081c044040008e0010b9100c00000102d1020920700b0554005c1102030641d00d444415070314146c01032900c12100d40d0454183d51003100350100100201721041c809403080c071001c06e0003119056242e071074405844084a1000c00039003640000713692480100e440640000d41400400c00909200c6003d42d0049600007107140d25107481c0011a182042400c429000138900f8100002440400603006070841c41c24409044240b502e071001401e041005003880f00c0c600d595403102018507110741f0590b080b9980003002e0711003100301d051100703000c0c142c000b05017403080442c0b400c00134103a0072041d02040f20701e242c50702402050f5241038418840d03400c020500415801361411f004450b035158418640301c21004041c2ea506d070b0030b18190041500c201030f81c200800c43c003407105000d4506407080380c20030b0030344440d00403095258042c0c1c0100c40d02034004000000603202c401c0b400f1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 70868311 1250 70867061 70867079
    0x50105101a0a0804080f0705070e0604020910080604060806091005011508061309050a031e02030901020c0d06090b01061d010518040c180803030402040b180703050603070b0301 77
    0x10301440000041440e4540c661090001d032107014040c034985150100060044503004842e4036030300500480c105410b012915071290707a183d101c184100c0b101d805c50402401680e085054082e00000309890071410b0072400c0d80803c00401120f800c1200740100c06001407403603a030719008140980000e105551107824010644c683d1841407204148019081c0400411101c1d030240c2c80740d000201581d40e01c03a10b0740b1900d052100400d141c41d40100c0c2c180e00d41505001060040050040b1a84a641c5401040e1907424404110a0300307260800b0454008103e150950707130380043d5003101c103803044031101101003140c40c00300018070001c0303c020b000780c1071b00b00002607080c0c01204103c660009010b00d0948005000011a45403041c85106803c01881c80f4000005040603400f1790140102d41c2000d407280310a4403c81e0369083c40c240d000040c2035100000304070441c1814040c3c66520701c002d4440740c0045440c401c107030700707000e200030505020103a480c000210351741c0c1d00f040224001d144808070f09599503181c008031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 70869561 1250 70868311 70868321
    0x9030302030a0f020a1d03120f0a1103040609030311030910020d08090c01050304060c0207081b01090801090c0302060a05070f03050406030e0601051e040243110418050a0501 76
    0x4402c02c074607240704032184404038001c60b20340b110301d0703510020b045610030448101c05112a00345505032142c01c42001410161100802920070140710700341d01da08040f4001040c80f182c161620603590400e0004220644c0c1005101c01581d515040c01c442003800318518614600a160308558018901590b060205030007168421104070b070790b51000055079900138015550f114404000e0300103501040040d021440300e610100300c08081e0301c1070702c0704140d840040da440d02034009210080101ba5807112203156030080c1c0d0b003800030440f02c00280700e01c0750b00f51540406040c6510010340120300014400c0c1486104004842c03c0d2540300e02c000c41c100302d5604000b0300d1500301e8002c0d41c5c0428a45409603510100019409040342c50082c2000c0d510303041c80c8a030f40002c9080038901c51700183c080c005000311a2242d5070b81e040c0740503040002c0502000d5a8038100384645c01c20303910a4804100c15aa0002c641e5082e95904001800d580c00700e0001c20364203511090400c0d50340068805e000355401101001019001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 70870811 1250 70869561 70869571
    0x5040308190203060d06050c130e19050108030f0c0f01020f1308030304051b010c020909060403020d090b0412110d0c080106050f010c1e08070c05010f050c030313080d0903030203 78
    0x200001c08641041d203404030f1106407041d65022418401c1400081c130990041544040d040744554142800c081080f80c20a249401c03441d6011401010000f049504080c0c28005600c100301c140300d1540b400300b11549078800c20940303070a40640010201c0c1000300410451644c00b201c1c074002c558541403242c14400c1900003401c81c01018480c500001360b1603400006903030046400a0150280d070000c1c01c00c840d15504070b40c02e514107008104ca4002c000d43c1e03030f1030812481185a100902907928043c60002e0030240c10810300c506008602c00b0501c035012500341a10147c6100c00b0503000700c90000c1c1007c4400f075000001e91503004034184c10078810840c4600409084270300b010000d0158075165010040f040300b404851900044038074034014081703580c0f04000c42da04e40030300398107040c0381c4542c0e101d2401c1c80c2c4c0011002e59450500c00810400c55a002013080112047c0c1d02e002030a000d10589003945901c006004a61601d980314888800d200c000030031601da240c88050204000c500500d4064040c0d042114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 70872061 1250 70870811 70870831
    0x140a060510090302030c040b0307080f011401060207060f0c0512070503090a1505070b0411030303041b06021507120b060d1509141617010303030605030d0c0507060f020c0405040308 79
    0x10715080c01e240980541825250300402400001c5040c2081c000103140e01c6031304542c540b140350000500810148924507007004c0388030010030345260030380c02c01d0540c400607400f8030115400444100680742c1e100403840041042d61405c8000c501190806601d042e00003900843c0c4c0302c02c0083c8060412100000800041405454078004a03603548984d4580500c10201032010030b400300044400030740304042d0340c2c3e40316114052180c0b0703a2110501080c41e54200702d908940192550503555140ca00350103900004007102e2004091106060441e8003142c1c0014041d50b09202a150818548c08241d81010280380d45c041c2c07096484200d60442440607042c050080305440011030808101c100260159000b4070304600b41d812f00b2500d80b039103020050b801502d0480e0400040108503c0d13402100e000d6035000314026036001c0754260078031041500b8000314900000c140448501c030340e400101c0200301c0d202100e00509045121240c0c050382682042d00c68101c49030701c036250204000c1010742108403e401340603821 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 70873311 1250 70872061 70872079
    0x406082508040f0506070c0203100b1014040e07090f0f08031b0c030d090f080c0d020105160605010f05040609050403080f06060c03130618030b01120201051204060e0d03020403030c0f06140a0605 85
    0x80044400c2f00c0031952180d822415944520040c0b5000383c500040035500c1d81583c0e41382079a100c41540400e0803c1c2c5a0500203810a002000b2a103080032410300640942e010f4148a5403900d40500daa07449002d0a041141010b1052031131405424860009100c901a0aa851a03510014010005c86990040610b130102e804800300740d0600002c0d03d02c0841c83c011300b00b415003d103550010340f07143d04a102040c2035a08400c41d51800101d043c001c07a4002d00d07081c0d4074009001e09000c00c00c0103844007900301c0b252040c0380804200201f80c2c0320b406a070301704003201c901d20a00c1d2900c81c0852203d104101c5c503440280300004220716030318140c0c241141202c444c0c1e80e48007120170f404400500c1105062002a14050202005205500a00414031101441410450310b00001d0a29484030b1400c1110305882055403070031244000d140c180314801d003001e43d62808624260560303802619809a0071800390001100c003100004004041e403010100340042c0600085900e04100c00c1d001402d124052980100c50303603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 70874561 1250 70873311 70873333
    0x203010c0207051809011107080a080708040221030405190f0501020c06070602281106070809070e040204230103050f03030f15030a021003020406082508040f0506070c0203 75
    0x200e5102d00fa60340040c680110b40c00f00d865452500038011300000065540c840761181c07203020140013052284e00c00c0c12003a856040300c0c1400b0342681001007940c030500074200204401a5148400320303c1010400d1071815003510904411072450045400554024080d248480e542c8841c281400d021201e0b10b440d910403440d1600012a2501e07254503c107500314900744406000980250080c1640c21a25511068401c00300c3c0e04803001d07510300c21880000f003400000e10945104042c041554442c0a40c2400017486c181002100da403500d03d07200311038003d031031800401d045640e00d0300b0036a005a04003665440c261421a01c20002400038031044401d44a10300c8204140e00022003541e10510000d0084001070f0750b032801303c0181c01c0446040350741c54054800c4003030060b511066101d004552551300181c8403070a003030001d0309003003010b080c903082d20317008d50543c8592081c0702c03170320742d4030071b090351400845030b4460303160503400344120030070040c0580240c0c01040485a0300024045d02c160080b81120064000307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 70875811 1250 70874561 70874563
    0x2c2406070506070c061b050a08060406050f0415030804080303100909020f1c021302030a0b041116021c030302030a050c03071d0d0b0f0a141e15030d0206040203010c02 73
    0x591400a206030400800155058020360f545100e00703000b000c01140c40701400100b401d120b408044070301b010903004544070216139449151954050410703a000c020036400c0400083d0100350200ca1948616100c040c2c0c55850095800d840005542c807803034003510f443e11042d0aa03226002112400441da40c442c40c000350741d041d14010b1122450f0040c180031912900705092210070000320481e0b100c4024030440c4040161541d001000d400441500c0040c0c90b414001018000c1c3d802d0010b440d0701c81d40c24580844181c041d03a404884800c00980b060b106140780070300c00f140d41c46a03154508254222502521014540c050b0000c5204070300c5000100015561140b0300102030105075640400624240c5100c00011742c5003404d500054030082c01007180344041d0303885901c5030004441c0c044140c00d000c014008006c00b41d0044002401e10112000800c1c60459100d0b40c0380e40f40032100b0310400c40b074800802c10502002515050500d00a01514801d04c00700740040c0d80c0311810b45089020f507207080000303a0042e01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 70877061 1250 70875811 70875817
    0x50903030f010306020d06081009060b030f1b0103090807030302070308011215090809061305030c031f020901030902150304030908010b060d020702030304090903020607120203102c2406 81
    0x32007001c1200c416402e42d1501c50003508241d08510026640314004150349070704120b4a40880c00386080031803605524900a015100c0460049000b58010042c0c0042602c002c1445605560b564050700b00320088500101d001c1c0c00a01c00282149600041d44400e03d036141c0c0041103503034000e40750b14180340d9840c19a901c16900b088005130040901944901524140703810010b02a40220b01c0c65080005400000e001a0311004a14214105d004402c03c03960809204149030500d08401410004c841c0c0184884103401d11805c07010050350002d92501180c2c0260700c0a000390303030082c204030301180040754144120752003030f20180c0210b600580005000103050041001038100500341a0500181010310300203074115003401c076414001840049070359021707885020320301030107607004100d14200400c0c0a0700c82c0d5010200d5101c1303540100200302da8842440440c44c00c445201320032201c0402d64004080d000c419114945180102d484c00b40041c1411503251040300c0c10185500c0900200c201003002040c1c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 70878311 1250 70877061 70877071
    0x506011215050a060905090304030203070504020a08070f0219030f081b090d020103091a040314030603120a020a060c120c0504140108090304031a040c060305090a12020f1f05090303 79
    0x1880012045019004580082c0e8111508041c0071070104d460b0783d242403c0e11ba0817905a44154400702d001c10035894204050f4009060a9a04500c3c2550b2070f10014041300c0c00a01c3c08084c44400c59a00125a200b0400d0180400545c850400c503c80503140042c10640f5a00000c40014458000f0507c80d00c1800721100d0840c01d070751081d503e410400ba090090710302c62040242e05140d0b88030040c030049001c241440708a06032404c0e070b50740389203018030b4050041010702d030410250720310910030025a900d0004014005000c840c90b2151909480c602c2280707091714191005027041e0410607075460742900008400340110640c2c0080c050005945402c40300c0e07009501c214604a03011034540007007540294400368100d00c04100340c0e443c0503140d403911040000c00b2144034001c406e03c1c00800007803000590319940a00400d1405010324142004401d59816074a40050180315502202e01d00d8a40200807060344101c06805440c0c1080c620300385004441030782d04c5403024441c20900020401300000c000c40f4410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 70879561 1250 70878311 70878323
    0x6030c050a022802030703050a0b0c03010b0405061c020a0807020f010e10020a0318050303060f040911100302040515120a0b0607060c02070b030a0506120106060c030e04180f05060112 80
    0x88407510300300400e07481c40701c0300440e043c032982000b400158070103001c104042c40c085e02c002c03d480c01503450070000420b0003c10112030300c40c0a1006126005500b0704036401c0328030803a006511200c130024200355940c48954824130042c800142c003440c1030303003210316a8401c4449400740e40c003e0900b10512030030384250b020b040290743c00c1941880c3b00c80c0d4055000d420b5518017403500137501040e424503143d8843c0e0003141a1a690f00202c10400b0078640340058180c21901520184405605691204464100d4080d0180304945245013908094132a5051320000c22004124500c0c4148060342c041d02540700503100042d812141001510240240c0141003100c0c1c40a032040f8904035540d21090000d00318006101c04600800b200090030450035000f0714060741d224000021641400e01c00c1154100741768011118690400d0350820600390840c90b4170600e03035018100300810740300d8140050f0003070000180d01c090307141030180c2140c14007a1146060030b03550720070801c40b2416601c4130f004244c090f104041c01081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 70880811 1250 70879561 70879573
    0x5060928091d060105090606042102040504031e0302040f03110411031003061d0c100c05120d0c0206060a050f0f030304151d03070501030f02120106020c1804150b01020316060606030c050a02 83
    0x41c0c503403150302b041400078021030007644181c825030000301607420580301030700011200015804181d819289410303445005050442c5850720f046000f8003030120034803010380044003410f1031400e291941c2e0464440ca480a15040ea80c91511461202100040f4081584c0e04c0d440c01c4184c940d0040c02002d450041024040141a02c06402c020498100041c3c0c0c505010000c928040303400142c42004802842d0254003c07090325101c0200349503085075440302981e011540710000348a1643c0300c1e07118510550f80b0507500d100d901c3d041100828a0040d42004141d00761000044c0000d68201182c035080c80041a1742e80e03100b8025413121101000d0214915250741a04000810055580254441080d640c080310000d410100904255040305600340e11210140e0450390144003d0f140640714041e079040d4246180d40241841d440310380030b118500048041c0195201040100c5a008005442500d842e131405412101c54600d02003001d0501031048401090900342400449800740c401c2e1400d0207000c0c2d0040c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 70882061 1250 70880811 70880819
    0x40503060c1c0207060519150b0d060b0c0d0e030304180203100801140702070b0c0a0f02030a0f0f0b06010906050a0c1b0b04080705060928091d06010509060604 70
    0x810740d40702032980c01500c007070301c900121128002d00251030201c0c0664000201c5180c14042c0d00b915928a983c008005860104418044c00e910048601900d2540e00c0c5140c40720741840c0390700010801900050b84010f408a00c841605000140d0050308001e0303540c41c02c00c03000c080c0003030580e030340107030b014110410240d00102e8075009807640c0a540d0010307281e8000351426035240d80352421265040c103412282c1d00d04200304070401e90100880c80c000e11407090590b00c2d0048103180941c86020404008020002ca54a403400b0b5540c10400c80084c030342c1003901c180c510a542e00d4901c001c946450402c460003100c140001d0203070341c0205100da003218000d480305031070f10f966040d085400c0d907414070040342c00da403482c0403184000c2c0c07000c1d1510001e0142d8880301030f51035007840f561528214807640300500c501800c105c20386180c0c460210800c50b8600c0d0b4900060244200d0280390801b0340350350003413408581340c0040c03540e40080c525071b0710307010b2800c06003030f2800381c0d8a54082c40302c26042160b01c2174200e442000100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 70883311 1250 70882061 70882081
    0x321020c12070b160302070210120b0102212a060a1506140702150a02031804060305150717040303061509050a0b070f0f0503210405060a050c131e060504050306 70
    0x401c5500c1c507494014a40380c0b131230b800280da0303804500c14000000c00120f8046110700784c84c407862003449000d000419884802e480e02c0180e500d9044012045010003041c0304d490781000f10091011000402c4603012401a00c8200c5a914002199000c8803103080c1344000081201d400010810f55900756912860300341041101e006030f52005d0300c00c0341c100410780c0f030242d000403220300078040796100d55000d9a5940051102c000d021801c1ca98500e208615001d401c0000030000a0030030115210b41090303220740d5484030f0302660803042580c0d00783d51280c19001084109581a40101c0640b101c1018600d003c0c641401d0403a00302c030090284942008000d1401c2c0720500f801d10107080c185214060304a401103080c2c5ea1650200054201141c40394400301d4400240f1801c01505550382c0f00c4a04032030501c0c9007030f459050f615100a45800d40503540c650106a000e1f460b403085407181072445108205840e6a1000e004819a031003414001082814002081007072003681160100c4600170014201516038a440c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 70884561 1250 70883311 70883341
    0x603050711011a150c060f04031e05070c0815180f030706050603190503070807020d050607120c050f070605070215130b010605030910090321020c12070b 67
    0x14080d681d484030752070900901075001540350034107040c03008642d58014410001e490860403822000103100036500c5400028603a94080f0804400c0100b40d11141011741e040c810041480d081040550040e410b000c0d0800000c0607000c0c850504d00b2a500d944008503600c800c03c1510041410104a022032113090f46500942980007640c0262000c001c9004d00d0349255030303c00e18045420503210f200b0801320345001d00030304400060b50a2140c884411170307a9101d440740304a040c02040000301245a00664442c03c0d0850040c0781d0183c129034290a0541d8003030041d00205000e0300a607414070001151441c8038000b960072088280071890305040d01a9601e2001d00002002042188295010702003001c2c03e8200e1540511009140d01000101070705000724440416000300060000c104180020309a000815090034004c080c2d0001c0c000c2c105285c01c4039070040c0601021003000715402c4100010b00d8035801080d440422408a9140c20148404060780e405102d5000d41035207140ba0020351041c0089100c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 70885811 1250 70884561 70884571
    0x50702030a1212020c0f070b0a091e030206180405060a05030c0402030a0e010c09090e01020a081f050402180f10081f081009031b020307050409060e01050106170a060609060305 77
    0x75a83c011246104038201e030490342800308541e111080300111140f0a00c1f851000d003664034120740c0341c84a8600041c01c40d44003482142030a903200550351062082c1840090055580249415901d280945803000c01c000c40489051043c3c0ca0280444d1882c0b8103524000100e410207400340030718458500c100002500b00910b100c800d2526000300105e4042c00384113500d940f807030079100c09280a00f000d0741c4104680388400700b180283c1c4100801c07860075800a8030164800811412044103400c841c1131401c02102d680e00c110741007400440c1020401030411365601212105503010700b03169503001d04005844121a640c2c502203004400880e03607202ca198000305248101660445000d680c68010f50300d0910100140202165614616000c05a0010b2a201c1e207103564102041c6108080d00002e4880040d8440e07544215682c0c03140c0380c10000103400c42904036010200801407076a454030090455550f08044444000c032400000341c00d4852440390718241c0d00ca80e80c1d200e900900b0110103400808010302 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 70887061 1250 70885811 70885817
    0x1b02061909060501120506090312130f0f03120f061503240602010c0824010503060d0803040501050426040306050c04030503070302070513060b030a09030c0206031e07050702030a12 79
    0x7840d0010502c58003400c1d0081c0200700c036207031801c3c015081031800d014014000d06040e070000c1004000305034407a008150400850300103048210380d140b5010700051a000e01c0140920340c1c0c00364060516801900f03681c0074040001c8140615816010341000319011401202d0f0f40d01c1c43d10403100c8001d4800d501002850f14490803001561102030007500300090f4aa02403001030391907940c81482c296015007516048030034024082200d6488040c071034400b0f1721100c0641c1c10031001100080716035448880d080070b2a50002c000f15a242424101035010300011075094480c801104000c004402e034441444000003c1b00c1242070401d42981c3c1c801014240240c020391180304107001c04000308000340014440c0c0c1e4400c3d00141055450141030000200300b00015034031a614019041214803007050403241c4c004030385000010710704000d1505840c0d0180300500030b07412074000701c00c10840f006d5600c90b41d5004079500103001066502c1c004215800d2040e5107000390540c0280030508002100c40000d1a60346041d81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 70888311 1250 70887061 70887071
    0x602190501140a0903020705010f0e0108040606150201060e0606030103150e031e09010e0f0105070323071a2401050c0a021c020901080a0804060c08090402040b030402041b020619 78
    0x50641210002c0940300e41030031a035a60050020150100400306c0140f00030300b8140314250034181d014003048904405c46042c07001d1000010100f0420350710660181c541500600c4403520f8501c4024001d204c14040c0402d03071602c2d5030104d100c0d89814419603048940c00080c0480c401c2e2407000800c050b000d1449901c500c1d1100307104954080c00301101d06d40010380c07110715a40d124241c0380c000405244042031000e008070942c1e140713502e80340d85c0141143c00194060624208540c0f003001d00b1403020010348999070304032001040840800900800c40c1d0444280050b080410352904c1d40c010300c00d200816501d1440030b507804e290007007950094020301069442081a1b558034030f00c60b00442c1c0d11503c0c1d0100a00748030500790415045192003580c49000d0a0b5220081034540380c90303980c5803128071540c080d41d0144000f800540040150350012114081c10142c41036448640d10402a1207603001aa8100c0c819814440403045a90880b41c3c611080074081e4028100d40d19412403a42c002c01e208080d840c6150f49903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 70889561 1250 70888311 70888331
    0x105120a0204020d0b040c1706041a0904080c070902030c070f0f061406030f032706040b0406030b04060902090102070b130905010305060108060c0c06040201080709030501050a0c0e0103060602190501 87
    0x5480544071130851841c0219490341080200030459030b2130b40d80d000600101112211f079001400003265803201c816240014048142e00301000c130100100149a4001501c800300000c2101c07507000352280d4003004045403040b5854210f4202030703000c00c80d081081080107000f007102260600c0481004036000720400c500511141c0c5401d002d8400440c032a20708039070084188400c0f428100002920500700002450400391079482000502400d03107500c0c54000744007800d00205645840846004001800495607940e41d5070501030701400101c14407a1040d1f10b001c0002619500c4c5000310b6030450416400387c805507042002480b01d603040b0b41c11010350b17404000e4000c1207196807072217000c0c0a14040c400801180d8500b2401910303082c80240b0300d06416400384040701c0d42010002c0c249070001c2d424200350f4069501e1603411a49107115601c054040c4d8204010b01140041607400850413501c3d9640700d5800c0c03112500198255004e130311442c00141c0c011582c101c29084504d9000907414400d800101c1d5a07580 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 70890811 1250 70889561 70889569
    0x6170403030b030f160609030c0b03180a06060801180206070303050c04080114090d050408070308071b03061d0609030a080406060302090f0a05130308160c05160305060a140105120a02 80
    0x41520358040d01d5112654405408102c0b0211a0041c501c600c7d204007000c1c00c60352100c0704040c2d01d108401c0024400300110f0184114400720280d030b0070081c003c0b40e501d50914140030700a040203101c3e0300c3c615444c08110600581101050001c502e0300541042e20b00741255400f00d00400004201194400c002e200c003191400c400e001d003503c1c800f146002c603a0b183c01c0014450f82052011440030b024000200000c100c540c0700402c10804a90b000380307140751201000d003042c200031951031041d805580d260350804000c1002a83c0401300600c52000c0008160408029550795032070207a50340a40c41e4818000c6058071485103160300d502078818000821070599a41c04203038455000c0d224100301c010036030100030501040d40f280c1c0b50720059212140f205a085501d000c2c1c040f02000e071031304900030302c551044090140030b50000150b0682c0f00301251484101c04a004581c0b0415010850b078070f00441c404201c1610160007030620808800105032116407a04041002541d0070990140203402031030403200c05130752 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 70892061 1250 70890811 70890823
    0xc03070512130507090204030b1302010e060d0b040f0c02010c1d120c120d08100302060d0903031524090e07080601140415120c0206070e03070e0c090a080706170403030b03 75
    0x840845c0c05a11a81586403016616000420345000c0701c84800c4c0c85030260ba84110000c04080d17040e1901551151901002005000202400350708103051540c8445641d401e640240684c144c181d0003013114014406040320000e01c10304949281c4818198100001d01d4890008a00c03860994211120f070a03000300410945605d00007500c0d80c5400259041e0502c40e08000103e44c000344480c80d8100007410340e40000d07514020010350688c0c0c01d45d42d500c00010140a0740c0542e01504c500f41e200c00460b51f0310100d514100c181c80c1d0a4881090a01c221800d54501448800041e2001e4002c1c80b14544d0b0342c14021580084010100e1341007180703510b1070000700e03103041300180301826608014420b0f8080c03075a4090030343d0b410490044003051402080b6001254042070b5590014154602940300c4a4042d000a18100c41d03600300c058044100000c0c0090002031000820007404282c502c24500e603620b181c06604c03240b1a103d03030740200d0070752619039007031003842c0b0f400a80c030a2183c1000174404030b05101280c5001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 70893311 1250 70892061 70892069
    0x10c0b0f011409040b041e06090b0105041a030307060f021605010b010215240a080118060f0605031b0a030c081015141c0609030c0b0c03070512130507 66
    0x4040000180519031446100148200e425141030f00c40d42800d9507074005241006102505400d60180c41128034010050400c00d060340200d0b040c0081112810405400da00130703c200791140345010324083c025001c00308200310a8030020007440c2030036603544800010b030844480540c12036908010180002c541c41002d200254040d8000045481900c4006864440010b41171920142060300b04100c0340960310041c0c150702440e0b9071100e03040c140e070408244010030981203440366508013900a0000b60030b40c51103103070742402a1010b10070002400e00c0002100c030640140303a019001100c0081790b491030149081d003c020060102c950066581c0c6a00b58602e0054001031841c0d0403410018881c0d26a40c000c406590343d01c000d16203021490804490803410500c90240d0003100740341c0031151111190200c81d4201c41e00400203204e80049850002d240d040c007120100d60f208602008641c2040d5650203582c86180310703440d00c510701004d1240900512800800c0340540489003030001001450a105082c005c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 70894561 1250 70893311 70893331
    0x10e030a0e04180c090e1204060309020f0a1e0b16081c020a03020309010e010b0f010c03200307022407080304140106060503160c050303010b0c03040b04030c170115030b06010c0b 78
    0x35424090036900390780d20104101b6560784400042200042287c0840d82161070500300024016a0b42c804500340c01d207801c401a40c006401d25000400541d01410302244c1c1b14410381103000e45484001501490180190240460314046070b01e000281c3e00900806041040f207142a2085415554242c180c0c7d0100c2002e20010b41c0100c1804401c1a09000c0c0818420381d10000388a048105400b003400c0c2401420350504029001c1140d00070b05004120b0700381400240c0601d00c2d04848440d80c4c9995a42c800305049029a0500c3c1d507428201c55002182c04a8000c4510140e103400c817240c40714a01c0c0c0c0c1024109540042c2c03513210041b1140c1c3d0902c6490b000300000c0c0c941c02c1d2280781c158882c2c0c001a0403002e03000c041c005585113400c002000441141d06440e80601d0080c0c0b1047c507102194503500940d00310b00c403030a40000d004030900c501115040b0445060080440806212440160aa64201c0503841004020321800c0c80010181c450545d80300c4070600d0811801d0300c0365110f044091809481c02005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 70895811 1250 70894561 70894583
    0x9120a02100f0216030f03020c03030f10060206070509010f0302090916030501090603020307030209071707110d030e030307030b13060b04050f1002060711150405060a05010602010e030a0e0418 84
    0x70751542809040c10104514100f141803404d04041078803903042100000b0304006144100c40c442c603010394162840005c0708402c498903464150b042c0313200341b0016202c04110044850b000940c20b071001400c107201d04401d82c0d0751410034503820015114080341e1002c0d4010f00d80c00b40105005da031124040c00e8864040b003000031a4002401002604603441038100c0c40d0000c1c2410b0044c00981c0f4002002c8040f00c1d070540b42c1c7c4045030303600d10048400c5a00340004806400d02170050020030750340409946c5c400003801c001e58078403041989041d42100c3c01480c05820941090001400a501942c800f210411015040c5d520440e8484490790031031780c250300191100c1502203000c0c405030030000c2d002019141705947c4100f1000714a90040d50b035100060aa0040000e0143d600030303c030b241480303d10740d42208035043e030440d0b007041c4c070f03203103858080c00c440100c182d619000000804500c14001d0035154107440b005503103002c17101c03901141c41c218218001038006480b210400214620001072224450181683e480c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 70897061 1250 70895811 70895833
    0x7030f0e030408031c060906030302060906070c02090105010507020109080304080f070e04020108010b0d060b0301090506130c1b0c17030c0d0302040302060301091d06040302030301080c010804081209120a02 90
    0xc4482480340344640758810710040c08444030000c111002440300c0d4014507106500051058040c00007a04130b42d00b80f50901ca030002c101074000520a002d0300100d0152465a0340c1c132002100c1c042c01c483d1029600c2282c0400401c602c0d4050002010702a0062408400c07054407011070034595440b81c0e10004c0940c2c0240840c10500205114500181103103140c03a003a5400e25400080c070032541800340b0b6051507030005050304100141d500c52801018201d20b10b03a01e035a52070410800a20048509500076070601c05a01c0325441280b00d4080034410503260300800c0c0d00009000c41a0001a41e41100c00c00d00202022a03803414008984a42590070401155102ea150b4411400c0c031400c414000207041c014841400180d8420054a066400c0031000141c04803003c802050030103c0d06a200201d40580400c9c8024140c0c08030003141030751040012a440410000c0c011244441c045601520408052050780859090b1001d6140c0110640c000c0b240c1035400100d101c203060f4000e40d441e174096842481c07014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 70898311 1250 70897061 70897091
    0x304170c06010f0f061e080c04030c14130203090a062c07030303110c0d030209060d021303062f0a0c0507090203090c0603090c0415120c03060b030604050a0605041106030703 76
    0xa000c441c0342000e40340c04207042c0b06c2c801800041c082d41c144088a000952614520b00c295001190050005803000e560790701c811031005030410220707009500300f80c01980810094000c40380583d03010740007010031600d0390325520010a000802800043c0d03a48c0500e4618414540e204038046e200100a4900b13a0701c0c3d4030380902194640c038042e00307407540c00780541c1c1491140400c0d900c000240e40e0401690740d08a40001904900c2400e440001182c0702086a0a00c801c1094001c82524462181000102280710786801030228610001c0214410b040403c00351740d00e640007a240443e1b4509000c0301541260380c82505101c00368002040c41c5501204100d01640b04210311010760400751074071450744c10400307041da0315600c20a07090b90103291940040780681c94408400d02c02410b550840c95920030403843e0600304000f1a22090f9811400e00c418481985000f1801900480e800401442c14035040e50b640700103898000e1081d581043c001c1140901921000004c51060185e59400220036103403032408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 70899561 1250 70898311 70898339
    0x605220209030a060614010201050106090b030c190507060e061311030304080609030a0339020709060b0a030b0a1d04030201020c0a0b01090509120a03020d02040302030304080a030f05030c0304170c06010f 89
    0x15045a040c0ac0c010441103070400e0804081c0c4640ac1403580d0380340e44181082e11244100d02ca42c10404060f0540c1c069000e6000e0040c24846104440c14858580b4080d03989580d4041035900003c3c0d4852030324602d002a0700e40000400904000e01664100740da103881440c10100221007400c1c0035080003400d03010080d85440b0b9000420114100291000b00f41100300008095507029006503161584201070b910f0300802c929802400118014000d040c0c0300d940308003e903040700c1d00207008a4200440e80e140da00d402d190100540300e40d85408400782c11200000c8480b01c00241094040d95420040400b940e80c1c1403008823207480c00b460700d118940d450a05404200c841c02060854a40c008802880c070300d54400c81100c000284602e00580c5a044845020000f445190300095052000040001e8154804580006980d0098403040c040301030b4100700380d840c2e00c01100c0c8000205c804000140c00142e030141c01e020454006003404d405c016031048913a182400a801000b01c0804200040026071200005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 70900811 1250 70899561 70899599
    0x30b130e1f0c0e010804080909090304060201060f08030304020f0d0b010306140a0911062101030b04060606080114040c090314061614181f0f02100605220209030a0606 73
    0x10407411074010b03401001c0d2550074041d181009900c4c0003283c144403030102590002c0500503d20307010707800e10403400d96495219100d168099424036070300091f11210904800200c40104014502c2d550b00c039401c103c40e4203001c00c0300c03030340c0550091042c0d004200080d40c214040c600c03132000011800c0c0050a0101e0f10b8000030560324009081521010000d8410300032400300e1042034900e6511410081345d2080c40d142e0103611885a649090000814004920100c1c2c2c003c0d4004e80c0d04206070358907001d044428035803d01803420f0181030030b4032040c01e0741061f51240b88207a4403403410b81e8034140c072543d800062040504040055602100502c08800c01da107400c00045502411305076030b00443e8240c100d185000d450320103550b800360f941c00710350541ca813034141c0700030801d00c4e0322001c0ca440c1c0000c5000e40305105c0300070b420300188507504101450007120701c610300c00d03190f00400800201d0061f190304405601d4040540c2c020503004c2c0710b5800c2c030707440822044243c24421000440c556081415801c1040740ca045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 70902061 1250 70900811 70900873
    0x5070b0309030703121803080a140f010e0709090c0c110f0d02040e100c0203041d1311040b100903030210061a1806040905010e06090103030f030b130e 66
    0x414041da4100000c00c480082c1c0e414200020154522000103005142a0440c0625084d4a0b200300d0101a8803503000c034841c0402580401c80f0318800c400d4105a90400c03510382e801840f4100c010b2001c1c4400300c201d9a404250341c90460f0005845500b1b08040ea4644100100840c02040170401009086c0300c5800036a102500c0703038454a0b44a1001481c25061168040e000b41e5a4990740c1112443c24044044100d5000005001c1b056182900950302d521501c54060030120607121011001d1040c0c6400e40110060b8132465100c0035162155031400c400d0030010b0f540103545000c00c2c02c894651085280b145001501d07031001942c0343d401d000e41441d0a244803046040e2500b50140700c42d1a11403854012241c1c5480002d4507409481f003140e034004001852151b02103004980044c503024250400c6058844041280c4141d4a8100c2805074608080c00018045200030541c005d0041c444ea004e0198010018500848941c1d490840030031503240004007207154000100541d00c110b002d150215001900b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 70903311 1250 70902061 70902067
    0x18030c060509060906060f180c03100602070e0601032c06070f0507080f0a020703060203010b09130203071e0e040e0706021612110d021002010507031104050306181507030905070b 78
    0x303246030361140b50060400d8403a10381c400788010b940d1200030b044000c1d00003e68072128141403000009c61960801ca501d007402420080c008121248003050190894101c404101142e460340e000540c090060983e80188440100140710000d031400415040800c400b05d018020500344000000c0c035005c503c001c03070028404c00308000b10010b114070f0700721440005800c007031a841e2600204100c0c03c00b03509a10180c6031500202c0041113603209000201285903080b0b500c01400f00251000f030701a030100315590008910403641c1705070f1001c2058514406052280307440045200d00500150072225041c61420866005003820701c40a5010040030f41b01c40803090702206081c1ca003504403080100718000060104031008020003054480d958003140e1107030b004001800600544c803009008040c2255082e00013402c0000c58ac0080040200700c4040e90405800341890b5501c0c40c403a003190102680c1070307503030b00d101d0800910107223114101902d0107000c1e030780c0d03010800361410f090181c940030160300f110301c23075060030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 70904561 1250 70903311 70903321
    0xb06090a0c0203030a1d070801142409040809040f14061507031206230a05041a01030b06070210020a050c010828090204110d050903040f0308030a18030c06050906 71
    0x1c1520390004200002280504104201c06c100b040f1500d10902140f05440010038015010341007003e410b840d0f604075504ca40d40e1104014101400f1881e801c14500d0500c060340d1043c18901c0719982e005020b601035038605802d050110301229420401001666641c03076152020201c0d81c402181c00480460b66080d0b000c039040b031707075410512a12900406001520503401c0034544660040b6004020000540345114426110588000c09011100b88521a81240880c82d4909032003100c05000707211049032020f031030240041d401418608140c603400b00e01807000c000103944900021415040e290f000c0d12141c255454554a03142c905190b0f24148918101006440300d00003510021081401045050741a20806448018000100c02a41050500074001c222100000051080c0701035580308000300d0341c0f002003281e00c86c0900e01803a1020a01c030310b03042000c00c200c10055500401e40d000005001c0f030b02000648590240c846c41100400c0e9108000030511509204481d802451070000c3c00c02440c00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 70905811 1250 70904561 70904563
    0x20d060506090612070315030f060c0f090b090303300f04050a060b01050d06030c050a1e091e06090c0e06030405071505120a06360917070b06090a0c02 66
    0x144c00c1030912985503180c0020b2a0350b1182d00034406101c4000602c0341090303102e040000000f484c60809070341190810050300c60441c49a01d800400700c00b0f5903a080340311802d0018848555020310011a4984810f1000f40c130b16040c0e6013400c41d605610b4034078242003345e21500c240c00c1d0a0b401000c11800300034903801c1001141c00481c0d5501007030380c0540b00180000d0350400503079007070082e5110700f02040d260500c08400c00903500c4e007410944100b140c0440806995040c4144200300f4580c421191b40022042040030040a401c10492800124030740311810302080703c003008490703895100450464844800c0c40070680c0100c000013183d04180e90341460b5103082e4541564030180c511558204045098068040c0c510810a0701c134821020340c001d02c16402d100022101604d21405000e03007803080d01001a200c100100c40328002800c0d982c21520250449940403030003007a0103541a01c414142d41c40120086807100300031b008092040200244900b0003030144002140000e01c0e1450441c504400014290b0f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 70907061 1250 70905811 70905817
    0x117010e0703080f090114031501020c06070c03150204180b0414041109090f070303020c1503070f050307030209040204120c050f0a0302150405040608030301090f06060504050103091403030a020d0605060906 90
    0x413510705950320001c00004030340814801200340540071003c020700480e000b40c0c8070402005c0409a0803900f5819000d4204074442c800e52800502c043d2000604000207940542466000c002111300107041c95615442d0a1360003115050703070042d042e51350500e8180d80c9058843c0228482e00068071803d5440d107640c4400b081d0391554401d900c0351500d42d0019191490030407410155084407030990309080c2c0d491402035520440403440603c11600502005000b8a50b10207480c89600c156561000c04404203c007600d60740d00281c00f410400da0200301e4a5410b0301d440c0001c100034001c500d2800320058090034144880b00e800c2d04102c0c49442d016188c500c0980e213601c1c0e0320050704d404842d00f50803460710079a610800d10503544801d030410300380600003699900c04409581240c12440050049550301c0410504880e51802010003103481400244090b5100c1d40c40f21044e0761290741114030007000c00450b640340d07807c1154100000c9400081c40e05000c001c60040c40000c22050324210b00340200d81001800b640 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 70908311 1250 70907061 70907077
    0x5060909090a021e0901210f0c0e100e13030203090402090604091b1e021b1207090c0e0904080f160c08061012020d03050d0609050117010e070308 64
    0x1942440201e5840074041c010040340702d900521049892228034181d504070402d8a071030511404020b0f0002841c40502030020300109030070b06072441052060758980280b8521901d0540345111a0703480400e0052170a545140079410300001445d00b42d01c2c0c00070300c0740044001003040c90940006161840040c0e000001e445010074110b070b02580f5508000d02003441c5020382c3c0d029600081c1801203504410549856080000d0003c0c0d42d4038086181c644050a8210f9a00440798010380c0588180300c160103203110b03d0701400d200240341c015061495181c03685030221a4100044003960344042a1000da013080001c000d1034026981006245002c0d120a0014003802280b201407200c0064840c0342c003882d60308030702e6055a201c0400c024081d22401005c1d520b0702c04490b581442800b900c0c012074601203402114150b82e500500400d00d0210f20742c1d08503559000580c0205c0394a85507500494401c02030f0203002e0107400b814800b4200095001c0c603190954114070300d10401a00a55401c0c40400c018504461841e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 70909561 1250 70908311 70908319
    0x60203191b0c060e0a0213060807050a030506070806010309020402031602160f090b0604051206100509060913060b03070e0402030d03020f0d020906040b0d0f0c09080c010309060902060c0d03060906050609 89
    0x204015040b21400d05d18064002944003021850141740c440b0190300c5141500c1c0f81f44101d900385500d80d018401d9a040e00c0c0400340c01680500d00180c00c4511a0400707562080061501050003200341c0c0c045416a0815914040741000e44a02180c84990400c9860b5001d600c40c0b40e8401218178203c01104001590700910f40e07615100c28503406603407640002c4500a02001e00311020050090001980f154800da550314888005001d00041034501050301038003130b500c0100b00042c1500c0741d5101d10700d10942a00211180c6440725048680c0b0385e8240301c10001806030051040744d40c5010300c1014240070300f04103880241031040c81030020340c20a0301e0030758181d02030507240142e4401c0381d1000620b00d40a01c1d4007803201800e0001d5500e14803445030b0000086507107540400c3c01601803485040c3c8102200d8052610113500020f00c18000398843e0300511044c5000d42000600c0041a4010840743e40c0311f24000b0503140e0140a043c01c040e070b4540700784e00003810030040810410341444002071140c403030700c016140300e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 70910811 1250 70909561 70909571
    0x10306020c06070338090705040e0c1905090d0c09090212010c090b030403030609060f061709061f0906030803160e01020a0303020705010e01090507050a050d02060306040c020703060203191b0c06 85
    0xa00885c401e18003410050050481d030072460701d000c0051850340a0300071901d0b400418804582e00c8111030054172000440d100e04101d422203000011100e6070410744030282e0200c0f90220100115004061082c090034040c0d2000c41d0742032960041c000c0ed4070100985c82c00036894001f040d400203034041c048000f52040300c52142d03a01d8035241801c0340980400d800c0b4580c424a4800001703101c00075421008126900c0b030301c501d010070729400e44164203e50110307449070f2590044800100a00109404020b100b1560290b03010306903201d80c011011110542c2049502c0940001805190204240d890442c0d500c00d1809e103101d4906000000e4841212410040034107070040b5515003002801c0d04051140001e9600810404641e8240181d6a880d68410b45001c1c002c2e052000c40c4506007212024034554002c1d16039881c68035100240402000c541d00e1060840c01203917404000201c0c00e000460181180d110f41803a90b48415a5a004541690000c02c56500149021a00c0981c2180d202ca410680013040054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 70912061 1250 70910811 70910891
    0x309010923060f0f0a170a0213090e0a15060f05030a050c010e0d1208070809030a02030f0c1903030b10050903060f0a060b0d02030f07020a02060d090812010306020c060703 75
    0x84c0034011210403003820110f07591400642c042a0300c5000840c485000d80070361074422480c412841014008038201010500038070041031a50030809c124100241160003080c0c8540b0340413540009420701d01070fa036840700000c201c2c0c4980b46840f1400723464100c000c0d0800c0b5980399110765442840c0e40c0c2040c103004c145110240565070704602c80c06020f810a01200c81d00141520003061218112540404100302101107a0303007050001c00d907400c04409400441ca8010b1801d00d4000a8105802e510b94a204142d802121740c000400090707150ba11070340b00884c2c42042030040242e008600311320181045001e100c1c030b82e923566001842ca6089068940c050210f91900710602c0040e10702d80c1c0000d141040d00141d001402c240d107500443c8500c0381c80445529a450714201207894001500c0040e40c801c40a2120004410032a030112404901c548090340c503102100d5210080f11400340d0054820700d42c00700781424a50303130078002c29501c1401441c00f04621105400c2d0140001c19130100b02d0b90a51005d01411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 70913311 1250 70912061 70912087
    0x100c06090f020a09020304051203101a0d021b0c041802010c023f0f0d0f090e04140d23090102100f020406021603080d050c0912030901092306 62
    0xe072801d8024002810940e2503001d828080e6005540c00c1700d6a10941780301e0f80d145200b04054a000f0746031840c7c0d15a40a1608104208002c04501c01c0c400f00002044084000c000b50720041c10083d400000421031542002101e5052040306800755000b07038240b1001942c0d5085941e031569207280d090130408541c00c1c0b54004642c41e5400f07144100480c10308000310703889032041c0c0c0d0400c144110342010070507504503068040356112000e00c03011004981c458a1800200b40c054410380900c40d04600e8201000c5a464641010320f9406640913510704200344090240340c0018001629040485e051241c00d02498040000ca0810440f100c03054181d070100c6c2d1300c00303182e10074401029a030b00100c00c00d1210880c00d40c2c00c4002540184038903005840384100000444003880d01480440b504100c10300c0c1004031030f410f5000600001400481410010081c10002d9550742015030802400e150055440c4c2c1c611500160002119030030420340b01000f03901c43c0802d800300743c14843d100a03054800c00d4480394505400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 70914561 1250 70913311 70913333
    0x2150a090203011401051507080702060703110a08030123010e011d04020d02030604060e010b0304060207060912030504050c0618060a050f04121502030f0609060a080f03120105100c0609 81
    0x82d490b508000078140440e0a80c0315540c142c40007100c3d600b001c0030f4413031012501d62003407000080c100f10742800f442c005440c000b400344c100c8c103009042040d8dd15017005407107800c00c109614100e862800110040c00300125103103628100b100c4807031030307a0329484c1e03400e00207044041c1014400c0d0401c08400c440d0f51070075401c1e2240360907000c0301038000d40d129440001d41c41c010750011944c150045141c00c5002031240401c02c4401d04032004242e07010300d182c031280c4a1101940c0300328026243c0d40d031540b01040000380f0f681b50104540f9000e03640090103041500d40142030401c00d4291522070b46080c0300d2903683c5044024200740d2202c0450b00240d8401151005440320302600c0e07038040b600171022500041c40700e442e0454100e41c6100700700499036203100c0300c82d0a00300d0201b9606441d414002d180003424034140848095003110b00208622200e503a41e52007185055500c09003200e640d00301003251101d000b41851014050141169800003980c103140000300b003d0010341014080e60b455150440c1030007804914 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 70915811 1250 70914561 70914563
    0x1b020a0801060f0914010f0303030b061b0307060501050301050c0901030e0c030307080a02071d040609030e100e0f0306070f08130c0e01030519050303010b0f0d0501080106080f0a0302150a09 83
    0x2d00806580d182c05283c2d94186100d9020440d0070107203510070396100c1300703140f42c181e820020034407101d03c0c29a01d08078000c01c40c2e0200e04ea040700080194404000b960f10001450800b136a00a69803201180b13080340540300187d000f18000da040005100140d89014261403840c034080c40d000440200c003214162904d40e480703001a42502000070308106009562000703080380010740d021100c00582c0d0714a184640d50f2082c9818281c0d0282e880418002001500801c07515030207440e198551949420000b40c2e214000c0503945c010078040607040a00703040100f2100c4a442e000c901030700691900800c041c11021f03500030000c081001100000700650448811002e8850308002e40448403921004a8503220f503003804155124400c000400a011042d85031007540345a0100142d810b50b4a0941040d03000c2c0c004040b102960142170001c8681410385109240c002d110302000410030a141910513818040d00310381c1038455030040c9460304003194002400d0300c4160700e400f600c5181e5a86c1e46251386c000f0030503100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 70917061 1250 70915811 70915813
    0x30403020406030503220506040b0703020c03070e01090609140f06150a03020d1406030c0f0406090504051501050315070f0c02030f1c0507021309020411031008060a020a1b020a08 78
    0x401000384000000a030407400091440d4610701c90074100d401c2091190344c443ca48e4031800802050001400d02005071040b68800d004949010480c0c0c80003905040458218800e0311804000402a1002c14000c01d40100804c1d0740c2009501404208a91b11100041101075000e04201c04030b8610303140c20300e0500c050002204155100d01e01e10b0f0008019500825000044c941040d0500c00c4042050f61282c1c09040d0003401098100ca81d139082c001950314400489901c40c0c0e0321080040c80d6091801464880e611901c00340401d110040d43d440c00010060300003d01035030004c0f41002c22078005c030030116008812410b250100035200c1c1000ca51607225400d00a4142c00365008803a401c0800240518030050107500035990031a422008441c180200355000e0b512244421170a040e4201aa1100e00400e0003d0004205030281000f000000e501c140d4405804a071500307020009040d0511803180c00c5500b02c20300b9407070034514080c010244111000300c040e40c581201010070841d56040700400c01401010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 70918311 1250 70917061 70917071
    0x30c06091c0e0d0b1005040903030207060c05040605070f0f060c030b04050106080606040b160503070f03020d0815060a0309150c020c030102030906010b0703090305011401050f03070b0a030c020304030204 89
    0x299465441d0003030711902149a011000321400e44030b015800b1032078005406010b07620700b0b030682d4981d6050320002800054a49034140001708450b10389004410455000e40c80c0540d50303a000385000b10484041408041c100002880300340300f03c660010884030070031f8200340600c0b0480031a0400001104241100400706480c00c2c100c6513030a60190132500690f0400c881c1000240e0365140255500d40003168860740c0004100410b0041803020030103001c8828030121500d000c000310b07648040c0796910000058905120f00000300080503410080f02044015500c1c110100b410065050445a442c0f0b01e00d883c400e69022400114991103a40070481003500200e800501c03144040c4640010300c000b20074003005014040341203050f401c05000701c0340a216a400144001d80c038003801c0c02900c1c1c0040000b203042000782000040822000d004080560458000e08140f55140100b000340070250540d449009030446a0f04015500e01c0c902074400035203050402092410303200d28202d085100d513420080d4414542 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 70919561 1250 70918311 70918321
    0x1e0201081609050d2f040b030106031721010308070c0816090506010e220b0405040f0204200703080106030f1427061509070503090a020f0a17061609030b04060e030c06 73
    0x30005009400d45e0941d01003000b100507400345400d9544074000500113070031080c0d00030482c0044200030302901c0c02c084106040c1180c1c003403c458100c1800c0e40290ac1100021540409000e00d900380d070f4005161000c01040c20103069401449030a0703440c0f06000303030541d8641c0000c100f030340620400701c2c0741c550052184c40901502034240c480c0b018074103007240180746004103084040c01c042c41804c0c0142e403c000050344000d0582d0800c00500114070441302361000c030110100303001780028040c0880911a440b9040d841d810018008c00315486400800303101c0d07040c24099800d003811018402d42001c50581c002142681c0c541e40da0701c0b02c01c07800c0290302c0d2034850030040213107014081c13407803030174105007151400281c3d00d51041c111464082640c0450481d04002ca032100140b4160f000b004980710042c0041041660b90102416403c00d88080089103030405420040009240c0e00d040251011500b881c140840c20744d100c0640440008000402440e0341e0813810b0384841c010419a091040c1c0707907080390400d1803c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 70920811 1250 70919561 70919633
    0x110603041202070501020a0807020f0a081605040c08010b2d13030b10050a1401020a0b040f0b070315060309060905030a0f09080d0f0e0d1e0201081609050d 68
    0x1e9010750030014081c09001162540c4042040d0404e01d420240309070910b801a000c0207100c0d04030005084d07008410040025220809214600e68228003c69602d0514a000103200c190b506c511003101c10000c1070740051160b03590a00c00e407000c083d1602c0303841140b129079500240000000321100c000a0b130001c241441480000001c1c4010741348103038000c200709d48a120203409500b51034058540d1201d2440000e00288404840c0c201c90400e05104484690312a61034110800030103407401d56198008100300300030f100f01d040c203954000b2911301e03007001101104c1c01c21400c070380f90303500882080540780e80025090041d540c010007540b0784c124060700e03662150503030042c01e800c040d426240003007504404000381c0e580e80400c119011603500d48540c0090b00504108075140400402c05507401071140700114041190b1618a410408403c001180365014500000d0500c2c10002c0421040703481607002c0d04580390340f002c26401100d400383c5401d00d09450714a4000300d002d403c1401c4468140f040035040304151a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 70922061 1250 70920811 70920833
    0xa021c020a03140d0306050a080c130f090b04110108040b1f0801060605030f0106140306060d020c070b0405010311160b09071503020a0e0102010506011403100503030f0a02070806040b06010c11060304 87
    0x1611708000e0300d0382ea030042c840250140c0c4107222658116a07070300149410641c0306140100c0c0f45c40342c00280d08a20340c58a0048680c181419109608048100320400034044c644101440f000d0900040702d2130301d40d95a84000c000145046510440e030b0341c82000348138840271017074081c1000800901086880d408010b02d980c000b00c8030600d15a12880001854a02800071207181190b0280410b00d0750b40d41205105056025001502c4019070800820b4082541071042c00c000c0c0c680320444941da0b601e40400101034484d10032950380c000313204015041001510044400000794041b0420010782e880c40009401d01056620000e980000c040c2080c4e0301c00d03491350042280c0000c94541e807010900d800012802c8420440c1d103207010880c1c1181143e4214003010140d40e000000e42c2a8100d2251a80301090450704450380c00c003600000413440c502410703018800c41018124000080c00c1a207069190083d0750307040600464180800c2c111400c05120301e9130380120003008060102940d90070989082c8010340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 70923311 1250 70922061 70922083
    0x141f05030a0b04110d0f03051606020a0c0b01050a05061905130303091a0a0f1119030302130e060112051f15020d0f050403110307081516020a021c020a0314 68
    0x12002910380105444c100c00d218000701d410158a000c0c40d4041d5400792307069800f010642d0000502032800c080000d00600050100c0b50b0a65a420130034415460442100744042e00300300d00c144e08005050010ba03c5580540d0103580031014007038202521488181d806100b5904007002c945010f82000c01815080700c541d000f241d0005070705d07400640200d0408200c6004200c030400004d1425001c001c440c901c10240040840c8042c42a1500300d0b800b00c0741d20391100c46103038048000c6a008075081c000b00450fa60100004c00d07400c4402a03c619145000030041070008070300b0003819960302c0c00f0171070155545180e4005940c1540c14800000e0720341e6221004040110000c00051180d00785d42220140b003000300c181c10040503100da6040a0640da900e00723241143c1c070415900361144800c000f5040d8006c20101c1004490b15038000b086050a8851079070092a4880110640d440700150000603203404211002c07132858003040703034002100c2c0d2001494006141d40050910400310a940803000004500c0040c5c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 70924561 1250 70923311 70923323
    0x10303020f0c06040e09120310050a05040608030f030c0d060902030609070903030e060703031b030c1106060102060103020f0d060c030b010f0c051903050f030c1903141f05030a0b04 79
    0x444001c40ca40e0703950392036012480d500b00a0a0004002d4000e000c00c001e90031038440f0f02503a00da1100b1061000b0290021030f83c0094410344002c080003241410504039000c1e010968003801324500f024200f590300d1203105010509940d0000000320302c621034800b07503503184003642002d000c0c081c0d80e88074850203908180c40191007420300d4030206c1c1c041070190701c0c003400701c81e4191200c0232425064410010039803c00d4000343c00340340c0c44400c24809424610070740112003405440004a42d00c1c0300000030000720038055003c22582c01348040c000d031030307030001002411260704441c4114031152040108503020070718080200300c2d0342440d241e450842e8260300300c0104a00c080c1e0303405219072956a8111003000f078400014150f5004580e19441506000311075024080c040e0500d070f49418411580042213601c100c0c1d2a941e01d2a01151a0304001c16000241441d81d0f00c51400344060030f060340c2c1061482c0c0c0c0207440c4020142e1800e5101800c1600850040c008110040540d40d0300e003100d0920200302c5800300c5007240d070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 70925811 1250 70924561 70924573
    0x316110118030305060402070209070e1926070f140111010e0606120a020a14010c02092805060102060a0c020c06070308060a08010501080604080a031107030215070806060f0f0706060e01030302 84
    0x311b42424425158895001002d502480d240d64209841d0300c440250300c01c0e0803e1581022010500d504203111006101075030621800003010303d1030350007080c8000810003142d08078503420000c40c0001c05484040c0c0304003006245c28108500d0041c0c0b028040130315051a15400c1941d02d494101c0003003006031154005a80240400c480e100e0895101c840c00c502c004d501815400091140c204048014505014181010b480e1002c958000800d09181260510301548200d194100701000d030b078249125903100d009090001e8240500080e4a4440c0140300b040322075030301e002540c6201c0c803c00901030000390140c07907203a403140142802080302c402164400d014a0130b901000402c540141701b03003412241840003070b05082d107407943c5040e11a4062500e1004041c2c403002030710440303115a00100714261280d002002e286002c452a5241400001c0909080c894810100520381c1c64a50445251204402903255a071055900d20142400381d040042e00080c0b50003804180102c181005134140c0b4001d0302201c02c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 70927061 1250 70925811 70925821
    0xe0a0504051501022808090a0e0405070305251502070f0603020414031207080d0e07120302010524121005070309050613030905041e11030a06050102030c030316110118030305 76
    0x1070243c4860a140d103201d02c22240c1400840c1b496009804a0800240200c5003541d59140380d04a021003620140c400e504010010410400d0400100c601c3d1048401c0301c440441e041c21200b0881c00d02841402e190b60001441d060842c0c0c402d20095000d09055143e04c2503050b00c41e04001c00039045402a81044012999484100c1c580080c080c0041e80040c131410b46001490f030707038001082d000008020710050b1500701050b9034600500c2004060f0244103031510303488240d41402402e441003c2c12511a40c500146004848981005000c60340c50041d00c00711042001140b070f0074503000351440c00d0540c00740740c4800c0c460121b5043e007083c0d01841c010f0048503c01c0d281d580882c014002201001808501ca841c820401405c02c1d81050041308540002d030226070041c1c5a0309015140c0300c20f00d03003c440d00c002040282d100000e2051002070300080c80194117000b55101d02c1c2c0d98030305c0080c0241048501441c0004902c0348201464481c0003c540028031003455865000610401ca5141c1100485e0910300011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 70928311 1250 70927061 70927093
    0x1b14070501020a0b0a0b060c011b09150801061d030601030f0b010803040602030a0e13230106050a0c020d060b100306060f0302070519030e120303240607030e0a050405150102 76
    0x10a2283d0400300d074000310b03101d840114001b0010540709641016052103900c000020a101d041d01000c414007084042d4950714a00404511407600301000303030169951120074ac503512030a02d40c1074810b141004070399080310500e044111403030400903560520030b51001204024801c051101060311807400d084150362108001da40701c0c00369000d07040040c1e01c2400510403079881200c080c810384070f0141c1280f03207880b014500c50043e501491040000650070507480c0c90318507030805282d4010002c600d040c50403d10f0700c6000808003180100c3c040c1c81790410543c00c80602031980d00400c0d0041000707000342081d2505000150180c0680d1142d580410f402c0f1040c80c07400c038040d000b15240f1652000c0900b00110082c043c4d403105081030b04040e4100320480c010a801512103040380301c2d030424a100111f440b881d00d401c00d0b140c1801c131122910140040c0f03c0341940c03d51035800035514403c0e8907042025803584842c020422030f0b83c2e03607400250302a05100a02101c207035180000f4004800a03426507031141301c004555 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 70929561 1250 70928311 70928323
    0xa090227121203060604030c0603021801050a020c04050402181305010e07030b0f090f0706030222030f150b03061503060609040209160c06090303060501090e0412050a1b1407050102 79
    0x59900ca800001d070301c07034210300b4910046610580081140707051070f41b80c0d2944020102e85401402c013081c5e00080e0300488400f81c12024200c0c40c0246000b030702d050400c2c21b000f51218134280c0039a0103291a500800c0c2150346880c0c03c40b41c00c61107a8451440340c03a08081c1c00084910a03441034480d9443c014030541c81500200f0716a0075030390811200041034660303c1da00c00e5103900040c4001c690740942c051240d6030f440d003480040020821950701603100c140503e403510f98040100f00e240c070b03074401c88001040003e442d0031414031040d40114042e0a40062a10a1006095260010342e814041c1c401000110703603440038001c070841c1d01a011560380303a80e10028841d500106072006544005400000740681d22241c0d2401d0f14078a0500d002c020b030b210280d4695041d10035189084010940781e0b5002e202c1564011100c000038828416641e0640c18142c6402c0440114080700d00c1c05c01038009020314100f4090b40c4c2c8100490207240c11510140840d04021a400c40842441101c03801864800203c80d0f10009d10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 70930811 1250 70929561 70929589
    0x60909180201050307020102120c0c0d0306080d1103040f091a01020a021e010c02030304030803070e010f0e010309080f13050411120a0c0e030a0318090204230a090227 73
    0xe03421000103150010340340d540004004204664003040b41d00c011510500c0484d00624810b8011a20f804c01ca44075182001d18528000d000c2601c0c10800704012000000c0d40254015a03082c49000082600c803122b085100383c4c2c0000880365083d2400103139106031903110f6811041e04000c000b03200c0c449400126150f4502810103035201c0c0308240001000d5200e10302c041b1148105040c055204103866000c80c1c1076821660060f50485400300801c10100e4001c1703081e0010040918003149021501030010b40404400d1007100c5c1099607440c0728104001c800d40480b8001340c0c000c0251510f40300084d81d84004001c15004650103541000100f204100350301c0241c0c0c000032100300c503220903075864505600003007148500e10010088100328034031080e02c050144c0b0605500a9480803001d10003240300085110300c40c2d00205241c0d10410042142c42c0c500c074006095400a40303406d820340090344000980710b40c0a6040f1340071b00ca100113640d8200380310302c42c0c95224103280b145e41c19591100b8502004210449540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 70932061 1250 70930811 70930841
    0x10f0905100806040b0d061e050103020105030c0d0b04090602070203160b120a02071407030c08060103020108070809072d0e06090403050c0f16030302150c09010c0c090e0106060909 79
    0xc8052098003440c0315a42c843d0028000054015001d000980358055038038050300c0c125601c508d02c101c100c402040102e9110030b0702d9014041549107030f00003845440006c1c1599842100490032140e0010660400b80201700000e006208445003400d0400080d482114128031a10801c8102c1c801034803910074010450700e01518140c2400c5e400f0355058071840740200b0490503168204a20400550250703110300038110388100801d00c0c1030851070004800c460540000050ba4002401040180e034001c0a6030b034016914980030b18035455151840d45061244d812411f040302c2000f555001c03070300b8034a10001e6500701c40e880c84000c075942c4085405030303203030203594454000070081c001401190041000f4168109040110303503801d074100320241d0420040c5040801e220701c2ea0078040041c180d04115543c00b001c0381d810580b22030700b4030401c6000144130b040d441d2414096207903400d0b41070041c0d00c4218001000c40000501c40380d80500f20007402419940119004a518450f011507020018403e004140800d50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 70933311 1250 70932061 70932079
    0x906120c0e0d03090801021218030412110315040501020c120702030d05130902070506010501080c1602091305030706021306021507050f0903031201081c09120201020304081b010f0905 80
    0x40148000d0707152402d030a500780a00040d0000d5042024801842c641e4000480510030741480440c1e15911281510319001070b038000e00080c0b00c0c0e44180740c029074a09600400c01c0284050400200e030502c00404103400140b4104010001840419002091103400e0101601c0490306243e21210306030141e158040c0d050381c8800070f000c8500d40241c0040156181c20110000c10b2551803941074241d81c80392000701d034036802620042015507003101c2001c2e000f55100446605002e4411408181840b14000180c410500d06c004501d050110410f01e805940c0c200c0d0507680c0d114100e08046020f5400011003a40005140c0d0001030803e2010525a0400092408088040c3c85099085600d85c02c1160143d2980e6020081c50b2800d590030070041c2514203425505290562501c009581401c0c20f0309200d2041011140d04c083c0e1032580300f0301c001e00303440b08000071580e0082c0d81d00040303146018075080349582d0310500c100d041d4844003d111400c3d01903002da841407510350b40c1c003900301c3d41081248105a0480064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 70934561 1250 70933311 70933337
    0x60a0f0b040e0a060c0203121005011403060904060906061509030b0c040b0301180605060a02010e070501030e0309040e0c0603131203021c020c10150603050f040c030b040f02030703030906120c 84
    0x960002e04200302c0c1c920449050640d014040c801041c0249c45170790389000c0901e010030055802c203014222000c01c943c1951300394a4508045108144018401001c0325948c2210b04100b10310742e8040c02c0908422240e0203e5491a034001801502030750109865259254000130781c1d229241c800c13030b41035881c140041d038110307445d008000c1011400c1d402c84080c5070b03844840100312501c44402400c803055450b4004034031464204d03100c83c10146c1d10f40090781010b05100e000080c0700b04c00001c407003042030103a500144000400c44600d042103003140240ba84820000300340040902e04112603003407180104010a0229800700d801e400300c1c419803620303004104d248000451800f965034042d01c4040511015241013690003117480f0221100440c07441990076020505110f00380d4544111580800f03550103010503420603480d94210366100d0303c001400000c040000404004020010300022a406000c9800550320791401074061020780c09510001018030715112040f000034082c0030240364ac5521010b010503d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 70935811 1250 70934561 70934573
    0x1050702120a0b041a0a0501050a230a0b03061809210705060405030c010b0109030b06040510080f03030109051302090601080a02040f1e0609030302060606130503060a0f0b040e0a 78
    0xc140a94a05809040d4003440440c3c90403110911807481440401e140a1550442138240c3c000948260409440c2c0300051000e13840e171081c52010780f11110360074141505810018640e4080d0300c0e1641d600030711001e0000038415480d002460180c0000c0b1000302d640aa840081c100d4001c089903c5451a070010701c2600712140300d91503070b40c14114540a002c1c60004541ca072140761a03010342d4200c506034000144001c5000c0c0a204641c6030103001d00c0c00481d050700d1500c1d40080b400000e8546485140d542010909420f0040f003040000c08005054507148807000b0384807610b036042441031003c3d030f0f82800300150b0710802c1160b5160031917500518040c071b9519010011954208c004024000007a800c00022503099020f0169200521032852110585002d00c544409091501d0b07000f00d040c0007403042c0a10000c4e03008138125902c110196201926040500107154013502c541d400250140901c03028042070b091503030808a0000718000c4103110200141040c00308403003210f861155a600018038244c00078075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 70937061 1250 70935811 70935829
    0x3090b031b130608100e1f1502030405030105060103110a0f0e03070e0103050d0203030403090612021c140105031204050103020c0a120f022116030908060106030905100b01050702 78
    0xd10320540246404846031206955846840e01422480c1034440030460150321100c1e15502008149420039081c0c600318000607401009000c040b07000e01c01f041d0040920a40300051401807003c1d04241480c4001580040d442e90b1003402158040d5003098001501c95020340904902500d96016103840d141c203603003040704c3d0050500c50b03140402c000d0107070000e805d81d0101b081030098a07010300e190400d94950310306603260020704d01000082d5003040c41000003003a0858840380460f01d00b0706080300405243e603920002841a1a084003031003442d00e000e115403007801d41c07220804450202d9900e92030f90f00c0700c0c105642d4a08103c00a14116420001032000f54070a0300500120b05869007100d1803031602e9903d421003544a8008540010156010b02030166410485c0072032221940b099040e0281c154040c1d03030a41d03c2420003001142400100c500304052103941e00b1402810024142e440c44d586610f0000d000d8641c030b0409840503c03511003541848403a500c5681c44a010503100c00d484c2c08016800c0c400e07a90 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 70938311 1250 70937061 70937071
    0x50106050f0c070306020309030a020601120804030b040305070605070504150201110d0f09021f0f230a0c0c08060105031005100e0415091208090a0f0204020c120706020c01060b030403090b03 83
    0x3c09001e600000065440c00994011404c0b000a95124121a10000c3c03918005a00241c440303d030200907130003c20824412036003070701e8000000c00500d54840c00c01742c0382449800310041c8194906130411083c0c0e0b5018001c1c2080d29044032510360200146a4100e0a0790148901d0794030803502000440e114400e203520510452070342610114241c04503070005075141040040c1204100340300000003a40544c07000d4a501d030700405041030000034010740e4a0701d150907100c064a030010103002440e9800e080c0560400b01059a001c101c007c072036500d542d1280c0d10340d0800c2c860300307010b441580b080d4500b40e40c05000d198440c01d2504403242e0307140d01d082801e1800c808003070000d41d81d80e5101040f1f055048001d001d208200b41c014003007a0016174540d24001d0005070000c150000340d400c20002000001c420038114842550100c80c05604e401144850601b80b405003042d41204d810700007146010000030307401901001c0210002000f1440d0ba0b548a503010344400c6030020300040e1000402c0c884800500c0180d5002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 70939561 1250 70938311 70938313
    0x809062502010b0a0b130b130e070c020d0507060807030207051504060608060f0f0604091a0a060f0305061b04080601062a0305030a0e0705010e130902180a050901050106050f0c 77
    0xc3c070303400341c041290111a0b0b0814459010300141c0d50380141e609a00c0d05000300f10101111b850311504100d804003a840c28011144414460310100302094420700e04400d07095001007030441d0b101002d25080f43c2e26441486060301007441c190005510a000744261080d507500701020f442d1303190124141c40c404102c0280111209a61040049810030080102601c5005102807450381424486105030050f100100500d116508003a03803130001410180729980c00f690303010101c01603911102418400307403d00d908604c41006403003800100307008c000a9240e004540c0c03c0600145a0b41d201070203940d510941c043c1244130b5002400421280e807207a030824504204988102040c50310000403000724102d00c0303e00b50000344000c01400320000151082c0720344201014024aa5145840300103406140300480140c820300c0001d2180000b64010b070400041e00f0307402001d44000d00c00e1850030101005041d01c00d88046440c1000140840c3c0051050b18141c1c5d4107034a900303044c0880b070840f0f000c00e60701c41d4200b6506 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 70940811 1250 70939561 70939571
    0x902060d0507020607140702011b020f0301020c03071505010608060d080717040504180312020708041809051c0e040e0102090a061e03060b030c0903070b0a0c03080906250201 76
    0x10022062103518042c0000e40d01900b07880c10100002004240207011144250008001880c0141c0c2c00420f01600c02012041c203981c441024000100c2c50603040c072040707805500015240344031604c04402084064410045008620034030910b18080390030902400c2d011880d0080481d03800d1400c5550459003621a45116141040b190b6032007070514035074140c0e15044140070806100a20701406544d1045420006502c004201514000c250302c0c1c420320405a00703503000409200b030102d000211800b40c0303000d040c0e0702c000d401480d207081c0003481c00342030544540c01030b0f0030505c1008006a080180325501983e54400d601240c07000c03c0001d1545211600a44d075080101030300c0d030748a1480c1d44c002080c158490308003992007440032488600d0221005400c040c0b03013160034040c2c010201d0550360001b08020304952991840b4021034a815041c3e00107105c010400310b14880015449062440d04601c00d6490019503124904815510b03401540d000c11080090905a0000c0a85000d2078410300d01c18800825 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 70942061 1250 70940811 70940827
    0x13020306030f07150e0102030c0714121614060a050a0e060d090b09010507020708031e0f04030821010602060406090201030605060406170105190603020705030d0f09051203100504090206 81
    0x1c43c0c0b000550150b032640034a02210500c50740c11061031001e0a400780003461409054190f0142c907980640242ca04481c140034020200b074403800a007808c010400e40c12114441440f014442c80c04000c0d1203015a005605040d185850901a040c3e940032a22078a9042c200036590000740c541c0555070b070308103402c04014009290512b00c103004643d03056015038140f04c158180024041d0030340c0c8009180500751341c4940410052650000129a401c03178900988400b60804607006410a11840265441d03544d004a400300502c25071074000c00305080e130000205515030042118400d4400240309010141e046100090040b44654104034419031051400007441c40d103400001c0c4040d0019000781000840300c2040380d14920007020418094107040b80c012400c9158004000d07041141c81c02188200760300800c0c0c81e01046020415180066280c003c01d01c000068201545c004040000e41074030359126484040e072540c0c0060301100d02504101c82015500b81c109000d1002502d03c4010481e0880340c10005a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 70943311 1250 70942061 70942063
    0x501030c0801060f2102030601020f01060f140607140610050409020906010c110a0801020c0f01060e2a0406030b03061609150903020306090606010f0207080d120b122a13020306030f 79
    0xb440c5c0072201c01c401603c0303041c040002032078644012000000b6030316014050201111680c000011100d240401094030100c2e0701c0401c1190043c0e0034000c0c505001c2500c840c907550b002184161041030f5250385007014540e16401c201c01c1d9100988065045003600c000b0a000d54452940741d49014050384050344c040007144080f5074108440d90107490113035404240c0350041c19050020200c0b04072494001d00c006070400c1154010404051300041100003008072192580601040e40003010440105a640701c65513030704043d014014a003161446805401d0004941e04441174201c06080d0051355181383e02c03414141c200001203404003942060041c0100e0010040c0d0f0204a1144a0705c8907c000e4600b901f490b40025200c1c400b201e5451003950410903050101000000b60b210036968540b40101c5911081d0030783e40018040b0a503003070b400c09042a008120850001020b48294250b004165003500380b482e4918101013440c400c1650141004981c01c02502d259005581c11086c000c0503141c2200e24005a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 70944561 1250 70943311 70943357
    0xb03060103080318030c250e0f0f011d190b04060308070b13030f030207020d050a03030617010e03040306050c04050901030f05010f021218210904060501030c0801060f 73
    0x448030321900208004d44256001242200164550015801c0003400460192903241100c0c049a500c002e804400c0e00c0044c40c00c403607070010800001e0a840d2810701c410110b4901c00200d82a14400e580340000182c03070011107035507244e0b000c41c4020b507800c143c494150341144020f00b00002e070340c455120307140101c8540d2076100392001140718984081e0380e1034142c9800310204100412400e8180010410714010070f4100c5480c0c81e05a605142c0146d41c2d42c528030026071306c40000307040901181318071741841c0d04045d0190b201e40140c030905800180ca070b001c0002160f00744c400810b05c03654580c000303010410000324a500080e4001c980d80600b64145a114004180d85804c02d900a80303026041c441c860092110a01c24004c21200d061419450102c0300360000c0e4000f000500b40f01800f5070214030641c0c883c1014001c0c1006409000e0020342400403407d589101c40e0040d94030307a40300f2407a04200044a41c000d10441807910410b40300e0384c140b80e20b4481c0684800c15207203a0903040c49103010040c07407208160056 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 70945811 1250 70944561 70944563
    0x1e0702071e030507050906031510030c080604020a0f12020409060e01020c0d080106020102090f0f040e03030703020904060f030203070611160902070b0a050606041401140309060103030f0203071e03030b03060103 92
    0x10740101518504000b481c048080e4045406412006c0030f1241d03a0701d001c9428002e00c140b40d5641d04094840b0208203104e07910591004e007034141c24010106440d0780100d81e0710302070340c02210402a160348a10401c2d11001091103031020b078000400d20f84005040c41d070019200213014040c00100601000f003510b0980e40008900761050b00080c1c05c502c5000d800260490140c00035100850411041ca00801c0380c8401700381141d807081800004d10241c0390354640001040e00c00074001d4030b03140e04014402030040c0d0040300c045403113036007080808070700c460005003480d080b00c1d0000c000741401c0d40b8046096900181d0354210b4541406003030001200d192400f60890018034003040c0051b69060319041030700e0f1210307014100c1c94005040c401484000d03920641504c0556069182c140c40310f001800050b076114110b1300a22440110110400c542201c000c04c5041c100d070301984503c0d40d0040905001c1361244240e42c00180044050080900c0c1080e50032111140184a8100014a0100c81001901e024000d900c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 70947061 1250 70945811 70945859
    0x605040302090901140a0f29030f06040f02010f090b07050a06050106030e0a020402221403010c0804030503070e0f130c0f0507020a0e270106060f05031e070207 70
    0xa02002142401080340d0351141000700200100300741d801e06840d101c00068035100b2050f890308102d0030399401592000042c00a0040303001d240c2d0f800064038401180d41c010080d40b02c0d0003210ba03844000740c400306510b48116417041c803180b851400b036030054880d01d031056040020041240d9020522181400007072409500600003421403101914254090b5881600312100309420301c0185414401c0c005900d04025a04417409038592030348110740c0d809032840004005e2903620704140050240700c1031403440c010880650091090410410055890b914151030040000d181000040d50981c07091030b00c011104801001c40c681c190300040090014101d000840e0a0075540c2c1d0007526246400c80c0f08060b007000700d82015803d01d5000d4000801d0740e0380034480d03544811040e50010701c44900c00314003410460107030b550400d0884500400300b4000c0100d03016034001716215040c402c100c1d9001d0002d484c41011041200e107210801c240d003d40401c40302400d42030662140c2c0401181d090300498035160040362640f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 70948311 1250 70947061 70947067
    0xd06050402030705040b01120c110a0609060f0606090902130b120601020c030706140f0706181104020301050619200c01170f0f151806121b0f03010b04060605 69
    0x10040600384902c03648103c4c8038602d04945403c11fa60458202e40c3c1f000c0154000003503024041030b0a461030301c0c83c525102540d0151000038402c02c060765000b01c00703c0d03000e604100f20182c1011408411207616016581c04660004c5c0c0c2041855819002000300c0d080c4050300701d01c02643c0300b00541d441d41020001e90f441d0003020741040f009590420020112000441c01414403614000f40902007084603d503205000381300003210200107500f101124819644140700f00401240d104143c50840004c00c0c08407400b100165041c8000c0c81c0c035000b81c034181c0702c00810130b5207040b000800f007198131404100c00f8003d02941141e003050401c0088410318180c017404000d040e440d0300450004105d075105002c1110f4080c6140c09122a103003c4031030280d844500d40e400c8524a46509038090141300342003075916403020034200f00c0c0d58240c14445186002d00f0742619203500d1040c2ca1500152a8213080c902402c40100001003842e035031030450041e100204026000013401035000d4042002d444243c0c00a002180c400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 70949561 1250 70948311 70948313
    0x3070504150206040206030a0e070b2206020a050d0804030c06050a06090b06030907060f020a0c0b0a1d0906100905060d0209010e0306150121020a0c0302250b0706020403020d060504 79
    0x40c00c051500714081c406400c452905a0015421340000b0300300e1540683d071000760806205003001200c000c1c0c5000d00e001034841301c280203280040d884004180c0c0140c0c0c0b80382d20000b0f0450002802c0100107511002a107202c0420007000ca4a41c80c008000b80c2c01c1003201c91884001c201a0320071a801403031714000c00b00d40d003800d014485056a90300c0301c016000d0f1742d0400403c4207010001c42e48000f030b1101490101100c0407800401c07468a030b81c503235000c1d0103c082c904000a0b4003a0b1340c80240f05880150711480c449003800240e4084440e4038a5070280c028945c000054098a061420804044a80e00b005501c96844101140307854004d0102e611086600050b41e50103980c0041207420b62050840c0281164542910340808400f20440c4150610003003022155000c0910310004031500c0c2c10302002c640700c0c00f0100008029044544082d0054040c401308040c100c41e60b01480368552290700745910400340b9106e510704540c0d00511050303c2140d030910001c8010781d5940c5042100c180100004a01d600349 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 70950811 1250 70949561 70949579
    0x303030b0d0809060304060b1503010806100303051206040204090608010e150903070f0302010f1811010504150c020301060e0103052a150904090512130914270303070504 74
    0x840903091284080c1190000007501d040101e80c41100c042c1c2c1c9094aa80744c0c0d1412002038000342035015032140d226100e220740c20460a02542c1292440030844406480d041c2c0b8011240303c01e4000640060420040d1402480d001360f03840da00103130007400c014501599070000f10100e59417504940307445d945440c100c1081020800a402c501ca06510300c207281818903440da140c0c1c900ca8014001c2c0b0b00120b41140009150003940702910300c80d10751310140000d21030342c41d9000e41c2594403403086440502c0c51841e007036079511078015101915040f00080f020102119826a40300c800c1c88400c0764550b4075007801068207010011901e00a511400041402844080701d0031240e507031140410840210a0040b6859030765102c003200e01c5000c03030300595941e4007c0b100100300039100748600603120b03109030f000c1400e184503140001c00f08c00c4051131106d103841d900c468004041e958041d000008551150b00807c46040907459403240c89000c0a00c0c03044103545448034542190021a102804600046020408090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 70952061 1250 70950811 70950821
    0x30a051e060603030301050d0308041a01030f02030d08040309140303070f0c080f0a0c0302090a0209030105101e0305060402010f051b0c1507150f020706020d05060a210b190c0306030303 81
    0x4403c401640c00c660402d004036049081428010b401c120b2580041028010540c14044802e509001051499a128109071900490500c8100c1c000e1003581040d100040c452046d680c000d607030503943d00380c01d82c0c83c00340e01e414a55090a9102c1c3d050200304103141c00509074134911801c041c46409104203480c500086603041c4107103c0300c060b10541000404400240284000406880d070455080340b290300c80642280c0240181508940c2542c07901e018401c20001c0e140541003241c08086c40b1150071541040c14211840d500c1c84010034035405900807900540c0600d80080036101d4901e0702030704100310032403a01100042c0001c1d0b40e4543d04000c1e00e110f100e00700780c0c0d80402042107031049035140400e43d94a6034110444072400001c5030796514503c500071081c680450300407582001d019910b4040207900c072002080c0580d82ca602c40d0022001c0003580755003500080301c81c995101800d0164000f2600c2e202d152032001400000c1640c0c159142002c8084e030340c402c1028540041e44c0c002049802d40c43d001e0101c0e6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 70953311 1250 70952061 70952071
    0xc1002030a0c0b0c0903011404050d180b070f0218090709020a08060f0103020906070b0f1806010902090112050108030c1e0c011101060323010c03060509070e030a051e06 74
    0x500100904106a40c00c0b07901810440c3e03200480c006156101e101801242c02443c1007a50305509010000d1114554482090300441c000d0060304c9405950441c159400915100c0c521314100250104101d103004120291811600440d1000283c4d15030794009a01440712280e241c40316103880007407140f003000412224000e000034042c11890b01c1159000900102d4000f40003034070814101c400c81580740d2007a010b80c2d0034140054250381e21060f881c0781c101100300303080700c03844600c0d48403100240d4a58405e19170760f201515201d024003030350390130030f80900d003e9030041503190305100390f01d540c0450b51442c070300ca118004c0c6200406152528901d01c40141403005940341d9083d000002d0515080c210b0740410005004042401c248d0305181022441502420303a41d8009441503950118202c00403000c045072000140c031340d10007004071040c2c1c000250120303049405401d400090b28000107052500610060990040c010215a035940d403c1d511580342c024007801401d801d003000300b0880140942088855004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 70954561 1250 70953311 70953313
    0x60417060a090f060507020a051006090b040c0e060315130203090d0e0f0f130203010602010903091a0a0c111509031501150c03180303020d09090507091401110f0c1002 73
    0x11071907519015100d0f078404030003070701d00b55562001c00c2c141c9000300810316220742c4c01016036400046075244440248407030f101d03c40c105400e06501c89090f107840d00c40d04400c40c1903a110340d510313645600140a10340c0c0005000f01d416201000f030a41d141d43d0307610300715410090b80041c0940e0ba0300d4034081046c1003808822400b0306000300c010100e440c0c1d9560034a64180d4400696442d940451044000340b00b8080c8810240345141c40000080380782641034010081c1c140c007035220360801c43d40d140003c16100c2c50300c20300074801c404184100305110748541e5050100c50f00482e021540d00341501d0004882140900c101031008400040b0050142024452202030719403581c00103010358501031805152a00000f402402c000c10100704030101070048030402a4106161040c2224a07128540039550341c10805108000c00c904c1c100014040740e080c0503641c400c074415500c096545103850389041318181410546814001440544401c400041000f004030314a000c008010210680e4240032400ca034840200c821 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 70955811 1250 70954561 70954571
    0x7050d090e0402132409060e060312031b12100501121401050d06060305070e27030702010e030c04240e040b0c0322080307020f06011202010c050a02060417060a 70
    0x1da1344000b05403424903802840840c4250300204000151100c01000d10b01034004150042016070741a44240d05940048001c0d10b1603885001c1015564510224540c0300c07443c04000084044108600000c1c0b0844072403500c6003030150390801d1216000341100e42442c0402c4945040100b9039012500100001807103078100440d803c03454009100e018140900b5009002d00b00c107000c204086a40b00d0300003035030003000b074404140d1220910b60403400103549a8054005428114080c50002620000c8021540c0001d520f880740a90040d00c0c450185140547d0501036001061500d484034047e020601e00c0000c01c4980c00d00c0076076850807841c0e00e26000341101034441800c01001070400b941c81608030358006083c1d42c0386c3d55481c107203d0b60420f2002000b82c01030b895203e02800c00049001542c09541d182d02510b079003e00002c01a95152000d1060503200205180e140001d94001c20302c40320792a00410950300802900d8010400340d901c03507030042c0102c0c200c03141250009502800299046101a101806 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 70957061 1250 70955811 70955813
    0x60108070e060a05031902030117011b0806240d0204080f030a14131a07021c05120703030b091608090102070305030114060c0d050a0e0904120e0a0b07050d090e04 71
    0x800e02841d26080213100c000004140304030b082d010201505180d01c5419035aa68507400b0b907040302100c0e001e1307103c015030070b040680c8a103600c11689001003a0882d41c800c038030703075a44008000d02035059503201001e2030340141000141d80d001500034400500f548030003581d102d26100c00d440c1b03440c074640f1040405400601400f181340d640034080400402d050840c161321030403074205020720603035281c0c00500984000e051044d000e445034805480054001c45885507443c03180540c1d100020b01000c0c009040d50020400c500b4242812070140080b64000d150005141003100e0100708002001d840204640101c440e801c1c80c0c4030b6102801d00e40c42166800254241045130f034016105003c10301131003c0c607520340305400740207894410680e506d0280d00030484500141010000c3c110b0347c00318800c0c0c000103c1040c8d18005500b0718110660055501c448200000585803c007110f0300800140c54940c000ca42032800600b05202380c02a0101c24025409800e05414420b4080d124080c0c0337601031040d050440007080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 70958311 1250 70957061 70957069
    0x9060e0a0b0d1d1903030e0303090c0103020a0507140601050301150602070311150d05060306010605090906040f230f010e010b091203041205070e01050108060a1202060906070b060108070e 82
    0x51102801c880000c200c80006844040c800101e6804000461280c4c11003040400403180a4410050094500700040100c82079415202e1000300c40b0130145500071801c605165121f9402011445194070305181048965900c514440001108180080e40310a006003e645400e108180c480e4510740345441440303140c5003000e515040030f40310140043c141e07043c0100c0c083d200d550515417a66401d020f510341d0b42d0380c10650750303006002c1a0f969038003900c20100081441c1d40035800303c0314007072401407446400d9944c6008000251101a4102001c66120547c00c181c04216009110709500400580c400601c2c01480c103861944050340058203010701100100200e42c1c46004541084a0650b260ba00d00607594000343e26500c140e03031002051aa0b810a5042480340105030741040c2c40095410781483e0342da420044403010420340d01d4a51201404200f005000e00084200780c002c0d00c042c1165060005401c006402c0d41c11101081e80e07035170306441c2001060f681c846a071a600c602207091041814940c01c1c085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 70959561 1250 70958311 70958317
    0x50d051608040308040203030f0a0201150608060d0f060902060304031106070201060506040e1b0313020f0405070e0d051203040b070206070903171e0c030702191206050718030309060e0a0b 82
    0x180c103000c080c0c0e010900391f49090045500201e103010540ba51001c100c84001d008203142008000100400100801c1603845406268020140149120682085615216503da400343c8084458075a2441c2100050312107078003841c444d9010761164a0000c408074000d6040000081602c000c6914103a001d0200e60317244000c1c0e4003951300c051003072600e55480052040130255114043c1000301c80200800c2640c001072091014850f20a1340d01071400d00c1200c0c144401d4505c20342d106070200341d60320303241c032820305001c00054021400389044500020030452013070842c1c0d00960f02036541401150030002459010040c45802101d03d181c045001803958860130202000016105111000000c0302c0c2c1e5101448641c400f001c410900301a60340b0068581001d6885e03020303040490040c021104040d0320014000b10310400c84170581c020a030401056911403000b880000d042e10306001040307003405280304d070111007080914426203a080a0354105079000d4850f03882e1440b1540b04141454091190642da0410707 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 70960811 1250 70959561 70959563
    0x206040303020d2306010f02011503020f01120507260f04081303080f0316020a1104050a1d0a02030105010503010b0105091e13050601080601090602030922020406050d05160804 77
    0x401a265001d1594140150011500e0441c0c10840c03500903480c0e4440c402000b1703005a101f6242c040049114101c04e81c01d07111361003000d8901e0540b0b00805c10260414150102c0306400514281515003424100300045407820340d000c00000711100c1d000710819090309000d41414551068500d028944000310341c0c2589001040100356031000300d400449203031605280400345600990b41501d4000c20300b0140d24980044880711003881c1e85400188245001080c5045550341003000303648043c00c00400c0c003002d810040e10801070340d41d503a00c1c80300048080e400c0d1207440c51104000351a40072401d00426081d100d040c3c00c800d00c240d02d8a0400791250307030024100c0d04680c2c1e080d5104160b00800c2c080c0c1c0b06500c5802111a6080100c10300310039256000350348040d205803000d0700c0301c2c10603031561401151944200d01a40300568004c0005250500d000c400b01c80289c40b2902d00d40e81618130801a20090b42c0007036000ca030101d6170106001c000e032a02d40c09055801400100c070303810040c030f54a800034942840984 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 70962061 1250 70960811 70960817
    0x100b0301030b15060c010f020d1a010f1d04020d0f0c050a0512090a060e070303020111030f010320040c020d020105060415060f02101d0c010309081b070510050301180203010602060403 80
    0x1410351321035800341c0b85409041c0c0c00030030940351a1402c441c013940c80450810b00300d40c90b10082da8450305d4100503500e99400e06039100185540d60034002d41c0c1138651550101c15940080358070b09491342ea80d00060080794051100480c0301210101210180e820740080342c030a026051007030b030000790390207415916540c0798004103a030380381c451051150502050f020094509070804020705600a00041c1c0ca1003100c0c820b038020852900464007100d070341d003c00d6410104810b022001000480d940c0209030109030001c03a0000c10580c40d680000d01210107540b647c1d005038010f884aa02c03a00c0d028401e0580c014030030754050080390704006035606e80306e42901a0310f0502c1902e45103258414420440440c4142140e1020016644450503030407071288580394440780e0307100d902d08010352540700340141880c0540c0410210f0502d5494051040c126026660740581841840300006d01c030760b6003914241b14648141ca566589504011140b0003091100d01c90894681c010401000203550001c3c1c816031007038040c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 70963311 1250 70962061 70962091
    0x501080a0f0e030409050405070b09030604020103051e0a060906080601031203020705070b040306020d0b01022d0a020a090b1021020a05070221010507020703170a0201140708100b0301030b 82
    0x640c95074002c041c80700e80e824440c40040f40c04103031000503521003400343c0c1c00307981102d814079910700e0340460302e1103070250680e016000980403c0040d40243c20850304015280340102a0482820441104040c01c0f103007420055290401040b4514031032103104003070f21981014104640c11500c0700d00c18000341c920300034105075000802e00c040c4032007800b02c800a092800b03c0b141e5115501d082c400b010b90032000300d4000892806c13065014942c00054822450484411206000c0c50f440b1440c8220045481061025004001240d0010b9660000c1d001c040c01d040f510005808000400340442200c0c0da10b0084244030b400400728060300003891021010310481a00581d540c050410102c44a015944000350041e60f201204403800c00540c0380d9000e50f19100000f00a030b543c802d00200c8c0d03114198440545040038002c1c81c0b85540d10340d8001410180c11034000400c802d85211b040025610b41100c0c1140099826018007421b204422130304001400c02516190940d415030f1501d030400d000151010001102403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 70964561 1250 70963311 70963331
    0xc020109030f060b060a02031905070b0402040b060d090c1a07051506031603080d0b0109050f150c0313030c05030a0804050105031003020312040303110a0f02221505090901060501080a 80
    0x54002034282e62016002e66111407006d01c020b540c0360810200328050b840814103072074100c0e220b4410b54401d6038104200080e0364880e40c0a0000030000420100d82059080010703451219090080d084954440d03035116881610740354110300c00480c4940d242a840f101000080041800010070240c2c260310b4110003070103501c860000900d1f121004202e031070417188400e80003042c40b20700d4010b444030320290b00e0705001c0300d4070729401110f4490007405804c2e4040e013020392228043c14040701c0c0d4401c1c0001c900c0f103240b908154040841c9140c01040e14108440e40180c01403007040315a03906a0000e00b000e4009240040040da00c03403e090045000762410400c021000424681c0904145d100079900642075401c1811580308110f102e030b0081c0416800315200b5801b0807905100001c40b490f20360707000f903166086403030350350300b040101d1b5103882403060030803038080282d0310110141c460070b980b541d0419405026640340409010340c0703440c0103055401c9a45004020001039811500c40e6900038204000083e80b8014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 70965811 1250 70964561 70964573
    0x11d031b0106120602070b130215070201050f1306110d05040515090a0905010807080304030b0c07030c0501050a1d06040201081f0b040e070905030703150f0e010203040b0411010c020109030f 83
    0xc2c0b60b0111003080c1080e50751106010040e4010062540900c0d0070140550b114a6914509015610300940110070794034040b80740d0340c011002d440d1140c4149040d0f03207095a40d0400e0815038022075010381c05402132040810104d074100040006198019000e0728003050a02d20262840c0586e1240b0340c00741c8581c01c1000701a000d60030403030702e03017035802403044882540321003104004001c00d028881e0709100720b00000c500385000100792000c80781d000404c105903a49000342500c180c0c00c020802c50903c10f5070400400010400c1c00b0780c40c03241d5107081c0009052641601118103031300503001c2d40380040c0c1081082c400540d0b80280110383c010103250b414240c00d82d2045402c00d01034050b03400112070705004600460185040211a8003505082e651041695218020035072207940f1880000c10720000d2030384240c04200c3c60b4000c40740414400000180d4404095182820380c0c3c0111412180800d400d8204002c010710b00c5440405000207180c580c581400550000c0c010354406d000c040c1800442400520410130 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 70967061 1250 70965811 70965821
    0x22051e040f0603020612010905100503030d0b030a171206040207080a0f0e04020c06150301111e0904091109101805090f0d0206010e09030f25050d11011d031b01 70
    0x1074045c0085540d15402114000c980000780140c44141e41060301141c0d000c480e200c125010b0340d030020b02440c6480521010180140032a20b05180c140c01181c01060101d60102c4525840e621802c141a0b901c4031808201d5007103440042c1501e20580c410702c4840003180380b54059a00c0ea081c14100845101d000b030005661148171480c80c50340c002d0000981d92407410700404c842e40a4090381007440e40019007901018241d80c43e104429641e000300b80300c455085001610310000b102e0b1805140c9140c00d0900020805407848080251f8902049189060642c1404480c0c40d03808481d28035103030078103410081d01d83c0d070003100c5000c002d640d25120000700c0d4801c1800e1205014058000c4101c2d24031140c49a0040c1d100c9400340301e80024030303101d82c00290ba264804401c840c01145119420313441c21401e10359959030402a2006191143c0d281e440f21400a141000080740e40346468550615401c00c08104500391400320784804e0030354500c01f17401d1107007840c0003041d2452528500010164140b1044000340180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 70968311 1250 70967061 70967063
    0x9010309060e151b090d030504090c05120604060509010b07020402040e07031d0102040530060a02131403030706050c07080403030e011209030807050c01060b22051e040f0603 76
    0x14a002d1042d10400390020703280342242030121400856a543c048000c989400d090440b00000d401000700c2c0602c3e14107901078000d000d12a05026042503100c1d01c0711401c4404500c400d50100303400142c02c000000c6c007200340c1540b0000440b010b000250130b0101090b40303150184a0001a908085600c000310759813078042c3c0e000313807d00ca06070080d01d00c4c2030711008000d004200180f01d001c44485000004214060086406540e03010f40180d080c0d600407002041100020001c0e000c443c540d9442100b00c00e4020322144d40246c518420260f1104000903c9003000e2005600103c0e00703038000c42c2c402c906034602000351007546070041c500052590313074040c604480340708800c0c0083c405031380007601008141e0040c9172010003441c01e0b6a0159040c401d20980011600d201c48060701140c200c0000420300b510480080c800c1d800000f00100d1440da4884075600540c10294003181e50000c031403000103034004070402002c018502200c8041c0d800c00000d44200c00c15403240035282c0556200c0003034081100349504054029 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 70969561 1250 70968311 70968323
    0x1090b03070201180c09050c0c0a0b040303020f070302060619030302060a0207020f0a0902031e060108150604090e0a060e0303010f060f02030909010e040203060f0702030a1d0a03030f0206090a08040501030209010309 94
    0x10074042d00d8050051549801b1745001c8500e4130300402d51600d000829503291600020003040700e43c285031079000840d18024811010940c080150a10002615015004c0c8034460303002845a41020001c00500301c0403011060b120408510342000480c0d40040d140d82c004031142801a940c40d000c1c000314005a8290440a402c0b00921500044c80e50065004600c01c1d548130005214140d40341c0040d0340e80c410227849990001d030f0004045242c81c50452020043c0c070b90010841c03842c1c29601d81c00c03101a2030007200e681c01c01750042c0020a083c440c0c00c4c002c40e0445512a0081d500e11340c1822905200140a40a0542040015880940102c1c000c2040b2035004000030300d1001150b035112440b0300302103800c4034103c0c080d0141e840401ea080d030900944600690150b0041c5080141a02017158040d07014280ca40d40e2305500ea8a800441c3c0725201e107080a0b40c0250b0302d0b00134028070040040d01d050b50240c50608168000d0103550049801401a501614024603000d683c0e4808400120081c0410560291034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 70970811 1250 70969561 70969601
    0x103110d050f010905070c0812180f01091e0201022d010213170105060f040911121507080f06040c050c01050c0405010f140708030925031a0601090b03070201 69
    0x41c82c100110010704890786104103110782d46d5000300417143c500044100500d03940c010300c00a06004031801c1078950020051800c008081c02d0850000d25110550151f4030240c2d5542c8a804180140409140041f1501c00d4085140515940c0000c0d511801d01540c0c20042e0340d99500461083d00070b10701c40c11086070340c600035504d680d640500d02100904e05e124080c0c882c003116540e06502c84043c000d251041100400a1081c4510b1030240000780990090032100c590201a811001d42c3d240781350200460502c000078502160340c40240d1080b00c1d0041c0562040c44208030400040d1140c20108aa000300e0603500400c0107444110240c0c0c46004030b8240104035401c1200b041003400f0071130007401c2125002d907280702c0d01d00d42200080d039007800c0c4480044c481c0e850400c0000f02141940b0015600004083c0484e100800000304401a20600301c0d203800100b01071480030010310140c42641e400b00881103103c001c107400c003903001030600341c0d41f80300c2e60007010000310024501ca4000e600502daa40316017415041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 70972061 1250 70970811 70970821
    0x120103050d11160501050d15230904050d05070c151809060803030112020f03120d0623210706030504050706020c15090d14010b1e010e0103110d05 64
    0x2885403880850300002400b5520041810710001414801c50400b1031920070600f814903004403200e0f808445d0148009840318a688220745400b2042001882606030301d6402c0480c0a441c2d00380301b422030340c1147c402c100b08400e100c0402c10101b02000042030f282042644d0746c0c131074503000b441d80599078130400782e4940c002c88941304681c000040c4221528010301c01c1203140e44130995a803c944050140b446517a005000622688100c1c000c7c0d912039034001003c0310b0344110000700080c58207030000340c4003441003801b1500c075007000c8581c002e2001800700012000784065850f800c0c025a102003000c19845012002c030440c515034074a0300b0f40782941000b0001c1da00c090b03803110341c068040d090503a0100d405104d00c010000c0c40c0c600c080381e40e040e40380e40200085a0400c03940301e268110b40051141c0f660080b40c09990800044e01a11100c0c0c9415041d00081414200c00d4100600f5011016140d038240c10709510507180303a0381c02010001d04003424240001d4844112140104601944030031100716890841486 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 70973311 1250 70972061 70972063
    0x120c050a03031106070513030803100e0112030306050306010b0a031a040e010209030705100c02100e0a1d060306040b240303070303140c0c0703080a1206030804090c090b04060302090612010305 84
    0x4043c3c0d0440030100c13000780c5c030f0b01c2c51308070744c18402c080700800b41d01d0701d902c018000203401e030f4004c3d90402d104004081295440d40c104e4402600280c0c0000c0c208145001c0e40703010950140180f40080034128040e100d590b1400e04100310511842e1154000c0603900c410000b480c80a00f11982d0010380080d208001c800700350281103000f90b00c0300600c50310a114103000040c0b00c1c40c04103402e442505c4950307500488040541d00b400010810100b15000b444400a591030311505c428040500420426804001c900d02001540d1071003030010742414001d0700f2020800001c5110340c425280c2021a045141e000218041110131801d8511071919038180400181d010605074141c02001e0300d007500c81071420094407140f180540d18401c1d60b0103195039800001c42080441d071041c02804c200301980c10414100d80400c040c08040f03c80701e42080b0741c51a00490140090b07900d0307100f40c0e90000303501d060190815040144105e02c0b8001c52048604154000881c6005621160180d40c07107990403031207401003546c42c1d01e052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 70974561 1250 70973311 70973327
    0xe060f07050f030d0b03010e03040b0f071208040201030c05030601080705090d08030406060e010e090a0609020a05060a020f1209010203090d0c030b0c0405011202160b060a080a03020c030c0604050a120c050a0303 92
    0x51138981c00d262000056240610604450510620045140038903010920b106500404654400703010705214010200c1e4000c00c5903810352959a0b0381d010140b0749480050220380c0d40c0c21094040000601c10440b00d641c0103c41d0036000802414141e4031000c803000010070034840e0f0440109500c902105120401001c1c2c0c0050080c0c406942d94940c2d00d85c1c84021460303660000f00c800c0041079011031b8000740810155480141c266002800701c2ea103036078607100803400da50b0100300160016030040c202441c48038014040601644008004e05240c6031010000035624000c0120180c42050307401324031410000b850060318019a4000c0d055840e13440c01904500042d0800e110302c80c00305d0440058001d40280601c00c0700c0000d851003902d241513055039103820100c400006d059580109081102040c0000c0412402d580f01344a68010101e090340c5038140350610300058807950003900c0a010030f001c0d940c1c0e02400c1c0c10039204401038101c1da032501d03030030304010082d0340340e2200703400840008010040c1540301140c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 70975811 1250 70974561 70974577
    0x20405031b0306010b0c01060e0115092301111006120c0608060a030b09010e030d090501061a07080a0201060915080d0c11010c0302011b0c03080106080103030e060f07050f03 76
    0x2600c020300020320703000d00107a02040009038903412240060002a03074180181251030b109400005165498102051b8042d20030381000d801c0004c0d000381d0081c52944a401140074000c400060002c101420b01c0d181e00c04010b000055040c041301452011603007604102f035101e901e003c50000e202c0b0300c1d0340d4032030156801b0714000203035032981d102940405c601e405400b20310f001d1500923000b008043d2440e120401c0c0d211029216032819501c40001524105081003e003203089403e481c000360803011450000d08481260f0300c4001d9420b00c10005101904c0402c7c29600860b401520300d65032540500802c03070040030300d0303008035506030700c0c00c0a41040e410464207004252100e082c21100c0c0040040c80c00d41d40041c03c034000030501d0781d0120b003a485652140c144455034502c03a000128004103007001004d00d601e400c69415000800b4411402d00f4160703c10b400a0040601e403c01500359411600c3c010b145640008280d4001d410019100c04842e6150040707030106038001c1c05855800d9503e480140d121391128003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 70977061 1250 70975811 70975813
    0x3030903150204050a0303030902030c0d0b01090f0b0306070c02011427030a2a05041b090e071b0f0510150906050109051306080f01020909240f061c02040503 69
    0x200d64500841c51003203038290b41005008691070f502c3c59400b01c0c081e0000b05802c98060003058180006a10b4030003030a80d10a10441e81c040da298100b4500c9000c4414504840e074610382040d6100800c0e440c041552508000c080c90304402d4285540010313510038040800410000d1000a2080e03984140d08917141803100203885240c2c003810f410742c2010360700c9052000c00340c4146000d9403918070061500300b00391400c11030818420341d015600c03400141141d051410140307450024460000540b903100b5202800380a642c405c0690074200703100c0003820340804c100f002800e0981c0e8450401030080c40c2d821100c0d8954000c044990a0344001c0c00d0308060070750343c1420f51010a1194001c40e9181081c0034280503900180c0d900000d5a140904104143d0554100c2d1105a9504d0f1404285000103004070340200d0441800075a44d259850140090b0040080c40070520a046c0304000707811001c02402030900c404204c580d1400b042d40980060414800c9000210100c0708100d42a002d240b20394000e4000c80f00110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 70978311 1250 70977061 70977083
    0x27202512031a0108070215040303060f060519081012030e060307050a0315051806040608031306080c1606020705100615080603010204030c170c040c08010e090f1905010209090103030903 81
    0x303401541c02207800c0c1c81003170250300034206480c810f42c80c40d00b07a160702501034030380031850720b0752030080303200f881100d0b0840000204e001524440c904040218903021030303c1c5150419580c03904401410031a2554040c1100d50034031000c800701130603c5803d400b001c441c5c0003031103a656070400b564080c100d41d00c6010040003203818269074a0594210407140710407109c02800e1501c131038002502c3c000401d540100003951083d5034290108040c0001c00c00342421900484112010f5030406070050034051000b00314550344c0b082041030400c8282c40d06088001d043d0312000242c1c66882034500b082c1170800001c0081400c44c0b81805c0003c1030a65030f030450784500300395140c0c1880390301c425042c1801d0b4400c5000241414000b0310082101d25a0f8004205207003c440e4140d40520480c1e100040a03154441016400507010100500c0240d40348240184c100107084004d11401c0569240c42e6101d09018006e0150104601044020300c40290102e5030403110003469400c043d80c40745009046440140005d64083c9428 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 70979561 1250 70978311 70978361
    0xb0a090905010c080121021c0c030317040807020d060b090a0606030e0f0307020f060706050106020115090c0e06160605010305010905011d0a0210092720251203 70
    0x401e0098141d81404034480c01e9201e61111180440d01d80e42c03400c07a00803000d41c50104823401c1507400c0e900264401c07d480307031160b032079030400400145042e500c011010032110b0a0100090800003240d03901035042e16215080211070401200900c03072209041e0300302c590081040811a801c0c0e1003017046d112527407000c000702e0f02e044c0c2070741d5513410a42000101a500c05c0003281c026103840b02c003d184035480200303007030300c4c00341550780340300075500d0030303440500540e4458290a021040407500c41000e021710b110204150142420010090031f5506281c42c0103510004d442101040003144c1c03c994203400c84024812940d61f8030f400c40c002c00c0c0c68030301a80c81d54030f40480d040000011480701e07140141c5c480b00400c1403081c2a0201315000400e03420000900c20b4070003000035030610030800100d646212203001d04138281d82480340d03826240707030031501440c01c0440030f50b0410502070308066074040c0f020b03400301d007041155402c0e0360805540c1402c40505103215018030503684540c581c010880c403200700c00841d0954080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 70980811 1250 70979561 70979567
    0x1303020922140c0d050c0301060510050703030c0504051801030611070203030a0302180d060c091512090203010609090b15030307020901050108060d0b131b0605030601120b0a090905010c 81
    0x854226401610000c56000e000b04842c94458410480107405031141d25101c1400036181414554007200e040d004103045035290316083c07140310020001036618013410402c149004240703100e134100040500d82e83d0864004803c0c8550309440c050607000e02101920100541c08212248091204031040b50401d41600d0b80000c0c040141d881c007a40c098029400c118032108190043d4218002c1c42d14101c82000c40d800e200c0d6540700c01d802115000d0032001a05e00a800401400704645800c00880480d102241c001655801350f4086004049070100041d082000c0c1300081c0500801c2d4040700396241001c048400b80500151200e009102072a501c0511801c1c4805140c2c4038081c041006e1f41c050000001004507500452007254800e50040c00d5021a02c069542c107502984250744552a94401200b442c0801c900c5060194100340d8054040c104ca41c40d14900420b544401403005040048441b90b0010017802a040b0f00400840103240040040c0c490022200070102d00398242e81c9503003010310022807540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 70982061 1250 70980811 70980841
    0x41a0910050c011806020d0f0e060a09020f0411040f060f0f05030406022101080c010206091c0c0c08030a030b060304030207060e150d0f05011d01062313030209 70
    0x58050022031649291050940700740e008000040455500d448000003895050414074160f648110001a141d0408a050f00f0490b00d41c641007803036003842d04c450801c40400001e03220b5480707a603980c0003150407840ba20108182642c14413907640c1050814031030010b5100a00301510030f44110200d009003856855604943d0074418141241c040744000480104803403140300156800780c0600e0000d41381480c07a003a0b5005628124450b031050740c40e03c600505c8510340034008001402000d200030f050a041c460200c0d9141c02094008030070348584440c03046030b4903001e11312101001317800c580c03030080c540e0b0380d0f03c2100e40342d621411007070380040c2c54159603000f1442c20b0030590b070040350964001c1c01e282c2c1c202042910b050b00302540540d40300d045154820f0f420b40c00c010050039031070400c800124103402c41d03241044c00d548042e08400b441510001c0300340c2e03c41e0380c0c04440504541641c90040400d042e0814007804600454100d0214894001102c5103200b640c400003400b1284283c0d043c125039a02c520300d04440c11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 70983311 1250 70982061 70982077
    0x103140a09060b061303030f031d010b0301150e0a05130c0f180e03090411040906030f0b0105061204030f05040f27061503020f0904090b01150302090f0909010908030c041a 75
    0xc0c8010505002081c880c0786038403084070f88c6060021303288035090440400550080001c8015039160000132400b41030030b014000c0400740b01ea00c0403410606203440401006402080e400711a03945600040403d0450b01c000600684c0004800c0c0a503912038024913602619405440c40c842c61001e04c0b0070400d6010320414503450b0300c17280a0740c1800c11b01070400020f49031142c0e001c180c016040c000030807607a000b032140c031008611403245142c2841c4107140ca4101e440c016402548100400c0c8044042c0550b00d1120540c4594549800c807640c009a840c2901c0b10700458000c10605040c420002c903081101c41070a80428145201c0b03042900850f900350000d94840780030b20700c6071400360548080c1d00e5000c3d030060804188048021410859128041821120444e03400e80c0c0500c07508004202d41c0d042405e6510200b002480c1c254542070f526400300d100300e4132884105024a4101c0c0016032032000a602c48020968042e02c103e0780c90a02c0c46403a0300e80e0700180200c40040080b003466400c4924520102c500c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 70984561 1250 70983311 70983337
    0xf06030309092d19050a02090307030b040f05071401030b03010608120a0309050f011b021207030e040209030706031e1509021e040308070b01060807080a0b0103140a09060b06 76
    0x16959a81c01c440650310b03281d9561080400c8a03005040303000700883e045100d02240c002c407181e0341000014850507a2009440701d03001501c100070714601900e0200b0788605803038000c241018191154980023401c1c12041c440035089004405001c50500d41d10f07020341610700c070245d9043c006d006106007054203da400e40700e0341166901c040910000d07083d0481c080d212030b02090070005600005070302d890703040483d42c1c40d080a00703035520307094415a40c10054854011a011b44001d15810001484040c21442031142c09810700000c91104907041d51160125100110090b09454049039139041c090090710018001006107803a11468480100f03552103840d910241c43c8034243d01c3c0d580381000760ba0003540404041e80302e02c164016500584151702d001000107500c6803426907a5440e442c14103000301181038100d03401f080b4255090140d00340d4450f01807130b0000c1a150340001c2114548005a005007000043c101d40044082e08001c0d40802030761041300440d02030107042c0401340c114000c100080c03080602c40504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 70985811 1250 70984561 70984579
    0x60c080402040c1b20061201050a060804080301060e0a09091b050409080403170403120203030901060f0510030c02010b03070b120703020a05070605060d020a030602130e010510050f1e030f06030309 86
    0x1c40c40301061702d0249448090f0350015084400c0100d1544c0d8041000c00b117030010210010801c41c280440c80100800c0103140841d080d060659a44090f840103210714410800c0080140080d5540e00340054024a6802c0302044211840c0c50a04912940410804501200050001440c0c20140560013483e60f0002089103001d003180ea500d00100050518952009801d11000c03000482181c80503841c0006900115120701c1c10340d400c28259840341d009444401507008003000903481e822201c100304400c90801140005496500700c4c01808e2030369800e68180708a800000c4d281c0304540c01055010000074004102d591190030907010703449000d000c40e0004d42c081161801050583d48030070b42080c0300410b0014414081c0d00003542d0001c2c0381c0c00030745100da4001900852307074155110340c0005024440c00811190f141ca000105500c41c00c25880061280c00141516001c070190111004141010904c1c81c589034488860306e2990400c6a07144945519040441c0e0759213000410b64800500007050589 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 70987061 1250 70985811 70985813
    0x5030f1203041103030309070311030a02010c08070f080a0c0c05180402010c0c08120306090a093807020106180b060d0b3c0a0305030f0a02030403060c080402040c1b 72
    0xa2640001c005450003080f42c0010000c56070240015801109164000c0a1203419410803080e82e590f06a60a882640700300358110040c0d030007001c410301054002c0d01c1c1546481c035905010f50345842482c4000c0c00d104000400f8451590041d0310b500595005c0d40080c0c01c20340d1680144114044204e0052030f050021400040040d03201d620b020070068072418094090302d580b450ba282c0b514050041c50300004502008100d40760a00710b03242503010010503c107100e000d11075194595609080101d800b00d80c4103100708031103001c0c40304001100014581450400b18984914001c2c003c0485004503800d900060f039102c05440c0351405603244ca40301c02001945030010084040e80140942107150750000880c000300c0c00000b41e105481d414251a8104006a0070503550512100307041c1000715a01c80e550090085c000301d2000019110614201c2c1c03011980c402c203190007a031440c0a55400180b82c00d0909114881d12540801814050343c030982e0140f00302d11542505581e0000744101c400101e010490500c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 70988311 1250 70987061 70987093
    0x303060f01050c0303011d090c0f01030509010e0f060f1f0b18040903030b0909010606120902030109080c0f07050f010f0f030b040204030803060906010216090e1e10050105030f 77
    0x560000d00504240b403404000e06a42400c540090740800d0321000a05804800c0f00407003030721a40c4c0729080384040c0c06503c1e1050000f0741801401c2c2d440c0390425540b840052140d1038254060340641e910402110000826030104c0380c5e94800444403007903407815071004030b40b11150020314201610074915541c2c48540c00e0240c10304071034120740d80d681262001d400200304070340ca0303d00c038145015010340e9000c11b034005450180300012102030501c1d0b240b603240210030041e2540c002189200d0f1400d007003001c52725507103900029000d07058001020348841c100080c200124040040d06410544040056940c4a0b030703980b080081c07114910341200d02185000c1444103402740f2070020810320094504000030040400800709040342c0141c1c0003201c40340700000c103010461604003255940035400f4801030003512180400582a00c40038814184415111506060b003600184404280300c00795034000784a06001d031070301c1962524640c10a82085140100100d6642808a00d088171031501c0c000501e01c0d0210a0005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 70989561 1250 70988311 70988329
    0x3091c0201020615031006080609010b011103091201111b010510030b01050105070501060806070c03030f021e18040908040303180b0f220e010303080106030203090d0c0204090203060a05011d0108030306 88
    0x620b502d030007101c10a04580c921b62089a0150003200002e0800d45880d5010508603940f1071145414450300d1000d0b15907401000007110661f00e401d5420340841000a0121405082004c0301000d020f800456410031803540c40d41d0511900d4851402405140c540c0e41c03100892265601020f0410000400140b00550203080100000781c460701c00000d00c2e40ea540b010508048060302d80100050f820f4020b0810f05515000d90080107090360380c2180341138000c1c02280340e101180005888450008200600c0022202c041c16403aa00301074003e004050316890240d00c26401400b00320b004c101d291540782001d011049c1c10509561503921068902200240030f81c0b62904001030b010781c07000d880d4129041601400041c0e10084c00c564940071507075411490041c1041005030044010144144100319100000042087d00c03c03410b8240180c4001090000c00c024040b00b210107909803164a0500000178075550000b03040f43c0f10b0810004210500b1845070030b81c04800c2c45007011560081c804103001d854145c0309 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 70990811 1250 70989561 70989601
    0x315070e0a06080610020610031101050c01020a2c0d020405180a060504050d0f020a0605060f0904050d0807020d08061207240905010f0828090503091c02010206 70
    0x1021108108010000d81c1044030364014400143d0004240032440c1003000d0140b5070202c0e0760016005500e400e19807001c14004501c00601600c0e020520388120344d00490460f0a10b4801e64000d6540359404140a081e21750700c2551102c0484442e05508243c4a840502c4131185000910308074940503c1d40800002c0d0001a0a003840310503418890550508100301009a0620441005c01c852406080550400306034240d410280059030744140790300d0380e000c01c420840607404500002c0d80e03103802e00452040c8110744500c0d9001074801041c0001e2110000d0703111944191940c559a0039902c038403040307854905161100d00450a1800402c0b601c3c5440c10b80d032003c5144c0c1808407100b040c1d90300e0034408030000e401c03c002c8180d81a4500400813580c00f2110703034050013084c00c0554080c018080010b0540703000070008600b210150320340d142c1806440640f01c40b4107022410500c240b03011410060349030381c4000401c9200f148500ca07501c14001c0f00d1484016495016005042a85c1e20074825071203d10b81010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 70992061 1250 70990811 70990817
    0x6180405090c0409050a0c050108060a121a0108011a0301060506040e0405030702220606050702090103120c1212050105150304150e060106030b0f0409080a0302070303020d1103040b0114031507 84
    0x10030b99a0b035448a1041140030b50141c0014aa4030b1100d04007000c882c04c1d41d030001d60400110f2070400400c0d440d0380c1501c01c03c98064840000100040307052500c40142e0403151241c840348001c00000e18807405410242d042240511200d080d070760040209401c0711807510409800100500080018199481c61140d21900070070551707240102907400160034040300d007500494443c0b10044010980c807181700e9940074040d40d040ca9407a011140c1c0010351000014880200740385030307000900039080e11552420344ca803a40204030042410b03c904c009420351568000b0011554600f81c000109440c0c28040c0e0801802c0204010b03240d502c60303480e40810343d003e08908540840c0c40c5d048008111a040013028000d100e240e03400038269006a0800490480200081d03201e24105208040450b100c107085404201e81802c0051b030300c2c2c5041c5811381c0071b405440d2040c621903242000c00107122003500b000750f10070b034402c1c100c1400c0f80c0e03201c5003401000c5020030701e1160580c0c03100c10203904983c0548001e5401101f141 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 70993311 1250 70992061 70992073
    0x81002090102160f170613060509160920030c0708070512071211010207030207050f030c040e15070507081e12090109060f060602060f040326010f050618040509 70
    0x1880003603e2040c0c6a01500c907884c40400f040000b0b40010714800d4588a9207805404d803070800701045400c4e040d1140c40070b07010580e2000414840281085605c9243d04840070000000d552249070390010440e104106091081840c7c8000025020381c040700d1184542c085002c0c10210705880b80401a00500c4088030184540d5030740002c03007180c510140c650540700e10b52446000c4424180201400113440c080c0119a005000320400260041810780c15242d003a14806194003107100061702c0d040000000a810a1400010000e4600007168120403203d10880340750a036100d82004031076900c42c18074090018042800300f140c14010910034241d03000c41001507182025103009000381d030070105851942e4160b40d550071000c1080307101d000d2800740c0311aa41c1d040100515009020b074441c02c0041400e09900d901c58002400c040c080d0319a0103010344c9a507403002c0c100714415010300c45da140a005481a04c00e04080020b018a0002c040b5500b007010070800d55111145401032001400e0068032008860203a5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 70994561 1250 70993311 70993333
    0x1204080405030a0c03261902011d0a0b070206190203070507081204061401150809010f14070e190b0a02070305120d0f0912050c070905070509010315081002090102 71
    0x801580d14601d008000103e0018a54034000400417506e20b01507804109200111100c1500790b02500d98003100d404060660140703030002240140031032050010700110000c01e542c8d03140c500207541c185542c4078034041ca0143e124200107036551038040310441c1c3c42c0b50228a0b107000c00c1c6a17680145400c80d10504205040c5140d85d40c410b40c00380c10100710280340010078000c0105101d00c6010b0281c16406401420030303e5414049040d82104401c0d040d94140b010000c00300e10710500961010401e038413440000c02000d240d560805203180d00c1540c510300042c01c004c11031040d0703207003685c001001014501d02c880c00c035500d445442c1241e82c100d410481e0950095100c0040810024031050400310500c80c03050750f441d00c2005600d81260044a2208110b520308000300700040c04006050145113070a04000b80c651440b0158580b8148068010020240c02d00d0148002079270003401a01094400740c03014400304a500d40e200e0000c00d250f1094100c1c59005d00101340e2140701c10b50041000c41018030540d050b804003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 70995811 1250 70994561 70994563
    0x405150d0e12210106050d0b0f06070c0f0e060d12020c19180204030c03030305040f170307031103040c060e0102010906020408030a02010b09130305160b040f03081803120408040503 79
    0x10300030031000d50b580b0003c0d03002c8583c0b01d2601d0b483c6544502841c3d2001650603c040180503028210380d03a40340c9a03988880702516582e502d241a0802402000541d0700c40151911100744030280c41080c400820340400440c2d00d070680b00001c2c0c4201000b800d000d46500c1c09896a0382190000107004040d07020780c1042ca40107803035202900d1700300c60b001d0010b0040076140501014025008034440c44020f80305000c1030000500c04a00f00e4200ea03054540402c40d07840f91304080c4890341d042c2800421754041407225454100c0f0000c00703103108400c40c2c3c50400c40305100d05200c4400b4441120000c02500c0120400d0141500401d02e000d141d42040c40002140100ca40d00c22080340d1090b00804819400851403200c176a03824002d5100c032045c1038410031079500300009d1032810340c1c1501e0001810f002001c54200d20040d080c08000c0070464200d1648a41403c09060084040c5c2005401b82c00140203580000d22080d070a11038403100b1880040250b2918180840101403d14040d20454001000300170010781650 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 70997061 1250 70995811 70995823
    0x207060e090a27050609070b0f030603030c03040306060501201c020102160b191e05070e09010315050a0203161d040e030307080901150504020a0905030601290405150d0e 74
    0x9141810060320846084c42440d0003c01003035000030f03600c11103081c0b12185032101a00d5100340e481e02d01d03d840740c40f0b40d00028154080d43c0e540c4c0c0c0035884045400010301c0410b0304034004844080c2c8942400300c111400950071107081c0141415160311113640307210410601b4900e94003143c41480010f0030121401324240508002d164103403000c00460041c0101d0001902040410243e859020007091783c080e40705008251981e0703000c403c26507441c4001000d10780035240741032a405c0020000d000f07940e12441c0102c54001a0050380d811540340100083c4030901c5071088a000e860164030035000f089108c1401c507081c08503140c0b00856120600401203860f1961f001d17003030000c0c1c50813002e50b0f1245001c00008003000c800401c04030603a81000010710062000e028418103440c403d40d000340e500c0803491410780b0551500d0740542d030140b013600c1c00005c01110494840c80c511110250100000c28081c011883e01d000e00d00031941c0c41643c2e294460450f0705204000c2a6103c2c81d480045052942c210000b4203140b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 70998311 1250 70997061 70997111
    0x70201110c010c08061206070f0203070203162d12110306010303020c01020d0206100b03090a15050a0b040506060a18030507030b0610030c020c0907020304050a03140d0207060e090a 79
    0x30303460b10f4140c03403c0794001c0304040d03111600b600c80300204030946c110182e8625001d800d00003441005405c15038090b20900850721081d0300501260381840048000e20180d41042c85260341403040481803a00c403040b1400340c0d50b525080314403161a00c2c0d06020480745e1220762603604840e50103884035019000e441c1070013018000c40c007a40141c8864840341e0000790130f00071540410021508035801b044143d40006074000151000c0c0c280b540d86070794503c1d468034902148841d01400d9041035a0762098080c80c0d582166100303486060042c0f0082d421001408140c1d0750a44103260305c51014804001902d11840d08a00348082522080160a58075101d50b4144001500180e074100c50500030450746040840204541c0d101030320b000c200a803041c0c60000e45440c1e030f00c80414803420031000440d418520070029a00982801000007118554a1a00f0036444e4800d03c20441140540383d5811422070000c04da00b41103030030944808540402410800030b40c140300400400c00b031651283c8030345940940c2e001c0d160b140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 70999561 1250 70998311 70998313
    0x6030c0909060b06190318140601050f0d08030c0c01060b0c070504060b0301030f03210e071e06051602180c030411060f0901051b06130c0b03071403070201110c 70
    0x1150042c14404141c0e000303207203000c0c080c0e0410001030800d5003008000002000280c5000600c0d451410b2260700282085040903103603030091701e00950f008002140650481d44116100740340424500148000c8035404034001d0810001880041c3da4070f2030500041070903c504800009050b5164480b02c3c00c1500000113810065004550510060600d4452080a0b00c2c0c40b00c0c41c84c1c00c66142d542da0103403842d0b82203002003c02c01c4241c284000300602a0304851100181f400510540c03440d000041e5480032140b01c0c180c2c01c4c9040c0c469106000a00c000701800f51070320390b681c4c10b00d48012001ca031801c035614007001300d0f00305402c003400c03243e440c0c07450a07030900038900503078482d54030708003420009a001e042d220094800c140400c0b0a10310980f4540c12111134401c02c0c01c04a803100400d0183d048139401049000031035001c1c40d400c00c84030b040064902c5041030b00c02c0f5000c18a4a403203040d0b500c458002140d445010a842e1845520003900d08405035500c080b0038030002c9006020a1820b140e15080500741c0c0e48a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 71000811 1250 70999561 70999571
    0x310060611010510030b0601051c0507020f12070302070317070c0b04080d09052103071401051006030c050406030f1b120e030f0f0903190506040201090803030702061906030c09 77
    0x407140c0c0a02405800116221154483c24295100c0e0722040002403c00750600800042020604111041c44030f070309004001d04018501d000c00c13002c1e4452064103420350490081002d8003200b42c0441c41600c0c011070305a801026003a05656405001800d81503080c0d10203401800710ba4006500000d4200c064500690303c01d44580c47c11040601d00800c2c070028000f4412094801d1200f901d0310440510f12007a2030003401482d502034034009055124280d4042c01c103100725031034035014510541082c1d000b450131000b0340c410750340d0381d04084080b1100c4496200004004200800c0150301c2070700150070641a0030130000c1d081c2c0101140007a4000d00100d41c1c80400c884807000320810301d241c403501d6030401e80040514601603c7c04500c400c4c5102c2e0f40e6401901403c04141940b142d1800c11a84408a01c0003550080240071400c00a549080848040340020350310440411626004403d407070080c101500102040d40ba8200c0c2440e1002411001210017540c7d10390000100b5a65182d182c010700c040400003034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 71002061 1250 71000811 71000837
    0x101b181a0f0c070e010b03091f06120b041115030a0b04061203080402041a0303040b0708190503091603020310090303150f080c09010f03030806060409110307090602010e0307030e03100606 82
    0x80e07804c0140e10081c1e007114140304100841d000822942e40107040e5920050500e09940602e200801103600400711389607041c5400f40c200030300355210340c1c05180680c08203c488105203040100341c03d2104603d40000c4820300100d41241000d0b00000a040d000820104416466032400c00203000b981c5425400103420500b4801942024894294034001c000e0840751200110b0f0b002c40d0b0340c1d1140d03200381038981c00b000518109000400055611140640004000c40500e01100a15a0b041655020b105000383c110b90000070440301e01d0081101e90150117802028081c0d44c0300001802c178000150285501c50000c0d9001039038080520001c1c0050004040a90f070810035601d14041c5650640c03030082c1402c0d801805807200c240007034402c503641841e0041e4a540d07036030b0103d2240d0047d503211490090030202a41460091907000c4c5100b05016920f0302c02d819512003080342030303989030100321130b46e90004c11290001c81d104908009140782c01500b200e1481e41c1c800d84e0042200c01d6980040700140c00216007103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 71003311 1250 71002061 71002079
    0x12010507080a15030807060213150906030504020a061107030204050117061e0408030c0f0d0209040e06101e03080a0302120906091c11101b181a0f0c07 66
    0x19040342c81c2c01e0341041802a050781440e102509400b0183c5060400309107002002010b4040b510610501c00d01e40840e507540d240c1d4200802c1000e2003a03808074084c6003020950602c01e01c21240b03c0c0707400520381e24001d441c200060303a6001a8200d446c59500400c40e0220160f2541c6c041d250083c00f0007802d01020202641c443c60425001405038245580d21f00111540c10b01c28042141e00310782c01c118825038079103641081c2c00092140207402102200007150807000d800c0154013414002c40c05560a000d10300782164101c1e120013045401c96084c0d82c410300240002d100841c8111602581c00c485016003c1e202d40752130702507400c003004040001360002600c1140a12200e80715401c038036580020004c1e070a0484465403540380074280b41d541180e20000400f9442e00c140d22040b90100030205448840407101c41010143c20309642c40900c4c940d881c000501030354400e1081106011104006140a0307090080e80095100310340c250f4500e02200380000045034021400810008403d00b004000091614603c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 71004561 1250 71003311 71003327
    0x110c0703050309010306120b04060b060d0903080f090c090403031104120c08010b03030c060a15120b07021b0d0f0201030204031e021c02030c0103050c0c0102040609050405100308072012010507 84
    0x707d032450311948000ba5115202c0341d00302e0341c03282c1301140910b0380d00c000c40d9443c0101d18604c00f09604040d00b0205241d04154554080c041009184010380d8440c1e10b580c0d5038602004400e07070032601190001c0d0109209a00c400444c08020030500d2505035285612461805400015209803203030600403c1040402d01c45c2c0c0c100c149064010f10300303110429040a460b00f05c002c0c1a059071316101c1f545600c010140c151480d015100f180c124000c510840d003004801c20070b04079590700261003804264840101c0780403c5d403c1e14000140310f6000c240540c0c7d5040d020201040041b41456024840800028140d50744543c910b0035100c0e615250700018010020322444d1900b411050002ca00345040240c0c4000c104084041d0080c00c002c1082d8030f41c0c01c0d45507501d1080c812174800c907510228012070506d078480480300484004a60500040c0c8440304564210402440010815481049008005010340b18042181c907502d01c6006404140200410b00d50b1f0404001c891042e503640c81044503841c0c010b950 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 71005811 1250 71004561 71004569
    0x506070e01021c180501110a15090204020c0102090301060608100614040b07030c050607050a0e0d0c0b0a03060509061c23030f09190503061803090406030c030209010812040504110c0703050309010306 87
    0x101041f45000006440303581c81d000240a400010100804072031154008007105640500704640e109903c40c000740c000d4010054103031007542803100000e40c1e0780c8180d200314021018400d8140b41036143c200c0c00d99104078800e0781c0440f8040c09110015104401e04040e021560213507e0f0b040e840c01c5caa140a034280300000300030000703104d000c3c00300500d480e601c10b6000156210a41d40f2400700302c001d0400804043c69640319000000001614201d102e505800036030881e90300361070741071079074441604000d00c491412240d40944e0703200e8070410020800f1640c03086a2041d06401025441402401c914216131184c940c3c40e030070040001d1910038a04124411500041c03400788482001410311002030386643c4042d0680c658203076140400c030a15072042c0101c40c4420001041001884d0340d070319110112481920082c0d1050310b0b40400001c4042d808590100c07840f0403500410700c0c090601c002c10000300074820050b6003030f810500c80010700c61810032a0300080c41c020170095460f20242400103041d50480c4d08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 71007061 1250 71005811 71005817
    0xc0408060117031911060a150815060d0c030b090706090503160501120209040203040b0108150c0901180509150423060d031416030206130506070e01021c180501 70
    0x510640c0800b010054503181208451003c420284000301100c0c16500c4006030600750180805002c0035800c50b0380203000d21440e218094044660312215103480d8003400c03c0c41034043c98540c000a050f0b240c005440c02006214640c910000b42c0c590700c6d2413600082c11201d5001c13541c850142801001c2c1c000030b45070003c15085000b0080071403202550801c00c4164840d15061042c0c18118150155054058544030071028004546a2030903040c07041d160300081c40344074042c3c050340c0c042102542444c803e240c400c10450003210b04c3c1c060900011900804149068002014204804251075448002042c010150421a000e101c040c05040000300d0381003425001c803c11142c42d5240c00e00b48444c6000c3c0d40424225589890040705090a980c0301a03040080004e450b400506414400e0420050200c0c01c2e001e0342c2200e4180c0c2c0c4900c00c020800c00d51700e0001e0000da1084000440c502d00c03800440011303480c1031055841442e0000c0c0070100c441c825a0550000c9000329407801201d0303d001c9a0207008000904e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 71008311 1250 71007061 71007089
    0x4080c160302060a0c06020405060f04030c06260402030a0f05010203040308060303130e090106050612071d0a0306180501060f031e0b16030e060103150f0603020a090e0708060c04080601 81
    0xa80080d10902c04c1880050510030003654035000c1c440b49905a400800d40a009142d9407034402401c501c650b442408201c80004000c000412054031070703054801c46002015103910312901c0c880d032170240d0800c0144100d900d88141c018020024010352108070081c1e1040001503203d081c14600a4240b000c010001030180c1c2c020b01c488540901d1626824045039030035004408151a03d01c4e0043c058881600060b4000800017500e0028103018060b952080c9104da845114840003281080300c0c140340c800c04140d04c8001c0e14024070104102794080d40040d42c0180010b50304c10350310b03030741d190030344140e0b622108140007a19400c07c24000c9080b01c9a8881d1039410007000780403003e5540c50034180340079040420703004005106c0542d0034069800590031040c0300085514541e5a450444404400c00ba0100400c600701a20000c1c051500c2c05143c0035290f0041815558a060a000400810380342941c0c2110740b00f107140c0001c803030300c085c0040380c002c82581c44444c0d1794a0030a060a0314090042c3e22040b01d034a01d036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 71009561 1250 71008311 71008313
    0xd020711150a03090c080d080405100b0f040e030d0906060602010c050903060f0405030c03030406050105040606030c17071803140c12070302060901051c0b01030c0e0f090a1404080c1603 81
    0xc80129602c0c1c1e000c038200000e000038541040c82c0903146680004006202d01c46a4280c069044540350f4460380c800c00c00c0743c0414601e41c0105007a5070740c00d03000c141c0040446641c22541d241581001000340302650032a410703d0f0450080b44117443c409001590016514207040c0506642800380e01c1602040c2e00704030b442e1a1420010940c1c507000148a016429884400304003000001d1040b00c4006544d1b40440352241014144100140300c01e00c00e451203186072a0300090f4040c024090100740040580313035100400303140283c1030b800c0c03100200b61034200040e00c51081450200c80b20840060340c02030500010704001105218a4943d88402c490303c50100c041b12000c031000b00282d40701c26207505445107600c0300003001c01607401d8003c882c890160388190302d8040f07004000d5980202e0b8021401da8083c4040d081e200c105544017a07003c0c41d06074100d0080f00d0250854141300440c1034008020500015030450800480511148190703404c446c581000079400c5004402040480311190425500701036040c42c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 71010811 1250 71009561 71009599
    0x10110c0d02180601030207080a020606041d0307150b04020403080909060d0c03060c05070609120f030c0207050d050f0a0b010303111b0906190f03060e030309071e03020301020d020711 80
    0xd009165460042e0040000300640d1003074041e120295802503600791a144446000394460004584072400b6901d00801040c0007a480350704c04ca06c5243c40405180342c0f07a05a29000d440f00316901d014003001e500c4843c4e81034107450303a01c0140000d601500500d80c58078050000c00091a4028260510a58a12070740e00c010a02010348541100d03400440041c461030120000d4030035018842014200a00d00400c0c4400e00110305041d064201840e45c500118272540c04054003268070800ac1e00c00103030b01580b001c4c0b0150800200c1e00e01024000d604a5107011000240b2501e41404450201c440f600040e004004068118442d1442c05c01e81ca4040c00e01d0304090004503500c8841e044055104109010200c0d0740d648490607010140014a0107000407251110790024561190b880112521480c14030074206150010080d40c0c080c82803200503148042c5054003681030440c111120840d54040d1440000040e0740074402020504854030000d078544c0080d05003007290b507490005e13160181811411101d81882 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 71012061 1250 71010811 71010829
    0xb0606090a0611190809010206060409080306010c0201020c0402220602030a050306010c08091207140405130b041a0106080714070317180604050f0706020f03040303030207060b10110c0d02 82
    0x4054070f400c0d60054280b40b1081c0c50003403100b43c0300524a50071086038081c407120030700500301c800003130302114019194201404202c0c0da84000141c8000c0d41400400c45540c441d540b0441454014030498200316a6a0006000c0b0390100c41c41d50300c9030107410341c1c101d581d55960344080010081c2d800034508001da003c45c0030b481440b000b48100e040104509000081000d00d000303842580c00041c0002c10a4505113062603554102070041c02c2d100004000303504000d18282c02540d10460108d412034074407031010380d1100b03800709019004941c0618903c181c0c6c80380e140c04440701c80c0200080d5803550000c1c244200090203940c89500088400881005000d01203504042c1030010301c0030b41e40160300305640d00b218a4004c1011840049a980030307000074001403003400a03810b4440301028090300c200c44c1d03440e1030a99440041d40340f51141504180070030004207000b5400381806500407800418566118000110550448901000410b282d6103c1d54103005c010000c0482415081d42c0030310000d000c680000c0e80401c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 71013311 1250 71012061 71012069
    0xc0d031b0909021615061404060302030705100203070506040b06211b061b010906050105040b0a06030e03040f030f0c090c0504090902060f0f071208011a0901020708070801090b0606090a 81
    0x180d00011055800d51094414a2130300b0b4001d941548695a60000d01001e00114403500e44460f4800040040903d403500c10b901c100ca80c02402040114689030a02114140c801d902c4d1040d40400c0c040b100120340244001441a40b0543c82c0d40303514070f060700c200143c0d01d10072500200345594417040903403031210000d030484001b0403c1207240c0d40c070b0341140c0c0000d440340704840f11220f00712491321400d80b660174150082199280300c0c8105112507a00c9000f03004c2118440b00d50294400e0083d070080102901a42c0f00c10302d480b0118003520b142a40303e0307200c41c1c4003440550080319064000000901481540704009025103400070702404490b031030940040c81405070340030b4040c04695071007003d0115511003003159040c188100b072442d01e9410030444200c1c1c5421010301504c1000242c02425441e40c03060400c907060340c031a02000602c0340114984041c082d00059012410361164000c04070381032408114280080100c800013142c45540f61400f00025a40904401e0041a007842000c1d210307036501002009071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 71014561 1250 71013311 71013329
    0x70807091e05031609050a0b0f060d0e1c0305071d0613030510020c07080c010503010b0304020d050105011412060f060103020a120203070207060323041b0b0c0d031b09 73
    0x40004090300403000415a000c2ca61501c24070244155012454040004075610f01004000030386d81c1d001c111058a081c903c01c95845440c0b0800712015103440c03405402c1c800c0e010306c0c0000d04980c2c101040c51501d602c01811500c4a645c0040f45c0c06907941c1406401d60080321403428410790100401880e41e08480c0c080d00f1441454003096050300c0a5124040300c0046402c030013100c4e4a24000141b1600039807044120665a004415010620000000340b4800c0000c069440604c0c5030b03c3c000341c40000d900041e2040780d100001071008400b0800900a59000e090307104200c0381d08014a000b0002800080c00b8518034070b40000040140900c090b000c1564402000e003805a903c444002c4200d8122500c840d0300750311240701000b8000c1d469070004080c420754032692000c00c041ca03809550740040f000c0c0d004e140c3c103010742035500050008901d140380c4801aa240b00c8c0f009080e07901c815040480303411405c0341418a030320880d6440c1613298540102120785800499000c8544902d0340020040d9100d4001c203412 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 71015811 1250 71014561 71014589
    0xd020a090c050d021303030e010804110103050606070210020d0305090106031a07020a021e090705040b0702041d0d030905010f0209030a0602130e090102030a1d0c04180c08030307020607080709 84
    0x28903014000322440002184002c40d0b98000e00170030a151008140000c1d0700050f007000080c44554011003106003d29002010900c4d209583c0c401100a00b100820701600b1040500c40c850050311100c0400c250030410b038028120420308203100508941d40200206140e0b810048200040751440150004000c4240c40c000c0d450356179070f5004d920b80700c0c1c510b8000390000d0352000307404194151560545aa2001298a11951f0300c1d480c4080710300f40640e024030000701074100a401c00510745644140e05e041a41304011491103540d180c841d052202012600e804203840340300c450f0800100b031041c120300420b800300c11410401389002190746d5500380040105581ea000035100400260444004010402480d41c08401c0c54103401c424040d410540d8400c200d81e080c0344203500c0c4035800124040e51000428001e1408182c804c08000107001000e000f10124207108080d0000300f41c00c0708a0f00080d00d03901c00116900d041c50340000346043e00040c9440d0801c104841800f4280741e10140190440d4911180580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 71017061 1250 71015811 71015831
    0x30c061804050c21070f030204050a26060c07060f0504050d140c0109030f0f020c030d050a05040503030309030415020c060f070305160507060e03030f250c06030b0a050d020a09 77
    0x302c01d04c12860144070340d0b9910001d00880c0c080c0100c1c001c5c070035821941d8007880700f5a0003030f0907000c0c2c0c000c50107450b6100c03102140911001c8219140b00c25460b8400280100c060004e40f846800c010701503440c2140e840000401c0c00078402240078018581104480800040c641511070a07203038031120740306030304106500c1c6614210800e40c00503109071011107002040000040e00e000b0b060722101e40490808184c40500040143d4000301e00d005506070f000e009003880050ba014120b13100d034050940342003888820311000c141174034200301841c820001c072070046580d03d00b044070b9240100b5545010078110742c4644482541501c41c901076070841c0d0a140704007519030390945415101c41c000c00341281d01c81c07103a1061003800c2c0400000c0345c00885000b611118040d0102500b4103442e4840c1038001d1440308401c00c20035141e80fa40c0c0006500b2260003d08440a0940d16510961101c0e91750b840000043e44a4081413001d00d0190380d22401441c1c201c2e03250061400350350208001c061544222004250750784250340d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 71018311 1250 71017061 71017081
    0x504080318120d0903030e0d0308010506090604080a050f01060e010b0901050a0e0904060b1509010e12010902031906050601110a020f060d0618060504050702100c02031306020c030c06180405 83
    0xd401009001c00b518990443c440e0014009900c0744006c1c0c00007211121089a5400d06032542486150181d0b28848243c0c00c1a0921580f40d002011403900110f08200c0004c102c0420306c0190f1005204201909108000400795400c1d90241d4120a20003040c5d517004014142203002203508000003030130120303151440c0d182c00760b400710031003a40d8941144407402040108001c9901c09040d20104131003071992000b803058003d100d8055005918080350051241086a203006030001010761001c0340040303901c41142c0e0109042210703044c40c0442298010b442041088494010789901c10420701c5e201c9811445810055520781d403541000e8018440d8043d000410707210241282d8010f001004144921942e4202a50f0003a20151303e8090030b41c505007010807c1e14141c05241d00544580d802404120400102d4000070480a07000100b0b500c410042030580c032240c00c031042c00410301034000e000d115506405240c01c2600c58060380744144010040341400344240385030440b010100303450010b00d660b5242001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 71019561 1250 71018311 71018329
    0x5030d2d0819020712050c1005061e03010209030703050d0905030d0f030c021501080c010305060402120606030a1b080105090708010b030a0e0c0a0902040303022404141504140d0504080318 82
    0x107030101e500861610740c071703642010040c8a01b00c0205c0c1152030004060b94420229182620140d5020303020101d24024800c5404103010018002400185000c54200001c0c6c98414141e02c22910380d0842d100441e502a048200761004101c194040c011007012101c0040c252420618014285580c9559640e0342a208020595a411002c1000c1415517110300b0402c1e500d02070045150700180c20a0000741080c2420b009841000551100b041e489444000402042d50030080440350896668012010030185640f5010000101c030344590445504043c10b1004000f40140020207000981d0300401c011000d46045907485020101300140130034020302c9039403c00b1050300781d05500c00a11075000c5a10645940184216807098088803050a0381d1410000c0700c8080000146000c0314282c00540807400c1d0701041070398442024181c1b00b0f94014401c10009040040e9420780c2d44c98105607400b104900100150030f0a0341780b0b400c01505040c60b040c0c2b1141c5c0e030b20901400c102000c481d50950100c98840e181e034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 71020811 1250 71019561 71019563
    0x120f02040507050903121806070302031c050a0612020d11040b090f0a0509060c070b1504050f010602010f020c1b01050417010b010e01050f07030c0c05030d2d08190207 73
    0x410701440c1001c041c01400c03504200c0c0c0b4240b0a004256070b5588500045040f2034022040411305462110346500f044115003103040107030258003040220050000e000318000754011813031040025241448141c1a0880b051a003001034041b2001d03000402503600e000a22200130ba000892000d10400c480108028000501080d5001020342082c0b00b01030000180240c880d4205800400c01d07036584401c01e603500ca100780c1e50209105020403010700130034405c0c0a001e078400c00041a048407080c4030004941210804c8138116070102c40000140141d55080c05000315484048805500709040c64151036112034030054400c660f0301080400801c682d0240060360010710f003000308583e00e074a9246520f80600142d8280c14006003003800911027542c0600c054601300e0080c0041c050030702e0308070781c1d05485032410a0816941d004030310070001401e81e002c0102540d10100d41e5240c10366000118146040c03005480d80703003455885002448450707103a2000b030155010401c1c82101d080c054014000400912500b20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 71022061 1250 71020811 71020819
    0x14010501050313050c040906140603150a0c090b031303020c01080c0405120c06030c070c0f0e0c0a090305010e0d03060b04030f1211010207030f080f10140402040f030f0309090b0901120f02 82
    0x24440284208e0b68014645c080010705c040170710355100d004060f212102d00b11103411140b02038004c1007000450307070300020341c1912030300300b01090700d0715451f100300f16410440d01c1c641c2c28200c50700600105517045c002091194000c0c2172210fa1030601c0c0032603000c107028600826014503070041000c18054400c000c80c02d0401c1d400341016640b0309101d00003411030341c8414000e1b02d100000c8000051400321103c681e00845d8510703100070415486604041c8a41d921054040c410032040b07450200c040344003880381c40001403035900100040003596001900742c903107540c08110005024002000840d4891038986c04603075108181d03801c5054441c02c107507490321200d2a141650762001c01c0120030960001111036003003000e074031008459a50200500405101111030440c80c000c80ca10402c40a02002841828444018009030510b40c5401031038841840550094801031800030240e01030580106044024081c01f40d0144400e44400c80811401d42062103042c400308024030340b54052002d00c514004621764020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 71023311 1250 71022061 71022071
    0x100f03090803072309030d050304050f2a0a0803040b09060d0e060402010801080a031d1c050114010f060e1306180506030f0d090e0709030c090504030314010501050313050c04 76
    0x184000b0070025142d810611003180041c14507411307102201c1a50803502d00280245000f0058000132901a0406081140d4030320034180e51481039203041c052090440d10800120420344a5a14000301d01c050300c050441c0655604034041c840f6640203c100c030190340c1c80b400403d6640d800040030403094816031460a0400e4074006002819400114125000c0c0d4003d90310300c08640d80b91151107894050b40c05d001030108065004421002c003030704000580c125030042c64046214401c4451b070040400004088903640d41d07818490120540d0001554003404d1021903169286042200203440c1c5108100134511540101c040a000d041c503e800c040d000d000181c05001c40c0382038002c6410054102621752520a0003a82801440d050002600c031001d08050359031802d11a29080102441d004080d101d08200000c281000c8003041d10840300b20001d2122850000f21440e003030500500726041c1c4a0315003500c1103050010011681d029003500e400100780c5000481c404428a0042d140c0b00e0316081054000b8241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 71024561 1250 71023311 71023321
    0x90804080a050a02040c0f1e030f09030e0a0608010b03040314041a0703081f090b0f040c0206040b0603070308043503090a0e0108060f0c0702031605130b100f03090803 73
    0xc641c80ca03903140700f610140080300f01b0f41020b5506041c0c0d0030390000065040c1200115442e100e03002c11203181e40038140043c8004208100c90141c034071b42d41082d03000c134071031911410407410414044e038001c020a24080c0e041d941000d02c1e07442e1a1101500c00b4081101c115910501e06019004903402030440142c01800100c4003045078800340c00c6242c054010489407400500c20761180389504c04039015031400380c494035040000e800020f201001c40d05400c00c3c00c10082022036121407140784070041c1160010300b0a4541032070801c00d0b0303820050140d4040d4021207000c0001034006029101690408001d00b0b80d07280b904449d14407a40141800600392050b0f010380b400030036002000a103100e05003070b10f80101e0300383c440ca00300306440401e10501043e940300d01d000419010050703a0458002021822780b62520440f500060700c0d103407070708400041000860700200b1452400d920042c6c2202100041800030079074410010320b2240c0c06110140601441741c200ca088207100e40d10212040d0f40c0007069a442c3d080c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 71025811 1250 71024561 71024563
    0x3030402060a0e130f0b0405090c0607230a05121305010305070c06060b0309160803030a0518010c020601050916020a03120e010f05060301060e01030506011e0503060a0504020310140a090804080a05 86
    0x5140c1c417030401e842c60b101c1380790a20304042c0034141c450100c241c01007041442d400148401e9902402d0309850f1083c0f4003030a031403c005d50040000094140034003d0218644c0c5051035410040094050a03002004014081d44d00260764031a02c2103d00900f0001403603030f034207082035400282000004000c00d11305000890b0301c6005102440c06008a5021610090315010415800300c8450042d404130f68020700000d84144003980121750300040c00c0c8404030f142c0074603c03207443c2503500662510700980c02070b200500c02420b005501036030050107034a84e084100d01c4864040c1d1569240c7c403000d010001810022840064160406004d81200304002c1104003020800d0070018882652001e1195003842c200041d054441d242d101d05030398001700682061791a1041d00d0050006080c210840c42c0500000021700343d80600549101d002a00408601031805104250030002c0039140204014a0500e40642240c4040307840d03039021031031100001d04220541003501060107680d100c182688a0a1400d1080001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 71027061 1250 71025811 71025821
    0x906090f061409030c061807080304060c02010e0103090f030c0302010b10080105100908031903110705061008070f05060c150709061d090703020702190909050c1203030402060a0e13 79
    0x1000e26000d84a407111050301d6120322500c07100110350341c00003000c0b8001034190342c0c847e16684400f01c1101d442941d1411034900b5600664046004901140c80080541d6080361a0b000300240901c0e007080080a20780c4c440c400c0c241050400390401c00c41d00c030100d04150007540920008440103041a032104c80d08400289503120901956001740d40c00101400180c2c041c0305007005a80700400954104000c0795588080a0f5428202e0b00415440b24151020324010100415629024501070700151501181c2442c0105060b0b000c1001c603404001c0420102d145031013200c0a80d0011250641c0c0d600703401d190107181805031400402d241d0b40030020704c0b91031500680d400c005c0f26402e4441003c80046521000c007003201c80760307032141c200181a0000b0300c0e55100303078002d0065601c000c0040700440320699442d90801d403d9004218025a50101da8003404400c0004266002080700d04503003208410a4a640b00c0c00040e200a0155002190708110300d4080c2e180a100341780042c08883d00481844505000340c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 71028311 1250 71027061 71027081
    0x91a031312030f1803110a030215041119080124050607030302040e0906090f070608040f1a09010b010e0604050a050d0c0e09010218011706091803030a0902010906021506040906090f06 80
    0x1506c0c116010391400001c14200541d03a010b4014040d0362103c0c05a4040c003600062013241c0328100c00e45010030954a030300c49001350802001d00eaa404074148032a55007103031f01054504a0601c82406031042001042d4610030644000361001030311400305d0300d0141c02030f0055800c8074260400302c00c2000060407002880b07500c02d41c1403c00301c40100c00310740040c0c5e8a5502c07600422001904010000380480c0c4000d115103c614420140030b8000120501103440c0f4000c107503041c1405135124000c150381341d0781c0540301800381d14044030702c02e00e000e1600c0001040b001c801e1040309e00030681904d00c1d81c113100d50454400014401961180664030704001c0c054000c2d4000381004802920803600c46005520039064200480120f03000000c07140c881104001e0711440c02403240c0d1852944c04107600c0d0b08042440a18011403050300c01140703c484610024000c0e44803900500115840758402108402c000031015030400400e880005410f201c1c0c0c1800800f034840c02002505050b91802e03000c0c1000142d6125202d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 71029561 1250 71028311 71028317
    0x10201111201090203130b07020a030f03020c03090d0501091202030d181214040906030f0506250c050a0204060b030a0b090127060510091a031312030f1803 68
    0x5201041032180080c094005604801c600d00790040c0500d48032030340116000f05050811103043d00f61540d4070007000c142200c1c50401a040a000d910030950000c8441d51420601d09007035003071100805c5515660300034242800d114070580103d00d81400703000c0d40000b4006411a180c8078079291172040c0a540ca6001042c00701003645810740d200d2100b840d0b0344944964582c07000142d0507100341000304840350010020b140380310320410400006c0d10200c0d4070030040118480d03854090061480d06206003000c0c0001e010740316160104070110208429038403000010503060500308000c00381b40c1001171810801e200001d40152a20700089039661403080910f1186030408030a2195100341014800715140a220304203100103078000b034140714416002e511148200307040e000114240d440b00014034801c09003015901180a0751000e000000c0034062480040505208240c13035401c028823450054000d400300070f465000c0f90042d040c02d683c8030360440d9102c4070080394140100c5109003502e0b290145078180031008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 71030811 1250 71029561 71029571
    0x3030903030708060a120321050a0c020f01020307020d080c0c0d0c1104090201020714030a051005040209090607020c04050711070f06032d09030c05100603022806030f0e0318010201 79
    0x103494031169105c2580c0301c41003500e1810b1125502a5181581821244260034401030300d05081e02480c42800d03c03440f1484804a883d6204d242c0103828214110500c6840d0303401041001030702a000105a15651114a8151500c0d500c201d880e181c140605003615506025030100c5c8081c055101e4040101a17001c1d00d07003100b0360355015081004407000b0310802400740c7c001d100108184005070010f581e0281000c0c042e1503801e5525a142030030704007238600d808603450341d6600388419400c0141c0380b6030f40604110002c1a8900381104042e40c1c03a8644d01c40b16204e42d482c0c03000900741d1b41c400e08183d440856000125000c182e100c21601c24484001d0090b4400a4505080c40a00c0006110113411030500c00403140740031000f40004c103003c0d1a0355007041c0c2c2030200740300c9081d00081040020000320400b0900000300241588101b200d000d22a1900e0720051418808200b141348070b000b0ba0904030b554038200002c032012180d0b0408050f160002516186010201d684240c1d500c0f030f02c00340c003d0550244d0007000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 71032061 1250 71030811 71030821
    0x50c06040c0f1203090519031a04031106070e0405041103010c0c0210181a070f08071208040503030a050912040806180609101104030c08010c09061e0c0206040803030903030708 77
    0x3420f019003d000a88005820845400c2c04549516184205840c00942c06d4603038a400c81012802c0c052556910801006c02c014550300183c2d80035400000b001420160030020350007400c0320041180030b48215a2140450100005441502c0c0080d402074002e0011090b040d0300030b0300204402c881640500781440b400420030717200b44c0c0b059843c03072402214203402d241000c0c0c50824140e000705618010707010402040000c0707091160000b082da4820b002042d0394007024509880b840c8900300c14113060104c50414040042e2000c000e1300d6011242d0480003e2076500d07004450714101c10034080c400007080c0060086031004001c503c162103100b007602000c410103881c50a080d500c1d03000b1100c0702420f40040c1604e4818200e04c0c2c1102d507900700081c41031810651240c8514400f01c006520850362a0340d5003000d00b003400d0300071103203c0062146041032842200c0c0c1560080c1050092030081c0108500b040b81501195581401c0e6030180c4490402c03030782c4900c2c00711200c55072540292050008141e070b03580010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 71033311 1250 71032061 71032079
    0x804140105071b0203160816060305010f09150509010b070b090607050a1110020a050702120a020604090c051908100e070c0305030613090308060a061403010510050c06040c0f 76
    0x180a41107030764409849410940100d810030440e000100d915025041b5903030110841995100d010300020805070a07480030035200e540e4507a520303610490600d030424004200d800940c2904908503618031178085010340b90100d841c4200801c1e500051b50081030900041000d11070040035110040c030a07407400015840e21036200b5516030003224401d0015100304520954984105d41d80e01446c00d03c02d0440754101540010101660000d40d0120001000460f221041d440e010170b2600c0c030b941081014008030204d9801040c3c0a1096000c1e000540d0b440360201c485a80c410000c580f031260402c0f04001c1c680c6801400100802d10507107140c241300688103004109806c84582007405005691241400c203c01c40d50306035943d400040241f9408071096940712070410084c011410401e00c2a035403c0000c2c60580200201c1d449940c10100420000321074070000d01e801001128155981205c8015000c581c600b002c036203038800d0341992541030140c141408100140e0381040e0081c1c41100c1c1390362000544482400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 71034561 1250 71033311 71033321
    0x30b0901030f030c021201051e010b091f02030d05010311360703061e0608071404030206030c090a09020a090b0a0f0305070e030d09050f060c0d0e0607060c08041401 72
    0x20b0040707140c0d2000c1c800001d014000400c201803003d0240c46411459a400d5805c40e10f0450f22100c0d840c04214410801888083c034a5000d810180c1c0300174106901c200100d40002a00301070045e00d40003107508180818020810f840308d0302140c240a000a43c1c4910344118904a00701e00745010b030b4001a8080c003446044000007c0a1001141d112070051020680300a07100000c0c041205041ea61030f40803d40c920000100d21030015203560883c4039600e403000090454400030401c0041080601e040d81c4158071039130845048a8044464548948400b10b400041d031040c103107455070001c2c0c1c40d04002954030300c6401809a0301126154500c0184da034244503511849600030b6400014213002400e0240d5000340e000715040000362400b07003001104034011900d8540c03042800000300e084404104010b1401905160442e441518200d01b0003240300001a0356200c820582d40511010044426140c0c4440742991441900100240213518200b200a85040026601901e40301d51040d001740c0d04a0050140c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 71035811 1250 71034561 71034563
    0x7120c0e010b0304080906090901080105060a09060807060c050c060406020a05010c0f08010302041a1002012a0f050a0507051506030105060a0b030705182e080405061b1207030606030b090103 83
    0x60b0320b00e5580c3e1030f80c80341219404410301c0c9030302c104c050004a40030740355616a01d019200c042d0000809007000c40170014a00226408210090b042481c00d000b11381007c0744038011502d10b401c0c519004640ca1525505001c80d00044c190484e0000c0340010b509507000450034a85070190b8000c11200056040440d02c603401d1007042070100341c07207100400043c1490380c0a01d841703060218074149500308000c001084820b614442c3d10050303440e0304c01071030700d00000b51041940800c01c2690208020000d10041d04001000b00410103101c3c001c81c1402001d8051000c4440740b692260a46030007000d401984100720f04c041e1500c5003e9072a01001611900740f00b001202500d00c5000c1c0340707040d50707507010003120741b03038040c42c0342c0c15540581e4280140191076561100742d02e0300360612a19190300595000d00e8a170002071840303408003c102c06c01c1c440840c0c404101035030000c80d5031107091001c0410350340c0c524144c0300b9081207140c1e0111200800000302d13850b078407003000d90340d40303a0f020702c0302c2c1d00c4c100c2c1004040903080c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 71037061 1250 71035811 71035829
    0x4120305091509030c100c05151504140c0c0a050708071a0703020709020a090512060a050609150d0c1502010608011503050c241303050d110c13060807120c0e01 70
    0x1c151500e02e0010031000d1b4074107192a1000d0304448a03901c01d4201045035a03980e20200c090418005114202e00055502e120141c0303042201c0c500c4550b000c030381c010f4040c10003098500b00083e811440307201805502e1f00940c110089a07201c0c1c0d587c1544603a00c26507071103440b400740040c000320109805010100c803a15030305540286a001c0c24103895900a510485000060003c1170100040c20f8851030b0b040081300c6406400f41240386030400881c000d6840040456101e03800b51020081c403907001d201080c244c2ca20541e03d02002221614206404c6041c503000141207502c02100c030300115030b0540001003a0f6400200034014105442c1e41001c01d03842030300005120380c100000008040c2420040c5070902038008616028600000c0c00b541c10a50190781c1d20a4020111907051083c00b4003049403000d111b4042c17401210240e9260341c1c1c1c40c0c41e414042100303407240c99241d03041c2e8030079895900400080d080c1c1e1026a445296581c002100080f10014102e0307001000010001c0c3c0c00741000c05240c12112804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 71038311 1250 71037061 71037073
    0x90a0501081e070f0602100b0f090a2d0509120415031119050703090608010f030f060b19140d170d090b0f0106031b020316030201020412030509150903 66
    0xc042d0b2555003490500128425000006504008010b1801c010b110316006008001400e8aa020940f0f0030b5010440c018030140c0a824035036190003920b10383c08051a44009011000c0c044041e070451000c2c503c0401e0284040301c200f00a510b654020b600402c00e80e801c84a000300004007841c0d0328000c82c03281440700b103940c09aa0040b0350007274110220240600400514101070740510b48150340b00350420b54005080492140d040542004003640039104500f40803005600d40900206c004a02c1d0100820564800810104000c1140c00c10a00302e0001800ca0010804600b440840303a200b40c8103014054100840c54010350070285274001c415034000c159420003404482c2940042d40c0090005103482e46da6400c42404034003030004440c010603400709144025454454014141c071016002c0000000e04080c450000b103400100701d55a003044843e2801c400101414103a00a0145501c5000952419085103081681c8100100350140080707410171281c0041c1860054140545818075030035502003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 71039561 1250 71038311 71038333
    0x20306240d0b1906030204030b0a0b06040515070f06020a0f030506060301030b04030c050303040602030613020c0c0f01030905030c0106081501150c300e040c0e060306041118090a050108 81
    0x103600003003034050b03002e01805036804900c0c0045000c021580d01110000ba0f010505208000240382c00ca50011080d000c10300003070078000009540d5104502ca11031080465188016884640c40265082c01d5001550480c28060324203102e4080d51110840c0b40003d400075444c0c112440c002d200780e901403040500f00b281540c1c03c6980b40c1417200320203417080e018030418419900c00220200002e5208910035900940c480c28548144200e500070700311086212030050000c1c40030350320b001849502c806411600d40203007105190050f0018480e40b4009841c83c0070000b403452807000e0541102d0110751880e41101c1d214004801c106007160401c2c01101d80c1e40f03d1005250080034420703064113441c17502540510b09010308824202c8481085820000641c002c940810090710313802002d80b071907042080d07601780000c10f0175540041180c0c21071036401e841104084003040c1d082c0c071280c3c40f0010010f01740320016910f004050740580382c403880c00c00b40c900c10000d01c0c000801700e081038000d45040b1240c2000034402030b80b103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 71040811 1250 71039561 71039587
    0x20a050403140c09040309030201030b0d200f03010903110c06031015180303030e060903030108030f1606060e0f09070b030c030a092001080108070506030c0a020313060302030624 78
    0xe10003204450303c038841c0c450041d0340e1240034041c0140d1080e02e92003440c0d444c610000d400d5404a40c1d100d4450300c680381c01680411030074075141101c403640141041140441c81c0008407111000740c001c41c0c00d0340c80c1c44c48442c02c047c0c00c030000c042c00d585800101da8585041a0402500d0721084403100100c10549808016440c1406010599150141480c400011018001c582c00ca541030b4820b400080e10758403080741220050008640000094014518540c1000c0c103181e0740e480740c210918051000090031800f090483c0545104165006905100d6184d40e80c2e0140c94104040e04e010851500a1001c260440c40015401003150800800350f0300355918000305c440ca40e00018800301e03050340c5031850f50f0001888540080701c40ba03000c080030b00c06022200d0004001c0c80d0141c0160403070703074416039092150f596000b080d40e03030003060346006564502240b0b60882c00c60203040c442c1074510340c0f119004604550190043c5224220035103003d02200900744511b800c84d1882c2600c203007001020001d80041142d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 71042061 1250 71040811 71040833
    0x1802010221040b12010311100e0f03161712040e040303180f05030c010b090103021513030605090c0f0103140c090d020d050606012006070807170a060503010e01020a050403 75
    0x809500c50600b0035a84404076030150348109401d12000100c00c0050081041c20100c1c611340c054140d90b14418010a81c03c013400140480102a1181f403640c12403c3e9595010084400c00c3d18210f00941c4440350350308050360413507031108407024042c099100103104016a00c01a00e0403030348a40c0c24105241c0b075a407401d0700280f060811801200035145032850120301c001030582c140520803001140d40b85030314007505003107900003009a80b040020400410140c1d0310004d02c15165006c0c03900761640e852038000c5200d000c0f202e560008261604081c1040750710b10010071002d0981c48103a03101000c0040710001181140e880d0b1024030082d80c80440401c030a0b41204025054541001d0300c3c11443c0300315030300000c0340a2200c4404490756031141d420080c003568400554500d5100000d507019507038455802c3d4a4440c40010242002c000d000070002c2c48031881051700c4607544098182106550503c00803600280000d402120300030f40c2014803215107081d05100301d6a00c0f01e502e5451500341405c1d0799518011078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 71043167 1106 71042061 71042113
    0x40b01090e0601030b250801050312072303041a280f0e24030a14070918060302030304170d021f050901060308041818020102 55
    0x3400107201c5064030352151786865203643c4c0350b16001062086038a140d00e0310318600a150754031600500303241d040c1c81041c0d040e1000711541028501091089180041208035040140742c1c0f40c1d18007111804910060b0015030f031805a84206181c10740c050142803220541e40010608071001c080c1e4034800c0c9101c0308100b000c04400c102800a031480c800b1601c11400d000c0d07a100c801c03c142e41c4401c8600c4040d008031180200c10301c01c0189150040d00100c400b10340359440d04100d03541010386a02c1851161b0199650401c00350305281516414213008241a4400c54503843c010006940c14406030010317000c00400f181c051140c0610040c90f0240b0300304040700395008085820003604142d00011402851502c000c180e44e10340c500c41e41e0040c0002c1d0300c080e28001001c2000300d540348458942c0d0040d000910001e120f001c45844506103a0a62400000e0140c4e200041c4104005404800081c4c44 = true := by decide +kernel

theorem cover : BRFrame.Cov 70863311 71043167 := by
  have h0 := BRFrame.cov_init 70863311
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70863311 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 70863311 ≤ n) (h2 : n < 71043167) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
