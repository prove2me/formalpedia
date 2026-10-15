-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4738
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:34:49.18132+00:00
-- url     : https://prove2.me/submissions/7a516e24-cc5d-454a-8377-18058ea21291

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 851978417 ≤ n < 852158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 851979667 1250 851978417 851978419
    0xa060e0c030603120415030902030a050703200d030e01050a0311030a150b071a040f0209070c0218011a0a021009210905031f2310051f050912070b0405 66
    0x603494020071200401c00645003514004040910b1b141a0540120014408140280d900d48550410b181c0860380074880180914041c02c0152040c0009015503401380c900c0b075540600620855009078042075019084016070807013483d00f03940c2d9410303944044000c1c0004210300c032424040003080c0806000c0581c02010000d8580020700b1140e99100d480b00440d006280020305910300300f0828400d201c50003500603522a101c0d03861240a0225500440e00102040b9010300c041242c4101c4581549051508604080031501544d1195810219400c4802940c203002e403046500c0800e803d4807150092066095200780c0f18070070001c1c014182854134001421040001078407845481e8007081c5c0d0310808008080d160090024020b500420504c5007000b00442405504a544d800d03265003061800d8248101d01343c12095071105500344055064020f1150364025803141c000f04a580e002e003018051000f10814190030041e440c0c440b028003080f058089111b048800e07001e0001e000c156698800c0141c015070310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 851980917 1250 851979667 851979673
    0x6120e01020702040e070503250501030e070806010609170a12030507020a0203060a060906050a080a030507020a240201060b090f0f010c0f030f080606120f150607061a0f15030a060e0c030603 83
    0x3419400749001c2795180b50404a441030150014070076075009030054408400103800b101c0409980300040c2e818048e0030b8110f4030010340c52003c01c1140702c0030709840d904441010310140c004d1013420780d00c44c081d07501180c04500a0685a00005100034000d004070b10602e500a0241e0f1f110b40380940c402d100410748d81c02030b02e000c503162602c003203040d05200c2d41100955812000901040d92292015202e50700150000ca901540c0d402001c00c00d048403480c0f034114a0140705102e441b00c00e1000300a400d48499421400c0050410321000f41103541d02c000c004101030301610304800c2c9110001c0129003400341070202810010005800c0c41c10140c0c065001e41c410760607540e862060b0b0b02c0c2c2d00204212441940600484400d04001291681e400b440715190048088001c0030310089010007c640140c0180300c058400d60703035a100c054509104c4119007005040201c42e5020550801000a941d0007000c0c0c050079001c410210000d4400b19155011001400c0a1a0080c00a01e00348220b904298401c80d40303503002c1c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 851982167 1250 851980917 851980933
    0x5010902030f2e02280f0201021309020304060b06120106110a0c150e120c01080a051e090307210e09010e1602070302090403031d0706120e01020702040e070503 70
    0x602c003051400c40c04034a0755210814110300d0142c00ba8010044842d0150070b42e00f00101541d0254031000c10301c0840b07a00f00d9400742001d107144094200240c0729070b5001564010030581c40e10040101c900c02c1035032200000180c4a0303c0310f0070428010413070341c5545a088400007981c004c40203481d14115040b2051695510014507141082c0c94444d03c100900410072442e98a0902c407540200200001504840c90402003020323b80740090100040e8038510707501504180314424155a210890aa100079084811b016a08204480a4a04413140340c14469082c1e40400700320502014401c40c3c4003070380c200c52004a032a1500f0300701126901984120b80108282c084250302c281404a2424122810700034100036a80d559003139801d0448000341c00c1e1045009505010005a55400c581e41c06203000303550000e0034038042e881d44005040307803010290041d03000310782c20031040da030000c0041d0034030720224000724a50b080c4404903400b900412030300a61144c188684c0c10900040000d054040344c400b2002c5070079071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 851983417 1250 851982167 851982193
    0x50a090204181a01030905010b03120a020706031a0d170c03030f0a0e0c01030b010c05010509070f1d06010c03030b0315040302010b0d0c1a190c030207062a0501020c0a0501090203 78
    0x1c031070f04007114101c03e90b10300b40910958066404502c81c5c600500c00820858030660020b4100350301030341c8101c450310f00840c892450940c1000725201400340d81c10308000000e002c9180d50101082e062065204800819584080100fa0048490b101340b10046044d11101e416a8080e01e0b5001110204030000c08800014024405801400d00301201400541901c00103400110b015001c2921b083c0d0520440380f020f02c000440c00d1280d90b01c14040701000d080100c5c11314408100844c2c0590000300d12100c1e010310400218030036400340d0f82001c02401d064011895600e802e60151a036a80c4461b890300500c0303144803002a0818060b8807aa2280e0700800081e0103803000c0203a00d65000702c01510b46d0951050500014400091005050160024031414926a6160244000304a00b01180055a10344841c0100740c1c0402090001c0c190314209550003603d456a039844460031600200e50200715803040341c0c14007000794101c6182d040c44009aa00c00303030860904601914006808130700902c03401c88580c0c00703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 851984667 1250 851983417 851983421
    0x10b0d110f03150a21050c060a0203040b0c10020d14010614071509050321100b2d0406020c01080a06030b0601120e0a030c06050a060503071e050a09020418 68
    0x81454a09181d500316280c00c0d407088401c181c41c03900c1a401c0030760040c01090500248810030820303411000d480707001000034580b40f402c2c80c2c0d000141d54003440080c03003a8000e035500881614203455007050318607180c21000740440d16220607000000d104070310004100110301c665401012001a03203070580d291990b41c600080f24400b603076464428500b0030500c0b014000603554048034030b1603140c6020200e007402403921480e0556000c440c1c0007800c00c41a00209242000394464180c0c4000524101d6000d9172030103050090510440c41c141c3c1c10121952039803291a80a920340132440540104200c0d211500c03140d01039074030203042c031100340491803030000201041d04032b00804083d41c1c1c0c0030041c1131035a20755200540720305402c0248485680d854903031402800c0000c02810041b640603507100c64500980f0b08140701115405441ca07940b41c0e0600c01c051050b41c50009082c41142c040c1120a040254881402d4000e80440d4000c42e9005000c03c1000840a64580242060303802643c0c40040c210441c1040d0b01c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 851985917 1250 851984667 851984677
    0xf0f021518010905101b0206180a0e0415051906090f0e0a021f09090203091c020a0b0117010f050c031e2a0405120d0e010201150b03040c0e010b0d11 65
    0x107440031120414280c0580711b0715525002c081151041c04100303105a00003201500145444000c8000300850b964552600c041d880004024041d50f50a90b4240750301c038145041e140e40b41080f5915215000b04e041c0c07011000c450b40c1150b42d1741d10100000340e01c03681d21030007510400c122318583c9410081d08103402c040115031080c20030b9008000180d0106410011081080d1449030a8144042d14000050520841c00190b214640117401f501407181c0c50035002a402000307071151001c5611484180d00002d440101e00347c191001515112500300d0304082041c0505003d15004118508000502c0201c2503004040e501078460b412244006210f5100a02c8403150221a00043c901039112b005104424007144a000c02d4104005030b0300c0c007900d030000724031078060719681902c0582c058140400c240b0703485400b4a05154007413000b44000101800d1900f41e005081c001e0b044e013800004041020820425405e40081200d40400d00466a440e0b100c24480c0c2c10481070089858207000d00e908030843c500c8100d031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 851987167 1250 851985917 851985919
    0x109180e01050702160e060f060c030c0706030908160809040e0a0c05010302070b0a0203060609090c12060415030305090a0503150f010807060f18091a0f120a0f0f021518010905 77
    0x44285886c00010510040001d80303c25000380c0301d2a0740e4000b54540d4001002c070158680015031740c52100d254510f1501105900c6503041614100c50180022100002c6800720303602e401d840552000b06041a04092180081040d44540b8010560b4846080814102031032400761401c800056503401c01981a8859001d000b041220840000390502405070f0156030441005803240c0d0508009002080003404244c0f80c001e1001400300300380300030007035003c0a158000410b40b418007218501049210640c092408001d05020000c2000c1d04c00b500d4200c094401090000e08540c44c903e400c0d10016000c20b01540c01c01c508241250012803103420006005003129036941c1c1e2502800c3e603a00080701c08840e46d02d02505d41d41e40041c40081c442402c0e0141c0c40741c040c244e004440b07003801441c0030440c100b01d191101c140a00100c0e0800313003443c10082102c0d00e05540003210003000c420300d4684140c3d01040390600a5010307401d200703290071000611015000010080c120b8005801007800191170b40b120354400d0b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 851988417 1250 851987167 851987203
    0x18020c06040f0f0203101b090b030114130204030309030210090501090509091e0322030b0403080c0f030103080d0b182a0c030d2403110109180e01050702 67
    0x1141c00246100344158010b401900907612685065000034206240164103490781511403948041c1d5420070342507481030f060f1500b42100900d1404446642c0350105200d022100803045a20303111175180e03031501030039014001c071085580340d40303d14002d0044807403404160f0007114001c03062026903004640c100706a400503110f82225901c0c010811000d00002017400465000d2445c07a2030321424008032000701070800501079900c4d20520b00c52494980c0c4624607103414547e03000000c01c0801c01030050960044e416241c83e00d1943d5411411a070984190b0f203800c0c1002c4030020000040c080d0540140c0b9091105020070310010302d0741405c0090b001c4601503007086402c2c1080c0403413a00705a00e01c0b10120803a8130030030480400e40460004650390491414070701d86800004060003004039922640790380d0189140350303105643c64464454409009030000802e582c42e044c101e4011a8002d0b0189001404002d60b5650105500140200a41a000d08407a504e43c01c0c040401c4040d400450800c0c000d00e41300080d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 851989667 1250 851988417 851988421
    0x120709050c0910031b2f070e0703060911030408031609081204030507061806030c030204151e050a0e040f110406080106020601080a080901030c0210020c0718020c06 72
    0xa100010000034001c0e803030304003040010307808584500300c188081c5682501c0004840421000b04100c1d01407078005001000740250780140412840c1d10740c81d9144001714882045000042c6501d4a00000e40e04075079500c010000801003a950705030801410340340e0140c0d081c031250f41c917a1042074284c00217880c01408840d00344000b60705507007100c080a0460394185800d800b00d640d121200c6041080c0611b502c1c2c800400080c00703100707100082003e80d000302841d00e05940d2ba210004014020210703240034071410142c0310701403c10100d00ca40c05480c05490620395541c00003403038040c0a000782d02c1c1c1000d514800101210301180150280d0243c4031408030170746664a0103c0144104802040441040803201d642e404614907001486400340000d000c45480d1040741c1d5044c404083e00e0400c0c164000c0c030a51b480000b609000500083c02d40360303044001e0a010031061200032090b414508840c2c2e8180e0010310200e0002c000b01400a42c1d00c0c101d8450300322032603407440100c240d02d040c0e2040d500703007441d26404200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 851990917 1250 851989667 851989679
    0xf0512010b030604060e090c1c170a050408122713090503040b12040309090606020d2a050d180f031202032809080607020a15020903030c01060303030501051207 70
    0xc6500c03081c0140000b62846d100c10b600e440000066808042135804110780305410b041005043c05040c0c00124541e40303131340c4d1a50350080b00e11b12210220705030220100b25030340f20038000c000342e07030241800034256035080c0c0310030551101940100003e03418825222443e072106030403012501101c07040c01313440400302c21002042c401c041c0c4185103049456120400000803080902e50180c440f601d2420900c880d503040c10b04004100010b541c0004003c503250074810040c040d00082e941c024003c0e58184004141040d8200204600508405054608285081b00700b00500400d60418a80b8030b80c5a10014001458080b000f030059400780720040700c4400d0040c4040303000c004403003407600030500c1243d01d003802c124420142204045680894000b18800c06c0500540204445000d06a440b00404562410010081d5103200c0791401501d10720114485001d00c03c040e4044556022010342125500e140c4c0c09070f601c0c02059144070503000a40b0344000881d040c45d00c00002a202c00f107000c010045070341410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 851992167 1250 851990917 851990939
    0x15150415062001061d0c040b03010909020607060e0601060f0e0a03080c0102190306052e0f090b04030503070b2212090918050c040506010c1707020d120f051201 70
    0x280402c080c1e000090400412aa000d0080101034903001e90075480c101901d148540000c4006001516890b5003440103000e400d0a01040d02e0444030110000305d40c00020340040390042c410321102622050a0401060501038009580c504a0703d05582d01003840c80300369070498041150814066000c22000c2e81000400d4944000e000c842d03402200041c54401d15968045584001201d00d8000c6515000104950728040108030241c0b06003214040c0e81d0414100d554801d100303901401414400c0741d503e00c2030103e1046803c02c0261041459040d982c1e82c4030704046540f07811480702221856540300001c1c040d017040208114800ba469840303082080b40f15501e6101282d01007145104110b900440003c40d0742642c0a01440045190404001c10110b424441d0410500e0b50303c0c1c90241e82041e041c0b20050740d2010045036065004225108440c02295044a0510503040003a40c04860419040309000a001620807035000035140c6002111441c07000340c4c0c01c1e0240c00c600d001c411000100410a10000c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 851993417 1250 851992167 851992187
    0x1203020f011b081e13050111040f170a080d090b180d081e01060309030e1e130216030302130e091002030a021606050a0b1f0507030c051515041506 64
    0x4891040c4c11040c50a4807041403401113480c040720245110700c1c0414041d0038440c003240307030354100c007914039003401d01c0c510310b18501c81c034814501c481e10b080100110100040c00104c0c001503100058998445c1004446405096407020940d00c0300c0d1260046500c000c00301d110200c110884c0400b43c41070f454800402d45030140000c0641804810a6002a0a650604121034040c0005840015602010f42402032145030601c1c440c500441040c282601010a11905403110000448407400c440c03075a0000a0040c2c040d5403180400041900c011004158154000c1c02c0c0804a5883c0310720626560a14414a40c8041d5546050754100a402c80c4100085800031903129038425800761810030071869414104502c100c05a56159070341d8240101e01c40305003d52074a500089542d080c0f0a80000c605400003a40a40d4540600170001040ca041602901000c0b881710381100c1541c1c001412500c0030010f074a0115807864180c800190200c0031403a15100d1a25810a40581202d245003429016500c1003030f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 851994667 1250 851993417 851993431
    0x19060302100f02071203120f0212180f10091407030807060f09020d05010e0c0625030e0a080a06110711010c05071a04090b010201090f03030f151203020f011b08 70
    0x2401c44d011801c8000c04408903200340c404d548200440700b07480e64000450741e40328100d0004034010081c0c0b40c032400084010640200d2201103800c00d4109002a4a180903191360603402e250191548047c9409119031181800c0747c042c240700c005600382950015101c856030301005062400900031407010400715030025008240c2c0c440e0020380d4029940018102d40980d145c100d80c0380c1c1d12030405514805052003581f800c0d28040d81d1090911100b145070078906900c80301c008079007142c0c0d29407401c01e03d445008106040b21015014040c0f594035031403059200c05903014161402d5082100c080e0a0204220455141c0b64105040c0703040003800100459908200801c00e0754684110341020403500c1041c01e0501d0b40101c48401036503240e180c42c0908050381d000b05950fa0540e45000717648004100b46803a00300d040340c3d042c40c0010b40701811144201c024140747e040034070461802c1c0030200f5002500366500306901d01035000c480c0c40d100500f40940c261200c0c0d420b10786050320f080581039000742c001d103607541d00401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 851995917 1250 851994667 851994673
    0xf120c0e071704171819140d210c030e01050f0d05090a0b09010603140c0d080d1506051c0b0a060e0d050105090d120e03040e0601030f05010e19060302100f02 69
    0xf048164480f05800800780c11017540075600401c416890000c0c2c003088400010b0030384094661a0062000c580c035820490140a001214140c900f040203402c46840e80d9a140400d48903080d0b000300c0c00a0001c01079101c114041140808200c0e459030154045d15090b00c2000c0d0102e00d00001f942c2006d0183c8009483d10302d00d0301c1303010382d24800120400701c118403a000440c00020281c2c5581000c030f8111040000d548034076000405040000d0b2a8904001011500010081c1e0780b00640713207000b00103040c1b031551045000040e03240820415440802403039440c428401083c60051a44c10060448035044100d41e4884101c6104101140c0540761941c501080185502500c034181d8590310f003074a100311010f0f807060300304210413241035030010700c4082a0041c1900400662542c2204160350348a00c2c05170b01003804044000890580c800d820040d0340c0d008152080c0110759545402c040d01100944484040300d80c03142d50a107c404092090034103e2380c001b003545026540400e401e6a1812400c448102180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 851997167 1250 851995917 851995943
    0xa0b250203010b150309100e030a0305061824030f1509151905070f17060a030f03030b0102010b030f07030b040c260111030915100f120c0e071704 64
    0x640d80089103010b00e07514aa0240c0d89186c00301c1040e082c2501c01c0050000c0b1032522035482c1c4048000410f8400d080c02c103050014540d02c03a0400100080f10080380f80c2400000030040000300120107000c01443c111101c010480a84800300301900c41d1102e00048030a80e00c684450408203c2240c00c035500300b010322003560000203401083c240d010100310303104590001241e42501c2c183c07507107100d03c03a13101d541842c10720701c440e2060500038620f2942c044240224040d05c2d000c10101e40c0e541d00f00400556001c40700d544000e100f0b01d8040c01900d11402414003651a106d42e404182c1004904020086806400740006a045a40b01c80640102800c1501c0420001e100460611541a6100c4040700006041c40e1100180d1289030b0a45204903a03408481500b4414400303a600c0009181d100300e42a8902e0301226511092030024280c0245e00404800d0160704e00010401d1000009185060003041e200c3c06240d103d0352640d289910958400002410520000e420034407007100003a0054401c0e2200c121076 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 851998417 1250 851997167 851997169
    0x3030c05220503070509060a0e0411041a0301110426010b12030715060b03010b030a0905060709081213210c0b27061b07090501140a0b250203010b 64
    0xc1590403200580c01c40d80c04000d120300e02d800c00441d00217185c100d451394218640003006c0384440300d075842404042d0b80300c0404a0b0410007200a82c00700307900d01502c200316410800c4104c0032401c0d1204c512034001d520344107182441143d1041110203841045400290301e003c050600c052203059a03c0c000c28a5507980503044c1141d03260104070790b030b100240c00150f03114291820000d13a140c044100d030a0b0400e04e00642002b20410f01c50540c0d0455180c441c8042e140d540344000d00020306400c2c00000d0060080c0d0003040020b6070014040310030f903134044c0200c543d96401c1481c5200c2d0b03441000000f00b8440341c8110100045c0300c50000704035600505030291240002503517600140e03404e00f6000300400c0c1401140343c034550054090305041c85941d982c450519049003030080761007482034540001c110510b121020032081f00811240c0028014103104200030b681d210500500707029550003030341c41440c040b0310009118128506849020b034429500d044c04c1f207920b42c0b0035405071610b468200d03015501c0710400200d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 851999667 1250 851998417 851998447
    0xe041104030b040b010f230d0f060e011404020913021c08120606070b0103080310030203100e060c2704090b090f010b060408070b210703090b0703090f03030c05 70
    0x1c5201d10031000c1c40381068030f0944e0540d10140c10015a020211404000d0400c1c0b064503460320650b401c0d2901d00880c0301202042c180d802150001d081100c819100204210456203c180f0084198000704494500c4942c0300d01c1d6034500342c502a50226800340800c0302400700700c0d00e10000c20b100418440d100d07036690814a00e1100c04810030340d0001004036000c2c0c0d84403c00416940c3c092000c40d503440c5040916942d902d0b00200601000d0520a000300000b400c020259240101454000301101c1c7e502c0741c4090b9503800360401041c909868041d01000c900e4601900081d44e989413038180c030101160502c101783d1104121810032683d400354aa14402c40414010100a0302690381d6801811600100c0d40240d0300391a2a0004107001f000c04000411080e00301184401c142c42201c421143d66910302109008c120f4101e04d0080350080048050101194140d4051b0b80028454540d20310030740e81c0e0480a41c100d46100c4005411512009030328000207110342e2140720a202c9509180342000c80140e0724400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 852000917 1250 851999667 851999669
    0x307020705180a0c0804080703030e0313080f163213090c0509090705210d09061706100c0309030506100321051605010605060d0b1e100e041104 63
    0x201000118148a03010303416020320f010b01030490a0800003406c1a6540c0c0c0074074481c00b0400303420140e541c4032031807041900303004440c007070107249070a2094184c54959040d184e0b035100319107a840d480380c800c3c008040c0c441540a8000c50780080607001000c6000b4003407010a83e14400509085c200050546100e5504c0c40008004a16070001c001a40780807171920591404141c1c11446c0310303401040805c211100002210b40541e101a580f459151410751840f107404040600c400c0c01c0c42c019012480e4286500000c1d0008407021030f980c4232120020054030300c4811030103480c455005440c00c5001500c4174001c2e981904581e2180c500b45801960769195641007030015900d01d20700c6403001c1010418803101ea030740f064015010118038990f0001240e0041c1442c0318036007855a0090680c3c01401c103000080d40301200902c03001d444140e44540741c81c511001001489100ba00c60701e10390241c203d034140700d02815100100d0183c0124a1554010000d0380c40700c1d898101e8603803040c1c0b1103003200d0030105004043c1c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 852002167 1250 852000917 852000949
    0x40b01054303110115150e030a06140a0207080a0516020d0b010911090306060906180a090c06020109050a060b450702250b0703110c01030612080307020705 68
    0x4041c0300c14907008100a101d000122840d030b05003500c4000524010350071004403461170007200484080f40f0401d45a000b0044061545806482411b00a0000c9508181880280080b1075425a52804011000c84c01292009028207009000850382a03000710020601d844685143e203001515550014a111460940486854080702c0040055480e18041c1002d030b4080c49001500b45011600401d96420000700514411340c4d580001c00e44c0c0e0707140c400c05e500a445840c81401c80da803601440c5a000b800c210b24044580a61460000a0356441032081c4103100b40e2160241c4007919443c1c42c4d41e40a0a241841d0759408081502254550000035800d4072101280c0e064500040310440c606e0040b140d545c18081055208000c10041d0b02c550100798083c0714105906a10502e000410b00281107100542041c403103c003000440200313140e08112000742d84034100c2d04031260b90a0306001103080e50014402d4526040d03410140c003001884000c040c6510489a104542503159100b000807002c41040404c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 852003417 1250 852002167 852002287
    0x80315030d1710120609060209030a03080601090b181005091207031509081611151207210b03190b160302041203080402031204080304080c040b0105 65
    0xd0b100c0c403815070007564403003034442d015440340e49800310201c032080c980715009041a5540801000708949541038074803500d0082c0490761410040c0c50301501c00e00c02034a05074041440200c2c00680f1b8110740e0216408110300012402d001211401071001d15903482e00c40009000041c401141981c440407540811030943da4000c00c07400b80b07142000604002e04064045540342040340600100301d07000100c40f1615140c82c0841894000ca0402c2c0807660341035130000d503001c51421400c04038455580003030000c000c602c0c08041c0305a02c81c1d01050725418400c0e02c11404981d00d640e5050582d07844c40d4040803c3d006e010b170542c0c00003d1448400301d240d44001004469020800b801c0c04003070b46101c60550400b03040750504514090808004c45a03044100b24010104071200c07001808649050216004081c10fa1000603111620307a10000d441e600b041c09030740542c1c401e03000b05e605185085d0240158210040e16005c1ca006008084035200340011040c40712244541c0c0800c0710000340303138008450210a64580 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 852004667 1250 852003417 852003437
    0x90c02030a0e0a0b070f06060306150302130b0312090a1806180c02061b07060e0309030d020c090c030718060e0907050901080c0a030623030d0c0c03080315030d 70
    0x41e0401c410b440505010381c3e0b58803000d11122a80c4800c4516a58000c08030f42801280c40c50104068031040c5c000401d05410280d203220030710000075a0700305491003202e041d00152007542c0c912046420750800c03a64560b10201110303404074944001071040b43c10240540c0c1c05191140301c1a58090030324018002203907503c4808208143c002c41c4100d5016240314014030900c400c80780001d5890790041c054160f010a20b203d020311080310042243c21060b0302003820b2045010740703c00c0a483ea000076484900a016000900700b0301440491003100c5a40000d0030411107403070341140c0049a07000100382c5000c0c80000344020ba16281c90583c0340d8002e1002d5900e512144480700c052104030b20000e0080310521800b130284060582c0c0080d4071a501c440074460240d102d01003a141103010b00f81c07d80c0007011650762004410303c58020f0400641b03410005504403095250319540813034a00c510010017811841c0c11850501c00111003800464010451404644030714070203000090070306142035414000710f150616 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 852005917 1250 852004667 852004687
    0xc081905061518011e0806101e08040309091104180e0f030304050d0906051c02091302040f0b0328060b0f0c25050405133201050402010504050910090c0203 68
    0x15442ca4002c1001e00100c0050811140c09448504041e14240c0300f408c0c07505880360060b2007080d040180182e9400c0440500140c2c04c0043c02e8070ba0300392010ba0000344251004034503d0120b0203085c0c4108841c4007d5881c0526101032981c40c2075014003c085450b45822000c5107158080040311a03000360716010b56601d0034140741c42860000c14400980074043c86c11410050300750040140c1e904101c03a0100d0340308a0b07404144c0c54000b84100c1c88a150b00c10614025051031a0603680513105076045d0300300384611140c69585590141c001100c495480b40da0b4508501c1c40007072020308503240800281d03804508144c450844202c10b03001900a00450035000c26000e41d042c10422030084801d0102d454240d2103800e4644042d010350050152038019629071340410103444140030381d00002038100f0503a0541c00042110741520b00d2541c15000d2002501045c40c01306602d040c42403074051941615858942841d00d8180070b01c03c0002400074000920001c8006401c024502440804501c154055690303094242 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 852007167 1250 852005917 852005927
    0x250309140409030905100c080f04031a15060d0b030a121b0213021b010c0c0c0b09060306090a180c050a080304180b031905010f0c08190506151801 64
    0x300101d2145040500789004250400010b07811341d0016103094206099003032040d03d80d201c00800c000c182178000203158070580803860180080d41e03c24000b8801002c001c041c200f01e40e05066414124400d061860300402c1c2c5410b80013401210f003030300404a0901261030001e03003424080041a106603401c51009a80140e00805c00050b4501c0f1002035a13401465030041010071038540901c41041d540040c142944680c408191030050034080000d21280c240103100800007203500d4001c690036036512002040190174981511000600076204504554401c3c040004040c0e01a00d2110076036031310740c0307400d20b4000c0c0010352880b03030b500500d111140fa62900080c407145460a500c4030b02da541003408103001a84254110102c1002040c2021550010000010f0708103250f101441001310940c00f490402c0240c103401540c1911154007003089070980410341951401400c90b00d09081701a6002c100d0401c8040f9400a03402a00140500c850100c400300449455402100d404900340103c592003a915a440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 852008417 1250 852007167 852007199
    0x20a090203011238090c03011a010807090e0403051303081206270a022b050106090509041101030c030b130e1e0304060f020307020d1203050604060503070605250309 72
    0x80700c42040c04202e0103040e076042c0513000155030310307106840450490241000070403000c0320000c00030041b80704055552011090b200714401d0200319038500290455024001c0710045a026590400841d0795554044481c1d921800d4400c00c1a40440e0010000c2545038001e1700e4503070000c4400c100c440c104030040140b40c000b602100c92900480721600944085129061070b003018034201c2c00350b251000c0514550751340f441c482c1c0d24502400180c1500f94401c1a03a08114101c03105502c41013050b50700c800601900940440d00a808600c4001300e81000c0d5100390f102480c609090725000841b60408000501402e040303c6904200c15210380f08160044c00c1880f488498421003445501120000c07001c2d607450303001c0d5104480505c05180106000f060007403045601c065802844401ca000082ca81020404ac0f00c00c8200c0000c0d20700f200148050405124007000d40380005c000305942481e20701c049a1642c020803881d80d81929080102d0450741240080c841d01a10940321507107030314100f0324000700202c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 852009667 1250 852008417 852008453
    0x10f0b04060f0b03040501060506030702250e04030f1206060309020109050319120909090309090b09040c090b0a090c08060306100b030c07031b050f0706091d04020a0902030112 77
    0x5482020044464001e0b4074608880d40d0507510343d220354560a15600524155115540041c400020851025404150f000700311061311000d204410b04181146401c0c504c03801918100030b140c2d0082070119005060101d28041645401003a030b080d2404001c040d6940b0f03030f220350b001c070b91192505000c56800c80140d101910301580100001c20b10703280300641e0084202809000b075146500c00340300c40c9208004400150100348000d00c00d100d080e15009010080070311030714002c0e600d4580c1768401c5143c01096180a1500100d07040e69050503c0d00c0c202c020b0403110b900d0382e03220240711740c005010741d094040c103040140d40d9103804416140501c01d05040c0b040051203000c0d12032015106000350040c2c0350943c0d42146001001d40d40320703040d5140170f440001c3e550140c0c01d081c00b0312041c500c0400c00d0004005c03100005c1881512034069640c6820342d81e14660340561881c40035156490600c52000d0622150b100307000400b410441540d03607a0f074004991080c0c00015581081e0800e075402c0c080131010000b83d5200e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 852010917 1250 852009667 852009671
    0x10606020705281e21141f02030601030b090c0307020610030c090b01032a09080318150f0d15140105030f0601030b0a0e0109050c03100303080903070b09010f0b04 71
    0x5240c01d00340544500360f000c3d44401c2030041c0c0c0007000110b2403550300e81c0a04032403030307030000650401070b00310f800301d120200f084450075400c0c2086c0e209510086400c0c85921502c420070500d2807081d503440406504018140fa041568505c0890815607544041c3c6009043d0398a00580d82c1c104464001c1c02e00800920500842158400410008403001ca00604407440036070002032150020004802a103414900d044160207450418050300d46e610b143c54001d0180e42d121121403076550075030540c0364040c1c41d05030031981c08103810301c03038507800c040e2240f40550039206a85441c0c01301c1c07140001e865402141042e00c2d0b103555075840d0251181d00c2030600c0c010309090700d08181710880c03e8000030300303503c0010144403200080002282059020340c0140e40c4818004200c1c00415494512050900200340b14000704035040c0390103d000f9513044411640984002c0810141c00d5040d41c40a40f143d5002500c5246503210400425000c15a42c54800d40a90442070022600b80d28488011742a0b84000c071505115034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 852012167 1250 852010917 852010969
    0x1118062103030415060f03050d030b0906150705010b100f111c1808100f051e040807050a05070e0f061002030a03090c08011506120e03030f06060705010606020705 71
    0x440c00400c0d66405070b8011aa5220b00c491010704e4005072840798004015080c07054008400c011001c1020302182041d541e00304541c881e203908004009200344c540030380016140038410345002000008114950103a000420945e0400d008030320036100c00c890031070004400c0c4210b200b00aa01100c0000711320300410003030019040058000519908240468082c00810001e681c1c0d00003055480d20300401c1c0340420345261046a201c020050301d00850302a03501803400340001d40551403c0c8240b081c0032070807113900c505503555603181e00c031036881807600f82d03034511410700114001130040000e40701501c4031020b0b56519080038210b07480e4449010304128411400f02443d9684954000b05132805080c240c1340c0401c00600c24200b51a0695150300824250350900741103407502e01d1458038040803180943e4800307031131038441100302e41240d03010f090240080d0000c00128407003010014034540c00c01d0f4010259860302c11540d544508443c1585d00c0030000d40c224070b100f000145482c60301209035101340904c0c44604 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 852013417 1250 852012167 852012229
    0xd09020a091a0427080d0b061801111504051c030b0f19080a050714032b090801050915060604120b0a06180b100e06070f111806 56
    0x3100302c1c005019903034402041c0209200d102044030360000900880110f03034454140414564020480540c0103410900d142c1c4003070506400301c1c3c17008281d8590f80080078400d0001100c000007071180305500c62041074403c541c5820402e11750350195101c0c600401000e200c5071000810222044d10749824549480c48a0166071581c40c3c44000715881207074800361000c040d2050002036811500600098802c2683c400c080000000d0030000f690300d03041c040c0301c541200c3d0040643d1821910800301a000300d00000c40d4005031819002100d041544c20942c401c40d40b50044682143c0d01101d10a0180c0e02500e20f175855003810038245900041d081c0d550307074600303400d2a02c61003020b113500c000100101500000100107010b03ea1005014220321560703110503e9008110702c010302103a0000c94030131003042030840f0b0303501d003d042642c040840c0075140c01e081c2145a01c1d141442100a04c1c1521004034040c030403065540c60540700ca403000007950042105040c500c003480900d0745040003042e00e10303107404040350301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 852014667 1250 852013417 852013451
    0xa0203120f18031f230105010c062720040e19060213121506030c050d050c040f02041e080606090a2c06150a05040207060905030d09020a09 61
    0x406030511008120b81e034640808a46004921603c828a059000c00c00c0080801035802c012801c440c0710128a20340d801103201c2414081080c442c1c02e0206a04250341400500503402c000141400320300220b084030285201f90346021251502101d5010401c0c400c524503007080c10103401c1041e4207450801081c03814109184d901c1c15110361104070703442e100740034804010f995011610308208040725079407c590340c1c052101540540880c100d0300068001400206446230784151800c42ea08401e6242120f482d002c1400f0600080f19020303034050240307007100171698441d40200b00102130b120000680d02c41c03915440e00d004007490007110484500002c02080028800520150032820031140040242c4415001c44010100d080c0b104030411000f40100030388001d400c111038082004075095a829584214242180040e022141da81c4416100d50038412420a94040c007a114840d4200061040032515000d1946d04a0104406010f40300c000c4c01d811420b01c4c041040040404003010710a14241001c1d40305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 852015917 1250 852014667 852014677
    0x807020d0f0e12011e021b0f060604090f02030a120201060603090203030d050c0c0f030d050c270612011509080307080304030e15031608070e010509040e1e0a0203120f 73
    0xc400c03500c0c0030070200f4681080d4031001041c4800031540141c603207580d000e18041d4000d032580880c450840c10380242d9004c008140c000c000080c03280074082582c3e5003420040109605102516001c01c0088680c005840401c25000500e006115112565500b06002070a550040d000181003500340b101110068900005071a800d0b05016804196070350748054a250500801c0c450100c01c0c400c13030100c01c0d69424044000c001e107003200c2c4800c1c4150b56540d071000c03002d44075a18869100140540407003081483c200400d40c00b10070010142803820104985c22204813000703030460000d09050f440704940742508000c0d1007000f88105030195080001039221036815001c0100b0150600c440440034042c3d580d980000070110b031482122090b240d00b84205001c0321a140040203201050701c000c042050b0318061651807075081e005956141c40c2094150a12001e809081d404000c0c80c45018002d140351980c2c440d47c4108501000018000009140105071401d1103200444030041003c01041c0200400d0901f298 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 852017167 1250 852015917 852015919
    0x8070503030f1b0a0c0b0405150304050d030e1c020f0c100815131103040308010812070303020913062c010b0901051b0d030608010b0a1203080901090f030807020d0f0e 73
    0x401c58184140e503d82004080301000b4001061014085a10701003600170740f050359426903100040c0003001a42001d144803d80f07000e40075178003001c04845014442e8000c105181405420741c1c4103034207050003001200c61002d4528004d80c002c00d4200c200c1003000c111010400302c080740c0e000c000500b025070180021101410b000f02110a070305c00341c03007540c455801d44401003400120400058045115040154209540403000515000c1c00020908000120a0141c001c022641e41c9042010b5034150001c0d44901d1000360000200a40c000345048a441407070000e001048031030b100f6a882e1171000c0e01140c5400d0341c10342e0108003100107200d0490904190340300c401080c07c0140e903c24400d20000c0904111825800d5984107903110082b82560507040441200c400c0c0000b07124801050b020010b040d40280500c1004051a01000700441d100702c070030a07000f61088000041072105038486920501d01d0701c20903030101e140c0708148490164100841d151005c0c041c60710320a02410303044004c14072010382c0c502c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 852018417 1250 852017167 852017197
    0xd05030708090f1204050111010603121d0a0605120703180b06011814120c0607030822110109060206040f02040e12031306060e3304050702060108070503030f 69
    0x80016000f00400396007034a520382150031008580d10340083c035902a02a85000501c404a104411041406500b003601c2d4008141c2c540307400150b8080361115941d8541031034956540c28001015107611420341e016003055030715143c2c2c90000c0c0c49042c0403030704003606000401d45005c81c2403400340d006852540b0000e921004000d0203880d8803004a44502c400c0601040c40c1013100350005407080002d0801c20300c201d050340c40c0c4012004540c8225100e2103003c00c1203401c0740d0100104000a84511000740c3d00100000c10820803810f41700c1807035101107085604940400d1a41c580c83d000d5a00204100c00034589071000304030501c2e2540d91b600240460714002400390b5110244525400d00074818000314200316070030b69407a85815684008081d8800c0015a009803602d2000b081001402c20340c1071044201c103030680c10380c03848280d0b242c0e0130702052241040c00e11451602c0e0140c03a61503004450142080d40d0062040e541041c02080c100317001c070303400103110760700c100328881c0c21000f03210035202600488859 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 852019667 1250 852018417 852018421
    0x40b04020609060f0307090e01061815020f06040f0b0109112703010e0601030c0e101a070204180c0608060114031008070e0703060906030305160f020a0b0c0f0d05030708 74
    0x304880740244c45a1100842c1c020080084036a40700d200360702201c45504078040c4036662410240c40d400001501d800016481745d03003e0041c0308000004101882e2148100e4005c000d080c1ca0349402c0580641d41112910f44c0c2c50351641c140520007103414054400d01c1404c00c69810f04510000e0f5a00c1400e0301d03c00c4201111000c0c0c07000e401d0706050884403400c090002d03c01c000f0350180103500d03010300340001c0307c480c0c3e2002e00126610312031005107440b406440c031000c02c080f070030109401c03682140e41c540c00c58820b400308140c9005071102d01072460300038a02c1040c0c6080952070310780813411302601e402c00800c01c01c900040004580e03000c2c4104612580c50210344c0d65a403100c4c0300000c2008640d400c2801a44a0110005100c07942a00340c2d910552490342c3c201305154803003081e001030301c81c10310000c3c0020304284150310b6000750b85c40d9541881c81c4030340700040310f419099020800c0154030758006c950125000c219071440c05000c3c00110301021011001d0104203040b4940500b40e400017900030f0341000a6240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 852020917 1250 852019667 852019669
    0xa05040e10051e0d050615090a02160803180106060815010804030e012a140f15071d090907060f0309170c03040b0315120f1c0306031a061503040b04020609 68
    0x200e491180e0170400340c2c3d025141258800360f030b15542044036402054043d00050040e1418420b4032064050380002c07075034038a8681c4400e080d0360070103400252813004881441c0040c40c0f09215000c0102007584030703060140f80103c41e42030101d480380c0300241441004c004100000364001c01450410009082080501307811440160316040c02002c45280c0c1e45e40d2241c044140039104c280201c031010140f046400c00b010b1000c0980d2941d484030420140a00d55001042e040c6020314846810300c1c10001b4154003401c9140009018540f0541c0e40f00c4c9150081c030400d000aa40c4020702c9811a103d6040600c0825002d03614500415040000660805404030316100101414800c54005210004c0b66039168103003020219070200c1e0464100d40b0818040030100c11010001c2010428110740601074006010700c69610020041902d203a1000c259640a0101c0098050082c58403040c0076010041880d241405c140102c211528005030b83c0400306108101c0042c01605500c0d50003a03050b13035881d0b20f50304210 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 852022167 1250 852020917 852020929
    0x9021f080109110d150906050612040b0406022205040609060b1e0702030601140a0504050603100f0608101d0a020d0f030e0a0b0304230a111201020a05040e10051e 71
    0x61003001030b0a082c00c88058104001748003d4058407070862003004090761b9001008154030803482c40304261a03004000802113004e1140b403a5005001e044094031b071111030b0010742c05242d480c5521803100110418140020305103442550080c0002c00c40c204003203414140310000c94040c5140c4164014640480d03080e20907401003c0d03840440e805403c41e101541c4546008000309401c8074024000c44116200140501d0203000709401100b0240180c076000001c25149806000d8080c0d20a540350b807100000608007804201c01c8920b6010b0f01c10006000c00303400018003954a603842800042e80c0500e41300809030380c50f40b2280304403e0744003111101c201c0070340c682601d9000d240c601082c1d014500c100002000907007400118031552041c06070009248180b40000e103220f1088425040580c040d01c0340c0b4001905111401d0300103c8001c1c03600821058600e07043d401e9a10104903100020000300d010441900b0701c01c281d03034014840c01d040942003030520f000b080040241b000c0d00c0042d50094000881c07507864403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 852023417 1250 852022167 852022177
    0x6091621060c0c11060a0807030e010e120a17100501050304061b0f0f0207030816173f16110d08061008010308070f03050f0d09021f08010911 62
    0x8a00148000d041201003e0400b542c03501c0159203642100c181c059162518004541003641c0ca83c661b42c06503180c0301c074101c000b0029000300043d0fa659518482846001c20801060b094810101e40e0b991041c50420040001c1e0381100007181c070103111414486403480e20216202590710a10f0440d403242d4403400c2010142c008204490141c00140240c5854698030180c0c21140c91404d4460b0941c06a0100e022680c0b032030588006026001c0902820241d552954500450396018441c40503109440070150715150303000d010b002a480c0c00400e440ca550400030030700590903080f40710070868a203030000302c0b44c0238528004000058446851150000441c0103a00000d02c42c002e417000c5450082400703e0142034418103aa030b140c403480e4403941000c015482a03d0250599900c00ca069080c5000c40d074889603203681c0c0c00421010300c5003d00503507410f0000740000d0a400326002d00045000c0c125801400754200c00d241040946e500006844071803607400a207440d0454a560f0800144410079140143d4240031f2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 852024667 1250 852023417 852023423
    0x601050409091209150906050a0e06220e0c0d090201030e0a0302300702090603030714071a03090a0b09100e15130201081906030c060305040506091621 66
    0x1400140702c1c1841003188420310705441944602c0440768407442142103002d807405170440000e10703030340c420300845210790094812a00c080c100700310048004d070000713901078104018500e000801d58074403801d1140b40001c290014140041e12054a041c103003400c0d4501d1160081c0d0440e05078035108080b04691080d0720109010444205450340c51210f46002511098500c0450000003500812007243d4002c0d48458418403240c9800d0700c1c0343c804154284507913090018070082d8140814001000850041c03071122540c01300520181c000a421700702004034085da1401c24084210301030003000000c15001401c035550076000a00d102682c0e94200f0000c0c6005030620640744040d0410000340c0441d180051080080c1d2040002e001840d0f803961352410a01d900018064005801507000c2401a4000343c0b250480050303010021502c15260340302c1c0100c900282c5c0c480c1001940c0e400030401801001e0044980040400024280c17000d01e028140d80d100040b40034610903100c5540365075644c00d0284076031002040e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 852025917 1250 852024667 852024671
    0x60c261e0d06230405190e120a0c06060f050a2105011a010e09091c0219030c0b0604150b0f09090f101a12090102090a090f0e0604080703080601050409 66
    0x501d03914810040144640301c3c01209043c0701951000c1d140c1400f88a219201c1040800c050070500e1100c0000b03004801440501400365860360a800340304240100003200d0540c4a034158244249401400c48011390301c5100d0310035030802e0600c000e541d04107820040320120010402000c031908480402d5081072840140301d03610b400c6030b40ca65841d45120400b0a5007098032050aa40c641c0c81c180701010b5800c41c0d89000d42c1d084a08540c2580d506c0ac00c042007031521a10460704c41003092044502440841001603010982034600c40040002d141e21807075214005a60900203181c00801c0e5001c042042d0140c2c0c10007410210748104c41a0401040d81d240c660014104400340c01d10b14152144000c2c243e520f030000901c40d44010451074203508844407900d00d46022a858168521150107070500090b101380d03900d5408100c20600c642c0c030708042070050300301e011000508941c460545421202d8100740070700e05411400c108004a05c0840564501640508020003155580c500403903052090760002d0325258 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 852027167 1250 852025917 852025919
    0x7020303010e0114030a2a0e01180b0d0602130b07080d0f1b030e01090b010306020915070809011b1a06030c10050301050d020f030d0309120c0506131506060c261e0d06 73
    0x10f140c03003001c034101c4006e22b14518807040310740500800e49081956881d0880d116061100004005500a10381d4400d00d015645509440c1d12900b24a623010a0080c2c6420700003160501145029100301114144d440f041040802e04a111144011181040f50740a055503504140e801403000c1d00000398141e4880800c0c0203070340c1c691421030000d4115140950296442034140c01b000062b0070301302d400c4260015a0103013001d425400444840046090700141411103034100350020769245928003444000f0170250b0389a141401c24540307007078003140c03040d440340d01150500c448080e042421241501e40c01c0d03e607195031881600202d9141d0101080c219054492941d1410450782d06034020003400d80321303000700f80d400040400c040307466074520382d80a0800c2e00241e001c240090075000079091100d1044034800450241450304204131100b035170080d0042591000700c2820801c254841c10351000711040440020340f4480404240d90081d036050316503652044c4803000c412070224081c0d402081c2d054106205003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 852028417 1250 852027167 852027179
    0x510081905070602030a05071b09140603060c04060c0b130f1202070515120403031d0c01020606030a0b010b03190609020909130b1b040e07020303010e0114030a2a 71
    0x41035008165118020080301080d203038804011282d0000495a031181046400d4035810807121403488201e06020074828001401034040c000c0c0200c0100001440d0010725007030701818145a00280040c1440ea01000248282508080c1c03000b5000d80180381a601503803004c8442802e0b03e120b0501400c1404480300f1202082030080848603118466070a440d5965507640a10408400000c0c90700e022007414048054005003c040655019000c0d1070040342003a5202200b03d411a02180b00744400d4100c4685c03100c880d601084419003008040d8001d08614406884a041d4400c0600a9043c40d00740080801e0040c181c0010000c00c01d0010641080410343d601d8440000354007980d4030500038803100c0001184a03401c0308880c20055040702090000740e450b1101c001d1000f80c0d02010000c118010700010842ca00c4406246108a030300350006c41d643c1d41401500caa040714143d020034047c4018020b200d11944003c54130081c940d5116245d803030180d8600c10f0306091009203240d1411200700c00440010700c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 852029667 1250 852028417 852028453
    0x203190f082d040b0a0509031f0204170609100b1807091a0c0d0e0103021209010f0e0f0a0209100b1801110327040603081c050601081603051008 63
    0x40400c00c10041a82c41042c1e4261200b4083c0348111100b49209006203c100c5001d03c0040590040c002d080c0d03000c4105090800b1070802c41c040ba500d03035155012070b080c441d44884600c072040162100300103220910b4a802e009503542c2c04591210305454542107603000c40d03160040203c20007545104402c40c00c0c98900001090b00c400b0384540c9040354402301180d01e020380000200c1d28001080009089140304050303007559905d1031442854101369080100288a00c40b8105a0380a411104004103000141c030075003005a0700c0ca02d040007410b400031078008c800d404001030580c0301c1070b5050351240000c0c3e942060451484040d0360219002c1000040ea401401482d03010a0318030007426201c0d01000407050480542d40e00071804414281d03105d00e504201c168001c8455248005801400810555201d90300c443c001e4214050003102880c1d0400100d00d644034034002d40e503101038203191043c07c52800307002c84203c60351140e40c0e84091540d6000410a44192a83c0100180400804540c002c0390b0680394654 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 852030917 1250 852029667 852029707
    0xd020f0627012307060e070b0f040f1d0a090302010209040f0b09010b031e040206040906030c0e16080414011529030907180e0601240c0203190f08 64
    0x10001c3d40c14440f410502d0314581d4031407400e0280f1000741c0d05060056803604000e1221307000c00c403601e00c80d90600150b04828400241810701141d00d13410384441c81c084d0b88840f00341c0c582d04203882040603110041c604c0c9030200e014641c805540c41000c20b2104040c14240e0084c883d0210244d046410105007850006a68100203540302e406d840d05c0c0e11aaa0380e00360609580410354020f04241850641003401010501c0a140c1050004111502e000d580741000400c60300b080e80116100000c50340200814500401020307889144c2d40008604e5494040c0e0050206030010002819500552005a81200d00350300c0b442e50b002050302000640c2d80c4031600f00d09400304180981c400000a040828101000d007410f0340e0007215548020400c65041c00401502c03540340d0042c0548042da6100b00c01480c0c2020402c2900030b040f01031510010400b03204044400080e407514040a010f080b420a40050310001608514101503500a5000c07118031314044103604640f010140c011703e00420061064085500500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 852032167 1250 852030917 852030919
    0x80429070e091620030a08060a27020d0e0a140f0c0901060c030c06060623072307080f030c060912220e0403090503011a0d020f0627 58
    0x2640c14001410020071500860f0503040e203100211445544900801000044848940d4034134071310340141c100030786035070000f220541c00034070003000380b2140d0b00740140c25401034a040225940c168007200045002c0021100c0064120341c2d0008441c200d005107503015103240c92a6000340e510804450424250540403610349011500a00d00e0b100c44c81003001402d101a40380141626491fa880d015040d581c002800c5420f805010f9007808040014220b07202c1c0001074002511070010b00b858064072002c0403500c500421007001c004000c003501044c51103c90440c0d41c652154440e1a003011480c0c40b81c10710407250b018a40500c43c841a600c1d07100808000b501c00010380e0710407140b641d0740315903c0941e1061610241400031030200080708140001c0020061405490b19080c41110342e40c400f080d040000458050b000155040710600403844c3c20b0044605c080c90411425000c8500d54000803c184504c2000a214880440d030f03400e1103858138016500c0b8a1000006400c0c14441c10009186803082a01070b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 852033417 1250 852032167 852032177
    0x40b1806040b0a030621110904030c0c23060301030302151f080105010911190e03012703030e0727090b1806011a0703080604140c0d0e010605010f08042907 68
    0x508940c1c0c0101030b14046c140d0046e240701c00001c40581484001600a07200358104544240a4404541d00ca10320100622140900510a41304803c440c1c0f0009007460100d8400d940400041012941c0001d610b80740c00d0790482c2030705207034440c85100c144e503409401d0403000001000070001503085042d4007441c101d8600d800c05011145265054895902c2090224020300c44420310301d41e50b0510802e85a0004213002d00006102c00c070b5a80462b4451030020b01131015500180c200c20209075040c000d41c140c141511000b068201d0a10340b0514034002440350000c001e0308241d90b00d408082e10f9801080040741c02006803070b928204840b03000101500082c080071a440307144000102861060070b1a0700194600c44502d040092564048071056005412a544691544098450a81c21049440c002c9200c20604da41d0f0320407600e07008041d50151544101203174036081007000300d40d070015020f2180b0f44003441e28844a41d558030f44500d80702070412126100030410402888511506034505000e03803040c0d00c80d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 852034667 1250 852033417 852033449
    0x4060809010b0616082503110a23030f03090106050319020a030803063001060609030b0a05070210112503091701180b0615040b1806040b0a0306 63
    0x403903003039980d208010381c2c0090041289410a03c00c40201c50155031090240341d117080000480140c0d107424041c4243c4a0030790411028040541240c161801405c5030400740540040a88886070600c10702e14600ca103044503141980300310007040c021650304640d40b0201d103490341801a082c0e4001c003404d00800c0c1c020300c66403940f05000328452840d5031040e0f500404502606055130b8901d0080e070400751869400414041c1c103804184850b008040c000310401c0229040307800e940303141609640c5140c0c042c8060001404003800461180304c00594031282c174410200311a02c580c03000702e10703241c03103000e042002502d0031000008602851008190505001161a8510201c0b1101f04004110aa0000c02003102040c00b084603103501210303503c0303071688040001084071080c2c4e480d003000015070101325103503c0031000b08078180ca041281311002d20210b283c0b070b40c2003e0800028540500c9601d0340a8615642d03503400013140c4d9035620840d03011300b41c3c0c0c0c5074264030303031841c010301401910690055105115945034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 852035917 1250 852034667 852034681
    0x615030114030f2811060c2d06041101260603010534050c010617061302031f1d060403020f03130603050a0603060e072c0f07090911040608 61
    0x60311021000201e210404c4031004810042a205910041115030003144200d01101d640c481c400f0741408a1040054a4540e40c2180003104140400f0121240213036007a00a104902d40000d0403644554842166180092403500503200c907207681d040800c84100180390340052400180200c1d01480084d40244896190341c0300408034200b900005019001c0d12141e00180d041c40502036011908003800e00d5480c124603100c0c0c0c103096402e55004031104079240d04209802050070400c40d988550300c0c0ca059241c0710659800a511106400c821800c803240000c18a0301000305540140321400800c180f030000d500c0c90110365601c03888102d03410f0b0007600440f210310340801c0010044580180022800310840c2c0e0900105800414020f8608802c2d07580e103200200009446214480511080c480208030719480c0180711500b481c20255051404810018159407607811112400c0c1c008144014083d0180c2d2010380c02c0b50000c10582c040d00c1010304048240c2d00c4500980000e00503a0110341e6441c03c281c0d2500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 852037167 1250 852035917 852035923
    0x5030c010c02030a0806060a17130507080102130618080a0b040201080604050411130212250f05030a020a0e03010f06060f05040837030203030f0106031406090615030114030f 76
    0x41119004105c044000032001d00d00800105419a80e1b400d0011860030450180b4000d403a044070300408911544c1507200a001c402c1220800800c2024000d525143d003411040034032402d54800c0314240310f90f071800f010740c0c1c540441c0c0389000307095200212064460f00342046024030a0545007640820244004501c1d5410513000c0c1070710994000d6000644502400c0070f0082c600144000360f03901c640c0c20301a0302000307030340050f1560044201c00b0100150024881c60903c903584084200c000780325040111103940c1741c03c0300540360300c401d4000005849400c245801c0d103a04003000c2015505500e00780045145100c60f034060800c0c0c0ba416a241000246440d80503509403003036004440346984840303c580d0154240e0b8160003070101400c040c0c0440d03041c0c51200e01150340800311044003d030b040441008100300c8002c03079040c014a0303d4a4103001c0600c030368070041c10400001c0c0009026594460002d0416200c9904c040329210b040400c02d6a65a916258402c49000070f04015100b40a58420b036081d44c0307000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 852038417 1250 852037167 852037177
    0x1502120603191106070209010b071b0e0109020d1404030309060609090203031903090c090219030b010c060f1d030304050706051c0b0a05040203091c0201061203051e040305030c010c0203 81
    0x7a022403600107169407030304002c0400f21101141e00113020452a40140c5800b40c035076000b0488542c405464004a140c0400944203041e1203990180d000807040041c4500000001c0c11610a804016500e1941c2310162001e01940383c40b2400c0a00b040f01480100741e07050740500303015070094008110f8591220300d103006a4444c07420107549a0320a01040300e100080075400405000c403410001610603542d5108400184254800d6510540c00f1402403a07403803040704494800ca07014036040110f10944400a0b0029200c0880501050780d034420350318540499a12000c00c0508030003003105070245180320381d03a5a51084408a540d4003440e040041d00c0c82c01142940c42c010055805424038001c3e0100c58401401c554a04507840313881c20000040c140c581e44002e50045140c4409400416030501882c0c034202031100c03141045a141c0311080009044c5911203000f402d901d80b40045c0e03182c6101c0245264030007108c0c0906400d03080007a00208200d0008024400c40e070700140240f1202921600580c1c40e80a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 852039667 1250 852038417 852038443
    0x6020f0310090e070302060d06081911010206010b04030803040507050310151d0c0705030409050c0703081503072313060e070e0a061101021204120e27040309031502120603 75
    0x1080248011f203460000b414203203000c01400610290b640c04c015161a440c11030480b83c40115401410500050701c8440b60702000c280000e000329494007510706054440e0380f102401d044c501101040c1000300a2001134005d140c000c04840c0d804441040d0000204002a910142c0c000014800a0450100142e103440d00c08031500b41c465a0741c2e01482c0402c00ea000002c1111540030400010550b000d481c8039840c041d070070305010b040d140c0301149030203000c04070007400300b00d840300481c99140000d0381c00040200c19a402000c021100c000840e0f070000004000c3c00016902010310041400e8005960703004104035203810041348900d4403240380503602c030812001c405402030021402844100e000c6c181040307500c84e11000040ca0308603c1d03a4081000c000646003106e91180100e048004507500079024262100c4c112020394081d0300c0801c0c83e0514106a0500000094101c000034086c180102e1a02005681042d01c0503203410400000f54000d500901180d03864001a6021801d5818000383e25003e841d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 852040917 1250 852039667 852039673
    0x6022a03030f0c15070806040b01030b1521130c060c08090d030c06150311040209010512151807030f020f030a2f07140c0a030b0c0706020f0310090e 65
    0x2c0703940c01100703990100441a04a104448015814504100003184180d8960740c840480d070400a007040b00340c859031100181014100181c89100d03a4601c80e000b0032101070201010342d83e81e040340b9141d0441c107007070b1420420345060404020509102e070400c0107400303116060242c8155180d29050740c00004421014001707a4040c007050f22507051208010340307100d010b4280221064400e82d581401c2c1c0d0340b00d64000ca54a80c500c4410000c0000d80700250101440c00c80701541030080500008001d405080030072242d059100021500f4415070005070380803000041c0042401104100c056491030700140c5944001901c2d21504541203981442940d0209441400c01841c640302c01d2881c1000d001200069540d4442e14100c81c407a6034076104054102c2c014101200f6103601d400d08042050703080071a000005604540010f041696805501c18252580001040b90513121980c440c8080c0c05405d100401c00c51000410302c0d401c4103140051482030302043c0100c000aa00c41d000740c0c013070711802412500309078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 852042167 1250 852040917 852040927
    0x30b090a05130f051f09020f03030a052a010905330f090106210312060b03070516060507090510020714060a05090a0f05130c0906080a1506022a0303 65
    0xba42818001c50542c0c080c90407601e201003114214500d989030010b0ba103817416901d40707074482142003e5003210200c200840156080400d1000054906e02c120311185840d40700c424800e03690260505500d111042e0460000c001060142c501203a5961101e50500103280e000203400041500707049103209031280c0b00d014000d4580700e4426039154058041c14205044d521520042890215070406611314000b00e00748102100ca00d0801034082030302d40c01c41c03161190910300103200060840701200d400c9886460915541c4010049079900c2d1a115140200300b20f0405003444290382d40252140706403002228107840b80d01c072008060340e0794511403062032960301480d0a04500d81c40c0120107002a1481410940d180c0504400001c907040034039000320b40011000e0700e00f80702c80c0c1400d2450603600070f04083d0401c0798151800300546040402d11030081080201c100250608140390004401004c06d00e462800c010744450300a500c1720300c50340c0c4408505060703003500b403200c1241d01a41042040b01074041c620301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 852043417 1250 852042167 852042173
    0x2032d060618031504150f05041707081b031809070f030515030a05070e070c0f020d0c090f050f240d0311070602010515010801180914030a030b090a0513 67
    0x581d14800b254580030384203007100505031124095100b2885804100402090510704c0343c1140d600d012041451840c0c40304001c0041d81d002d0152060240741422562648500d01d454a141d11815403980c20052540c025001000c00c000080c1c28040000c4071000d07000c1c140382083c88242902214002d001501e00a0311180040c06540041e0704071502090784109000d000011034500b6195001c111101d03031020301c080103043d28050a20750028068a05080c800d40c6c03035141c40014001c5944081e00c902a520f02c103504010352418400d005114414061001d0810f6020650050204544054000390f40758006151200e074004003017070a40310306645501c41d420810078010b000d010300d07008506202d0207804d1250f0700c003804c000c00030051001c1c4c0d002003000d10700f0441541304401d00b00c05442c148003001c80144003085011002003034030b17603120034001510811402c023085044d182c10001d40b00b0303001c00100c1d0414581d0682081103914420703a0040e40c640c4039151208115002180c0242c8100441d140305800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 852044667 1250 852043417 852043447
    0x7050301140f0609090c0d21020d08370b0301060621090f0204022b020703050d020a09030816030e0d03080f0403091e15080f060f0409050102032d0606 66
    0x241c01441101c0c40c140c6c01c140840c1c500d5440c0320342503401c1010801e1040000c40c620b6007282040445101400201541c004068640600500b48401340500c12107034907202001b2038104110140e128090f01310920140c0907107801000f840011038081d50904201145460184045807980b105814941b4420202c504c0d030a0001c0c200084100c07202c2d18042c2042002d42c0d12400a0020714105003020b1210034810f0002c0b80b5070f4110a0294186c07140180407110200b6000000d403040400d840300d001da51108164001c407114685908000e20310800440d0310103401250409400006d840f903210044e40d049800c08102e0314a5500e2401000204c1420004075120720341352025401c103110342440c1e00071a40b00c5150950312400ea2005103520703050f0302d804201a0903034111900f01c110840c01d007401c031030500c240c0b003000c0760100809550146a0440080f40c05407201d51080d081d41e50000000c48d164182401101d84464009402c80d021070080c0c0c014030820b11820000e18065a0010001481d00c014a0b64a0752 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 852045917 1250 852044667 852044671
    0xc021e04090b010e07080901090c052e050a0e04020c060105060f12010902030f150f061c020408010204030c05011403040312090609032a02130e07050a030507050301140f0609 76
    0xa00661910807a500103410392150324060440c04000301064640044004c000c0300e0010004401603042ca034441012446000174501034400549440c11150b0300c551500842c0e09a480c0b0b21406203e103407100c03041c2981e0080140c65007501d140e0703468613200c0303074402084140d0041030a04d5a15400c01c800401c0245400401070158805440840d42450303214003402d04900c109134000b004082d000010000d8143d441a501503224003000382c560210700ca01c5001c03601622035900398030300807103000895000c0c4030340200042c1c0c90400090300641d0f94603190580280030350800d100464080c003005002041960080541e66004a0000d40450942c0d179a81c8084078000a240c4c200b9400f50b940703241000124801d800b410301e07914001d03140c1c511107084c00d54442044c1d05109450121078400310950340016130362804040c200d8031003c080402c0b20354580103040c1c00e00711598401680109508400401c000e00440d22204581040b0002c00c01b0f5074001307510f810807540441310040c07030714900c60010380d5900d0305521b115 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 852047167 1250 852045917 852045919
    0x8030a0b270403030f0920011407061409061b0a0c08180f030102091018150c06111206011209020a0b040f080c0d080c01110d020414010c021e 62
    0x1981108115048400c441c048a08450800c60490204014180c15000340f281c00e070702d902c8080142c40440d48588200c410103202c64112004100300304070300750307225124800c01c103529282410750b1070941e45010703401040711001902c4050800c1303001540d101c501049040c415010000d00c030384220000404109503a200d843d040044c00724084409000c500d484000d040184400c02c440e488140026080020020314024218402d80c010061300d5510784911910380001011428040f45420581c405c6201110450b005003200d0b8100e0980c4503401940400200c0d240c0d406940f041020120403404021988141c0802d02c0040508001180b4035500c9900010403112032050300141c0c40060b40e00180c41110302c1d0b07110404410001c5010303c0704007040c81da54002030081d5401046c0c0c0d03400110109403d11824a0b0203003e9200106580590300400e401050011400001403661500380c1824100203400a0044601e00031074101c400702d295003d0310503082000d4008140341800340780c2e8030306086041d00c03c107802 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 852048417 1250 852047167 852047179
    0x2303161508150a06180f06110c12030a0e13020d141518070201142707120605100b0a0503070f020607020705090915130b060102030a14030402060c0604050706180308030a0b 75
    0x1d4484000c9950070054803160b039403000304600349555035180003940600a0301c01d40d510841010502800801c032030303407440b837810622880c504020010b281c203150007803402c504c00d0002a2012010305151b00c00306460700c1141d0001520380702c11360400e10300e024012500fa00100d101c1c402d10780d524240203146a0043c0380d4400803600b401030142d500b03040c00701940c0a00a2401000384488142c0450400e4101c004001c0c006024442c64135120300c0e83e504560402900c181c0e5a500800d810400048070311020748640ca0209980c0c03e8116001801c0794002c591800008901804507000c1034030204030076014180e180d00070041203041c10f041050071f60000e000c00c001407203040600040141910985032042e100e00d40304540382441400e01c40a0304000606540c1150002c200b03840c0d01603004103101031112010340c00d4581b69030f260720108020f44030f00456008035210780000c00040010004941c4203540090f0390b03d42c00712200d030045a400134002e01008001341d0040c00003822003001a480701c1050380c00100301c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 852049667 1250 852048417 852048419
    0x31b010912050c2b0311061815090a080307020d030501210201030e010f0c1e0201060602071208091302090310051e0a09081b010507092303161508150a0618 68
    0x420301241889070100c020407030101c041c41e0100001d200c095480840180d48c00d40601070b0040540d290020f0008a507141d1060401140c15401e00300228008140c0c080034842e40c0382411000690750f40c01c4203140000003400d041c00070400e0450300010a581c44146030320f0710064403040e070056000e0002e120f0070a029659070b501c0002d6a050a018415071080b0b01d459030040b2480500102e0700240c02c0074085015607050002c100311644e80010714400312900450382c0c0401b01d00f580f8250640b489a4402c45510441c0c22842c0c100034402a03005100c40d400131000c480b4a031408100c4d10b030581d0400c603580041600d03007804003841c040301c0814090340020700989c0018101c10564070203005400130800300035844180d1080c0044910244210740d003115840c1072054410303141c804510f6402c1700c10601c2c02482d16192802801503101000100d802a011100c50354209844840382048513246894210000e8400404121702d8420303d00c84102e01c07000980f140c0242800c0500c01c0e1040410156007119074514030304 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 852050917 1250 852049667 852049729
    0x10c0e301204030209091908070f0b0109021909030803072006040f15060b04050d080c101a040b150f040e09100b0f031f0209031b010912050c 62
    0x40703028504040605501c9504500501804040040038000581d100510415000010301007910743c1e164007983e070591300c00c0d107850002000010340d540101854000c03c004146004c858015000440241203107101c2c00541c08401c44003c001c0b803201600980d810004940718600c44c0c0795511410b1484410442440071310014545001022103040e0707810801c0c040f428040018000d400184501202803d000040c10141803501c01d101c4c07403007842d104a14001c0500c042010090a40e111204020b0070744000618050948007d85118000113640c0c540c01d40c00707a004c0d03161074400e20400d144003a0061072488602100340b0b825600a001c00c159282c02030200050b25010301c405c90384030755141d00180180031920f91840042d140c0c00c1400d548503070031718415507106450014140d50710414051007051107001c0b0721900e00c000e00c03030075142580600401e913416102402d13081070120317000c50a1781c4140700a40e43e030041500441c81500c004126401503a00305079545070215480c5120031113001d1481003061800707 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 852052167 1250 852050917 852050923
    0x911030102130e0a09170301030309231309050f0c10170c0708040f0b040911040311100e030a21080402011b0c0905040f0c050909070501110c04050403050309010c0e30 73
    0x6907446c0e84c00c100000041c420154040c800400800800804042d400f0085555a104007081d1005a00075481d01c0039030121074481e504211034054011099404004500c0109a2543e02e41c0d10024010401c12605a200c607104003054501000010584110382c0c4604100c2045940400b03420b0b140c0341c000b8031001c80c620500302502c0780142030f0083c01c5c555951412000c5025510300881c4200e00084c02d00007080881c0d401c0500b0b89441408a40501600c0000b51050342c4400803005859018860f500024040220485200320461040e01000440c07a04003c8102c2d0b0f10300007100c0090001c1c0c002d910004417080b011850f1514140300d048090985a00d031280002141d00c2141d080c8e0b0108800190001800305a0807150060107003a10b01800034500902c8290741d90800c0d12401e030410050744454a05200d041c0181214410000c0040c0401c0c100790030002c00e242c0066403161840d5280101d23506846005110b425030702c40e0080d001c0000b080039a40001e4904041d0a9514462000c030a80d00044800c14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 852053417 1250 852052167 852052193
    0x9060d0c0503010f05010311071104110c250f0e0c09031209040e060c09120712060c1b1a180703050d02011404260f07060911030102130e0a09 62
    0x41d03921a03490350301d445802009408568001d6050610b041c00c501915240c0390201c0300755641041d440746500c0801d8011074010020104044000030740843c0107280d9000210b003107c00340c101160070386201c80c0380b80348000003140b09204606c500800c1d4941041460500300b8219841140078a04508005039140401d0405091600e2104000344c0001c00c0059854948030b00d00c000c0f860301c1c0041c10741d49020440d07140395110b1080c2d0b00303200700c0040e45001740c80d400c05c12618001d0f0a0720f044103101d500e6185018409010100d10040210341d0600d40300e0603500c504180c0300c8000c0c0d080f0460501344c40a22465603801100034209503030f03004204440580d11802004500300851244008064042c8005002400c40f41b4044401411008034014800812480035494500d140101c00e901e440520000d402081d5104102c454014031601045072020303c07400e603020f00980c500480c80c07404909a01c1c02094204d04c80c8040400c9001200c41050048442c4c00b6520760b40401103400c0003070443d43c0c5071944c030100c805d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 852054667 1250 852053417 852053441
    0x3030f10170d0807051c0b04060906090902040e03070b0601050d0b09071e050c03040306181401022a19020111070807141206220c0603090b090f0c0609060d 68
    0x841c14070340d0b241d5800400603612032202e103041c90602000505a11066241120310800c00392103e01108041c1d4079580540c00401035101c0802c0f0301ca40d103010500240001040582c412850100f24007481c1c0408800c030f803500e503401007030034170f00b50343e400015942070304042e494052055541441d4580c2c1e03228105145d01501c01c540fa180f41c0d403480803500d42d201207008a40e120420500b4860420090350000030703102139039840800416040150007441c1a002c3c500c4c807010b030030450803050311300140d201036008003624202c50541858040c4416852030184508420454466100d04c0080d06883c4400c82c0303030350b421481498031400c400f021240031840e001154000c81c07180d40001c201044001045540c10035103d03000e0b222561200f0100000c10b84420b002012408404102006881d200c1d850b0710702c62086650008405420503280d5500a005180d100f80c00c0341d0317a18840020401002e40001c1d9071981601138001072209a0590050140e26000304080f203401980c184040d260070b00003409410b1803810703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 852055917 1250 852054667 852054673
    0xb0103060917180a1a09061b011104080c041a060307120c260108030a200102070303021c09050304060c03170103050a0302120a050306040b0f040f020904110c03030f1017 74
    0x1c0035400f000b42141d50342d44051700c0082520fa5604005111a0944900102c1200c0064943d10200e030318500d0343c080d402980c5425445e10608108101c1c00030090000d44010300110707202408040184011a40340072555130045400744038072412032400b00011513102e14030345809140b005480010a080c6c0d1007140d503440208400003007041ca006c801808002031a244c55803210703e254034081d0a2612403284200f5607042000c0c0c10700014001141c6a2041000480d0740000c655495141c20000c00079084a024140c4035845a0245000301c3c605001c9c1c0c15445811101441c9464640802940d030f81d8504c050032401c0c070080481c401407a0108404007130017107003d0340242003103011500c1e00070306004041c450100c180406221400c50580e020040d26488841600c0019220001500003458502621031881e4010b08009035a0700d01c2050f0f4028144210307056a06204680704403280c0f100038042d005050b4420360091001803000e02c0c40c8024290050711031052002c1c0e55403200006503002e00c840d00c0e10f2400303074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 852057167 1250 852055917 852055957
    0x10c020a0609080c041a01050307140d1406120d03020a1b0501060611030a08040b130609050f06012304050402040207020616030e04020a0206040f0c180501031e0b0103060917 76
    0x10f014405803c40364411101040317407040ba007001000c0072159000d25030400802000003000c65006000c007000460610b48800e8035501e203840c0d41c0c00a401c01c43c03c002a0700c443ea9020400600f1700407100d903800c08101000d00840b110013042100250000c0c001d200401080000b002d0340c003144800c4441c0403501500001c91400d09010004d0b0040d40007000d42000c03544100700719680294003c0340d480c1c01c243d010b041c03003540d0780f04c0c0e0100340707450b12581d50007a1003d8070b030101c00003c01100103032807407100d062030080ea10705a03661007090400c81010318032070b014900b20000c5000d151415a0200d94005d200170700c01410004a0b40220b0403603003100c1501e02c0500f502011040034160040b50080301010200d4056180444800000b515180040d03c014400c450b04140710042100f20340078400a4054a10b40480b8802d1940e6414041c11082c401039403440258018245800003020300703ca8450741100124100d64a10350301e0340001c0541d03140641d0622034560034860124034030310003842100d1030140788100d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 852058417 1250 852057167 852057179
    0x9031e18170d0203130b0f0d0203130309050901180e010207051f060b07020d02040b0d05010e0703150603030e19120305031801060513020d320108070b030a0209010c020a0609 76
    0x1058070a89410b05550040c022145456000c00b0b542d02a500c10040c596150190006448414040c403203d040c0510300100030400039950000b030032184180a036940e0300c131155440052240c070340000e001c2c0040d136032800b00c0746003204d0300310f50070524100b0880b000040c0342c8842504c40c01d090480c42445c4264580358403109003c0450f05020716005084082030503854108242e0000354928841c18009000703603100e00c8000816580d1711a51400350f60040c1c0248025940f40200540303d8500b40011079400802200f40f180140051061800b901e5068944180e40744c031503c208480c00e0304008408e400d546c0002808910b2007182644000018420384906481e420b08401d80f0101080c08503040e503450780b40600c100a181d95850580c0003544001c080140d44480c1039020704054820340700f940100b040010340c03c0001e911042c3c1e140d510464441841d00b5903903254240b160322078030a07102e409001e0005202003512803000b60300524580d17a0504003005801c102e0350205400001d40d610640100e03100807410404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 852059667 1250 852058417 852058423
    0x9030c0530040807030f050309150c010c0315030b10090207050601052107031709031209280302060a170910110406020a0807020d0f0b06011209031e1817 67
    0x2a60350007031000303040034100b0120301d0b82e8181d80d12000d400141c0c071030041c0c414480280200d40c0000000b506400d04110140495480d507031268546c2406036291282d40c2e0380b00c1384a4070070740080000199000c40c20310314517140c04804000281103101d05043c80c420004141c80700744014145075102d10041c203080d42c074000030005092140d0b18184080800440c25a02065000c14207000b5258400003032000001c0c49e060800302400b8410360650148980008840c000100303001a0900c01c2040303c44181c6010045515032541180b10303800900c40140751070900040c50410090007080c0341624081c507032400d0102540400d00415100811240c0011140c03004100440c010b03090020080b00b00b003450507103070030802550346403803150181450030013085000440d03440c01002101030340c0004078420200d14505021540f0b440030703036009011800d1500440342c40710890203103184141e0542c46807002e221040c18060604400501c450b401c000281c85818646840f12030180007400c8401440414108111aa10700e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 852060917 1250 852059667 852059743
    0x2070804350114070e060703081b04031419050303011403010b18040b0f0702070b211009141b090103141810180f0302070305120702190e0a09030c05 65
    0x100948083d4030b56081d107900088401052380b5107000c081660700c0041d070b9003620080740450f0140d4000060000248070251651220300342c0c603881550501140007003581c10039122020020025003091004001c00d020781c08100c603280d4000390001c40e114140340300041e002e00c446500a00c0c1c04649506200601400300d50180c0c0c0044a180b041c40319040904c6c01966070313510b80c414407990202c00034003408040e003122a2000c503051a01c240d00c807507040c00c0c0104203141159025005482c0c0c600390151842007045881305025901c4440146000480e00c41c3c0c2d510075501ca161214189601c0321203206074001c805180714805c02010301c454590998000c00bd80c00d00c020b42c4110780f401400c1c0084c420b400d4100642041c180e542c0440b43c0d680006461400b23901707042890740701404500960703e466040c98101c03c02040360b24802c441c840148a11856000a6029240101c54010050301b00180011003980e0050441074000d05001801031460f50b14980f402080c030444c0702090b1441491100b0403808400910 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 852062167 1250 852060917 852060931
    0x9060a050919021c03020c1c080904091a0708160302040806270304090501031502070b060609031f020c0c030a0f02010c030e3102070804350114 63
    0xc4800e04041807519920002d291100320301809148000c0110340d51041c040c11420340c6030407910b45900440c01c0203505c0da403005800e81c0c082c2090b01901940e00544910000300c0a611808007820703c0d9030b0030241310081c910074070f0454a0303110190308164000c40c0c041c8043e104003002d6540380000d18050f81c0d4011481c0100390f07608141350040c8001e0201d000301061440e4840202082a0354003500190462100859054030280500000034085030b40051504014103990158680c01040c038aa00e1201040380300310380d000350005a00a01048103454410000c02c50070000070103c61080e03041e48012000350b92103508464071554001269150f0074130a010300400e465044001d01402e01503500d0744c0350360840d0400000d0400804580500030135000b90742d420400314018001100c00104d03940c0b1259042203503601c0b0300000350302a100e8081482c00b802151801d030f07481100303581064500004100b0005c10058071003142150f4180b0043c000450100d420000015880045481d85544500310000040a000c06c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 852063417 1250 852062167 852062171
    0x150603010b0a0e04080f07020901080a1703042310060e0a0b0f0102070b030a02070b01060e132007050709090b01180911010e1206090d0206010e07410309060a 69
    0x2080f004001200a81d403181e003000007140d441112001c10402803142010080d440400c080c00821100400151085503a100c0e00c010009031042921030015408115002800c031001d144070340d60101101c0103008074076410441151000580c41c000b50080c0c500d1f0350028900c002041c000c00803003042a02422480300c6042e100b40c1040714440d0700007516001203021b0307001141000000306203008020f60450f44032a4010184078400d5031901d00050440d108150b01d540716840542c0c11680407d52807040d100d821861070105541a084102c0100e05600070341c0064540307004610000450041c10301074400042d02c5817040401560410003002c288008841031703080d020346081c50500001d50405240300f000b000900300503d000101f0000214a43c00c0207041d03405502551003841480040051916552500c1e42c00351416680c03124081c11511004548840c001a940030300340000d1001140c0c200160a440e82039565904082c030b109501011103642560200400002041800d40091001e40d4100b5203010341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 852064667 1250 852063417 852063419
    0xf0206130f020603041713090c1835010b0a080d020304090207020409060f020a1d060703031d01050903131220010e031209040e0a0b040b1008150603010b0a 68
    0x18070109000700c1a0003801800008045028004450040d003403000841d45410380e520010000403d43c200280324201200c0d0900e00780441700781c014031215400081c2c49040700340c9680b030800e1480b40150710707078040144071a62240d00702a52201c08152035070b200703030720f0004a40b0021740e005000c0415400e070300ca401c80b0381080840505540e800f1040340c0446038201e0016890342e00030300009006000b24200100f400f1b01d0880c0d0144510701c0343c0c028000207051920360090814601180c0004108403c40c9180d001d0340411040c00004c0c002d80c010b003003c941114848160030300040301c4508580081d20303000c006c0c0d070011800700c00155041003400d0180c0400301000c2c0d000c59441d40c0e0a0850740c008901b04040d038817400f0881c604c0782d20502c8042c01040004084440b40f140192a1050a80c80244118002d5042500c01d0b6022100018038260381644280b4058684e540c640300d198410300c0c044d000c400e10302c1c11031500041000e400c01c038010007445800c7c50104503041007001c2600316003281c038016016040c4214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 852065917 1250 852064667 852064673
    0xf020303151816080a09150c030e1506040f06150c080f0f031e13080703020a0b042103110406110309090f011809020a14031203070f020613 61
    0xd403074010041d80d2803030111580c140700055000d950010181d880544400410550b40f001020042050075907449102190b12038480d40000d0360110701018000d402d01c040c02c0c00341a21603030711081050341c40f81f034001190316038400641c3c01d003401c0c00b03146080c051061050040e58038052003406048600302108125451810340d62000a0701001010f07418007040d40d5140092203540000c4980411090b07034000c4d0303240d50446446910360415034900000c001401040e481003441e1210440c006c1040a0034065403450a40d107504055002510840440c0106c800307200010740d8040940b0300492080040c00d621004020345882c004e4a4034483d002018201040001c1d82c144110860301038130009d00e4100900c03019010500d140d4400c45418a8101070404104940003c280b08001d0680d21f0361138407a0300022508042c10155060300c10080d5110724420010018284c074a00960700302c2d6806000d036004640c6010603d415500111a044080303207201002c4000c0c25070521020358021040c8008034445413a6807 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 852067167 1250 852065917 852065923
    0x12090308060d150e030a1403100b0708090a0b030402120c09060111010209060409090b090102070b0604022d03060f0d0c06080601020307050a0c1508090606060904020c101b0f02 77
    0x1401d081d0041000c6094402845804000442c143c00100b03002d02082203203d600c26581c0d4050f0348080d0003d12494104c1d0758001800045070b014070505c200c1d100300700341080c420381629400f141d0308540d16202006003c40c0794950001d850010194680c0d0203480303207001e0051114550160901c0506900640000740d0144e654940b4071350006d00a00e446e00815142d80c64150081c0b05990780b040c0d0010022800040034401070704034010341441003100000c2074071a0f2060500341d024000740123100d000344400040c0b02d818240d01030008201042c00790b1400319485107503113030041c01d14903441402c20340020030030085040c0303002c08950607101507508460701e180b1a00d49188074031450103008104100440440c1c4aa88204141e4212070f070403206603144000c15242c2640e43d001284910061a49020408030080d401b8080041c440c5e095040500010b9641e0820031081d503018041c1c66038007642c01d01c155140d41c030040000dd144208025400100340352400300c0d00702418229001c00b02001052031b0143c0c2c1581d808 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 852068417 1250 852067167 852067171
    0xc08011d0703180506100501031104120305211015050c150a1103090f010501051519030f0213050906030613110114030c0d1d0d08130b0f010612090308 66
    0x20b450000741c2140400701a00221022a102800520442041c41040c0807184008802ca54098804109444040c0c1855165024501c26041c160031003415500c0400e010b00e0080c0b000d000940c2844070200d0050240a0701c4440c155607103510101c02a01c140700d07039112105c1d5606140d0b460b050035420300310b8031280941d03190009260b03c0c030b9030000b000104000d4103894001000c1002d03110075480e00c0b8640001c4966139500d440d0311940c0b0540c01c01c0000103003824a0b80389840c0403c2051245031609050302110a15000c0c4c2c03001d40c0c0c0030199504550741d6038200920150824100b1089030030865450441040711f96007025050030712036046441804481c2044010031510290320200ca240c0c469504c1c0d0041c1d80a803042925030801c0840003041101c01c0d0b0310342d80103104400c1d06600400c080900c41800c69050700030000020002d42c00700702c4401d5a1401a040030740e0184078280c4802080b100e42e5a00206a04180c5c2e5908420b44034500500986030041d221310051010b1100400400b9001e4600030042100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 852069667 1250 852068417 852068431
    0xe030a0f1b03080a08010e0f04020d0c090e0109030e03070b090d0f02060d050610090609061107030807260304020d030302160506161404150e130509010c08011d 70
    0x1445240c6040000740350580806018505211410350396034100800544d0226102200180c20980045814580809014005c0b0800f4a450358a90f40300d40c240903040114280c241d81541c44048005030990300e50080e101c2e91419035001189080683c9005483c04c2000c044e4180310390424034050041c202c2c40c41c203580382800c0403100854005128246000d00d40c0e0300e140040d4002e0300005101c41112a030b5040a0300480d0140c9417200170f4640070400b00d0382e81285008400c0040d11503082017100921a100211019001c90107030f40301c00c0c0d903e80ea206183c1d4040350003110300296851542e25481a03400040c4099448044003601d03500d0316900007101040301c20401410b040d8007042d0151000d4419000d000071a1348602100c4c801e0500d5005001c2900603040341034001748035402c20b040741400850680e0111425811060110240c0740400d031850007043c1043d503044011501c0c402010030b82802424080c11510000003401d41100000415032001600b0058880300030800c1c42990300c01c511603250340270b54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 852070917 1250 852069667 852069683
    0x601030902190617010803180906012006070807110705010c0c090f05150d02090103060902030c06030132091b16030e090a0506090f0402061c0207020f010e030a 70
    0x80c0c00e200144140798500382c40c901010482e080800c001c0c1c4c110000c08129084c80315100c5840e031b66840d07119941e22074445a00c002d4142c180e680900c5040c444e008940086050420221008100e907104c1c0a0070003500b40c200950b80150706012510350400c0032103400c07200340c0c40c1420003400c5401c200c035a541d0851150504214203070842c0343c02e01802116440c0a0400035005100181c000e038052400360100b600c0b400d0100010120803002803520188d0b00d4406a03000e032070784495030310b1900e030f41d0010146144103982501030503149101c42e59034800154060300b074019034210452040b00150000788074068140104005d803000300303544d50340c410340f000340d00c4520500f514a044c1c00e028901e201c940183c043c841c0748000000509010550403204500d00300f0340554545650f40c0e0b07181da0401c00d40f44140c0c0c500d03410960200200e15160342009a07103901034000750031a464030008260f058681d07882c003140121100d07408182c0400b10303d800c903030601a1100928000c42c44044400000e51501e00092000340040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 852072167 1250 852070917 852070931
    0x50f07050a021e01021e090d02040f09080f040305010c05030f04060f2927040f1109010608010311040c0f030209030a02030706170a2a052802070b12060103 68
    0x81c800c101011030b400645180f584400c80b00c0c0c880c1800303074019201c0302d00e040500d1900c2030715150742d0b07a054481c9407800514071800c140700c607000e0000a002ea60102d400140e110012000403400c0b00000701a041240d9000540d21491420001d0071600032404a1003001410401d2280440d00031a5080e04031b900074000103041d2521288400c000c08814043d00d07001c0e4102c041c92014850050b840000c4164103071440040e4501001002c1071141000c000744645480603c0840d0205801603440c016003446200700807524800311002804c1080c0981c090300000d00c5580040c02041154081680355020aa90030300c40350801080c003030722184042d0740d40e804159001c10901c0d101c0c0c1e001c11094000075009001d8412003520380c90014248614000c005140046c08004101980014800c2c509a41810b101da1031b54280b4005002c13069440211103001005002e1040e0214006101000c21071600034280601242e10360310f6020b802c0030000d51041f00308100510140b0580401d54040f140e00000910b8000b40754 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 852073417 1250 852072167 852072187
    0x30a0b06010c0213060f050d2310050a020301061421100905090616110705060901050702180403020f010603170a0306080d050a1403070c03141606021b01050f0705 71
    0x260807001c8065404035104c24800400e8a4592041058902c1c503c030303c00c2c280740c8940a1101443c13130030800070115201c250f24041c10b030003082e81000d503801c0101e055580302006050110142c85054074400c14240d40040104442d03500100d60034903071440561910300740381d107611015080001071810840600c0c142000954582c85a039458806069030080401443c2404918182d48800c00c898888003000d2a1440d4103515000e40c055242900c1000c000701070150502c414031606801c4958214140541401920016640d0040302403249940030000542031829050007031500301400c0d030404507649026414800700e5a80a0f9082c00390340050840c5e40e42d0301605030103c00501070756100076a0b0b8083c040c81340840c298440000d013048441940c0b900c1103400300503244a180c2c4030945000c0c000c50401049400041d00507020742c20500403100f640c9040c02c030400e01c031619041d403100046902c0c5900244035080c2c1018041c0840e418081a40200501c1c03401c510390b10038104029081038144040400c0803210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 852074667 1250 852073417 852073427
    0x608130305090f01030b06070b06030c03030c060c0a0302071203020901030b0619080c0f0703020a0b010509010e060103051f06050409150803040501121503150c030b060d1512110901080606030a0b0601 87
    0x31040640325a685842d031b07081420b89c1d888140c40041c480d01034038040c0901441c002081e54442c9070601c002e8001c680310509014030540c8058941024585c0a010040104c3c200000c141c0ca00c0059031400f50ba03c03c2e080000404885a00d01c031184112020700c2550041c0d07a40191061103010b03203003002000e50316021440145400348103042c9284440000380c0361b04141d408560040c4092250302484256602d40b410231001c500e0034001e00144942d900c00084547d03100740c01543d00000303501942c2d2400e201d00c100385a006d5500e5008a0042140068200040c101030300c5400c3c411030b0138040702d0b121a428004043d03141d101d90301c0b4090420442420400c44d60240d42c0c0001103000701c5900132041a0740d00e1070020707400080300d0b01003c0007524002c80414042c1c064060600b1240b03005040a02d41340c1c1e106000300c01883c1d04001c0704555040c0910114100041e401d45c520054000c411860b2022641400c12100c08416003001e4020b8002d1070901525071400650074401c030b03601c9242c08540303545441c01229 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 852075917 1250 852074667 852074681
    0x3031611012d14031303080a050606180d171e090a0501030b181003031103090a1509030b0907030c1a0307140c101d010c0504090203041403030a060608130305090f0103 73
    0x5048000014001845d4412030100f04151080e1100022541c070f0032541c0040f242c0848505400034010403981d05a02059004030440c2c03c002011402800c0b5a41c03200904c2c0e000d401041c0b41c0c031650009107042c041d850b11861208010301d0115540c0303070905e80400b049a40c49a40b040c5814903880300000f010541e00c04041d880c10b03109010060050385007000205222842600c000d030045601c82252070038000002c4111084003d002e007a4901091074810b940c88040310404120040201901010001401c03280d00240034401e14001040a6400c605040c002500c1681c080e00100240541c00d03403000340c1e410300341c07a4450b500e410f21800e803510194094038140300f00c01c0c0d507921074084c0d6404000351117483d0b4400107a40030404602051440c40000d05422110049030301008248148000c21001182d070b0011540107120f48041030246440600051640d00203807140c02e10951614002d11519a20040050344124000b08454040d01161030103412481043c40284c014400352112840c02d9001c1d410500c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 852077167 1250 852075917 852075947
    0xa050310050a092a0f15120209030f161e060f090302091e0c03060a1e052116050108060f0409050303190b0604080c010c0302070503031611012d 63
    0x3850060185440b034401c0c030030f070190704e000d4420360480c04660b04075070780901d000352558080d9078005922918025106003008180c0076070300303035001c000004840d14140001300032881070000600f5081115240041d6203000742d00200c2821844840c0742c00d0003541e5403643d008480036801c15582c0e80c07516030011940c40b2f44c1c0385c002a4205020009000088003480010b22092505144075a0140c035aa21412950300c8203075041c5921840701001130041d0b448205903480c0d010a041d07400810345503103001264000010b800d460310940960340c04a02d50450a0040d200443c07000000c9601160800340040c0c2441405022140038002040e070030151a00c85074000c0c600260000f040b6522858881b440303240d9481c048844212030703410141e12000b142002e1003520180ca08140c081c180f03036481c040045582c030714051001c1e8114840c02c0c00000340743d05e0070310040140c032024a00308900c210180c10b101200d13241c46c42c2c581d030401c413000300440350311910301440341c00341c51003214090003e4804000449601251110309 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 852078417 1250 852077167 852077183
    0x60907091d0a0b19061412070507050d0215070c050a0501060b220f090506030a060c030c03050105010c0507031b08060a0e0105090a080d090c030605070906020c0a050310050a09 77
    0x2105901c0e106501280301c1c0c1001d0780140b1242c0c0300780c42401100181814280036462494000f400b2003800313140c802d91000080740079981041c407500105900c0c40819030305240440c0c0c00154400138080c0034800201148003e0004180c580c0d805000850150b5009123844208503451002a0401106200d41c010958011000f880750710745a0400e18126403150746039158091503244114120318003070036180c048441c90003815102c1d5140080000181100030101039142c01803907021f10004020703102d0001c071048207030b03000507420f40b0101e0060121601038005c1e50503c0703601d0304110300080380061100c09a03540042324050318800328125910f0343c00290447d00c00c034010f01c1c04100103440c99601c00781608612100a0009884904200740c1300c0c048020041c159000070440e141d1140f6560f0041c906040c414110240310f541c1d29240c81085403c26030f50710001603219002007001a60400c0b1a00d01d194040b110150080c1c603080c0065620700c2101d01c1648400d0300c41000410100003a8480700307a0903000035013 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 852079667 1250 852078417 852078449
    0x14090a020d140105090702012c01060b04090203010609050a15110c03190501110a021e101406130218010c0f0212161e0303050d06181a0d0201050306090709 68
    0x26560900900074940100f170080006200300e441409491146d40b170001340c10313800008035440360056034030090b043e0320690740310540080d20704401d800410003021600001a2254102000200582080c1e031000b031151805035024814007109003d14070350a400b50030314175641a26000d0681c1070040304494154103000e40403121000c0100b50021600e501d202d1030003003000d440c4610000c45540140000500140c0c01110451180c9400c08001d8020032019070480d103e040c080351307424095925200c2c4081c0c01c49158028800a03080c251600410240030300010740c1040c03c0c604110300018495204d0714104800c0244a0040c40301c50340d26095242e40203080d529544051004440d81c50b100e250348058503100c11400000d0122551102d0081c200301042003035a1a49191000c60307041c2c00c44141c041165a60710800610f03009000d207000c1e04608403c0000c00d4410f60008030301a480e10b03008107103000d0301502040781c00503030b0b000048a07071052017200c84200c82e0700d80c02d804a60528280c1c00c5104041d05540c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 852080917 1250 852079667 852079691
    0xa0302090109021c0218060307090e1303020d0201050c031f0308220e1b0d0209100207061d060909090f010903021b1c060b131103040203150114090a020d 67
    0x1025400c4808044080c081d1810380310030228429444205075070b0406d614202c40500d0003000542d0008a2460182c02e2140c40e04006c01380f11170f0a1302d20f4621103018580500400d5014040203204400301d000800641c0f81901000c0c0c06803200406000030b0070342d4400300d00b55003402d1401c900040e42d00181001c1e10307490710201032101c0030b01e002100d0014540c0c14100080c254410405280706240c00200d002180c108030b070040c44160400090070566030780900c40c038455903c0350031040c940144242d004003040782c581400a008075819042e490600020102c2503115900c1ea0310880d0031070003041d81c0d801d10a6aa6240040c145078084103081c00f00d500f080c4000b014580d0000e84140d016020309010b5a8800c1008100101c20741011200c40c50f050100103000003050b40b5074000b001c110005032083c0039048440c1000c40803901802000d108406010081c813017581002c004040c045845a03503102d400f94180003d0866a00c40202840e00c00c05001340040c1981200780c058806502c01d01c4005c4c0072a5039088 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 852082167 1250 852080917 852080921
    0x513080106030b0906070903110d0501090c1e050109050f01140706090c1d0a050702190f05010b03070b071104060512010903021c2a0209100e09070b090105090a0302090109 75
    0x88425070f8454032803808603240e0807002c54141d000b41d016840c0c1d1000e40c1e15540c1c4403075141160310842644030f50320300803c60110301c0078010984030034490980d00000d68280042074601c032160030142403481414001c140000c1c1d030071032440c0c0143c2d003040781c0102025040c50300403100440c002d10404039031348001c20400c0800000760881000f40380b0401e07002d04030300d46601450303140c19142641c03820308041e03460105401c85c01d030b6070182d070b0407205134819248100c0c001c20899102003002c44046408080e0303600c0e40d80a02c41c0030f2107420703a40d49044000e0f0040600d0042507200d82c0c01114400780c039206ea0300100306a6603640340e1003400140000740c0065400c03040490014001c0202d20403d03405400b0f8180c0c91010100c60001c80344810225441c1c2003087c480da40e680c0b042400103030903449503441074001c40002590303503c542140304010b03510603484940e050501c0c40c01c150b0b1001d003c4500c540d100350024050302100c0c9090303070301c084402e18040d80c6910f0a00000340c0d0104880c0c0c40650404103000c008a100c00543d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 852083417 1250 852082167 852082169
    0xb0406020c0105070209070c14010c0e01031401050906063708070c0b160e12010501030515091522050c0103060501140a08070c1e11031f0506010513080106 68
    0x103800303031402066040d0041d00c1602c1940c200a40c011100e030300140101d0700440115034014000c2007820b80b4001c807103103101d00319000581c000f0041500084565469079060003402500000c0791400d41807945000c010800c600006400c25124000202c1c240d05003504e200e4510420000c5448400f103040c080e20b40c90301c42c801240ea4802e0004100c41e0008074824010700d102585254040202151541c0311410003100c85a6040c60508104c84000030503920790b0f505003403071401c03c800c0c4000100c55140d894214074000c5022041e040b800342030802c100030940e001c03804840d000340149040030346030b0b1501240046100b048800d00c03041410140004c0a01800003400d0015400a8908114031500c0c0c10054400e0b0b4007100d01014018010802d140d2201d100e43c101a400410314202078221440b56501d400407900c3d850610303e52116606400410700581c022151900705007600907045000c0b075114018440d114415500c1000ca4a82010540c0b07640700b5400c4943c0558060081d008140d02c455100b4060441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 852084667 1250 852083417 852083429
    0x51e04030f030c020f0c061606050a1413031706010311030a0c02070602070b09040902030c1509040560120c010c0b10090207050d02060a0204050a180608070b04 70
    0x54542c5100f202c3c0d0000491501d88400c08005004c0c441c100c808100c030320f40c8142c44180010908095000019042c1d000326400b507102450045030581c0c45d00c82c0a440703d40020540c02885648207050008282c000e04c0c1b403001070802140800c05a0f1b110300040c1d010707011a41d9125008400041007019071a8590300c40c00c2c0c3c03406962300355201507641d184105c0c0d86201c140a103660440041042e502d852900341c2c0300030740310741c4003509030750410104c500002c46d01d0061804400081030300040c171240302e1a04d8130034503501410500c0b03042d0450b48001c411000c4804909080c5030074441c001110411601c3d08101d0106804500f183d045100c0c022104d610078034060b40008034050560790920351030307811000c500c6900020341a91140c20505081e01c5039408004060f1802e00f6039021410049411441400200b0031a0700031002080b5800f075081c80245000c0c0000d10b41840a0710500003404640c3e244231449080341ca0310015100c0d0714162800700f00050915a000c00c1841c4121000090010281c10190045505c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 852085917 1250 852084667 852084671
    0x2006041a09180c0d050a0e030a0f11060403091e0317120603060606191202042c0910200d0e1005011d09010e0a060501090b12070504051e04030f03 64
    0x1002900100c0241060fa4020603144051181090032480c95101c568416512800851880b100707003945815a4015224440001c0ca86030f010400c2c079070051150100046040c000f42000d24040e200100020001c1c0512007140200600e40c0c20140250344004000e15007141d0202c0c83c0d98049504003000350b004960300500b0001c0d03400003986034503021400303610404010340440d182100c940d51894071a5000c02000c4103100503105a204100724610150004d0072210f92400c1e9a030500c1212902e01e0075220a4064a6691341800c10a6100300407456040d591004040030441540b005000c0e002c43c5899000c0681005010400e0a80c0381c440350400750300c05e03c0700c0003610f004031080290082510320900501150100c841c07001b0034407040540e041580010100000901e50413441c03906c81c14101000300664100303403100c00501034400b0b58420a010741c0c5c0100c80c043c86114560744100d85520b01b1f84103079031003180e03204001140501440030031030701a003030002e4082880c40c0c03620b800f0700849800b00784040002c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 852087167 1250 852085917 852085939
    0x902180306060d0219080708031806030402130c121a0a170a030c0201050f0d0c0e0102070f0b180306070c17030103030c140304082b03092006041a09 65
    0x400c01280041c061400540f034112060300395000d201c104180d1500c0411902d070b20b03400010b4007840601190003e005028041c55030b070203201c0c480c203c0c81400c0e580d100b80b0504040045c0001030350b0300f00000e007648410440119181c0c2c0103040c2079400e611158000e029090810210140c8210808105458504100e8100641d0341d00c450201600e14501c0e801b500d041d0f40b05e2016000030038090504030400610501d400d5203004400550f8040f160841c0d2041e414058907418072180b12600070226009112080c030052140b1460041500c580000301d2080f203025240c00188070080d81072030058030a1016000c0d044562508110300020710100c0780740402d680386801c095040b411140450b0850b412a5003507600c85118040070b4517a100043c4109140c52403500c020080042c0d01ca1081c010000407a28010411b00c1e9002d146c020110100415000e00c001c140c54091490001110840b480c001c580940c0001c0130903c0720303074011130018070079508940e41e65080c9000c01c01a001c244001031280351400d43c0d60014035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 852088417 1250 852087167 852087169
    0x50a05060c12040609110d030201020a030e06060d031809020703110706180b1606150e010f061704110402310303090b07030e09160807020610170f07090218 68
    0x1901800380680c0500710b0160208020400640007001c486016a0003008003c5400c1c0004104004020b01140580d4011a1140100f41c0511800c07618451050203400303d803070403c0000300f0315185d01100806108000545031001002c0c05030320030141c00f180702c04540d66059820068201c400c910b112000612403803034041a0781d0f104090840d00b002c00c40307071086500c5090100401040d04070f00c18455200840c0c81c0704402003220350040d1501105c503100b1003140d0500380900d5107001f04050b00100d00ca48072180d402c01295030b110600c090040c200009107a11134403140b07460203d2103220f4100c03550050001c5454105004540c103480070950808400011106000400030290384a0344005008540c00381000c122480407403008064441c420705e0302c01030043d2200e000503c519000d0ba40c0f51109108064a035162a400c0300c80030b03801490500040a45140c00f414010800c07807107004560000c00d4000301001c0e003d03000c000ba0810044100169a00035848131240310083d0004c075a03900301c0031203da00c030100d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 852089667 1250 852088417 852088441
    0x30b0108070b0f0f090a0f1401110a1707050607020c0a08010c0f03020a05040f09060e06061e0d02120f04020f3c09090604050c15161104020403050a0506 67
    0xc031107070242c1c26070500e1040403a1072141c1d00480c803102803c45080290381c01d103550703010510000c0c0907000180b120040c00d1880442c18074081e40c0110303050100908880b0b00b5200c0000380400d846a2107407100b1980c0c800904564401d0084240c002c08510030380c800e000e8501e40100304580c00c41801e84614a50301e0780c600c20603082c0c8007095900404140489820402203110b41c004028200d041e08003a0b2405a070707058103840c1c00140c0d1b0f1103549107030b40d150414020340c03002c00030003034000f003084880e14101642801c000c1c808215400203960030b03044c00260350248107199016903070529120300441ea118603020200c0b40f000c42e400c070381c224070492051640f40c00340c0c505400c00780010b0702007200300700c0d40c002c00b8452649904402e05041307409446510701c11070a9540c5e0040f091041075600e020b4880c90509141c0f00346400070b03140300346124204103515103034944080c00c1501d5400d0f40c1d003c00300303102d06043d0a05040010600f101140c00500016000c4140400082c084205601c80c0b01103074025641d01c80301072a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 852090917 1250 852089667 852089669
    0x612030201050919082217060405070f081005070e0612041209060f03090c080d0f1101050402090703181403070212010608030703050c070f0f030b070305074104030b010807 75
    0x40407403006d1180c13005600e55403001890070120440d54113151519486a11800303000591700706c24580c084810081040310038003503500100300c01c658942040e402c04480c1604c2e12406550707080c2c2d1940d6400040d25251081020030215800500500c1c1d0381c0c80e15103201d03803402e4021a0300381c6518008074a08080d2921412040003203951316030318400ea1600b0010210094410404203403a5100c04601c0804c02d644140300c030054000d8039403548a2806401c407009014a03034802c20306151a4034010401c0b001d41c49202496501c4951403800150070481c20401005d9100010400750442c40940041803202d103000009002c0b0600840380340344507070340348a0880d0980da450700801045801c24000712000070700038406041908250380c259006240c640c0d1030280c25602950000e001546000810000c0c070454070b6901d6002152031070103110500e88003c1c081c2c00c1c01c1940c2c511901910490300c10075000110500003000c0c40e1200079940020001c016210303982508180819910b81c000c450000a4218000031000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 852092167 1250 852090917 852090923
    0xc0f0303021b1e030f010c050903060a0207030e012015070e120a0f080f0d020301050a0501030b0d030503180307060203040209010e0106090308031e040c090b0f090610030612030201050919 82
    0x40041c545401c00b801800940d004442d40510030340002c0c80c6000007e019800a401260b03403440d0f01c50040008151034050040c141e05086e038410481c0c000400c1d402100c03407078000c800f803c0a440003660072031150003101071400c99000502804442c070301c0a40300c916290340100c03080d66903404d4511414080160f00700e8100716005050f44404121000900b90710712200181d40509425418220160b0b00709040d903002d01e44214819600100501480ca003030001e04010388028a0108202c1d41240007040c5031805028000e81484004800220020310340d80e4068110601c000541c1c0c0c0314101854100080d4000769000c81c07040f22030b040086080d00c09009682d0407607034155600594030b8a162a010a990300182c001c681e4a00e502e40741d11181004649a24040e034840c03038030b081e48140b038051034208580d003400d802e038820744041600024917a94403403220741105c000c84095040050108040d0014070700707988a101c10b01c903420342c0d4005040d01944014424283d0078255284000c880030021010350391a2801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 852093417 1250 852092167 852092179
    0xc0d1e140d050c0c06070f080106080c0a030f06170102040905060411120603031324020102030709030201050906040306050f0405011b120b042711090402030a15090c0f0303021b 77
    0x49100e29032140c02c050703004001c0c2c80e4080c2c0742800f050040b0341041812030715000407035181e280c1c5040182e80000070500500032490059402d0814101484032841000408010941c544040940200c2c0e6540140002c01d14910307040ca010706005000e502035080303440381018042c6031030002601400d1a000d081a8000c04041203441c040d0704480940800d040541910b42503c4207102d40641071042c200304d0800b82c415855500d03036546444000d04680c0d84d140b04041c0c11640180b043c444060781203020b840641e582402c00b252103000040c04141d00d40070310383c0050505400c09044c400348080c41c04c0c80f60301a034000c100921110300606048140a541c0095807400240242c2080d440706c1c1c0a41c1c01794010f80d900038808a070401d0040e031030318071031152501485407801d0001e600c1400c0080d0000c54505c4203900741c42c2c040f86494a03400003034035481c1c0303013030003804513660716480b1881048564011046030350700c41e9441042c240c0b50b804c103800505060004038098802c1d001100903c400c0700c804a446000011b003c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 852094667 1250 852093417 852093427
    0x100902061207090b031e160e010c020d060c0e011412011a0705101b0806090a091b0807030209090c0904060b01120f020703030c11030703050f0c0d1e14 66
    0x4815608800401a000700455414041850b90150004600855210310309003120f04202510528280c00500501d502c4039007914119031f9260401c07c50b511089090030090088000da0011406400301030b40d00400f402c2c40d00c090b04000070b0704200d2480d4550320a990344c00c4d12054661410742030b4461000c42d0408c000700440100a0554014011000c02c60416006810315009588051500c004007510007800340d11241c8054281c6000b445108030030459107000100c07801c103140070908115029003032240035a08d07500343d081070015840e060144143d026000141196440600d507480754018042240304184880100380d154400247c4843e0348040100486000d4485603500c200a00701902d4540c1486580d180043d8041000d11810080a614680150743c8590034a8014107c4040310703c00002d11420481302601c101e800000c2e550b06951505000382e5901174410400d545000300c09042c100d92041600c507924031684000078038280440aa003181d4520071009081e59544411009107440507020703c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 852095917 1250 852094667 852094687
    0x1050609060f03040c0501030e0a0b0c1b0a0c0810020a080601110c0409030914040c0507030305060316080d110c030a08090a0909051f1505010c0c08060a0e10090206 72
    0x4002900c0000e00140ca09103651011600c25041124265400500c040082040c0e5815014a403280c50500b00a0400401070741c0c0c95241820000c0c008011518002c108c0103040c0002427030203c6408028011203501f141a03280880c42010617020347d2000340102d10b0001052110342c000e491000d48181c490000d2603882d08011141c1100c0c0755080d19842c030510f828160107403500d00c1607030700190085c1e0b980031030307682080c8140c5214101001c00ea0b01075842e0003140403100d1b901ca016036402c0c940c10b02d0082465164a000285407051650380c040c0c3c075900110b00050107140009092040d82419290f00c401882ca070b18100740c686565000704c680503042440c0c03030030010381d001005000401004266459040d254400d0608032003062204482c00c1c0e10045503c110b40c400380b25000c100c0c41441000f40583c44528050f50003005e024403410b030510035081e820104128124440401034040c0a0441303046203003004503803018200c1406580914040c0a11521520656000d00f90751250060030036450407000390 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 852097167 1250 852095917 852095929
    0xb0915031b040e043c05120d06060e090907053303061e21011401032a18020309010207150c1403040206071707240f021603030506010e031e0d090305060105 68
    0x200b00c403c0c0c011f21b001c2c190016a02405000d4542404000060441c01c002c4003811f4602c8000b18603110b070a8502c20002111000924001074940c02e03218000891146c1e03048031255805010288490001e02990014000c41440514800c020458148142070800303028402c0c061041015a038111041c610303405034010703130f42e000415824080c2c000000c0100b482c3d49a00140a0b080c0c004441404a0071029505514242c3d80019040410034030154035078030703140c0303401c490032010071030358103e43d030048005211401d0a506407140541c22041c03841442e110700e00341c10002c3c4000b04c0c06a0110700c0b4001280c815082c04000d0b240300701d038003078900391902445441e00e0200b510840740c0402802d50811483d0001b440d000c2d0008215106241c07d094109401c0900703109440c049080c4010407481805a62901062103100480d6240c0500b00058281c440303070012160005411440350f003500c519000d800008103d0380322154044454001c0d50021350401d101226002100e2102078601d80c0f2030001801149849d07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 852098417 1250 852097167 852097283
    0xf06180a1104030218090120030402040c030e030d060806010b091e030a0c03140c0105030402130f020d020c0c1507030f08070903020d05160b0915031b040e04 69
    0x803500c00e051a83c0d070760000301d5035480201001d40020780f8000740010f6000034003d400480183c0f074920b1394034410451040307a4034040200080e10484d21003002d01d18a0380640c0c0008020303842e00080d2607070380710001007090141019200e440f0700c0384201c030000a00b49007500c00f40c404043d4020801c0740341c0031802d40740110490400d6440d947c5400742d444104001008841410000c40c4192820914258000362480c100340640d01307402d060201c02c100b000016510401690142c031541080000e24102c90f840e001c00a01400900d8110720b4030002d80ea403030350900020300c80403402c0708403441071000e407848560f03020703a0107203444c02004a4400480030b900c1c14022a4003c1d8000040d26040703004550f40d03000544c001e4040c1400f0749050300031080b0600c180c41c80c1800d182c041c1200f00745880c54051482c010030014a1080721a20401d413001c00490340107102c0d22820b00e000310040d600c1c01e46a030f403540400550350505441c1142c444040d5203514038104608607241102142141d80c940880c52100b07825000c102d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 852099667 1250 852098417 852098441
    0x50f0307080711192006041d0f070c1202011103010f05090a0c14031504090f051905060a1a030f01290d030c02280501090618090c05040812030f06180a 66
    0xa40004c0307545c1e13900e0f840041c00c01408980c40c03c041100d807000c1d5144c1c0c41c420107040354080900303d00c104200c00d50021441c42165a001e0b00740c0c0d0400400c00c000b24018615520302180d03480c1c000000090018041000e0300079280d08803083c0b00107031180300519084401c2141c400c0c007c90070b94405040c00ca000318000c1e550201c207005201e00ea014810300002c0440d661a5002c40e00c4000201c7d0031800c5c0081089041245036030510178111203000e58640a41d11000181a9024540c9030500742c5103080700c54054035681d08001d0304498402a07074054507030103414008800080c11a01d2a460200003410948018010f14094215001030324152400c84640a80300d43c16600101b071030b0300703400705921082142146110050400103e080c01e1a000510181c0c0e075500c20006c202451050301000d1010035442e40488410240c005107000c1d0f960301c20b484034090f5a000c0201030041c0c03480000702043d03030740c010741c4161854200c0c2d83c541d0355041e00b04000344400302a04201c1c00884000248003c400340d104030034200e5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 852100917 1250 852099667 852099713
    0x140c120c030c01060b07120509031b010207030c150e0a060906030902040b120f011a03060f0601020c09010b0921031c18140607030506030607080403050f030708071119 73
    0xa07003502c400c2c251070182c2e00072400210002150700c10f11260150b643c60103422440c00d80c0c03404070b107540000d035600584c481e400d841800059403e0f640780e0007048004c00550f07000c603602c441181e485104ca4100e4540342e403030101184aa164a0105241c5844803d0030303500745449540645081c04002c400408480d84102c1e0481d65030340e04038030203644101c2c10003e0300c0f08010041c4035030321001d4031702400e4030040000c5c00c82032180100041186d580114450f688551702000350080c035910742004030300e17100340d1800340c07a00800c50000100e04614080000c1c0b0202d00291914595400017130003189070048403000c0200b054005200700036280c90422041440c0c26440314000c192040000c1980e0740303034164030004444a9801c890751044039602400402d50121481c1010446490000701103134451030028468010001008000f608150282041c2c0780460101c06500e6140e00d0103503400340243c10290384880100e0001d00700c00300081c500103551a00403c00c00c003400c420925076a100d07402603001c0e6644080100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 852102167 1250 852100917 852100927
    0x20907050f0d111309111204171606060b040b0a2f010b011d0306040201080403030e0a061a090108100902012703031706010e010503070201140115140c120c03 69
    0x3180c040c05010512000d0003e41c1d5218040005500b4506580b0813400a400c0070b8030414486a01d000b40c0c1c8100050100c247ca060765246410040f2000304120306807000000300782e00000c0d15040514159130382c03082a00308010350300c0d420021100c2c01640b0850051420403c00f95200354400d0032103141c80c0e0b00d500300249130700848010b6a030580240004290682c2c2d5668a813482a43e405682034000703202501003201c0001c101c602007502c0c5e0718000c10180c103006c2c5c01c0010404051081e1712820b003003922802500d004e50f50926014001d0100078032244404a109100c40400e4907042c1000c07812075a442005010320413000c44d5280180082c2c0e41d007a8184010180086a1103407415030f10180c40205003a09100d00341036250242480041c1c50310241c2d281130450400078141d8120840082c11842401d110713031203540e9000d0413805400800300742c10404e1b40c50800052020200c0c0340c4c0d4424100e0544440d0b0300d100300003410070300c1030280300035040c860b034098a18480c070419030100505241c00c0c2e10301030300d2600c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 852103417 1250 852102167 852102187
    0x170f030c06070f021c030e010b04050105060703030507051308010f05010e100302011d030708030904240e0415090b090d020a0c05100c140708011d0618031603050c1603020907050f 78
    0x1c01c050201a000c45d440b0907c400c0000c000303100d400d0f2401c3d0300308d808000a50501001c1012409100710007424542e5580101d02c115010750107540611581e0700b245131005403102ca180d40a09160311307031403082508150012869401803c40da81c8580341c0e540a419100d8034540044810210b044403c12065001c0d04c0140081d403014000c0c8000f40200708005c0d40e039806100c040c0005c03100d048009801003024000402541c04800f21800700701c0e8881141d944030303038481c0d00348082011a40100d810015280c4040c00d0b04106071546c085124400100c2074803000300c0c11542c20b80c0c403803890030802081c06c2441300d820701c01464000880c48101840385065880042e20703945d03068119412503041003140d40841d43c1000035031024050510f1b5000d125901c1d0984059550388a60358100180002103003802c00460510143c10800543d0b403e5061021404841081e504000c2c4c1075030301900e6911701c10b001d41c05504024420358000a0300702d95018180f00c89595172800b040b1100c4c0c200000003015030004008083c41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 852104667 1250 852103417 852103453
    0x30709230a11162d0602090303040b0c1b09190f09050f0f0f01060e0f04020d0501020a09031a060603062707050a0f0819020a020307050304170f030c06070f02 69
    0x3c10300054401051101d443c0c148129294690503107900c1c030816802c82e265026440d40001c5080c50340c002c1000d41c4030307540107000078218003494200c509402004616108040d0000403540701c45044804e04d82c6c1701d41c420b40103004002d002180d2050102c5546884602129003e130301101c02c0142500780002c060b50700b90f0b00c0c0750030b00640200c0040c0030f1380702c51451999600306007e0803200c410640002c000561401d402c020a900c8005c2c4103460b060007810014056454114071422100d40c01002103540d10500080035004910500042d0f4104003052050200c10322000d043c6801204e0080c449425580d43e14208226841074465130440083d00d00c0c0301d2183d0200c03a0041ca400703070089860780c507281c411941005100f41d061080346000c000d400d105001010318001d000b440444072042c00036a139112000000d910758440c69000071311502c0001400240034105414110540d110042a501880b4203160382d01c0c2e49004580010307006400c1180071500701c1d4044c6409422000302801030b200091041c82001c05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 852105917 1250 852104667 852104677
    0xd060905070806090a0f030e030307060c02010213120b01090c180305062202090105060c01090c09050601031b05030619170d02060a15050607060e0a11030709230a11 72
    0x40380d600c24401401080c805100c0680d00412034002044850340d1915082001d61070b04401605001200d000b288040c0c40c01e1044504180c1c101d5024007071200040b00081c004e41c0240720405905001420108040300700d1030720044800c1d00b011100b456a401c00903070704001c1100e01170040501c25001d0b1002c1200a04140d044000c0d40240050507140c2b81800d481621070742402643c244403030b02034801e4001aa00c516515041da02c1c161455900c0b0300002c9141030041100d1100503000400007000041c03100041c0c4c20161241000703980a10018001e03410740044400ca000040f40850301c28400202541031140b101c2100c0800c07008240c1c1e50340d503205451348040c00000102c542e1504442c0880f0480c603010400f007600441821000c00c02c1040f0011448525000d41c0103c03807043c0c90002d2041c050110b160003001c1c1c51482c0e0070580340701403801e01e03040c60990342c0103160314043c0c003500d400060307402c60910401d05c40a072220100500d00b9803100243c100301c1002442c17214116034035100d510460320b1480c0909 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 852107167 1250 852105917 852105923
    0x109030f030309051002030f1902160609150e0d0309020a0506030103060b2b03030b12190611091003023f01090903051921060e09120a05090d0609 64
    0x40c50411504205040c54100c07960176a0550041080c0154440c15403074180d4043c2c2d400000740048070b290070311a800381c0702e80b540c100d100040d04c00c450300c05c0c0302d4581d1280c881c151241840c00f48104480315000c1c00d07603451000c442040d03000b0a90502c0302b14001c8e0000c5e02000d20003044100020f8807003000481a40081c2c000b541c0c03299a415503078625050403c0400d42c90016200e83c02c10308400400c503200e4218010702c004013010740340c200c4200785858444051512283c11020b403805152122000014000c1200c0b0603500a03080c00189004507a480045440b40309020b407030148000d003c070100760040e41c0080c5840740b6046009a0310000e9940c2c5210f11003414060841140022005000544441d20180c0040b001103251084800000e030300f040440f00c4148000b10010700440c011001910143d40454400e00401481d01038514070358a6a40008207540c0170207001c058a03200d80c0c841650314030855240c2005240101305c0c20a085001d20050a0785035001400340d084450560ba5260035150404411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 852108417 1250 852107167 852107171
    0x21e031204140a050f0d080405100f024c1a190509130807060c0f0f11151b0d06050a050607170f0c1902010906050c1b0109030f0303 58
    0xc1c084910b00540d0040101c0040f509403108030f040c000015550035641000a22480d99240c000c0200b004880945005110050040044032400c10000e003101c1021080200107000d000d600200203021304c10700ca204d98410804e039407040d03000c586641941c019806800054000702c54081c0701c0c110301c28056003021075082e07000134186000100a000305010300780c8281b01d89084601e014030481c5c840c1123101c0da009080114412101c0c0c43d6007000e4200e8468810042c240d5420405801c0c0340703603044500c0c1034030b1015981d2010b940ca0b0320000c00f102d40706140385003034100e40c00520000050460106100b604070f0303074083c00380d52007060f1100b00c1c0082c0d80c0091601042c25441d58800c00003450045184001400b094034403e18200c1503035142c2e4265102e9050840c041c42c40458160304108882041d03c0c0c4141c082c0e0202d407105080702c0000c12020400c40e400b280015180c110118101c5c1c8a031041c0d4507024503100c001c103c0200710881d8841c00d402010b034814100300581200002051810090200c03031406130b100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 852109667 1250 852108417 852108419
    0xc0c190e06011b062a0806190f090204030b01050f03061803040801060608040b0921071109011202100908030f07061103100f06050a1e090504020c010f0f1503021e031204 74
    0x4a6511145d1010070b11044441d0601c01a815541020000c2e07880380040300c11b5586140c14160140d440e5845070010520150300950204001415900404c1035a0154117801c4450b82c3e201c04101c1d10306803411229806803c0b1002162125100410040508410409032404c01e43c0b100042402c5408030b40c422000030f80681c0c184000c0c0125071107241d8021210b1f0000d0651150b4840161200000706548107810003030008002062041c03401d8802d00c080b20052404010303594580403060000102c0780c040c0e100d9050400666105401100b6032821205210095410080100784220454101c654140d8000e912040904044040d03a0300a510558460603c0d10760941454501603850300c26420000600c2001c01c2040010b940204c0806d192240390800d911002213494070444807000c02e507001680103400820003100e0890190082905d550079083c04201d1509441030389030996020480003040200320140c01d1015041c10f08400c0c4403101d0800600e07400070301e04030100f1324100c0c0b0b0b006e0032082c0000101e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 852110917 1250 852109667 852109691
    0x50d1110050d1a010f080c0c06100501020d03140a0b0a050904080a0f02010614040c02011b02100c09030f0212120f0301050a08060601090e060a0504110c0c190e06011b06 74
    0x858140c121082034541c4001c3c0c410000081c0ca131089045d82c0c003003070081c0d8100040710003c90000b02d6000010103030583c1c005003000c074950700d210706290058502502440c10310700d04451107031140c00600300381000701d01d08545800301020300801d040030341c40b030304041056804603690b01c1f00042640118401e414071551014001c00c010580e0311003403c000c0869040c120100305565012603801d14510045400140300b01110806034018000c1c1032580301c10696062541302c41940128a01040801c003000521168038042d0084448901d2400001c001c14449418000541002e40000d16240b900b4022501d40b100c2d403624400060f046002d03411030142000005000038180341c4074820042159500800b1141002000a0180b00320346c01164440c0340c0240009145aa4501c001001040041c0042090710b9295001030420744c045000001035104e07000e158115400c010750400c000c1030024140140946c00c040c81032201c480f001d49018100b01c10420800c2200d003c0842e003c007100e2181d80c0019030030310000c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 852112167 1250 852110917 852110921
    0x2070803180d0c110f03012f25050f06010314010c0c020310052229010510030b040605180702060a020a0516050703051501060201050105030c0a050d1110050d 69
    0x1030824542d8101140c5800160307085045595020b40c00000b9800c01c628180c0840c0c40b40041c48003440e403640c04c0150455807640117000340000c000301c444241001c4004100c40c10a207204da00c400c400301c0043c54400084e4403000200b919141480340c01074a00408620b0300c10b514140082e0025a49800e03140234012601e0024481c100e4004058200700c42942303095000640c890103800701030312915845000258000c1070403608800f81e0907039202d68502c1100305060650405101c0b441261015020f8152014240b80008029040b903030010720040341a0850002140608071611072a41c0080d00c0e01e0b00032440741d81c3c0003c8544401064880c0104070b142c1910b0081c0b40400240c00e401c2c0716803040003481c0c1199404012241c80075102d0300c0325800010a481e201e0b00e8040c4550000d8018000e000804015210503000f140c1240d0741740e8001d004507600c1e11708140c1c44240004900e80c3c0924a44401c0215060008080340c1071402060407044000e60000850f05c020070300c052010014a0001d442e4800c28454 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 852113417 1250 852112167 852112201
    0x19110c0108040804030f1b15080a0b10050c030f0f07022d0f0a0305011103090d020c030a03300f15150503090f01060608160206070e09090703050102070803 68
    0xd2030691640d0034143c0310080107118901011301a070030f4111840702030241e4081941c00207081c0c020008652565070015004105180b810240018010b90115482d00b5107401840b41c0607000a2030002160072845043cad4aa5200c0011318455000c02e101040a2060220103040d145c1103402001c0e654119520420450102c9040e4a100301001855102c2500d00248011a00b1003000e889024404600d0700000d040c0806a070705c001c000d50f00f05000d8040c80035004000d5405190390104440341e08280d0841603841b401c6110307101e505030307201c2492400424403900446141c4003168112440708500d44070080c043e023500882c0c240e00a5215000520810840e105a1640b41c202901082103d4184110700340031140141510342005000300108015040c140303d4100c010208070020842c4580d00c0101910081040ba880071850404d020030b01d103040c0c004601a44521540c2c0d07901c07107101d51003070204102c814018102d4042441800c41c00310000c1d9091005109142c02103000503100c0c5003083c4880c0402c102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 852114667 1250 852113417 852113419
    0x2812120e270403090b16140a08161403040e070c02010c02031027030914040b091608010909080d0519020c01020d05070521040609020607060c0e030712140319110c 71
    0x2003008402d006c2d2240400448800e41c0c4281c4540541316806000c40c98103108000240150000144080c031259410305251505440f030341d002c0301e05180c4942c90316280d0196102e051180712440c000100018803641c043c1c01624414108400c001501c1e801081c80c0c1100c1007207040c24a56030342403210b034084280d140e88031604003030320f0300030296004c41d03900a02d41800c40c030490780101d650181c0203249695075000503030b600102610807e0300740b82c83d00d144508171542070340724408964400c0c000300d080d0200780141061203821000c501d00e81074090790711000800004281c100e510002c500c0881d40040540002d1008200d800005a159181d20301d00f60700f03c0b080600b4140500500704414040400308003900244a0300444d40b0003899910781c00c010002e01102d680096000e54002849401c1015560084481380031a5656081d418590760501d90340e407485005507071440c0001702d540360004243c5d8120040c03607603000054030f0034031000c08230070241c480031184030038013180c0c1c7d0040354a102e0304100605098198 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 852115917 1250 852114667 852114689
    0x5180a061d073e07080f1501060306030c0308070c0b0a02010605040b0d0203070e0a020705030f0319060e0a09050a0606080601061710061d2812120e27040309 69
    0x40d900e6802d240e024030b00c040f0002040440e140c040803095052100070000e2410000769080601000110b940320a4130008988249902d040080f40107132007407103080291395003d03000320324035400d41d05c40700c01c0c0c0e0b003040c2800c0b9580c256403000410154a40740103401449002d4002086c17450416040005a981e40b0000c42c1c02010005094801f60b540010044121492108092901e442d4a89160301038451800080c01c03c1c03000003008a41541d40b80e00441c440e280358400a41220181132140c01584c01500c1340a18411900c2c0201e10000e40640c807482542c0c0c420811601d0218080d82c4220030b0303561550112100f501b00c03c004116045c4c110800d025602030101c1140d8103454a0742c80c58040e00a1400703007500700552110040c6c024a24400902c008020060110f400c0d018413001d804250224020b403107006290380d00001402d8019200f0003c501a0300042c00c8070488540c020881d60410a06d00e66075000281c002c400342d90074a41c00000c0415182d107030900036945410708014050600c55800500d17861 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 852117167 1250 852115917 852115967
    0x100f0e0f12030a02090a1208030703050f041a0705130e150d0507030605190203040b0106020c0d150506041b0207030302160806040b0606190201150501030605180a061d07 74
    0x2001044035403044464000603242c0c810b03100402c6203c00e56400034680c1c600c01d1f02d030000c1481003400155204000c02c0d0360510155035076000c1d52007992015180204289130100319009000e40d200e803600d5201c01306140007410119000d40c9070400b41032a6000140032501c18007404035207241070314101c0050000761440d519592682e510240d64901ca480b0280000b0b548034081a4111241002803481d5411a07000799101e081600341030082d58004c2c410000984103580084609003080d0440e2961070f80c0005070ac0140c00503a01800000e070800410240e4069070380c40d814402400d072544000d0040885038002e103032071400c52402a19041a03005000c0324145004020810720100061031036020ba4446e200194507120308021901c64003841d024400002d410b075800380001c960540c4400b038103118505002920b40e9842006400f03c0e0894024136070403105d0084030396032101d030f00c0b081c09800808201000039295a21030b0b110036016403c00100311b85448400c05e20607900d03400300f28404407925030140d50002c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 852118417 1250 852117167 852117193
    0x316110609060d05060d140f0f06130b100906060207140a0f03300f0207150f0f050c030403240e07090906060e0708040203120c060612100f0e0f 63
    0x1500840c01c01d6040d0316140c2000604944800030b07402c04441d488200c280084901f0001c503a04e580c00350003038130b00ca44900000c800c400100004c40c00e0244080a4055042a0760341d159601725500c02002c6400020000c0b0300050f8400b950b1041000822a5a0242c5146401d040106442c41040351000c0e00c01d503000a02072241007101405101125840581c0c1014942d0150010400d0f0306002c0740e100f5814903840704000e505030846421003110b030303480d0f0030380b003007591644070788500031006a1020001070b6158202d10340442c010450400e5014007801d0150030000b950f41d11074555842a001181c0d0b1400d41d2041041199540480f1550050800e40510810400001311661806a4170940308031980f240d0300c00090086560220000e0300b1407041c811540e05e040d200103040c444096800301d010348501e03810f4440301c841c40010b0307400d14101040a801c15032901c0e03080101042800c800d00010740501160126003282e2446205282d030303030061012070303020203403116117050208020000c106904041e40b80240d0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 852119667 1250 852118417 852118429
    0x506040506030601030f0608010605030d17151801062a02131a03030301030b0106110a050c01140c01020c100c140708030a0207151b0309020f1e030316110609 69
    0x54500a607512070b01e035034480e001280540b502e40010701902c1e02e000004240c1c4401900814143c3d00140c1c100d4030046170b0b02000f1a50060411046130441c0e00844c00315030740c00c25000e02507a1403000140f00c0380d003918250030301d903131800300a03400000480c1004403280890b036100c4d21614480a0b844981290504168002c600c0b4041098035080600d40c1ea10004d541000c90114070031485040074044907181c0d80c580c0b8111416440c00c1c01903c0c0802c101c9a0014078142c0d0001d80191100d030b000010b04092030302c01005640c005001c0e42c0408a603542844036a408200920140c000b03040c21200070010003608008010444022401c03010801c6400c401107075002c05040c1c00c5401269001d030700303640e0b240c2d25103251400070700032000014801e485001030000c485049400c05007007020380329085181403a02010640468a40440007034000c0c800101c580359a1800c00c01d80e139143e42102d0780309400c40d9071480000e419a070041c0500341080e41441034403000e000e0050304030a14583c0c02e072035561504038040300040e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 852120917 1250 852119667 852119669
    0x50306100e041401020c0d030e0106050409080a0305151003090b0f07052a16030b0c090108151f020a060f020406020a1425053a020109030f05030415030204050604 71
    0x12140c1c41100400a02d09504513041c8140c06000d403031031400c20547c01000b501801d803808406608000001c43c003450140305000b611a41b100400b89020410302007540644002411505104401c11005c2c40c0c9465400206440200660300000c02000390302d8841070084016007890131245264082140f0103030010b040322040b1040540c0f00789108032000e407804108100c607071150f6541c00340008007144605100700361020750f0300c207004081c030325a10403801070410300400340b10038001003c040c0429092102c40e0000180c011020341b00d04e021981c006070700040d14425420550041c0d20415420003480340c9803241403600c03000d00300150700d0a880c00c0002581c41300c610300d0181050206210a80d881c15080050702d501e42050300860703150212540c246011140f080c0b00b880d01480261003424414140107000b2050020b642c145990581c84041701f4040d0007903680c42c204c0c107103c01500c0101c0411507100f001c551151003440215541c6082403130308000c5081101000003031600512003400166030f44d1003514 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 852122167 1250 852120917 852120923
    0x2e1407050409110408011104150c0b1306090f050c03160e0612030c07080106090e0d090314070f03063912110d060501080106020d051605010615050301050306100e04 72
    0x20802c600300090400f074a1007968080b095540c0b90000c1c840d201c425a4000e4801c459080c5210311030a8800002528010400740c0010035120603100024500c0310103211034030b10280a10000074000ca00d0383e03240c119000280f0001c1c0c4141c0c1c008104000c9a1908002c15034004103046009034115143c101d8055182e1009818503101c1c5c505090041d0751300d5010400d440355802c6607011212001da0b40c000c2c0170700a102c3c5000b41030303405051402c00d01c40114006083c11a200c0159510405285107441d290035a10158458070510701404c00d00003903580a2900c40000745004131070000715040100303a4003542160b4050f0400c1c807861461204000c108030f102d0103110050850900c07140c40a04030351401c0c01000702c40d40c8500414030100340b00410b00c1d265440f01082d1242a03c4c0d20000303980301d00301079075550310345d15902000a008100c6800da0504580800c4c0c8120700c100300118510762138003411f10400e040170045400280c80480100040d2400304401038000141c58190140729081c400050343c4210010300107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 852123417 1250 852122167 852122171
    0x2070e060a030c1a0f03100f0905240105040b070b010f0807060804141915060e090304050402090607020406030f0c0b070b070503090c150406021b03030a0804052e1407050409 76
    0x30484c0384c5043d400700c6100c14030110905680e490044440c1e6080100c500401d404a526a034011511468510495001e04450250310030711040d566416454080c1e1903a040c2d042107000e00001541e0f03007a400c05454841e03c030781a410035540c181001080c481c492a400076600d0b511218003004411780090195400a8005000039500c104c445941f81c034000c2e002c01d020304002980050b800034000b4041c0784078045500b0100c01d100140d41c41a0690b600c2c1d0041c0c5014246800801c4104190702d810390007002c41001c040c21480c00c10f5038a400103012139403a54010b03900d10a1080125040151861110000d0001142c0ca14204903550319904014440100943c0c00d110f00000031806800c0104080b480710300d802402d07010005413503050b2205c5900188103500162140c080100c0034082c0030101400c5003000a00150b0401e008020f080382c0358000500700340d4035030050b5000c00100228405910000162801c0b04241502000311910110b80490b01c4950f520078244052051199001e402c81e02150604140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 852124667 1250 852123417 852123449
    0x507050a061d03211308100603021807091715010e01061e0c03050319060321020f120721020d080a1406040f1805060a060f08070b1c020a02070e060a030c 67
    0x7045003d8501c5030429041c522500310521b480c001f16800800c1624030a40c0c40e45406c6400001481d4082d1060711510040b0b205420203002034600b0703902003542c5528503012921602c03207100031040250703000e800c5100d4140710b0034010f01404d500000d00c244454524000e4848584010200815015200c0b43c000c0030040000081610184103029a000443c12550304010495807441c01e0b02691807030860034068041c0105861050600124190400300750040107884048500c2080c403101d07a0050381c048400c50300e484110740c032804602103200900790940d0010700f407212020b50040e0031440300403e801c002c1414140210300640d120f02d01503070002d0081e1000710303503110340a039448040d0142c00004c1401711750340e0640788244040025203500541c4150301c00c00059071106541c840000c50780c0aa80350503802484100a00b08007900207001d02c1862541400358084140c03c410180e901080c14007006074030580051082c444924001d54101808030f642d00c081c6d500c0e540d41c0c52024022442410512002018 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 852125917 1250 852124667 852124687
    0x80a05060a21060b040c020712020612010e01030c150c032d050306040b120307080307090e09100c1b060b04090b010e040c0605071e0507050a061d0321 66
    0x1101d040941006102e01d07070156414181107007600444441542d04a04145079480203050038032071908000310b6503000d451818140341000d0109040705808981142d4104400c404102141401e58040c3c000380010200300d5241d801c1c20b4070040d83e2758001103c4510700403964041c244c0c1000e100030304240d042c2440080e03002e0107414a084881d50800c5404050f01e0a0b11140000313900500a601c81d641c100c030104404900e03a000e100d901c0400f005161345551080111101050300307100030710b42c42070a524040e0550380d01d0b4528009160000d48010700958003102ca810500000c1d4001c0703495003020740c81c0c44090007100346404d002060222308064002030352500142110340b100c3d0404004250403500d50030895948400496040008440648100c0040000483c01510500440d000c45401030310321091085051a41c9001809070101101c4503c1440000030f202e881d8908039070024046030721840c4000d0050008840300c4800316038a140b20b0340158400040420820b40791000e41118444025101d000343e0b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 852127167 1250 852125917 852125929
    0x305160c1101022802190305030304080c07050a060c06180c06050f0c070b19020307030806061804050a0c0219080f0327010b010311031b0a02010f2301080d080a0506 72
    0x40040d030780c1201d0b0030001c8482054455010313089510a9501d81e03012102086000c01d0259280402096a002000860046107845002d4000c0421241c00d548200e5034900024540c8042c95200308042070200c100d01080c010030b8400c1e0b8203d07455001c00c1001400c00340e540d0342e5007512180604424400c02044010021401d6004e4a0781501ca00044030000c40d00c030103c8421680004503c0480f510740e40f103465411a2020041c0c81b000307681500d481e110b9884d400c0c100300c92604a10300d28646451900014141603035140120390285040d82c03c0082d0301645110000d0500c081c81510440e5402000d1034000052003400850701c81144030034105840740c13200c1c400182e40020700e030800240002c0210054039140d04c107501c003031400720f000d80301001140c40704040781001303000440d10807041d0001a420380c038400c48004000d0510b600c1600c00011f0444032003441100300d0303940030b0148580c80301408400c0c0115200210b003501400d90f0100510000d499502c00600c07500c001000c0003001130b101d0000c226551619 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 852128417 1250 852127167 852127183
    0x40311030409090c0317040b07030e01050c06180f0c0d02060901020f03130602101b030c180f150309050a110d14030c1608101515050a0305160c110102 66
    0x24a1041c40904020f0a01130702204850100341d5100190100749003450075084122400c40b040d054000e4200103203501c003541c007880010782c001e040c040c01700035400a072030701444094450000c90f403002c040c1003030b141401454558001c85d074554070380c130074064602035039a41e03048002c07616411a0365a0380c8400302c00c0100c0c1405580403200c0524840882c505031700983e0115003d081d2035841e800c8880d0002d1151a51050352151083e81c01d1f0b01d4003514103d1040d0348250010503250045041001ca00d240e040f80c420440070450f031104074060900d80040c450303001c074080c02d141c00904501d42885000c0080d00c1d200d0300c1d00300110300100708003243c0301298115206c846910f50082e400109210044a0030010140c0341e03404540e00b1035050280a1112804010762407601003980e0040004203a150405400500140030014051643e40d008180c000b50300d500c00030314141c02048030340d07400d504d4941018014059030406170860503c01c040c401603a8004d940300d503404000303981040490458003103100042c2d007081c42d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 852129667 1250 852128417 852128429
    0x102061012060e2b0c0221010b1c031211160c08010c051818070e060f0c07030506071e05030402010c060e1c180e102304050604090b0403110304 63
    0x38241c078008100941508150303130704001144003000024406801c8554011981000303510a840690030425a01b2404202e00d026003d01c00018a030141d01c40046d0096410111007100444e50b00d10b0101090b82c058840f0313840c0300c5100e00500000841400c1421a4010a0794411206403803842040510050301140402042c441c0000c200800502000900781c1c1d108440740d6106000c111601e0030741b8245000910f8003906005078905a58451040c02c440c039410100340c80d035110006200d4500c85c041c0200042443c884420010842549185002810820010304540c184089180080d507031030044154180303203840130310f00755540355903034070051b14060315151016080d10b15042c10040d04480004421584001c4038407078800180d8410780443d81d2519a0300c866210301551002042152034142900b904040d540d6284109a9111440486600c00c42c0940d10160420006c80c91405d0519128540d0095400e03034007405081404c0e200c0358100d04019200504202106a19142c0b0450a205803400303130503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 852130917 1250 852129667 852129673
    0x160510020708030f06010e010807081315050403021509150a060b120105130c022a09040303020a12090819140a03020306030d020706020718021b0102070309050102061012060e 76
    0x41e41401d000542040382e400c412545042d0100301558010f00341810704071416502d00c841666442c0040b42c2c0c611000d00a61912811144500c0000e000c680104044080a0800040034074180c20001c0c60140c40085100405c031103002440841c00d001700b4003506050130111440800d072515031104c03005040b0b5520200c081c08000c1140c3c0341204a01c4000c44c100c40d0120781c0784140c09400300204044070b41a01d0036402603840450161b881010f108180d15541d4001d01d200c400da0080701001c2000c5841c00c540450000e0b90014841c55055001074000c81c401411803420800b20643c0c0e9540e0314140b08804403958100040d500000510380b10310009020b003050804170f035488100038240580a90400e6401c58442c0c050044034a0b01180f00040c0c410071070380c80368010540c0c7c034036140c001a8bd1700c6010703214500c0241c0811010301070500309a0306809016030303007000690750001820018404050742e040b450440d00507009014440c145840c9900c15503080701c11039020007000b0b01d0610f0081020540da042140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 852132167 1250 852130917 852130927
    0x7200a06230325050901050d1e0903050a0201150b0d0b031002040602161e0312020c06120f130b06011202070204060e040b0a050f0117240603160b16051002 68
    0x1800c0000301034400010f00104440c0440b00b08003610705028009401c1c1c00038201703001c0c88224036095000764030100000b11007110340e0310500a1001c10f4441001c0250003207500001d1069803154244518040c18460400039100503081605000380752003916000701005450716800e1240780d50612203c01c00c50750b0303284215655503455501940b2450480b8201e0302c0311504603000504450140c0d07100b00c1503032910903207003545825692580860070b60041104111f102d100f010019645491000f801c05003607044d404c6005282145030440c20f090000c00c800500d1100c1c501c403000265901004a030015024280109948440740c0c03008001e009244010f90701a00b040c1c0d000510303618500450740528020042c580c201d41d030301e4281000380c501c20303a0f2044032401024010031a42c0340c0e40200c0c911440310352040d6441c0000c40220780160403c84103a60015400c0034082c0880392804209140210f80042060034810b407401c40b031110640030b031400d100310401c028240380040180038050360901d200d40303400440d10b507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 852133417 1250 852132167 852132181
    0x504060b09040b070315142202030f060f04090f170f27030a0c03081b030c100f0c020a11060403051005040203100501030b071d03010903020307200a062303 68
    0xe400250750800c007007842c2c081c006c07a40030ba00d59910006d07034042030740764050114484d060041c1048034040c980ea00d410036580d40e0403100000d0004500880d1080c80d6412103003050020818004000107a00388100e2a0494000c001003144500c3c614042e00700301042009042402607440030700ca807410244040c0000a4200d01401c0c07404c0810078007942d480002140008080103040d41d9810f8100050b200b0395a070038080000420500044c40ba1205a0b001405003074406001c641c42c68000d01800119038003c400c0031b50411340301e0f1003000c0c0b64134602441840b01100d02e01004c0d440e030848407005402c4113001005c889080e1500811580155400b804441d4001c02e00f52050000b806d064030128030030302030414244205207860240c2410790344c02606504241d1101d074002d0355420400c14014003111028242c6280f10f030703000c2c8117002055011750065591030a0603d0940d000d8140e81e4121003064490102011194840c06208010764000c0d041185078034000b02d0018080411480d50950b058100004019078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 852134667 1250 852133417 852133433
    0x506010e041401170309011202030907090608010b0306150f040e0312010602060708060a06051b0a02040f0b0901170307080c030415110d0206060928020d090b0711100504060b0904 78
    0x403640b20803403250001244c0c01e002500ca01c28500c1c000d000500f4030701486030003000c0d64000c5400c0f0100004640100707640c0c080c1c0d00c0580e40250300ca1000b9135034854200840c0e040a00031254806152605220009505000909107207071806085000726235404440c42182401c00131580c141d511244004019a95003000951311401299004000350003c0d0128149041048010042d5206500c0d130904000300e02c00400705d164044403042c130851103054217040241c0c540c1d00c01c403200320500000c04100c0b026100d0071300480c050184c0c4901c5400c444041040c1d022680802540c0c09940e0010b909c55031109850103c0d40345001d150003450b0803040380f0550903004e50300000c2c5107440c200701005540e10a181d20b074040e40c9604007252041e80001d803030320004038611005080313000c00801941111044502c20346801c01280c20521a660390140d54031095001e0041e07052132294005040c0c0391980d0100225005035480d030040242d025400c13603c0e00045000c00505400c41e00d074145014180e403034945401d0403e140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 852135917 1250 852134667 852134669
    0x5061909120521030709030b250f030605030307020a0b07020105070516090c02010203240a0e0a150b21041103060f04020916140714070602010207030f030c0e040506010e041401 77
    0xd034407000c44100205a420241031342c1c40b540150300c0b00c00b0400c0ca50740340d9040b51a00189050f8038000000f044901c0d05c000607090a58014a590303c41e0b603020110000541119202c0d000507220f90700900880740160b5501d01c01e182a101c54640e00c40e00c6003071900c01642c0070b0041d000014094000c0c3c0382c800400265140540c41120394010060089108050040c0d080340b00a84600c1410340c00d00c00c0070301c060145c4842d12510b0761000342c040f44501e0381c2c1d034422003001c0005560001c2e00685034500d001c0140c518088040141c402140520b140c0042d10200e25508148015407840c6001803030009014010000f41502d080310002c2d081c1c40003494000038071900040700311400c030702c00d401d41804283c0c0710540c02030300c010840305074680c0c12000e118102580e402e17801c40b4000700c0c0d48000101890251380402d0204000500300c40e000980c4a0072285805003080655203164010035151004000101c0c0e03106404104401d019600090140c0b200001210006092460340c0d411a003460b80384030710303290748500c814 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 852137167 1250 852135917 852135943
    0x1817011d0a06060f080c040c0e0d1119081509070f0e040b09191502130305151e070302070303060b041805220308090109020904150b0a050619091205 65
    0x400d02d500c0fa04c14185001c040c1c040d20101d5403151544440794141640034845100301030801d2441d4490000c00030f0701c41d41c40c4490445100000c0440300c4003600f00502080b61003020244034bc0201340c00e001555036550f6008043d01e03810300044001c91004501840100050207508040303428040c1c80b45403a030032011090f101140e580051100044024001044080c000650b039003140d85083e03019110100d0300410b851000c0321156081041f4070410b0030303003a00000194441c0000d041e002488086941103008010282c00c20a002d043c030700507001d8904450f10f90f00c038000742070040e22032200c6d0600301c00400003074103e01c07902c08000070041080c0905210640404642820a20241e640d075984000a50300e04042c4241d580307400f030180c2c00005e0240310580d600c00101000090805c48076000500c07041e40907101078a240e140d905a4448111450084006441c0180d030382c3c0140f103280c2070110b0458031444040245290058000d202524405d6140900030410044802c0c080140303800e007140c40c2c5c4031040403a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 852138417 1250 852137167 852137171
    0x409060204080f0708070b1b010c020c1002010c080402060c150c03060f01020115051215130b01050405151e1e09070c0b010302040207030903051b03010c1817011d0a06 73
    0x1440d43d024005211400e0300c0c40c44003d4403416142c0600c26403590400b140302181c0002030081005c0ca2407092203400d040a01640c010b1105908060521070f4607501001c3d40d400716410000380e42402600a1400d5410a6040c1c0d003a5a441081d401c0d00e40c10001c0080c5400028050241403003015002a0040d50150004803240048240d0f000010b908954407418030503d00c003206d02c4208481d01e000e81410021102030b80558000c1d030110310ac184140601145c09202d50f01c925490700d000c2c040d00c0c110050141a05840030000e43c207058403004060143c4070f0006100f000303100907a15142c00c0c074148507803111201518420180c00146a202403402554400b0b90140a4810010344030314422070340046007640000c245d403166421034003403202941c45450190309120654500200265040144001d205030382104200d828103c502010300356807080442d1400c104203010302c0d145440030036064030101c59181c00804001e502510015015040f003880d84410f200c6410740c6003000c00c40100361070601b00c2c0314040c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 852139667 1250 852138417 852138433
    0xc050f0d0207080708100e010605030a030201020a03110a0c060e0c100e12010c05030a020c12030705031008070b0a0c14030705030703020d050a120b010315090902041109060a0c080702040906020408 86
    0x40c0c2d134603c10791040d8583c56100040d4140da0b407001e40c0c420045401010004030722541c0b0344c004a450310b0b01b00602200140e5002800b0100564175100f2a007010305040c041d2454200604030040c841d001010000c0e058075a20003004400d10400c003d5071849041c0544030088896401801401051480c16024080c646111120b000828184682c030318540040d100c2504507220a02650025049858a601903100d6210030560b105c8040001d50320640440c3e99981d0f89181c0580105540f024039402140070781d210030400d0000c5135460003581d0f0102c00a24201c2401032550a100401034110542d5122171f00000a200040c00000b000422000c3e010340c003201c128100c5e520044a29200700540100003818071910380290022075040103c900a05244c0400c1180c010005071200409552122008980d10480360741181414000d000922884075001070030089400701280003403217421005010400c2014080081141c0c01e029903d5141e0040c0c0100328000091171304400030f510502818409104400e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 852140917 1250 852139667 852139679
    0xb09270c0a030f06060c1b030b0109022a1b0a0b030901090203150402010509010c11040e0304140603010b07020f120a060903140316030b0a180603030e0d050a0308070c050f0d0207 78
    0x144504a6005d0b54032500b007000161280c440580c2103504078641d00c03502c0100080844d8104840724040c191103000103949004804c51054891aa03d031404202649120158000f400201d950b10002e98071500120408072001c00007009054150000710039110080309010486405612100a4030b00c25000c8901442c20f0492480b081c80741258000c2c0060402c204030312030b0303501c01c010a900c028440c050f046240044000090b003074941c4102c11607046e520201c1c042114804400e0b900708a40d8069a0f001c0c9507505200c1d400c03000c4c0c8101003020b1301617500071500d410320b0b4984040034688550043d090781c2081c0020b15105c0040d00c8803034010b40000c0d4059424402c03134080300046038050000b5100e0030baa080300c0d20030158007500103200c016a2050010600044e001041030811015001a40001642c1400c0d480c01521213a075201c0090301451a920030b200003d44002608600340e038050501d0fa59580d12030408a600003800c1100070450b0007004100b100400001840c0f030340300e4405030256150726403505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 852142167 1250 852140917 852140921
    0x801050a031707020f030d0206060a0609080307061a031219030b0612041e0515090a02010504062f0a02011d03150c090301060602031801090b09270c0a030f 68
    0x101001e000502c01c0700c07484105a4604004040141c4090608810601c2813000a41003c0c2d10110000140c1c000c182008500e00d403414010000e00f4081c00c045070143c2c10410125030704d0184036030040c070050351051281c5609440c1640810282001001c88003692080c074103081e9580c000021041e602c0d1b04006415004034024069002040e0340038045138241080a12800ca19000241041d1410380218580125444003002001c0341c1c28015002800310140200e40340c005004010480c80307145e0050000040143e9100c070441c0c08880352440c01c614141050000c000418801c03d41141c0c0034540d145042c1100c00001c54850041ca00076250220340303004203030a0301c91648011541551640210301e1003005c40c12080d446541120081c0102d5051019010100b801c440e4180c1000015074800300c0c07001e076246900042c00618005c00c0c82c12180d80c52400c00d00d06141c0c00b406042c144600e429410429142d1403628080210031034401030060641001518001c09501c0403070020b0001c0c3c20605440702c6000f0b14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 852143417 1250 852142167 852142169
    0xb010507020f010e0d2f04060312050f0405040903030e0c042a02030c060f09300d1803030c03150807060806031509070510022d032106010801050a 64
    0xb03001014030040b01c02c01140c080750541041580641e255500304003048035640c50741603040d2504210507400741c0c14880301d00c1c518107100c00c05104030708240017840040c01078103c150000080b4100709403641504010a20341c0d00990b04401d4000e4540340301c40085c19890b4011b403800721024010380c0c0301102c00744180400e5441c441c600100c2034010520720f821010100383c4801a441762441a0384c00d08696403480b0381486030903510030000b2000c040c18000407010070710001040c00d220f030740d2001c1104c140b8030510880798080d00c9c0c4c840000307101141e0f004030f404003600108207071004d030210117140d801c05103400780040211070a8080000d01c3c0c0b100300040c0100192401080d0317510000201070280c03801d40102c9840360000d01d400e8060060043c1c0c00c89009121140034011043d03a00540b01080c14502481119000741c0d000340210350010707256000007010890362800301c0500c405244030740030109601c2441d521503d2204055034210000ca02d2040d0a4102003074007a0000741d1310104107036660410000c0e64512 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 852144667 1250 852143417 852143419
    0x807140709090b24280509010e0f1012030503070e06120a0b0f0a0905040606170105040302120307120903021c0905210d0f09090207150b0118170a12020708010b01050702 74
    0x1c0303001c45c41d0ba40449000401c2002145000070007460300d400125902c0807081c0d2010494010f442c06101d42d0712240210242d00414008080746000d1400407861703007210020380041c052050010120700d10b14820442c4500008000d042c03195074001030003c0301c64a0381c3c1110b040441d01c4c500441044c00740b0f461042d102860400800240819090038418001414082d00884801d07a071880d001440d15418100c82d030a1a4001c2c000141c1c8d80b505040107800c240301d46c0c0740c2b0003001da0308104102c94a900100c0c200c107152040700c000100c20070185810303490020104c1c89110341c00c50b03106078800b0041e8030108003402e5403401c1e60017031008080c0f271155003101902e003440f2440f207810514804e07104070310034559044112803920f031641c045541c42111004a0340042019100c44900c1400f0580501e01c90040d030303002640138a044400b441e86140d07500c03000a140d026003074890b0443c3c0d00040f0031410400c8824050b41c0c02c407100c81601850440d010307683c0c010318880c1d03003500d500300110102291b0142c0161205260 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 852145917 1250 852144667 852144679
    0x307140d02101a0406030305040911040e0406181b1d04210504030f0c09050f220204090812060102100905030a110102070b010b04050f0d0807140709090b24 68
    0x4084001d40d01801526045034940e6207807802c0301d83c20759114003030400118000e07202e00da40d9030300b4481c0e9101a601c001188030b80078501000100062140b81c16034a92168001c400060b4054542e120054600c40320071015040341e040c204404094000c02840074200e80c0d01803402d00c0d2104441628200c40c00c0111000742c100c95440d5030340b404d00c851081300d003000440903140c8a46002d8072651070807901c1103468815202003190180600800d00e0b5031207001c0d048000d041000005151060200075a050301c060980b40d02c00c2512900380071034846030003090a565100140326105c0c03201d0f600e95001c000c0200c0341c0c1c2e40144151003d040344241b40d4402c00b600160002e01452400d1500d1405840320400007c0350581c40d07500300040320103d51199804d80c081c0180b03141d55170b641d52900b000c102030501d0080c041032040d0070002c00d9100082108041f02da419a120800061159110701e03828240255580301154403400e201c40340041241c0307088544d01c11b0003174120a58080007036803003ca03074403a648582c0b240c01003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 852147167 1250 852145917 852145933
    0x4140c2a06180a053c0c010e03100f020a1b0b150a08060405010605010201150608131a0a06150c0b06280b0c010f02030412080907090e0307140d02 64
    0x801030564100900d00d46204540600c2001ea03611443d09034001950261740300c000c070806030030f03400d010b01c0100d00c00c102984400246042030046925100d00e0300d4214140300b03900d220111a03440038040d031078012176020010030a0403210b000d0980a58000102d130300006040083c404010010801203020035600b200340031040782d4603c1080c00d040900543d20a0f80305015450004003140708000d818851407041c00081045403416002a0945020ba20705085400301700005012156000405d554405442552258800c000d0b0603d41100001014070640c110103c4040140a00450700715100300c841407403440da401c80c0a003600710b8501640e00c000030596214200400e1161401e107100100340701c1c0c809407034400c4440440d1007009180f8030703078800100743c0c001080700748842800f0711804240707a001c01c03c19031540c84c0540d02e5441e043c42e90100d000901201304080303156440204021005403211403001c10a42c01010340c21980ca400c103120842c0c10141504050f500f00d1004602c0c035446142d1070700100048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 852148417 1250 852147167 852147181
    0xe030309093615190e10110c0705090c250c030506100e060607081c051609050a081203070c05070b032e050409030519091a030f06040b04140c2a06 64
    0x80d10408214848910030790f10010306c0f0911070302c2294900c002c882003560f581c1d12140000c605100d102e62010b845035040000f00076080010b03104031044402c90078003c18820440c00c075080c03007458004102500030b901403100030007004000903442d401030811130000e000b1190f441c1d448140d18402218a075800280c1413007034800140441015242d4940d5401c1820b103da204e20180c0000c40742c04580d24109141d082812401154000c0c6080d009800c080d548051034a08044a003580c0b049080c1c60048516400400106910302c10b8100d0031100d648401601c100c9075681c00e1200703042d00299030007600060100e801111a802841c10700c1040002a41d860b0b407070358a401301b04001002104000e40a00000300444000312035101095901c0c090103403669251300c1d0805ca1500258005040ea02c0c000350000c0040c0710580d40411200d582c40107084070003061418000d0003050103480c02815164141a8100074485c08900725405000a0405100e1b00d000852506584509000200d062a94241c1080c0b02180f15 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 852149667 1250 852148417 852148421
    0x3050c040f1805030405180609011a0f040305010f180b040b1008011404060b030a0506060d0c09050f04030f020102040b0906030c0f0307031a010e03030909361519 71
    0xa1074400c00000503000003400c40c06151180448022541c80c1c00004060110749410a0900c0c07200b410740403091541d107044004940c44042c1130160b07a4007406060a10080c0000f81400c43e9122403190414646866a80c503001d8040c2580c01ca840340010304241004c00f0303000319440c80c81134194000045c00302e10f440c0c07a00d0307071450f03581c014105202c40045010045900007090044207982c1800b6441c0505a15142c14180c04442e02000f881e0304c42c3e00405610400324100050a03a04100c0486001400200a10b07140d03c1285159000c1c40c80d81e400c00007004100b0480706640c500c15400fa8403a920311582c01c40040b4201c2c03080780035070710002e4001c3c0403696060410300301865100e503080070101c1c40c010f0155407a141a8204864200000e5194041c45500b01c05d0a0f4450449560a0a21421107110040026141d000b10b00c180c2c1e0041e00800b000817100b000500a03807000450010b51f40302d90910034400304200c0e07001d1200c4100c8502c2400c9003960414120b0400b18440c000004400780d0200e400040500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 852150917 1250 852149667 852149681
    0x110f010c030e03071205070f0b0903060c0901031b03090320030d0902030a02060316120b21010b04050c0a17010509072d0c020913020f0d02220c090f03050c04 69
    0x14040c0725900d808200952201807540d1817074000c50040141e00d150000d0b8480100017900321112104042c002410720f40c03000100d59070464040300001740c558001000481c014030842000c000003101d0101d0320a60076406900034441c0502030341d50803c3c0d5180f1800e60448000400980310015481040755000e124611340c00303180141e2005050b2080c40c22070b0703000218560815140031b0114044c480c0e54482d0190080664251800d01450038401910300400140305030031516102480244000c4012034681c0d400c1d03000d00c14401000300304101c0c5080030440d642250b002494124042103004100c0140f0b6600d02c030f012812500000c280c00281d035680b0804880d15104045519080d4240701d02620800c2c01d10310900c00310f01916541c2d94090307280c81c010046170a070050561481141924050405601c400c0720305601a01c040d43c202c1c404418510202d41c004030500c103250503003161f0420801c1840d4058201c2203041005a8505803495190f214a0902c50810304c001071032540040b580c44418185600492 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 852152167 1250 852150917 852150919
    0xc03051b092d0c04051002010e0c040b0f040e03091306080703021002120f0324010c0209151806030f0d091e05090a0b03070801143907110f010c030e 65
    0x41c0710300054140c400c2d0440c040c0c5540380d800102090074005410028054400462288001d0280d84041ca0800b6254040c2a0b54103006585501581c450360701c6031043d0361007000d409841000080c034048241d540340d07040900c5062140041d015000031006076401120242c0b840c07080501402c0d0320316402c001407250702140950950192070080b022206a0700e0181001110340d0302655503c1ca02440d10948500412209441d1000c40c04400d0700c0b941d90040f0f104107003039411303903400ca015200d8040c000c0e0001074000789242d1090b0810710012812a826048500820381907084480d10408212043e40301c819030082c203800116115800c018100b410f969030480703510100001c58100e5110f00100e01c0d201c4e02101e407104140e440d1000c1c0070160804000790002861184001c000b1032101c000104440341c0090250340c01c842e504181026241714180954180c65200304d100b4070340d0445c00c0c4188005400551040d10b00c1c0115460b80682424403e02c50041d10030b05a5030665104016a01591a926001e0303c131 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 852153417 1250 852152167 852152221
    0x16030e1e0c06070b19050411090a1e02040f0f0303020a0303020d02070f110a150c030c0c0f0609090b0108070512072717010b0f090405030909040c03051b09 68
    0x507040035103880c0001e000c401d0040507546400e2401c40840144842c045944030f607024901401c2101060340304075000c01e07080088a001c0301948034408014013422800d8031003074054a038444140385c2c000380c5074000d00848990040180e9030582d03441c40966a4549880064096000006040c000074401c1d03008000d0003000c0303040181400c0f901e44030071a02c2504050704030340c41400c110600e022403602404110040c45000c50780c4406920600000704400742c1b1034401420f10210440c0d41c810000000c8500340038104560001402c580e590600038800c2659214075000285014490340655204a502c2c62103003400d80c984a1070682c10002003005458000c0c403140400c9011134035800d12841b01a80504800c50300190240d070303039003460340c8801c405196804207801030785807940ca155203803a0320300e01d14142d032012103030a02c03d503a44d810030b18154400e402c155540050520104803c01840e00d1941c81074074012001c5902c080708031a21070521900508095a100a051000a040480025200504800311840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 852154667 1250 852153417 852153433
    0x80706060b071406070212090409060e010902100f0e060906070c090218010e10111f091401090b06190e0903070512030709060f0e12010516030e1e 64
    0x110021a100c541140044500004001c07041c8910500d80e02c070810410405003265080c4980080c0d510340c070b50201d40075410310100d040304107640e681c0c0c00442079542050041c41101003011243e802003841c2141240f241c2c0c480000071810501c80c84d65603140000340d40b40c0c074400051800801007207403c0070300c0307540d405142084001d000544a0f8081c2000301040e00b00940c03224809200e4155042c03806800d54100140810103035915650030300c1d081d00107441ca00380a01105480020079003802c040320080089071842e010b4110110000c2d600c41102c2c64064168280090800741406090341c03900640907008211b04004200e03189401c6070708002400c1c41c03505581400b540c81503603040301c0b242203409071156000452201c0901000b808403000c800050001e0074514540f004000d0030820290007518100700e030000700030710014000c2c0c0e07480342c0c000401825040e0701007020024078084c2008540a01d076800700a2528440c0e0b41c020b01500038000b6001020b07140f805a190511890064090782030b071142c2c880d0402c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 852155917 1250 852154667 852154673
    0x180d0609150603030806060f09090c04030b15030618061531050114210703170c070905010f140a030605160305060607020109120309180b03101109010c0807 68
    0x81e2601c00703291414004241140b5504000c0e1070740f800204041e0007004108030b8201031014410440f03e007807008643c103010030f03120404d5200c41401f494000516074050031080c0311882c0b04401c0f681c64040401c40807105c169885200c3e43c41c5000ca80e00c1514a558032110100b0510200310541d080c000c1c078050545950104a000300c0300701210800c00c1001188007043c04000d0307c11050190074054002d031401c0c16181c8100304c010441d0702c185c40030703001c0c6081900c1c409185000410700c2108001d5800c102c12050b500d44801c000d44090703000c1d9881500d00d2081d2900000c2e1621030340100d40c100c614900751194101e14000b00110b80803031240310554060144540400050710601c240c5004881c0f820300010181480703400903040b030b00c0c0074200038480e00062107501d0060f80d00c10248001d4a4051103a140f80d1800c514050700c04503425080421203c44604030a5000b0040707030300100302100308030200e403002030204ca11481241d60040c503807800c110381041a03010a50151501e2030031b5038031400c145031030160a61 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 852157167 1250 852155917 852155933
    0x312410406031e050408090d300e0d080a0c06180503070c080c0a23030604031218150b01020a050307060f0c05120403030b01020a0b01030b061005180d0609 68
    0x2401c4100800e5540400144402e2034048016040f000050300300090704003a00e610340c5601440099900c500c074094844010064841e40311031010040b142c10803400a255401c1d502082c0040c1001c10008190103030411076440c00750400403c20b40c0088006140035000d0108407180d1804541c155091900c961103050089a00528050204d018501454a0750114a02445114640d40c04299140d000803008034650360b5121244c821115440042d484034560084002d0000c4106c6c52884c0d0325000c4c200070802416004150b110003000303c00c01c10000c00c130803450381c065035011042000d0032002d8001000100500381e640024030024050046400d410400d41d41c80d45154060102211300f1b546070340c1c840b084800d01e802602d01202107410410700f48040101c144100e0302c402400a4201525240b030300581c0e034020700030b9950542e000307401144550303100c1c00c0840c0d03000d0080c0c8020f030007285c51002180741c80d44101c00b5100030415407082c5402000d514010840200c0348002c0690f1095500c40801000031012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 852158273 1106 852157167 852157169
    0x2151c1a03010c080a05060103110f0a02120d150501080103020d0615051320030c0d050601051605060a06090213030201120212010f03124104 62
    0x16503002203400500c40051900340d482c11410705030070f95202c50680c3c0300d80c0b0010024003458517240011000c5541c404180f65045000303206198240d400c1c14000c1c018a42244101d840c40000050030440b00d902c4400004070301c0f175503664101c050081c2ea103400e0b0000c0c082424803003082d41c59074000c901c0072018040300900c4240d0369001c444e1402c1480c19071502405003e0120900540c141d40404000c0240c584004440c82503813400842481e1a02c00310fa116030f44022140c1e06081210a96002070040030304000e051003c1030104031000208410038038071460080004080604025214030112130103504414080d900400c00845520362190000080360340c203280c03481101c4050101c0b040280a221203030107543c00300c400005000d010a018500c152400f8013003220781d0030f21415080e82c01030011220000c13500ba20300342c0054006501101500603811900740309800446040040c1c42c581e01c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 851978417 852158273 := by
  have h0 := BRFrame.cov_init 851978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 851978417 ≤ n) (h2 : n < 852158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
