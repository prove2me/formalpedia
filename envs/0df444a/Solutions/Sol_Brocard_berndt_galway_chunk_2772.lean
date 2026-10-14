-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2772
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:42:06.609336+00:00
-- url     : https://prove2.me/submissions/adc8fe1e-befb-4195-bef0-15ed648fbc67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 498381294 ≤ n < 498561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 498382544 1250 498381294 498381311
    0xb040e01020405011b08041202030f151909020303030c0307110d0f030c020102070308180304030b01120c06080f0408030c0f07200d021c0305040e0a2003220312 70
    0x54042e4200380300c2c16001c038545040b04032a03154070515062080e42d000500500d0182414405a080141901700341e070503114400c1c0c0c03d82144000c20644001400f001c10b091050b1514040038400407041c1c4154a448505000e50f103001a24000306503a0014014241240c80c1d0351042022a04110000e000305a039106888071a40c0044e040090800881c00da5a0300344510014040203a090784990000140095000b00005d4500034030004031040f414026020340346496a41c0e15003003980102a00651409091161008104003a02c06054001c0c2142d080c10345040c5032022014020711030042010b4810071000000a4240000e1400c60344d20203140e258464990001d401c22603071064031241820030b07207815004c4000c142c6c5004100d68105582c01000854a021030215013208040c402c2c4040341802820b202c0071804040240401d80324500440d0b001906000450807102801c02c013a04c20b807203102c820000c2c4600d01c0142c25800c522944810041d0154908501d022540e94517036800b41c440c200d146c41180f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 498383794 1250 498382544 498382571
    0x515031b120604051e06090702160f050a0e10230a06021e03160809030102040f0e040501050a020a09060f1403010609140a081f2723030d09060b04 64
    0x40d010b01d070181d400300980d955840440300d1103071030010444444240c00c80020b003140351030310038190b114482d88191244035920b1b489600c803201c1c068004000401c1c032044248000d09000558100401050b0716a10003402c000b002c011000358280120555180c44400000c803005420030903810002c00940300a17480c60341c03004000d4607141c8085d10310900c5070990322003c0c545a0000240c0b01028000c90540161400c00d9417003104031f9000110454040d5024440040c2d60b01c089034480c0001c00c210440d52001d0300c3c00385440c1c0d085540041003241401c0c814800003840c2c50b40092640165812401c051010010500064900d11118108540c0c0034000000218801380d200000c2021103552030030010701c145003801040640781c03442c090840c1d40e82c071032300081011003c0c0c0702686d001c44410020008018103120342c111444840440104441e4000b00c44150800c008400000000d0760f0014041c50728080310500c89480340300308a2015002e1f07440e040e84031700340175450f441980383c0400103100300511440740f0b54 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 498385044 1250 498383794 498383827
    0x708031008060a0b030c13090501090506040318030b270607200c09040605180a1b24030e0c04060906030b071b1b0b0a080109150515031b 60
    0x1036640500440b0089520f0003401c0c02040d074812002000342c0a030728201001e000c0c0044113000c0f40b07600c1d540c542141c04082242803064584450140340540764500e000e0901504d070010010801898003103014003040401e00c0c204940c0d400a004013101c510018400640c0444081401c5010500d80a00428881d01982045100c08807503964030060742d0b90100001c01b0f40d1104206400ca0341c01921130000180010280d0344104d51145580f52607141801424504524099540c1401c48164100a812000c2c4a0303803a100c150091441a50050000e1080c2004408070b80d081d1081006040d282c0040c40414001070060380b1403140041c00c20040039980300c407440301a00f00741c071050303910f03801080104010a100304c51203490154040c880c03402c40f00700340d40d401d07558440c0c61108940a070113070381c0c02042e104042c0c00107140f101d1590303076a10019410030340e00c1d408844c1886400c1040030f132115800c000c10f8503103d03403205012286051103500ca569802a80d03001c8080c5043c0280da81c4000203c0098030300080b85d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 498386294 1250 498385044 498385049
    0x9080a020a0c120309050d050703050a12141611040b0414100605121303050403150e010605040c0e040f0b090106050a080601030203070c060b0117010b0918040f03110307080310 77
    0x21503001c00380da07070f5569554101c18012030240000c0d45521062110303081452000c4081440f8000710f40806699849107400c01900c90030440c0e01049010760442e0380350f4420102c3c400044545449071901c201d010401400951024004029285200c1c455407103a07a594031408034960041d00c240030510503048203510130302c003c803201e0f0480244031b6000705845104801355100f5200c16040d00c507141e19001c421404040a12074101d0801008200100004000e008147c031140500e0070b010039001d294000780d50070f65103550803060048e40342c0210b003002180c1c000c001c0045ca41080c4e82c0080c0d8441e050b86c1400143c00540c105031f4100b150341000044040d0b010b00104101625503450b40810f071900801101030340300664410b00014000c1903500c0204105070700503101060705040c010b101a001908260042d0740907440046020808540403003517050048810072010303070a03a52400140340a03500d0541c0110805005000c01140c5516092803000400842c1d180039040f1441e0b03034172480c019010b00b04006190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 498387544 1250 498386294 498386303
    0x10030f0e0124030c061b06021b0f0a02010e01051602030a050d171005010327151a090109020913050901020d06062c040914030304051e12090409080a020a 67
    0xb22400c410031064244040a890b808101410b41500d040300031201e40100810f015030050001c001c0340c0000d8241c0c802081c0f49045d4044840d07500d00b0f081c0d03083e414502e011480c400c6907005008028010b0b83e101d152081c1810007400c1c032940b61032940e07240d12004103041a00a40620519480006000307001030301c4001d002880d034641d041081c1c2c0c035818000001081e21801030408402c68248542e60094001000b001c40c5042d808600c00176040420f4502c4100440a030741d024208040c2035140356107405a84912044014a484001c50410120366440014030500308000ea000c85c1080c8180e079a01c0c81c3d0494911241410b03c19030400d11070450003540302035010329890385850000528a4060003200d04c048080c0d59010b10840001c41d608440070409900c0c07190301690382c000c0f050010300d01c0342101541041040040d0748074507040c41d24070f21b491054070120b00150380310303180000720140008220101c1c0a0061a054807202c0400118000d44102000182140e401007104402c881d800265508800e000d0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 498388794 1250 498387544 498387581
    0x2040b06040605030c07060209031e0601080f0714040e06190b011b0b04020f030a05010207060c11070909030311071202010606050c030901260c0310061b0210030f0e01 73
    0x205000c0060601c554818040441d1003440011020203401010b019454083c0e000549002504400207041140e5096900b40c1c5000c0765018901d40201000440d0140c9000030041100e8000c407420150f640d29607100d981107420014004c140b07541c0307407030300404440c0050104984450070001441c000e42007a07245c2504445141c10501c44940d0300c1590600c00043c01c1180349030018100791290300310701c0f000030416078100c208420400600d0310704100c0399a032180210001070700d502c0d051410f1003c1d603003031b140381e0010402303400c3c2400e801c45800300d025012982c40c03020018020f1151728054024040b091170800f10110041442028810040c002c031400034055802085400c0d2104015500c0c0e0044450020f00c990042c01020b81d6540286400c1e0418400e4070003411240c001e07d01c07541c5c4c0020045995807000b040200512050124032003800c4007501440c1003400d40420740c812800e001d800552000784c80342202c1080080c0c103d00984c054000d14018140c00d200c0e1000f03030450a406005c0000c00c0074001c062 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 498390044 1250 498388794 498388811
    0x801081510050f0f060f07050c040e030f1b0a06020a1803110f03010e25080f030f0a030f0609060819050709050405190f020109080d0f11030405090109090204 69
    0x300e046454840c088a1034a040c0c0903003000184044942110340c10394002505812825440d030f00e07200503240c00304482d072080d40e48000c83d1800c6400e21000b181070f02e00990504400e920b18100210640740c4440c9200702c01e42c2c0319028105404000e02c46186c10040318040d1861900a210700c0740c00406000c042c80e115210742d101d01a0001e00560b416103c09400780b580400c0b0b6943d1031504000c0304154040c02000071880340110094182071040c25008001054840e5200e108560700105a0768000c01e105000342084419009c0501c0c2c80740308024000003822000035495400c030340250300c40c994000303a0324002c00000707840355540001440315000740e813298424945900c24a040030050441c0c01503100c1c0240601c0352400e0386c603001a0001410840f07050103109007594142c0300c2c8102580c00d10b8000c5545e2546001540009041034540b6040301d102d40c0c0006e100030039001e40190350217038041c0300c0c0c2c82d01c40d030001c1c0c134100c416055002da81c1145138440e210000008522030180c0001e080c00d4022503080081c083d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 498391294 1250 498390044 498390073
    0xc12020411031314010e01020d060e0601050c0a060b210d03060807050f04050c040b0f040302150a0f111009030302040510030209010c17040f0b07061512080d020c0706080108 76
    0x41290b42e910603d5070401c02100056100303452803031601d2400001700350700c40c20090250a90300300c0e821001e500c84c0d544404110b900e541414554001e513080c01d0161401001c0380d401e94440b400c4c150068101c0d921082e02400b00d0f02c0780c029004605c1e9141d48100b500d203c0c0425010348a2050750a10400207082010125610102003036030400c440004219031a031414070340c00e02018081c005c1c40c402d209503042c000010400c0d14a03009000041d40010306a642d0382c2036104001940304aa140c0a20083c024008001c0c0d85030000c9200031604500d04140021a500c15910384c585005c990742003d207281412a941c0426030941c026009541003107682c024080741100c411800c07800f41c0300c2a980010460004c21000c200883c600119031080080b42626190710380b08050085002c66000034003400c80020390406102c09071180d018038444542650000920f020543c00c5030344401040902419800240341a4a41695044134a000700100559016a41c3e44602030101242486000961f00406166024a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 498392544 1250 498391294 498391297
    0x1e02130c12090507050a0b040314150103060923160b030c0406080a02160b0105100801050924101106160f0e210c010e0603130206090307030c12020411 66
    0x4041560390703190024003844880014280c0e030802603540d8002c2040118060300c0d078a10f00030103800e5040c08160307101e18510784150910180780c0c8a0000350401106510b00f013010501c010b0443c2c4d0012008110208235042080740410707241d020402042012054800c48080428881400c1e070560152014555503100129158030044440082e9000c1c100b000344903290141c030201d070304145c103c040141004010600340d15044152081034848031031110040080786061013400c98001081e1038001e0700765162801207004031002401e1040c45c0340050800030350740c5e1405202054043d1000b0000503580d8a8054081e002c240c4041040700d0600800340050440381850700c0302003401d41980d85070224a1a044c40444c1c80400a0090590044001010842008403800f2042520900c1005089110b00b044009440381c40c5607c00395028074000e01c1000f4680c00c14010089440c1d4040c0c400e140e030f481070040040c2c20300c4039070340009000c0804440c000c45c041c440c0c98910710002c1d02c00d0b030b0200b0441d655035402c030303800c1e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 498393794 1250 498392544 498392561
    0x140a0302030307030809120c03072102070306021e0d0902040b1f03051e0a060f060207030803220c1403010f0e0c2119050c0103361e0213 60
    0x940c1c010480c40c40013a00c00c00060b603200340d000c000d4462071103003d04a42c02940c0318549035150303640f0205900e41480b4524a003010795076160582c22106106190001e5154100d030701c030280507140e0124621400d80355031552407950000c4950511b5076070100028403001000403030f03816800b407880d00a80d1141400c004001e10040f1244c9000b42910105c516400c0b0b01401000700a820f41200010150908aa00c40d101c5806050300130000300d621410b2140c0c0b41010040d0780e00c000c08540c40200200041502001226008441c052003002c0b031030f003070a203d502c8800c06110020071032030111000041043d4516401701c1c09950450003070100c1503050038200306541868929070003607000091400014a8011151004024560340030b22440d8030301561141094074140c1c2407034440c8510141042041000d20105507000c9007402d007040544021018001c0701440341084c452003078041240345916014110b0709008159004018071400790019203540420105204100d001e601c0b445841e07407042245020b000403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 498395044 1250 498393794 498393799
    0x3070803150d0f061a03070f030308060f06040602033703020c0c10020d090b0a080601050d020708130512070b0315060d09050d18050109060c0204021201060801140a0302 74
    0x66450740e900320419120040080c503444201c4a00c50000503404450151000f80104e400041008502c0b501c1340d2440303a9003003c01d12940240b071060100c2c070151000e520690340c243c0707004040340c0d48080101d1100820b000c4140cbd030260021600181d2168000000c00d8100507500300004032501c1351030099018468200b600580c0761003582e02c0c00d11a8420ba018007034443c50041214012612000070134103203900f28800300010780140c00702e1035440780c2002c030306001406401401c0746058a500001001c0e180f014003d241046000910140035900540560300955040131034565075404062a03d20b00c12142c0c4a00350040c05e4481e0404a0841d02003900343c126266030050700c0c5150f4860080103082d25003590050380c811400e0001c2103201484d0b02c94598100d00c280d0003004010207040024041c03a03040040d105030701001c200f05105a903806001e078411214a810111030f03e00c41c920000d0003038080c003c501600c0e56816000042e070300b50b00c00c0c0c03041d049913514816000030410300c609000382c000150001a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 498396294 1250 498395044 498395047
    0xb0712090b1c0209043204110103090f0812160203070b06040b040609050a0e010b0d030c02190e0f0a0f180b13120201090506060f10030c0e030313030b0603030708 71
    0x2481802e00d841072070b0342201c000c400620f8105900001021960346d280a80220802c3c6c0d4003005841070803a200c02e010184441a50b525468995161650030302030b000814105503c85c0b4580d0100700700e0700120f0315070540c05509651203102103048a00121801c8a1494081e1811024201c02c1030002c42210251b1303400010b803400681e5503070244000b0385402e0700b2190f0856034038000001c5c00d1020748070781401a4041c1d8404124501400781050070b580c50003062a01c20002019a440040d07000328859010b80c0d03060364803c0c08842d841e00303801d10268165100c03400158406080003425650322205a01c07450446404020000c40301900400302c039030100092000900c00039480021640b0b80c12415444200320820101d440b05a42c1c0b61680421401030ba20003503910b5079044420007205000c03032a031000c001d45040300c400b002c0301c0004022100350450340080c0f668a4131101d900c0b601c44c81c2e103244444000750840340e585c880284038241418603031200b520030501c003101007105858003000700d682c0a43c100a649 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 498397544 1250 498396294 498396307
    0x60a050609040506151306030506040204051b0a030c1b03080f1006020d0810050604080312060f01140d09062d0209061b0a0c170610062c0603010b0712090b 68
    0x6601702e0aa01a00c0e540c80040c3c0751551096150030300619000c0c501c0b0780040c1c9250305090bc140300640b8000761030b0308142c0c1800d0400000013a08035050b0380d0b243c3c1c4103107804102d030740518000769010408020b00040c0c4003001c1d1804030a00d82c200e00c41d075004e1709444454002d1b0f660f581c0500c09410703405024002c016000600c4280c529442109034070381001c0806148840142c1c1d4400044003a8043c1d4004182ca0b000030503105d07948074024404036803100041d07071040c503580c003400d000030086003c1a487c9007440da8081904901200140d200010707042c1d220038108515071080070484e804c034044c40b12407480c20303540310040d1180d40202e0080d90f0075150058221401c005400580b0b0700b14210070744c140d00072442080c40c2000803034201c00501c4003d080301010210304101a81d59a070034100000c050074610049160104801e03a0703c040300340e0381400110383c88441140e01070a100b00d030304990005660300c00b8000c80080380c4c0d0b50b916001018614400d111102d02d03807084440c25983c01c613081c420b9040000050181c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 498398794 1250 498397544 498397561
    0x3011403070b0a080610032d091208191a0f061e0a110a0201120b03160e0f090a0c05041a04150e1e16020304080a0302060a050609040506 60
    0x10068000001415124056202d20300c142583e0041e19050700000d0313644041c444a814203030784c82c2a140d0750320302d0240503146803441880b801da04045030132410f450360001c111518034810b078000103925a2145500008140c1130100400ba06001e0300c84103202002000a640c0c502028031078071501000c2000c224038032114160030800080d00c02403400f0340007881088450031203640c03c600ca0314041884a000b90f22001c04100080641854540fa004183c0c0a8000340000d80c7c2c02002e0002100000c45021464030700c2800400e0810b4281028100c80c402000008102d001182e003040380b1640c0454803030032241d0303502d02066944103040039015141458580b0140000e040c10341107150103030040c089024500a0050100b0300321a40d04060704900d0580c1c0205004981004100c1030704207005200d548026005410b0110702401c1c064914500044020845aa054001d0081d1001040b505c01074032180110341c203011b5210501110a81210b83c41d180018400745000c0c0103440c0140e800c88001c00c140d07640c0b80354 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 498400044 1250 498398794 498398819
    0xf03030f0207022b080705061f0311040c050d06121e20030304050d050c010305070f1b0204060f0b0706050f041a091510090b06031e10121406070f050301 67
    0x803a0030025080681134030110702041c0092100b1841200185000e01e00800e00e032021200c000d003643c101d0f900e00c403c1040031030000003145c1500002150001902803203401c041d6414826070142c10745180c20b0400010703108612000050340c56020b0741c610044028100940001d41100314401040c0b0b0740750181101449111040b0780f03c1040002c1c044a15284c3c641d400a10032a0504404813110f6000b031280307a01659041c0070789500b107012170034114506880f0001c05044003900340078440304401685184410f560380c54104034028070041034081d580d19220090700125903c10001607400a0400004c0f030008404010100d103e183c201e03400603c100c031014198100014046c103e030040340300e5a0210070040d4008000c143c055161814811035041c07134240d07000c0503240811200341c40340c20144104100064089121000700002c9200e0390340c580d413420f000c800c2e0381d111504044211100200307060b00b0400710b0741d00c0d00b41003800c0504070740d81c55848180865401c01d500180800090f024401001408103041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 498401294 1250 498400044 498400099
    0x20a09030b0c070f0602041d040308071206091505010216030b0f131416090b0a03030c03090b0d0209130504201c0606051906021c110a0f03030f020702 66
    0x300b81030b00d0030000c0d40755040600084001610b52a40c0010208054904a07801628940c0d01581c28607030b40c540764501510112004280d5020321450700c124a104000540c050b2000d0000604200040226220200c0ea40135603802010302520034143c9600e1281119250302007129445060928580da91203681c985441d4003514011000300069001c0f000a41a07200c0c50084050000050000342c44106100c035074964594400124103240c401200003584a0320481c1007502c1e01418018002041ca2504a880d940e03260301c0241c0d000c2020a03213460008840e0014040d03880100c4e1900ba000302c800c0240800c6031025035000b0a40035080322070707401300c1e03c5081040000a01c010100380003000d0000300134100b070f48417407030446030300d656460180004d10b0719008042010400e00140b111070360500d900655500303500b00c0307071100308070000051640c1184074a03420b2000707981203000c1d40c42d000c139141b0740050100d0741103074100d021030305015001c0b4400d01c0600c00d03901c41a80040100c0880d4090f410041660001403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 498402544 1250 498401294 498401311
    0x4050607030c0f0510060b040b0706020331020a0e0702030d0b06041e080601060206041208040c1503090302060105010e100e03030918010306061a042d0b0406080901020a09030b 77
    0x20222003000c00c2402c0c0f501002c0c1400744014010701c4c000380e03c0503c00c40e4155088480907940c140002e101c0f50280700180c80301e403944404010f941c0d454080c440e00200c50500030003207454000f03807a1b00b02d80000d40d08502d25041d01c01e0322181800350304d0b030104106060044824000590040c8000b01c133411894220500c5450302412451070680c03100902d5100031080b40403034000782010102040500410480d281c018040b502c00b803d00e9003450307516031a42c02d9402050030100010100450240001159000010a4140180b1602521442c0c020300602114070003036001d40640c0c4000109940a01440307034002d600109003980000960700260f074400700e0180340e80d41600c0240001c1c0210b03240d003920104c41c41d5a031408030509614500e02001560341c80c0e00302500350080c03911310303054980320601900d0694100346074419400c064440c0704510310070801c01741402402c3e0b0090008101c4003440081c81174403165543c0601d00c0e0f0300c15002c5401d034412021030200140b9034850400124419020b0981c011200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 498403794 1250 498402544 498402557
    0x118030507020d050d052a0a080f12070806034312080408190f02090c0913060518012301090305011e06060c0b19090209090c1002060c0405060703 64
    0x50b4440030b03c1c1075007032030542000c06c10001c0c0315140030718407015801c981580c5548900344110348500607501c0310503800c0d000700a55000b00f000d0720320750b0100041c1ea00755003150034102ca040c0b804140c002c2040c1000c0d1100d074081e0007800d003030395140130a0000d140700200d07403501424900d4501c86445601070518850a00030004090404203000c10b6441c5a10051230140a650ba00c81e42060811418400c2c80d00e03c0d480755688100c0714000003103440c4110954503404603441a220350752025000c3c118482c02003016488084008810400e060301e0f80410300752401038030040986802c5c500b00009890b0f0a000707110002c00110091280300c0d400a00c2c04540a8043c0b6003640c166650b9901e06080d611034507280c1c603140c245560740410208003482100024505032400000904c031a0301c0d080c01c1031401501e00061118600341c581c074850001c1c2c0013080e900d94040c110404500d031020323043da01d9540d402c03881d600c140e015041d10f0500300c0c800101c0c80d0103044a4103501e4542881c107820040954017a0500314144a0f0703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 498405044 1250 498403794 498403819
    0x51f0801152a0605012310051917060604031a250f1b0f0201032c011509050601090e1f0815010501030c1b080708030118050702011803050702 62
    0x20102150310310003000c9402c052440c19a01d0094143d42d016003120881d071100480395407007442e80c04041140400d00340c1d00e48840100380c0c14101c6041c8609100d00022000b24444181c3c030547c00090022141110010414541c82c0d0f0000c204c0184074501c0b000e004180340d0243e12400380c20b40440150403000000020b02c42c3c0900d5074161034500c90046018001ca81008200401e40d50005c8402c04a000204482100c10105941d115000c154036280030b410142d6070104e808460802c00b0740c80141c840d00a08001c1010a40c08185002c0d01600a260720311442e80c09000031110954011140545416195207030968103089050344c40101c010310340004049021004c014540c0880c0b516009080c98402600711424002d00182c85818103074046410180382464401e007031030b4002e03244203141d8404090f540b8011502e060407403160158007c00740002000100014400c010090601c0107000d0000085c0096981c5c140c059080719800100d420000c400340c107220780003c1c03040c40205001c0380300406039104101c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 498406294 1250 498405044 498405077
    0x90b04091e140f060904080318010609020c030c0106050612010b0a020c10080105010f0806060301090e0708030d0c1d060703050903010e0115080c0d0c12140d09051f080115 75
    0x140b03245104500140000305028160400b00002039008105465030f44541c141965030701d10340d1100516103200204901607010702131a0a41044000700000c20080d5184c2003503499840d2030703034020700c41304800c1d40c82d040b030000301824030307405550078000f8810610000d0780c60010980000c2c0d10061032034007140502c81450100d9a81c41c4504440d0061550701c03d0381c60340c100340002d810050b00682d1003050020140400c24103030313507440841e41900c2442201103910341d02120058500845500000043d00010a03050313901c1c0c034545e00000f6641140d9035608a20000740c01042c03440303070b04a101c1e6a04920104116030100c0e0003038000780708244014000086102607280c1040c2140d07001c604c40d118045511100f040f1002c000c01601840680444501204001507910888000554466940100700700914030701804429024010b240c61503601381c2d801c040803060010055581d9000b03052081c40c12440503954003680c2d08014840e44550303241c082030790b403d00000441658280c00701c58200002500f4018501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 498407544 1250 498406294 498406301
    0x2341d1602070902041e06030e1f090209090109050d05030c070b0c04090e0601060201230f0408070803100614070f03030b0f04020c01051b16030e030a0618030e01090b04091e 76
    0x8041903d00d103e5020421941c601042c645980560100341c14815400320720a00401e03005010701c012000560010080d9150602030212f40c040a544460707494100041503506422440640e40316005503588040d110303c05903500c0c0016a01c0321031100060007078400094440f9031480d0031159118140c4c4c00d141c0d07200c060000b40c40704401c20700315035000700004003c0603409006000100e0041d80342041e9403206043c440a003804010040310001c480d0300042014450350350119800f40d034104000c2c6603a172508101b100d01c0c2c40054840d580006042c0660851846d1850003514195a0f000840302118100c17603d044025199450000c0c0d4000c0d03443c44014220f1b640c3c5c0c40203104491900c40080741a20344001301d10b40d060003041d04c582c60100c0030010a000301a24402424403290f050070800448450360012a1401d07a07076072001810316140094504010a802481c81c071924441d03a41c1c0d119090203200111503c04aa01c40c91001d0403080c4401e10500581c0e800541d11b65010042d0010000350b21104403054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 498408794 1250 498407544 498407549
    0x40c1e09241707050306070518040204051f081b070809030708010f090308060a12150213141009080d2a0b0718030f0206030702341d160207090204 64
    0x1d103040c019070200e0800c01d03c0044020841100078290a15110782e020f80144103225103500318440d80000c0300110385d41c9034140d4000d084040d00c2030440072648038241104034000702c04c000104a10310000345815608001003000d03080e00e00241410609c059844660a41054640035418051808007152041003441500700c154484900828500d08609001d0000c41c00130340b4560161418039000d00040c400503e4081806a05c900541451007503240179038001d000760f210801140c117005200141400340714008120740c2c1011039480035950361176803003941c02500b18815007240f80c0080c000010542e00428402030000d005404407042c0c8081400c411800d01282e96040342d6a034080401e015401da84421128104a40b424001d0f2605041d501c80016010032001c000348152000400203141c035100b804010006000f00200000c1481030301c5481d41903244d1400940f00c0e0301c50190002494902d21941444c40d002109940c2c0510344906403c00e01e200e001c1081c6c1c1081d449520300004a1b000940300a100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 498410044 1250 498408794 498408809
    0xe120a02031002130504020c0c2b06020702040501050102010e06041b0e04120806102f0607021f0213030213021314010f0807020c010309110402070b040c1e0924 70
    0x940e1390201340300d41111081c0740c00803801144140702000c288400000c00c9a91000112506030243d048020703c0c5105051030054a469140e144a00703008002d05a00a84107030b920131102880703107a0f2210012402c03140c0c10303184201142c0c00000860049401080070300d01c051040701d58505242d803212603486040030b0507181281d0101d13a031007050448562051416400c082c003110252840c205140c03009002050f02e0000c502c90040340a0098440750b58a880c1c0b0b030110b41250280c41c00381c0381020001e0b40b51041502d0420a0300305101c0c92400343d504510071170b8007100c00c8040e602c07056800c540a11807070310307210200301c100145d08100703081c41114a8102c240007805188500e0b40408224030004011842c2441c409050105050034455181d8000c42c0d9408000d0080c070b0001010107031070030301d0411043c0412409800c54400a01d48080c0500b068046104034014001803002d42e50740c0301d001440c441620310141d04450022401d0007403803203503000400520010451155102207000c5114101d0340035030322424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 498411294 1250 498410044 498410047
    0x4080d140603010b0901030c14010302071a0f0a050c0a050c120712170c091c080f0406030e0c09012619060510050f0d05030717070b090c010e120a02031002 68
    0x441c1d46401d014510301d0444c2554510000d500d0350391400c00a80180c024515039400c5402c0110741c59119030305a42c8055085800070b02020f101560300c0394114802ea40040306164004006103800c1c00502a06e40540300d4411018908a029070049500e41c003c609882c2490150401c3c00002c52200c00c0078100190107054003640042d89580090a8405036482d582c1080403000c04210402e180b00c019174020a0342a1342181150500407010000d010f001da000038910b20003c1410400803118201410980d0f0640e1010403c0501000082d5911840e100740c6581c003080c40c0006001c1100000184c0a0800904da04144801032990555090035400d444840070303044018805000c0c0103642c0500c58022100c003000355607413400d20740401c21941e01d4218140c099501c02e4a01c80c10043c0401c11111041d800c1000450202641000910150300c101801e98030010240040b40d46401d0210b0b030007840c003034140c40310b00c1e64285240c103001a9204100d5203161a0051285d40c0c0c0158074144020540402845c0c40107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 498412544 1250 498411294 498411301
    0x1509020316021902030714031c020d02010605060403080901140d0606021f020c060105010f1106091b0105190c080d0f09020901081f050c041a0705102304080d14 70
    0x3890305184180701c3e29203440c001c00d61000b6807008909402501c10b03c4c94000d42c0312072000046440d06c03038603071813000050151000d0b03440c50710b60214810035035400950003801708640d04c0040108034002d42c00041d105c05400c1103036522560240000c1d448840200d00414100b6140b44408022a80380d507115a0240e0000305005100c07801d036503140500c00d01c0380d581c00c6003040c0c6050001542c4a00500445050016126401c900345028a800802d012442f408481c0c45141007219103844a154144c2e120000da0a40310b601000e42c0248290351098411550180e84100c0a030000c40700d004d5150000d840c18102000b00c907400c0300007030140c1c01d04040d01c21008500c030001c2c3d1050140c024030503030000030356070802026002c4100306170850039585006904086038076210300031403030542c0c801d5600c04000115000c808100c9a00410058141c030382c01402581c10f45841189000309881c5107004c170b6001c4880c24080c040b000703400e6600e0306411901801d0902c1c01c6c881c4107500801280c800301c0c49140020b075a007081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 498413794 1250 498412544 498412547
    0xa05031c06050406210302030c0706020114100b1603030f0f02070233091c1a010605030c0304120903021909050a02090114070302010b0d12110106181509020316 70
    0x5000c010700d0243c408102840c50140031074544400c40c2d00c0c8243c80b100050030942894401c20986050304620390503121055580d09010f402030054034a01c02a01044400141d9100e54002c801000c540159082c00e04c2c00b0342e100b031681683c203d904000ca05069403092041d080500c64840c66000210301200141d40d01107500410060501c03900301c6070181c02d005149464103421004403c0380a03111141016100d122900000e0580e100b6141d03081030212841c07540105000032007007042c12408520854080305d90301e8400c100c032640b0088030f40118001c0c0801c0494005050041060341d84021440c040c0711040d00e03030340054403c0ca0105aa480e1024a481d0140301103801d0b84602a0821068030b005c40c070b080800030010b0026240407044016000300401e0240600d8001c0d00038820440c0000c040c40042e448510300109a003840120400000d181c00c10803070301d00031051003103509841c1030f41400d0480320340c8031400e6400741009407080b004000200348009902a11800130354013682c850920480c400c00400300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 498415044 1250 498413794 498413801
    0x120a0b0106030e0f010b0a060c0f0206070305210f0103080c0123010f0611060103080c1504050a031d090a1e090f12080c0f07061805070501031d1b030a05031c 69
    0x1303658610380d01d401219135071542c4000145e012201181400c1c05444524106842034000c0c07643c012f5080180080c0000c10107500400415000e8000030001010314410183c800100c4001c0301d07540702e0032008a005002003400b00014002c50340b0b040001050f041c13010050340c07032200c60130000560015081d000520904075512010302c0641410f14144402030a0b842010795200703818803000e804403e00042c0c1d410460030034070000810340c0c2a07100b1202070b820540780283d03403a4840c0da410341c0004c003234032400c840c0c1c5115240d44811341400103140f20210b4940401b01c00082041c42c00100d000b000154102e03a50200754041d80d0ba07030601403400b41c008203059040c988070a414000e4114200640e503007c0000185039882600c5490072506030850f103410182c60404010042c00e50342058280c25900c0b0641001b00000d45207060711070030f0360700b0b102c00c100300c003e90700c490090840001e500e0313000080702c081c600d424110190302c245402803c4500011554683c1800d540c0104400c0c40190000048400b001e081c0c2e01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 498416294 1250 498415044 498415063
    0x81c0606091205101a150706050c0304030c17090d1103060108070f03080703020106050a0b07230d05070c03120f0212030114120106030813030506010b070809120a0b0106030e 76
    0x7008004214800d80c0d440344c4803c0102d020b0284242d903092078034a0301c0c0500034196402000940601e01402580285605c5070f0801c0c5c2080381c1c42414000024148243c02040d01d01981d4140c40300212018180d89103d55030070000360400f4030003820f00000b14990b4409007084030082c01842c0c03000c409545c1d04141402c1c02c42c160800305003540900010040a81c801c041d01003100d4000e010340b40c8801c0c030341c68201e01404050740601d91004421101042c9144080020b0001500c20000c20103100d404603680b0b04100d0344140a074590340c215998010086004100070700500f4411442d1061154507542d840305104144813a42c00000c00d07a0654080090301000868800203808103542d040d903140041c0242c0500303424540e2809055030003400300681c83c0940014028690001085d0b4440901107803100d81a019444241d8451282e02e00000701d503131100c8102c1c2c0c1560f4000ba00c2e54903004243c01889201301302c445544110f0303c100741d8105c01107105030004502810050ba0082107031085000c10781d25007101203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 498417544 1250 498416294 498416309
    0x105010510111501090519090503041e0b0c060414070e06040f02090306163506030a050109050d080f06010f030c1815140f090103020304081c060609 65
    0x40010300c441c0d918101008000746691800c902000301581070039083c45400359059156203d03c0d40003083c85001508403502c160941e0103a544648a13810b640c40545d00d070315030007510640042005002103881070301c60340f0300c2061100c1a8190f1075541c8110b2001684030800e081016040340c8280010440841c1100e604030b001d0600404065003003007031010210340007510343c922581d03071f1f00d40c02c84003088140c045d501d40020050540300603241200c004013201214460213400284d1195210700422030124455840705503000c01c03007945a282c41c403c0c051400000c2e141980c0362003282d11400000301c0034081d166405105402900c0700e1a46824050310400d0040d0800300d89104e400204065a40c5c0700c8134440c002c0480c1e02c0c000c640e00341c5070081903036800c051064072446460400000b080058200035048000e08060769020080002c014404c040740c01503842c80c107a40b410420102c8000d40c400e4014582003400f660100b0324010b4204440c902c07408800382c3c40c1d092207413100020000c4035000003213100100701070b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 498418794 1250 498417544 498417551
    0x6060e030d05030c0d0e0d0c21020a06180f1511030c030727080f0d0203040308041203090506120a050c09010210051e07050d060603060b0d020315060310080105060301 73
    0x2804015000f404001c100d1449900c010880f042ca91100340c22860010740d80d8419900c512201c07500c002c040b4000c01c0d40659035025010ba002c03000c0d000c1c20005001480c02c644c0604460b00381e40d541d0350007420702c1441840309480f10b51251350102d0a2440203c1145200c0e1168030074007001c000d441000d4864192088440600c02c0c03003084104400003003202c1d804141440d052046080744284060501c00100300c202d030501d250140441c150400194403010040010126003810003030f54000c90340c0b4812800020004a028003040060448032204440315500c070f800c00b0000d841e280c102041c8039421213680c050240e8104000d00c21114194402c0f540c0000da00d4001601c6d0050150000c0e59555460182c5210f156445001403041c0c0904528000d4050124000070314504012500415640002000d0300115180520001d41107000c0c0c4640b0080f00c0440e44171034100144c44021000941004090b0152004100c0307040c0003540d510002140700700304030300240b0802070a1400036401c60340010000f82c0268074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 498420044 1250 498418794 498418813
    0x3070810081609050a11180f0405090309060705010f0c0504030201080f06010e0d030302070204020a051e03011a0306040e070303050408070509040f06021605100b01080a0c0f1b0c080106060e03 84
    0x102c1c414900203407101c1c00d0010406440d1200140700400580c002c0e004202c40200300a017503c0700180184010400c12036580110060603807c1200302e80781650403840550040181011a040610140c540030f40240000240d01d0161711004007138502c00c120690004100140070b200310b42e08020041d0f0000c031180315204440c5050340018005028102002d84a00010b0300c02c01d00701072003601242e040c20741c0a00195102c0c6c104c42c4000d02150854143e40500c00080c0011a40c8140e564064034100d40945140d896221080c0e010925140e001820980d0050344a4000102c09001004031400540c03003592000e941e5440d152940d4142121500b16512561029052201003421101103955468001400681d14065140703e881030401071a0300400318041c0180208408509902c940e8444000707884440b615995145a03200702c0c1c1d400302c005008141c41c90b03880d0b08214414a40382c4400300e1000b00201d0012a1910b8020300080b29601c43c1407183e4480c181409510f601119080010030294003c2000d0013 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 498421294 1250 498420044 498420073
    0x120106050901031a010f0536090f040b0a0b010e0303130e0105032b2a05060a0902010c030c080903010e010501080708010902030a060b06040b0c0a06050f01061706150307081008 77
    0x90901265004028012909808d00358603080040114028029130195402e900039440d1084c41a082c1c40364424418003000800501c40500111320507540a1807046456403a150000028001b00e00054108500c0c02c64840440d10104014643d5040f442102c03c91a86003252007011150140c2025000c0e400c048401d00c0e0a41c4a50300584c2100d44180d1040000d845420040b14441603014198101c11046898510017240580078000c5c020301460540b151544c80354225801d548403403000074009101345070f50002083c803629103014003620500c40c03136142010080000742560b9201d00c00380803595503480100081d6100b000860004c0c10410000e00c00307540c00c1e07000292246800280070b861592500b003241c1c115a104c00480f00a401c244121544903444c41c60220b680c1d81c8511404c403601441d180c0810020480405950704945e2540e5a207540159207541c8601a194040c14154002c11040e800a081c1c2480401451003001682e5034100c103440c001000741c0e11312005500002103504072915802011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 498422544 1250 498421294 498421307
    0x180f0e0a15060c020d1106070804230609130609150806011a0f0f04031b08010f0506030c0d0809030d1e0915110c09010603020307030f05012306120106050901031a01 72
    0x3a404039214440e01700c40d42051084840e0208509070f008400103103a50030000d141002d44240d8000740a03144541c1040900d684120007051030040c1d03c403009004440b01480d00d6900c5481142d0080008034009941d0b804840a41c0d040b1180042196990142405885010809a8014060303100108412461026020071600c56110741c903020303400000da0542166102d00480e0001d42d800612104000140020703610340386500e0003400125400c00749141004407203801064020900100605036280031201040130400800c00203c0d8480420b026180060b034050045114020381a01c8105944413030b502414941c580c050003500921080010500c0b000d40c1d1800505a140102e041198103581f25441140c41e01100303044007980200c048002180c1c41b41d041c0c02450003280c10741c41c18460707900c080c0700d01c50955400b40150b4100b01d0144454018910200c80b215059010280c241498190030031141101340070242c110a02080001920011030b5915101303c100c011070f00c810340c43c10201c503000021f254 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 498423794 1250 498422544 498422567
    0x20c0d021216020d080c010906060e0411091506070b090c030a08120612030711090921160503070507081506010c120228060b0d080a180f0e0a1506 64
    0x4021520b09104115240e10642e01e41207030f0400c3c182038841c818400305034064142034000b01c07951400c20074005131412004960b140070b59888a400a01e0b90f6618052100c81ca2000706514160180240320364400c6d10b4030b2000f4005203001e203e881419140041e5040c1c86c000d070042410380250311242503d40030030040b03801e8545030300382611511126142c1c3d400250f0900701850070b40c80c1c03d00000552004000074030701c1e00303981110261001160707039031011012500c1e000f40544035440c150000441d9202c1f241d4000043c9036000d41c042c04a40b00c150710740c0301c0303519580042404039080e17400364206000d164010889850b0002e10140c41090a16080300000c1018030754000c002c059807045044125820b0090183d40c15034070000050360b80d0708000d5203c201d80800c03600400c1e1400d526050400119080107075864203800c4d0003481040c50101d544000700da100524004010500488410210380d46180c2c4480c00d0041441c1c000400c56401c003003001d001140c01c1110041c0400301c41d0241040629080101c1c900c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 498425044 1250 498423794 498423817
    0x10b0f0d02181503090708070b0d0e0a06110706140411091512070e010f14010c082803140103230307020904050303010e01060203090303030c0f09090a020c0d0212 71
    0x1c0340c0740904030002c44050040070040c0c0c40b00b0450064021494218040c500c120001011100c015a43d10180c0751160f895010f4051040001c04c0001c8449407a81c00915101c12900101e4030303414103a44584c000c40c0d141240700f854812000940d0000d1281501030022400c848c01c1b040b007014100303550b0703000c80840028041c0c0d024008050000c3d590101c183c0d00d0144130000034080d82840d010011800c3d0704c80b0102e000312040064040000715100c090102100d0643d508956880c0c01c28508200560b0000d14460f82200c0e10032080002912201a203104184014003a906240500700c1450b4064161064144d240c1020080c40380100045400c02100d07001e5001c1445001440c4503101c1025419807040303800107500704d50300f0020301040000000046040760340150846040f82d8a850341280c0342e20134880c42e240c1c51351042c008503c0741100c1d030300245070703500d01802500d1900700c0c080007040071180205c40440545a01041c00c0e01404014001921009503510181001408600c450f649034019001e40300d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 498426294 1250 498425044 498425047
    0x3030804050a0c0312020111070507141f020c360a060b0310060e031614120f0a230613081209010c2a030f0917010e06010b0f0d02 57
    0x101071020600c00202d420360400c41c1c20b6a499160304149429208800c80d1000543c688a0300b841a030340103200f42d070310342a4400060080e462a00c5080c2c441d5103d0010b6031580401c005c0000142c0054800c000206c043d02c0d5006464807881d540104218020141090144c6000f41141000c23507541302e80c2c540704914084a0030311840c2d06ca10622900038040d40c0c00400d1103810000a0089840b501e182d140300700d1704c2e00e0b030383c0140c1901600c0c18140c8520b08a00340030340c4943e1841d41440701e141c0c018100110350b000a0710f11699480380c01006440e100300c1e80004410760300000c99080a1155480719a1854420703140350584010001e0a01a036413803000f01605a880d45101600003008603000444418480d140a03e01c2c5608015007050700030002e401c4540c000c140c0f103c000c00c05140003800d188600d00c2d20700c40c16120300c0340d55031020b540c1402c10180c40d0042042484020a50b4111802c1c0d0528190425000282c00382c4613680d15450617006801c03c2040b24418400110121807070012030b03107500652503025 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 498427544 1250 498426294 498426301
    0x50105120a1401021905090a0b040b370804020a080f0304050f0a05031515040c0c0803070908061003030801290721030b2d0d030912141c0207030308 65
    0x2c600900420550489a2001450b20094194804041c080b64030088640e003034403036503400c0f1400303c5200310b1241564084083c807a420a0220250b00d29044809000407000d540700d21580505180040340c10a80c04555084184003e609003500e6002c05001a60001d0a91840e0942c1051742e90249204030352041d03000303210000d25611927080f840c0003490050200c0d1841740d00701e8280344848a080f1100c003428540c05034040810b00d41402030164540940e286c1503203101203503d4408a90303100600b00310503c000c2080000f0b25102c00c0004510615080c89a405002c1c25468000d00222042e032001500840c1ca00301861070800700f07810f03030b0300811003c0d26050352044285800003413082d40781c0c1c0900c00c03d504401c129004a0b0950040c12000c0380c102c072151240703910001d210b070b24120000e0120000d41d25011400c212420b0104c21500f455000c0d00703004500c40d40d200341105c41c900d14100c0480b10702058025006184004115201c3c502c1000619012091004000296948814400502006400c1010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 498428794 1250 498427544 498427583
    0x161715010c050604061b020a02091519080d020c041b110f060c040302120307032001140c0a08010807061209210f0207050609090103060e011b030f050105120a 69
    0x11010403503480742c00c0ea541807805003020801170041450045004202e203000b42003080c400b01d004920198003e1120f252600e42444030410307580304d02c802070f8002c6888241a0071701d07010b1100100007005c1c80002883d6401080344020b0030701c0f0900f10303064007841c1014070b03012902080c004001c841c18001d140107403840300c00711102e42c5011402020b11105000d04000d0084142c030120041040e030f40240c8000d450545051030541d0b4a1107085030140c0011030b00d0000305649803c000f91440d14078040400440c24003c0148440c4400a0075201100d0481c1d00050100e103080c4c10940345401407195601a004407450070402410703ca041e040310401c09a5a629284200702440a4040f54501540ba840144d0040490b01030600c10400250101511602c0c2c00002c0900c0d1181c03c40320b00c588040c240c10440d92039560762743c0142c0304800880c2d5083d500d445038002e151070724044500d07444d2810358002c1052108100080100e03003040e0401b42c0188031510312007d915000003024402154028542c10301d00c8080090b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 498430044 1250 498428794 498428807
    0x204020a180602010c0e010906020606120304151d1012090f06050705030601080c0405060d02210c031501030b06030f060a05060409020717090307062102040b0316171501 74
    0xd2600c2007405040100b04940d0552002c41d41d40303041d45645040c4858840103607150107640c0b03c1c880040c0e2004000a82c9420404c10780900d04400d1411a0b0406880c0c007071101c04100240b004100186419414686d454004403d0b6900c0d030b442900c0e0422103000c16400105039603885054403804a4480a19000301300c414407068401c16008202001181450b640040c0705038000e0b0b1b80140020020780c04102c50070348110803a02181d500400c006d01d0001c0b000c1500c000381d0420040d5010065028030300050320320350850650711401e808070303400350fa07441d2906035180008170000d20181050f00e44803140c0d000e5154032003145e801a00030003540c16150348510028418a88030381101da044840442c0002d4066265005000c46510031101d46e0020320080d54081c1e2540a0744c40c2007a0b16501000d0200710f0f250003040f66440b02c0092508198414500c96103d2050b03911942c040301c0410000020803040320040b12201041c03562914003070111084010700e071100d00d00090701c1c4005020b1807482c1b82c401c580c007809 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 498431294 1250 498430044 498430067
    0xb040608180604030504090b09060a140d05010e2506050319020c0d02010515030a0c030b071710050114090127050d08040305300f160b04031202070209040204020a 71
    0x600700c860b146020701e03004110343c011f071103136107680c03070a0100d070001038a07042c28418402d03480a0704004150f0b00e056511101c0035100c5445c51340281d000311079a00460350070701445200007900d000801c00c0c100115030b0b4030080b00460001e11004858001c092281c40d900c102100d400c00641156900c440c40414100c0009100e003401c603c3c1980700c1c41c5000102c05030190091031042c21864076101881c0100424940c40f02010700008100040101090000a13541203159402500b213240010b8103540c00d408281482e00c0568031580d01d0083d2a0040010f983d001c0041480e203c20701d040c05080c5466100081d01002c25a402c02d8062190564124205102074010000610f001452004546040d0a00441680c1305010a0300d441c001e540002501e00c080030346440303685403c1c1c20404003501c1f0313266141049801082241d03a5100c001c22070b201d8160032840704650498040d100b000c0a83c20030b40b5000d01080100c031008410680144241800346e900c0c0016107a00035015280580d17129000481262441c0540c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 498432544 1250 498431294 498431341
    0x706060510020c150a08010b0c0118031718060604110f1201031b0602120309070f060519020106080a0206030406090b160f0215070309020d02090109020c010b0a0b040608 74
    0xc4610702015030005008080610664150041c0818410ba40e5141c2c800c3e02d500801190308003004014810180c8000c002000c0400000200070341450b180080404c032501043d400100c03c10001303101c040101d80e0098010303861460140c01040155003480c0c840b90020092441155218115042d100c500400c4600c100c412180c01e40d512500007042c0b0320254020300050360140030340533000c0303803015556614006035001e0ba0001c115007000310031004480c2e0300040480713a56006081000800e07248903003080001e0100c54030769540741c805045440d04625207d1040d00704580c10890b04016035540428031610311a01a111160b507942c46061240150005440062502500d1030401c0807032a0b041303401e040c48880b903a4035180c0f00942c1101c01c03680c80602c2030464151180c50004120014002d034004051a407016220291030040f42d0006500c10000f41c1c0060070705500003410000001080c410403000702c500303c0e810301100c3e080c0780444400f4042d9014800c01d115400c00403d1030315644021080c070380390b0207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 498433794 1250 498432544 498432559
    0x612030a11010b030c090c03090705030d200a030519021e01061a0918040609060903031508070b030f0705070c0b0712031e02091c0b092505040207060605 67
    0xc60402040000010564000c55181119100b480d190100c1c000b83c2c40d25000301942056117070801a4402580b014140c0455803144c01000030b5180c6041c070654a12420507110500b41d469190101498840c511400140c1030f003110f08688000780d00103060b070b4121100500900344580b9181ca0580c503180040501d40794100b0141034071000442c05400071015070b143c1d00181040d004424004400c00d0040d9000c6651201c1940450840515460b600c4e50b1700c24001d510100b400c18050311503600700c40c10f00d00c00341d0003c0c1d00c5100034114010500004401460170b18010814940390451000e82ca0102030412900424182c02144000e4441d4041c1c44403950403004c0142d9080d40d84c0710008095026840840b91101c0381441460340318064400c840d0380c00380d8a42c211b103003845c1e10013196000b9400300310b401d0351001004a91190a880b0010400c5a01c2c1c80342544036414180f04002515201921484a42c9118150805203550141003030b12030031540103403005611509240b0340400035105540126070050726 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 498435044 1250 498433794 498433807
    0x105040306050f0702010e160303030903170a090c060c02090a09020a080706110d030509100510120f0501060e0606040611070308030c0a090503031303110a090c08070201141608061203 80
    0x1000c25154000c4c00c468000b0040c54071022030f541c0e22060700240c3c40b900e035490404c040020901036009142014820301c3c03d12640d03229580a10304942e0141c583c48501650f83c0111405c121140d0f0511001c0c02003400c0039014a40e40c1da002a0541034028030103400561a044030a045440d9030202102030040c20742515203154442000518013400c00050071a944a415404510f0901038400c85000b88001c01c05009141103803150003014040241c0116064403107100e000441c085842a440c2810348101c600c0c2c4500401801c1003030950b01d00d80c00c240d005141500500807156522005c9404a402a00300041c00c03c44101e070b01d601340701a541c4040d10448000041195010011000b000d100ca425103403042c1d81a00c91080c141e0b2405142290a21050075003818400720b80485aa0803880c20020715003242e00740c60f4480c43c01a110f8005101e0007080841c010b0103403c41d020300504000c6621030320801401d26000c0c06411511132516042030600c01b820010071103035101c21608811910b40d6408072691903c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 498436294 1250 498435044 498435061
    0x50f090a1205150c0703110c0406081f020a090509090f12030402010305071403011e0519030210082205100e0601050a050a0e07140408011a040b030109050d030b010504030605 76
    0x80300d078800322454054020603c00c0030480e90001800745201115545c103210342c0d580d05a90106c90710340031805034499002c42c0c03401075845010700d901500119018140503042010058030808048103480711a60044c81030b00601e40e8844002e00072604e04071a000300c5c0e44c481030552400c0c82c41548555069024080c020718500003100b0046005520070f90303080100b0781c0c44200461b83d04403a008001e8020030200700400c04001407080301c1c04900313900b082030107040380d03100001a42c1d4104103402c40b13603c4000250400543ca801152a101d0b01c2841c00d080c501481c11400c245014004582c0c0014180800030b01501849800c1140c02400d21400c10100000d2118042207a43d5150034807805114100c821404600d40c203003149068102c45103403c0c2130701c490322a8401501c07806039400502c0c10340c0c0810700c000901c541e800d020f03c0c0001141d950094040a10107410710003900c00081c9414001c0c0c2c10081d0002c00150002001c1048190514000840350214401291503220300c1c1c1c8085c100c0360601080c050000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 498437544 1250 498436294 498436319
    0x308040209060d05060402040b0f09091501151211070204020c061602010207030e0f01020a0f0605190207050303060f04060510120b010c0201080103080c010212090607020c040e0a03050f090a 83
    0x150300032a18544070350365100c01c0003180520700800910702d40100300032900504142c2c00003648040001c040c1c012400001d008114aa10100e0b0144c0580d0310628000800041c40107140703015201d058055140380307088040c0584900d08100c14100403c0e038401800b0406180081a07480d12640240150340d02c4200442d02c07039840703d00b138900e80d1010392038001003a0351728014401c54134995856200c0c942c814449104000754103203490350545c1580258134034600002e00b0400e1008036103216070400030340c80c01c011041e040901d18801d03045040c54410030001300420700000a43e035002d0022100484200ca01502160240045074009500a4505282c829166800440d800c0c0b0322039048034100042803040c001180c888120960107800b00340c0c02c000502c042080c0000502c01c40d0445070002d80380800c4030703d1404e000d610031100909203801042c140105941e0500c1004c2071240308075024040582d022a4035a100ca4201600405000c2c2c009407005d007500c3c0490a40780b04007002006108080d60b20030104480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 498438794 1250 498437544 498437551
    0x8270d2409230c0d390504200a020303090705010e091801110a02010c03140c09060c0f03071a0f0f0a020a090506042606040f0f05033901060b0a03090813030308 70
    0x1030317210918959041502c9074171840e1170602d1095a00136894544414030004042c840815424140102c0748510011700d8030008250b91100399000310780e00d2070080c00700c03030a01c903154101c0c40c100400c0e1882da00c1603907113282e011b0340c01001407203030700c2c40030031030aa03000e40107105840b0b0000c150800460b107001d0181d010340c40980004119142405800401515003650f88011106440e8400040c0700709442401d111014103407098911040703580007103c43c2412841c5412400d022645641500180c0902e0700211000c1500448a070034042807600300910100d03841c0c940140302c4642e260380403460502803441014541d0007080c1c0603203040e07951394407440712010003900c3da114810f500c03c5408140340c0c80350001400f60f00c556044200c41c0007000841e03940d0318074040044020784103844240003092005503452a02680e55001d01c4451407840c59000184014070841070711400640d140c00c02c1000005200d0301124048440c80c0750008840000740f03421441d900032072298480340006c0c030310003104154018141070300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 498440044 1250 498438794 498438833
    0xa12180b130927030203130e01031502030f0105040c090b0f040801051e04080a030f022a0304081b0103060e090a05070f0308270d2409230c0d 62
    0xd0803602d400000c2e0942d0f2105080400c0e0005005000e042c48966030341256410b4400d00c140c900e401c8980e080000c401a40ba00000035102c0070388010404c00902d5032070510000e44c00d22040d8110325003851030b0713403940005128580c0600d480703110201036180324651880c05420340c8141d95885040341c005a80c0203410500414030782d580307410040799104203003085940c815410044000d40d907540d81d581c0c642d010340140b081c24050540307441d0a1185e03030000e80041d182c095400c4000ca0742d0402607030016140c4451a032441d00c0950400c1009101e8000702181040c078640480c000718540390380c3d4500480041120381c0c460100c10745c480040c40154031010880c6003015024004460400751a0380901042242a10008040302020020700d213224000320031810f0a045e1680d1121070703035003161020881c07582c0c10038005c48010180c10902480c076502c0310709003101b0049840c0200401d0071207038bc644e4095401c0c610340310711091018040404040082111108564028181410b540c10901e40313a0021003d41c020001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 498441294 1250 498440044 498440077
    0x41d090607020c030a030f180902090406061e081b0705060f011a0417010e010606050904060e1006140403020301110c10113c0c060702010903020a12180b 67
    0x1c407001d1000940407a140c2008000c1e181c2c131211944d0a455428050b9407032000d2003818103400c40001d2105e03c1e1b0303200904820b400580c0e25816402041b00315150340d007002c018404500349031140c00328007101d08900404942405090744e240d40a001c0402c20426400c8113104400181c4171042000105090340500494040340f80c940e602c51050004902c403619800c001c6103028402001410703120f001d601e041107003030000040e00045144240c1c0c01c1d2070031078110f000464000036601e41d980c2054030801e0b0017440681c0060300f0500b81101080002e00180c41481d041049002c1c01901c010000300440c3c00550b801002005407082c202098a01901305410040aa010381191200c445160303000d0101f469100025080c80d120580d050604002c41810107112001c001d500c3c1050a07080304600714a12107000100a600d841c03040d21100d02c0c0203002801c84d800c41e414407040c20002500046c445102d0b03a8002c520748107003003800508503031040f02903090f1002d030300241d140060109094801041040c4d410003012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 498442544 1250 498441294 498441301
    0x5120108070f0b16120c0b0f070e01030204030803070e0117091b0d02030c10092607081501030303020f09030307060b0a060e03060109020c1203100602060a050c07120203041d0906 78
    0x8002c6003d610120540d13165001911070010300010502981000780b030800705043c2025883c0c0c0841108220b489808100d50081440314441d040041005c03a682d00346020761900e803c0d45e464403d640006404401400308148441015030300400d91403400084002a180e014540102c096030f88144014400c40c43c840a2050340080741400c00c0c4c00e080f419005002809078000c0441802800c00740c8082d942e00b0040c07000703008101d0701425260311455085800d0300300410858401001c0c1890002d60040344542d001001c402080c0c0b00000181d81100d405003001a15401ca0307070500c800610440d03000c42e40c58003001644408011242d40015040c14003603a44403441c40c0c89040680b0041100c0c085039138182e0009004101d50042ca800030301050f5024801d9499074542901280700c1d0303030030a48008130644e2208505014850b4100314150303119903210340910182c2000e00c1018024460064040c00c01062300541c0c181c0c59008208950007407a41c01d10111140c103010110400d200750076202c004060080c0c4020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 498443794 1250 498442544 498442559
    0x10902010e010c0818010513080a110111060a020f090622090608031e040806010b04150924172403010212060603071107030b07180303020304120305120108070f 70
    0xf0303120303090703002d03800e02d10305140511074041c014100021903040010401103070030240042d1100d80024132003000101030010542c54a1050f43c107040c0c85c580e0410000700d1000c2528240000d065410503036822006980e4410900c00c281a44902251190011000070301000c402c002e400070310507840c0f0b0b071826800c040d80d100c009800598259101d180e0080d0b01c01d100800e240c0d48841030002a0514048040e031170203a46262090524809034090101e01e0350125040004890519404044403803925007034071024200300b88446010030b02d80081c0001441176650003086406540c2c14078426942140d900d00503e824000c0d199640e0081c10301012030000d4920f2683c83d407c050007034501c84020f00c0d000d00700c0ca40d10402403102a40004003142c0800414960391440050103012600c051030050803038042520306800f01910250410129150b203140d0720b4010030200e940402900c0c10750703800c0058509100b00b079041c11200c601a040000c3c08000000e800000c00020018170481102c4481900026150740d0b82c50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 498445044 1250 498443794 498443807
    0x5060114011b0b07050a03020c060103080405100201060302011704081308030904180b07030216140a030e100819020f0c010e060610080f0717190b1009180b12010902010e01 75
    0x200500d0f662180d0045840c0c0c0340101c2c09808a01031510f0014240781d844401280350190a03403094441d034034001000c1c81103080c05044484001c086000034440702d07280d980028041c0503031b205a0300b52003180310041001c0000d00700c02c0360040340c9030342400b00006885150458403540045a03451180d0f1400c2d04901c00c083d904a0f01c0c001c00354200c4585d0b43c150b81c1d4500150041d51118245d00c1021010031003281c0040c0c1c201c0b03280696600c0301c1e0b0041c03c1141051501801107501c124003070b44100907c50a4070420b80e80080c0e0241d020006e100e60719805074141c1170700c8010740a442042c48501c40d0100c0c5d00d00400030154000c16a50f8804000c0303c02c5a240c0390140552292800415400103048d04001075102019402254000303096280118581d520351500900000c0c0580710600c217019041c0e2409002e484a018a8000c440201c440c5c6030036111584025104124a2054024030452194011450701c15075000640100b005008010342090300c0b98040d00808003200300301d0210340c1a844003061544501e6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 498446294 1250 498445044 498445097
    0x6010e0a0815130f03050301060e0f1e0102010b270a06080601091a04020a0810090c1b050f03031006081015030b0411190221070f08070506011401 64
    0x2405440d480058030501180102e00a002c5240d410020b1a000c000070304910751408124001e80d0351076100e504140000380010040030060b407151003048004115507980260b062461322440d2110002c90a00c44e005034050402d421285030f108084004101c24a50280b03070801c042240100c1408856607030144207422150030b8041c6170101d50140d4018000915168803800d15042d000d803c20042c0310203240002c01740d9020302c20500002e00e509080c05441401111402d0141c05069414000651140802045801c0d811550141c408140f11030809110341808148490240c007416243d8038076107054034240001451148000144145001a1100c2000741020b0103498160501c40035003441002c00700c0142403640e0340554041c0d03660103161145546007000b0100300d80c0d0440c008001e0310300200c01034206151040e595071540300304841a0300321101c0408950850b58802500c0b0310090303082c1000e104601074418020080d10074040082944011300320f6100098000f661008481e8003000300700403505000c503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 498447544 1250 498446294 498446309
    0xc09091e03040f170c011425080307020a1b03050d03020f130f15030605060906070c0305010903080a0518070e0702190803100501080f060d02010309020607060506010e0a 74
    0xc0403088204621006414108940808803030a282d1105040b000882c4a6400010030040054203802e4503081448164081402400c05002d24a0607101d91a403506c00c46034010b009080c411b080d450410343e00c4050840310754000e000c1944900d07090101940d40c030b0b1401000d944500720703400c81040b00c0c000c84c400403007a241e0010262001c5902c06000360007a41041d1212001d03182d040c440340c5080400100d91a00600e007009030001032524042c8503407203d40c0720800c0c0340205414560180900e44585048036201c900540f642c950b071b01d01605090712000c90075000103156500305941c5c24181980901d65074080c1411100400240d21924408030000c2089100308045800c080740c100072004100300310036408044d0b40151070b80c0301210788400c44080c1c070550044900d46008024081081c1e291040c0c00e019203000e0810720441c5c1800704019480ba440144090310030260886031a045902c41d0300116500c03039003d41f6031901c9181d9450140041c1c407080340c032640003ca000c040c1c05828a460b400c07500848107034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 498448794 1250 498447544 498447553
    0x103060f080d051336150b0a110d0504180204050d1104110a0507050106052d040906051612021c09110303071505100e01090504020109080610080c0909 66
    0xb201c1c05898581181d80c0e01c15180006000010301001d41a0701c1340c501107600484002c0f0004805c10350103030511401c402080c11880c1100580607041d025083c0d0050303500b4004241d894511040e01110f030625a002c04500500429104003400c1d9005009002540e9501c0100318030740c04e02000c01c038101d01a609c20355038000b04000384000414447c40180030610000341001c07440800c40710800c100d03a03101546410010340002041410300a0a10504018184c00c0b21754400546802c5104140340c01105e5482000614613084034480d942c81d544407014050340f04406000394034000340c245071415510756210300441c0281c1507500040c4468400c540c2400030035106003410f1541d964140c2e00900c48600200e9880c1d654035812041680d003000903100c11407041102082948084e0f0b409025110040c0c0380c07604015155405010b2404c90b881480d0655682c044009115a9580012140b01c0007540c0000340e103001e80004e00c02019011400300c002d0f942c8c0c0500b1181031170303143e1003403044000303040703802540c00d401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 498450044 1250 498448794 498448813
    0x304080304150e0f16140f221a100c03270503010906090c14060d02090102101b020d080405030307141c0507090e0f0c2203050106050103060f08 63
    0x188a180c80b26800a840e00055140c50402da01c1d4a04444401194180d5210b80c0520340b40b0003501c800e25000e403203d8800001a503441d50086440c2032050301030071723100d044810503001502c9508240d5092850701407109001103050b80c4810f16204846481c042c2c010b05c0001c00e40781c0c00c01e020f0300c040d480e41c5e645079071200003898954401d140b0780383c140080c8401440e54801c0c0016070360350074002d00b45440d00844c4002080c00f02c601d8405d119103510780c0951944ea070003182181250f40c034031060f82c450403400c04015035a04000340c0100e04050600e20f1000020380340496051581d17012680d030b60401c040a030201d1b800360040d0f000564240030b045038010305130350041000506051180403075070401440c00c2d444c242401403550100354507210040c40c00301490b83c0d44040050403a485078905005050b03501c1820f8803802c1440f0543c0c00c848004141100e0001e001030130b5012002e8035596481d80d80d24000b040c1485a84030700c2c00d140605810720034640040d00707111021915076140c010380011119001d004058180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 498451294 1250 498450044 498450053
    0x303090e0a021315121d0613030c061a120d1101020418020903032a19030c020405060109090914010c05090306010e07030b0409032d02150402030f0d051b01020304080304 74
    0x400c0c0382103804c209841d411806074020750701422005c12201d400b104103c560400446c3d18041000f084115400c610011120210b0741009035986100d801c41000704400001000017078060408154047d0030181d4201400100b10010940000310300040d9514142101084c1c0c007030b4241e0099005140800308c11170007005803142e441d4014121110003409990070000c45000031884605040140c46801da41445803181000c4107100b64416880d413841c990050b800141c6005111600e0030b0740080c01290703208082001a800b6100040040158120921045540341303004440d888056800d1000380d0300b02101e241505c0d01641c10b5400521780940200416841d02e45036071410103010740103100b4503940d00700c001e4482e20f132406200d0365280207444005002a00d802a50203030124518803626000b068030601d001c580d0701062a101041180050001c240c0715800002d0070081c8419400440c1d10540202d0030010b5007000140820003000c500c0300c081e0000190940d400d0344400c481c0240f014008100240005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 498452544 1250 498451294 498451319
    0x3060f03060c040902070c090903180b040f030b090a0206181c020108071202070206070b01060e0109080c2b0b04020a0605180105070609060e030409060f030f0b0405030d060303090e0a0213 82
    0x54024012000d4442e650850b40d003c4409c444010350003e91010307036030030000c51030269420040c02d4002d883d03407502e45841c01d40b00305542540801410070054030f0100d401c0805c20400c2818003138000380318650340c0c1c094528051034220040394a901036864450038425940d5261038104007a5010b031a400613940d03541c0c00855102c00f006c41c98010265080c800000540c0f2200050000c191180c01a5030b0380d9410890043c2c542200e110790281008031000c000c1c05010008540480306030006d8444003906e43c07000703800049924291082c0c0908461400911090244085455004500985810440c43d13212603046031644a003060450750b10740c00c541d840310b1f44c0d442003000708001d80c003d410000781411641e0b02c241c02e491141d5a40c113042da10200302070100c06050700c00c6000501c49540c0d150880d034039503a210415004030980140881841c5c43c00501444070900480f0000ca218000130480541c8925001d41081800e0007008810001040083d915001e01d2088401c034500602e0520f12240c5072000d141e058 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 498453794 1250 498452544 498452557
    0x506040b070c080d02180405060109030b0c0d0f020a1b03091a0d021210050102010b030c0f010905091006030c03020c1f0e0f060114012a0f0b0c03060f03060c040902 72
    0x40040d0312041c0b0000c582d4940180c00340c40c0c0c409a0140c1d55050014085810114100145114502d0141401000d80e0006041e0040700d42c04403e808150b500c0c403d50002602030400c564060609103400103214950381d074020000c41c1d42c40d40f6428100415280208407100e807419009001c00d040d010244141d402000c4030004454642402a03d040490201201030781c0140707d0f0011700c4500c1c2c0e4144285006208ca1640141c10288002c0002005501c00030359541c00b0880b081d8011002900204443c0e4402c4654502030070340038200300341d0350030210300e0810010aa40319a90020389441c4503151418400c1c0221003004492000601805603a8001039884162181c0e81c0f004840d50380c210942241d50a00103c130341c20502e9405010150300d0115a03115140c080b118090421441180d201e40d110204800c42c240c013200500c4805070703210540b0380000c0002d10808090502542d01c0e04025000070741100844c0b00310010342d1281c4042e40300b0b030300341039a4240c20395412918500a000c1413200ba00580d000c1d020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 498455044 1250 498453794 498453797
    0xd18020d0b090a02060a02010b03251a041a0421020901180902040e0d020f0f07180906290a05010e010f0306031202160e01050108062e0e03010e0102070506040b07 71
    0xb94400d144e0000d00ba44e8480e10700540545d44400e820499807505000350040e80c14030f007907440001004840c406c8a017a550b401000714904400541600f00000700043d44d0140201c2e0005174020444d40401008a03001442403ca14012408100310340b100b503592a01d02c52a07024006561590030080310580c413040e003070460003070596a918102c000d69217500642540800c15000b401000740002d1009003052201c50501c1c0c03240e402034100051601c0005495000c40c6e030448010700001103c0c510207006405503980107042142010355030701c01d81c140051550b4820071100b0084510841071028040e2080c1c0700d00c24107011491081500035154004c201c800c2c2c00c1503840c60000b9a040c0c499407050040c4244494020050388403280030540407000410707980103030030320300c0701c0c200d0301d40c54200001c0141100401450203119003c101900c40c40c04821041205610300505142481c1602c0005010810743e090751032189d0300b0700104554024040c0700b15000541c11001500d4117542d00e8540e5440c0440c007400310350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 498456294 1250 498455044 498455053
    0x10f060207030f08122a03040807030c0f050706090906050f030d03240305151f12080708030f091c120237020c0913020904060e030c01020d18020d0b09 66
    0x11141d07289024248202400d02d02c0711011043c2c0b0725520041b401140e00c0826104041041c44080342050058401043d03051422412040d41c1c0d18004d044105c10150040030342c80340510105600382c01069100686c1e06900040020aaa410401540600341d1903c01e405801c200911100700d4481d4109030010350300032031940e240104544624a450303807070307500642d00c60300004030824410b40358071040e58000e2a018070034041030f02d41d0f111030854220301e440b80003400d480002a130010000c0c0e0038140c0d403181382c001c00c010b9100d2501c10088a00c3d802d04591819981c050050041d00320011044a038005500a030382d80a80f03a810000000d000354400021040148220300450400714940030402d007481344d40900701700708015072620180c039042e00c0c40003452003010204d0401002d03035940c0c041200301d15011115210305441e1070924a004101c032186400150200040d807a040740300540080c02440c01d0420200100301e040d810070b21616811083c02984402d402100358082042045c0154000d5801010358 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 498457544 1250 498456294 498456307
    0xe06071709061b060c040f060e03010f0603061d0d05040902070204022203061404120305040c08160303081602030a0f021f1a0a0b030a150803030a020c06010f060207030f08 75
    0x82c0b40c54000c003041e02544108010741c001002ca05001141d04038400c1e05109041c40d0504d44a030180c05140d00454007002010101c00c0f000350380940042d40305a031141404c0114540380e00303080024008031401d501c02c46070189141c41e070803000040c90030a05022661094141030900020001960023500e0699000d42c092000b03200014038051040c0d90700521000031400d4500d146080001d99140e4401407080281c7e420400021412050183c01e04907000d1a0009459540c0d01d01201d0341c1d0030542045442d4441d074400c00b0f081b01c500b044c0400c243c80c000c3d1a07000d40c039a61800c8005803131100051100050300180483c040b80d80c010945101c101c81c8500580d0031900181400f188090b01c40b030020300c1e040392a040044147d00240f0100a402c1905032111011107080c04a0740c4400d1001911074807100303a444818501610704120307100d01500586048e6980d9041c8188043d01a40148080c1d880c2030084500001e101e040e001110801c8680d2900a400c2c0f140c0387d6214560f200d980301000755000d44081044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 498458794 1250 498457544 498457549
    0xc050c04050702070609150c112103091201061a03180d0e01120203040b010608100b0c100c1112030a06090c03060611151902041e05100e06071709 64
    0x401e8441e40c5203034001d0580c40d00d4407100400c520701e280e01103130507010001525070701950700c06401d07109203400400d0480040c3c88180442d010904a4a078000400705483d40101e07420310101c010b02d14820110b510b4500c207440c14641d10300300c81a600c10901010380304c4078281129840c05001e1580600f40c3c2481c00303400c40f10141d43c0350030242c680c0040c2c070008000c0d035540e035482e6030040a9412200c80c1c01d00d0450441c5416a9954240041030054105029032003001030603090200741885d003c0c0004201c1c13161102a1006250354425100408040300c6040034800c2c8400341c0306441d00740c01044880010031201c06000c01d41001640050700740b105c0503460b684081078482150054a00d1400e1703d65001840300d1801c3c40c002d1090390114559051a00030450059000098036038a03074001c10808000c03680303140c204910300000d108982c0b206a201198030342d480c802040002018046407019070b00c0f401b100c1c0880008484841103004450342c003c0701401800c010959003905641c1c40e030390310744180303180c0441d01c0c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 498460044 1250 498458794 498458801
    0x110709090524010303080a05040b3c01030c09110307050306011713030f141c091a04050625270b07060e010c02030406050c03160b0105010806010806010f0c050c04 71
    0x3505402c9081c2c0d100100308044d417010072a40c2c0302d0082c007400c00450400380c3e100034181002038010703207095000030f035444603400c5030300800140079079a040d200c0001606104003884c2e91409210641c2d612158403000100040140101f400b00c1d08860303411865940e0310345050f90300350000f03481c060412081b03a8510703611f02d5079580124040c08503603507800380c0d0392000e10300108030400c040d8809003003200742d138095401c82c042c074020b03900303c0c544a47c100d23080c9150011640c0010f240340d40010302541560b008500e061a454001140294001d40686007160b8501071520161048550740300b10b180d446a50060702c042c8101080003941e1244a032034184240d00d080c030110004100c0e0030541c0c11990014209080000320b00c01c2441d41d0380f1290003444149082c034406500d0380114451542800300000751030344580c1c800e00c1200c0b69111141021140301d00c1c00d08101c15010405d000b65408685004041801d642c09502c00c1c900c40c0768141e440641603a1003200c21681705400b80b0007110306120342581019655504d02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 498461294 1250 498460044 498460093
    0xb090403050301080c0d0201090612020d021201180203060319060b130c02010b010905030709230a0902040c020615132309120715200d090b071107090905 67
    0x1d841584a504000f4a00c0c10020001d40703252161980211141c0142d0300050400119142802d006820040c03a64443c0040d01c1441c0d109520303188000790341e9a1007480900102c1c181c61040c03003100641c089141001d8100c0c441a10b030a54164441e18682e868068480c4d11080d03014410540802c0400e881d4006c68400c2041101450711107456900640d07890358248124000c9070000d203012020b00d490318011a0315070000c0d00500318241e40f42c8000d00b442d070f0003920004814009141c0745800358907003401c0100040c004802c04130311890900310008005407001802d81d0090380c21400d1a1009041d04040001900c461010310b03100075100d464030506586007009003c4600b100c0800e1038400d01c4d04407003031818000c4210403034500301c406003d1480802c0740c0c0d035007803240c641c441740001900344200c850052880300039211201c501100010b421204e80310035040845024441d4008151f0354483c0d40301521000304000f80808107902031071040101d901c2a40103106a140500183c60408401420301900001680c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 498462544 1250 498461294 498461297
    0x2030f070311060f370525020d14042301110307030509090702010903142203080a0206060108190f0b1503010e060f0a030605060112020417070f0b0a050a030b090403 72
    0x8200058a040c0c40ca55010302d82280d0034411001c01210725080103211105800d01c40c01b550b403000145c1d01e00c000350307025079041d0038025480b00742240c80000a6841a8400c81580020b240b170100f000f820316a2070903102640c032111414010034803000e212200c4a202050031070b0400030405415104900d0600003402980d010342e459942d2007030b001b801e101210502400c41c90843e850045540080b9a0010120601d9064055001c6d80c981c0c480188107004e0307030514481050102490f000004011801000341003403800c2c1d1f0203035003040e5502c40065460310300c21242541d004c40700002200e4844100d0380440f600b40071890001412100b2800818800d1a8022510303420200010052000382124248950f015000b1213074041004440c00224808294502c00180300c180c89401143c9581e028442c2034166000f80b00e0308546903507031209146912409080a240c041c01a070a002c0b81c2c003940e1040c002c05440c9140100d529044d1414411a000da1150401008066682030081031b0780d910350b091240114000e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 498463794 1250 498462544 498462571
    0x90b03010f03020f0307050307051c0b011706090114072102031509010801020412171204080d060602070b0703080907180b010f110705040f090632010602030f07031106 73
    0x2c41c81030020131140c10f1184c070720980c405032040105940004180042e901d050312450601c2d40c901f10000103440c403403c03004000701460380001c00c032106002036801c0354107180c0040343d0503601c4c3da503502801c0700c0e01480f4004401d50104009680c80c1e000d2680c84000940d0034203116649460781020b103040b41c0040c1c8000c1c2c40c881d4403032002300841c40c01144249c05809094021840d0901c2c0040f40301803030000c1c2100070504005d03080804417582043d000c0d58050b203400016410586400d24001c03030240d000740070080d083c0380740135804500684005124001c2d9428400d100c0d14040307850f103080d500c240000380140c40b18800d0800208000038900e280c100c03000d000301c002003802c6190a00160000208031072400c204407020301d01c02c840f0f2800140c29001c4580c16078000038031880b20341000015291000002d080182843e02409403075440e20303803c1460f0982d44210302d410203046102002d14450a21801d0010b0707000380a0f09503c0c90351030340207040051081c1005075a00510700030b5075050400071204004101c49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 498465044 1250 498463794 498463799
    0x90a03050a1b06080f060d0804120c03050105130b0c07020a030c09020d0f020a0c030f0e0d2105070c091e06090e010b01020c24070204020c21090904030c03090b03010f 73
    0x351080c10b01c080c01141c03d201c55203180680342000c5590000b8080e034814a46090f035182406440310440b0003400020f0000303801040c4504180d4040900340c03104607999031038180050040c0001003800050303a40d10140c500c44030b4651031014001e030b07000100c090b60311528141c2d0004c0080c1015840c000200400d00e0090b0711540d9140480080700e852075511040f607401003000d011203503031050590340203c6d03050408115010801d882255404040e1089503006540d10304004203004c00600203030725507250941341090b503500341c91040300c19000d03000703004009051a680134098440c89400c82c1840c4001c090301400c0030303856140d0036010317111541d1000b0807291782c07401c070800c2c0b080c0b01303010342e81c01038000380010a150301060010035111070401100603000c1005d000c0385c5411400c02e00481c1c005640051055448641c0c107000d907601c800a995250f034613250380e40303945802c0d10410303800da0f144814010110101399503252800e6406c3e0f40125811400c001c5843e2021481c01d0241d4040e6021b040d003000c2605d011030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 498466294 1250 498465044 498465083
    0x40b0405010f0902010c230303010b0717121603020c100e061e070311040305010c030b0102060a050108030d0902030a020a090e0c120c010c0c120605070306050d03080c090a03050a 78
    0x440c1d0100300e4010b14100410b00d00940d801c40c40542d1229813250742d103400d103010076070004140e01c4072184000e5113000c0000000f61503140200600349041c0110103a4070f40b40da422120115600c00d255410b04078401c05e800260540b002c15289000468040c2030141c6000c801030790460526051025480540703655041c01c05040b0b408003c0a42c0c04005480307500802c1400c0c500340040014001c000c80200b40d103500525119410090943d001564000000d12408c25460070240c040c1c14560f80c9213006104e4a000550350082e5401400d04a0300300b80043c40c585a034030444d85000c0d00343e451041e60075100e034201c1074006031243c1c001d81005044420001503003115618145003008400b04e511840b6504000d00810701800118607441c1e1a00242001401011585801c0c102c000c119480240c0043c40074150074140722254000d184281c6203645e08010044d110b8003044000745038014040c00040311100020490556040201444040140500a81956907590314030740301203201e0071103e40034041010048c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 498467544 1250 498466294 498466301
    0xc0513180606020c0f0f0a051504240c021c02090a060305060601020d0e19120506070e01110d030c0306080f070305010b03030324040207081207090504021602040e0c0603040b040501 79
    0x10402c910140a100e00d6040c005280798880b80703001c501c51110a00300c1c40c00caa642d00c0d0f56900501c3c1c00f03031800c2400c1c00241c4000c03425401c14421010b0f002c0441414291104021442c10055035140d105d41c0d80001143d000d002a00381c040e58080b943c2e4094642c81c1d401750b03890001c11481503c840d04041071250440c42d295040c860007404140c103651140149500503a0041100c02c448170064480048107220040040d520b414a40d022070103005081c02d019090000220b56588901c040d070720341c00b11100c0305100441e0000c150a80080d540e8102e09554a48a4030070f4120000c5100140360100b03406131030782401814150224040c0070386500201c0d08000b045000c1c0610180f8002c128080c2d0308610b031103229a40221500b202d004c84400003161145843e984680c140c4a1140e04040b0302c83d210450305c240000121401da8201e400b0590110000642c0d10385402251060f4240a0507000501010f0b400e0101800c188040e140043c083d0404104094581401562140c5e01920070342c007982c20903041a6084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 498468794 1250 498467544 498467549
    0xd031104060e0f13050403020f0c09070906120b0a1217030603030f071b092304051b010c050604050d1b080405060f07050708031c0506130c05131806 65
    0x1942003030004214103034112a40c16122142070350403141e58804075002501c0b607906402d240d04824034007024002810b6001604005c055500011100300c0f604110402202c3e9904560090016809000502c1154170500e074604218a1010b00495034601242c0050114030045d00202c44400020b26040305010300440b2504291203541403103442c50428001198803886940c3d8011790354400002c1240421210b038114200340150f114010600c0c3e034681c01458058510140030f10402c44040d0100a0301c1e180b90500280640d46c000700500705441044074601c80c092104082506101721036081201041c1c040c0501da01c40c40c460405084007480303400340a001c18004110b000c00b0386255105c0100003d1010045500f600c01c1100d8058450300800d00d0f1011620039200000d00714000d02a0002c4d030360100001410000307002038094581510321030414400c1b55801c450166000464030007070741522a8642c0304140d000c8880c0b400524042c0003064070100307064203a101c0c0c01c0c21403040b600c042d403442442c42034001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 498470044 1250 498468794 498468821
    0x2301032108090c0409050a08040902030a050601081005012115050109060f170c0702040e070303120c1d0a08070e0a181a190e061f030302060103031805120d03 69
    0x40c0c103164042e43d5480d1081c0d9503581c011541d0302d8a0300244070040044001443c0d00c80402031b03a8a0320340940101941007580c840c4c280c1402c10022800300d60040800a100d40c10f040303804890640b0b80700045581c0c0000101c042036142c0403c8900440491b40d0044c5682c080d0600c0642c640540f80200040048140707500c250204030b00318400f41841a800008030080740d03040c0206140c02e4603821400381231032065120003907001e4608254070810300070110382c02e002c40303000307440f501018080e14000c0c405035075240700250000307001c000d101610f0556103044282441d1028045200850f219001185010100d8110416092000041000d107160500a605422050448002510595554201e02c0c81040554060800040700006800047d203114132152110700b00d40a000311414500c030319440d014140c030740440a01ca401052586040d9400c080c2e0203c903415801047e2503031035a1011615240d009070201d00072a9841d40010f41580c4400d020350440022a001d840d13120300e10b000160454558051019 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 498471294 1250 498470044 498470057
    0x1605030301170a0314030a11120603060703050603150a0e031315050f040501050a0c05070603020403030801140109030308070324060314060915030109080d090b072123010321 76
    0x30f0020780d10103204410000440503003600c07034a8070f42ca40d0000d0b105c024000c42a180300800d0079058942c9900d0a10f010b1714040d000e90341d4544a020040342551070171035440d600741d800456110103410722160031690025051000286180c1c644600c81d06550254003044000140020140f040b68061075514000c0902410007a2800112000c9601d082c05144665414002e001c41c03400322150041020302c104550101c161455603407074081c044d009401502043e000104001c0000c11000c2844040804200c816115400a9840c603601162034020050480003015180c880125000948aa020040c1c026210034038151908092009040342c82040c0405040079140b403d00501d92160006030340c0110321441052500103030080480c0c090035001030014141d0030002202d694405c0c6940c04084042c2c4200007591090304c0b2284200c5020ac0c003920501a8803c440a81310b51a00301c039071103240080410b0501405550041c0050800d045099000752080d8002c40e170326450100c90101246a8407505042c0031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 498472544 1250 498471294 498471313
    0x1407081e0a110102270303070b0103080301080709060e04020f0d080304030507110d02010e09062103071b080c13141819081b01061503020a0206061c02090a02160503030117 75
    0x301401c480034040400c01041d0941c280b2051b44003070040b00d40c00c0d82c1180107030f80c103540c2da841c0031821a4424403c0280705e0181000105001455000b004100c0d0b00001c803010b540d444c3d907002c00403111070f8203d00c16400480c051400000508180c00756100d0b03402038450944808660038100c07002c0e03400d403440510440c0704903401c40061ba001078620121800c01d54031084281e41e5407001c01d548007803c2121440883c02c5080f04800088000000d107200b03031003a001c6928049000c11040400c200e07601900105400c04841d025141c10085c10b213038880740c00c0038000703e1984900c1440d0401c02405036540380240c0415044001010343c100300f00c00c10440341c0c002200e00d1404903100c10b6420b00501c80c2008802c41c0204090401c410250041e0700a41030440d00ca43d01d047c1c200c1d0000c1e009510092030344025015400004155107880b40d240300c030b03600110b500720801103001d50801c000590014000c1450a909002c1014441d01078251500741c1440b420046a481d410030b142c41c0040e401c1500c070010301e80d0140014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 498473794 1250 498472544 498472567
    0x3080d06081c030b09092a0a140f040203090d03050408070b040807060608030c070b0c030d0e060f0f07211e02070605131703040f0807080403030305090d1407081e0a110102 75
    0x4c8181540c6080100c400c003400101e070b00105401c0103010550302041c500c4022480089d01c00c0b034400e2484046509240c40c000c45c0d014041a4041281e000401c1d40112800362400c070f0190304402d41c4a4816190546401e59175030b00c00400ea04250b07015912604082250f808000180c400d06010301b140500860a15840b240b086681d0380581c050080270203800304902e0151007080050740e0592480560500c011404803072126a259800c445102d10803501101107026014009005d0340a00760704d6843c810255000300d4208c0b0854030700f82141e140d0542c0c2e0f04140d0030132400c1c10390401002004540141e550802d03410315400f80c410107003c1c0c410a40a58144000055510700880100c4013001c44494070b07603031682080c0307070048204480603051202c0010013104120540c401041968441c3d00c04004d903481d04c80c00d00780d80da54085103042c04910b61003608045622041c3c041c054891051050b685000e06107010090001904040080b05042c0400c03188042a0020009101c01c1e035900000c41c03e10328407055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 498475044 1250 498473794 498473803
    0xc0b030a05100b09041806020408010504021c0302070b0f070b010e010f0e0906041e0803090c0a081b01230c01091a04030504051026040501061e03080d06081c030b0909 73
    0x43e2148255a1680d2500c1074220fa150208031b044e400c00811500c460743c52001794040d0000712000c9105110395604a09180d61341c810505e001501343c0d00401145003001d541e1441c40e804801c8039608044180007400002e00c2d241c0d4207502810554030180c807154540081d00a50300c0181d04110796594184007000707c010000160306038800d0300002800202881140c0c2e29401340c085c4240030707200b6203000040040c1da8200288040c529101a181044410303558013070140c0b50190214040300d40d40604c40c0c144900d40c4100c5044c2405094148400c0c1c56440b600c0c40c1047c15440201a030b485a510f445404003031160381e0404510700c001d194804002407519a41c0140f0500c16400b80d18071801d0103058000d1100c0c403c0041401400c1c02c44540c0018001000e00c06404040c01c9404480710f60138400003141d0310310202d1400b00c10105501103e0b00035400c558441c83d05401606a48008555039640021480010010100300b00303036a51084600d9050140000d060700c1e40f04000c00e0080f03201100b4031070b03452000603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 498476294 1250 498475044 498475057
    0x30f020c010f1421040507051305041a06030c040c080612030a021f1103040303090b09010b060901110111040f03062a052a03091309111009030c0b030a05100b 69
    0x42140b581e4024a82040010503403810b01826613601e010f04010405c8800110101904c00803501044036002c0d05408000742d0b0003c5800908802c01d901d15074100d0001480d0840e0003c0c4001c054031106a18203010400303c50456400e0350000d0300800c240110360804c19418001c10170244d02640c90a20a000060b5460a12480e003e18010030400a124903407840d03881142042c800c240156a00d04050400a018080e510300a42e28100d180000c00e1a0500512500403a0980601b6250900d2503600054a010050300700841a0b0b54880c0080800081e00d0401000901050360300703000298214140740003103442488041800301c108210640305004c031080c8030401b4031a2860100d5880e00040741d007080c8400f02030b404140404982c6440101d100010014100c101015110600c160801c1c1c00440c0548201400140581d18085a8800c1c0c0e4108003004a50140031030900003000350341e0755908a9050307844e9108403481a07010042c0b01010017240140d98000030b480700144851402c210702c2d91034521031203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 498477544 1250 498476294 498476327
    0x10315030c0608040503040b03010f14030f071815030f0b0a09020603191514040f020715020703051b01090c1203021002031819020301050606030c09010e06070609030f020c010f 77
    0x20f0001010010100200e8001e40482d01c4841c0e200d5940342e110501081d5180621200740045004098090a00150510f01600082e0003400614500304070700001c80d01414110400c95115180720030707500008484d1b20b006600c9144642d12010490500382c9070050003270166114681080e40c2100540d4402c0141c0781c0003c0c038a03140729840b50a15800c4001090703600340da50340351a60520002611035200308510400b41041e5000d000c0d50320f94031000d400304d01c15114000c0c182c48107003514542c0107110713a000d4440140300703003042803400c107002c0d21541c0e004500c80303000f140c40d03910350641c5000c100c0c820540707200500d0360b40f001c4003010000740e03406034542d0f2071400c10a11440c1c2c01f00000d001140c0d0101c0b80c040401c100410b0755150076003414907141103542520203070300941c201000f0600c82d040040841e0301c50a0341111441c14103203400300448030000010a004d60180c000d00030240801c101d07108505151b0310913151a2038078100c400010742004200d0b00503605020000c4000e4000c150032130110043c0c0c4565 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 498478794 1250 498477544 498477557
    0xc2b0804031817160b0406050f09010c08070803040c2304150b160501061203051c020d05090c090903031005121e0607030506030a0c060305040606081b010315030c06 72
    0x703641c0a0051550380d0000c20f642e880701406562005010070075921155524400c0a61180c442c8500c0c00b2500c0b65103e4070340064000c01c00d1440d008503074009084507a905240000210b0540e0b1207240d8203401002c8143d400840c004180070401810208007401414085441d03016824100c10484404100b000301500907600c603078034551507098a00012000d0820711400310f444412a40229180001200f0202c55a62805001040c40c0d0801140500699030646d5180e2904c0d544489840303188940c140060140c1341c080c4000541f0440f18050b1138030582d2000028074000d800300f8100062100c0241a548aa0300100b0510a41002c4040950161036007a14800881402000164600f001200307408161101641d00c10315049008a132060241d401a542880f031500c0e039100709a103601c0480002040a80810001c0002c64081d8002c16030150040c02d000540c159190a041d040c402900d00701c51102614200100080d0703011b20510014050b03c40d6807503285400c5564110928509000315002d0240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 498480044 1250 498478794 498478817
    0xf060b040e04061e02120105030109170a0513061d0108061c0512030705130f1508090a06060e0907301502160210081501080c090301020c2b080403 64
    0x241c603040108000b0b40d00c00507031003040342035681304000d402c42401d01c0d2221071000d000154a03d070500404620a80020301940b850070507445450f00f03035110002d1f010034001c00740b04012000350a441ca00008041540300c104090198215407080c01e80d0741c0c5522070600c1828418841e19488003454407040d038101040c02c40c8200d9150038a10703d40b02011702a10380349400042001091580036014010b600c1004e40941701c019198280915140e065010311100d584c045c44002c1c3c0820b10481c031040d004440c103415550030400f0b50b12044203481094001c0918500c0c04000e2241242c0100665002007510b11410000011202da0130402c2400203090081c40e004041d2102c0103010307041c0331050303444040c1c0f48119a640c0300c501c0201000410710310141e00c00d40010340360150300c5004031040d81c405c00303100d0709000e280c071080c078019200b2030405044043c80c04401e0198908540382403000f4866200e040004040c00c42c5991890000c600107440c8103029804040712818049030480007240d08540e240c14208034420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 498481294 1250 498480044 498480053
    0x10806180102180f28050a0803070b06040506041407020106080d0e011409030106050d06090c0611030a0809030d0c121107080409110d0908091206090705010c05010905010c11010f060b040e04 83
    0x41880d01002112541c91704241c80403805284001c04962058800c1c40341036544d840c1540d260f0040590160154015100003880d07407070300f544920b41c448401070000982403486d0341640e03c880400c030f0b180c401607075407080140301c6500100042c4a000c0304900d000c685c0b00d0a010b0000301141d11017504680300400110f05080303150b8080d044a00035040103810014816468200354000c0c004000c1c056441700590440800d50b41c0c841c0e000c03c20090030350001580341020020341110410801002191540014400f02d510303040140901c0800403402c3d030318444100c082602c9001200d07821603068101410410210001841c1034080d90200d4204a41c00600120300c840200365510820485c58600380c5448040390803c21100041c0116800a8641c80a8020041d0115680702c0c0203803001046540155020071096205000c1c0c45049403040b00003088180c0b003a660301c0c4c02d542240030500c2c04110440b00391b164080c0309208030700d80c03654040018811146090340162280c411801102d11800d0142e00040510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 498482544 1250 498481294 498481309
    0x6160207030204270804060909050606030121080319110403032f1504060b090c042303011b0f03060e0c09010c0c0308030601030f0203060a12030215010806180102180f 73
    0x1c400c60f9405500110380c50b080300d0f59031003402142c7c00309520300e03004600f0401ca0f02c120b0b0b10074280544014030716401c042c980f00310901c4051541c02c2c0b1552070358000c0700190300f00e0061806580e2083c00e0f051540140002d040a50311405100124a80140401c20100754440044941d0122559a5014401210140940c4810001444042489120305048505100c1c541c8148190b000340b50400400c0200700420451702d20544851b80d00c03460510003071191682e0058000d0783e00d44902c036901f0040d0900e1001c24252032a215030a610491508804038902d40c218142c840606e443c3d180802000b03003400d0300000e10700409404071b01105c03800308a68605902408113044403c1e00706d910242130590b60310b040903003a881100e5280c00281444086a0080998005c0d40d01a6100412090703e00d8140f690110110740e0003002903007180304c1c0070886a03510040307a00030350103081c500e009003a0b9071070200d00e0150f09400c4c142211100340e20412880c00c400f01511707403c07202000d00b1980c51010401c4800000c140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 498483794 1250 498482544 498482591
    0x939020a0f15141003080c010617030405091303021005061c11040c03091a06060702090f0402030d0507020f0f03120c1c021609050606210906160207030204 68
    0x141905034241d0040c000c1040500d01d0740c040400e002d0021100750003400c40080c000f03640c142603100044c002400000e200e0030144c090703c2625000024120354500d00c10141003010350300664203070400a414000c2c0e04002003e1544490100c1d82800d00c0c42d50b56400039501d4035848500700070240d880300032400d19a1202c4410803080072040c4055640c9480381000800b0114516481d44510310b440c0f8180901d6000c1e0140500240d0044110303554003c40d01c9007000079850040c0306683c02641002020016502c191000f0300aa0080035400c000b45014418141350030340091121081c0070003440100011381d100403202102401c142d8241904c91483b00100c1c5c681441d103c0c80201201c40424546e50f81c0000081b5480d290f4030250701c0b1007010400c140d060780c5900481060000405418209201180c060340110307400a90103403045140a01035681480d0545030030044c080a04203000c18840c0028082101036080303001210101180c4001c0d1201039039446607440002e000380c0d22600400b0760f418544526821 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 498485044 1250 498483794 498483803
    0x70204020a03022a030403030e03121903050a0902090a1e0e0c0a09050106090b2512080a1401050f06040e0103080a020d0e030a0f02040f0c08010939020a 67
    0x446000700701d8090080d4001201c0b810f00840c15003551202216005642d0204800800107545031504540301280c0c5c0200c2d10762000c0d00740c802c210741d082194031520000d103a041c211041e403058000420500409982c4090211032219082100300f00160751005400364000301d260800181154000201c62911105d0419080c07905250205030b04e5884400310f0901d55004088803030100c0c0d41e0b01d8016007000c030340c0280950360000702403004c21301007821b46200406444599140fa604424001818100081110f65003100c6400c07602e481542c806800040c1507411218541051180d00c8071000e510b00301c000140324081c031460348000d015400f03850700c0c8201d8020380008940100c0541e12420f148407564010208100103200314040400d40030311800b92080501c178001d0250400401540f50040071800c0078034107a80c015654070300941124100c2c800d00d00003010a0311580320703561401c50b44408548240b840c2c0d42d04a26030185240041007000007402001c0017403081c3e00c40198032000100d1806144100090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 498486294 1250 498485044 498485047
    0x1f0509030a0e01031d0c10050708070303051e091f09210c08070501020a0810060c1b0e0f01080f0120130e0403020c0301050a0c0e0d03030b19050a1208041a07020402 72
    0xd4010017040314941b048095419a03410705541c41c00310b40a1295410183c92040103005000000e803003508025044804288010a01e807400380f0070504000301902d04d420355601c1020794250005095801d8400ca000c1203404001081d440e85840158501c03d404e5900b40068003a03000d8035090103610004c8210742c005603050b898030582d03c1d21500175400103070304602043e255000581b845002484050a4850950360350f009048030341d440100544c280d2515041000e00e03420007140b54182c9a01c7c4500c0742c4041090613210f07501d0200ca00f810040040c0400c122641001400d401030f04e190303030203a2868422410b40c03e41c0c81c1413445d500d00d40c0d8000e9800211710350741c0030001d21060660014540100410840007000740d511201c10020445010280d41004145840d03400b21461920740440d448580c02070502045a42c9000000f407990001107800d44078640c204a404c0c0098204403003080054002e41c4a2070410f40001d44880e900390003107109105a0041c1720140740da000c142202503507201e590190066 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 498487544 1250 498486294 498486341
    0x10201020f16110d0512090d0f030201140606270d1e060e03040f03020405100509100305010e070807051c020a0e01031101020c090c1b030406021f0509030a0e0103 71
    0x3007203000c1100c20075241c086814a10f00464600010a00b0840da8002c0052003080c82102c00c5000c3c0b0340100503142e07441841e580000000c0741595005485640c0f00380d0000590718001c2d000c6c51140d42c1c0180100c0c1c007410040c03007240d00c070081061403da143c20200030386002c0e6540500000d500ca8000c60401858201880581e42c000340700c050000390140d20940d018480c056494406e2582d0340aa8407031140340101c1c084040016041a900898000c01c468030480034130740d1104003060114206503102203151152210400a2000a201d0800300d21608405040c2d1149840f102d2643c5614078080c5501c101d150303201c201c40411300ca0114003101a030203003618001d16991a03c2d844c40304c02c01d02c016214030b1003586e007240325513202140741c0200c1000102041e107244c41361003c0c9509504607090700701107420f01c0249084500d0040001e0401841250b0090a03240a11040e009901c02c2401c5001e08140c20b1a0903c07008000210a50704241e0007440d00c40002c40c61000120b02404612035010b80e01a114000c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 498488794 1250 498487544 498487567
    0x304120c0f09021c09080903071502150112170705010c081920090d050105010902090a06020f030a0f0e06030a090b07050702010909020f0c060a02040510080420010201020f 75
    0x8440449659049922815980c0d03010350082c2e01c51350380c00359440c1001c1c50b001010003000313a0101c4c5219002c0c00801d030038800c0303400102e4a04180c03034010380c80040c910080e0080150b41049498401424602c1805095162451041001045001c02031103040ca0300c01001100d010b21080d03030741c0150000001e00200c111142e000d000c1d201c1c242e4044144100c03110082011161a026002690070403444620445075000c0f11207002d0341244944603800b00503102c03910f0206000b406005d020704030b860001a0307548180d03820800c81d45245d03070103802550812035042451040101c2507480d4000e40b03003002c018101080600b140c0c0d4010043c2143e510407804014404281c80d00e80c009511781d032240c10410100d480310102030750785002e940c400030b0000b00350610a0141e076030b150b005080d60300f0b8000718003401c0c90501c2c400d45091030011a44140300c20745c0850f00700410710304002c4800b0140168140649182010740b500245403020401842c1098110310440074164401d50485810700044180b82d5110307680c0350b51 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 498490044 1250 498488794 498488813
    0x6021b0a0b0f0f010803160204020409060906051903020a0b030a0603021005030a1104050607031d0303040b0d1a06090402180613180c0e101403100302101d04090203030412 75
    0x3004442c5403a481c0000300b0090405070454103840b21000214208049109520341a000025049800940038080002c9500150081c0b1014040000300481c00c24101814003006001c0b0411900501061200c20405a2120400c800543e68200c606650704e86e01c0360070103405001c1c540d100030341003c45060052a0309500201560150310044424408032008140f60300060040d802001d61060b020003807100002c1c010400015100046041c018051500c80006421900f00d5808134000c2080003074007160f02c00d01e500c244104400141883c82403519504081101402005000350045500061103861380305a1814003084010050031543d450180820300d5440c0c80c02d070303c01d00c03892a41c880c0c0441d011440034000d8000004032651a50384001d001020098154030b061800c0041c003100003040c001418070000114490115a0251070b009441c40c410701003e0181500e00030104107003c04000c9240c03a030034a03240080c1408850124042105000007810744c1705503032044d6800c0e01298043c0303040103280f50b07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 498491294 1250 498490044 498490051
    0x11061206010807030614060c10150503070f03240e0703110f0a0e0c030c04080f211602310c02460807050a1211060406021b0a0b 56
    0x307903100b025803509403040e000c2e41c00342e0258039004a90b80c0e079040342038140f0750050140c84407a23604a42d50390300e0050040b401c490900300c4c1c003120355034448020f00544c141000700a0081404c4144000c0d6280741d500e4182030702900d81087e80c100d01070f010411500521940108804014160903190141d68a250064401000d03240036402139440445010b0b0929044a8a1003110011591b000315507503a02000358a80d80010116076458030180400b05030840d040051044c3c5000001c010803135240f00c0d40d0701c1000945d00c407000003072400c001c2100520b094510541c1c00b590035030598502e02016580340315540c0c2043c0c0c070f0b4030035200c0c2010741079a4404140150042c650b054619000d50703040c0140e002134003400e00041c582840701c3e00415040d40d14030699250704100765002800304034200e05500e0faa132070b040f58840c003001e40351030340b200718400180981c41100a070264918107201d146c4a5500c415682c664000400c0540104c3d80440e410f030140504180c4414044280000c0d141d481c0b0a5141101901c2c4069 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 498492544 1250 498491294 498491297
    0x13060e0d030e01060617040c080a0506010f090501080a0f0204110a180e010b12072015070e0d030804060612080703090b030f1501200d0224060d1106120601 68
    0x501d480c040d14103108403030a840140e900e86e01c00d540c2d910412441c0c90405072040b01c540142d4480018001d60a00034a40201d00c600f01400312545020400704201810350002010b5502e03180040004075400a034142900d90310840078194441e41c4d00010b0010301500c1d050811160002543d5502c05da0310007040b41180b9441c900c4900590b071120808080c1c42c10902074214000c4082151f241018040500381d41d10031140c3c0f501050302c2c1074a034484c80822403a05140ba009900aa111007552803407910120b9001c9003502c0d00ba07a10b004400b0014511515588000d800d11220002090611045800c000c026081d0b19010380c001c40c00f02c4c9400000380e803012606030001455200040f0b5111424002ca03801455090701d0100c450300c4960f11008800c0d80840c680b0f040c8085007030f140c04820782c1041c0340800c0f00b01e8440540700304440010082d003802c0c844801d82c070805956401412118249422154000d030040e105070f402c11000c1d140000561220300b85103039001c10041145003e0722800066103100344002e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 498493794 1250 498492544 498492551
    0x20910170304051f02070611010e010204090e0c0405160f0207051908160f03140f0604050d090b03040506070e13020408161d0136090210020f030a050313060e0d03 71
    0x68009203040c030f204c03800d01801a08680343c10840c05118144e25102005030600009031148203201031070899100d42d010760032080d291299004102014400109214020390b0184000d00e00301d1a1201782008030300141d000d02500c03020780800c040c802c00042c80900009820700d041480c6018201441100c24860b03040700d481101c550340100d1a070307481443e08503480f034510150300609581d20f00601083c0e565050000e0f10400341500c02c0c0c1d1004029143c000ca029402800011641a40c003c14211140c0c12100c9151000c0062000090340014071561100441ca0240c20803081c8000003002c08584000c8810b50740e001190100f0784035800304040300740707040c1c12014170740c0744d07a654140c5c2184035a0b50841080c1b20001c0e20041050440c2ca502c09410f003807218aa200720000306070f4003581c925201403515050166200b04d64011401d080c514205209400e0004001c0d00004c040c43d2035482c130a00c0040c90401a011010a0048108110030140e4591180d020b220700b05030071803416501c0550b051030f4800a401c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 498495044 1250 498493794 498493819
    0x60e1602064002031e0a0303361205070206090d11030601080304091401030f02040515130203011805160309031b120905010302130509040f0b0126031602091017030405 73
    0x81e48017980c400343c52480500010583d030f0300c041d8024001442041801c4a4131b400f1041c9180340d5032110818803403480032014040b280707800c0c10403403180c1d03840f02070303003406020003010025a540105030361084034103c0d0844400b409a1811040c985502c81c0841e030103100d031000104e01c2c1c03900400074205641c1c0d000000c00414080c01c802c40c070444820302c405000509800d03202c001608080e0001c540c031400c078102021040d002d0380085280c50344440750030002507a011006110342d410343c1c00e08081240c2000001c0c482400c20850007502c016030306140c0800d00d503441104c1c0081600846522488100700e0700a0000348c00c290074081405207c905002c000a070042c00042010341c081c0c800e907851002d030484000c210609200500c107a80304090002d032044448044241c0001d10502d0440d4040c00056542c8010581142c0086540d000640441000b0350428000c00c00107941e16900d62850a8048450b034bc003a40b110f911403110700300290040200880e64111071115408000010320444100740c9641c603e580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 498496294 1250 498495044 498495073
    0x50f0411030c06120a060506031008010e241302130614030a122d0309170403020d0215070605090738030601050d060801060e160206400203 61
    0x260a02c50550740404244081032841031403100545d8400c084c01000a149504d410019107182c0003100c4848156290001c02d211801e001e00603495161042d000408a540c100d1010001c8000352100d000403044040b4009085560b48a04200d01c5c0d64010b402200c042c10780c028070740c3c0a04914014480200da46648080140c2000500c0180c282d03005880070300f03e80c520b103404a910081c007000c032440080100043d14524110148610046c0c44651400580d8450900c1d00105d0401c1c00c03c8000300d442414030081000da252081090760503981100c41d07850341c0059007203020303440c09664406414646030004100142500240810030399203030300c160052104180180c0009000e0203c50304081c0e080988602c500714803084050364010405041407418001e214a527081140c141d644a005180c3d150385081014404031000260013031262448207030303000c00040000c1d654482c050030441c041c4000c11503010009454240716001c40202c05280c10240e09080003c480402e60103c1c1a8403d0041c0c030069004503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 498497544 1250 498496294 498496303
    0x201020715080105040c0e150c120f0d0510120215040b071b12020d110d05030307030519060501020303042307080106150c0210080402130507030903030b010302040b09130906050f041103 81
    0xe0b03500a200230810310090401d02002e400c02d1050556521541003d6581c100701200544032100c00b4000d01c9403103a0b0104208025100064240200c001c49098207018024192400144464040d9000d080029000c82c50754041e10640d0305c00c50050101140100c108142e0082d4490004c4500d2008110691a811042801d800c01d40c1c0003503004200d141280002405021070395071481d401032003002c1c0d891190f00c074a82035604c1101c0410010380c0e01c03002c202c039040c2c1c038000340136201c45103100422460f400c1030b0000c2c1da01c0c0b10140c0301501e01113900509000c00cc6040b60300d001046400410303212115a1b0b001d030310b4081d1505009403141c43e06007828002c4503a110f21011810700b60010490b01e102c51880704251001c0364041c0040c1d82020b03031113034a0a1190f8040c0a440d0240c903039550001503013242410002d0881c0d0b40419040d04050040004208140720803080d1030346203d048505c0a01c001038400b001c0c00510709032000038020781c208004c20113001000303d07035203220740e005609002c901c1101d0020140c48 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 498498794 1250 498497544 498497567
    0x60c0203010b2713050619180b0a02281206090b06040608071403160e0a08370515010905010e1503010f0e071a0301080601060c0201020715080105040c 66
    0x403030600020060034604030100f20b4102002200079000303900785840345800d20104980c2d10071010310b0620304040c41121031040184001403403040301e06000881d61122020b40e1f015015400d41034012030001d250890001e10380840740074030000100d13100280100580500c0d182d20724400f14510b800744c0020141c406000750580c506000301854501030411170140d0302840086c3c0140100034112614004003d6030030300550040300c2d443c0321940f903141c0700c20005244101440702c0d14001c844090042000441c0082c0280311400d581c00320901080c03080030940071002035407000c100c200c214030945c00c0504c10302160300c5400143c0300c507540e0110f07a210720820060b03407800e2061958251907000015080d40310208944200400100003143c01090742c44030b04146e400c40309000a158120340c034100481c1c0e0031000b4040700462032001d528219032504107800d413142c078144201d0b818021204201001c580c800e0215002800ca0f1100c0714844040c1d00c0d10050252109003e054040c92078003075000281d80c000c041d81ca01c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 498500044 1250 498498794 498498829
    0x10305040206040e07050f03270d08010e07050c070e09010501050102030c03030a110903030c0d0e01030b1e1813050114040519050712030206090601120c090c05040b04060c0203010b 79
    0x5441d00c1c1200b03440c000d09009001780c0070440c0c10b120351955401180c00031806000450042c0020300c01390207240c0402c105a200514640c0d119800c034403180c0e034104035580e0440e1764043c03a4004550300c4a40a80303203031007818040039060103541e03c04540c41c8c1c41051554050000b1070002c0013640c1c0ca41006990324030a44000a030f9079031042c40061045c40154102d81c100422080c446800c20f5642c01c0841c0c038580042e03c08021a400c03000d251420f850f0320010100170040300f46828021a404200403469406004964103601501f040000d44030351105401700d4500030800c03803d0415442d002141090140c050482120503500f80014002000e8080300140c0c041d5030050b010b84410343c1c10b81d0764810480202641200c441c00b03900400a0904d40314103240081c1c9020b50040d240c546040d450203410103d0503007018005000d00340e4600702103800c5410801c00e48001c248002001c071500902602c4074050740c1d112107004c0c3d50019000c9103442d030100001740300d00e00c03e85c000c1c00200100d604102103281c0b04c800c00e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 498501294 1250 498500044 498500047
    0x7060207110d05122803020d1a1005180d1212020a0917070b040f061b050607050d06150c0b1006050901030c2c0306091506010c210f0e010305040206 65
    0x141541a0200a0903058038440740c0817410312400c0e00d4031110410110608010941c0460006038456207400303503e1040c81c001c44170301400c418010010700c0101e490f0f945601040404900d200d1039031244e13040c90403054001840510640000c0c50b0207042031030200046000078000b001c1050619255009817006004241c84035140141070078248070b120420754010081c2c078807071017500080440c0c602d8002c2001d0a0801101600c050414002030f01031401c1f8030045200030029060306000c20008602160030601a252956032403100d00c0c4400d0141000e0741001440600c90342000045903000808110414491064800d0036642c4220b010301803d0140b0401010520030062641d496119501112400707141c4d040803800004140160740c0c1c0300c8841d1488201440c51029041e07050300d41003140551107644a0014070b510b03801480c4801460340003408c03030b905010340e03203200200b0099030200b00c80480840710400f0103114500c0100501c1c1c0c03901001c1510101e01c0003030910b10294400d026441c40b440d005003485 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 498502544 1250 498501294 498501313
    0xa0b12100b15030c0333090903070c03110301060f0b0403030f0c050d02010c082203050a180b0705010e070b09150910080a06150c0b040503090306070309051b210309040207060207110d05 81
    0x500400003c08e202001d00040001c0c500142c802c9400381e01031130188540070442401c000a0500311503c0c1c3c2c105c01c9800301501c17401c221a035108402c07201580e5040c0340021b50211034000540701c01c902400010102e0064100d0003070800d6056115200d00c0059544459403a2104510011144410348404441000900400003c24050710042120000519000d0514810524140007a50054004c41540c1c64009107603030030710009008906c0c1e0705400c100680040340c90004c0200702813083d128564001c80c07003440c11802d404070400a0b9485504090202488141b001d43d0042c0004000c03904001d4140c0342010216810104140e002200b00541c5c0301c558007280d06840d15a40d20310028400c036a9840104080744c225101071081501070351260b2804280401a4507105d4103010166080a406019442207405156a05500140c170480010241d40d403441c5503042d0785045104501149402500004040d010030a269001f04141030107503e8154100c00121f040200d0b00c904180058260307407146004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 498503794 1250 498502544 498502549
    0x30216020d110604120c0506040e010e060a05090f04150b030d320d0c050a0f050a090806011e0503030f0a260a050a0b12100b15030c0333 60
    0x2101035180c05035140c00d42c00401a0300083d19903000ea000b807595140c40d91035003400c20070080d1b80040175140446950303003801d003480a03048840c201440f48556086507c0d002c078a007a01d65021310000340030701034410301803881c041000000342c60069808030703141824044102016a1184612003440900030003400c21020741c50003c54604211045110102c0c4400e8020481f102e40540c1544404214010031610744011102070030807104911902024000100044d00c0140d501c10383c9812000c0190604d162104800380045840c4c107640d8015146620844001180041140c148094440c608070444500c090f15041410f441e402090a1948500018400d40c421140940c04a05800c5031164a00800f241c070b240089564080903101002c140e0f83d1241480004000d501500c0c081c10010350310414015140313401d85640f002c2c1c0808c0c1001c2503654804440d0540e459102c55074403203417215403658032800c2152900ca03c0358415502020030008076250020320030a0800d82092040384420200000c0061405 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 498505044 1250 498503794 498503809
    0x8070c0204020d020c060403020d0206010f0b0c1e0c030c0d020901060318151a01030b1302211806100303051c090f060e0105010b1303060b040209060a0f090603021602 73
    0x300c0e40140c080c002c450050429101400800c40f00c04000c2c0014101414040d05001c0205000011034001e03c00600c12140340904100488040c0142c5c0c3d0750390b200e90300c805401c11502c040d09841c1440c140c982d07150b05680009608050b44001c500351361480e04c0d094200001ea0088000081d041906140100000c6004e9802488100451581441100c03400e50b202c44208101c0800b10460550321001c10046858100500c44010300a080801c0202c0d81200018140d100012640c440c41d50001080b8040800203c080034048e2401c62640c600d1741421101c00700e0000102580840f50301c91000044c018007e40d5a68500b12078040d16600e15001c1c01e105003d0b031030000407015401c05500c80940d84001445603102841490144000013407562519030414251803041e40403040c01c500901031160f504800d1402c03e400c881d44400009000d618040c0070401034083d081c800d903441100401c910003100e40080400240300501d0b60744580c1d00c2c0e1940400d030228060003200b005c1541c501d900d1180107080614 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 498506294 1250 498505044 498505067
    0x411190509070c0506090106140f09060904031803290106090b1315030e06010b09150304050c030304030b10051009290d060302030615011b1a040809030f0a030807 71
    0xe4a03c840c140151141840d000058840340e100f07a5544504109500720304180008114045030305030a404400400500401c2019015620078a40368020900b0580500c600b008050901c1d0421007003180e803420220240406405c0a58004c030041c11441d2820081c0b8070058166516900d50308111800c101020f2401d80002c9200c125110031400c000c208403100f00f20495006445550105000041c0720b0a517007031a2040c0d210340d800300c800744501200c0d9540d1f0319200c0c0085c801044101c0d129525802d0107850483d4a50030241c05000c0001d020041c09008140c0360702c0f610000401a0625a03558144400e0f01441c031004e00000d80e10041c188085620381c003403440c40d18158050380381c41000351070340f000940d40a02e1004606070340c0d5002c01c000b14102440116404000c85400303030405a40c440000e00f0341000162f5184c070045002154104226110310016855902d03041251301520306031501c102240d03c15013000388030388039082c03c0040c41100010382100d11076048d0b4400502e611554003c0c2d40e00455003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 498507544 1250 498506294 498506297
    0x2130b0d09150b1314070e0f0d030201021b060403020624030f0708301606021c1109030d08070903050307080a0f0c12050d020d020a0305041119050907 66
    0x4014920115190700c002802086520b5000540300a0032020480b010742e403002845207030350a184c0c00c401c05d40c1c41d407050030741d008401d410301c1440c1858170710018071655600820950311000858400c1c2c24154150301600780c03000b8008484800901d510f440c0f942e1810200c5004006a00c8000041c582103407000300f4054048040c1501202d03c003c0c14002400d005080d010400c45a000740350422400c10200103540c13018041015400b17903040050800c68a03409419060402c80d00005502c4201815101010748102e40100b4215100c08814000c640000001d4051482e1141440481c54494011400303c0b0007036500203005084058002d0001d55012100030304605c140031681a0000c08500c041c801044c41e10321403180b0a070f440c000100040d20042411040d41d04200502d0b291400103607400742840c804c0b4116061041d1070324015018480a84111913000c6a60390000c51500d203102c0d00360f04414001c83c0700303080520b04404a5018428900e50780c46d00700c0d01c440c25015040040742050b040003034210340325 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 498508794 1250 498507544 498507551
    0x723010e031b01030f1e0c05070c14090f010b190e10080118020a0c1e0c1203020606030d02030702040b031207030f1b020612180601080f0c0402130b0d 66
    0x164000207042025620705000d40c000d40460303200140d030707051103180c1750041444400c000c2580080d82115001103000c1094010300e0740c2e21090b0244900071000c1c3c8010b0740c0e000b50701086241e1074166509460f82000c840e103025481400104a40710210f4448606070f55144030309600301803103a2031000780d03140001543c0c02803018010b8106450b80703402c0b85a5092051644a50f189075140440c40070908100f502082c902510601965010a500c01c04450300c1c6500071010003014500403018455280c5604801841c070070500a0000b02a510000401c210a009800782c0c4c1583d680d26050540b02e04000b1820401a0000c210440051038964024126484050708491104030071443e03e10303503540142c805502040408070038903521640500c3c400c84810881d21928480c540ca640400c120740034503613440e51862307500c80c001008055040d10f003046440c9002e04841c500d50b51248440e84034060080704850b071b40a055690081c50401c1e000712584940d00600036030241e480c1182c030690a03041201248400380e00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 498510044 1250 498508794 498508817
    0x9040e0136081c1d03130e0f0402091929030105040b010506071e0c080708070b030106030e190c09060b0c0a06090828121a010f0504050402030a090b0108072301 70
    0x2441d0420000030b00d138200543c1c2d1464104422040500d00f548503d000f141c1c0b0b9010000220000c503030064202d0303815182c001d8a620340c582c0018403090680c0745c01e45294035002c2c001c2103c1c800c4900100d04060340b280815440200030040c14241c0303d013102c002e0f050b010180010445070406000030041540600c1500c20204a1101c41010041e00d0303c0c01640d0b125030f03036541480001000d12604000301505002070500614000440c0000e020521824007810b81c1c502181c09219418403400203804140c03501491083d12038900700306181d01d1130003500c030741618000001c01e0341907011007221041c0144a00a142c0c4000300d50383c944c0a0070800500f21118182481500c8a54445d100c03802502e61026a59194120200400410070150040b44454007410301c594100060309a4600e14551102880c240d40d0304041e0b440705136900c0c819a0f0140fa001403002081000501d2030381e1000d15030900c140350711104c17030740d80d41e8a603681c41c0c0b401e0140c4810008220400d0042a40c02c8500c42100207040c144040600f8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 498511294 1250 498510044 498510071
    0xc010516150501030c170c0d03030b0925020708070e070c0b0411040b0d0308150a05030f0313050105070b0a0c03110f0a020f0106150509040e0136081c 66
    0x60701c8030011001c0685550040c01000f01e03081c8010043c1c425051441400c003140b24001c2d40d162002e952130b600800055132000c09051082e0040b11540b41c000d4070310030060801c00c2000076820740104206810a208550406c8a0b900c081a2402150009070003064600d05240d110701c00d460740a414a000d2100440c1c054001409591116200f207026041c0c528102000006000581e50241502c80c03090100d0440100007d03040701511380c0116400300085055468480411840740c2140c0042c6c1e0325200316803a03d44c1440000006120300c0c011140d42143c002e0340c58006541c6e50040080c0184088001d00004420141591201580421915000c03840010241d00040113a00800520b600b1501c0050600035079601001402007d1004500800c42180360502100b142d4400050440c200400001c4108103551030303811890304452400c008201c9140c43c0301448108400d0f09a00c1d41e095a0405c0d01c640c106d4089542c0300f4001c50b01300c486c05207894009001d84285e86038501c00d401d10b5603910300c80b0b400e112 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 498512544 1250 498511294 498511313
    0x509010b040509030d0b0d0b040609020d05030309010903021204050a0611250503012a0e01120e0606010f0215060103020f1e03070e1c03080603151f0e090c010516 71
    0x201c5000020b1503517480c400349448240c80d107944034a40100d82d8401c1d00400180c0f1800010b6020f40c100400055240d641d2001403526031748480050168400481880740525040d0301034081c2da88a030b000c5864440c200d1003200a00d0050388503a560241c10644100100303405a08000c00c04c10051080ea08000003207250092035007c005400090303285034040621040c202441210200c0e005c0b0030203945041d42c000003c00f039601d413500f20f0314204070310356400755450303406015911600002d0745024400c1e0817406011a5542c1301c03c80e2494009040c2c424132082c4a0300100704000c0075000200b42d243c442e900c480c01500698041c1d03d94103140c2c2800c0112628031a54010005445003101e20310039580d003081c46000306004502c4510034840d0f60016070000262a440000c8002180e040c200703038080b69106c038002814075200071966038003019901b080100078409100105c8000e2a00440d070500c00b0380b544101d1889000494051080b54040c00960060350300480c0549034018504100c50020703009951b0f110301d103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 498513794 1250 498512544 498512551
    0x3141314030403080a030b01030902030d030e03090a0909060c050a0518060403060507030e010f1505041109030303010b0403152d11161e032a0b0f09060a1e0509010b0405 74
    0x44010030b40d0a21700c0c3e454040c850740310000346020320110140307800003900c0b0745400f03d40c102410342e1800d0508070101c061040d100030450080494103610756030f0b80002c020300162801101c1c0203140075001e03203e05008406650800407150341d642e040481520007500ca007a2441141d59001b0700600c030000004607a80186485070400790360108003045040401400d588180c4081039000e802c1540000802c0d0440c0400e030b04032002100c0102d4a50106e03a00140e441c441c40e1035091b00b5000020020512160520080080724490040c00c0700402c9850510012610150800d80450311207040a02524901d210b1002940c18890700004420540103028070b415441100700ca002c160001258409000200704408204030b101d81c2c00c400348110380d5a00805111300340c6103c91214030308a500f0851446500c10003281c15601c085c2031080c40c10007c83c002c14002c401c46c0e01d03c1c158480c45d0000b0380f807410103005121444d61030703450702035061000c020244041c00c2c00801c0100d140d03607103d8004130941c0e41c501401e0700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 498515044 1250 498513794 498513803
    0x50328050705130819061e0c091409010f0b07060e07170708030a0509060c070503030f090f0f030c0f01030f090b060307090608030301060c08210a060603141314030403 73
    0x5444019941505600405910002c074175048100b0581c00f1000d09840a030505500a00001d00c14420488000381d0313201d071043c48a8401d00d06202c8054440d0056068003d8468289400788441e181c5401c01c860860240038411700c0c1d049246040140c50088000740c020f40e407103100d0115000e146030401030322f00300d0140d00100c8200c0003039000c001d4200c800d00441001e0b04451020703500c2c0005051f4043c0c01489040c40242c01603a0008004103010014806c900c0a0180142500d954065941c0080765a13000300b1803c40c82074031084800c0101c0d10305002641b00448018029042020600d010005c042584154450501d51a0070100c01111040e200d810200d40c4160702d07180441c00c02500381461f00d247c0343c0011401516003282800301140000c15281110000d2400c030942e03d1551034413203501d020f024121515400031143c0003a0700341c00c00011500c00c0f00381c4030040004580d5400102c06075440486031f2440b2410728008104075039002c0603940d2501c1e008410044103c035007400d913603255034083d500c00d55 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 498516294 1250 498515044 498515047
    0x30d05100f0608043f05090f010f0e01120e03040306051e010e160c12021c05040f050d08040e090d0e040506010f3002090301110a050328050705 63
    0x71050a00841005000d491034501c10324030b0107aa034090010070580f566184102c0292a00900c10300201740042d251810510f82542d82000c0c50015025070002410b40f0301c1485107a16017095944038404440c100c0d00e69644032903106000e1001500d886c14849c842c6240c044e00c8944582d4021010070060009500c2407100064615101c80449418840d115110800240c074900401158000b07032001e5404c00380041148010100710002500c5003083d02c0f130014800c402207003990310203540100308250000f1000301c00b4013190155508c11141441540038651000542da04284160f080c00e44052642c81d1150035002d00d850713100c01c44000140022038120790603074000842d54030019440b80408003681c00984040c420b40c1045000039145a03036640c00e041c00c01400c521800b4000250740c4a1205036148014420f0340c5000f200841d00181d0301c103045a9003c0d40c01c0c0340c040a0b000e8140d4040780c80700459640c5440c25a02c5210020810500d0090350044488803400c002da4080c450303110b118020050b80d201c0c175 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 498517544 1250 498516294 498516299
    0x308040b0105060301030f030807020a0218040b0603013b060903030a0f1a040f0b09090a0530070501020405090112120f02031812070303080708010b0a0c060c02030d0510 74
    0x5280d42001608402e0240070705200410001b49003402034854164181007070100c59885180891030326580900c040c2d0b0004190302a80414080400c8040c05103004440e5900c1aa40f610181402e0702c0076822940c4091100303010b10f01c20140a00140d81041d000310441c0183e40560b0100d041c606030003a1120241030f0030000070301c48000054410b210080188420034800b41c003d00d50044040186000c0e00740c011030b01e4546203804d120055000142d6104010907810751800d0810100381e03607104600b401c46940c41110032260301382d80603181056502c41084c03140040b4410142c81c0003c950080d080c01c981c0c1d517400740302c0841c4c541d4984079207031b001c1d005021801804075007074144521201155007100040c80409005820030755804406c8554460400440442d821440302c040750b08024030782d040c0400ca004052022080540c000d041c280101e00c01d031f0301c0c070006903255010350b6524442d80458902144041030a03034000707011904900c40986141c0113036402c04c02030b403d4440c01c3d5a030841d000ca25504018406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 498518794 1250 498517544 498517553
    0x302060d0b1c03020607081305060106030501080d02060f04020d050a0606060315092912030d0f0c112508011b03050c0a0c08090a05060a0302040f0e0402211603030804 73
    0x4030b11800612600d200c0c2000100d8802949400d00a0040c50810050100080b6031100c81200b00941a42c031a088460560751403400900400082c0a801c03038500a03054421003d5100050b83c0d401404100c09543d516195a820441c81005072001110709029403500240419490310420340180500c3d1004105c1c05540211703009020700079006903412034078000b4a4a5000c0d0b039000e003060503021010811550392032000002d45050a4400c0e96602e0780700029000840c40400d41001c521010914401d020229514100765011070f8140d1a04030243e0040f040340a5584a05900b5000070300d040004c03840d469100c0781d015007503510000301400c0b0048c0c50f501c0c0c4030707005501d48600340d40044c01d242c0003070408a074400001c0522610220103004c2480104284006036500c12100d0000d20f8014150b42e520b1715400c801170040d4016105941892403161700002c0c4042d00c1070144d0380b003035600505030318000d005141c481c84c030501c080402a42c28861f913200d8002202a8800c0b21020f903009482c0d00d620351809140c0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 498520044 1250 498518794 498518809
    0x902090711030a20070914010b040302060a050304030e120a0c061b03030e030c010501120506010e1308160c061106011703041710091a0a0c050d11040302060d0b 70
    0x14100016074005245014011082c2c0d00541c0b0340345030152811072140d10310040031001e0392100146003c3d40c00005180d1032036034032030160001c5d0741655200b0b0360303a42c0d03a4221a6004500c0003a410076070801c00c40785d90342e2041000b0340d4003a101e810310888600a0030041044890000358803c001c0d0b102d121004103100303800c1b00050090045180940b0300e0101d02c0d6420401c030703d0f0890002c0515440b055150260041230080c0c6140e2820b0000030000c1e580e51b040800a010140700d000c3d41d0600400002084000340342c0740c0e035440303072a0021145030364880d01d90f903041103540f2405540e80c4001c8404860400181007107075a0004281c030740e5032051001002824103040c0403040e40031020700b5820500d0005008000f00544003140c03010014010024200a18a030506920b40034242a0300d15004202040011040340b03508010103200311031060f40c0d50540028100c0e625085802c011910600030002c941a4580084002ca081e5420302c504080d51380e03001c14a19044101d040c0c1c40241c46540b84851800c004c2c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 498521294 1250 498520044 498520051
    0x803030c0901112d120c061603020705150c0d060e0a0e0c0d140304090510061103090a09050a0f0504060f0e19030813050d0903150e0613021909090209 66
    0x40241140084501300c040d540c40a100d118841900035048030345264070b05024909442026051550340c3d03105035414030340ca6002c00c8071648a20136098281a800078860b10076208285e85c800c0040c10032a540e419200c21005d0300070f0001d80c15840400c0b039440b50321810700408004001004c003c04d8241040d54451058a5081d45002c1181e403106c50104001d07561321206032103240d007104801c10700e00c01c05150f4a0452140350030005500e800c0c202840081c4903810340035803c0f04d44940d240720041000035502c0f80c0301e21582c05510fa11801e815401e00100e40b20f46e0056801c4100f5040001d44406107011440594004850550351240e641ca003124122000740144000424180701030308404039000040340e0040002c03080541004400e000240300044610910030080e81c01101b01c6100021216000b0003109803400200c1d100c0c000c01d04003281260f014000e9910184c1b80c1d001800d229a510360207040200031a1030142c2e407055000c0d053f00b13070342d1103912001400391403104408181e24005006101903c103019 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 498522544 1250 498521294 498521327
    0x5060619030515150d020d06050907030b0408040f06031406010e040e160f0501030b0102030712090b03090a0c050402090a0e0c0d0e0312010602060609012c0106030b01020106120317100803030c0901 86
    0x1402500d0059441040804090b640800300142d01d45443c02b40a2030002c1603000100b075001128240401c1c0480000507100f01d4107092012014240c94101c01c4060750001004004030f114100f000c0f66240d2f015503101606504050000240420079840342880d10740090000f10301a68070700424040701d00e0080210700500b200b030034180244148000006c0d0740e4441d03008060590004800c0292409201d035440c400200346080c2416160300300201d0a603142c203a8603108603050380131031800043c00d01f402e0081c2c40419400421b0180864546488002303a004020a001e1640004002c0d0440e41040c80c8201c1c00d551402c0c000550300ea0001b8040380f0741140040e0401c1c401c1d513001c2070420086554000400d415203084401c05401d03280c86d48205501c202c03040501d940c4104802c0300128915030f040e031045442507001d9000340011070340d411103120b12a20300500580065403800e803146081100410b01600150741d03900524805a445503a241590400c0c0d818000c1c0f00740000d034008041da8405414440c00404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 498523794 1250 498522544 498522559
    0xb09010e09100b0d0603020d060518060603030415030605090a09021c080d0209030114090609010b010521090f030c0703061413060507020f01090c031406040506061903051515 76
    0x141034900404688200400314030b00213030040d844111a0010001960b01814a035040040d6152003009070100b00c0e140003400c10102449809004001805401418041d0203145001c1c01d010301c03940c0a50810b1000307424540c0301c0d500000c964590f080c40920441c0c0d003c00020781c0342418410400fa4940150340c0200d480c9580307104102141d05401252340b00d685500005035602d4607500401d000d0822881e450310215200420003c2030342d00468628841c7e04c2c1d2400030440f44507543d0064a280c094015011440004400c0e0040f12410489690350002c803800c1c03c0f91444d6820b494114030f1680101c000d822a074120700c00800c100103850196808950715004402ca0f249000c00800340410303807505015154a8880010629290090020b0310520042000a00c01003a5a0800c1c0020b201c051000303d40207000c040200005283c0460410f0085e41d20001810040d00c40c01c00700701d00c0d685030b68440142c90b8684580040095800c020150368006a0511038050745080108030314104c10a05000d4003a00e00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 498525044 1250 498523794 498523801
    0x30a0f0203030c0f09010905060a0306030204150803030c0a090302030304150e0a03050c10120e01021306170103060e0c060408060718050609041a04020a0215061c0b1f0b09010e09 78
    0x14803d060390307400d40460f10800e440e20b0180303004a6003c3c80651110341c2043c8001080e42045a15030043d4090ba4000d560500021041c40c4400000000714452022039800c00e0002c2110544010014100780c000351800981d410b49a80000341190b100d940400310299114145026098002e141040c04580c121811255036113541c551984902c4040102489041c1408100c24410300408400400002442d0100f0103044c0c42400d1a0003548211400440c3c4061a0030000d482840b8882d4074600c1c40590f060746d0403a03440c0d95a603001070401440f00307503201e000d02d060300700c1e140d183c850180004240110007040d00f4100f01c0b6000e001c9002072100c0c1d01403090303525018442510b074141200d402c3d130029200001c44214855081d0010340d6420030142d48180001200e6140c3e580c000303500b80c40000c44000800c1c4c42d4440408000ca81200c51004403030000e0f0b40f0448a000c1595040401c0d0700c084a4091101002074003003400186281d560465a4034031004140f030f01c0c2d1542c0c050703031859148c4800d9440d14050305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 498526294 1250 498525044 498525061
    0x309010e01060f050607031e020304060e0402030c07080706060e1005120705221b0207051314010504020c102a0809070909051011030109050a0c0c0809120f030a0f020303 74
    0x486038004c603070145400280c07920406100b040b000c2e01c8468181c49150b0990700c0785c10300035160703881442031400080e02c40c0d41c00e41c940d25103482220f018188580c8118502401641e03541c12f140c0218400b590b00700d9032060000340040c40e40e420306104205009004844a040c101009041002d1440d41d01c0240d100c803074140066180c0e03407032110b240c01d4080c204a400506078082c4001a082e400d410030241504160b400c1102500041c000050710011158054040c0b84c0131800700403940d292035101c0ca40300c03091004110504056005154081188050740d00d041c50001021050b2802032075103803100003a4205860490b102c0d03503098048045180b910142a081c0041020390b2a036281c0203109410b50744000c183d04100040100c49030700c8032400c60a00410700b5507080f05505800912600212034207180014540c94034611681d02d084100780c40c1d040405001e502c540040d60003000200e6000040e0b0207481e010704000f0405403d0319035000000b1a690034018000404400703103c40c544c01558400d000b03006040d1b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 498527544 1250 498526294 498526319
    0x402040f140c0d090203071502060601020d05070303020307050906070b010e06120604021e0306191a031506040204080307060f0b0909061302150d020304050c0307060f080408040f06050309010e0106 86
    0x51201418945030103c2201c902c00400b4240002589481641c1c000101d03c5070309035044200341242e03001e803180c0e6600c0200698070395a80003066000900c04001e480c0002c0c3c0030350301031500b00c1850b141c401e0a000d42140401d046900c21281514507185400041060203100504c29510143c00c0c2c42900341802c07401030665451a0190000b4170401400401f00f5014800d0b0044901100008040b6038550501c0340e03001325002600b42190400500700181d2075540c518000041040c444064001c0055081d61540d01049480c00380240c2c1d8002e03001c000000350002d0400182c0104e60041100040781c0e00201d50710411034408003400790003901c14608111f034050002c201942e200300d42710a03500b107078002840002d2507558003081c0d42c01c2d600c1c2c02061829050701d0f03a5000c1d40c41540b1900441305000362070420140c1d150710718422440040c0200010411852003034804980041c801c00303255003090b417582601050000705401000002e000032013040200e0409000c0e01041c8503840000300099428102200d81c1d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 498528794 1250 498527544 498527551
    0x7170108161206090203120307180321030b0a060521060f0607080d09031115040506070e04020705011802090a0c020303181c050307170609060d0f0b040b0402040f14 72
    0x100d200c850042c0c803d02c0308070b420140e02185d0080c140c5d42c4496260349140125002a900c0c4c5002a40010325480c5110455146c41e007925006001c07552050659110410680072500c42e42040544030200c00c01281c4569016401600c21b85e00c5140d1a604c0e103000f118840640e4903042d5414074a8001400310075203850505041c10751060310781075680d0500d410721841c507100c2e40340201d0146103031100920a055200e0368044038030f2a60350640300b030110510340760088590162000351a0b40c0140d00419102c2c2d0003084c4044d15a030303001e44098142300081c1c84072402c50759401d48a09004600200e20380071494500036490348400d43e02000c01800024400003592408000e01c00780c100e0b0080d00390020392600402000c41d008540002e880740138074191500030401d810039141140031074620b0255503600c00c00482098442c9901800342d142d40d40c3c54200700030303061001c50707400d0320800e54510403000803d940d9240984640c0c019500d480c103a050901c184401c613a41c4020284015107484049040e450303098400e00c1c0c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 498530044 1250 498528794 498528809
    0x3020322150c20030d0f05040c2d0906090b1008010e040c0e07090513410901020424020d0c02151b010b040504020306010308030408120717010816 64
    0x9034900c44140aa40d105410403040301c0f0f9944004070044460310000040006143e248000e02100c40031044a40580740c0030790f0000c1c0f00061480b4144801120115141d40907150303050034001118a80c01011501c02042d081444400e1f02c2d036100340710700500c600541e0501101540ea0b03c04000f08260000d01200b410701404141380703080d601150901c2046201500a04200c020411560a1100019003010320a10485000f107106041024040b459407086883c0c1b607030103050107459100c2c48282c8000100c240424150001c100d540c2400960128a8207a0302c46d42400d0700040c1e031507052079620140040c40484001e001104880701d00704c41580810468480521400c000d03444004500c000b43e0503100c0302c515051801c1d4007080d43c082d00f002942c0c0c04a01801c00c2c9000b000105508014001500c204940194065001c02c00403c000b8180f44000c551060051020504000721358030401200c0700b00b551110b0000d90910000125841a00481401004040002c200b507a02c0e58103108250030b100c1c0310391079 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 498531294 1250 498530044 498530051
    0x11d06031c03020d021b010c0516030e04020708040f031403031605033102150304030206040308070c0209070f1e0e010e03070503030d05160e0102060c0c0c0306070302032215 76
    0x1401c540250107649600c3c01070f800030754070f601c610a040b1884810180040300c80c0c2d07091820120300240030b0303012600044d5940398001500700082e1003d0780d081c0481c0f50760540241d4200003490104010b0006071010f4428000a6441c2d03e245041400704e200f4110014041c075001041030210104401601c500c4094043c00c0541d2656a24040c4423103844c030b003031090f0140d445400d031414000c03003030448040c103a184221000d00710450b1400443c140c60004032001000340c0d21500114011134000d640041d0301001520388200d92526076800300394030000030f80320000400c1d0842d81c1c002e040f0303400c02c02c0303c41030004204001c21468400000205407008091505050189403d0003000360b8605200c0e4401800e000350449958902d1403500100078a02110410303e4100e0907071000264610422654543c650140d00600301a100c04d2546e03081076000e803442d07107021b00c80c00503811040e840500c0160301c1030b1030b203490060701d0f13261080c401d442030704082103020101a4100c0aa0001510542519244045044002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 498532544 1250 498531294 498531343
    0x7050c0d0c0f050604140d090b03010b2203060507080601051608090d210f0207030302072102040c020c010f020f1009030512010920180f061908011d0603 67
    0x20040c001c0b80003400740181c0541001c000078001c082c0560410703001c255046032000c00c8000c1c811559100c4031301868880e001c04000404c40240000d016042c68094001102034524546020b1364000440e40e204031403440e01d4030308001201c2e8014800d2a403007242070030214a010311804007944d1401ca4814000c2002d800803810011544800002c08a8150b001810f2120304d085e003191000e044c5111501c01d8009101c0040c0f2007900d91011407050116580342d0024910142005104048115040d07044890114110310450241e03866001d010305000564018141c00e0304210001005e1540c107080d25030030365200c000660b0064030001660410b039001c1000002d61500340746000c807102d00c1a08040d0850015504c00460801d04540c4000420b000c407940f0224144240702c00761079280514000000000060b0104403840d082288070061a0503009000720314001c0c03c0041814514040e964550015040f0320040c050280b076180711080d0f03c2401c4890000502e0701a00007642c904000c2079010554a1100380da = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 498533794 1250 498532544 498532553
    0x60e0411090f040e1006080f0c04060e0f0405010b0d0b0f061009060804020609090106210605090a0b031c0c15020909042901030b04050d090f12031416050607050c0d0c 73
    0x48105c9840d401003481483e07921445560388a4400750880c49078041c80c40300031036620301480b07444108c8085c000380c0101507071162100e03080c1c204010015512552203440302e00c1d00d60b498051903075645d4418150b41616003072400640760524002000140a03085c40340300510015000160070048035810300e8000030b10703034452010914601502d13038000d0b04400c0901c00800d046802404003920500071034404000740031503184840c21740300342d032003455000386e00c01c0085450103905400182c054480a022a840d0102080c00004282094101100015003c10110b800c000001002c038020b20f00648013942040c5440300001e2450202400007007007600300b082490320064080110000184c820440c0a02941e07503810b162444400c100c17030480300c074000c100c240722129009200f03001c142d0300140b503a5004075041184100008039a84006e41c240305014480c1114141000e004206e4820003001c6180f1645443c81c0051030514040d15280500a050109003045040001e0728003d0300c4480c541307000d845183c1e042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 498535044 1250 498533794 498533803
    0x80d180809102f0d18030b0c19030e1009080d0203060a0306020f190f0c060f020c0604050a2f0d0201030b0603070c02031908070b07020313060e0411090f040e 69
    0x8105000703c0c101d03d811040e080301282000200d03242415075942e007140070811107400701c1410348040740003000d0b0020b10218091a410950100000300203500c3e1000700c50b0b004090380d00645c9042c0002e51195180c865494091207003156400ba00b050134094451b859440714468061460302124859010000030b030181d5650b6004001190808000c6540b003102c3d01c41c2c401c80b40c1c0b1501c12030b00d8a909140c0040e105501c42c500301c45a0b4481c2e541c5000d05043d490380c034000a0a8603003510200e240c0c00f4400303034120035000d0112500441c403400c010460001c10345060085580c10120000c120469841d07030310310441508000002442c0106d61540385410944010f07002802c0c61070140b90000d1000c020403040e1904180c001102d00d00840888000d42080c000381d1440040390300c4e0040c1b04a80c00c0c041d80002910490245400c0111801540e0400c0010440703070302480c00c2503000390300041441c11401001d00345842040250b440808100e0f01e028950320104d4031069540d00006c2c011595060420b074651414031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 498536294 1250 498535044 498535067
    0x1091e021f1d0604080d080606041a090901060207380a0c1a0702030906072108041a0c1b100e0c031005040203151b030103080d18080910 60
    0x40756040030001aa800034811000070422281003410100d07110941e00d004002c0c0e4046902c924018a2041814001280c41c0704002e0a0590840d03030500001c038856041d005071341d803503000c40c0021030344803500302d410095860750603440442550080708040c4100c07041c0380388c070301d0001080d2480e81001031001704c0c4c2c0403200148058901e07070890000c00d0001c159540800c41c0d44000d40101c0c41182000c64150707200807a90400e0352500050b9008210340320050400201078003905004a40b501c0000c400c003490030700f001503043d06800005840300c00704030030030a40d800c848010744858003440c8040c0c540090040418400c90301c04070401000350003040c50040381040403c000340c50b43c40c0b062001d41c0110340810703a503905e0784036840c1c40ba0080a0322003120b4000380c8901886150000c2c0140550382080c0d009660210000c0c04840490aa00305a2008401070400450003940b20f50b682a90b03846444030070380121040c0d01e03c0902e02d1180c00c5a14800720b0004000e552003a102100c8980000b0038070b01d01078811816a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 498537544 1250 498536294 498536329
    0xb0f1f02120a08090d2c030a080f030702061506040302040f02090a0308040f1a16020a08060c0a080f0402030d110304120606060e01090b031611010f1b0201091e02 71
    0x2e000c0350382d26849541a401030364020111090060014402c1e01d612020110178400038100c4400d82c0554000041c0c5004052030240503240d160880d038403840ba26a11822603c551080000144014168100049503002c03000d154005809000d4034000381d0306109500c0041c0c8955101c10104a51884a504540c16604010004c0140c1d45e6a0302e0820f110790018481d200c019042c2410000303d185042c210410800e6200c4965440c3c02190907954401c0651810309a07002041c3e284046941002084010b0150b00308030180380d100ca2407018001d00110000b00318207038003d258410b100040c0c03000180b19003508041d040c01c098081303000102c14554000d651001050654440e114400c1c8040f607032000040d240301e80e441d8403010a1110040d07a400110b841400c03c10401040060700c0340d1140308a1546880711890480c3d65581090007050940b00703142c076403c46580d83c401e080c259080e07036188040c0c0f61014a000034846901d8603107400c00158402569841c0c00004240c03800115a01c203e80700c0c01c1410103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 498538794 1250 498537544 498537547
    0x1a0d020a050904091208150303070204020a031e0203040b060f010203030403030921030603060605010203030105130b040617010b0325090902061207020f071e15030618020903010b0f1f0212 82
    0x1641858601d415801720300c00b000c039121001241243c51445600000741102034003c41c5801d9865003400000d620618810041543d1f488104100400f40c00d140000540da901c00981c03030b418141018454664080c160038480c4812003000700282c0d8011055951040d05800e001440740c415081400d01005000c1c0448004215080112216a01507200c401900d0180904201150700c40c401683d5030b200a0180307660240c01c06e1521850280140c004c0e001558000d040801c1140c0d98800c030413000e055200f200e0fa40c99454211a1995040421405840004120010f070050042030040c4000c3c548600880f40055180c11140c0c0540d00ca40040f2030b00c5200301d0309041d071280307171449000f51264602e0300210801d003ea40400103082c02130700200181800040420480e4a1a01c200c4801d01011410300505040d2160000250605160841451840020070260b61106002c080501711081c640d038041c880c03189104825841e8661270f078240428414540001e000c240da017007040c5c1c03400207411003030356440c0e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 498540044 1250 498538794 498538811
    0xa061803140a050705030105010e13140a150510030312020705010e03070605070912020916020a061d160803030c0f0d2d090b161202040b03101a0d020a050904 69
    0x700014125400c0380a03505071010720382c0701c100305403e9030b000780b2901200012141c082202883e2a04071208050310030300840d40741c140503c6160381843c6500703009441440b1440694600c2a95a01985a0062040305803101c181d040d0340e00504000082e80692281036030115000040010947c400035000c1c05500840c0d1f2201101d2611001610045404000007000f2120008184007015006001264004c0c1030308459943d82809100c20140107551078110711a007558030002c40c10718030500f20f1740d1601c10101503524890180040c40c048551406040c0708000440410040801100781c83d0003480099a00781d4543d0000d00515140c0520030310000220b2500c5840c0f041700030407a843c00003180c14452800303c1a845d101d107800c212541d83c3c6003c0c000c00140317000100c15058214041c0350300c41042c142340600c1d001e02103258040741c00ca03400c56071500d0000001d0058903d848850a0018a070040070080e5260a10810f0780150103600a0303c2c0c002d0380c000c00c60102803800f40d0b081ea2007407140038004001990 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 498541294 1250 498540044 498540083
    0x30a060f09050c1e1905120a0b010816050904030302121303170f071416050c031e07090902010504031403030a0e06010f0501051e03011707050f0a061803 67
    0x40c41500480303541c030400c1200c1c0c9480c140540c0c5100e000070482c3c10411350700380000c144000c00810903120300301d0b98046100810349603281c00302c1c81d4503100b55000a1200c40e00500d0310300c84880040c0c018a0040e88076a03092001043c600e05407400303581d010341321400e080d1100e18013a80680500074144080143c00b030204040301c0205108411058041d98803e910021544c44140401d5001e903408071003420298005600a80600b0540040343c007010303000c44c6480040090a2802890001c048030143c011141d0540c0520b01004880d03141c03003441c04403d001c8048564290b45c0e400c0c0030b1054203c81c0d900c500d460702c00d40e0b0003501558001c0d6040340b00001c20490750802291030742d204a51001c0030600d00034040000e000c0024125041c0e03600301b0b1104250600340001511190001000c0304d502031740750400580c08011000181d0300914045524800000051801a0601c8070795007241d070203010400045005540c0e01500e00080398440d080c040d84084951a9841d04800725800c00b400304400b50828081c0c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 498542544 1250 498541294 498541301
    0x8030c0f0114041e140610140909031c060503010c030f140103021c05011d0604020901080303090705060306041508031305060316180f0f0609080327030a060f 69
    0x103995040c002c01c0103a46407051500e0001c0d0a41c2c024000007089840380040c000121a042c42445c011003d003070341c91142c0300c2d01500d4410116001d20004140300020000c0c1e40081c50240e1441030701300d841e15010314000d0442c5580c0c1c007850500c040b0391032614401440701c0029500c940058400074009100c45400914058040c29540c82c144064618101c1465090444d0a2000b8166903008002c9811005204111085a441d0581c02c0d10b89541c0c807011240407400106064807054030110140c80640741c9401000943d500c160300041c181e41081041088a110128107801520011507444d5181e0300c424001c00e0040a00c000381e000ca41022000100706400d0001c013402c2144040c2d0f880c00402c540b2070302070001c0b070302041e03884080300e04a984582e06214090f08036a6210300d9140050038409035113a0441026a0a44d0321034000d110300410203000c460b034880c08820107000000d004503e044001d02c002c2810700c0745c0780d0320319030400c5904c03012004540c1c05011118038150010810b020400040d07081000a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 498543794 1250 498542544 498542563
    0xb0406020715021e03091203010e0f0f0c070609170c06160906050f09010e09151306030b0411040f020406021606090f1404020d0216030e0118050d0c08030c 68
    0x30a03000b0704031076401d104580200d6282c40760036249200341400018141500c0e0b080540100190300580000303e40c900c0341030b8051070080035a007020401d182004011844109006881034412603100c03c00c010740d0408017000c546030594041f0300058040303500c2c100401c002641020281e124440052203e101000008160380184820904541600f90f00001518908954800c030130128500344400c1d0090680c40010b01105803040c18984110f5035000001681e9082c215568900f800341c0304424511800c104000c1c4a641d44000010020301303041d5281c3d007140c0038005200414141c3c1c81c2501c0304168540d070b041a0003081c91b10b1070039501d4944868010b0740320f00d40e0841c00700542e4009080003c5041c8200540b1048495a0000420050508440c0003c4030605403419400c5a0208030300d140c10394152004203003c0c01d8488a40414000e24030f4014980320340b401c0e12034100700035071151018845824a4100848400702e8442d07044100ea4508610701c03142c594803141403130001140c40d190200c4085503100d00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 498545044 1250 498543794 498543803
    0xf031403040308180619020306060702030115060f030603081c0b0301020c07080c0d0308071b0b1302120105070504090921021c021507050702030a05010603080c0f011a0d020d0b04060207 81
    0x2c1c84c1600500ca50350b0101140d41100d580300304080200c0021059000799046040038080c2d502d060450f8000c40d00b540d25854501418924862040104c036600522014092074946018000c0380d00e951141c940b580120410b0b42c003440d035482300b030401c40354507507205030018200a4001c1d9121040400d030301351180d10f1031040010f135000c1c01403a0980b40c035000c05d20301425940b680317a45089880e0702004a940e40718071001454004490040b403c0800c03005c08405100e07c158005c1109000c0d20341c8180200c4a1101c110a5441c0c1c1c10a410b01c042d032034015040c4c0d02514454030001617410100d040001c0c0382c01075542c512100c2202c082c3c0c14045240d0114404548e46141341540c5a810340c1101c0407a0345450840b2441c240075030031404903241a214200411216000608070346040000c2d454940c212071041d88221000e041c0002c0c03040c05600280481001c50a18000070042c4445000301d8040724100c00b84003078401e4011502010856507a1910412900d070030004214071860300b407828800039030002d0010744 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 498546294 1250 498545044 498545071
    0xa17150406050f18070c0615050f060c0604030f050409050405030a0e0d03020c150f1209010f06030b0f180a110102010b0a15111c05040504270f031403040308 69
    0x34a5040c4a1140107070443c0281c50351191500381100c2c500c01a80190290b01001003d68202000c40d406002e40100e905691b00342148a524103c2080400294080118014002404041c5c014003020954540c0141c05040020b5000d20490085a55209075002108181d2600c0207010078400d000001c0c01c0b001307101d07451b104144da651070100590ba007580c01d001070041c2d000c40c1d05850789003001c1924071411949046e54901b8801d00d0300082e20785402180030203a0b0307101924204401c441007400342c1291401c00c0c4004204c6d980c01e40c3c9a07a03522110084c240d6060002c9680402d1000a48103c400104180031007625510011442c01c0d96500c01c25a54050056007032604802c918907000c000881201c00c400407601004840d4401038481c04048048200745004160307801e040303192110011104030506a603290358450070076042000f00d030300d80d551390122070000b4003a00308000381c40d414020f151500504a0420000d0900c2d00f241d90724500304c54803028400110030b00c800c1640044072140039006144019 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 498547544 1250 498546294 498546299
    0x15030e1006080304090b0f0a060c03091a120c071406010315050c04150c12170a05012d03080a0e03241303032c0f0c0a09020a17150406 59
    0x3402a00c4160040c01556002000100b040301c606502400c1c0808024015044020060b00002c0b20b031030041d4011000314046806010800d644402805c0c0900000c0d9040d042c11004440300145030301071115003006414a10010070000900c20b019298050340c0205081c0d0900d03400b00c032107034481200b8401103a130302c24400c80ca0102c4040a004562040d200e5000c801d042516040000d80c9141c408000d1780c0620090729210070110708900c40c2240100b0032510307144282d0105203446503050000400d148c0103140b0b80700041c04130302400c001842ca4450541d440540414020b40c046c44400c10b2988014102d1800262406405402903039442c0641c000700c0944401c2507042521000c6854030190b132940c40054800014107051105c25240c549a0181c40c1c00a09420b42043c04019108c1c20021100001503507424400c4900c801c000800b07118841c80c0141889460b040003080310801f0500500c100e103600490000720b40b038807555600382c3c182c6034604540c0b041c0c148059209800b80480440502460412501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 498548794 1250 498547544 498547573
    0xc0708030a1205070509130501080d020c0a0b091f0824010903150209040908190903030f032007060b03010608070b041502030903030c03090f1017090715030e 69
    0x1519010103a80d01c520115590b80140c0c00000c003802400242030000900c0200020b8a40b56501420407210000006203541414651450012080c3c0c402003154054600d620454480c0c060503001c03a03421907281d5448801c240c0004130989881c0c1018040c54281d8005084021390240352107000702004050241039080600100c001a00580303100c0780031600d01e01d0100000366808801c0099154010b074014100000603002070280ca200020984800601150001c0c0301010202e494407041024104100c0d564038540d009419581c2174003c100c145a80d03101d08443c41c1194a40004420900c9520a40e5809441c9030000c0100301006040303000c0c0d86004004541f90000040c0c02c020b44518203865418640b40c001d2544501405440c09802c42c041803044220075102040078100302080704000e161500205000c1c030810103103da0900e44911100760002001d9504030032000e0700c0d1555402000e1031603480c1004146404043da010013540320800000c1a4410b6065202441451010081d121a078850344174 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 498550044 1250 498548794 498548797
    0x2010b18070801090e3f0715020901080117010f0c080709060e010c080c010b09310b0a2a020a0b011203050a0c050c04050f160309050705042f0c070803 66
    0x405d041640e1180d584511840100f4510f01290382c1c517a6684021000903440c001440c2c450313017079004072805001c1018410020148e60540303801c42c102c1c60441c2420a0140028110801846100081c0b5481318602d5007500c801c2d004401c85050b001c2080c4440e1500140040c103101d82120b08400107640e031000869403034840e815100003d0740507515200500926100d401069000d00c0d9811140c3d9aa00d00c418207580354040b8180c1b144800920a0400c80304440913071002000c01f12405001900c4841e4000004862206da1a0004010b00f800600d042030301c1c0c010103041c1031b0203520f040c80840c0c4602420140e17500103840c4610911039041c20146e0f0b640c40f100506c0d40780b01d4620040120782c00b44902441783d4421089084618003132001c680102041074085811a20107840e0001c00c0703c4650304020080e80481c4c5d400106400b1446c040014030701070703100c05890b04613030b010b031501c10380d210348a45000015001c09515441c001c40301c140d044c1429800040200ea02070020018035015610001416080100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 498551294 1250 498550044 498550061
    0x70b0604090b0c0c0715050c12040b030403050306060909040501020c0d020708120a021207031d0d020f060d020906030c1e0a0210051b0a030606020709151502010b1807080109 76
    0x40c240c000584800c0c0f11800680c00440a904441c840c1c0707080001c003142180070340d00b6071100d030f0b8588596803500c840302a030405071500d450000ca05010003041240810081c112644035402d8034246850303032070340c02c000344452080c00c050640c07000c010380c203020600c101035005054030044081203807000c22500500340d841c3e0800c0d10505a282d0001a04405154014001414464010b106503400c4141007079040585801043c000c0c0c0019801d01c5290385400c595114412050004440e1110000031a5000074803001041042501a41000c00e00c1002640c8940549500800003000c4a480c0d00e01a49214207071b801c00c180700490117290b00c88407082c14481c8801c417001c0c1c100581c0030b08000980c8003229006480040c03e851907030b0749100815014604620050303d14840d21b958003085503881e0400081c50000c2e10b810060b2401d02d40202d43c4540c007003c1c1e554408070341140c041c8003007029040d80141e004010149a25800607042e880c610b048002007208940726420585600150342d0300c80481104880116 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 498552544 1250 498551294 498551303
    0xf030a05070b0d0204150e01080a0209102d031413120c051606200606010504061110110304060c0219030318020a090209040506031c082a070b060409 65
    0x440c1d060000b07022035070040003800400c101c0540781a6440401c080200d02481c0345100140003000d40080b5903030701000103070708170350750410560502110f9400030710b000300035110800c18800780f004040a000000d40e00d50300030b811401480c2c4030b502c0400c000500902092002c09010300c041c4400580040340c0c040c0303c4682280c014070410300d5100a030200340c403000c1d0284400d03141c40c481c02c0310f43c00d003c1890720107510180c00183d45410403100414105609048040c005e448590410382c100701040c3d0748682035404544140c54894910302c0c541002a0403c02e01c2c814044140303007040d521060007181040154061031240408204d0380015910890b03c4080e0300c0600c0784c441c3c0e817900e840130200c2d1007500705d050f40220a40f00201c2a40e259400921105259440343c1e41f1a500400c41646a10701842029400a000d601030b00e0b001e4960a00700621303c500143c0e03d0113000741803003c110007a040c042e900711545081e1620f00140b41c054092490183c0100c001114007550780340000e111414180100c0135202d034030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 498553794 1250 498552544 498552553
    0x309030405040f20031503071512140613020d1503210915021c0e0a08070e040611040b070c050406140901031214040f0f06080708011206090515060f030a05 68
    0x4d25043d503a031001d00020303c0214061404a440e036400c1c401a001842ca400d4a020004031684001d000800b0980c10303541094540440041c0d40800c07c0100303644201d04541102d545512544000021b0003a016154056841d21150511600302c0b00c5a82054030300a420301106010601400c0480380380440c6000c002405154080114111030303000500014014015a01d8882007000103221022011903500006100406800302605102a500c8003400d40c81010b4549039081007400c40c02c00c2c1c0040c1000f805d40f95250828140b0b41b1045082c7e074054560381000d280d40713494034208120744840a0046500c22803805200003030110703081164500701180540295840e03880c0d03032501c42c3c000c60360076040070500c000caa5001079140300c0240208041c042c800640407105081c41c0b41002c08401c1d50301302c20b0a01001e1418880d00a41004215044a410000c611031407100d918103540504a800b0009109214103058251b08900460109103e41340030b9035901c0c001c1c4010401c051f580c02945101a116412 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 498555044 1250 498553794 498553841
    0x121314030a05041413090c03210c08250b270d0804110a2306161e080c1c021902061b060712110901091401140309030405040f 55
    0x6504020600310003401c05d61088031a500b40303401d0311b0a480d022640d1520002060080191044428140250240041c00308103000c10001d06022000301000d40f00d104086496401c0d9509015082c00c007031035070000f02112103410b1911a190820940e80050411046070200c10000c02c00c016080403000c012000b4580421001e805540300400a482551070311182200c2d10200d48801c401d5400a0400503804c960210013071425076a083c501895451140d207081020b041e031002c194801d04c102c1c1d40c0010700003026143c0b403c1c103d403210f001d81400628040c404100c00000e0038020840d114070314004080202d0342407450700d04907282e8019151404040f0030305902ca101508000003c2d1541543d44c03107920040c00d10f0510342a280507800c0314a034000512510311804070b1009030165a070a180c0468080d0305221365400080c05a0f1860b0280008030f03104010083d0b030503031003450042482c0c884e003840241c6d00d060112045031254018044c03180640d06101a101b601c00d1140309407480801c51148045440c0e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 498556294 1250 498555044 498555059
    0x6090c0804030905030d050910030e0d05070b06190b0c0f06040f02030f0f100e0a1406010f060305060603071202090d03030501060e03210a02070f0f051e030a1502121314030a0504 78
    0x4052740c0d41c8004242d0382e0004803481410400440c00e0b080381e03030b072906500e5808620700b04610b640c2c024489402100103644220210000c10002c4068070000c0540395151440c2403095440d204070382911417010b120300310a02c0b00348002460104511402130f82640c4180c02616002650380c0c2d120400f07200780303601c49180b03921801051392145540c0e148400a680c81c22810381c448070301041c540b8180c0300d00780d040344004219641d1043c410900809440c00c0601051400400152081c000100441d041c0300b00e5040c00d1400302c200e6030440c2c806102c0100f60954150032810000c00410382409040049900d03520300d40b400e40ba000828a4080c0c0c950603400e04006180840540d80381c00c00c03c2500103500c501100400c0070f110b0800326402910501c1109060301d444c2604100c003280c004120b448243c07566144101594401042d0b01c0d00c860b1300a82c0d802d0030046284810b00092040e001c8002c01003d41c0024030001400e801c0304000c400340540340c150400f0401503203141e01c030b00c942494207001c940100000c00c50305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 498557544 1250 498556294 498556309
    0x24030203070216030602030106020601080a05030f09010c0b0a0b010210291207060201021c02092d031e0f1507080402010311030a021c0e070b090406090c0804030905030d0509 76
    0x12007500c1a66840c00d40c054600d1200002504210381060b008001408003c0d4104541c1d4010301d609001400d0560b0755454144c0c803407050115001c2100d034005002d2105034025880b031210250f00c003040803842d1412004590040c02000c6446005020395031721088445428007400009992030305080141d032441821031648a200541d00540000d4890350b12000020144100801410780c3d400152b0303a80f40d104a281040c4080c881030000e6144103000f08260b54840d240c048540805102108441d00c202190203210b01400704c9a00d98184100001d1228104502301e02000503030340803044407000f05045a085441d008191080a0300c03101000c00216081e208086d2150003900605000684c000b280c0038201e080e40c0708440174500540c00044044451107944142485500e0b200000c10100421080030740d03c0f02d8980c4a4001035a0010441007210356076580710b0002044c494404000f52007103410042d10080040701c0c1900450490702c40003406e0b0901160340344040c00150368a9103170100750010010700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 498558794 1250 498557544 498557551
    0x90b09280216050f070617010e01090507090b161b03080a052b05060f01030527120a170a061202060d0e0f0f071415070807050102040603050a0624030203 67
    0x2400c040b90520b5001c16001d010781c51a0360803820141c0050342c2454405072841100369100000c042d292070040140000f41c150442c19035108550105071502d85110803070700c20384182c00c80031001400094000d03184c002c44015000e158815080304071161040c0344454200b85640c40040c0c11110108100102d6610843c01170208891102c03000310192001c0315031090054a03c07058800d865900c07410301100d840c00e80151160000c0c2440c09020600e010360184041800704260b02c0741c03245c009042d00388122400d005003480d00840103c41520364100c420001d14421000070100304000c4101c01180c80211135004d890140c81076590003800840d0741d5800c3c050142d0120b40000e0304907694000c50100c04409102013054420746200902448206202c004d080444551008c400003520003901c1440e610f90700402403e448880107226118082410580001d106244004010f0352000602180103509940014000c203042001000301d0303603c51820065842e0b00c60942640c0b020440c1d00500b0491207600111360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 498560044 1250 498558794 498558817
    0x4030303020c0a1502040905161e050714010f050112050d08070e030f0a060b010314150103090c06020f070e13060f02040506040308031510091e0f090b092802 69
    0x1000143d98440c2c0d50103029145040c0703400c41d000a41040000d104c1e004198101009844102c910390a008003d4410041385510100490b074240f210441c042c084e00507510b500303400450a12a490006030b18038024007881407103128036441c001c000f141254019140b11151076100d4010038400b0062001912041401004030003004001070450741c058800f8000480d980b0010001440401c1d81f03480c0c0076080c2d407402402141054a480081d00848600c00000f40e04800c0c2003804c1410000c01600407005031030703001c07005444202900c00000321750f50300046a4440701c40407001d44d04003a0322201141c294800941342100441e09428800000c11b0341507000400c0b103184dc10340186465540d002040705900541d005680d081c00200030414007603100d40c00041d0f141d200721003e001e0190708031406002800d25000d4003590124042441148400c04d003500c0c800780c200c84008085190340c4254160150442103c000d00039901100420000303c170448042c08020b4011030030444040700d20341414000d4010050204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 498561151 1107 498560044 498560053
    0xf0903070b032412030a0801080706081e1e01120309080303090715090806010e0412170c07050c1c0b0702070b090405060102010b09010905070e01090b04030303020c 72
    0x3c2c2c19402c641c00c40501081010000c184070583c3c14100085620000800003006034000c45114100c450030700072a8100d40d26048100c50390081541d100c4026075031001c110314507403e90810650700c00d1000883e6201e450041007591aa50401e90060b54940f0110003040d09041d440690b0304041d1428900561a604285001c00e9503071205e48509a4802c2d01ca100011b4a239109401c9000140120740c11620603585900d1600b0002209403030480382602100302c0c2d50220381c0144848040b10100040c0c3c0180780c3c2d9400d0003108142c0c007484044a041c000c00e0482c0310b280d40c401c144031049206524640c4035410b0305260007008140098502c40555000407003c01c103950083c001c81e019924180c4021403503855110050b0302407d603418102c0d074841d02c0e0b00300204412030103070302091003903190b659091103d441c1c1900541e5219824050720f651124100014030110b13010b03400030120350b50b2150884 = true := by decide +kernel

theorem cover : BRFrame.Cov 498381294 498561151 := by
  have h0 := BRFrame.cov_init 498381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 498381294 ≤ n) (h2 : n < 498561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
