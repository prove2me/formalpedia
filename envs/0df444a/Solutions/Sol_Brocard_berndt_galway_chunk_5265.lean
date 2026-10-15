-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5265
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:17:18.062737+00:00
-- url     : https://prove2.me/submissions/22a7175e-7892-4ef3-af04-1c2452d3a8fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 946762589 ≤ n < 946942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 946763839 1250 946762589 946762627
    0x60303220f0b0c37020301060b03010902090f060f1c0603020d030804030f031505040218041107170a1b080f03040803070f0221090406050333161202 65
    0x1110030041240410f8032400d0160501203851400d10a00242c12400b07184204c035200525620340c400340d414000704540b002d502a902405100004544a40e910715616000c0d5200c400824010319001c041d00c4402e05042c81621030070030340c00036074909010900c460703100c400c8440f5206181c99600d4090010241c1c88a001e90f0400900035030301d44c0b52500e0241409130800704031400320000c141c0f5005400380c1d030140a05030113083d540c0413540981da4100100c50b40b01e942809546c036035800740c6803208006510740008000d01c1d42d94855100d1200d440005015502207026007400940800d600d4600901d11001c40c0f40211811846201400e040c850701d00b0315844a0b030000c440840358580b0001c180071500b500556140d5102c00d1a01c0200150800051100703d80c1c00d40b001d03481a0b004020625805035560341c1c0002c030103454050101c1780c1209029207c040288014050001c10009582c481208410700c85507a83c8110b008401140e00e0701903001c3c04550507080c0c16540c0c1d44195081c083d08580e52200b8501e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 946765089 1250 946763839 946763849
    0x40302010902032806050c09030708010b0a0504090c09110408010e1b09041505060d140a0309120c0315090f0f030e0a210321050a060509060303220f 65
    0x41c8000c018810725162446000880c02e1410004902c0c125110050301041e4449621a101080c21b40b14005140624000e03112030302d40c54029600049034031201503101c04070007181201c11240c6c40b5550400d100813600400d101a040c2c0d000e03028140440f1940350001841e5a170780c5000c240c60035030385480160858a001c0d001c00000d811044440403420042161091880801c071010310b09402d00340d996451410202050021403501c9800054680d9594140310700c0d0300d034002c400d93f00c90030b01d40c10a42e40ca03410164821004143c880d0804a028484016540607031030313025244203445810b5480f5911031070200c2c4490f82982e601c070a0410300040b04400c40c90001d92282c803407515403804903d4042c0c001d06048070700b5401040440e004004160001c02000010000b6004600001c002401c0840d042c00300100a410552414920030040401940c0072512a01419000708149a2280100609034034245d0304558113610510101404135109441d550030242d000010201740d0b555151000020001740e805 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 946766339 1250 946765089 946765091
    0x5040b0a080a110a0e010e010e130f0c031104030803060f04110a021c05042c0103050601090605030115030b070e040f1d0703231f020403050c01020c0a09022104030201 73
    0xe12042456074055050f095a4000b070035401d109084600515000030b4001e00d030704100301c0321082511a4003a04166140c500060005060003000c1c00301403000d04860304181a40e130340f5025000a080c0c0c440c2c802c0d07903100f401c1c9118039843c02e461030329021019003001e08016481010102542d00c1940c440c803603030a119190350102c40e00ca241000300030b4207009a4140690400c00034201110300030794000111002d6a0706540c0394035190740b04644440c044c0601c05500c940041c80c080010042c4000020124121402c40c4801c5c800d05031141b040c907007a03429800c41152002c1c42850140002400c1c400c40942c026000e1900102c515074200002d005d903840c81c150b00c240c0980c0e0703101040e120030886440004003582100100445d51540e034440d03e001c5c0d40c40c0f0b01411200c584107284d4840140511140c1c15142500344980101001e85252070000c0d441403000321228820011326009550004c101d00011180003419031031010b1401480002039880010b024400d48440c1d1401220743d504407031081d0186001e680 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 946767589 1250 946766339 946766341
    0x3082509080d0305010501090504020a0c02060c250302010801180b0406060807140405030a0209061f020714010f0801091e020c0601061701181508061501090f0b03130305040b0a08 78
    0x1c1d060814003040c60300c404042c00e1500501107640c0241d034641c22241c090b02d0059403603c80540c02c41d00015591130007580316400140341001250001082c07448000d8001039070680d002010400207800b4050f20009002c030711402c00411140c00080b464a80100841c03101082c800e21040000e07040743c0b803d8124002207400b40b01070040c1c1990208004d5180985c0107601c81c03506003814002983c3e0280500024807856502c40060050f0320b95034200c0d2034103e00002509c0c9003402c400b102a441d040c00e030044408140031501401d1040d031040385404c83d1840c894903125440e03400c0c60010f034060140020300201c1c8002c1120000003d0702c039440240520000c0c0070281640b54108680181540401c03030090900c0c614600060008049028200300c802d490b0fa4400500d01421150141c04186281d1220046001d40b400308450b422a140d54040d81e45000d9032188a000d13100e00c0303004d180b01910f00800c4a44141440041c008802d000000c0130303258020700303003582440e40e42d280d032540961019400c1b100181100c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 946768839 1250 946767589 946767599
    0x60b0c0a031407050a08091804060c030f090f060b03030f0d1505010221071a150f04150e0c0d0617010b010e010e040f1103151804030c03082509 63
    0xd1000c0740218102d074045482d25166440ba5a0389416102d00a4265040043c64222543d10501d030105120607144404081d880c0130b06020004204840c14440401c0c104150039840c5541880380480240d0b1002d52002e80032800d45880c0024010704503416014030080011040c4200840b003d0000c2c1e12000c040418161081e02250440ba540c40d40a0344c10344d03000f1000d0022521103440703481440f0b101040c02d59240c00c00c0b400c003640c0007456441d00e0105c0c0c3c1c032058140300d1200ca44040b01e400d40c9006691000914078020280012184c1111503202c0000782664180540189091a2500100d242204500b81a0844904812100203070702001100c0d01c420311954541c0c130213010305030040400f404c00801c8900d59400280112101e0907440f031150343d507040c001c42400c6182d4810307900b59807401c003d00e441e8070346164103031078004a02c0707991442419500034000c1f030581491340c0544500d40c1603540f111a903049660a4880b604094030342c0610385095424850f485054200121032100c10742d851070f401d00c1c504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 946770089 1250 946768839 946768847
    0x1d03070519060905060f190c0c321c0206120a0e061b0307031d060705090a08120a030e0307051501060306090c020615010504120b0f0105091e0604060b0c0a03 69
    0x1d44c411402071005109007515042c0c00405c0c0d0711110f140e000001c824188620080b20000c8a8281c010103484004101154040703807a21076400100c1842c01002c0d681c01240d01558100e00c0a2141d04e500c1400060301c1000c0c180018502445c0750b1010f0b0810b424078507580d1114007826001c694409585a07101d0292402d96400c101c940c0d00303d52000301c8e40180240200b02c1d5101403100500413024541c49103510030b0042e902d510818100651002603078680e0070004030090290b400007400c103101d40403109006c1000329011440089044200242c1483c1c1a0303142c0c4c05501814102098410602041c041e0b440407840900c4408008540c08140c50301643c104800074013102c2c01500010340d490b1174031400391320031900000d596800c0700c0e441807261003e80202d00100d0b0035100b81c0e00410382848e00142c03000c080000d150301c0d0a002c0d254480154039244c3c1c844083c000e41c0c060031180000d080f01200e60200c0e004940d1407100c0e800c180080d00c0860141c2d1103003444007035030f07000030844040e0b030344009004420b00d944 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 946771339 1250 946770089 946770107
    0xa0210030b0409061a010e221505030d0914010f090e1806070203270d230d051c0903080f0406090807050c12070f050618040618060b0a1d0307051906 65
    0x4442140301c84234042d50040c3c140c00358525402440366550f401d040c25042602d2044010a0003c0c12a50344030041d80c0020040c81c01403040031809100f0307144140c501e40c0900b102e9500c004c50740d03440c4040c49140005944e410440541a8034000c641c0e0b00d81000d50780001e008070b61107411113800840c1c0e1088102084620350000c4142440c031440c583d100c02650ba980c040d1707040303a00740d0042e5400a00240c403000f15041580c05558604043c0b241c2d11b224070f0003542243c042c06020031405121035012001d11308c0103040c0c484039000140000d1440000641c0b0060031031003503801500503400001c20050300d585041c107a03804100305880d180c0c007070f07483c80c2802d02e80708205862000201d00501310085c6072419400c60b44109001d139510803240400c0c19050030781c030318079000c42008008105010569449000500105420010000c4682440c00105d48a1170791030450f280c1c818035a6600746500b66200c032800001e8590042d10f41e240c081c14030001040d944a02d5098417030411220401d2002e4681480900000c03a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 946772589 1250 946771339 946771367
    0x206070c061b080a031a0406090c08090a050d080426040e060a150309140106060804051e0c011d09010905091005010b0703050309120d090b090a0210030b0409061a01 72
    0x98402c408001400b01803c0d101100000d043c081003508400c0d5029070500118511150424506100003680b0015500014102201a00d84d41040e450b40f400c155107a00c0401c001401e145e0280c001e43c03445511461781b043d8468080c0d468005140080300c411402038103516894405444045000c1c0004071072070f241c298021408491a09509140200e10911400ba01d4101c070107059a80d440c034024046128900b03000c11490724004c11030aa00c607480602010029142a1143e01c02d035072914003651002e800f10b649900511000304603030401880111504042c040098000c00c80045105210340c1741c0c443c14601030240d00304042281d2030400001e901c1c115030600340050190606004000d1010500100d50020b900361030195030325582c02080c14070380322484070346a60300e0340009080000303484c85920500c0103030303c1444810082d4503007006480c0d50300c02c04e0304040c5d03101190b42c10b52414140a5070080d045040040c001040503665070710b81c0300441d0201908070b02500f0800341c401080d90382c0400c5102e00340d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 946773839 1250 946772589 946772627
    0x1109040b0d0f02040209040f0509060109050c07030e06090a17010518070f03020f12030c030d0f0902030c01200a06020c010510300b091e030a14030a090206070c06 71
    0xc0c1d915264040b10450792031010f40240d50000d0340c640355450741e40086e001c4010425060146007070040d00c169445100f4407a0117145840d210100300400d40900840703c1c407a802d581c421101c0d4240d801004a280d2141c420150700180700c0302c00041480c11030400c000e09004940c00064a032400100383c030f804d4560240b01548903045a00b00384900314108910505498064131008103000d13036200460540311000080308200d22011480d400a280c00100801880c10940c01c1800613255204029082d02d08264000758950004480d46480c2d5105a500200c201826040c03071100b43d6107804118141704800302c0c25074042c0d030000380321201041c003400f8554009210380090440c0a140a542e00413074a0450407681040103007007011100030110b1081080c4058200c1c440030a613041001402d42d80301c907490401442030144591104030b0300b101105944111a09444440600c03100c14010016030340001c00c1c0c81c5c12140e90303000c5e031409a1244001703812a584680c0141183d541441400f900380c010b6610808140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 946775089 1250 946773839 946773859
    0x3091110050f0d020d1104031a01050d0b0a090615030219060203031f080303190c0206010b0912010e0f01140a02180402030604200910050f19020304091109040b 70
    0x4560000446500c05000060b1503118542140c2e40b401a210704009241c0d41810a45030032452190380c0c005004a034410394410580b40c248000650350780000344134880d40f040ba412210008182103180c8158008069000054000b4403aa80c94044500c845030354980032a00c0013051045052001c01148048000601c0c400d01c0d614110000f0340c1c3e0b10000705480500314581065081c42c04603081d01c0300241c105000ac1d203840e0b00c0c0607083c1900940e60600384410890a00f210305d18064000b08645069a230840c2495142c64104404e003c0c06030300c14560003101f9943c400914800c41001d00c50482d038074200f0000491691041c12103c5041c1e10302130842c010307051042010f400724814844c25448000d80c1a10b002d0f850303580712800100103090301003000c50361000e040142100d07418040010314090074222140317222140e1402c8103c0303090060305e0714114171010401000c400c14641d010071600a21041c8104c038a00398542c40d640094410320200a03c00f120007007403e0703031030b0b2919010301600b00d01c080d1450740003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 946776339 1250 946775089 946775119
    0x10905070b0c1507180b0705072606011202010e100e1e060a02010c09091116050c0d14070e041a070203130332060a051f06030911 57
    0x40328000d1140c003211400c006010034000b0342c2480214484442c50112001c2403414200c040e0826036a81c01440d0010794101d4003140c80d114800650341000c1d0000000d1484038100b4900b0710b00c034a42c10a00c4854114000072241c820501008428080c2034100b6045900e4902c070701c0003615000c41c80038003d10407200d0982c0300a00c55805104200c68190071128030421015120a4020009100e031441d038000d00000744885015805420070400841d8643c0d90950b03c5940e0003441084441d8602c07003041148003001070035400c07114048241c9500c0d010354142c07030b11018183c00145c048040303980200c0b80c1c4c21602400c001000405d0005800412064503504807510f0035070345240c405030720480c2c1d06030400c012901080b08503100b0010745d042d4a84250341c84a486442c0d0410030b80c051100c004c039520390b41551060f85c04401c8180614034013514507000505194840c102c2850142c20020310030b1041c865040c410a05400710301d402c0c00d004201a850008d2058007506008502024481446014116018899078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 946777589 1250 946776339 946776343
    0xa0905040317041b03030509010f14161104052809080319060e0109141f061202070f0b0105120f0d0c08040b0a050901020d0e01090927030206011502010905 68
    0x200782100d140d50300143d0740e034a440701100a0b60500d005a1000c52500881015041070080001000136261243c410301c50000c00c59140b0481480e418034034a06001500410411200109640d0700c51200c0e086030700303418408282100e4084890100d040301e80c1c9503d110348400da0700740e400308040c1110140001ca13a203449414180c4400741090030081920707001010000201d84c07080d0040c00e4010580d240c1035940314a120040e202d5001101000382002012841401d00b404a1b0a40d0b990210181803000389890001d07251312203c140342614240d000c00c0030074000f030f600b0300441413624411741c01640d0340c0d410481070240005861712051a154456440010701d850002a0340d21120380920f00040c1d404d440b450882c0d510300642d80090b030440c1000c54030b5040c2c030350032002500302c04000f84d0844180e8844140f04503600503580d038005000c030748008010710041607690042600e001100c0403080c0c00106400715414030042d2160203400581091005124020b5402c21107900300c1890f01c02444a10703038640f00c0503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 946778839 1250 946777589 946777607
    0x2090901050105160f080c010614030d0f0908010203041209060206060117090c120114071b060b011e0315060e15091203040801140a0e061b0d0606020a020a09050403 72
    0x606101000c124102c00c0c116024100c0c040c40e920811024a6015a2070716407559001182d4800312035027801d0012039250b080c004545041d0b00014000c0c0485e55083d40107071000203182c84507008002401401040400090000f0340c0240c3c4030704440e5081140c00c600060550300507410500464101605014082e1707485080e038500b0b0424400d24140c5d54481b5207203140340006207406660484001543c1180d41c0c60190b0150003e519890206070007651015000c0301d60581058030002507000500170742c0041000c44e0302244010b4418106044e584404500c0d40e1a010719498581c00040d0310391070034041881071200c14400800060400d800500050780008040c2592040100000d08012420007250b43d10390350b03441c13030301707541c80c01641d9403941c940701014040c0030003940ca60920781c492004223448884605c1040710510100001c1d01d108c0d00d035803450009854103144550702940c070600035a111819030344600d000070700003a0020111110184140040c00c550b40d03001d00c015920309010403001c41c0e00250a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 946780089 1250 946778839 946778849
    0xa060c031403131101030b0a09270f080a1b080a0e040c0c0201140d0203010305150705090d0308091c09080c04060608040215040b070309170703110d0804090509030403031202090901 79
    0x1204d100d4003407001280108035200342c0c10b6000341d00c6a4001466042c0f907001c40111415182a01200c484508108614609982c002031102610001020110304130002030b2441c4611454003079085200800300c0100c4521002090305e1000300095503030065504410404c0000009a070280402c0501d41c03005407417500c84c0603019061003009107070034440429117001c440440e00c117000d045441756140d090143d62a116900070140140c01c18000c1400c0d140100c051300d213112001409503095016a98048074110005444410700d8072032400c003501141c1021804d501c1201c20b5580b201d003002e143c060403520b00541e031f001c5180640d103000818443d040d80300c5941548243c040d201c00e644001c400c008681148581d40c030181c880300c0003058410802d075200c1e40300300c03c550584165101496040ca03c0ba502d41c40c00e1b1000070220350032081e07a180ca608000c2a003480460017030501c141840e41d215032100c00d40d503048031400c41c503130000282841015008000c1c03844e0500112000c6040c04a00d40109103134030707818010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 946781339 1250 946780089 946780103
    0x1b010504141c09120614010b22050901051c020405160e090c0a210921030b0915030a05190b0c03091b0d140705040b0607210e0a060c03140313 62
    0xc940905c505500901980207480121501c690783d9425240c4c502e411000514520074900408000007103142c1c03c400701a1000205501d5250b46007004004400f03250410b24038003200680c5c58140035075540c1c8500c1b0f10a104240b40d11802000c20341d0014441c0c04d00e51301151041200380306101200c5400c101740d607400503140c1440c242884c09051482a89000080c00c808400d0a01203680304104000350411803108056003034007000f50791a5829800d442d096a00d0580000c10b040016030901c0400000d0b464241001c0c0981d45a8807103600c400703007032020215000c01070b000f0030108041040341000c4050b80c000c00300c03003005040d410b03c200c03156192100340d444d10361814440c1412034030035070b00d400c1c40c5012030354060a81d18003181e05424268980e8200d102d04c038070807850003004c07007401d0901c2d10072940115800300c403000581c2c1164001c480b03040303600d52200d010031900f004054280e4844501c028098081d076101c00003d01014900108912118490b42003070603c00e0052042401d80440c94402050740490 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 946782589 1250 946781339 946781369
    0x3081602030c0a21020a0f060f0810060215150402071a181e070e0f0907060e0105121008030a02030d0b060702150c12030114130c0507081b010504141c09 67
    0xa4a044041d0001d52075007011090019080b49c100f50b000c60500200d81b900d2446907070344186d98441403024450360000d6044100345080c441400d0a01d10b5005d441ca8005055055031a804502242c0142c2812159850201e0f554002c0484216556600941100007500280781701c01c409600e985080c60321022414156940c4800c5203001c1c0700aa000c0c003d102e0b8109000c0c603141c40043e2903688140c4911046001d10000828200d1082d00721402c580010785815250009020601c03003800c40060001025038400d10300480c040509200070203002382641d00560b1104414000c240c11a4240500c241c402c900400885006840d4400b20340700440c40100c5c49a205c0e41c0d8a80d001e0704040c0715010800e078854001001250441400440d2100d280c010340707400c0040da040300d0a85044604040350300010805c00d001860009590301c00408000c24040c00c41c9440f0310815641d94255201990100e0349003500700154030b8003480801500180c08294042e8141407141c074940a40b0142882c0a081c2488400179 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 946783839 1250 946782589 946782593
    0x1707090f02090a1a16060b130204051002070b0a051602060a0c020901061d040509100912021917070218090a03110607080115020a140705040e03131e03081602030c0a21 73
    0x240c00940d91410181002c49811394808c0400e00035401070061500c00c0c007407085041500d500c0040c10b9401e941c0e4032680306203004940c1909441e40d070800c07038400f07091140f101150070060711914060010007450f41c4030b25480c00074500c100f20410324160807150030004e070040f298201201d140c1103003000702070a071000600c1e615140c0126007081c580d5000c0001080c10240100c04010f00b0029408420706517600f13a5615914143c20411046209000540b03001411800b2401c00214a0b0050070810b10040c8542c0000c0104401140c6d0070303608982d111103d41028502c10b0505401c460000c0201d074a10b0080c00462801d000043c044000600840319130046070681c004126008114002805d50000d0802c4011248c2140480c2d07590340c07900134a4000c0342005401c603d4104000180d92183c507440c0014030140e07060620a80c19407201010b001814207031080f00202041a01004241d424000320f440603041d0158010300d840d007034107403502501404050008004d04104090308403543c00781054420340724280740c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 946785089 1250 946783839 946783841
    0x12183e09060427020306090a020604030b150307170709020703050a03110d18120f0c0308061306080313060504150516120203120106080103020a1707090f02090a1a1606 73
    0x911058003080f0650030982494264400a02c064802c90403145140e075034141305070320307020600d0000f5004501400241300041040346e40c540e004a0071501041c044013003200003450b106c0c540d801440f03c41c00e0a034030070b004042c06005510240150510640c5000202c3d600244144103e024101c10140e56070454019261540112018603108842c20f000e41802d07042038201c544107201040b034030031358810000c501361030141074080716100c010f880d000600340d06038806070780c1000002e01c3e141d844504014540951700c218480d50010340035060046450302c004003d410300c803000ca9000002030140070b00041100013001441e02ca41208146065500e449441c21610703009044e0120007442c0e110020350039100c9507400005800001b410503000001070b643c0e5403040d40d80d800203000181d004400c0080c2400f564175603500c0d2100c240b2408049481285d038864084003261070f0142c070564165000a007144151904c02101d4001d03120004010b0307250311a955031a40e031846034074010318101c00c00103550010701070b01d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 946786339 1250 946785089 946785101
    0x111902150f010e060102101505040501171207140a061b110d110304050d03080712061206110c010606020304170c0a05042708070204050a051612183e090604 68
    0x410f1f075003403042800d00c3c010200e48000074094140564034000c000140c03c4c40a14005804c1c020007000303030212207020504004180c1c005401611403040c01161107031286002c109054081e0301402000078019003000207600041c1700b01e040e443c1000070800200c0489074000c9901302d44410309040c808030a20904003240d0860240741d0100b075001040c48a4001410b4201c121944101c901e69107001c00c801c03c2801030340868000e40280300028400c2c0c10300c030f400030710307a0352001c500015080102030030b0030114164a401c0d690141c20060050300082000c112814500240040e240ca07108050300380c1c2c400c10000307e0091007075440b465114036140c408201048903100e50000764404004106420320031141080b0506510601c8120f001d545880c00046604ac002e10501d40a1010034031049489442e413071701121074114085141d031070556070366800c50f00c0410104440c000f00f8441c0e00951648104507000c0c010f143c1001c030302180a02e00074400d0402c081948001c00d0060325044030400102d1b00e81d00c01040c000c0c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 946787589 1250 946786339 946786363
    0x1008010e190510080d02030c151e0403030c1d1e01050f0c01093c02060f040e06130e0304090c0306050904060906050721050406111902150f010e060102 66
    0x403400b814440c1d0100ba1007103c4054414a40458064551200089940344585800c890003900841c0300c000c908800034840c0385d0483e034200d1100b2042a203000501000906c144d070200c000c2691840c2e9440741c1c070f0300501c000c140400c41c0c42044401810640201e00740c0c440880c00b4403106a19003201000981c0590207079204c0398112410552030b02c2074440564024240d1030412341e5130b10500b41a4861001c500910301c4480e2012400c1e900b5003145c610250420000200d800301e80c04203090021601c400b981030702800081070841d0301600a420b02c5814000070b2100301014900030360404041e4410440004100c904469040b4030001e40d0490b08013046005006a411080c0c0c4082208240700a014068210740c0304a401410108100e44802800303690241d194a142c403002280451265100140c541c88198414000c00000c142402c2c140c0a00b45036034014004480762055481000c941380e41c3c104468401404101d809102c0c03070810341c25010301400b0510a124100745c060000514991003400121100f02c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 946788839 1250 946787589 946787591
    0x2030606071a07022a0f0307030203030c0a060501050d020a050d1a28050907061202040b0307080f0903032404090b24032a06041d01090501051008010e19 67
    0x1a01031002c0300111030090355008014480c0001800034401c0040f800c0d401040d003c1100c0c2641200d41c000c2c03140004045044542c9401122000005031310148000c04a84000078080c0c60004413525020b0100c800c10780155004451400c860300040c4c45490996056038402c03503130701c9003c102c1407610322000014400041200e1001e0410301a00d0100146130008021074484440b4030422011210800c80340100c0c2c0300801c80c1d1000108110150040842d8490312120110141c42c203612080015100d40c0195034184c000b61a210402080b1140c000c5401c4d00080408051440c40c00d020b06500c110420000d800c194072140120240010b40d160360041f410141e00c036441c0c08180c43c01d400481c00072541c00c007810180301e813141c150803c60324020034842c0a582211501c4005144018031a443c207003922504580c1104040001140d21654090102040140803a8030809581091020f00540b40103900c0716000304600b50070480342c5600b28450605603410900c56111603071300d00c00d08101c01415040166070386 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 946790089 1250 946788839 946788863
    0x10804170a0c1703100e0c13080708010605060a0203030604020f1c090201111207150b0a0306060303020d091413180501020304051b06040902030a0b15030a150f090203060607 76
    0x41c68000b01c10080150141051034815000c06054100030300c01101c45c019045441c281c144a070b01880c10f0480c0c0c015a0000307055040403a40703440d110024810307800006860b44030040412030018240107003405080107507445820b109001102170740e80c1c08082c1c1458491900072846000120080d000d440e0f80e0100e40e038095a100c1c440900c417400800c1c031080103038005401007082280307182e400203100e00c0131114150507520302135850f156a401e403944010488200c540b16400c44150365202511640039500403003000400302e04d5450045d20300b1040500c000c00b4407404d070b0350030000e504408600c26011502070340e13081500400c1d0031181000741643c60380c030400d450041070a90288001503000e90712552107041200d51403562006041c050521514a03503521400810040c0040c10890b0050364209011150210380407070490000b42140046031004000e1000c0407040000d020390500bd170803070f070155911b4420301143c10800c0c220345030300381405203c0b0b06e91303000404a006e42c0c44800c00c9a1a480c2c000f032040488d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 946791339 1250 946790089 946790107
    0x702030c1e01090b240a0605070b061201050412230307051602090c1b0f1f180f0b0a0c05090103020a020a20011112040302040b031f0516020705090601080417 69
    0x9a40b0380100010601700f1065140016007406881402542d600e5240e440c107124850b510201c24010040900f904103018100751150403809010707050003603105103045258418030940003030105041201d0b032481c40f0002c00c5203c074031100c241d0480360403400070310340301d43e840f030032003045441c000f8030640020f410448130410084090714940243c101c0e552014030b02840c9421a20180755218412089028990481221802c4152032202c02c58002d462114021820b541c00317540d041c1c520b607038120f01502c00c080c40c84e048904025500005ca9804941c1d40c00130000000740110090180c0501e50405061503030009030074010600807c0841405603101c28a860b040042440c42c80311865160304050202e00c1080c40100c0c0c880010901e07950340710071104e41a050900d542c0030003002c0c01508001c2901400b600d004103d00d1030412200301100c0b207003c4004a002e05048907501c401810844c2c0103070454010903810301003595200d0100390002c00034078104980b5216400c02c0b00c01500310614918480d140080d4400c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 946792589 1250 946791339 946791361
    0x20a0210050304052a101403130f0804091d0f0a03050a090b03040602130506042d051c021c0b0a0c090b0c060106090e0c0a0f11030711090702030c1e01090b 68
    0x5170b04c054403005c21403030710300074195200040020700011700301d01400001c1c941d00001441d03640c5903000d8000020a9403c6480e4003103180c0c4103070040c210054844401650b480c888429110040e03025800420780700264001243d12150740c110000c08004002400c104010303c60424a80a4100f5405c3c488d582d00b03051901000a43c09080514040c4110a200107010300d000d900359800c075411005042d5800c03088080ca0100035981240c003080040b001c080105058035102c0000c8102c45210b0365070700880e000c074010461410708a59401701e887d803c60303483c140040e03c9a034050741c001c000840c0c0824072842e204001d4990006540110070b01c003a011981d20301d103003000122035049812540359490390584415019140d100c080f603038050030103000c21145180310722520a4a20340c00c03292034010f00420002c4025401e5620900c016503e04002c180700320a00c0c03810030040c0790440307070b1400110715001101000d80c1d1038260700366a07014200e0000e43e89401d805000e411001c031141d40048072840b03514180140c64 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 946793839 1250 946792589 946792663
    0xc1103070f051509030604060b15070318080303070c08130b0712030f060b120619090c020c06070218090a020a150f0e061c06030b01080319020a021005030405 69
    0x540b00703d290300548240c0d589000b040b03d0b00424050301521440d9035030745981001d020320545a5811515203600d00300000b03184405811000d110783d0b9076802009100102400307100c290381107903509400820030310411a80044414152960040c10300e901e891040303c90300d000c1c048a034040e501560300010003c0c05c0002580c11030051444545081219540c031905d540c08980c2540101c1840d074030108141c88036501040c42450b4003c0c80245003031000a40700d4a03026070303400c0c0d942c0030016040d11650302023074032a01400001a03081c420b03a4a1400c200080d000500c0302c0c0d0082040ca52103220003000724051039002c0c0319000ca8660080d100e0303aa40750b41c1d040c0310131402000460f0f8200154140791250745c1c4500c200d0038101c1c1118020061810100241241304841800d0750300d042000340d8500d000400524021102402010403001541e100c0c0402040d110020380340150090441d08124600030041e540c0460348280e503c458a007584c1c8079a11803030120303e810b08415401c0000030b400f0742200b10102c0c0456100e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 946795089 1250 946793839 946793849
    0x605280b0c011d0a020a0b07140d02011a010318021207080d08010e0f061e5104260a1b05061809070201060308040e060a240c1103070f 59
    0x200920b40e5641074003502d480395020029030240161b40100001d24102d40913000c11030003114030883c146c807145a000c0c038080491070741c880543d45600d881d500c4088005502001c0940a0070184031a240607440390007080d01d0400028410f1003103151030101700e0020404e00700545104400c0700d41080e9110f0000d0402413003445540700307121001001440352201104014005c24002d0000914094001c2070780204240c100300f4143c0181400f50f40d080102c03500c40e001c0360181c24150b0b00544d0240358494460781c51360714905100280104211425004065034201c4086803001440450b08040c0c68401095018500d60111550702c1150800014450f200e0b5101b9051000c80d10083c0b039103540c3d40c085c00307600e000306400c00004031203c281e01030084c02c0088034594405614400041c00130345a81e5980504c0d000f6030080001c00b90f580c4104941d5040101101c40901030881c40190300c1306c020351040d0b8035001d03001100b02c100031410208034104086100364415403100142985d000a0320b4200041c8000b42c14030034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 946796339 1250 946795089 946795121
    0x60f0e0a0e120a0924050904091e1a0703060b2502120d02010606110d2f030a090f0e041101120c05071106031501050f070503040e15040605280b0c01 65
    0x481415139402034417103d00c81100d48441b420071a82c001004010015141d055891092300044601c0d14034401c0712480303906100b0200ca14541562202403c0c070110700500703010515141200034008801e000c82954a41c49008404040e4050303a1101c2032540050301d003000350450040e081caa56400404913a4000a03a41e65001304491552024212200320b190400703c1601d0f08621042d0341058810140040c048121060481885101042c2c8451840080b0469215030700003141101c0e58580c0600080010412408102000e81c2400308004c81c60b440038000606014042c103840080744d005607004200b59911800c02c100114400402034401e52140e8030840b4048890111b0350454030300310043d40d00a80d12404007000403008000191000e074840b0204512812050100c40b0003c0d604000400c0075210f00c5030f1811180c10044010321950059148640c8213504103071041c016a11100f82001510705004807075034003201485101c2161400d141c02ca550102e800052403402100d0541002c000100d907901 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 946797589 1250 946796339 946796369
    0x1c0b030606010e150f030702060103140732030703060606121a0d1e12110105190b0f04090b0117061e0a0605041a04060f0e0a0e120a09 59
    0x4101511058100d581c180424800503940105050003a841c030000300385001300e14540b100302160385a01790030460345900107078441001401046040340000d45180203036001400b00d0b40c24a01d403482803850080c0054256428100c00005070b6611071007210080c0341c0901034a41040d100e00b0400c0c060000c600400011815040101504158501c2010b4080c5d958000500d40e07203a03042c0800c001e2004a80050b81c00180c0720f0940c1c0891044a507640010b42d21450b400f464000300224040e045044554445145c1d0f4903010800401c500b0701903a5190301000303508001080d07212200003901d65400200344d281c1040c5044180c0f800c00c618424414103035000081c0b07036148100c0c0603142540d215411584503043c0703a024682210003840350a101c0c0c0d08141900d002042154841e404103044a9024041c60100b21001c041041c1505280c4500c43c003038006104225980c030308084100d42086409026030031103903a01c003a90850b1400600481c900c4e011140c0800b651044016070007401c1855034004e080003051200c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 946798839 1250 946797589 946797611
    0x15032a0f0e1c0602031314060402130212060103240b0408060a020f1602010909020d0f05060402091005160501060b0415050306090a09020307051c0b0a150315060503031c 74
    0x51100b401e003185010181250480340e4681010390400740c4031b90b04042110b081000004d07280e21842049103202001000203241900421401443e20050051501e00c10400000420f40350744400d5800f00c0c0c203080c007181b050302c03858080f0000d0481c00704601142901c48404215900c484000b001210510411a0740360b85512010108900c609005110304120401900a207004401041c4070054014100150400d40d654246000e0740e021600d044800b5a4888150760032054601c102d54200c1c03400e440450400b550304000c580103d49d00c0c00d030310050040201c0e140020074104010a85600d511100030b2003a01e07a00c1c0b480241d80d40060242e00420b4070180c403c40c4195125200ba2417141000500359a815102c1d001200010540d03200c0130b0782c06018080d80401e0684407500d0840b0140512406030281000600340007042c000040e08070032442e41884400488006c2d44101e51b4241c98021403502c0cbc07070700752590005005004641c44a034060001040c9a44481490580c049001e00106028454003032030b2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 946800089 1250 946798839 946798849
    0x31401020c01060b12013b04150504120e0d1506031205070c050d0204200418020915091207140103050f1009020d090b13060e060115032a0f0e 62
    0x5c82d1500455000e0380c1c00400800e40c2d0810011884848507080030480504030a18000e501904510242c21624a00a1000300f1041c8881e204a0400c80c6408201509065440e59641030500071141c003013004100d044171480d600c40c5110300c070159119003898440d100004d440c9014001d148400d6507403101550441c07202d0b900810440d00d0050348030300c40d0710856084c40100600c03641185002e9801c030740c0e283d102800403004500e40f0000501910030150f2610b01c0c0a000d0b422002d125003c40e0081c50041c4440d0310a5240c2410005c1080b95001003692903024000206101081c0c50a60310554410401d00040d50918044071050f922803e0340d060001d40d6642c408046040c401b40e4101c0c0c44204d50403000c02c0740d6200d40d409807411802481c0041084655a2200510340406840c00c803495032003440d42104000c01c3d03100c2c8055018400703019102c9980362089042188200082c0710082c10f407102a0710540c80341806010f070100342c424101141e20f01c00d0b55001403000c40c500b91990040340108a010a8501d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 946801339 1250 946800089 946800097
    0x80d06170a1a0c121302090406061523070303020c0a0605041a0106080402090705130e10050901031a1527010501180501032c10140c0d0e07031401020c01060b 69
    0x55216a04c0c6003025000f815080c0c00c10040103011000401c0f6110390061740c9403060717240102d010b01d401041b16401c0c21184140c0f8844000b45400344446403000d03003180780151a01c0c4d100b1a18006c0700f15140c0d04242810b4019102d030116000c128001d448a40c0c040180c250300007400340c0c0c0110064018040010b01d00d8650703070030030700501002c2000c0307400040040c608400c03a40c2e0710811f1881c225040006100010700c00d0862070708402000e0810108006182d2900d00e0708400822013143c40c41340d02e5146884a281c41030490440e54030b035056400004d00b44071442d8182c0d401740398000c0d005441204544502c0845400140c1e1150400b83d2000e0000900398424040c100c050002c1c243c0140c44a45090b0040d4020054041c0318804c514101500344880301d007035040f13540e51140c40380140c8400b0030103554120465038098201c20b00410044148540040b420302a20360f585a10440029400b0022080a140068079400100140c0c018507602851100c10b40181c5041c2580e04020300600d5240d851003400341c0a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 946802589 1250 946801339 946801351
    0x50d030207180b060301051c05010612050606101e030204080a1a0f16050a09090c0801030b10061b0f0203250902070206030c07231b1903080d06170a1a 66
    0x700510043c4a6440d04401210b5200020800c030003023285a40d841d2800c1d686194800d0350310f4801f001060003030110074000c0c543e10050885807502410401c41c0042c0030300b86403410340440104400c40e03105145000303a04503800341a140c0c0c11600c0b00c024602c1c0012060a10300740e030300040c18164011907004001c3c10f04403030041c405140d140341e04d90300c40c000886140e0000c9804808104181c500000c400c0c0035486079032440c2e05542d542c00100e40c19801c0c41c100c0c210340031305124442e1407001070400010754000d14420009042c81c0340032011613001d05202074512035240c4041d605008070810400c805030008400200d00c05440715440310710340d882c08200102d00500c100130390020710400010b90f007000039100074507006204e0200c80c0a41c1c0d0340e151011000d414200c40072103a1383e001701c4d054035050440d9840301000c41030884001c0c946076200316201200d1042488000c004504c0450b071410f41151940003900a01504010340400401d80d4100569440104a083c0d0303912170740c0800400b0f900300318116030307200321 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 946803839 1250 946802589 946802599
    0xc0201090f061503020405010f050411070f0b06060d0c0e0f040903020307020f120304061d0a060e0409031101020f190f050f1e030406020901020c1207140a050d030207180b 75
    0x2000030b4403034101a15081c1e814401800760038038003100680e114411103019001581e01c2e00091820310003031104480c40c080c4085085c840034441b01f400107a04043c141400c0303a110b040c14010340c48603408500c4600481c540c0d480094100b1489804d01d0760302c4076103200362150454000a0941e1800240001c071241008082c0043c4c000b041042c3c09410300c0e007a01949408060140300840c2800404141960862703008040016002840c60701c14000140b4100e44644044603104602c43c9000000b505c85884001c1c2d06000d1500d82d1a00014940a8000c90310581031420096503030710484c140030b00059200f55a50480c08400850032801140314510b0098004e0707494481034540300d10302111003001d4001c01c00d644641600200007150b1010100003035805a442000d0141e00c840c2140006410045079050719401044402a41c00070800001a01b404580e840f0b0300b8400380030803900200c1c0f00042d258115030b0b003100903d0f11240801d90700007003102c1252140c4d40000d000030152043c0c0c0d803d54601c2c200466000b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 946805089 1250 946803839 946803863
    0x4020d0b190b0d09081228150e090a020301110a12050603070b0c0709061202210d030b0f1008070909020301050d02100e0d08031e22051e03030a0c020109 67
    0x80011503001403095401003401e0350030101c41c001d41d410210b0044407850700007c40080c1d140b01d403001211045524000f5000d080c007425040c0e01041491103564400c05114010350070101c0d480740d0042c020322241c281c014000340301480520603e2103440d070188141c0c0740010380080c10802111440d100b080d0150398020081e1440768a4840c1c4060706400c100d8500ca414050907800144515861290400070310000c52864000f00141c01009001c04041003c0c0c0300c03a0300d070491498459007011440d020143c9041c10700140850021012501d03080600400c0358128141a800b90300c202d070400703121407143c401d83daa0800c4c3c2c2034403400010282d00082c8079607900048404072280046c034143d40d444258480c20305d80f0140c204a03c00025076011440070095074036240002c180051288560042c801107809136070881e409042c4080613032004a1100410b124841448440070200801800a1004541d010042c00482d078410364400b0380b20780c07040c2d603c0811240381ca5580f40c81c4a0040c012110b084d90890020400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 946806339 1250 946805089 946805107
    0x61d030129060d0e1c05070201200309060403111908030706020a12090c060305060d03080a020d020c1c0e0f09150609190312030b03120a050904020d0b190b 68
    0x161140c01124551044092004507001070444c8114245420080001c062116100c0ba005d0f50b805904140c520030445e0410040380540d820840a030010507030144a100540c0000b082c40d81580240b42c1c14540c8900002800018014a481100d886410840711108201c070500c0311054640d03540e22034101e107500207200410108601380c2c00f5004940081c18810311600100c913442e030458555050494000b01084014000070350315100701944503009951403241e40220791405000301e40018010041c050700011a50360148040c4c055943c020f888004540c1e14441c511295000300c0700c40c40c1003000184031070960030002c1c40c00f0082c00f0160b120180411034203032504100d0480800ca4204080d8101c4020040001c1644400c0500d00700700350200501c4901c2c904524101c0a04e07011102100c0405040c4100110256400305000e0810310040f810b60395960a007520a60340c0e030213003440d2190b003c0c0c80403d6910080a2030741021079001401c03a4240c1d00c40015440f0010b5141d000d001e2848440c50038004400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 946807589 1250 946806339 946806401
    0x40e06070f180e07080901050f0c0403150609090c0e060303180420030c04030c05150a0804030e0901090b040f0515010f020703080307170109020c34061d0301 69
    0xc040b002041d035407070840340c94681c03d800ca5002500d0300d0002950450400c43c184000388076a682050345608000c07038a0078918201707104c42c05507020240c03216441c00306904901a0b40e0348508018a07448a0030302807400e1500304440900000c1c4502181e0901140002d0101e00c2d000c821942c0c5045404124508480500c05000007000c4400ba420110710340715008100c0400860042c0d8440c02198205995850541c0386c8143c104205501040c010126000e01c00d01c0c0c0715408041d901c62000d81e28100509070740702c9c2800c45015100359946900440e1010004c103da02d8560000110000300ba036040c841d06c3c10812001044440c1110141040b608a03042625158461042400ba000301c034412145c645803a501c44210660098a0003004100241801c2845524030420340d03005180b40e03081181044207031011651901c52851101d0185802c59000c0350302030070183c000101048140040c00c1c504d64413090081d00e9900d601e891400078181d1034156000614050043c00442100d503500d000722044840400d00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 946808839 1250 946807589 946807607
    0x105061803010e0f1e0f07171204030f020f061204110d050111040510050c070605131d040219032003010905060703060f0509041a0705190905040e06070f 67
    0x103a040d500d8052940c003c080803c441d100c0300302c6903805030a000038080318841c1c0300c0f43c0a02c101c460070741040707004030902c0707402151400441b40303900e8018440482542c400c5042298590315110040d038045130120030b0015600003440e03554801e5030141441540c0404100c3c03140502e441400e03d0321113001c00900064810003108118103c054441e0304482d2050742c8884c04d460f544402c0144418000c14100520300d01307004161100320880c1412844c203444480000d0b1281c280f806141d05000000502c246400c000103450401000d400b01c00c2c8550962007440101050400d0380c0980c4500094020004504113002030002100e074404001c0341d01510b11103c00d0480c4c6800132100d075042d5a01d414000c0814010321035030344940090354001907500e042812106038141c081d040280074180810030400003992240840300c500341400100071056903a56400c94091150f003041d44002c10040b1945e180b140d802c21280b109682e012a0300b0b019031220710210f544d82e40710464245001074078020340d106450380502018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 946810089 1250 946808839 946808887
    0x4231006090e131104090803150109061202160804030b04050c090114130609050f010305071401050924041e0914060105070c1e030b180606011206090516090e010506 72
    0x984e6103191000000f0301b1200d41640a4542d0b034400002c010845100c40700159040c84242800131803203003084001441e5180c5485c1c1c410480f90b0006448101600518030150750503407000001c0e40e19512031405071100e24042d2003c580d107115524051200780b0f016032000d41a81c100e0220300141c840c0703c1d402c102d00c211000002c1e0800503503c64002c242001140540c900c43d407805203000760a540742d450150301c2e1401c17540c004415003039008440e140503030b408401c0351180ea07012509600c040540c0c0c0c403169091240c2d4156001280400035000134035840d2000400c002c40b0702c00c080940b00f03030703980c1e156202507801c0001140301c4190064000703500d540c0284041c1c0412801190340c0400329071103081040103800000030b13504281c10300080400806c540001c1040e408200d0804501c41c0090180c0c0c040d07518800500114140f01035440030440b600050f41c416401810703044014007641c200301003580f648507195400c0c07500186001101082e1107480c2000b450403200081c0c4841d182c0603504002458400080c510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 946811339 1250 946810089 946810103
    0x1b010501033201150e09011406040504081c05220b0a1104030f0c0513140609070c0b0f091509060a02071703090c190e010306090204231006090e13 64
    0x5402c0850910032098864402c540b00c40c0202d04104c4422032406000b001c08100d07a041c11031004011702510b103459080941501c000c40d07144c0740d614220089015100010301140c212100703000380b00e07640f0f030425030151724180844c82c155030010500203000003030481c01030301c40340c03600780882e2000b110b40d44071584d8000b41100312800d0035100c0d0f07178528a50145902c1520600607814080c409440c0c0000e40040d000501a002c01c020107140a04900492006003e64030410100300080e030f135107020f5014407035015031000030f00a040c50041c8012221a2007541c445019100e04221401030004000000c2e0151f105500181166650666014041d5001c0d2500b180c03254082c8a01d0001c990b280d0014500034071400700604810351044003803001c03131a8425844070100500000410003541000c01d1035055982040c004241c4994600100e4007404500f10700c42c044c0c1d034480c20314034020766080c0c8250740a440300300b182e0342e0390641e0303408200d40100da14003030803001c202d400011804c2040101d4080304050b2090203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 946812589 1250 946811339 946811423
    0x33e07080a2d080712110c010c030e04020f0d0c02161a0702060d0c03110f040302090c0717190c030e090703140c040906051f0c0519081b01050103 64
    0xc401c80202000010840d4507440c04a0740c4c03000c00000d042000c100c0c4040d0311303045005400c008038150341d51130808001810700481a10350410f2500c03c1d203080d481514081c200350b5681940e44a549916800002001d42c0d451400741791400300b0344045860715600796020f62106010341400c4600c40300c1d810340060480ca0740b008000040058888401616050300000400140c0d0080f0070070103001c2d628400e10400502d802044030380400713004c12083e1019280c0586413105a582c81070740901c142d2007070000c041c0400c110b1094169928201030b0003007880c00f00d000701c40484182d140c04203076071030030603c00001d001c0b41c0c001e00748488504100031040d600864901d004108000303403101030f0103030520980e201d0041e00c100043c1404003407080e0181000400c0c0903107005000e1160750041d9030040075081040300400060070351040c01e0020401c01c4904001040c0c100d207826030103d291624181d8400e123200d41050000c060000030461040c441c1a04880c1c1151243d01040381d4801c1041c030031610311040080b4164069 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 946813839 1250 946812589 946812653
    0x91e1f050409080d0e06010f1422090c09090f080901120903020706022407030e0708010212011a07030206181e0604032a0f033e07080a 59
    0x10007149200c80c0540c1c0c2460762801c80c1008401a00c445d4050f450840d807219004021025802c0d100c00304031048007847c0040250000006000c2c0c1d85c92410228100c24070076880000603d01d503001c641b040d8452803c100401c0c4c3d441e43c03054240c0d442120040c00d02b0218812690100341210000c00d0a0201407402c4012107019500e10012510381490540041e40000006d10a25404214403415a00c041130300c41c2c07130f90310f4421080c6a4100f00070280750415441c1c0020440c030301c1c4104242c1c00a0700b080c130001e646451071455044001d0307800b481030900d07824140c00000d101c40c05c9030b0200c955094043d80034101c40e5407061707080c00102e090392481c61820320400300ca06240841507191104030b51030503009884181000d050060984941541e06070840b007003810b4200300d102001d601c4c0d5a50310750044041c1c1100190f414280c0740000707407a03028200c4400441e02032032200718001d801c410b45c80540200c00c1000410503040c1da6140d41034055542e0301c2e407100714a04007080d1041b0000c140c5401c24518030081e40248 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 946815089 1250 946813839 946813841
    0x1030c060e150d0509070b131a07080f03091204080d080403091707051e03060403320c011b0509090c0403080c0f0c010c031e031103070e091e1f0504 65
    0x50140300d0800c0d44ca0061000700c6406001e101300410703003605018141540041c4c40c29002416104401d0346190004559102410f05410348020941000b10140c80b5145890155100e500c1200c81ea84070740070f41003540c2040c181100c20b45054403840c1f8010700641c2e81c1d43e1416240c2c0318004e0015001c1c41041d80001449604c03620486281c4042e00740501440b03440c1609012400921404000724907503056003150705a100000c44960150309464058844500303c400f9807048040c40f491045a201280d078a5030003d01003100403c03600641e17000030815003506404520408034a00c440d40009041000b01403040d15104c1e060582004d21120700a2806580703684140d045c4e07100e070b80301520a070000e100059210006100725140a0002c0c00c14070609181950018800d062508a030400d18005500068415119500070448100c039044140ea807801c0940c0094580c0d0000c07100684610b07480000102c8207484c03c140210000c400084403001e640340e585842030f141504c903000b88480607014074001031076551 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 946816339 1250 946815089 946815097
    0x50d08070c0e24041b02210415080703090f0605090c0315150a091a090a0e03030414150709082a28121106070f02010e04110310090507020601030c060e15 67
    0x32035001050045047c4840360f600d5000d2407100c040403542800200181c0c80e5a80c10100c05240350f180180b5585d94502d4203400904195502606000700343d03a800041244c541d00c414001e003c01d0307003100c150030100345c00c15544050718235094110364003000200b461030607207801400651400a01d894000d41d201e140e220126802001500407007602c1c0d0905081909105c40c1c0301d0740040e000d901c24811140e80e40c4145030b03644800b40c0014206040022000d052110034440c0c8850f610355101d0842e541d0070200700040020800e8010f8100d5809030301e1045035084440ba8142e11145265412807200c0c40a0004002d031420b00701c0180c0c403441002c0c480c00c1251440d122211005041280200c8240506508012018030519090300340140d80820212010a0441e808665046e509280034161008a01c3c04100981040c40400011030004005d1007039050700324104000b030302d000c02400c00c010380da104800c90b6149400e100c05000020682d1060021600c14601403040c51400707000007541c031a500d0307100311031a80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 946817589 1250 946816339 946816391
    0x91403070611030f13091107080403083a050a0b03120304020114040902070339020621090115031e061103010323010b011d0a050d08070c0e2404 63
    0x440300071b00c554040c6100704a841c40c401c6015034100340840c1d4031141540724501000e0102c0c840440c1c2101c2c00010303880c8001200d02c0c29060280d5001e20843e402c0a6809898085031010303051400040064855201d000c40100006005244006403500c4050807548040d0090341041501c0d091481e171421004010002000021001642c03042d00781001010745036854907103212001c01010048900c07c414004101c1340f0310742c4405840240d00340c400580b02c0d114041c031803100d818240c1040307591307449408100d43c418400c80000f030042c07408542e083c14a40c2480d00006044c0002d10303c00201e034849005078041d0091050700d001170001030100c40c800f66500240d101f01c2c2c1c640f00308580c13912421814807451800c0039204000b4083d28a0356030000c0c11100d0a80c101c44c0902404880b4070f0300c0390750356100d403800500c8098840c020b9407000e418202d10b80d0740a2501034504c005000c600060041c84583d0f094840d407070002c6184151005161641c80d24081d40c400642d100380c841c00400414042500c032144010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 946818839 1250 946817589 946817617
    0x10c05120c06100f1505030a0b041806050c0301060c030513080a230d121505040906050105100e0d0308130b0a0518010204050a090e1912091403070611030f 68
    0xc41c3c081d00101514260742c2214400c07494501081201584040119100b100d16040c05922940c0b00b00c21540141410000507038098281500d211450031070f401e12801d180c1c02030100b0b00080c0c0d00e01025030f049110a02ca82d1000408854011000c2846440500058800d07120480707051507891480e503107480001e1030182c49524214005154070740d80e20804e85000d9000d0702c01b90642020002c009840c01e000c1c081305880843d1a6600390100700705c08a212009402d009204000e00300f07586c240000141424081c0501402c3d4911081c04100d0040c100c03105c0c9100c004050f80040103150740c0454040c04040c107500b03c8020846101400103182000c0b4034400c08410000166a00c0c0460b500210041000410301d55644100b0040c8103d0326a042900c00362881c0f68030220b4079000300b0440600d001c0d0180460780d00d1401c1803164004015032458800c0e6010003660341d00d0102d40d1140742c08840d03059400e10030f950660050204000c6c090041c0b0301101e0059150043c1ea0030070703044c07951038501603011150700d40041b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 946820089 1250 946818839 946818841
    0x81b0301230405040c051309050f01050a06120803150a050d0605040b0109110403120215070201020909330301061d040524011404020d3209030702010c05120c06 70
    0x3218148241c14104a5090080d401c0c5074036a989004240c0c011203008807250340302d800c004c512035006182d070150f000f82203030101c3d0000100f9030300030300c0162103c54050b418550005003c421042030300a2560700030350340526688444c80c240041c50600c01205400071003444002030156105040c0382d0324240140c10100f018a070a1401d556500300581000319554a00500011501d00610598040c0d0b9400064640100c890b0358060f0b28111030700d0507012000c04030070108101c0c280e041d0060500c0070401d80ea01d00325070b04c0e000300b888400f0100d0070f80c1e16240f4940501c0c07486002140c6e0840505184043e000041c181c1d254841100c02000c0d9031740c45082504060140820840700300b0030307040a03070080700315405221010a07008841d10818801c0c5c1c50f85107800c2034407440c40d99990741100c942804407002041014004c1468031380344414842c0f6003040091200c282000c4480311b0411a1117000c10b030780590b151103000d600548280f200d02d2801c2d11a80b080c0307641c000d96241580c00900010000034010540c4d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 946821339 1250 946820089 946820129
    0x810030b0f0402090f011a0d060806090a050d0e06030720010f0b090112030c020904140a030c0311060105030c041107150603120201110d05071e05090111010902030607081b0301 77
    0x2c902000c2d00d0500280e803103a0040050111428071108200d0b14102aa548c070160080a50040c2400d500210f6140c060301003407180f11003002510b841100d1182003552aa1054041e090324004100101c454010104000080c43c142c841e0712008400c0503408206607440303105014182c2102c0833808a07140c902d43d00e0402c0d002c40c0c03600c0c5120034018401c0c03000200c4003250f85d950081038000c0a032030003400303080303944082010003080380d5040759070031101800c8400c0b158060078000c2080410000c00d40c00302d00300701c0c0a1540c441340452554143c1c0c4019000340282c600800600000b014444617040300382000340203200c0002c240e0380e11044d044524140104003503085040c00c07071603100030b0360080c0156031403d5019800512010150741d014140d503400080d2554501905484644442c0c400108850015403803010441e007103005401005000c1c0d0f40e0217004820078290b1402c0390000300000e0350541c0513031300040c1480e04c6201c0c3c40358002e00402441c460514880a0b0003003680003030300420f02c00d96204003180c0c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 946822589 1250 946821339 946821349
    0x1b0d142a0f091303050f0f0c0606090f06030a0b0a0b060403050d081609150c050307030c03140703200307170405030606040b0907030b03010225050705061201060810030b0f0402 77
    0x3007591012542e04402c1c1c1040f807030321100b143c1c6a10b0014140440441c403e2103c003102c00c103031a001341050135a00ea07610300709034016851b044101d079054415146040401c2700903400c003009622a02c4040d00600c07150f0865240d038003851000a001050450321040781d110703c4d848143c0036000852048000300304040c0c254102070710302c0314010f0074003504001101e04c4035071999210035418119520000c2d10b11659000304011242c4c42c4203d21b0180c85440005400ca0405a00034826900103003ea5a0170b10408081c805240403880b5800c800f82c0026200b01e1099507045600d510ba209961300c05003100c0c80d00500e036035946030410110a0035094010301203001c03c202d041c18005143e000340122401c1280f042c0a0000810180700908101d040580e254a005680e0b00e00354101c07815000f8580c0c0d6a10390074820603012104840d501d408403114020b480000617207092090694415108465121146a08100045032018001000e011180c3c0e02d4070320000100d001c0c540340500034035901130f107010070385083c1c01440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 946823839 1250 946822589 946822609
    0x221100c020703021e01020d0c0c05040216120201020a05090609030a050d08010801180312051005090a090201120b092a040605041401021507030b040605030303070c051b0d142a 77
    0x15440030b84181540c5c00d40e0ba01143c2c00384552658144a082e2256034148003001031003607004541c00c64800503101c001507400180d09400c0b076100d40c4401c0c4403d040018100d090703005406222012480601501c00c0602d04503001c1c01400c003024040b0381081d402c503100c907440d1130216450640400c0c42d40c0014082544203014440585d0669220588904840d0381c000301a2080010002c1000b40d0340c0c008120010046280c0800030701d40201410b2203030a080384d0f030300000c01040d81c00b00d01107480d04040c0760300300e03005005000100c0e030020081c15165071611546031003109001c140803000c86141c45c82c1024450f040b000341001d400c90b41d95103511903007840c3c407520141c00500e14090641d40a01c0305105851806802650320081500e07012813128010000306007d403000f90807d940c90302002c0100700c1c0040c0d11441e480c07c030b1030042d000c456030b10380c80343302c1203486a0403025465049841c5d4184040460358030100f480215140c482141c110001030b002c0e0505140480c14101c80151802c2d40f081010b14080100c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 946825089 1250 946823839 946823869
    0x1305180c01021222031b05010c1110050c030c060f070e0a03140f1209270f061302070b0415060b090d08070507030308040c120221100c02070302 63
    0xc14040c0d0489001035540c5910940700d0105000008071600040e1081d00401c07006680d00001c0f0383c40e55140d20b404800740c900c0480b0b19008103021040060550300c58081e0b40015908011044c8a5100f03600030300c00148074003110f04050140c1085004420780c410001000b040918202403c40e5042c120000681602c001d41040100000c00281e2581940c171081e500c022240e1000201c200103d0180c90b0600700034114030321011600816003040e810441d2071000b0500c00a0446034180312501d000401440d20305400951100b01d040400040d031207446c54003c04d40c01141c002c1c240c2c80424a807582c00e0040c3da100a000702c5030100d8450a0000b000012816900c0d011241a0207002450030400c403400e013405403e040c40d2141400c43e0804040c441154100c541c19a002403d95003a59281d05010700b44400c00d5a00701d0303101c5450380300001c0c400c25403640c1c200c0e4244d0080503483d02d122031054030100c18980c044401c210f4000d40c0c1e404240144948103d070541246034000d1700c0c0c041e19600400c0113802e04044c070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 946826339 1250 946825089 946825093
    0x150c080310090b0d020f0f010e0d081b010603030c0b040305120103060b040c0807230f030702060906130c060f0e0406081b090412050724020318070503030f1602130518 73
    0x701c011b9807000d0500c50808800e40306c540d44000414012510f640c1d000d030300c0f150865201c030b100c90140b000a4000748092883c0c40700b492442c044030b8112074201c0d800e904c0083c0004007103040400001d000c20340980d410034003900e040390900e49010b04010340d0001c00ea200b02c80450351403403002d00038200382c0030780b1541c4003403401c04a83c107142aa030050002c0030030003403102d80182c0e02e50201c01c0010f00384055411030040200b4032602c03443d1260000c1d6130b034101510144594452080040c0e51800c0280070115810b1740119040c40c000d00d400f00507510000c0e5503003d42d0510031842604100c0751181c0c41620000e0040500600b081546c000c07000e075000480c00e400701e0260301e0f40010080401c08440b64846284074918085544078058202840501903080303202b000c0880a0030900f01d207030f40a40181d40111000c907981d40e02e24800d0b41405541e04840e00c1150b4041c0c1007400b00782904004038014040c500429a0401c584403491380c0012803400f428411148001c0c2d603030702404191712003500178001038151500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 946827589 1250 946826339 946826359
    0xb0703120c080105100504091d19030f030b04020c16230307060f1202040e010f08030a171317130f08070e100302090721060f150c080310090b 62
    0x101c02809281c050103031600800c51040c11808041c0b04000b104c0c000c080340d0038200000807e9103428116413107040085a411b105001007844800240350b011009154035803112042000d04203010b801410180d80e040e0f40c882e80c28404240040c0b404d00042c941a601d803510580c11a0420b504034480700264282581454881342e255000c3d034900080d54415200d440c10f106402548a0200f00d55411903a514200014000b00d000159100c2d41008a4140d0b030f0100e185184450710390344055602c0c000c211ba20300000e501039038001520300044051903001003d0140700b5202d0b00585d16440341054400d00101102c0c0130006040c0c85010900c1e19010143c400c2d519219000e510f041e1aaa545008502891a8400c1124041400c2c002d400f0348100095901800c003c0d018500034801415600368242000081c0412a0611441a509109003005e85650008a984031410b01c1d84c01c1c0300e0001c02c180b0200c01d20a404081001040600010398070448036100a966503e04014011094135072142a06001e020119 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 946828839 1250 946827589 946827611
    0xc0510122007150209151201050409020d060e1213140f03031c0b090408221d100b03010e090d1409010c05010f06150305130f15020d0203010b070312 65
    0x1504407200301e0382143d021050001c0440c1c00c40024401c0110103036124420170440615051001d0241080b0b42c1d4142c3d0989a9030390b1072092105031140128001d40c050181c1c810702c00004d800e50f024a800910381380484180c2d8010b400302d42100da2003419000100100140204903c6240c0c001e403410100b816241d00e0303116516100400da6a00a032000d103420111420760080300c10b2444e40c040440560000e1450099003000c0c2404025541701400d0141e05c4030030840410b19030840310901c00100e0b01c50f442400241c19450907050500b00d0058504100d4086150001500c14048030146021300703c600c0c1101602d0034081070092428240701074840c140203121540ca2800311142c006e4404402080c20189042e00c01407410b41e00420940b000d12007003c1c075040d00400c43c6450301c0503041070b40f141e9413000c10040d2507900940002c800d004000401064001545800040407082080a00d4060782400341c01d04d103010310300f8002c0c0d030026000140f400002140d00e00c2410303440300701100240201407042246032210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 946830089 1250 946828839 946828901
    0x203120903060c04080a1e1b0602010507080919170a0f02061b0406051c060806071116060c0f0c0303020a021f200a082101051f08040c051012 62
    0x1307406e01030003610190f1000119900c1d1070460b001c1c440c0d0f000d81d8a00714207004105c5050391b0350660084100541ca4500098401406030700814050a581402003011070801e982103000c40741404001c4481d01c85090b0218010340c1060094000d2131603c0d1035400d220100c4480c000e1810500900c030100411001c6891500204d049d012241a16294540140d50f280200e0f410145101911158090941740510004054a001c104540100d603a585c4078403078a104404025903d56881d060320a452207200e40801295008502e210340031841407050100c40556038688113100c01303160b8800d0300035030482c011032030131442c0c056403854816100095002a110200d00010200410750500414061100c07d03a4032000c8000c20031044007035442601c103a07880003000b03201b80c00160001018408055024008152460441c0b0081e480100000c00c50051030144c04086171031010241050364851108000801c0356200d21202c9101d42003291103c801e0764a88c900310070b085960218004400c03c140465403100300c000703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 946831339 1250 946830089 946830103
    0xa1d090c010203070f0b070c0b0403030605040e0c03070b210f0a0506180f0a02041703040906060206011a280302130f06050406030906020d1b08070302070b180a0203120903060c0408 79
    0x44846d9100642e1501d6095a4414240801921000d025001c210030940d140d00702000340d075401d0340c090042c6256450305a90702c040c20518103906400840c0c0c240308000c5100090141c2c021840124100c40050282e03460700103005440c041e8103003000303604000c0d552102d070084507080103080c0c0d9040460201c203107841d0600e0201a0a040006070040085401841d5070f4060b0750150101c84084082031803608030b401e40d260f1003840f0b407050325400d1034400585c0d1400840c0903412030304405a010b12800c0d2a421141c07050340404210640030304048981041c40524102400044c60561030050380c0b07603004030000456501551108040303400b0800c0c207008240d8080c003540c040341e040d8200410558813600d01071010f40107481900d6a03041c601034030307121545944c040101d5181010740301e011440d00d819000724103034450024054444102d000214520350002e00b180c1c07c685600f9000d403440b016803680001e04040c100c92200c1019000401c0b00e03942031806200b85a0401c003446d0f009442c06140c80c00303881c0c030341c80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 946832589 1250 946831339 946831343
    0xc0313061d060c1c020d0e0306102706090902040b0a0305033702071701050108061302061306030203090709060e0c070327061b1106090a1d090c010203070f 68
    0x8040b0741040c000f0410000809002581003090301180c507218002541c4441c50580803002680b0300301c01403014200458618000d03101c0407441c08095060618403480400110054080b11041c00448004404d561140c4006450300c02d0010410421900400003910740e813070001d0f80710303005409041000134030000443d031210300310210103414071f18505101025070340004c480b2003031090440942c400c0c140d13000c00d101c0e040d9002880d4201c0e0080110035440d00300e070000d0040601a61201c00817601d20f0246010f5404082c0c8020181841e00758010b08520541007150300483c0440e0b004400c0c449030100620030b51014220603542000011300d05a402d940b50700000e050410252000035460b0103152140d24044103107001101480f4103440b10801c03020390400d140c0310702c0d00040c91440040800f1100c042109500a80002514501d0348100e02044015032042d4010781d40b140e21200c000500c40d040c5284002d15088021824840e03152400c03031241800b0f904980d503030442d00700b00003040005504200c500301c019 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 946833839 1250 946832589 946832599
    0x8040e070302130b16030f231b0d0c080f04080f010b0a060f090504230c030403080a0c020d030c18031104060609240309060f020703031a010f051e0c0313061d 69
    0x90340010381d11640c65440410f0700d11044001e523022003041400510f120070420001000f0450140916526007035036084d6000040c05a0700b4803004034610901812145210003005494070340c1e03818603545002030030f48000000765140c5284071854505002410300030b11150809401030522108d0080070000c81d8090a0311540c0c0e9000007003004e10403009031170f0740031042c1041003000f8180a000d001080d0400c0b201200002d402600044210401e80680c550300b0b41e058004000c00920700c4020b80103452403852240c200404854281c55581040500b8001540941c0030113100041001c24001501d100b43c00500034400c52102c06c000348042c0c01c4410302403c0c20740300c1030a06c440c007a02d4100d028282428001c0c081c0350502170070402d482150390042c050780c2e1081c3c4041050300c0e40c0b00c002d60300007140c5403c000d012682c45442d00103c03502a00041026010310b120b08101c200c81e004000c0785940048081c6041941b000c110074685090b10b09454004d80814103044602580c6030040d0200701254135241d81c0a8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 946835089 1250 946833839 946833857
    0x7060f0804050a020301020a0c061a0609060d0e0d05070203073507090908090f0a0b16020a0314060712090c0b090f04060e1b0c0604020d08040e070302130b1603 70
    0xb202040c41140445540100255550788041c1d0700240000310b440015100c1c40e14210180d0741c0006003503d00075a0030b2010f800b03c0e060400002c1001110307004042c00c04640d80c0c40d0210340482c41801c0c0b0425447d11003c1e04d9803a20344a041c0149881c01d00e8507080410100003080068600034120668052803102c491002d40350324025141c0c250a000490b809090501e080c02d603004200007410300603106401003510242900d1420070100102142c05200e41d080d584010003406503586103102c12070610900140c2030301c00d01544d80c2c2da540b4550006003482c20b1582c0019040c085032650200c58404c00343c41c0c11305c0510034074100e41c80e0b094481040344104c1c0340c10803000541d1000f0f0703190b07640884010900104200501076584051510340c02045400000d440a4801c2900104400c0340035204404001801014156155400c0c849007054030310781a01c4241051100042400c10080300c0e500c251250b0381d0141c1c0700c0c8858410209411256004112504000d202c034150729115003001400c410307018a041580 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 946836339 1250 946835089 946835093
    0x121215030f01060902041703160b100e0c0a03200405040906060519080d0309080706020c0307080304030e0a06090605070b07030b0a0b040317030912090303091f08070207060f0804 78
    0x14007014034401c80842d5081580c0010300001c9035019104440030100922155200c00044e26141d205900941464203510001000441c08051000b94028091401d0540e820748652460240c0c840071121203101c1080000c0b0480b149905010f59400b001810b4101d040da0407201d000540b0901440c0101ca0203103540e92a6007040c002e0540202d00140740141800d031055510b403440003125081409495607512501c41d0703a107003287c481e01c20844616040340f0090f041402d80e503513400196020303440c00200d908c41800f01c500070520180013036008903c00c0c0c0300d000149400506001c410540340d13004405003c04000c041001e550001c04035445c05520400300c3d0303d5651844020380c003c10f1502006500300740d0380c10700411540f0700030008105a0f03000301c28103140c0084501c4484a01d02c8100c2e00901d05800c11102d05014603015009060361348001400e50f4107000c413940204030a64118032288405401c00c0803044c04180d0007203c690741040c0340e4406058150304140d000741428080141280070043c0000000b01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 946837589 1250 946836339 946836343
    0x8010204260c04050412110609191a19050a02042103021f06060e120316032c01030c0c030504050f01050c0d18060e100e12060a0e12121503 61
    0x120a4800403c1084581814140f003083d4100f181084404180306001c40007140c140011000d1084124400820708910f8465103090f090744800c03400c032440203100a801a20031001c0c0142c80c4192028101c080c031340712810090300260380002d0303e68800f080c8104018844080c1c40c0007103201c3d19000d4403d0480420701d81c41c040f450140c11003062880e8000d00c110510340c410523504a04125101ea030344488031180e01c041004206080702800300c0560340b003001100301c0043e4815450224a000c2c1c05c000201d10b6142c1d0b00310042d00c1c1070305266810102d00c007045485030768140c0308001c030000d014a010000902c1d107035005480f6225500586124444030118803441d688100100c901903180d0070140ca50760325010b4070180607076031640d6240180410182c5c02180c03140c4a41a10052058010400b034075070a26800c2c1030794600e48080f00c00d81c028141c150b080140c2c00d01080b100340130718440400010580da5240f0500d04007070045000102442c01001404014018401c800340c0041c03070311445041c03080d10b243c0040c2c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 946838839 1250 946837589 946837603
    0x801120203030c070810150f06110f0f010b0913020a051324090b01020a08030a110927070c0b2205190309050904120e0f06220801020426 60
    0x2032203e10607601c000c5071500020405c00d90307003c090002405240342d00049801f40302081e005481703480c2a640d008001d414403a100c017002c040039440c1030342c01d9203513500009401c0c9049040c0c4805642e44030301100515003400c0031407551002ca140320106c07402c58241d00181c168031080c032800f441281401c0c18254183e489511035038085a5070440182110707803590000d41c107580c861140d072003811f143c42500000c03940003007080c0261540c40024186140d442c0c1083c40024120040d44000d031803000e0041400e81c0d22442030403601408000640c1c03c0148504915002001000b07185c070040100c1703102c1d10800602e6186403107411800003003034a0651800541c541c103061180f00009001c502c11081821001c1c2c604081c1285101e020790780721149540c4500c18003c01c00c40948001f804844403086080f40580306180c2d800010100905020b914203d030ba0000e503150300240d00c0307048074a0100403d0740701c0384d018131400c10061006100a500781403400c4095000312090030030070001d0555854805c6440b0780240086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 946840089 1250 946838839 946838857
    0xe01030c0201111803010f110a0305070e060c1605030d0e1e041103010825032a08010209040f0603050c090c0706090f0b100f0b220e040c060807080112020303 69
    0x585500b21300500e4a42c2000003c41d19000713510300b64900303002c00c1c420b02907005450ba07001d442c2840c000e41090214020240180103070100150b182000720f240c1d50b47d1000b040741d20f074000010401d0020041c0130070703c044503a03405a803003940301c1c4620f03d61154003c03881e10329105040f918a12460580d44540d041c68094410265000c0d00d002461070f980314404001e941600e0340d0108517204c42000440344003102140100307903c5022602d01003000065960541900505514020024480c201c00083d1100e21496000104c09035004180300106041a100b44000100314100070701c001441c40d1030356504c541e03252140304e028420074000115014641421119030340d601403001c0004202d01d0078040251941900100e41d00d400c51306c04209002910f003a070400743c808100002454a18020b101000d940c0f241c0113030300750390504031007191551201c0030b400c80003000640c00c00d0041d13103464900b50580c8201c81e0007450a0040e03410074480d006a00c00e2081d07041d92003079040e120142189000007461405030441c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 946841339 1250 946840089 946840121
    0x807030908190207080706050909011230030b1503150a03150f05010b030f0f06040e06180c06180105030406020c03070f0c0801090807060f0219080103170405010e01030c0201 76
    0x2c104180f68000780c1e110031240c005098030204c035100c2104441c030380710706089640e02c07000361170042c00380390744500201c40c4181c071404071041800c0044c2403400c41c8a0303103641158145400303110040310720b68042c01081071002088440c9401c2840c11400714144d40006000c00c0032403180509a500b6075101c03140500d01030b40c1c010b0006080c600c0100a60005800d4400345214054240000080c1042114007600c0c0540401a4070001e255900c0d00e0841c01620000e000544c01915804161100b210a002e5030380071f0001508041c8a2018401d512440e2800b00080d20b40203080c05c110420340038103440900034602d00c0902c5e00e00d95030344841c14540080e0084c0c03082c1075803501001070102c0410403c0301d5544c15445c4502c1d01640c050f9910b40d002e41c202ca030708140c05002c9010410002000410981c058000712400e035400505001d2000042d043d034140c014500d0300420410f6005100344842a2000c80800c80c000417058509070038500000c0a2240409010341030580311040564502c2c000c0d08010400c94201d25 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 946842589 1250 946841339 946841377
    0xb010c05190203071418060d140708010b011b03030e070f030c1d090622150b0102010c0f02100f06030f03080a0e0304051507212f030703110f0601230d030807030908 72
    0x5271580c69800610900d0641d45c640745885032254019004080351152801e408080c80e00c080c0c03016005810300840c1c44d44280600000418084c0d001250040034601a01c200c120103400d115103040e80c400842e00c040c002a200d4020401b1a8500082c4591300085d10811860800c544080740c102030080c80070000c3c609a620200680000c01c03030750001e002030b8401da0003030180e0300d1080410781d00200000440c10058000b060750a150701c074039410107604d25a8041001400543d07907100c0d480110510384013280040c0380c0c8418002c40761094003403070442e50100e002451806140000241d000e8403509540c2c000010086414000d00940d2042d880e201200c0760703071121144c1c500030300040041488581c4581f0800d551f040c10803010030140d010f080c42c8180c6400a52602e011a03d082d11071155208031040544036001c0900c0089405100250013402c0c1d50894640f0048031239140720345202030385141805400c641c01c2c000c000ca0f0744a8481a0000175900380025039400307506110450388160381c502d0b451184502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 946843839 1250 946842589 946842623
    0x8040506030a1b0804021e010507021008062b030e010e03070602070f060206150f21150f0906040201050c150f0106300b010c05190203071418060d 64
    0x74111000341c15410b42408a00c40709103c060350f8440e010386011350801000d00038030b00f00080d00314449180350014100b42e801d0082590008582140c0d41c7c401a00154064040c0502400d007106408820110121550010403d00c40d46082c80003901c503010f4200140c42c02124100e9004d101c0d0100b002c02c025042e540d2680e201c0310060b564428501c24011003c0162800184042c070108045004516410100385101c03840010408105503022005a210320740c40c1c580c1c082c0c00c20442821120702420320283c51900c3c03548254100f2034200030302c0d601080d00a0020010700000c0450481e030f1050b82400c2550302c55aa4102c1a0300c0c20020150070740110501c1000d1000c12040001380504030364031695002c4024a40c40888149940c0c5052054000c20300c81e040312055103000d070050031060b54103242c02c05c1080b4880d00c40c1803907c1c0c400100c43d549041d50007030312015030400703000c44c4000e400e50202c803446046001010803846110f608000c0202d41c0380d5000b03e05a5075500041d0a001c1d50491182c1d140c1c0441a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 946845089 1250 946843839 946843841
    0x203070c06181103030a02031603350a14071808030d0e060a0e1905030f0d090c1e120609120206150d0c03030f030b060301060e04050a020306061608040506030a 70
    0x502d4090341c04145800350f00c40e0702c2c07034000201d400e076800f82e82c05181401c810010000c54a43c81100460621030b00c0e9500c039807000d48544400f01c050000c10a4070b1050181e40000360507581c0003410a1412034288a406800d040307110102a401215901d000183d0780640d0b010700718100c1d05a0800402400009800f5880d50b005400c1030b180c000f000401c2d00c445480e280401412224035050a1820740c102c40c0c640016007400210200d00c580c0602c06a071300e4101c981a200d03003907901480003981a2584c60301c4503018002e9035041d07100900091320401c115640103071104c0c508800305105003d85050b640300880300300302040d003201c10300c55402840741c6441c1c444100041d48924045810104203004c07151400801e00d08082c10b419103541098002c0e1100381183c804807503a10071284c0150625442e01e0000b201a210800114000c000654464a506010100300000e98001501d820407181c0140140091580d03040f049503089581c102c1c3c2150035a04c03524003103840d4040ca40c00113a2003032000c070800003d40da031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 946846339 1250 946845089 946845131
    0x1008070605180405010518090c030a0606180e0c131e1d030406140a0c0b0103050c01020f0601080c10110703230a03021005130c080a030206090601120201030203070c06 73
    0x20b42500352030049140d4061100710381c400d1140581c443c130120119402c18107000b10254108030440d081d0b500c01c200200100c0d160664281c811a4515030320841004101c081989580f1001c6030700b5024040702c00350014060b920303500d600e81c0d075124a4610580890300503d6912003a052120030300555449030742ca011101c001c0642400003100080654407000c039410000c42103c0507a0f500c2c0e15903807202c3c100d02e124071840e60410300c0ea460074425030141c1d20700880c07484110366001750300c100018802c6820900009040150044100015034008001400440d10115500380000c800f07541460445181c0c400c1211100d202403203007403050284035404028009011a810440c082604014405607000040ca980c3c950040001400603040300170502002c04180c1c0100313030404514450302000028544500008003000c4c0d1141c0c40c03aa104410550130142c040c01460f41c003d41c6240030b0541585050401700c40c0300e050311402410580c0c00400112560700880000100c160818010403850b499201000b5075446 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 946847589 1250 946846339 946846357
    0x19110406050d0f03050d0f05040609110a06020c060c0312011514070827131b180303030c090e04121418090603190c1406090901030305031008070605 65
    0x2040c40300104650610454960321164081d818414803491070f10210341c01c1c0c02c1001d0896895031140c60007003480226004081c042d6010f1540001d84d80350910342424400c0301d202c1803a004480d6036078108407103600803c1c0c484aa902c00c0c0d504507913a00c90420b1040c114031506480445a2031680008141604070010005000880b511964100449240e11003054000d500c00208984001c10400303850314051101d000c104112552492896100800050b030004103403005455240e81c0d8250312010f0b07130702d2005e03030343c0001003182001a030341c5091601e00602d0044502001d01410346904906050503c51140200102981c0d4070300282424a450488805801d0300307910780c0080d17030f141d00c0300d0400c01c044012258001140401c40759054440d40c2800320320b0344002c5c241c56250094560140f85c2441380c1c290f280b05548120103881c8054103104401004103030703550500d030090200b400b20500c40d450b140d41e0300d8107494050411036121b80d03034241224420f0b441a00007115600071550002001ca81200c081c200b038071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 946848839 1250 946847589 946847591
    0x715060e090d1e0e0409061b1706010903030c0507031e200109050f0d0f03170702030309062e06051908311a071106190c02191104 57
    0x100b0402c2100c407a1900351500811440c00900c1d10780c0301c3d010f01c1c00100402e03030140020600651644505048480a01007103081c082050303400d5904c2c0754010204070400001c3c3c2134140c00d80c140000000d21840c0749000003401d00642c0c001040c1800b0040014400844c2d1280d9200902e120b081170803585207004140440f00841c4d8400c801860110750703000805000e1041e550603210038500020880907210417041107402c13010400c100c0c8040b070a5800d442000e10b029403a200f240d04080101c10300000e038000d004904641003030052101140e804100350350010741d100c440d03240704240d41e40380d0044208000c501c2003544d0a403c0000403600e070000054001030410100f0038502d01400c020550303d15004966800b101040410403425101c10b840e40c1410300404202c0c038410600031641e404000c4040c00702004c840c48a0b85080010443c2e00c260252029054800a0328850502620300920780c1c854503c00c508640c1c48528440e41135108020404213400d00c0c121032049001c85007001032070103100c40c41d118061 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 946850089 1250 946848839 946848853
    0x509010e030a0209040b1f0b091206070203031f091404020a091109060714100b09011d04151b050306030d0203090a031704030c03080a020d030b060405060715060e09 72
    0x646400300b0390b4100b803a00900a0340341569503654502100d94000d2000b800d070194208a07000380e4540c004814050900200e0460361283d0000800054070745447c0287c5141c3e00101c00c001e1015404401d40341c004a03a418000c40340c1c0c200106204100c611f0360807484804d0300e070141da01251000c120b002e50003503000391075008180e51900241d0003601c2450416000e014000c000400f83c0341444401800c400303019000300040f0402c030184a50900b802038103440303082c940360841440f40d858951071050040c08000d000465400700707140150002040100060640d4103c80f01548000c030580d040050010070404491410902030b0300e01910307035001038802030f0081c0b103038202805009000100704c82c3d1a24009040b038000c45c2c40c69032041240525a954490780a9044c000000091101400c90780994490400992606003002e0b000f1b280c00300d065015820035040c9940800e01d17488600c11101a200c0680302150780d000c80e802c0450001c6c50f85102e00300100d01d8202e0000740e200c0400c2680c1d020340544819540d603 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 946851339 1250 946850089 946850117
    0x60a020c090a021326011509050f130204020d060513091a090a0206030915180c03010b1005180613030c090507172d01080c1804081309020a050901 64
    0x480c040d000c41c50307400c4e1040d00e40c244039402e4441e151441d21100c036010044140c0300c1440103400d5075840c4440d4498044015014400a0254040c0551003542a651040f240c5402c14030513030140c0540c800a0b0250f640017403800009207050300908090300300170b030501c0415a901c01d402c01c02480441000d84030f107020070074440c034012a0103010601134842c1c400104904c100540810000380e1019002822610580644000d0450ba40f00e609229a81c0c0e101c0840c041030301d0403403c5044c0695a00540e1081c2d1500c1301149450703440540300700b11039416161442d11048900c40554600c1100c003c800d6100c0d00c0456541c0400c0395044404099a1192104409896552603e941507520654102000c00c0e141c102c5216210001120785a000510304852103602c814041c001005c89640050310500344912030051002c100d08010a4801c1a41500c8451b41170611018100310120007500c01860031900180d4100701c6c140203450100605804c3c1310441d9140301030100909140c0c403603c206030109682d030004043c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 946852589 1250 946851339 946851341
    0x31211120a020717030906031905070c030306090506030604060f0b030f0c180106050415140a08161403040b0c0c1f0507031415011e1110060b0f07050705060a020c090a 73
    0x101100700700d13004609200720002000781c9504000e0a5000e8058180101c5508121138041c49004480307980794014840b44509004061322101c3d0400c3c101c040c181010b101003900c0004400b13038410307004840015000700c06010700010340b6400d4040c6a01d403090240c1102d010b400410303000c441c80d80031180107158000c428541e901a80092150740081a8140010021030815040c100000c01d01131502541100d110809011a60403904000b030010300365008000e551000d0032038801c210f207003605100c5603891218450003007070b00c00104024021401e80004c2214150054181c030b045952003000d40c1e201004031040601c1044010214503c0d990a2101240c203980c022710070b1000541d5102d101c40b001e07680320100c02103454034a464981c10003120307002041c010049110941c112820541d1488440c68a84c0902c52828014001c1e502c00189003c00030400b0f008160100e401640f600084180c4640381400c00e80e00740711142d809581c01000008800c0c5007940e01040c1e25003400d0341102d9030b00300380e187c41c0f24501c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 946853839 1250 946852589 946852619
    0x7030e03031506160605040b0c09030a02012303010b180d1703040c030c0b120c131e0b03100503160f050105090409020406030803090d18031211120a0207 67
    0x10460350010000304507848815680b07441410805003180789060180c121040014618007025201540d40310144400c10038250f490a03041141841d00700e044c182e26400181e25090040402418400208580300c40c0a80140345041f00440c410030554503581d44d0702c49400107500001c100e462500b1071700d02502207483e00012001c0f02c47d41140e0b0102070040e0f80f688030169540050300585005c03044c5440080040c00007151400640282501c10303494182481300100d9010b00036100d00e04160707050000c8000248582c0c0002d00b20b4101e00f00c4c0d020450722035556900c10742c0858016140d410400000c001c00c81d4000c0c0c035071030200d420580403114690040650b00500c4145401540c040d01440d08040045610500c050301101c5002000041c1861055000504507056a0b200312500701e800700401c50905024840c101d02540b09080501203d02c009903680200c0709a03000052070540da54618030800c03889409084010030480c41210001e9449041c1a641508407d43c04001889006004200041d00038006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 946855089 1250 946853839 946853861
    0x60c0f08330307090c030e03270d0b0703020711030d0207060503180102120a18050c060d0e0a030e03160b030f040201022103011d01031e021314010e0703 67
    0x20303400c890001401d440102907210505200a008124a109580e800340484401400700c4d2000150082203c0030150030345640d142c026116420a0040683c1d02c22622029582c001c078640200c406050b08500044080004007000b50503688850100a0615096401002000e028154031454414800200b695800c1d04145200040e0020542048424020740c003942d00300c56030f020030359946009003040b03d0072030304144911804038050100340f01041e0b03014802d0007070841050500c081c4030451a140c0950321540b010b485400382c00c0000c2e01c3d104007502c607400104052a07520545107810746c42e080082603502c009900b60b1007400b522154134523498030741d40c1c0740c0d0482d6011030340d4900b15504c3c81400310114100900c207a043d030080b540c10704001d41030403d40a050b016028001d0341c60754103114030a400c1300041e051b41404105030400500200d40507000d2340700341d000030b1a61140e54211903c0031035884007401d510040d000b400e01c1440790f42580000e0101c2c2c181e600144200741d0a6545c08002c50660b607962940c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 946856339 1250 946855089 946855111
    0x1e060c030603100b0103110d0f0b040b1008040521090a0b1c11090402030c040f150e0607020f060a030e25050d050319030204140103060503120c150103060c0f08 70
    0x21941e11000144c01032882039034141070010f00850224201d44440d07000042c0b500c00103540782d10003145800f040c400d0456500c01641e042201c0d480c145c001c40ca0305140300d5081d80601c0041c000040401c4410040390320804642a0540c11070914220005c410380c00c4988194801c90205034081400e01190094400701c006c011456071034500301340c40c840000c107002c00e28060402010031101d4503030b454038001075001d0741c81940620360b1285821340b00a03102c100c03600080e100c03440d01c072411141c0079030007030b83c1147c411011941c0d2031b95081103100040030030703c51081d513503003340b0007045090b04190141c3c07003c010b00c089a8280e9541c40b20030b0604d45100d020700c1c00c1c14a1150400503043c070080c14440034075002c0500c640103c074031f010b440040c2c4890907144200d0000009800041c188000c260801310307052449400e080a00c601810040005c3e200e40c0400304d4004030500106140481040030803076074903800701610701e800540d41c4034100340b0f01508000d1038000215001c11144000a072190f1441072041400c0c040d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 946857589 1250 946856339 946856353
    0xc030d33120309120302062202013f050615040b0d05061c0f0221070504050c0409051905063a060c0e090117060105120a051e060c030603 60
    0x9501d0301c4100c40700300107030204151040c001c078442020040180d129806500103003406d1400201043c2c003a0580c5103482944502c0c5000f505c0140d030843c156844d407d005410224600e010b03500880c1051030b0100000c00d40760308000d91507030603a540340c6c0081d000e2034095030b00181f5445207a400c0d0450b0f1246108401d049002001340c0802010240e00c0150840381c000c1c100070804101040e181842c01c100082520300c00308259040741185041e96550100041301d414009900304201d5159480b940a03200d03150040d501c0d034000550041402003214081c00201000f00041d05004a01d682c1030760810b03e0311b00c1d0700c0d4035007000b050303003440c1c0381180c60303154240c42c0c0759804035240905d0014545e00c200e1004000c420384081052000592901450281d407646030750700828502c40c8010800000c00681c0060800e14002034107885910b8003080c0681545c0090320050344062042c2c0065151129030680a895400784184280ca5501d5180c0c1041d5015a01d070111101c0d80c0320394001c480f00b80300950f0a0f0742d05a110718 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 946858839 1250 946857589 946857599
    0xd09080312060102010b0607060e010c14030a201c05010902090619031b0e150301060e0f0a080706050301150f17040f0203070b0c100501050a0e0c0c030d33 68
    0x1030510780c1c00b040610002c290482580c01140498214800032907041e41c890021846102c424030078140441c0040c07503c0c00540100034550502440060400f800c680c0d03d0740304d01070709030307140e4050181002c0140106a550303c07130283e140c00307404805603106404203092000008100c0100d000b91200c003400200114501011001b1300c8034150b0141a00d1006c0c1920781241014240034010007141e0700c8055203a092219000740304020000800b10f42c01d4800b04030901c0144000c540c801e0085e9080310050710b280303010441c20000501e000103654086846031145080100d15958060040c6048a440309408201701d41074038020398405183d00c400c1800504031149d0002e0015064900b950040d001e195400240d0882e9004603042c1100d5401040ea00c3d2400501ea04075030350704102e07803039249141385410040c95050a000840d464850300c11424045950000715135146841001c8070481c180300d00480b5958100c003c144c8000e41009001c3c10340f8510034051901040052030f41d000c1c2c401e000b0400d40c0d0103441c101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 946860089 1250 946858839 946858867
    0x1c0503032e08070b1e07030e03240604020a03020c03040627030321150b04051c050303160909050405071d060307090e010609050a09230a030309110d0b01080d090803 72
    0x7100a40c84042c0010b170440b10b007100090020110907001ea620404001f8036002898501141c400d052180d904101400303000107514858059000308089402590302c201d0008100c0190148043c810010700000400040b1160020103111100e2220203045001c0b040c1c1c803900369683e0b45240f00c043c01041c840183d0700c5140325000b0030741255400c450f900040d01043c0320b00000c40c0070201d4114072101d200003d0144400e1a01e06209007c050b100441c038407203414035a4801d901c90001816803803048019601c44441280144940d0b005407400003000c100a16103410000d0380e0384458440c0b060082c1711420305411804030f2100d8581b08400140080c40b11924000305d6170300501145d600e201e5107550f01d410208100700240a16801802500d001080510103420a108c100c0300d52000486c040c0404408003a40010214010f4081505804c000401e040070b410128612120020071a510480ca281c0c05010402c0524040d81078400000c2129070800802c501981c2c414281d0007131001c194000e2280e29084400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 946861339 1250 946860089 946860097
    0x61b0b010501030915090c0513020403030e04020306010c0212060a0c0e100c050319020a050c010207030c1a040b0304060509150c040b030405010f0e030408060a1503021c0503032e08070b 81
    0x86001c1071061200c4041c54401203440c6c0324000c50321140110340c200401e1900302018040c41003510800c51406103035507000b0b801070728a914968090b40c0c002c40001d400780c1c010402c12000c1c030340182035141c009920840b030f90f84503c403c0310b54040441c0b80ca0307050102284a80610b500c4260080d040c081607038101d0b481903810f0b004034802118144420011400c06002c52110301140300507907001040c13002414503005042011000e047e5045500c07620040000c100900c91b010b0403591101c03181e044130020001c64420b50b100705c3d04194a0100000207120400940d640254443d885210a403100c0700e2070f0b070840704100d04043e01d0101940034184420700c8240302110045402034403900001510000c07a4014400b50f80f07616010940a420109041000c2e80003480301c41d1f0300c400143c004012074160011010b884403400e00003e4007803000103100c0c00720480c00c4144800d006422034200c0317440f450903020f00c076140389414540055034011142e5102031174142d13240d05d000380c40041c1e028111030b50800343c01c0d0b003a90304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 946862589 1250 946861339 946861343
    0x503360901181d01090201080109020c070e0a0e0d090e0f0f010b2206021c030b10030906140a050912040b30090a060b03030c0a12020309130501061b0b0105010309 71
    0x81d41c0c9100e0302c008120360850303c0700c4000a000100b43c0001c980000f62040d10140e102403034a074010000d21a501601207108000d481d820204140c01d40c84428102d0300078001200041101e10501c40c910302d120f600840614100c80c84a17602c170b04241d480725841c2c5c11200040c0c51071407004006c3c00040c088604510082c10341c1d00d2400010b031f544008602481c40c0c1c101c40c40c2e4460000358101d43d401b04685884a0061070088025050500a12800300c000c60f0495803524000d40c01c050750380850108203c03103500201403004034a02c5400303003810300011070340c000c1c0b0042d186006c0911500e090715030309010b0741c070940c0c08882a24003603e08011540c0c02c0541c3c1d5035840c074101c00038500e6002c040d8501d080d5030301c00140070303d08200043c00701e00c0b407610702102111500300c0f80e248240d20500c2000c561800014422000310f0380958071001824040714103034654007a001c03c146d440b00c0d80c1850340900b41c059078030803412155207581d04000180b44500d0258840100c0101070640c80001c3d005214950007904022070880c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 946863839 1250 946862589 946862591
    0x11090a0912050f0c010203010b0c0115140f010309141b18011211031905010b0a0b09400c050a050f030405030418090b01141e030307050336090118 64
    0x44c04000c5030881c1d00c260804d040c130041c0880d0740c503e81002442224460303a0550052000745040c0818064440030300b0b05164481c0f50902d00c500c409921940105400c2c6520442d0660b03c0c5072040580780c2c5440c211041c004c8582512100110140761207070485000b1018080c40c001c8503400c11015140b280d02040046d81c032041440b5290005807020801581404680c885007203540070b1a24013142960752040c8a03522850800e01c062284031001401c03114000c07001c55051010b0030707c50106180803410080301c164414020044086158990784005030800702d808002c00c105010608162a1070243c1004040015801c0c040d0509c1a0742d0703036000b1900240120116400c0c550f42d10569541c0c07107500c04e0708506250300e440343d42c82080f206110107030260400903142803100c0600c00100300a0901e400c41a504821141a08102600c060041b540c5071900002600e50344c036080310dc031302d0095042d4001180304c1c00d0303802244030111446400d01d41151030028903040c9582d00c0c001c0904080303d60f4002c1c8101c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 946865089 1250 946863839 946863847
    0x80f22080f04120b0a1a0402030702101d12130501210603030e1009061b020a1503150f05010504030215120a06050111160306180f11090a0912050f 64
    0x4041480070b44020074610300c9a480e058910301d070400080702e014061415460604106030003400c8805200b0f40c0d40c0405503001a20303a9640d4200301d1402c1250088070200340d1074200700e031806543c5407a00d07010b448040001c0b1040c07010440000030592007178070003800c000040140103021943c49007071885280421240d5654070805140d50729001c8821541c0100c01145002c2e94000c45410300748000e4050341c074a420810700705423402c2c4018100c1d00107251101640280c1d91011821540d83c5c270108001b80c441c990f48280c40c4d01c1010000b400501c1924688036483d80399000002d81d40b81c0180002007a240117030344050420f417469090001c0200d541104505a840030302c994024510311040e414410002ea04010134075501e458009400b0042c5107032080c006402100901010280c01c1c406101101d0b84004001040c1030646690344107001030840061410701d1034901e0703400340319810100f6030001004642100c410348409008070103d0b03004100052070138040344601c500131801034020302860100030074030b40d01e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 946866339 1250 946865089 946865107
    0x901150c08040803030417070218060303070501020c010f05010e1003020103050c04080303270102160f1a0403020a031709100c03110d3e0a03020f04060f080f2208 71
    0x80307070b08a03030400c4019030310101c100818418100f403508182035500e03011702d152209540101e1100440c66001e840448a00030208009807020000c41c0d0340c0d00d8001008544442e503410f4800d01070040e0351601d451050501d8008551601c006004030b010b00703104070104a00600c3d50340158054840102612041001400005065a0148000c52240491500d60303040f0022544010118154130b043c0d03500d40fa072050000a10382d80a2048280b00c0c2030300401c40400107805890110f00460001250460741d06806e014041055000602141424441e440302615141d07503600600c0c1c02d01d001c41c0d400d1803550001d810000e00c461240d100c0100030203203141c045040202c4a903d0f440c80e41c45940c000320602da030307803c0080046403c089099148004082e480086d11003426105201c034201c814064a850300000d90000c50902aa049030240c04c280d400d0603031501e68640000c1c0c151454042c104000c500341c0c4c4002000d103602505418842d0361450b450010b85d00d00c9804040440d02000c1c8110782040b410083c080b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 946867589 1250 946866339 946866353
    0x50112030c050a2003060a0203090a08070c05060a120501080a0f0b09010e0f0d0e10020309190e01171b011b0309030206130501020f0c030604110d060e012003060901150c 74
    0x2101581c203540341c00c011340c40c02854988440200401d2901d0710500520038004000b00d00003a113240c00201098650700c1e5401c003a280401154805c507800200000ea09003d0b5400161042c904901ca800400041ea84c50701e107140c481c450500c0080017204a07030480e000241480c1d5400c0c3d040492107000084004512807451b2400700021010103e9511111a100105500c80d9407603071071050903140d00c1640311070080041e590303002c1c840c0f04030b20600d90340082e00c41d43c4018000311001092400380600c41035940d03510542c0d02610126400d4030b50f001e2161020901005d0304030000401c00180c2d40d03820003481004c09641c0d02c01000100724204050b1a00000141c5d49410103080c1c40d105c4449180c244914180c006407609001d0b010303a600c04d402c01000f65200c0d590200d4026402a00031070020a0044020000b0300940ca180200500183c68541c1003a1030003415800001c0c20240d00c1c0542c001a4006900d091480c041102e07400c1e0300040f01d0006103d6005125001044200c00c2d00382081c18407190b6680c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 946868839 1250 946867589 946867613
    0x7060302090a080c100f110a1b0e070e061602060d0b0102010e0708150c0d150501230304150b0d050a0320062e060c0c0504050112030c050a 61
    0x500094001c2000303000d51a2820b076950060010000910004545078041008000b0303000a89041c043d04281d420045c0c0d010700003101d1515280f000343d0303041d201549000300307449001e54058030f8403d07401d0502284ac40c0490407a64002c14135a100c10f11514040d40c20000303541c0c84240903110050900c0d11120047e16010003400c0c0f91001c0701c3c00403810b84001e41c002802c5071980070006540b03500c11442000702c8440807580c020104500f40b000c0d103a6a03260036248060340b04011202040610b0300220821441e805c00c01e400c10307140700340c2c0c82e5041c444100e4010002407190f40130b204181d10080000c50300191708442d085640c1c003050400407038020502000900702031003054040d07886400c02d0009000b0141c0c050f00d00144985071080002d141881c80941e146e451000505003c040c2400844203106640b104854158441000b98400041034851000030f081d0131900001310703080342200201142524250207400d05039440031200002c40e41c41c0b07440407594000802401c1d51a409005012004566004980 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 946870089 1250 946868839 946868849
    0x90c0f0b030a1b0f03021e03010e04060f020421020a0b160c08120301060c111009050f032803030204050a0e04140607020613030212120105150405130f0e07 68
    0x9500c1e403030005010307010b031082c03400b01c010b800182c0e03100220080e03000031030030303d00707519520b0016222a0352101d402c414600080c1204030a1802100004020030300e6001140b1451050b403041c862b01d046e6038140402e030b000d207001c1c0044c07103540313459001d0f02d10780c2c3c0200c2028202e000030035032104940d5400b40080d05078012034105040c50304c0c0e0810070701404400790800000380344400c0240005254000312005501060081c182001200c1d25008244522400d0004070580028103808140d602e0a0010f4102d035440c6c031990b030051070100c0d403101c1380f0721b0b01080b8081c1c042900747c80106007113110010128414000c0004a09055080c40042455150000c80b980500401c80c15140d00382842d052200d0101c100260314001640030f4020001c0c2a9408151a03070400f0f4082051510303401289410b17802d16071924014403980c0c20100708001c40c001840407490403030340290303601c440c18075070f0700e01801c1c45100d540900d5410030027070100401c0040c059403001381082d0100000040f28202280c646091815075400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 946871339 1250 946870089 946870109
    0x60606210a06080d081003141c230903060c0a0c0606060807081f03141f09020f0111120a1115150d11090c16050a050709060e040204090c0f 61
    0x60212120810039260113040034200066180760a030141c0101c0c1100740001007490100c0300407060600c104019010348a8503028040010a5421400a006810311a00380c5280c01903403004a6146074100300700c1c1c0b60404090041c05a0390348811074a80241c1c00641070404000441000e80c0110b04c8074032429014020503950b1080500700303d140200314020181095040520408490503070310300b14600354040301c0d440285414600a40d21080c0d0501d00442c04100801c03100341800061400103501c124642482110041c2c1c01491b40401100c00564088800205a01080b6808400d450307007005024042c0862410301010b01c201d980c01801e00b403181c80c1b0b1000d4041e02074103003c2c0c225110b0380515000c0605076600c03403600d602601c0d41000d810040c54001d00507004a00465000c04a07102143c4640f10361040900098135907141c66540c030010803806554034040e00001040c022a00d0143e042107034640e000c8080c098445408000080100304412141e40020703400c0054003185440e0308400512100d44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 946872589 1250 946871339 946871351
    0x50303010603050405070603020c0c0d020402040f030804230a0603050c0702040c0329010509060d0207050d0206070e03070e010b0318060106090503100504020303160c0b03010b0d0f0905060606210a 86
    0x24180b86001c031190800347c00d00d4014031440f140784d240018800890a021108440681c2541c00490024415500f00f00524100c0400200500c4000c40c01031007112440d9400561021000701d0b040520451141c8081d0f1000304094100041d5201c0d402180e000000ea612039403602e0599400242103a006000e18800b1a440345111001e45844000c28030340075002c401c038440e800c01214002402845444201481070601140c2c2860b1200d165055a02080d40701d811141080a0f066020b035591034101c81d208001540c2107281d07047d42c1400706580f001c4441e0008411216401d00c0d100140c13580000345084028180200c0041240e80c08001c014001c000b0f54035681e10740f40c10b00301458204401c040054107501d003424140401624000308503290101d0703043d503904201c07803103141401c1521119440b01c0503809000c00046549203082000f0500c03100c10b10710421142488000303400c16100c8070700000d042a000040010341c181031010080c000c1c0f20842a41c180d280404201e2041c200c04c0543d1024012543d0726 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 946873839 1250 946872589 946872593
    0xf120603011803021c1215030b01090e0619021210080d170106180801020f0310082e020409050408070606081204060c2405040507061b110d0503030106030504 69
    0x80300c2e00142d031007041412100c01541d610302954900c0d42c403c0c0815002424911004044d100c2c001e4250144001003090140c0d882044803040300381110702040c5c44000090f0f00020340c0c1600380c81000342c80b03110f5501500090f51040b03600b10003061020200305095808103e151107108201c0e202074407603400000800c841a00f02704036203107003d20362a02e21041c0204800d031846000e103290300301c03411103081d4940700525042d80c02c800c50300c400300c0d640001e40321360003c102c004e00500408091881100c900b16041940b45e5245041755413442d40000f10789540f100e49418011042d644820741c998602d21b00d4001d0b1400d036550144004945003290141d400040c04100703003080200d00d014150007004800000c0c9404100403c40060318851807242d0700c18440f06000c0b540410240401c0884a080c03040c0d00c035000355800707090002c064207003260102c915024042011850a00031024102e4104905803028011402c5559450381404c01e071001590001d03681d0640350008000b000114083d044035900480c2c1e038240341c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 946875089 1250 946873839 946873841
    0x1201050f0702011103041e3009030b06042c0c031219080601031d010b240a0e03070924050a0b37050a021504110d05030f12060301 57
    0x81e041c181164100700c008000707940c485007520741003900305180e03004102c140042d2040082e480407008012172281143c0301d009030903400d280c2849105008541d10f049085500c119400d0a8500005040602560100341e42d41003da00a003003880540380c01c1d40c030031030314040100c00c03e560320b021700c10150340091600207181c141070103403060204200310724904220482c01290112141111510304000361400003491580c82908101540d41100480c619101c4640c805580600041d40f181030150039960302400d00030084503000e05044c02c40800242c1040c801c100c00300d440b0350030100280c0d450b1044040110301e00c040c40c401c81412404e03081c40d4064840403021700741201456580840c0c881c0b0581c1d0010003000d4245002c9450f10342c1200584a501206038803e4122845c20100c2074050003400030b00c0d5807125070040e00500c001c100d16000c803150b1144041098910b02000c85008290340910320040c181c9042c90310180151601c5481540d08219024074204003d4111010070644809000705100480c102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 946876339 1250 946875089 946875091
    0x1112041e0905100e130f0b070f23070302010b030f060f090303060d0201050c01090645020409020a1d0402040b010203270109050d050106031a10090b0607021201050f 72
    0x34076006118610348981c0084980c0b8462190441d101620000218000c3d580341030b11092980c04000f2425070b5a1a0520746001c0d076040311a100892540130304102d13114027610031009800700c02d00801581d01c4a8400f014a6504083d0044007551b403503420b4540e542c1c0c1c06114044180c1c48080081206140c450000c00180002901140d4290001c2017805802d071034882d605c0000d15020f0801550b00c8010759005401003000c4880030b466640b804590750211905402c3d02c50a00f41480001010040704103010186034410701400103c080400704a034005082ca41c00103c00c45000500304038540b9583c6075034803005040000c07092070500e43c904c100011072526109000c055a001e1004608003a0740e07140600181c0312540148003540072141c0380f1880341c0c0c4a00784080140c032000d4951100141a0701e08a0301901c411300046504180b00000e204c000303031441841510522851382c000c00c00c60b1400e210000200109041c40d038006008101c200c000d0b07102c00048a440d00c01e000000551498803441211070908 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 946877589 1250 946876339 946876349
    0x1020c06072c01050a110609070501020c060a0206040b0c04030503030c030601031103010302010f12020f1204060605121e010623030601050307180203130524060613061112041e 77
    0x8050408960500c0710619040b42148003130034501e0740d13002d4510b800c0c1c03040c10b005003030a4141e105840402a02400c0814502c088407003c0e021603940320700c3c500070410b00b40540300d0560016403000000501141070300c8905600304c904100d21505d044e4403500c0761402e5500454502154410001c04e01000e960b0501c07542010354009171300e0505650459000a00c1414440c14080801c034a0080c1c12060160700d904403031192401d59100c0707542d001058030b180c20760841200c007921003620b092000a518200301d00802040314220024291b040200c4601c449120704018806195660b61000440c00030714a000c20502d1840591400208400d0748040610f13020050304002e02036000b02c0300420070f03101340850f94844602030701c10168607580d45102071000d00c448010b001d4880d02c43c0c0649090751240c00403003901441001207801c281ca560746000d0104622a034010140c1d2000d92340300c01c005c0188a0314026040c800108147d0b006911603400740365043e0402e402c0f80090841c00c0404885600d400310b20f54009003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 946878839 1250 946877589 946877627
    0x5120a0504050906130f06090e07120b0915040804051e060f0a03090b0f06031b060315032b09090516180b030f0a2d0b1201020c0607 58
    0x5104044020300c680901d2080500680d85040421007545d10740c049494000301d04207040100c0c00c04848820081d0046204583c110342c44c101c0d00c040b800d0310106100c401e4820112150300380222075030340c2161160b8000c02e1441940503c1c04c0e039040540b60362800c1800f031400303941401d071a41c0c1030504006060701c0d41c4005007022090404411810388441090781c510b410000501610b9404090013500030301815100280040b00b507004006014410340c414038003440702503045640070701d144449101c5010043c2c3c3c1031640244240300041c3d2000d072500c07840e10742480140c00d6032060b09a000c035415030144640301d4481010f108040b80326401c0d070701410840c02070411940612441c24410704d14446000105169820451140c0491002079103031030700400241102e000340d540e24a054a01034422034800e458a02c4950704120800308d02840010b0b840241d050004800c580346034026180c0401001010211034011440d124101c0e8185000e1001d8540f103101e2201a018131718001400900c0403604002180600d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 946880089 1250 946878839 946878847
    0x60d0e0106090f0507142116020111030c120c19030b01021b061914030a0e010b0d110f210a050106051c150f060810270201030b0f0901120512 62
    0x40d0382c1c0b002a0100c41c1c080c06444035940e00b0f894003c0c04544178400d00042c445031004c3c0234405903402c6c0042c5910309103c5c40d4000c1114000341d031034000c040c0c0b005403265407001505100c640400807000c240e03d50850811048546881154107214000350000040074021070350b21000c810565030140004500d4150940d513070450b141c0079400040303840c0500301c0b0710142035010b83e0703910040034006c2c00e01c1c80741000d05100042c0c4a02c0d11800350005400d01032601965035003002c14441e5581030001c1e02121081d1b001710090302100503c000c0c48143d40034203010941c820054280740305100020b002c0e01c684400b03142d020b041584c0940c00d200f07003995a2580b02c13034080c221036801101c00c1c0d002c0c0d1644510305a808000d605a1501101d90b54002c0d081032040a54800d1422100150f0154001468036218420500a1217072a101c1c107030014010940340d500b00b001c1541c081e80c1c00010741c883d602206584100a089440404a00c000304402007400d030807200c080c828070f0391304009105d4108240000c5410020742c951070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 946881339 1250 946880089 946880101
    0x50a0605061e160501060e101d01050112090204021305040509030717180a0b18030604020109050103090f140307030801080a0305041205100903020c150c030711060d0e0106090f05 78
    0x2041c03201c0b5007949841802160b410b210f014504408880e076a00880203000307203502e901820382c420700c0945d6410072001c04104001100d14640f031fa00c0081c4104400300f8030481c0e182600540728103441c250022070281d541c903040c10041e078032440980f0940c40d80f68142c1401074104014042101d02c040c054181030b90041c0103081c00180303207407641042d41260080c40341d110b2042104080c5900001e00d1000d82c0840d46c00c00200702c079000a006819004404003440043d0180f10302070648802007513030b000e030014030740b070b00203000345c1d406900501d041d280700d001200d0038452540c450660324650341c040da04c2e0711380001480c40e0915500030302c02801341407181c024001d00300c01c1340d80140a52046205000405030104450400d101042c41050300e000c903858400d2105400500d4000d4448280f180603903c14040301070032200400b281d8007074482270300c0d02c003004500e03092039a00c4010202c161441c000c0c0e030080c0100f003503440d1060075000760061a2245030020502c541403403464400d0752104003424544034948010031030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 946882589 1250 946881339 946881367
    0x1240618030609020a0305120909071d04020c1002040b0a0201240e0a0204330e090408130f0303050c0c011704060b031204381909050a030303050a060506 67
    0x41100c2c0d1100000a00d4000c0c1d10100755544901d9201a00c24002d022088000401c004010b02040310102d0742c4854641d10103006440640109950241c20b00c0445012046070806900500141006004507083c4540303440461040e60700075000055056404644111038070b0302400755204251544803131884040d1404050440540c1500c1001c541d51405800300d080f0320b00035811100504400c14004504030075144c0f840101d2a1aa143d2810400140d03021240d400e1042600003581303d00104541006c3e11291602c01550304499446001e55520304030002d80080340300401d0004601c6510344903190100c40e40c120b401d214815107213a0501050f98010340d269022980e446501560010300028140c002c5c6c0040303031a080c01081d00700c0c10000e000402007010041c852010b081707560100c88030b4445a204c0400207801e003181c09120581c1001c14821959600104005460300a015180c812042c40c1d46400084030055983d10aa01203a42e0304280858888030f400758002511007610018500041d20040c08 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 946883839 1250 946882589 946882637
    0x114010503100207080715090c140616021503041401060801020a2109290604020a0f140c0607030f05060a14040b210d180e07120e012406 60
    0x10b02000c0d40043e404042007000700581c2c8080b40c01104d404000c00c2401d0440004016103002610503903104c41d070005641079545400000ea0b440544040d003405101001408034410415040b070340080c254001007842806c030406548124028000040b44000c002007081c21207560350004441c80e401042106103642d0001242c81d592440502c10f00134440c03d40ea1080e0040010210062a06d0754094078007107500b0001030b40001d01c0502d51100c1880342c464104001c120310401c0d0483e8041904d1003001c0310f01500800c07214100f50485210185060300350240307030f400c0090864045002c03a03a29081e038045801d0714415154849000c0d104110406e0070f000c40d05221102c200b554a100315161002c440c1a600c03103c0403101c00803000d148209030343c0c030110400ca40b03522181d02008009450000101c0342042044040c4085910380fa540c2016500d441004450740c03d801044c05a0080e07c03003070959142082442941c0007141c1000140c082c810f00d000780d0b90100c1c1d08a074040020040e2000c11942c0c5012008821 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 946885089 1250 946883839 946883863
    0x11704020a05101b1101090602011e0b130e1c0203030708190f090506070f0801030807062706060e07020a030e100c050f07140406060e040f2c0114010503 67
    0x20843d04071070f8001143c103682039002c9804140c0d01c20285070100000041541c4001800b600c0360042203441e048100c1c202c0d005103130041c8103400e040e0513181c4c0d440e14942c0040c40e021700180814003101940c40c00101510342c04055030815034441d00380701c051450b41e08141202e81429102643c82c41c14540c0000b0509000900f202134103400b00304004440f031425038010741d03131041c1000050107200345a0030300d81c0d11000c0480341c1c5404900445c103918545072013454030760b041c4c07a40040d5080c1000b0980c4c6549004003182d42c0724080d4425540d401140e03130b110038095107144a102d008003261950801024100c44d010140c2108250345c804d542400029400c000e1010101d0f80940c0c0c1c1e0741c080d020300c0d031044074084002000940ba038050343c1c20100201e41c0100d400d4003501c140f8491500b80c4014030090008907911480f9407400210314981d150010318043d084144520484823021504101e0500304920104400e211402010324241d0811b088150038001c01400c2c80004140401d15031500f008244c8a5460180e1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 946886339 1250 946885089 946885099
    0x307050916320705010c030e03070b0411040e010b010e120d0c05030706051806010506040f03061806110903150103050a0210120515031c0e0f0a0305100209011704020a05 74
    0x400c5040d0446a818100d82107207000c031090381c0542a1040740340c2030348015000d81d03855080c0702d944c8101b00d00900418403480494030045117407582c10b8840e90b40500c4042d004440d50703900410b100f030640c0c3c1c4500840000d0036201000154041504001511074165a049240035418405050b4080381e070100d050905500c1500f021400c0c140c00e490b0050451258a1700200b04500e020184145000d202c0e0840c80c0d0a40300710202d44041e601c030002c1054901451080c00f500c510842824400210b1a4024940e41820903380400c00e2441d035881605651500054100940000ca8204150b207010000d900103070888400b202825411034a913181c0340d80d002e15020b07020380c00c29014a40310394400e4118000303441c0107840401040c180350390400034802286040c00d00c24414542078024000d0b584880040d1100242c8524010b0506002840510f00c0c810703030600c1d8440c50314040000412028400302c1c540082c404801a81c6542c098001b46c010442e194a41444402840412005072601e0340288242d80c401c0300c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 946887589 1250 946886339 946886357
    0x1e0a090213050403050301030506090303010e070e010309063b030712022b140310061214040803010f150e0f0406051207030303061e1412030708090307050916 69
    0x205079514404048884082d1800e0304100500d940500a035058a114000f03458043d110150001e580c0d01003801010480305805000c1040c140c0120f140f109480f070181400708217803000d901c2d41d0007114020100007440288140c0c4180d1641c001100713524100035100c00c42c4040340d215400181d81c900501c08010580b44410220030314141c000c00c0b2601c51040c44208801d081c0ca424800c90b00c0d6050340d25054004141008004050141c0a03000ea034400d113000e1001d884c0007480c1050840741140e50001c603140803940c400c0c050420000c903114040c800c1e03004950840d0349514000b00b100182005601c10004444408101c0e01c0f40d0781d01003210109420211400c2d089010740c2c40c005401040158080d5038800a410703002c5d08504404145201140c2c080e803000c002e03040d50f070b141042031010f1281807211032410001d400c2c02103100d6121450152000a0501c0652114009016186600a03072044c0c5101d400420408400d190400c812000752a084d950302541d03060030041c0c800403020504410090180c410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 946888839 1250 946887589 946887593
    0x91a092e0b01020c130f050112031d0f0423011a03010911042105011a0f270106050301170a021c05160909020a0509010302061909081e061e0a09 63
    0x396000c1400410b900d201c202020b815800030b1010442c030905903801c0100009e41c1c0e80c3c0a0300e02094454054881c1d4101c5041c81010721040140301c4500c5a0110207030150860540b501e04c17071051144121582000c00c802c900340b4260f00c030700050780280c503644201f0b92010440023420741624110707031040c44007155490408403881c00c64019604142c295502042035082c172842c1082030f02d04030900035002004200004a51540420007511407103810031100031190165043c040016123610140c0c804e400200f0340301203448820002c0c285e10610000d000440180165003500249180481540004101b0320340c145d03011940100707052051400160181000500303001c002d100d03039001d00c1110500c0c121040e481d4508c0100030800350b10107074022010501d010a03181404001c490680c2e030003c240c1ea040c03001c5007020080740f40d800399204080007854600001c100c48100070680440c40070b400c840c5402c41c403481e50146030a0000b800403403c0c141000850034102050440981c00400e0503001007409103040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 946890089 1250 946888839 946888843
    0x3100e1005300d08061306030c060f020c030a120224150d0f05010c030b0306010311040b031612030f1b110406031a04050f06010b0a12091a092e0b0102 66
    0xb980064868000c2c0030400000942c4544101c1c400d4070102c0b90036103002c21351a03104c01110b0050000074462420342005003d41c3d40601d04a1810100714411290b0f0a07895401103410010260402c45070307580a14580e584481c1c06201e00c0c14046016901c00402142d1107104a0210304003600070030180101002c4008944c0340c07008250380198011800403900e80c600e141c0a402080808043c0300001d01d0411120003506d40418aa8100c1ba04281d81c0e04590702044100b0009086554407a607140c80b8400c41064004080e024a030024500e10030382d030300000145d040191000800c2000301080201c07401102c100408481c113041d0756103030030010014400d01007901140080c4103682000e40800c581a02a062441c0209400c511031071082c2c094445035880c003e40d039540c440c000e000381c140b032030341c14008020308900c10385101c07800200e040c0011850203820745a00300c525456003410110030070458100502201d00f00448107068504c200d0104842800b0001c0303d80c51451036145100803900e034030a0a09607803013 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 946891339 1250 946890089 946890169
    0x30301061b020301020309070801060801090c030210050918010501030f060e1503030c01020d06030507060e150705030906120403031d0c0103051e07050a09050109030c1e0b03100e1005 80
    0xb000c0c2c000c541c6c0b8103040e07108035074842452007007008035070074104085a040e03018007400385001e52003031220010340d045500300202501021040300801409010043c12981d420400d0712400705810070b200d42c3c035410940014156040101e0002ca158144001006007000d091045544028400042d090342c03044040000c0c03d51142a80ca04c40c00d44c00411130540240c0c1c69441074040341c6c0b0940484140640e17900e419504007400035151f9920503000f0030807004a0a00e4401000c249110b4000c3e41c0c9003d1803240050080e0b0015289440e0302c0c080300041008041c0c152003010030000404104146042d220350826a481d40c02c501820304050301c90300410300640052686842840b0002403124442c50704182c02400d6400170407101002540c2c0d0b500c0090954083ca0b41c04060300c1c1c100441d0f0202c82c1c10201d1301c1c0084403100510384488103110f000002d00e65031001c09140603a51070313456800d10a15001b0f9018885c1400b0340351b8801401200c0f4200417a554009000b0010720300d0048040c260103004040c003643c0c440b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 946892589 1250 946891339 946891343
    0x1005150d0b191706062709010207020306190f110433081e091218150414090610111204080307030f110d1d1507020120030301061b 57
    0x40b01c90303010500441204900c4481a10141116134941e02c1c417080000320000d00d21180d40c80c03191305150407030040b4420405940a40300c00000b44c0340c840755034003007440c1c10001c880d00100080000000801f21416009281142055450500201200f0716019041d0310441c4030740d0340c51805024441006900b0041420003401010900703960002464a0103070034100d08886003480c800d000d07002122641c070070405442c00f4000100040c810103018625686640e40400c59480201c943c2c079181700350382c2c0e9800050100740d0800036030380c50f115490040b10361110350240142c0c0348200100010040340b03031242c6581500410032413030035040d400d01240740b183c10024030301c0650002c03040005020640c098000010f21242d0700caa031f2002042c0300241d1080322031941d81c5200c10394a41200c00b0403d0f042d445820301e00291079040000805040407030300040c940d40304038040003158140c0404e8076405d40da0080755a00da0800140d140b24a00c0e9900041a900d84c4814068002440f00180864801403d2070211041c011b07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 946893839 1250 946892589 946892629
    0x60a05040f0b03191a131202074506080d081009091a07050c0a06140f010617040524060a06140a08180a08031005150d0b 53
    0x21540d482504064003055842e41d019101d0210302429842d24030b40c0300368240341c220403031010142440102103002c22000e414001c58402d07049042021803040104401d41c40b0075078000b81405440c00c5280491880e400351410341c40c00711035000e102220038000540c0d04841150001c024854049442c8030010039a98001009500c00c0c0b1499500d0a07400c40f12460241400ca64490005559904540c050321f40081000340845403160741c1020703001562a00340d4210701d10f410007d0070640a00e264038900020010260b40054848040d261303080360162081d6081a400706101c00f65604003000a408141c0e00e100512000c0c0705200051b09100301440744070030120401c07202030320190203c20403005c0c0c0032041c0c56103840366940c080e0004030070340520304c4105200c0d2080c9146003003a079100000e03507610200130240300803070007160100804000144400100b0512400d8215101d0900340e20960251021740c10841c05000c1441044860301c0241065030b24403070110001280701440c03900032035080d5800d0704c00c1070400307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 946895089 1250 946893839 946893851
    0x2040902031003110303030412030c030b22050906220c05030a0308091506150901020c0306090a05070605030105011b1a0108060603010b0105030606070f08070f0308010f1715060a0504 80
    0x70b81c0c0d0032820041100e020784906202d06442d04205034a0784000d48004115005244001c2045400780d0403c0c0d4100f100c908001682194040108009144405ca0421492403521402050340b01d40d2003842d41042039000104040c0c5820003109080b001000100111145000c60a4082003050480c99020b0440581a103681c182d42c0d06d00a414002c054600701618041c804150b0006c2e003121189a100305802020f0189c4010588620f2045a1084000a04500503c03085034100e41741040018044c08202d80285404a490f080c4142032000c0d5805c80d4042000030401042141e9001c00990040d602c0261f00c0e00101c40685030040100031540c00d80a0310035140c0d0000502d408011551502c0381e2000d0780203110400102c40116110311044404540c400018040540031855042c1400c02c070301e1081d040d00d46030401507140c00710700300740d00c002c00c41c0041c643c6801030040341c0881000100a00c003001118602d02c401024040d06e0f80c1503245891050700300c1400003511961020780400007410050020404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 946896339 1250 946895089 946895101
    0x319030b0f011b082a0c0d0b130605010b13120305030708070509030d120c0507170d060b122d160504050a03110406050a0b0a0f030b090f04110102070602031c0204090203 74
    0x1204141c0b9961800c2a40410036031118940040303906c0c6200c030fa0040640304121041d40d1401134030300015048805107203009000c00006015441418044c18200c4421511204032500c019004006074200900345111034140c000025000700076a81c225100f0304004008da03035480d408070f07418042c1c04041d80d4180300d0701c14101403940d0415200d000d440010801442211007090083d94288544403000700030b0300512120382c9500c44104058040d130030f2016004148583d4464040540740c00100d0300507490b07000c2c581400392a0801400c070b650a500d400e0f041803c06040a0540080001d00800025101e8803100c0c90b0a0311500c1502244d004c0d25004059861654807401c00300311180e441e08035140201e01d0400c002c00c55203400368401c4203c0f110182d42602e818070400085480f5001c4d00e000b50249a11054650103550754180303d188941180c05160031603182030f0520358070001600700198150340149005002141e40071085400510b180707103100000d510f0544016000f803245600511481d4408414007107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 946897589 1250 946896339 946896367
    0x90a03050d020c16032604050303090105180301061806081c082e0602151b0c0304090f0b0f12071208070606090209012d2607020319030b0f011b08 64
    0x181b4140300784003004c85910816018102c51140c1d001c0d05505600910100800c0e40c8203800400d0881e20000e1400060ba480001090954030740c0c1d084032100318070904014040b10034a101c2c0e10300070941d090041400300d861280e113108002401d0482c80820030032000203954032991204841d03140c8180c1a030300300d8121000b4031141c0240124010b1800600441c42c41c2c03074400d002c00c000140a82c91a8a920701e07500001c00d64400c45a206103600704190205104c002485481449010040c0a0003900890350070300d048100407002d0380b01c8006034400e207645201a0303c00000040c2c24000d0303131500c1c460040129003509000d11180261000240781d5814504082a0a29190060040e1042c01e23280c00c810314422012010440e8101d14405982c2401000341e04423951280c0401004030707800101300741e401200c504085404500c12240384015a00011f01608010184180c640700c072541407804201c42d9071010300103402c1c030408080260400180c0300c203c21140c0040c500c03a10703a00b9409902d46544504489001c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 946898839 1250 946897589 946897613
    0x90210020f011505091602070909080405040605031b040b010c1718100f0807030207050f060613020f0f0d240608010b121807080d090e090a03050d020c1603 68
    0x341c0a508005034652065840280030b02501e500429450280d504e064080c1001e110520100d0304521400000081c01e003a54401d00101e28001c064941d03541c1c1c280740500c015100c0c640c3c0140c2c02903010780e1081c80c50050741003002c000c0c000121381c0030941014901c0103d42e201000c05003d0704032400302034049a01d204a42c028050400c5200d10300059a0401041140290b82f070000c0d0300204000c8a40d01d1001d07881940b10300c2d840507040c10b00606100c4192a128030388012100c4c0120135611680c14083c05150006072200d10000048041d49880c2d14000c812400b030045000d072041c0d0102c08104030200c0c503030540003124401540055808004c06624511583c2c0c01395214a601013454030303001095900a07170040b2100000c846d03200ca8040d0311040f1200303035500c4000059107024094100e0209600d04144114a920745017a6990300d200f9003840c4141c100b00402520903159079000059400000b500201070741c41141c002400180c450312251502401e00c9113060b80701144152422021003041419a2a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 946900089 1250 946898839 946898863
    0x806220626070e0403030c020703080c0610050a050a0b090f04020f12060405040b130f17040602011503050a030503070c06060b07060b0a08070510050c0601080c100201090c05010c0609021002 83
    0x404100003400303041c42d488507403900514a00091040014000c02d01a4114010140c00c5104448803960349440c1c00540ba0001c038001180c07500118140001c7c000ea4003440d002602003100c1145001c0d00e090f000444081c518401c8032140d24011aa200c01c0750b98058211114a40160043d90b41c0e01e5030b951f80704000d030b10203200c610b00c581181c0b010580c0c0b4200391041600ca507500c0701521800c0d40300d60040307042002241c80115040111240c9520000b4081c001001c821200c03148401e4a49081100107402d440c1d0340c00c9242003d1420610404c003007800081d85031400c54040c1052641c83d105c820080391201003c00c400740c0101d0511800060318564100208643c03401030300c04000600944042020001c414801d42c1c0701940312403001d010a1410105020700c0300c8060410360300e40700c01e6402403800e01000342e20860742900701c0400768485003084054407200c0381c50740c0700801602c8200e40d560050f0a40c40d015840c1001180d07000c2600700001c951003a2a4150010f00d060300c90b010340301e0700941c0e4009030508 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 946901339 1250 946900089 946900139
    0x1401060f080c030f3903060109060c051506031912030c0512070305060117090d0915080a020a0e060d06030215040614070519052a0108062206 62
    0xb82c06603481005590040c02020407040160b00c50001c201d041c0d215502d00007a0091021100c00c80700c40c081000c0e46440c45845000940301d1a01e41c1c0050134401e010351041041c0001e1814400000300049076030800801c02240c103001644401300401e00d800d05c204a001c5503605040d20410500c0759011450b000d801e4143e07000e1040412031501160b160040c0b100713805c1d01c04488030202c1c54482c000c1d08141e23400113040c5400150500b01141c807440d100e100781c40c42411030700038580e0640310640c4641400040c01103e52891490750640c03100038400b00c0002e02101c0003e60108501d40158410412400500c100800b0305840703071a415140c1005050a20003207200e81c406c00700191008011205a600b01c50407602c88902c56111a8404011a80712070400c036a1402000114078058942d942c01124aa01400061070440140d13070603005c041c011208038031301842034070607001a280e03030140c840341e4495416118506500300800e030032000d460030310003105d4203141030140c041180300495034404144075100c80c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 946902589 1250 946901339 946901341
    0x708011a0a0b19020c0d0c0f2111152107020f0304090906020d0c0207080c0d0c170703060f0b0f06040e010b0f0c030315010e150a0c061401060f08 64
    0x400a401940348a0302c00c041005000704080101505040700000d640e6005555140300c8030000a036071000c8603007045400600c8000c0c140651020740814402901220340c1c003410400c1494080003211619a0005001700c0d005c011403012510341c082e82c10300150800d0700030b41d00e40410341070705144202d42d403031a0820400140b00250000d07100141c5101300c40d410350040e516113420314417454050510000706980e019000c20104c55900c0c031030700c1002c0354000a40d018142d014103001256041002c11500729104018014400011440792602181101d00b812007901140a920310030030305058240d4005801149042c200803a00740706a00180384030380341180c0303002450f01150200591406a4003c03046d0002c2d070100140703c12036852005000901c29005610305100c0031014107841c550084403907503201c10b030059145100f96081443c1c02080401143c64000d0000900d501c4002d6020f03410381141085540d5800d80c0c28071081da400342c20304201480b060120740d84c66003030140c0800c40008507440020303184c00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 946903839 1250 946902589 946902641
    0x603010b0102150a0b03010b0a091b03090515131a01080708281b12021f120c170108061816120212011e050601050f09060307090503070801 61
    0x40f40e40d03003043c44811820101504d07201142e0300100314003a03036140c02d9175980701d200c00c40303a0318090540018005008081a94190400d0381c160400407086004281400c0c1810100000ea0200e90704105101c1c907801510907a0718508819071103100b080c0003400041da07001c29602c4940fa8008440d0688003824103c83d9441e03039498060f50703501003860b0f4085d0540c00207070178412640700c0d0028808440b4000c000d440503075100008070340304103065503002d01e01c242c00a2040701e0840c20043d01c0f04c5000401c26494010070484076078041c007000c030544400c3c4271080e52031031013038602030284001e40c1c0301c5607400800040560711055803981c0c2d074805481c1002c41840c1d031400c68082400010b40ea615840c01d00340105801071801450202e20b15009804992001d2500d80098003424248a01e401c40d905034604102800c1c08103044a0455102410890400104004580c0c1c0d80d00a44110381c8201c0d402d4582550b40e50b1581800c541d080859080203915003d450390018544070150000070040b00c0300700749201100051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 946905089 1250 946903839 946903843
    0x120e0109170a050d05060d0b0f060103182613170105090601030c060e01120c03051608060102071716120302010f050f2a0f120105031203040f030908150603010b0102 72
    0x454003180011010403590782d28400c4d0f504450740188025008040c50b1485d0b1703680b883c07295011592401507258075002c0002c55030741070080580d0320417106aa03070030000282c1c803145900d00b0031000150b4003004ca08d02c80280d80c80090300300c40c0110140c41800d41219100e00c40e10724540c02280e44055152700708404140303008000328049040340da0169094848a24007081940c003000d4103c0d159051016100314400111140d004080040046a0740000d0500e042001802c481848964000410040300300b00b264607600043d02200b0b03100320003003c06900e000031030104e10f010100b0020403500400360000142c0900d00d0b89501d00a50300c29002846410140801c660480343d003111070402c0e1404e03c03004504110840d6201d04003441c15092007100ba40174114041406a114251020034078900240c160f40a064010100340588404c402600d00d100016252400b00d01001c0d1003d81010f00149007002058002c50041000b8036080055034003808c54a2807424001008589840c0a94280340100320700e5840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 946906339 1250 946905089 946905097
    0x8120c060f130213022701110f10090c0f030803100b0304111005070203010926030c040b0c031201180501092a020c0d0f03020d050c0307020907120e010917 68
    0x380910410b200c8815408204038007a955002400035542000460503a600c05d4201000e8810841c00b00101e045002c80014000c5140da40c84c280180c1020902c0d0361003410218403007101a90004012600b440c0c54180341c07110071200e034854901e54410038000410814040040c61192064800e21411070340ea8260103440c6100c1203c0c001c08003c4d000b981540c0700e01e411100da0540b03120b6450102e007070200c154042401c4a030369850a55a10400c02c4e030940c10781d9240320319143d610810006080c04d505281d541000c1c540103074044d5400c00000440ca0441c02c02c01041950300002d0108202d0280f540e5030340500e60501912940070319150b00704800428103001c2ca026904ca04003100609a0342000c029054060700701d60407024508501450344884060b03035407103510f000c02500a18001c5003543c03492601034500340b448581d0784144907060241008440e400300580702400e405032400d020fa41d5130700400302c848644810006414070300d0004516812181540a00e1400e48580e40155480f10203c2040c141801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 946907589 1250 946906339 946906351
    0x2060610080f0705070b070915110606060f070c0f0503120c0a0b190e151f06080903040f032015040308090f030a05060a0614060f090a08120c060f 64
    0x5007000802c09400900040703d5101045160143c1012456515064805401e4400500003005002d0a0040e03031207040348174102489030305003030b400c42c8030311155161240001002d041c8142c0010941917142200841210380b0b42d984860552034080d15245500090761143c024140070744950818814500c400104448010965200900d918001d507954110131090080522014000c000511140d440d03181c0599549034100c100500101c0180101038180010020050000785540d0881d980c520704aa402c61801d603501031902c203103160b8410b00118514801d50703000185030010ec160010502606481d820080c030b10040d5600005503a400800c1454841c1c2e01d80741c032000030200800c20000f0121030041c0510040902880c40744610440041d00780310f0810001d80d00764100e03004003d0014410710030040a807044018810000c800d80f00070461900a01c850540614000282100d05550700150480145410011030b403030441880000c0c881e940041c01602910300c035004c08554550000160180300d20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 946908839 1250 946907589 946907597
    0x603270703110409020102070801180605100b030112050a05061003140f06060d0212010f0e0601150e2709030d06060c0f060c05210103030e0405040f0b190e06060102060610 75
    0x1080306010800100410b16041b03043d440707041400a4003240038024103500700a00e480b42884110a41042000d03910000e00024881200d000d09000c06c007c1c00d0160380c190742c1089910313442580b451604600d0121b81c0c401c0030740f42e8400d8904115440c1c0c8090001c0c4140c80c81140c000040400b0a041155030340c04c0190700701c0040c0c200200149407401c209410105240c001440a00107901781d40007982101c000c03282d03022101c0c0c1c54502d0000307501020402c40b4010001c1c1c0c6100140342c000740b90000e000f50300c2d01c0e440328400d043c422203030200ba01a1451407403e0b000d07400f59100302d03420102c10440d03413070b404100281006410f2000002d86c46008640003c800e5420410950903040d29540d420024810042084c0038003600380100069003e40c051000088000070207820031550450a01074941d64051038082d21580c141030030000002e551219850382d440e8007041a000320748507030b003012980081d007810040c0d10b1031030044e04e084c07902c0b0009031702d1340113032803c0c1c090f9411a1101d5085c806808000041b0310041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 946910089 1250 946908839 946908863
    0x50706030e0a0209180a14010e070803030f0a2016020a050f03030f0c160621290604081005040c080c01090b090a03081603020709022508090603270703 66
    0xc4202c032000c8409152514013030f60700d01c40d00c80d80c7d5070607818079194207404169914841e070200000c0401c0001c000c3c0c50a040254250328001110f4615400c00600b40c513001501e5015020807040e0324080036401507226510247c80d00c0e6200c0c00c00c7d14090506805900c1000303c0180000e050901e460440440c150103005180350207044003048031590320130950b4200788c0c070407402e50300003c250105540010f401c0d29960404601010b80d40d5489240c0d6100d000700660785480c400c281003160740d46400ca085662101c0a80c08424000006941401540d00c404150300a01e88480500585039010510072032240e09100c0301151aa01030707170340d102400903805021808003d018444440c101000d000d0b11790f0000d10180503541c5a41d1444a690840043e02e21707482c11001d031940030507405012803000751004103003c42c1003901c000601c51568600165032196130300250b0414082c45014000c441c00618054141c9a407810a000042c110b400b50360b800c098160754092040f02221404941f5108582c0c100d100c642d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 946911339 1250 946910089 946910101
    0x90f07050a0c02030a0606120605090601300219051504030503120901230a1d10020c0109063b030403020405060d050607091509030803131707050706030e0a0209 70
    0x9808502c0081c0c0c0d00d031103a41124400503486018250240004080d014a1900b00d85400b00990340060801a0f850700500d00500c64110025940085042035020380b02d071100c41c5004000c1c80c1091030102940020880d1603505506d000200d600c400c584094507140807410803d18504c2881c000d9003c0280f45401c10004441d502002d004000e4200b4044800090410082036180034200d5035110741c1580500318000300151540300d0300c03910030400c4440c1b01d92003041a11958081c1c82e00d000c0c0c4a04103075598041a801c885141c2580030a5605501c02c001f0130181c1000380c44500c2a0020f8103070307403010000d20b041003280600e005498103080712005000390f003003a04503420400a400020295a04201c0b081c40c0300002c40e9003002030500409094a40071074490500e160940071140d6201ca100610034042e03000c0002035030480440380c1c014204803840c00050721900d44504802d080800c203c207100c1c030114049040c0640440c0c194200c420945040113030200d0240e0042d110020a24083c1d40000b4940004803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 946912589 1250 946911339 946911347
    0xf030309140f010506100806150d06050a0308040302151201030f0f0818040506010203090307150201090503070c080601050405040503181f030504020909150a0b06190e090f07050a 78
    0xc08548100081000c06a0301c04580e4038000b440080d50703420740e4441c03040c0178582c142422145040710061400d4403861501002141e0086003512400b0314140c40018420308001865025501808004044020960303482c1001a2580c1050100740d1091500218105810810104680303800c5540e081040288e86076840b00c804c000c8c02c0000507241000032001d40c500042c000b600522400344600038225013074201600748130444c0d10082200b41554420840003200780d0b0000380c0f0004403205031609120980306103034100c1c003404a1038401400b0340b1021030200d04010305842d2180030750300000e08960300b580c1d07184200700c196041900d001e0440d4108000c03040002419442c0c002d008500601126410400c44540803256840145803000003980c4170140800c40c5000c07001a038000380d003440100441404078406281c0c06601425203400c1c150360352190316040e12440c09441e2140c20320218110b5040011034060000751103c2541c03032049000e100000c805200074512079002d04802c1e9141804e0401c10b0308162 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 946913839 1250 946912589 946912601
    0x50115030f090b01030b100f0b0f13050312070b100303051801270302130911010815030a08121e071b060f020a0f02030702091302042a0207080105040f0303 68
    0x681c2161940034001c0030079160404103000314403448000f40070f454400b01400940710b01c1d40126036010582c41c0104003203c00707801034a80740e24803d0030a07a0313152240b40101035000b504c1d600c02d42d094007a80d40e0040e4040c940d280540940c9024600f408019a0303800141d08440203e0f0200901040f014082c006400c00e0441002e10000750605202c0b199200701e00101c00800304400c602a82e61207108420300460810002186c48060b954130180b20b4003031103680308641d031150700da20a41007040c0007000540074402e0034030031240f45c0e40140569110b211a814941413660080d1070b0541c3d80d00095000c034200d03d028202c000c03000b070102030040c0440d03140d459080f1750b01c05d0080141c0b50280c0000000307038041032507071140f12002c0c0701003400180e44560f00c21000d003102001018050954200b488400f000d0785801a01951000e1b440c40c59510100107880010001d00d62083c1d452a944090341014503800c40304160300134040038580850302861303a2841c2240c00c2c0c580460f4018844a001e900450029010b50010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 946915089 1250 946913839 946913861
    0x60902030430051c0f060501020f06131e0602270904030f0807020c0a0b0414150a2102030a0509060109021c0e0304030b070215060f031c02030d06030803010f0905011503 74
    0x1207103000501c1c01340364041d20120300300010015a80c036030410446d038041040c03044104404015040514002c0c8540b0000380204001800c420000024440004085000c03034041c1a0301c02c0c000c64880190142002c9003084a07820818800c4010b8900d00c5171b0b1924240c00d40c0306030b40c1580c2c3e2130203000500d00c04480c201000f40c0b0040c103500c1b600b402460a9690004400040d010710080b0641b01c0d86040e80c0e00403031b041c1d1a110030b402054298241101c44003501d08880d400038240c105600c50051181c0756000d80740110301e1294020303101005100720280d0a420003030141083c80c040328040d03620760104100b01d12410b0041c02c150103460118104000c855000310742036108150940342000c0c2e80361201070490804440020041e000402c526415007c2c03000401d4001e8400d4540954022060f80800c0d95000702520b0205c000e8400008140d010f4801c1003120540520100184000c0e07a592901580f01d40003030003108821240340d1004950b40030700d8405c10f0b04070782d10040780c01d03480c4d40081d10540c0280804501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 946916339 1250 946915089 946915117
    0x1050f0313061e0905010501141003230f06120c0a1e2c090102090a0b1b0708010902011e08070c0309090203010b031e0108031e0d06090203043005 64
    0xe07140001d10702690640300e1410548004c140c1e840d89240c4282140d005030010301c00307042850b1034602161100b8061228040c000e04000035221026280403c0072900b1840002d075254030002001080c01840c40814004c28081d00c218480d4011250002e40700c6020100140e000364600d1030030021103900e4042100c03100d00681340d0745041c03a1600c043c203007410342d102120481403010400c0400580900c010303056021903400c008500b00158100001d0302e20505114100044030042804041640302d15214501c0e03880305012912000d40c6c036504c090182880c0c180590104696180491343c4203a00440c00c129400d83d0382e203801d0942e45410b000e0321041254034040d410400308450102d0050f141d4401036001c0d0500540441d124940180c10400c07160440c1b40042e88940c5000c01000315071b00c000280c0d0b05002040c1100609100c1054603001c042c01500e0000022900f00f40000400744002d500a500940c000c510002d003443d00c4901103401c201804000109a0442d40300d201480303846640600b0f06098070103d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 946917589 1250 946916339 946916351
    0x706052b090606081603030f0f121409010609021e1b03070b041e0506011a0f0304120912030207050105030c09041409100605090a020915120f0601050f031306 69
    0x1458204648581d4011030b000780da680c000784402d000800014900e007181c45450b4500320b003035079001005103024405050501440c03500f20202135000b841d0440700e40001c024101700d0384283c0010969004025229020b507035103003100110300c0c3d0a56000700c60424851090400a0000b0f2580f090074581c40b900c81c800c4042810016407041420030302c000d1210900480c003910b25410719040c01012001080340031915040701400c0880043e0011030f4203411548045c0d40390104c0349001c0c6056a861041040c01521540c0010800c8104100800303612480c0207181d0780e10030015110301d42e210034140d00700800780160b031010104009640c07040c0029640300800010150421a0380300105080e22083c2d084080201e40060070020300407010000042d41100240045c046075240c080462911000640031b464031640001e080d40d01910f1384d14403c0103049001001707d5460340b40b0701c03240f02d1a56023501d4a010411004000c65030a6114201391180100540c000e540b46131212030001140c10300303142080303c0880e1108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 946918839 1250 946917589 946917667
    0x60a0903080706330b031509060f0307080102041a0a05030a0b0f1003020a02010f02030709060806120607050c01110304020a0e06040b120f19030c17040b161103070605 73
    0x1100540c4c000030301c03081400310b9550800e6610f0104000c2d044540c6414042c03040080700018a51840c061907420740744810183c440001141082004030603407030f0107109502000541c02e005500400c1107a403129182d46100702c0301c0020001c144074200f03000c0c00190091000c00d070100a2507105461001c0024580581b8000550104140c082030f0740944021a03404503140d041d0030340a0048459004c3c0b0958214a0362510b0f25014094405134000c000c200a04080003601c581c071000c4142d44004840d81c02c0b69030358941007000400076408501a4600ea5081c03120710880e826090b010b40380143d500911502180741010018080c202008000581c080d0301c6130b90030f11803900c0c2c076210b0300440000c0b440070704051b01d06c108002d4901000704202c10a14023401c084c042c00310380d0091074100015401414074901303002e00350715034045000c0c07070f04807c2c45490002100d080000d00b24480c482c1c00c1c0c2c4104603009034550000e007090345440a0313214000215030100850a00041510900b28800e1201010488c600c0001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 946920089 1250 946918839 946918871
    0xf0d030f030b0d0b0103061d0d110a1b0303230301090c031b0906030605031209012105130c150212091923060712031d03070303060311060a0903080706 66
    0x20f50303030540c2c85407110310051090025600440b00d2444140317401e0900c61420161013a940d01d2500c0c1d0700b004211034044e20b603000c03c00602c0051560740e0031199142c10088000c1c543d2005403d07502c411001b040d120110381140c120039019035280c540a03509440d040d6842c012914000d440e143d21148201941d40314144c4508074080030b00703203143c4c441d940c03000c0701076040120140c200d5905030040c80c071951140403642e210310041000c41d00c00560038a0708106d0491000e00c803081d48089602d104a01500384070070401982261910030321f840e0b0160780341200c1565696450381003040103500710001070b04007034000007100c10090020101080c010706030000d4800302070304440c042c583c290000d40b0078290004040f0020200c0b50160b04614004651081c6451a607a41d0780704003240c10000c0c00285a140c3c04c150f849840041106034001000000b9240e68036041c3c41d0080041000f80400c9500c12111000b0390440d0500354165813403100c194a51641e82ca00b0f64171903601a40007000704882c81d60322400550b034602c01c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 946921339 1250 946920089 946920109
    0x40c170406050702061e0604020d0e0f0f0d0306060f080601140d020306040c0e0a1e12080702090106031503020d110d050307030210020a120207051e1501050f0d030f030b 74
    0x307040001114104000001e04055002d08242e081b83d28600c100d81844107010b04194118208550040c0ea410f40d00503c20041d107a40b01c00d2030741c2d42c021400c0c0080803550100e030110b41c0e250007200340c50800c2644c9000f90704480550107401c00141100e80003a080c54001d81001e9005841414152001e02020300320300d1581c0c0c4005c0d1421401900032051142038100350090314008032042c204001d03500120780104941e20420300c507038039462222090034055096003542c1e100140c070015500b03003900c5129050074895980204400c034000c80c084400000c0c000d01c03d110b100d000691043c180310300d451654081201c4102c1c0c4207030030b1310b00f0104ca1001043c1580d40b41e01038a1040e1259001e0764940800741406070500d1740e04a100c00c4158010000303134401070b0340305501001d420b6640000685440c524141180f4080c002c8514548040d003005081090b1400014141c3d01100319403003103011aa2030b41d040c4840c021030b503180c958000850060f20310009000f10088450800c080c43c0006103403288100007059000c2c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 946922589 1250 946921339 946921343
    0xe010c080a0804020316060c30051e0f25020307090c0521042006040b0a0c060603060213170a231504060b010807140c03040315050106022802040c1704 66
    0xb80c10841c08041001e109c0d540e003a00003d031191844a40c00510224250002c04600a406c0040010381080f00c44148000c00e5207030039003900f989490f0301c001100c0f003403607502606e0038842d619a01000e0301880300300a0007843c112176018018042c41481c1c851014003806810703d00c0d5090000c00d0045010201704403a064458090704840003459041905194940d0016145030990481e8403040c464455112441100c0843c2d0401c9285680c517248100119541d00044034028401801d01c0030010a000c031907005400684040e40001601c25641d031403415402c0e49501002010350000503160001c0b0303401c07003142d8001801e010405404006080505070805d484140c00c1003400c2d04000600051201c284203440f032140c0c003030030820150b04022001a107070501860140340300c09030000d01490101c0c014000c0d10300559110b016000250380240c02c6401400c0e090103000010306c5441034040029482e0707400c001600110800401c0c00104d103400f031001a0007104240320600214101c800c14003a80403510030b215078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 946923839 1250 946922589 946922597
    0x1302070b100618030b13150f091b030f0807081c1e1107021e060a110c0a0f09020306041b031b0f1713140d0e010c080a080402031606 58
    0x207040507400303441c6210481084500d403a03030f09402d00000306200f282c15004003d0503950171611100340380c061241c1d81200e8050018609007121081d007001c0c1138000d10f8845204640c48443c50042d504204281940d03803001800b0b2100c410a001e0124a03180010044c00f4006e1068500e042c00300d4510306030105078000d1680f4a540d41e41c0e600c1d007004060001d00802414041424414214500e080510034041c2031b40281c4500100c0c60300294207004141104074000010302031584a184643c1c0c06480c1e2104031290581c14007844c04d0100f101d1134000e0200c003c3e40e80d2200040e00c0c090600c007022009400c02007170147c00c82c2c0c1c0c2da03003a4520400c1220303240810880c50366000c91045800c060b410100801c40d5000801d0000c00840e001000c1e812080184030304c1d0344a0304181d135559480b041444000a61803001d404907440c003010303214200012078400941c24954495400c0c40c4411801101c95240180d0050001003040c0150300000d13102d04601c940040c0000c0441b5032030900407445d100c0b2070840741d00250200e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 946925089 1250 946923839 946923871
    0x220c020706080a0911040b0d0b011401020f010b030d0c06060f0306050a0f050411102303340804020f090a020c011a030703120c0b010306060906231302070b 68
    0x3282e000064035408642d141c02401a403003d5580c2683c550f0000694500c155145d81c14500251500c03400160010780000d0f80300b00d656501c0c994148010784204035180180200f21700d06600c07010502400303c404c1c001038000c144507000900b084910b5481001d08a80381501d644001945092048621028500416000905040c000030481c111a90303d132403550001d06000c10440403c1e200050798a003400c09942540003c440b042c82122071400042c060081c0380781c0100d504545900b414003441c1700c3c040030340001084240d00581c50b030b0100102a24403903030901d4510102c030301511035000700740c10910280411500c05510340000c1c919080458411a2166011420144089003406403c40428076105c45000081120001c00c2d1507090034040a4100329451203c1c0da030703403403041500368421508009030703041c2c40d40c403031401134040c00d00c0340b04060321142001408106180c01003403d602c0c2d8500d51100040d96812a420b0200140f01118039220f0a40c2c00e01501010540040c4c4851141460f00300503200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 946926339 1250 946925089 946925099
    0xd081017011b0f0f051b011d010506031b041e0c0e0306061905060f0f12010303090e1e0c0c0d0306030b0a0e06131e03020a050c0915220c0207 62
    0x841c2c4468100b0001c001d00d10b40081d5009030440d0b40060001018580310b030f902c0340003444032021078480090b0b59000c0c2d8602001c52009000c101202007030354001d4402481103468440405641c1e0003840188046415918501e0441f490168021901900d098915034006400204150304a81301c2c528010041405100c04140d1841c05015490303000c4803c690f01040c0c03400501c005042000d07940107190180b440010001c4008900380300707807001d064092150300d0b603564142c014103807484021701c011030104280c0c10022410030903142d800d501c14401e510030502d171010b0b42100c449681001030001c00c800103080059102c0e80321706100e18100e02c4c0071514041142c48c9185485040c8000040600c0d4030145883c04803440359501094080c0c01010081b43d111105645041007801d100b45c1640c182d4180030382240074810580c011410048450042e03040e60186141d040512a480c0c000702d4a0080040c01d82407802c9603868029a1020000310555903043e8603c84540c005007100c107610801005a80088030800c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 946927589 1250 946926339 946926371
    0x100f15030606030618020d06030c0303210216080306190b070b0a05040201140c010b0415090f0b0112090c030506090115080f1504020d020d0c1d01080d08101701 70
    0xc1500349001c01005140504000000825404034a4132580005031100c7e4101c00790841009940c105280d030100c1a52880e015280750300900761000000a040e800342e0401d01e891089c1c0c0c40c01013180d03038002007010300e6a6503868142d0008102540c4103134040c806861400c10b12000e14064101d0101d020fa440703502e41800c03111244010001054581444104401030364014622852058118585612142c4441466024010750766036950000d160120b10b1a8411074102103400321a5100410032007110003400b190252101038000a01140300c0080d00d40840c20160302002c101c1c1c0c001c00002940030744940c0d84504081081c1c81100c0d0580d11103014070b400c400c25480304001007449000174154107a5000c070300e42c0c942c20390b24a00000d042409000400755156a00c241403100e0780209803200d214524a40350807000918000d807900402e10000071601004030540d02c0e4180c1c3d80070703070041007601c80e410b0040b1415000213006403c0544001c10006004145039807251031491040700203d030942100c83e03800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 946928839 1250 946927589 946927601
    0x50306120a110102251a0d0e0a020405010602030a0e1002030714060708060108040f060518010903030e010b0a05030a12020f0d0e13020a0f080403090f030803060f18010e100f1503 78
    0x304814017489656081c03800700f103642080395004030710016408100c8456400d00d011700d440d600312a90402c080740156400110310314038464400c07502005140d0301e94074202d9503800b40c0c0d800203022503680916242a80f80000d1042c1301468a88100c078504040d0ba80c42e50b415011606162950380e02c48401d12001940107115158801c1d002c0c81c050009141644803040312181503000904115a504041400c43c2000d00d0f400c450290b0200003480f0000652400074000c19411110022551908440c5000351804400203c03c90f04020300801010308551119032803044400f074600e0079407040540f081d40220091191141d80c011940310800820b08140c01c0c000d400000d00001a0014410805084519044010b24071800c44a19042d08543e45619054031441201c1c3c0000340c0d40d0001050010800c00240029481210180c1e2041d00034807001c01800004c04240002150a5650700018403900c600c490380b459000380030072080701107182d0340c0b08810f01d070300e1298010002400c6004510300c10f0f15054001c2c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 946930089 1250 946928839 946928863
    0x12150a14120a0f0311015c090f030d05030406020c0a1a1008030328090f0f03080901020306130504020117090304050f03030705060c0706110f0306010e181f0b0f0301080f010507080403050306120a110102 88
    0x9000c0b20f44210b540280b030dd200040000300061f0740400d440c0c0c0d00c2c130310030041c00d4035513680f00313143c94207010b2007844002e0034070b400700c0e2000c00c1000d0b003a00c0030a0743e46012050301e00848051801d04500290b130329641c40d000d0000503120031071130340e102d6403440400c2c030745a8078048150081d541440786c80e1403410000d00a2500a042030a9a8010070034002d42d0344980740c0c0c40c845c2003003841000846407a0791004941c03010540310042030400c150810720041107000300c028400c80f4800c807100c40861440714141900c034081c101c40034100e41c000e0f030002051100c2d0003000341841c0b80700d014006440c0507021b00914580d00103500c00220244040b00304021b0b0b50b0401400002c540741111070390006e80e24000011212840240300d210b000408070042002000c40d1034007800a414810358490320380d4900071003003609410910411038648100b000040049e50184a102d0041e041c5540e03140305a03079187c4040d2520340c0050700c1c0d50b401c100c58441079071000c84103000c0118a644511244481802d1000009142c41460261 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 946931339 1250 946930089 946930093
    0x1020d02030703051207030e12031014100503190218090a020c06150f0a08150c040303050d0c0e040212150a14120a0f0311015c090f03 59
    0x6020007113031304101a40d0a80e002e02103a01702a030341c0c4110403006001140c000300802c0c420a4203003003101240801441c0301c0d00c0303011100300c012644c0344080c0c1c00c03c503150031145401541d158242082c052040d0300840c5d0202d84003400ca00b041181194030800c0380e01510002404503203e0503400c80902c1d01c1e821301a00140704034410340c20b0201c92110075848005c081e0941000f0f9482290741000303034031205503040640e04010b121a081640c0c07035a50300c1e00c071498014201c8180c86524001050460200240c0d4140c94041c0e0b2420b041410b0408014000c1641101c1030040c0184400300607400d80c3c50740014010105150722080ca242017802d010740d4030095103030a043c0b00d2f55051006004801d0600c0c10803810200c1290100f0540c00f480c1802410091703000405000700a413241120181500f0000020381400d041008200d4ac040e4050f010802d0614032031103445000180100c01e095510544407580301214660303e0010b8038268100070040c80c000310980e01f24040c004a50605117180482d03e12003207620580c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 946932589 1250 946931339 946931347
    0x303160504150e131503020f010206040b150303270306010906060f0e1302030907181b0804170c01060f120809060f040810020c010f0b09130611040b0901020d0203 71
    0x19425001c1c080c180b400b4040280f55000c094a5079500750024541440d20321040102e03402006021001c8480f0b0700003680504261001000b0070f520015100744555003041d400c4d500303525000111401041d171442040d601d4402408928030b6540c1c010480c0c100210f1280c12600506041d106050400c00c050b40f04242491900c00104001900200c000c0344603455860b14461030820f4900141a400300020780c254038610c00b008100c00c00300006071500a07a8158070110740480550a9400191250409034602c03444800b0954200760303004506030751700244100c92900b00c28081d0040c0c03215a0304003038003030741c050382d12941c1c01c001c071521400c00c01000c2c00100806003445d00b4262105200792203401d40403401440e00040c000d43d141c001400780c402400304542510000094082298041d4001042447c9075500c0d0010712034140304a88988224090044c09004056841c00c0450103450001131058601d0b075204c1445d0140300321180d000f407001e80240f1311200d440d60f007104002403030036252007205425540100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 946933839 1250 946932589 946932599
    0x1b150f030c021c032d0c18050303070f03110d02010518030309120705031606060509090c0109150509040e070806010e01080703020607080f030f0f100608060f040e0a050303160504 78
    0x1802008040340d800c01003459102d004901c506001302c0e081424860141503480c0c2e0f284001c603002071210306c2407a902c0d9207588a206100c50074a035000e1103640d80c1640208030400000760564050f01d0501d0190608001c00c2c0e070010706003801c080042014400503551785041045001401d00d881c85011200030043d4210f15003152780316511124840701d0b0301100b20100e1810b0030484100210f4203046c2c0216154888a61a842d00402401c2a80280351203070020380300150002900140c0c070561000140e4543c107045250401c01c4a40480811203d81000410440d83c10542c90360700410170400b640d100101009442c1400b803e081030341c103810040d411000d000040200500000ba107405a0b034040744d0013039640c2114941500c040c410786c04052980711002c81088105021704907414403640d1850f8058203199101c506003625200d2900030000030a038000b011a83c18241030b4944030340d28a000d0000111482a0788810303140410a5038201c0c0c0c01d9000100b0081040c1440815801091190800a0a007400c103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 946935089 1250 946933839 946933873
    0x1202070840051e031c020132060402040506120915100e0705040306140402030d0203160b041514070906030c08040602070c150c0c080307020d1b150f030c02 68
    0x41d114003480f40182d00442100c5603620440c201a42c0320040440d0701c00001e9000c90144181900d0040015503e00b8440c10508043e081010b034a01e200b241c15a0240408000c0703d1000360360180c0032a4211303900b8440400c40e51550382c020000f1009200640c1c0c000e1502400c400e2416912108410968110b0342c28001c070143d10310160025100d0070300c5076008940d50107000f101c2030b0003540e1000c4c04050402000d103156034440c121003406a4000c3c0c01f5260350543c03200040ea603d11400d6100140003040d008068007091589c1d0240350000e00c00e40c910b030040c0070b07203240392000d5400402c03401d0b018032046024005295000410000102000c0c00c00f4080d0081502001d4a0301a0080c0081c0100b074000481104005500c000c0c10302400000940351402c0700500300090020900d240304590b40c122206011170040000400e85d0403080e4000c050301740c03500880d5200c2c10039503e100d00000c060814188003160010b40c0c20060040c583ea6036940a08410800703000500f9505010022800d40d080a45c242558000e9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 946936339 1250 946935089 946935217
    0x1030201050c0a12031a010306030809040902010e12010c110d02070b07050a0b09030901020f01200c1c0503100510080403030b0d020a080f07050a08070612020708 71
    0x900307040b5100e52000d9000ca0520030704140c01001c124070003d680c90a5905540040061266a45a052560b03401c500541c1201c1603400b000e008002c0a018440385898540c0181c40700c284103242100403015100c1c04164900f803a4100121281d440d004d4540849a1040401c1003c0a010008004020120202039241e0000d4001c080c00500e00040f5441807000030042c1c00200c0c1da10018900c100e103404c84070541c80e41c12250700d40780180070307030003c282228505004000d5803103a04d400b03450a6188028480c01d190b0b219a140242c0760007486445401e02488840000c01d40c106070701d071942d903868114000e031101400c64000900c100308502e00c41d0b019580c081c440580c0907030300d0700700080c240000c400001c0070003c0c030280095001c5c2c0c003110041664071000c0b4810001100290072142c4658a80d810841403c03201e0003030658035030100e101081028488c210440000c401048014540456512200300c0343d4811a40f140d0703c80d041c01201070002600c1c40c07506004c810640e8140c12040f0742c609003c0740c00e40c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 946937589 1250 946936339 946936343
    0x1241e0806010c02030a05070501081f182913020a0f030506040209130f0c03090201171005040603080a0906050a21020405040903020a06060e06130c0c05010c270b030103 74
    0x2800300000c0703059001d0900c0f010410340080c00c0ba80654145d20340075507108024002da0340060003400102d2132840c081c40d12031049002018000c18014240706c8170502c911603002d0710041080d141c88480c040350391542c20300d80c00c062400c0301004050b103000e03050040700d03c0c0e0303404072450592042019550300c41e445070041c00c1e806030703511f408a4191034240000e0049c0c007038040c00c2da900c442c101305030000041140e07211200943c00500d042c0000310341000d085c1c3c101d81c1c41c5400a40400d1b900c070b060301041c6401e964101d038044008000141e03c5615000031038110344c0170b9001141d050000151900c6e003036410000c3c0c0320003030080380340061401d214414000d010905a20f0718000c1c0225a28031815103603074503010f49000d840040d108010f0745910b420000c1d41c0c3c032050355054400034540f103804074441c100100442d100d64005002180b0103255040c02d03900804184c0d12190811001c1c00c9001c0c0007500130b0040a0720134010303948680c947c5041109022068041c80c00b9107090318001d640c2004001e0300082600d044036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 946938839 1250 946937589 946937597
    0x80409050a1401060201140c030906190609110703021c09230603040f17030702060f09011503030513171c050d0f0f180b06040c0c05030301241e 63
    0x1485005040c0d0280c82c005203108024802000046002c560561016200c510004042d14254581d018407003000d21090b00c0d045059044a4005010007411582030490300351003602c0020703400d44d190345050441e13035000d4000114103c000f50798001d0640c1000f960301880420540e070300b0324141445014045440394803031600100fa02045c00f48078860b4519000e03071307492800b03024a03a892070589414090241510b908584ea04540c5014024880070001540c0c45561640c005040c942c841c40c04503410310b80c004000890359901e40e02e061003071039458520440254070a459849d140c89814480c045a4983c0e5002902060602910070844010004040d001b01030b1410a03003031a1405000100ca0612a42081c104050b00b41805203800120552000860f4001074408200c20316052540ca00402100207014081c080510007254141ca0558026a142c003001d0408481d50401a03444a040d40c03c00d90144040418410b070341d44242c40c0701000e04840c4140c0d032800c070382c030456180c0b9112038191400b20440200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 946940089 1250 946938839 946938841
    0x1060f0c060501090204030201091d060103021b0a06050708071407020904051e070608060a06080a050a1b050301140d0507061209230705040506060405040f09080c07031e08040905 78
    0x800e0040d055190300542049060045686a5001030040e5000d844100d00260b0300160019034022220050360600d00c000b094038030103840c0c0100440c06074004d101180c0d5941506040d00ea00090b003001601c201620690340403c1074500842d000d881072a000300620300b440101c48903100c929030000c00301c403c0c0d0f40c0d040f207500c903507910b4070f0a0251619000c00c2120200c41d01c1822000f4101400007070000442c3c9480c1c0d152031303069940300c0074400c0d002842d104003800b1a070010b02085512160340c01040d400342005030700050103080c0000012401c5401070581c80403039000001404107400d404400c0001c18420303103004d40e1041c22541d03595502c6402e031085400b040328500402c044800c82e40c00445050707405c01c4000d0100350043d4041e81420890780ca512080e0304c0b030340388002641c0c2858003c0c01d204400040100c2c1c102860281804003500b06c080400c4009030b03170b0300c1307400d0002650a80641204212440106170480c250301e000c072081e02040104460490750303038440200003445c8030101c0f000e8590142000c40d00b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 946941339 1250 946940089 946940117
    0x20c07060c05010f0606120614060703200d05041701090209060d030306080a060c02010c111902010c0b01090e1504211106010603050709091a01052503020a02041d060106 74
    0x1413501c0359140444c20300700b0074001507141c0d10540c210003c0400304401c10000c0c0d543c0000c0c190080504181c2500144140092000329015401e2006100000c1120300010107100403003074140849681d0407000b00e400414203000034807800c4a20030407411454004c0241c2c203010b4002524464009120f0341c45071041d01d68040800d0b2081e000040245900d2081320000c001030701c0c0031005070045c0c0004000540c40e04200401c440d109007142010070f000d0b203000c1c1180b03683c0da45d81d04180701c0714480107906000c0609504800140114441d17402400c49220000e500217011034520705013000c042030100c078204c0035018030010a14025511407030840c503172a002c0505d0210b010945200300482851a0103005031400000e6440e09078100306c0c07090541d95900c03c24036858041010440c0e00d01602040d01d0070600c60400c0d078950041c00102041e0a2180c0340741065000c082c511260034110080407001600200b20103001c505160140d416200c110284400042400c00d40050351000140324400401000f0403a9400d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 946942446 1107 946941339 946941341
    0x2011a010810170111030c04091b1b0c0e071101050702160e071803050304080c120d0c1104090309080c04050c0a0f0e06030115030f020c07060c0501 65
    0x1500b45003005503001c00c102d08210091850b641e190109002000740342d020794440d20310500c550390394500701a162380a447d03005928030040d28050808002668000320b05540908194103808000b0303480d800c0141010000c0d9000507010703000101403000c100d0b8815a05015030340d0341702c0280080d84582404030313510f100805c582061210341c1101808a00400201c0780e42040b201c2ca010a80c5e0308003142c03503000a035002e500231144c41d03100080c108400d05003480125a256400c03501040c001d90100c800c1030f1288820000801000800400101040003074021050301000240080041054500c1e01500c00710b124000e5418911411510200e03070700d000d0203154890380c0c58442c22030400090550648210103147c000c0302c01e200740341d400307000a601d504006e0350003080b64420341403600c6019280501151114a6041c02c00c5004100d840204a000501541100c0d803034680b40c0c5600d12203080441c = true := by decide +kernel

theorem cover : BRFrame.Cov 946762589 946942446 := by
  have h0 := BRFrame.cov_init 946762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 946762589 ≤ n) (h2 : n < 946942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
