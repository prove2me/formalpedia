-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3125
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:44:22.888748+00:00
-- url     : https://prove2.me/submissions/fedd140b-890b-493b-bd5c-769d651b5fa0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 561870503 ≤ n < 562050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 561871753 1250 561870503 561870523
    0x2030303070305040302070b1309061a120901290127050f03191a010f0e01050402090d06060b0a030f090b0126060c0703020c090103080a05070f080403060c11 69
    0x541003000000e078810b0180d0802c581180c4039104855580fa038840d12940720b0707080103020031041035910301c0030000010305d40280d07409031941681c1e00c499560303c44a04450340c45281c1c000a40255008000703441d000302980100c1514108403010591071070480c1d0b4255290f192141c919000c641d01180501026034146071003100510071685101d0700314181020000381c0580c05030040d40c54803495100c103625101c80307090032440e10703c038100c01925000c0403419410b030040160040c08040500203010401c000d11003402da4119402070720010707502d10244c0c0119500004c0920080c010380d0034a1000103c0110304801071495445a41c0c040002840d01101181583d4005001501d01c01c5032030014400200414880c20301d44440b40703100048500e1a04101e41496022034003809603800c042644000e16405001c100040403048880302010742c110b99074119640a006c03800303800c1102c049081c00030800803c80c3c407108241c02140080d2036598030319011020342209464038000494050f482c3c2094140059141c4003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 561873003 1250 561871753 561871759
    0x30118150b1b0c0d0803010e011205070e0a230613060e0a180623011d1f1e0321020a0b060f120a02210a020f18010605070b01050d02 58
    0xb070311412052503803501c0c001d200d88030158090740070b03550780d50f40d01d0804916640e0300c100c10b040d840703614080c1e03c3d1403108030503804291076a0700c10700c1e1400080c10200d880001e450020703049000310345a011200006142104001118100c0c0e000c0348049280c1c407650b0306211301c0040307540d0078800c2004101c0b001030351003900c1010b100001540c08180741c0032098100742a01d028405c96546407003a00c1d03d030302c8199905903040c11808010348100c07581800d80105014090200c80d9045071410b411000250f1800381d005100080031000c41e04550540110441c88400501c4c010001c1c20511008100c4a0452402440122a0552a1180e50800d038510a00100d00800a40c000c0d01d58242d040e111180c10310700c010a00c56020003000444001660303851006000684100000c150000b002d07c1401000c1444420604480c0c0040720015201c4500068401c1d607035a040d281c8500c91801040461440603402c0d44030900f41d040600041a159400350180c00843c7c001d000304000c80e41da920902001841c03428000c1c0d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 561874253 1250 561873003 561873007
    0x15080f090a150b2803060f110a140f0f040906060c0b0115091508060405060f1507020307170a03090509010b0a03091a0112060b040506031e0c06030118150b 68
    0x511000d500c0f00c400c62038058184c01d035404102c00d008085444801030848403125000d018418030250b4400c5410b4040c21000400a200f0032501c988154024441400304000c404a410303044e4000b0074042d1818071419181068407628003802e40307140341e04240100c0300514031300440003985a06c1150850051034014000700d200d03034200664414680703a0044603030103110018200080d0391500100c0c40958002c23591340c00d80e03d401c1240c204415660081e000030f100e14106030b1400b1543d9110903030001040002c250080d40c4410078408242403100c640d2245a0120840181c42206d460104035914902d00c65074980ca0140c2d03c8074100143d0107028003c0c494031b07440c01d01134121a0b50190340540c6940340a21100120003003556601d01206c03800360001e07201c0c483c10031031110401c5154014a001c84d0421182444689401404030340c1c0c900d009a0102c4060114100d002003030b800600c480e040380748000d40302540d01e6859007101c2c40144018030586208528040810f0303410046140494155040e881c8058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 561875503 1250 561874253 561874283
    0xa0201110a09180e0d05030108060a060f0b07020102121209060a0203011d0c0d0606230313020607030915080f07020c010210020f09041406041404050c04021315080f090a 74
    0x400c0d040500b0b0403801c0426a9014441544c160030044a507075003255680c2e95a44e07605000d0b0184c14011302600414802e82000400c1c000c400089034410191005001030315141c04107400101d2074080c0d4180205001d0000150000760400300c00b21861003a80e20318202c40090301c9008800080348024030a64420101d4188062814211803510a0b00403011103420307401d00390021102d908981407548a030010a800e04003540d003101650305d2043e4200800c0c82c54a0862502d122440c0c285030104000901c5100001541c0c02014042c00f05603015010380000f8803001604601d01504da20000d581400311808001c0c00161114030004034600d4514040e8054100c0000c00c40456002e5040540d80140c80703842884900d02e592510300c6150340d0851045660217031803c0c0502400221100c1502c28059040c0640411011440005a50400034010f4800580e248550f1680c0740c004c41c802c2c0c001038404888a6140c150071039000c1f0a03a4091710760002031015a48a11540d903655120f8101c00400c0d030040c0c0b030400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 561876753 1250 561875503 561875519
    0x13030611040308130e0901060b070b0403030225021503070c02010c060f15050f03060c040b0313060609050703050604051e0910051602060f060d0f050c1002030a0201110a09 75
    0x91015041203450826490f5562000c0c0d98015914400520725400810000d66009841041c5c004000c00c0080000500340078200310b440c81614005014500000c000c1000c2610a60441d5520240d111901c003e2032521700203c0701c031031006282a03201d900c03050400320800d0915400c07240140c100c0e844580c082401907005440b2012400400d540566031082d00f101c960303d040c080c90070302c0030f4230a43ca002c81c00e080004120440346034807078640c0681d110004011801020000311780c03d80f0112016240c4030754400b10b81c2c01550700c10036002000b0718117118000540b0034403030308030f04e02803c142d4030288103a640300c1c3c043c0412900106da145d0481c4114404500d14000c104441d140c00c450351740203440c14015030580d0b00060f181c040d901151065055005224065418405180c10580103e0460414209040064206510400050181e0100141220810604101042c02144043c054207010110b52202a44070b402090681000d5401e0460421074000c144048484c1d2410988803807500500700108 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 561878003 1250 561876753 561876761
    0x9060409050a09060626240c040f120209090a1104090807020a0f06110c0120190311010b09010b07030c02120a060f111306081b03040b0417130306 64
    0x18070312203250343d08101e80104100d40500300151907449540d0000e03202c0f0080c14401da4080313486124250300145082c8a482418540c0900509035000c00d1511940b22281704103030500c02c591124000f01500d02c40020803070482420300e22010300840f1620780940d44d203103009440d454039100c010520308030351040d00c5141c50254001d002c140c0c090640242400415400304008000c1c03a0060001e1001c1e40800b040040e07400307811039021340c6405015001c540a034000280a0000f00c003c45100ca10342e50001c420174000c20801d81c05107441070308451035084418213010341100c000c004e1400302035080c22a5050075042245e48981208c8001d070310b040c0350003441d403000c590f00e84041c242260300c02e00f030406440b4503070300070006542e44500030000082c80101c41540071040b00d0300401e95412807401801900f148455040440b4200d440c0d030309240304580e81c3c2e00b2505a42c1d00c0008040c1444180c007106000510002803802845a8840d500030000400050380102041c0622042c0040b05080184280300003060b43e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 561879253 1250 561878003 561878011
    0xf1b0509090a05100317041a0c0c151c0b010207060306050a0326070b1015122c0c03060a02040515180d0b04061a0109030605062b0302010c050906040905 67
    0x9800f04410381781c1d552004030300a6004e035030884c580080b5041c415103010340c0350b001005941c8000355291044820601d920744141440861240142014000d21490745004a41140d5800d60984070103c911134051001440c031f0040143c0188100d440c08030b0100d000b0702c02c1c0400da40c0300400720005039256035614256100c052030185185e007402006880c0b50550900640850b51181c4031b040b0640c42c14000d4450460056842101640348148100c500560081000881800400000308031600304060644000358503c68801251400d90280301c8400008900d980d07075030104505513002611001e021030113074042c0340551980140004d42544181c10890001c1c0005a01c40c88010b10600b050703000a103050310110415141114914100010400203108d864400c0940c42100c480f04400100020301340032180c0030040160307580e00c01081440c0d65545500011802e178400114405403003202d800341661119208801541c00c1c5981c2c55a20b40c01101501c5404001604e140e04184c82c100500d005488060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 561880503 1250 561879253 561879271
    0xc0e0306010815340809010c090506070f12050c10110a180803040e010503010b031506100c020907030e06010b0306010e1e041d0c04050f040209190f1b0509090a05 71
    0x5100c0b0034030392040d107206030102c18034820444e28001c8541400b40503c0401041d81809914010480203642c4d0400b05401c01c1e80c00a40d441e58603802e4500d041c1c0c0d0079850426000e00303d003444803a00f00d01242d02c64000c0c50b0989180d03040d5000d0008a4031340b83c0550700403100c50cd181c031200b402001c1c041e5112781c44c00c0703098056200141c45541e40d150045410340d84681c200c02004108440140300a084c24040d0302d00c80d140950041400341610f1460031500750780900107510a00c492081da52032284036640f0210b2030360f001403681e000c50906d9031000c0d00038800c0e034881c03030030380d010780000050403a654400b079a10507001a11626140c104040800c0203407100701340c40803000b00c140d64500396241c5861140304c64480710301c02c1c030300d8078072695400d401d10781003d803042c2e5403083d4100801c1101015030200303001d030407646c15200b065031034440882c0180010324410401c0001440e0085503002030350260041c00105d45800c4400300030180c10a000c558920441c0c81c00c58004624401141c2c0000b81540a260b20040398 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 561881753 1250 561880503 561880531
    0x2070507052808010207020f0d0b06060309030708190e0a12230a111507020109030f24050403030c090501020303072307150f0e1002030c0d050a0c0e0306010815 70
    0x109100c600d802d58107401508442c5e6010076040d046080117000010011011104420800c00c0d80e0b803100c821540080200e8043c80c0e0200c04102d810100f00240d8000642c040c00c55516aa501908140c81503450b007403400015055960945460804800143c10356503040c9600c0712002c0180c071203003109540c07102c40359400005040c540034662818059500240d200e0040300d40403a0380d8100f003017980c3c0c840d50340c2d231001024100304000042c0e8012140307200700c3c1ea020303800c800784411741d040ca0a05a582440840030351041c01c0b110720490b50042e030003244114801e460802159055142c1100c0d1880103000d4140960f0040000c01d0300079000714051050400840352200c410304034000c0011007500091412280ca86a64502c004008964000c10031480ea449100304445000d01d0b078455902c0e140c1d034040700002540040841c0310058400d084400101403203000340100d00740520319200810800114100080b943d160f01205460f000c07600c0d078101d0355800020046030aa807203410418a070050604501c080403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 561883003 1250 561881753 561881809
    0xf0901030b1b0910121113030f020d1704090f11121003140127020f221406102d0e0a06030203190e1207060b0a08010e0c01030207050705 60
    0x28403010822040d03141c0d4520b100040b0b070100d1507040c2e443e5000168040c40b014401c240540a40003283c0b000c903a04503860403202c881d18004030b208050841000303819a00c1c064280001641c3306801042119103441d0100840e44015190904413a918000410064400c02840d555010b02c800700d070b50028bc40c001c1c1008010303644d54035070a18400c03080840407140d44030f1b40c0b000070682120040c00d540d080100d14903400200e00354000365640000c049601d1141000c03100c05000d42c9503c58004040c0d4000280c10400c0e41e04081e40142100c00031901039102e4851080c01641e080d221751155001020900d1501c3d404580303964500004141254801003008a5241100c0c0d01e581d640c0940310090444e51001641c0741010b200340c20f502c9152000f0081d00b01d040005d40326007210006a05401c55a002c000a41c131454149020800707401c0340695a54404803c0d00c0205d10340b10706500680f00920603500304d440b4007070b08800640613030007840c901410a070800142007100342230041c5103e0001440034190700314400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 561884253 1250 561883003 561883009
    0x5010e0105010c060e250504050603070e071b03020c0f0d020d060b010210020706050a0c080966091515030403090602061b0d0b0102010f1404020f0901030b1b09 70
    0x812003090201c0e11b1194031060a8a0144054060107045c0130b032010f2102d45044408aa9240d0042c4907e42030700f2047d2001684151260103811814a40b0381c4c03610304045042d06000350b580180080c0503210f4800307075040c4d081500e041900103281e2a409450024071010b6912444020700800d0030141c10f60040d0002075140c42201c1c8024030020b48540d400294500340005903100312400c2c00780100030710100405001e046c510005a82c5050b506000b001403151540c0e160082d012007050424016114481d0f03c1c0b000e031465042d00440007090869800518240300d2103807820007040170100701e038010840d6404a0000e40420704489480c0502400005444030101c003000141d900849065001a6841c02c040c044654144180f80e044041c115034105182040300c040300f07841c4500d03401c1c0141c03039a580c280c1101690003900200d00e50110800f0801000c0743c45405140d50320001c40701281716001d42e50440e149468030707892441c180d035004101d881a550303c02c1c1c0311088509100b1206110940140184c02e4950303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 561885503 1250 561884253 561884263
    0x1090513090b010e0103051f2705011118090901150b0d06050603060603130c0302060d1e090b0402060d0b0a0f261c092d060305010e0105010c060e 64
    0x400e259000040c5403495042002c0384803410b03040b03002d101080400400124000048442d588442e51002328658920b01407140002c020144503a410392400051210160700c120004503140ca0080000380500b42c8108410007841c8220203400358040c1840b0900301680c1004085140d001050303800016100f01001110018214642c0c4020380940c000140a505c103003103402002d0080070300b502c1060550600c0c10018000d804000d03d0b0038403030709001d80c0d503c0c280b10450310070310000d5401070007280d0341c0c024018009020301003290218200344548000c4c00c406481d28492072940c0c0350010803d045030f44840e070801100c2e602a85804030030b184c0b55003c1591681e11407030240700a2031042a02d828a51905440e8550046158456000030803002d0138040a1840442c811450440b880c048031400f442340704003a150030a442d004510350b4400419039a00c084d01d40c00d5005540c1e82d9280308010003690b140070880030754000740511076100d0281c40041001c2c0d4028000e140005214610201d89030000703d10b0b403860070b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 561886753 1250 561885503 561885529
    0xc021002040308220e04171b0106050f030708030d0209240702010e06090a061b050703060606021908090f0418060b090115140901030b0d080309010f0203070f0e010905 73
    0xc1d400203007001114802c610f04d04198013031200200344149480c3c00c0600e00d8200410142c40b0040b015007002c842c9002d20100c4110700c10304a0b07540103901600040714020000c0307001c0e02d8010162503d001c6290b01e00050040c00b207600301e00080d4074141540c001c90000c1c1d0040c8603010b40013880420b1312040260b509030f00c4080c80580e00325448e03c0e010f407400011700084183c50094001e140401208585d5201c011a81064800d142800c02c1e400c41d191020040768212020064014040d00700007004100158000000721203540d4211507010080741c094000c418401100100727408410000712540d03092088a00c800759000038000241000c0c0613140b04c4000d900341030211411a968800c00070700749481c007500350246c041000c1c0a5400c90601d600501500541b014010400201091f2411a82c4c80381c0c1203100c0c4100082c11025620711585008a103c0c3c1050f602210954200784508070460500d01c02d9a220301510f80e11654410320b0807405556103403451024034104080c00b48041084d0300c42d056501031f8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 561888003 1250 561886753 561886763
    0x912070b0c01050403020c0a261006031b0512030304030c08070f060c110c131a10050304031403070c080903011103090709060b040509181c210b130c0210020403 70
    0x124a001e103402400c00b2034a0100600c04d80652006008078892042070822703690f204a103c1c815505803000f03070784c41c0c2081100c96600045c1003d0380801008000c0304110f000c5440400c0350300b040c5480e1000c01030b09144407540300081d41e01c02d00000b00428030801c05440d400740180c0c01d1500d407035030648400d046103160803003c0e1005034581c00c4140c840c56001601003c0c6080c07200182c060300781104001074503070005605008043d0b8a640160524a41740361100c41c0d6090014102c2c1c140600480000c0c1c01d0350030849082d8041502d000c01061075260381030440303100764101c1c0c2d0707031740c4803181300d0350312880980c0050658036015982d40c01e0f814069005580251f0040c0b483c4001051b20614142c0800150f0b00d50343c021040700241484200042e4607401030864011140d03109140e28001040511850306031110351a460340f08880718803582150b000b03600c2c104004090141c4802250281c1e40d400242e4410000b0b954200c1d00780044207602c503180354000002c4881500c1941c00103150303000c02201b40e8015400660b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 561889253 1250 561888003 561888011
    0x80408011b08070c020109230a09150f0b0f03070e030609060105030d110304090c26150306070806060306010203040306051501090f08120a03020f2a0109080912070b0c01 74
    0x1c46800040c0d0950110781c03480c01903108005980001c080e08a14840e10b20b49102419481c6880c00091383c4008003c03002512800c40c00744e940c03013428050310302000412829100d504c0c1c0400d01c3c0d84154825800e039020300c008a407030840d0301c1d28242c0f9103520050241c42082440c68403003446550a00005005407020750090a90354100402c0600b460f000c5c0c4042c2d0f007401030316400558803d0380401074808a0b08500340010710034445110551f01d03031600703000030410a480001d040340c0c0030006c0420b5a019020700c0b2000e140900b490402d2690703468054400e6001b02e82850000345441c03030140c0003107130711a2040c4162030800d03540f55101029598107039100d0790009900e0410f0300007540d01282c0e0000420114144011039031500e03046984940c8094007100750700c03000240c1724540d14000d40403180c00c0581402c10f29078614611000e40c00c140b40080c2182c004858940e0307400030055050040c0189150032441c40c42c94440502c04011409002d4100003c203401760f4580080c100806101034a600c28520001003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 561890503 1250 561889253 561889301
    0xa081c1802040614011e0207050a08030a0905010309082a0f0f06100608180102120f060a0f060909020904060806090d0909090b0703050403210e0705060a05070b0408040801 75
    0x4010f8440d039400c80b014281d0b01d5000b800035681e00801c03030000092030407206412194441012810045590042604103c000c0c1001510110000c0180814005a1350300420f090b180c03c0110103551003008043c0142a050051803a03c250226406a400b640d1101c0005403403441d04184e800c07e030000d24207444a800800d6000c500d00010320402da40700d14a03c2c80c2100312401c091015024000c040d094611a01290501c905202da003503049032205007400440b03150900d42800004031081e003c640300d600841b40e1280020702c2581107250601070307414035104d07004240e04200081e002500015000d40d841500d40000081c41c50090201c5401001810003030620700080303800180c10040250321800c40680360111041c003203419a030159411014600d07010510751150308044440600001524441e11040c1151000034000b550040722111186415103403402e568900300110b0340034a2186201060b010800c0b440051090750f111540719108400310340c1860b4850003840c1c21035511194584000c03c88075104c07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 561891753 1250 561890503 561890509
    0x6150306050d08030f0a090602030f010825060f02010605091e0f01050312091f020706091d06150408100501051c11040f11070c090510080a081c1802 65
    0x203000a001e003070341e04150020707469440c0c440ca4440141811001c0ea280c401244012415401c4003440c02c0e0088000d640300c0c00c0443d21030603884000c0c440c40500d4410000340030398101c540c4010b2800804142c40c110280f924000040e10110018400741c01103540e1030710040780c181c0d100b01000d0b0003659005122289103072071000d4600009409041502d0b84031490004010030340c0c0004880e01860407071b800a0b600c503a400b6020a0300d64074100755608001c864a540d00030b00c1680010204101d80d00b60342c44450155540f510721401c0301c00440e240d04001c069800040060401d40240c0b0381c0141c500070074034603165a4841d401d0074082c2d034140090b200c2d62100c0040103075242c44019961118080007000d816802e06659020b5200c0844070043c2c01951100340b8040b0082c0396520000007001003076142c030354819640c9020140440d083c01035021442c90000415865104111600700f5500010020007403092551148400364000004c0d5040d1411030002c1c04048114a009000070070329181c11716140c0d03412503c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 561893003 1250 561891753 561891761
    0xc01020c10020a060f0b211f06030b04120822020d1407142103032e0303020f0f0d140d0609061d060303030606073804120206070c11040f061503 63
    0x80414400120302c98045440404203060907120b9501c9230045406c0040314110028007400d0b400170b80309107424420401400744140f006a541c480a59030340c05142d0310140061905031400c0c400c409d10303e05140f0312000600f80800140aa54020002040791002000b1032502d4141c96400c0050b8680c14400d020b103083c107003800c4403020030303846140c0031f50302480350501d032640e03400300070f0035074156800d000680b00c0349400820000215082e410040e028564580c01e01950310403005c100140c540c400c481c0c607a0541000440d0752815148180e07078518a002d190200710009812070603100450030341d2000d001500041d244269001886030401c5001e64090401400418000040c0181c1c025001042041102d40d9601c0480c0e0065603c0001c504110000b2000040550b42034040f45808000007a400d082c075542085a17903100790b2240f00c85400d44541c0c10030884e20b80c40217039140c80128201c68a9800010040580c0c004088130140000540c8080c0d401d0100549905511641c0410b0364407806544450f85070103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 561894253 1250 561893003 561893029
    0x20412050607020a11040c03090b070c140102030f160504120f0201030c02070b03061e1003090203060702010606050a080618010f080c0a032a030b0c0405010f020c01020c10020a060f0b 80
    0x1c1d0032910301c2ca4170758078481102c402c26103200b295200707035108599010b54080d02155400c03560403c980d28041a010342200c92200701500c1646d00d138092041d140170705000700da00c5202501a4010701da11004032040004905d0b45c00103007804800d100200300700740100c0d1940f0600c1c0c0140700c3c0b510411000e0001604494980c040302045400104c410b12010500d802241c0d004282500d0304101c40340007041302c20301581980c00c1c00354085045412045640da040c0c00ca41d030650f0003201514200d49614505a007214058420680400c0052000c80f488070b015240703581d4015005000010407500c07008006c82d0100c0300360004030020301100414400c50408010b031400b0041c8c03d50f290005242191a55501241002c49504003403141c000c804000c0300080b55a04019644840c56130018100000400031030307040382c0a5140001c100c20340c40da05080c40040e0058a03090103070040d040312504a002d100700060901807510039071290000540014030588610705072130103140d00000e4002000c000704018400c041d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 561895503 1250 561894253 561894257
    0x307360e010c030b03030307020703021002100e06040302120a020a02010804061d0d02010f09170717040906050405070504050d110303090607060e1207150b01090506040303030f050a05010b0703050d020d020412050607 94
    0x1f008100c5155000034501040d240c04407a290600e844d445012840d00e1f10002100d41410308001007002d403d030000620078080c40c400d80036145907018240100c4214001d50418900584c450389800015500681034660001d005041c0482d008a4211350345841c03400c54880e200499000c503020a01c0c450342031103240e54a207401c0100740540707030098807080212030b03100441ca10100700014207541001070b60b02104000d07265007034106031503581c0c40140c41e0043ca10380c07240c94011070402000615007881081141c00351140105908048809a1540d00345107001c00c014030b80522040050481c01e41c0d40c00080d02400d441128040b41d00340400d4162400d205904d4640c480b4144144540c03c00035020b001817409111040c41d001500c54030440c0120b42c0c4441550095800450002d408402e02d44d060300403e510803840c140600694a80a8204044403000d02c90003100100074412440028800e0004105a0040a001509007010000344000f00ea00580c004801008124039882c2005400c5c04083c0c0d00c00914 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 561896753 1250 561895503 561895507
    0xa0906030c0212032d130b15040e0303040606060e06030a0209030a0606092304050c0603090a0803040305071119151403250c0506010e071107060f02010b0307360e010c030b0303 77
    0xd848148201c00d00310002020100c0b2180001ca440d400030808c0c407141c00d801070080c4024101d50b1085910790740256401d68905040040c007081c028081c0004404162018020300e146a8403200d0300e50094111010709a454028007246034085030344c502806001d0411100005203030941c080101d56800d2803000c100319100c2c48a400c000c08690f0100782100d010009496a40c0e0300d0b41c0f80c04102d41000e43d0b0a500412408001c01400f09159106000e04522031090f0065840080c06004104c0c94154151031080d0849030714205200244a11455450301002420800400900203a101545070421640e50012041108041c0040c0040303c8221b52001210f041c5000700d840f09844030383e2580014000c0c0d10070301081c0700100b00094070480792084441e0003a02918a01c54880070024502c640311a64a0010341c01d04290000900d0301007403110440b00103079580f0700c0040e07031400001411a041100a415900500c40803032070704186000e103c0244159800006084000c250302a00b02c03403101c1c2c0c16502039841 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 561898003 1250 561896753 561896761
    0x601030f0e0a2d0506060a05010c15020c0c0d06090c0b0a0c06050c04050301090506060102060601050f1206060403120e10050f160204020f1809010504020a0906030c0212032d 76
    0x4045506492160060102980304141c0303852941c209031680f50b0f28070001212041102400b0002c1441801070604841c0585280d036107400440f40811800c1c000781002d0b0100d180411107040f02e500900d6580100c809a601e52240c0000049003401c5801c42a100244c4a081c4607081000707421807500035008042d0100c2c104240d1900c024004040c3d04c20061009689201040541103201c081d1801400010000e01c01d00d9018505242c941d2002e8803098054454070020548540c014015034004030090130090341400c0740c9010800c40d282c00540856000304c4208004404a421400d11044000903621038800c0b51411138207101e40c8039600458102004010b1081248540c486422030f1b556207040b9000101c004d159000040080c800c8030f030003000340140007410000b00882244411075429044035180d900360303640c0c41403105901c2aa0b50a20021b02c00a40501030703140244d1250802c2c04040c0304507010064000c500c3c4038242e00a551105a080f401a000741070503c9500030996450500c003030390b82c11818 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 561899253 1250 561898003 561898031
    0x90c0f0210020a031401031a0603010501051c11100206070e0a0609031b0b131406070803012106020a110c03070501050315060c190201021c14071505070302030601030f 73
    0xc5039800045a80d90006040783c0354910a4011a00c20f0b0305d117030070004203035940e403070000b440d090061184804540342078002000c918040c807603503040f10f001070306c55005628484004045076461000803240c190a64540480c0f07911200800764046141e030b00200308a08010300083c141c4454100f01c548100e010400900ca41c0b07502865040480f0361050445210202440b0340b202c0e55007198001500140000c1070780101c290761803116108545050803411408000c12084c842d8602c50320001800ca00000c0004120591419800c0340c50040041111907aa01095590b903059a004c0d0300d0000000c1c03600c0a03440f030010303c144044c51000c6011002003400c6442d0400292982c0030081560300744c41d50281c500a055150401100d0700c0d2442603056503000404920101e034404521801079005200e818040c00c240105140c900e40c0070307640d54641720002e40306030006017113a81c800c2c441281d81e103400e01000182c0c5a040c0c001c140c05442e40c1e46001d43c403841e1400004040341e0f82c0440410301c040c01c11038100d403520 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 561900503 1250 561899253 561899263
    0x90c0609012d020c0a05010c0b1305070e090c04060b090a03140a1505090d1404030803070c12020a03020c15040e070c0203060408130b0309150a0f110301090c0f02 71
    0x44020300741205900e461000d40850340012016802d440d25109190b0624207501140d815282035048626400e11515540111144070709520300810305803400001c91150710741e51100304d01c540c0c0710340d08031003820340c81d01d2185044c22403e440d621030302d0b480000c440040d031030180151005491842030b41400e00070301d000000c1c09101c0a102c058002c024001c91442d42e408107100003689582c0001e4500260440401c80100800040b5582c851a004818001b030029215100940c03c900640300c032207041c40d0035500e441916609c050f110300140000c50b00950005201041d210080c640c2030f4000d04103040e0641806410404c80440d00307881800b1000011082d0f00045c2705030740540d0076001400f0060707079680380161468064004080e6140c420582084100151000108089034424040c3e5015548d00c061801460200303581c9009940c00c00c610205007590b206800c140d200b05034000c042100c44803540a9012510000c041800c42c040020040c041c008030390007000c46444c09490180c48201106100079215 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 561901753 1250 561900503 561900517
    0x60e0f0904050c030a140c030c01090603020315090c030603070b0c0729040b1b0a02010906080430200a0b090f120403060b092202040906061409090c06 66
    0xa140c05a0204062000c100a846940500034044480300366460901c01500b2900c0c03d4030700c0540c410f0003031088450070040f4a8806405060b10390840b410300300300040d000f03508010501000e100010a465590350b5a620b0514041c200010590760b403814024241410480b40303070010610154100a070310b4413603c000034080c040b1941040c03040e800001d090b040f45000c1e0146003059510b45004a000b1070300b03c4030f010040008555240450a51100a0340400c1c2c0352551244045e001c105415803c00035070b4028507201e54000c0c41011082000601a04854034000228001c9120036024410502c005a041200b440b00344075082074026444140e40030087d40c402141d40300810210644000c550300b40d60800c03c140c96070040d982074071001e20710000380031200e401a20007030721850b050016030881030a050414601403211000c480d07115002d002c0c60006101d0b01004220381240c3d07107803001c40100e942e80c8248406040510460983e4058690421503902d03030107044a8103542142d041c801c4a95104012a014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 561903003 1250 561901753 561901759
    0x12021b130e030c010911030d090614030a0b1306061701030f080705160801270507090e0c04022109030f030105010e040204050d050705090a060602030d0e1f0605040501060e0f 76
    0x1038003030380c916842d040d030044910400e81c2c0e6003001c6911013040ba44c00b03813951600c0c906074202e40e1003500380743d4102c80c401417911916022031001803074641d5107884a0300465014200d03840c0400c9444100020400b40c0044210002a80703540d0b160601856074480c040e01c92004408038418515415920b03070300c000b915400e8004058100008501003040400e00c8078030054103500060780010f40c0d0b0f55090f43e0103400d1508108000340e01000018140c5001c001d0080100307500000240096810f02ca9610b008204407500004503102d0101c82141a56070303070004100100c1c10746452030142c41e2900c2401403c4a000c0c1140203240c00c240112007003c415070066a0444209192600d0100c2146012400910854000075000300801c003010301480f500040e00d03412220250341c940d0321076449402c0c140484215000d07140060300200403c4950440e25007050f81c0649068040d90218141c501000e88a2004521018140303030b00c0d0702003045035150911a46005217494200522091058000074a20702e095420141c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 561904253 1250 561903003 561903011
    0xc0305041e0e15040f020a020d030510080d090e071704030311070c1211010509010c231c02010e150609040f06020c010e100c020c0d0812010312021b13 66
    0x1114014440d9688020b051000320070640d0b09000030010300302210555281d010301e081198101880045208580d6011702c0d42d8050a0520241e5030120050a8050030941ca024000320020914034000d0210b003100480c2500c5110300035103031007641d0440c01d000600c2c0340140455002080b030900302211a1603400740e8103240019001d41000070350103042c00342c108080c2c0701003240c0b5008544120003603003202c0807a0140c9420070840000c04011a4544075254004e40020303100c00303903000003d800610314890441c0c070b0200084d00f0b110604c00319151401c1a0040000200c404100011607902031017450300d40c998410162040e03040c2906081c0b8100f901030041401004140c0000381407100000032800c5003075026000751f54500341040ea19006e000c041d0900399440c01014001c4000300014030980025520f203401910307038500040300304030800324104000d6071000c038100301810b40082c0c51401c440c0038603c01d11400c0d880c0200d150000b858030005041410400440ea0008031443d5280c04a071240d4a00101001c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 561905503 1250 561904253 561904289
    0xd0c12020102130906081506030c060c0f06100303080c070507052b110406050a03020d0204230423011a04020d021c0204030506070f05030c2a010501080c010c030504 72
    0x900910507555208600f01ca43c140104612410380c0200d011115540116008031f0450082c9020708001600d44aa01da0f00100c15002c160030000003600710b416000003030382d40c3c0c140a0500182020720032140800d101070103072014005c050f00b012143d504100d5110b4620b040c28000e50b00c1c103a403803aa90080034400c4e4440034680e1305660200008030040040d182030314070888541e1810416044502040354811810080081001e0070a441194116278005080350514601502404002c011400340b40c020001c00001102d007603443c00722900d0140e841445800e0440700300342210380312035290341c2d102c05869041285081401160b074401c8500d05108440040e50751851a10240c000d10a50f2200c2000701000b0011803400f4049901a100700c03406141900c1c11503030b90315412641100c03051035000c0454001d0003c0703418104000702804501414940a0051440700c191a10300f6100350f0a0b00c4105a441e90014811914244001f9800075000c1c01d1a00d0001100da80280150003640990fa4910190002e45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 561906753 1250 561905503 561905507
    0x405040c0302040c030e07060302281b0305070308061e10020f011e14060306070c020a090f05191a04050a060b070f050d1809020c0c041118030d0c12 65
    0x300210382c020b108100700070071001c0180c09040110560440d0740603c4000058082c001d000310348844500d94051180c008440d070303101007940c00010b0f20320200405415800c100e5042e07884001e0180d80291562030310f4404d03d1030002d01d843c2008007814010030100c1501e280c0d120a0840629592100310348801000c0c1c0c80b45401c03440d100480205e00042e60900c03044025942001e5003495004818480070300404005019004c0000d5058680c0d50700766100d01e001403441c0b4802c1400c015242d100030300b490440e1369500c2e03002c03041d50134001d03500500765a503106008020801d2401800c2040c070f800c5041c00719002989010038100e118202e29400350f82c0326400214003a800368000c401800113010030584865160804200e2254505030488081c45590364802086002e54402003083d401c4540601c0805c0c18080107038042d41001b0807901c01889a0b1f400c200140d5140d0040ba0223080c07455080390303103a445005d85070640c010148401400b03a00900300d01861194481030605a0640100c05010003081a242c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 561908003 1250 561906753 561906773
    0xd0803220c090e0a2909030c06060607050114041515030201051803032515060b0d0b0d05100f06050604080a0605040219030b0106081501021513140c0a23040504 70
    0x203141c0c00c0404172041c01d144032000e400c40582c0039040c0d020850360f81c40242655070710810b0107150042d4040400510a0310788980140440d80c4240d00102d12034001c4c0b114070384031100c183c4017125240c01d0b541150204043d20b20501d442d07a11440102c0b031129246d034002804d14403d581d50000c07030400384001e111213510b0800480d800411070085006c4921940520440c0c3c00001140880700944190150130103806980100026240c01c0c0000c3c51801c2c50030700800740107150307906a03182c00c00002c20344140416001c0c01480002911800c1c0802c00344043c025031021201d560300500e20580050105108058000900c211929406000010380d03449900002da10580d4009002c100b006c8500c0021040000395038826040392151340307640145450708201c01c690350724012441030043e40007132200c0070003403801800725412042e00d5007600342904090f280c200e0307042c219000f85441c44d404042468014241510380c0d00007001c2c880e403040d04030007035001140f600f03880035094548100c0d200c00c08a0b05000c46540c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 561909253 1250 561908003 561908023
    0x1a0903090a090b0f1306060f020d09060c030309050303090d120c1b1b060509041503020616031101020d0219021f0e1519050603060c070b0c07020d0803220c090e 70
    0x1080e809220106a90703080608290701941000a008d503244245460000030b60f20040f0055890307032500d00b81440c008617802078460005074100b50320b6031000800302d6028002503004481100141480481c000c401410540043c540050b0151505206941e81588104221410500b94180c0302524080f03080c4000840a007580a51003181d0031040000e0780c80d0440001e1245803010b0380c1c1441006100c069000b221016444083d4100008015411480400303000240d01d02e0b10074200641c690081611490890f04070510000030540d00259058603d00e0f40942907404202c01d2000f0000d4002000004000d4440f0628068003c0d84884515081350401e1102052641e92501d1241492522001c0e03078690b0440312801d06111403400700414000d0a02040941c4141c003040c01842c5004415552011142002800c4035400d001c107014070801656840700c45c1d000107015072003182c2c81c0c0c00c1034a441446410f881c0e8400d6004c0d00303012007010000c1d002d1200d07481182c0c0000b00c0061880c80340c17060365007080c000714 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 561910503 1250 561909253 561909259
    0xc020d08040b030406110f07110a08011107051015181803210c020c010e0301060b030c0a1803170d0b090910110f070212191a0903090a090b0f 62
    0x100740071501c40800c101440c40b8a000f0f4000780941d01d000c80000b000c03841000540700314500200203007030101d491114124a807002c0985600e00450740c6004107400c440140d20313420186031001030300500b800820040e550450581032000c1001c450f00b03040b10754070851a4400d240064040201e81c2000402542c40401054905011605424144d150050903550a035441040800104000c482100c6c90ba10510802266640042c07800400f8940195076a071302448000c1c1d415901e4000100e20301741c04801450045004079109500e030078132401c02070000303a10302e0354000d02204203040030404103410610110900070805000f0344d07140c1c40078060384042e00d1540c10598201450380c0c28004401000160700d8460700c0100c4007000107050307d43d25005a03101d80d09010f2204d4109000c6c0401500d8213281b0250684a580203c40050980c00d66440804030b0b0000180c401c007108014180354901c081c030794958820749482c003a62400511000180034010180240010290b0300e2409150315289d460a000781c0000003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 561911753 1250 561910503 561910507
    0x21b1c03090f0b030130110a1208030a0c17010501050d06051c030201050a0903140d061a030106180506031b1c0f0f0b030607050306030a020409061407140a0c020d08 72
    0x207220b2040c00794006e10403204100b13075242d1400c0710999074086040305240c41d81e803030840c003405584500381d04041409043c0d500c40064080010592403a560406a4038030401c4296100c1c0b402903e13000441e140c9594800600204881c0186900b07100d480e6241511800d013031648d100c040e0312001c040200811b4110a403c11580c80a5a113040c00a0000070013080c8030380d0082c8242c0c0d81d820100010b44000e40740c0180420440350f10014000c0c0305c1d1015103c291405030000a6050fa511540d000803400005014800d410001c0103209035944000182400400050542c140314540000f0504610004000000b4815550020465040070700201c400c09510b2611000e40d034075079030403101c004140c1d2100030301c000c510709400011014154058076075241801009080256076854055035681d0004054079810300450079a03000581d03442c422101803500030100040c96044240710013040441c094103d909001020a1410307a0b401c0d02030890342e52445d24904001c083d412880429803600a4460040100b400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 561913003 1250 561911753 561911759
    0x40903020a0615120201030216020907170708060616020a180606020705040e120d020f032d221109070509031e100c0c0b07020d021b1c03090f 62
    0x100084001c1c8003809500c08010450500651007203685103445a9040580d00140660256001c3e41c05800b0b22801c0b00355020a095040d070000e10424011121503011031400b29040566410f0500307403560203015400c260050b41420b000103852809a50b0340c48502041402184086441c1c01044100034501020100ca903041c1003040400039004500a4000610170000d0009540c0b4143c0030780d049000070040034100b1a000c018182020340d002010360b0502c1d64080001c907107035500110046201d020180750000c200c0c04058004070b240e04000d4050202d460000c1c051014070303580c25000c5108280710301060b9901e0040e510f0017540b40c1c2d010202c0650710014600820a940d604071000b41004113040b01560001e918003055404250304550611003181d001c003030680046041c81d070110304a40c5071818819038030203040da07801301d40d183c08841100058100302c0c00400144c1c0c04208061820b998620115000d40114012411654210556407101203061610b802858011102e10028000001501c1c0040352 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 561914253 1250 561913003 561913007
    0xa0609050c1302031905040c1e0b0d150b090f0609010e15040807050a080303010603050705040302030109121b02060d0209040e0303040b150d0803130204020408072c040312050c09040903 81
    0x4100c4003005a48110219084000d805e4825144100d50028000e94490304050061078040c0300e90301c13000110130401c40b01007401d054600150a170041c07011340c08107c1e00126080c8001c51034690b400140905402d0000b61050f590700b00001c50b0410041d40d20b1501c80c00400d0048404c0350343c510440c0c4e00a0040100c0c0d8030710400580090058a07003c0c01103d4206a0300c80602107543c40301d20400c211a00305100500416101c1d81103a07030054203d1410900f00f43c3c8940010b0700319a00301c0e004480780e0500d0b00c44482000d8100d0940c0c0c1c1880380200003840c8440781900400d00302d202d05000d050002d54005001c60640d5902c7d4002c0c800c1020440c1200d40740c0c50b0a2518080035801919074035400c10342541d40c05174929140081c0804142d0010714030b82980c50349403039035940354a0344404aa00c03d409000200b032003601080710600800480c010840004400d90580038004620001500c010302010108400700760001410b4000100150000840341c1d180c4d02a0340190098194483d4414200b4481d002896 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 561915503 1250 561914253 561914257
    0x31e1c030608070e010b07060c0e120d020c0103020313030302030c070b1617060607260d150503030909010b0d11040308090909010608121612050c1e0a0609050c1302 72
    0x9a02d450450f03c1c420f03181c07403155250000901c03070071948200400c03103000081c40301e4109961070520ba040c0460001c4041e800a003240d101014245000c4e403007a03001480c0b482c0c0c10000602011000c3c2800c519504110814416144110034080d06040d000804944c00d11507940c12121141c0c2c01000d40125801e14211300340c141e514210320200002c000407034124002c0c1081d1000c5000e00401821145015590303601c01d480101000801c80c1c0c004600407029111000c40d030000e000700c0800c2e20000a1210608082012108003a04072500a500900030403175282c649000d04d5054820800030741e500c03480c0c003140c4040905007224036805a010049400410002114040d240c1c115003194440320580e41c061405080300c4d61171040e440107a10060f0103900082c8204005d05184200420b1030031004c0150701c501503503801d0042c02c00c0001e0070003c0d0440c050308041c0305145400300038018810b01d008441e140190355901d08007010344460780c1e580412080180800c036480324201d02800100003980a03004500081d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 561916753 1250 561915503 561915509
    0x60f050f12011212030203190c0537020c030a0318030c06030b13180803090c0307030506040c120809090c0424120207170306030f070e1006080105031e1c0306 69
    0x41044182c04d44024013034025248140d0b805001c0324180011005100064a2191602001d00400300844005140300381150a407050009505010081000c240020403903060300d915421500710f400300b45900d40d40860011250354040c982880d038006042e21012070301407240e2008010080030900055650303010b030801004c80f10202c5484501440c4001c002e0103843ca40400040111120b4442d48006910800074541002c40c640031240c900041c1408039140c20502e4205803110340c0003000300010001106104800b4000c9000b090710243d41c0b550701c0c0003d42c0540c1040358402c0700c0550004092000c10f03004d440c001c10901149000b60036840002c201514a1803a4520014803142442d41c2c801c165030007201c1b0b20944c400b2404400c1c14641c0035a0219800147c40b440c1d150040b000d00941104c0c00b0480c000207080346d12807a140d00c0c102024580c211020507407114040c041344400402035603070082030b000303516205179884180b2100d040c0b2289080c1082c40c02c610080304c0c80440100c11140e0b259102c0025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 561918003 1250 561916753 561916763
    0xc0310020a201f0b0102100905070504060905090f01020c070e0603100c03050f06010905010504030213020405060406200a031b050a0507060504050414060607020d1109010e0609060901060f050f120112 87
    0xfa620402d000070040d00c2c01c00903501c4c01340c2d0000c0e461060b44010b5178807000c0c10500a005907460103889000281c1920f11560004601d142c85009212050301d041c8407001d12292008001c52906a00003002c07916000c0c50f115144070394020b04000f8402c1d4030144021680c44c00010400c0240911002001e03006000c1554050300d99150a80002c4880d40907803080d00944805031205400d1520f19402c00c10b1101e8981642980660288000601d87e200ea00140000e00226240c4100403000d075681046070001d01d11418649070f10101c100000f01e50004402c1094541011b941400b1101a040c135620300004440e0013885481003050004500d42d210700504242c84007254203005280c2d905a148803071120555006500c030104000c40130051401401542195226000241250400c98001f4080340c8003607001508440301201040003601d02401980d501c90401c481c2c03410360394108030006040c06d07c8040404144a40080c02d0b042c00c0403203005490307203a900000c40440305d60b110b440c5800d003189280c208540e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 561919253 1250 561918003 561918043
    0x2d05090c030708060901030308010902090607050102070327030807020f01020307020325060306150f090905010e1b031608091614030f15162a0c0501020c0310020a20 72
    0x4c0e00749424100c0764100c81e019901d200a0fa400c080d1400000c0d803189a069502c0201081801c000960a0000d44860785c000d8032514203e4440d40300000d178040040b45c074641003452021003480054685416540f03056016900d0b0680c1004000041c1c0c55481210b40113540752003880b10740c40c0d040100700108180c128004204a00203076039040d050b8240e8096000c1c0c10064244500b251a406200e01245502181e445c500213a4982d41c4050010444500307030001c10031280d00104111144031036140d001509804010038600d1846c10402c41d004849010780740d64104130300540810240a8104900348800880c0150707071310580e035141aa141ca251560746228000d006060b500c2c174001d5030210301d4000009006d00d19100c155a160000f640c00c1c55462100c40502c00110000f40045071a961031002d9407031800320031003200030281081a18100c090388014119800310140d1011138034003188889038001d10680140e26402440740c01c3e00c0e038449868180d101c1e414100000b007501800050b08101c40440c17154802 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 561920503 1250 561919253 561919261
    0x51305070f02120304110f19080c180412050d141f120b0703020708030112030315050114090a05030f100605011404060c0309080102030a0608070806012d05090c030708 73
    0x43e0f2590760004811407080d0051001401140180c0d0b1600f000140040c21488003441c3c010000345d6600101c0340800800d202c1601c02e00c51003804100801c1207040465500254101032541c00d21052001040105010078031003404007514042e00c00d3b83d004160026080c4401401506044600715088502124100401640341001030f0b080a2050645084011954288031aa00c0d00c10340050058645000c05070b080080c4000f00b10344501a6010b00302031040c0246064040c00c004040d1500c842d84d010141000b90b00800c80c42c5e8100c03801d0080040e000414544486100c000148800170070741c44240c15014100c0e107404106804603141000441103a420403680c4c0c1c560004468240c01c50301900c4000204010910206001d02c502120032846850228642501c40e11081d00703980050718401c25041e11040180041030b003c1c008100070740b020340d0082c101e562500b00007155034403141d4081d4082144080c002001610380d943c0c210041c0401038189150f40c20414600c4100d98811039401e40043c0d2054082 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 561921753 1250 561920503 561920507
    0x3180c080d2309210706030b1014190905040e01021e070c030201110c0a0b133003110303040b01090c02012d06052106090a1502090109051305070f 64
    0x740b0350404400407050708025000b000e0162080c0c0d900e00b0308500301c0010001c2c6090709801c01c60240a44110b40d4003080a40b541d8062000441211401900707010f151808006400707591000e888008500c19001e40c2030003100ba03000d0740d2024040d00815005410030203550b41c0404150001e020b058166491781003d41c0c085c1c0540c00140c018500002c00c1e01440c00c0c000c202541c8568000514401201c0503208181130880004003444420f074032003604c0d03410100b034062318500a1010f44001380b0700121003500019100040d803110219080302c610100c91000c1e0507505151081e80001c00001c402400c4945d00d08040c01d2450201009129903031605040405041540d4818020b41e85944010301c0d032400d4032204440c03100401c030202240c2c90f5040da42c5400c0028036540d01d4440c561a204040342c411400e1131000115824114014245042c0ea80441d14040001d400c80f000000c04484400005881c0d40030000100c0320703103075a940510750011880e12204541c0d1400e5218a00802c0325881d0350102c000d4801e41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 561923003 1250 561921753 561921797
    0xc041e03050703020d080405040903030501061806200a05060a0902040b060909390909280c0203043b19020d06240f02150703180c080d 59
    0xc01062038110900800c014100090b144040510582c0b80501341398542000c207084401000d02030300000d86a44c01040070a421880c01c0080002c10340c400848181401c00243c0030f42034146035001d1880500d148030841000620000c0402540207081d81c800d0b051401c40302015244400c4240e20451503d46541c42d43d19012044450b0860007612a001c04da03669892002e045182c0119100700740010b0105a41103441c21300059244100581c03525218000d1105006003254002c0c8101040d04103044c106d2102007115410200606800d036020a240b00c01d88000c0307007140120751107128002c6c5180c41c0c100b800d00801140c0c24464014203054442d002d046200003074091415030740001c0520f6600d240c0442807000750010507088042d440c000c06c2e45c0360380d5241d1200c01101656520380403e902c51065001c603900c0144203c0390f031281d200801c22199554080c88888401600490901d662900c02403485004044600e11098005120110507952107001c01d03141c80080c114070000900c5c21048400218107011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 561924253 1250 561923003 561923009
    0x307110d0201091e11040204120b06040209060712091e081c05090f01110d030905060702120a1d03070303030e210a0509030a14070e06010e0f0f060c060c041e 69
    0x104504d800000c90749070f6581541803001519000070000f8400710640340c9000500041c160102858a01c08460825411008000e80014451801000080c0d00fa5179402c06031006290003d920482c06034544070700340c45014495000461411188021000c080e0b940308802089070852420b0f98001d24101c0748010034007120801100101e40300744440c8209050216031120314180c181010202d011948070030324075080e080814040001d844c1c40060080000c10b01c0740a0b000340640c0014180400b41501040300b6000d4a400c020400002c0c040b01036420151405c035194400019050701c1d40301e42c4904006015010b00c4071054210700c40ca0356402c05401c52000c01b581c2e140c00600c012824540240c200b00d515070b105c04902a8188070340344480022034550302e9100c100c08421002400e86a20b0007210040a0f070004160754148070611094000c1e941340d81c0e65a0042c0d40049400080313441c00750780061100d0084800055042c400d060821480120840003801514000305403800c102042c403100301000c4035240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 561925503 1250 561924253 561924263
    0x504060b011119170c070906060207060908060106050d02070b070c060614030304030b07170a1506030507050306090403031e0b1203040f090c0c1a0604200f030415020307110d020109 79
    0x1000b40082441d03884005135008020400c3d6103040340a078480f40c50f0030074540161074555901c0c10200b0045804200c05401020ba07420813000301c1c0c0c5018000c607203600c0305210342424000d00062030901042158115800701e64484620600340c01d059400519003001d500b002c0761281c0c50128042800203030541020f8140c600140154038180c1036a0b039140c42810042d20000070b0001c0c0507006481d18158508491144800810001350030388610250200350f20341c0d6011000307141c40c0c50f09110403568080c0450340e1001d0181c0e04819203071940d160840c000d0501c8091514155090401c0c402500010f4201d01d820200440d201e0300c607000600700d415100e110314450411100907458042000000c0c6d504080300104940c1030030001c0d81241d0b100d0f24441411001c00b0b00042c05507608000301072620384564101460060425407490001d80840e107807600c5000c0f40c00c2600540030002604010f0401542d91500b14072203020341d01d0b8240300d10060400d400c552a803038540d00a100c410f8220510520075201259000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 561926753 1250 561925503 561925543
    0x60a0303030e0106090501181a0120070f140f090106081602010e060703050f0901050c0a03110f0408070f0b070b060904031205040804051309051b0d060504060b0111 72
    0x159909500a00c2c050645500c25520386600280508492203414001d10500311101380a1044500070001c6944070b19001c014070841042003600c80e68800003000740f0707115540d500c407411000c3c01074052602d0466400090b581c1015040400c11200f54070700c82003261801c0e0b41e41003601484208120841209014480008285100013003489413000c02c1d12246210ba4000094504043d510440c181301c004c0750301c01701080d2034101303000301c0c40380385281564440080c60007003005041c01403020000d40304000200f81016124061482451103132012074074654196041d40f6543c6507284441e5444a0300c9218482d128050881c0c00510000307013a003112001ca81c8403591001035a154810446000e034054800d0741044406141408140618800d0300c0c01640640041e83e1143d2410041201003515400603112540c10800054001200040c2030b90079104002c0000c9890f044000128646000526019054506100030300c020300c15960b00c1201100003e0384d603400c907940c41017006c1b42d451000b40207842505840c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 561928003 1250 561926753 561926759
    0x1b110c030303040224070803010323010e15090f190b0c1201050d1110020618150103260708130e0405100c02010f020a02150901150b03150a0905060a0509060a 69
    0x4034220245d0541c2614983c2400c24055850f9102d558100341c0003114007050038040045000c1100c1b03445409400000000c5c420129114440394031244410035070241c154442000c83c40c1c9034418084041b524444204807910314070483d9000240018205050702e00800c50b030045085041c0020807100d2980e0140705290482e442c04080c0403013518030310720644503030240c0301c1d03040b14a075210028040820a6070b80240080d04065514a0745000081442c900b00e9201d00e4004e080381c10030841080c11250090110791032079051000000c40708159000c00c80400d07500003010380c20400080d02900c0d2544910542ca00d2550b2076503580040c0741400c1c1d070041c0c81d5a00143c0400500803c982140d604007059100108803100224440426038111610702000768224241d4500003c0400c1c0010381c0c0546010024030002c1040c42c0d0303409007044503014001050b00004005260300071064841e03141d044025110a41142ea2900c4100003403070103803071940c41461400c00001e903500e0039050707650080000038003000a482c9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 561929253 1250 561928003 561928039
    0xd170709080a140c0a03031d030c0f01080a1104152309090a2702040f15060c03111c031b0206070c0219080c150c0c131b110c0303030402 60
    0x3c10071220181e1041c04500c0c8116110201144019882600d070740104042940304050749407440640240070350302804900c0307620760f0703048020a412070080c01e000d41c0603150703080964080d0100d002c101c51034420020740020107103208060310010081c1c542d40d18440076030192202c13080700c070207200e100c030f40510170310821446240c013031082504050004800100e4210030f03228030100c1e04403008070918182c0807080da02c4c15400d050003050700d4509040010462102c007205040801c1126004400c1040a8006e81404050081440001c1d9034000030841d285100d02010189034941c06001403000079080c10383c1a401c058645400c0c51118040e500640441d949002080ba02c6a2050400ba6800424a00c015070400c40e00c10007403000e030441001810040c46580c05004030101c0e81d481c82c0030202000c21a017040d210b40030860001141040b1418065907041094032800b070003054142900c102c00e044003100c7c3e4281c100107980c44c1d920381102036804081926007051b881e4001201c2c040e401030081510000d03021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 561930503 1250 561929253 561929273
    0x21c0203070b070519030e10141302060409050c0406090e040f11060418051f0e010513090b0a0e07091406040921020a0b0a06060c230d170709080a 64
    0x20000345003460a01541c510b85045258080c00d8030740103c0d82d12204100307c01ca0500521242150490081c400507080003a00046910004c000300340b0540c00b01303505001c40da200c801300d40080801c00d0080c0301c142411400c5a00660080c0f0402001c00d410201c0080c2408007001013900c1590801d010368400c003250303110b028110300745140301640441c0c00c00c4007003010100d0482d81c5090b014040b80014407450400b1000e950790020040d4040c15600542d000c000070303003031041c00c2410b450003500e200d2244c0460f481c0b6040076000f031890042440c014541004000720700c0b81d110a006201c43e200301d442a035640c000702c00c11643d4441d204001d0007014000102181003640003044851301c10019a10070640d01d0b11200342c801074a9803c0c00051b041152030205024031492035507007020b012201007180340d242ca0f101500760f1160000040032400c0034a06103010518140c940b9504001344802c3c1d076a03c50446000070825032822454425115400011038220762082d0014030640320340d04024984500d050f140e2030303140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 561931753 1250 561930503 561930511
    0x60106113304060608070308071a01210602070605010b0315010f0c06093329101e02070303180521012405030c0409111306030203010603030e01021c0203070b 69
    0x81e03220b80d000905d0b0b200070400440190300030900310751a01c0c2180790803207190150041112940e5155001402101c0103503002c403c070141d003001c40310800c01341803500102a0241c154040d00192601d400042d141000200440c0301c1c0400300c030402c01001005005440b41d4030184c0280c0d0014002d282e42400007074a55215102d00b5000d41e441201c441014030b0300440b0401c0343c3c0308078810044017040003d20001d6a0003000e000402001c4c03c1415404240901040411401c0c50648905800120ba20090b03000300342c0062181e500b080b498a002d1101c08000c0d40e0b4102340d100440008030413404c040d80c00b05d170000e01d40c4c0c183c40300100100c080d8031001c0800082c0c1800c2040c90899956118003081c010485100030420148000307802c2028286800c04050810105100050155090000c0100021550824103600910482e9032510114600001500605054000a40545c80c0000200c20705030010300020818a01b41e08641a02d8007821200b10303403011041c0c60344c0142e07109204207400110118181680 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 561933003 1250 561931753 561931763
    0x70e1305100615020c2d030f012a0806010804060203270d090f0308031b0c0d080402100221031003060e03031f030302070e07030207050d120f0b060702120f060106113304 74
    0x840c0d10301001003400c4030b20b2b00340c850700318942c161b140c4910b548150008001c0c4100500f0000524540900080c0000b030004000402c02540000000c0720003000107052001100c13200890f00b040c408800c0da842d6541d65814001022410322400010601c2d00d0b00e8411064135032110362182503842d2015940a80d4135005800a040c490a120390307010100c0c1040120741c00007503607840c0001401c050040c860480c002030210740444d00101406048440c0c40d0304585500201c00c500e03260340382d55031108440051000c1d00028040d0b810503858002600c0d001000e140120810300004006417101c0a00c407000304c0e070b81c0c407000b00507030420602040703207100c00308078a58011038505001d843c00c420790b82e078182001c2c0c05110220100303801032130300441103040b48607850074204203050401c81106800005103a900a19600174843e944908029292441c24401a0b0010400304103d4105585818000c1d100714444462891140b18600c00f218001049248407000029403215001420740310b4030701c050803540b0080c0700b50b503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 561934253 1250 561933003 561933013
    0x2060705030f0706061d06100f1e090e010803090d03030c09050d0b0403080c090f090603100507081f0e04060905010b090a0903020708070e1305100615020c2d03 70
    0x10541c0010041503d03900c103002c00124982090001c20300f8155121900d42038000c3d510400086440f18440d09a10100380d0030502480350071900203c0d19003103882d03002034250700398050800316039401510b5074082d1041d08504140f280e80b60540103580b4000d448585e81e2008940c442c0d200828040d034440c1901c81c105107000213246440380089405c015540c8000c0350720107000d80410041c16480203a05400899a070f095514007400d0780000381d0721101c03507401c05100e10192004190903076403c100004591602c92018400c901d06400050400da108540d440b81e0603510541980441000c1100c01058031a9444010246d0311a511158000c051012003220290341c0e03101c0d030714980c1e41e80100c140d10540c840200458007207068540241420666440036085d984041400e100a10701d044046a005128540303880b0340306881e007402c6107800728036100701100d14640340001c1444048603a800a02c86216000c0310090789000081c04080d0301d11005041000348a00c940c42c0841d65441d8004000341c4004013111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 561935503 1250 561934253 561934267
    0x50a080d2a09170a021e0102011a0901050f0d0b04051c030203010b0406030519090c17030304080f031f030809100518060c030f220f03030206040f14150a18050a0206070503 75
    0xe0086c001c1ba0082c0003841840718482074103680c240112003e02488400c030400b20001c99010803c040010b0103001d04c940703200440180135440c0c04411041c41c0b500450503100b2070a003420402e480369020501c0d10418a041840c0051540c001d0003124100d85242c4070441c5050302c2c0c010118010900504112041c5504400c88050341015000d81c88005002c1c804251195182c40700d020340b41c0c219090300c00c403550014000c10012580c29400d45a0300040e0840c0c40d42d0700d07504c0740040c3c0c1c10001140d41c05842506410340c08410302500d003025000d503020680e484111035503440340c25101e502070064010705121403e070102c2a54145007001d8104211080200c90030082060881038558110320080c80381869415a144545044002e41000070400748110415050a6440003516248020005040014482038450421070200150814808000c054909006800880011044055030181c2a10781441640303040c42028204c40031010f94040002c1c0341d02d00d001e0382031054940045100f502c1c2070106024030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 561936753 1250 561935503 561935509
    0x60f030a2a0b0c011a0319020904020a0f06020606010305070c23070b040602060406061208030c032505030609070206090c1306090207050f0105150a0909050a080d2a09170a02 76
    0x141085031042000420b04080c2010a0031704202c00a1007039100b0391121038042ca5600031140107003503594040d10050415521400800c0002101d0b510043c003032072072100b0005800e80e010072580d000d0a001d030b800744101c0e1140310044900360428540503010355400003001c500340b4446400c0110860000303007540e00c4030b99034007004c108030341007030341b0010268101e0340130401000039178030440e0040c16811002d002e000055440c1d030040e60100801340c0b40b101c4800000320f1401070070401042e4015040a0306030703c1c51191a03a00405a400a440c5070340240c86000c04200c0c0103001182d100d00c80c2120314001c100d105c18100401182d40040c074984641c0e141d44240102e01002180010007189014000814070200d01c0c4465508403500180304c240001e9410790207003003580c0d502003204200c0d02d0611022840c45414281303241041e81d80080180441c1d00000c50403640e00440d041000000c00d18550203c02010707610514410070808628240018108001403140d140010390455203240600104c9a21074106c0e408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 561938003 1250 561936753 561936757
    0x60f04150303020609010608030307180905042a080d03110910080603070927030e0429040203090a0201050309150406091707032a020402070803060f030a2a0b 69
    0x2414900030604003401407507010400503802042140c001c01800d4503241507036442e408090081801c104002d4407107840103e075030400c0d001070856a81e08110031708103841d0091801e4008003010f18480e09140394005d0301c0d952100c1031000c0300c0c001d0000d0040d4040c0203030f04400805510508000c00c500500490340305498a0f17440302c080c50100d071542d59032420244e080600d80b00c210b81c0304c2107606040000380408400d42203102507502089511599004541d131800391480076114291076040317480c00100c107602604000d0f1030281c1410819181e05040200c1017072206902c4100c0d140c40176940182d481c078005501c560021a801020b0805607907054400780040186120299819101d803501c0c0e40c805000d000404c0042114000d62071407003803a003000ca5a020f0084440b81f480e030141c0000001e040d2000ea50b41d50074400009074000c01c215a03801c080d2508031420741041d14814003d84168080310500c4c200011451603068200b034960b8085c10201412400ea0b0000c0f8850040940c12180006003a40c54240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 561939253 1250 561938003 561938021
    0xa060603020c0a0213111b1e070e040f080c100c0e1e0a03050d050306030d1706041d012d0c080406090312020d020a0e03060105011d0f15041d040812060f04 68
    0x1c1c100c9511100315021f1450800c100c919442c550001d8483d00308134440009815007200c180d4106110113980780d00344204102c4c0c103004c001c0c01203000014030309440100807501000ca102500005c100a005840e070031155911a9850941c0000310444090210302040c01ca2600b84d44004000c0851680c81e07036942800c1804d0112401c001c94008414001c003803606104400885603280b809504030440031a10b03020189001c0c2045000d141d841c00d030203d01d4180120304a000c158144000e00c01c481142e542511417591001c1c9c1101904000c00c111613410b02c0b1801080483d50a07a130341c00d000d40e00c82d500c428000b0002d44004409001c0c003035481a1201884e80042c1000024613040140c82d040d0103038020b00480c08000b401c1d0704c66003140c0b0041c0a00ea801480c0d00840000348071507680c01081000118001081c140c0320142d2124507045550f2220901e80000d000340d941c441199520108820fa82c80704440301030340c3c0180f0348101441282a42c42e1244134580d40404e00804402c05034400d000420101c6010310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 561940503 1250 561939253 561939277
    0xb09030a0c06020604110d02010804080702040b040c09030605010803040605040b160605040312051b0a05091801170f03160b1314010219080c04050f0a0902040e0a060603020c0a021311 80
    0x84c080005201141900c25420002520300c0d01c204496640002e042c0c60700100010101540444c07000c0540d1540d501115110501070410881203a1520b400b038640c0020788801c9074224103080c0080b940070b4010054900300e03183c1c0d44415040c1070618450307082581090440c10141401d0003000700c0070440a00441d40514041d442e14850341c9082c035000c030180e650080c403c80150b9103080011080401c00c42c00c0703c2181d40b40d0b00c0e2294a4200c0840011140c4030b0b1010700180c006581000810010b80280300d010031520060700b00c80c000300e65681031588900985901c0e00700a01c0d24448800402d03440300c0150742c445216032144007004125541c4407440c507801c5200c400607070741c082141000380e840309110032520301450034121141d2500c402c141203184038500942c0d014405c421540c40c00d648805d46168068854000300f0b5403501c1c2c580c210130014400458441c0001c905002c00060b5030350103442228820540e02c0d018040d942c3c155002d100042c88001d052020403580c8a1107024175a07100405882e140102e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 561941753 1250 561940503 561940513
    0xe2d011b11030901020d030b04020c0105160806010912170c03071214040e130602040503031b06010b121b092d09091e120301030f0314130b09030a0c0602 67
    0x5000c018089a0168050780d5030360701c100002c40c51680c00040c5203020100a10b40841d0704100c01c03011501a00904000c0720b029820b080074000c240416810b080410002070360f5902c0c880d90340c81700464040005104004000b45034800c0540890302d00c90705220400010342c0b0451910f881c80c4096071441d8401601915000103900701c0c00d50450744a18003d40503c81c4208445c01d21381440700d00082140c0c054090458400c15441d070300104085501958000c09006040d20740325060916002002c5910007043c440a00130300c2c0000c610034005038107840000c94221030381606541e92010080b110640545030011502c01401601020b5503081542c04500301920020701d42e10b40c540c0c0e40712213400355403501c451280c04880100501410b000803012810030400c000800117210000d2018107014003404900c4150074000004418007140001ea0702c0c005100c0d9640042c400000400302102c0e0007410300a00000745980c10811101801d00050300300d04600405950300d41c0c08503038030310355280010b5021001507000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 561943003 1250 561941753 561941801
    0xb062106061503060303040902070609082d0301060c0b0a06031e0303110a02210702130c0e0904020303190e06031f090908030f0703020c07030c090c030e2d01 69
    0x22103500705070324036002d03940c05046040500020341c0b00d005900881803443e502180e440148201508550410364104100a6942c5050803080f6411003402907032900721701c900e0b00107140c400d01050899040703600d03554030150703a00c0c01aa01e1800c01c000240210700120b4440c1c0380400420140700c160206030140075000c0442003407500d00a016500001032140b1a55018088400d00c550042a00186981c44c1e51942501c02020043c1481500030640701a4000c89607154203403042e03079a6480400c550240c1c3e1181d071022140f041c2001039048040780c0c001d415800501840c2c00010b2600f0f40341042194a04048424103840e501082c06074004a440d5428511902c3c4403041d2400ea9028140141002e05018002818141c032181003a1002070030b02441400c40b038000036007440c4240d0688400020314429111720603584e0a04c11a800c400e40103040103a49040b80c40d41020b8020302c6075015801d140f00c090018540f070080034901a026511103840e6244811544c036460000c01c0c03007100000f8490940512500314 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 561944253 1250 561943003 561943009
    0x10f1d0c0306090606010f05160305090406081b06030601030204080a050706110601080703080f0408010c030606021b030c060c2415060a08060909011b0207230105070b06210606 77
    0xc0100c11070103900b21600303003d8050004030300d050344200203003403617900b020303211038111350506c1f81c0e00444102d030307001c0c7c000d0404065100307008102c05c040440e0248144c603220146a9103a250001030701c40c0c09984103803620854100072005c0c41d03112005040041c01d180d5150106410035134500401c840542004506000507604001030030451104480100015030400c0c0c80d4940c0c80d421800050325080d4007050504550600d0f008a4010303007003e500a0280551540010300a807640d4000d01c00507000301155032681d00440d02e0150100d480c01002840300030220014000c07681d101c0b0082d02c005005119202e0001d4101c5500703040305c02000020f80d0380500d409041c00c0e13107034640c07072038814401c01c8100f2a1803041d40e03101003040d8000070111840d40003070b140d05504070700404500400761825481c42c036010300004c1e0041480c000f10340c1c100d175241c8000491101703007810300da191540443c040359050001c0030114803460900c40c0e2104014040d08141b00c0512010150000111140300d4164801c0c800c200c0b01e82 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 561945503 1250 561944253 561944263
    0x10b04030213020c210316020c01090501180b13092019020a050106060905011e05030f0a0204030f06060306380315010e16080103030f030509010f1d 65
    0x1040500406050904590000c0d05515403988451842034002c5031320500c0020502c40031704007582da41c0e540c0f40c08400d117008000654108403080d06c400c0c004c2e161000c900754004036050045060503551001c9060420005482c0c8411601000c61000d0b41c0302400724036404100001c0c03041c10041050851a00d103803860030130581d03003400c2c0c0c01c52400d40c5020450a1090112003514070803a48010302905410b50a1004c91409204da007001c6e01c0741d8201503002641541220522054420030f0380e800c04900401d49801902c07003407514001c0001101003002990b094885042203410100c000409171406a807501e0324a038689480c82c0585103195260805c0040000c18410b255001030710301607044522000e85280a00d4220341d59030b4a11910548003128015901405000c106201180710030305596101c0c40102c00d801ea00f00c3e07200f81d50f4081c0006400005024900345c81c1200c1c1d065884141900f01c2000885c05010082c0c0f1043c401e40d02c40400032100034071402040e179240201c00300760740341c460b043e50560301d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 561946753 1250 561945503 561945509
    0xc010204090f06051c031d030a061121010509010308030903070501141e0609010312170406090308010611030f0a0e06072d05100504030207050a0f0302011206150c05011503060f0501 79
    0x2990f00035105c40c0000c1e00f1561085801000c0040038001c40c070004042410400f10785402000305191850120070b00a00c2405000b5285010300e00580ca508a0656116403031030038020507501030002d200410020724480000d5038011046070a4070b040840d9035070f0381800d4801204202180d9800b0004104244800da04501c4030401102c4004004e800c2c038002050f80518103000180003489080c49450409000d0128004403222145d9000c140e45000c0c05e000005144111040340010112800022158030403149001b5079060320004c1d51400d24000c10690303003580240d4901d01400b40050000d082d0f84e03242c1c4058036110b40501c100324615000015a41d01c801c0d801c64035a0740341c00b107640160b004a480040c0c2582440e504000014051f111414103a1074002d440d409186e200b601410045082c44280c01070104aa10130307254140030742005501d4406441d818090700307000701d400c201080806440340e031891136554002e0780005002c040c500850140c103d1a60130036202180c6542d41c10058604034400c041c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 561948003 1250 561946753 561946789
    0xe0712060c0302030c091e0d0501050f0c070c0e1f1508010f06092105030c030d0c02060f040813030b090703051506010206191104180f1406060c010204090f0605 70
    0x514984a440c944446c001c0360000c90003100610b41c900000c01c40500b611070400d400810940b10400302d0324140313010300340c100d91800c1e20080d01808250320362241d400b92203042e50308c1404800c1882c1000000e2010360b07070080100c00401c02c040510848a07110344180703800b42c0810008015080f042c11800f400e40d250607840303c0d042d400780c50001c00007107034440c041d030050315010b500e40700c03851030301200110011031083c0002d802400005805c0340c5440d0000001c01c0403c440358410b11140c1ea202d03e050b40c482200325800010502e110001900103000400103054400800c04856a241c0c1c5030384480c0d203810f404031140d6140c1c3d0b00120050080c04000c009111112084d804282c0040c0b40c4034000075100d440c054616203c075030211940040000f42038009140d001b107004055529542c1e02d100c0ca031040008050b00d8400c143c5450200c140c06581d81c098004091601d088044190300d0302401e22500d603010180c070304100d550030301020400c15500c0c0a400790f442e8100f10301140c1242044c04219510300814580c0b50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 561949253 1250 561948003 561948007
    0x6051e06030d021f0207211b08030412030f0c211505040504050307050609030304032d0f09050415050a080607120b0a03080706150801020a05120702010e0712060c0302 73
    0x5940d0343c0041d590001c000a040e03800401e41340e035050f0101a01400c03200900710301001c02880182d8010091009140301e1036035501c460040d08044600701404044405040e00004000250204a8410b088039182c2500d140010f4424a000301ba10308507075410001100056848220490018044c3c2c0f1102005541190030050303445420703c01c0281c41d0b5188142030240d030300d07100000d050100074805d4a01007034014007615881e02e424041c50342c03030394003c481c01c4002c00e0350b0030480b11050510648901070500307040c04a49041a03240002d403401b200306440e800411039a02d40206250706d83d401030000c40020302107844421428841000526010350b04140345076441902040a0359034032003612070b046100c58500081881840000c00c001818540020b001d42c100050300b141004260790240c03600b4007245984060658440d01c0050a0b48907103440c00001030002d0094650a086840305203030016014000000c01a042c3c418a5007003011a600c14401803050500010a02c640f42c01420492511403400318 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 561950503 1250 561949253 561949273
    0x5090a0608070b09031c021204080106180606050d110408010f020c0c04020a080c0306190608060a080601050d110d0609050f01050601030c120903030e060a1d01090201140a020a06051e0603 82
    0x1a0b84c422514185030709100c01d8070b0711000018024031083d9944110522003927600c07610382c04064068800f030700c1100021180c41480c1e088014003032042d0f2050b118107540b0340b40340000b13004600c000780002da1140c5003180010800080d26080034452243d42486001303015898034200e070003150420090b942e686003d1401080090f24040c0e00104855000e80b41104040d1070f0f44441000c604000d40440d107820302e0762103024021803402d41145140d807290004444001140741c440c030030151a08030038070030340b6081300d0740011483c000703100c103068284000d401802100c8000c030340d40c489005030748081c1c40a941039044844107203003400d020700466a00900a0800748910302602c0801404160048458464140d54a0003441010b1103608001110442401100c100d414080790404c010400944200315003400344c82d500fa401070044c05100f8400d501612104990034821501700d9482d0b00540c01071085002e07010318a00000c0749845030600410000d00350300d642c81c0ba0703840c521220703c80c09099a4440d81c0810100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 561951753 1250 561950503 561950509
    0xc0917010e0615060319020705060a061514091e040c0302040501140405030c100219080a0201061a0901031e02040609030c12050c06160c17011107050c010302070c05090a0608070b09 79
    0x50350000100b000c6200c0503854441031b000240030382c00e002801c6005000a0043d20f0001e03030000c00c20707598403c24100f0170301020041a42c14008489041c449143c0511460103075242060b000105100ca001030b120710300c80150000b4048410031100d03031010a6000c102801103503031040d0700c40c1c80344050703210081c906810440041c0d07131410880d4044e4428840d0344190420944248124003040002d24412805115203250140440e0894040b0100540c6810000103214110000c0740d0728900d5003403111454004a01c1c011405040c1c41c0c19034111400300303a09180701c02c0107203100030001401c455458040030ba0440ca049603424042e81e004000780180c0700c042ea400b00e07d0100301e10b52011f03411202940c0e00c1e40c0c98200079032010640c10000d012003903c0c0000188015011146c002c400800500800c00310040240c019041d024860015181c0da01c800611880d13075000b41d0092880c0b90040000781c04659a4400295052002b12503000100307403122400c0000300400c110388000741c0940013186003825510404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 561953003 1250 561951753 561951757
    0x5060f090d1a0712050c160f0807200a060305060306070c05010e030408100501060912170d1805060105030102041a180d0320030405010903060c0917010e061506 70
    0x20107200e812107401070340c20041481c406241121240ca081c600a1034074410190980c1d008221042001c1e0500f00010320007610350044456a802d10b46141284410030780f6420501c295204089456050030000d1b0800b1035003070909954030000000d03030078032a0300c003000070322841103c141d1150040c5030809051050f159004107010343c0c018542c1c54084015455810652302600b4580d048003440c1c040002e010030300c1100480d11501c203194001c030038042c59a0700c61041b035071680b1910803060401c003901849400a101174110480301210f0030125401c1038602c4060361300321540e4a81b50401344210b070600c2000c0120034009180106002c42c000c41c2418907003500354100c5605001c0c2030030003550025003660310750700703440c818811103402601c050b2400705680f8007d031032100300c2d140590300f11000c02c00d501c04140d400011903050390010396030300c036095185070f41e518050035425034540c050011008000c55440c41203a004d0008400401c004111407802d41c0009080c4500a001d00640c001803613603d031986e480d0326007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 561954253 1250 561953003 561953017
    0x12141317100606200c0603010312030207062c0714010e0103060812091309110d0203011404060c1103090a140d17130501020105060109090b1c05070f05060f 68
    0xca034820400d9404850305041c0780c2000d20450515242002c030350f840c1e00075241512208a41e030b141c6100441840c503c0e030750b000c94040d0a0f42c0404200014000a0302c07030b0001c0301c05c5100c00c0c20f0150502c18076a03140e400340d60340141c4e4811b400001e001c0252900040c40b6a032500c5186000203001c00380c1c100303400320741d1880c01c560010707040c4840c0c150066a0399100b0340c082c1c1c00030102c0605941a40d1024844d10840d51310103a02c051289902601c4c841c02d640a51040d090742940c0102c8041c41241c1c2a028006880203074642648e040d50703110b180c0c80fa6210816949413140344140d0001407480605080a8580c044001403900a13902c2445040d126407960031181003a02c154030150078070700000d04005a8146d284800041034040a000182081000d4070082d003901c0714661410b0302020344a0b0012404c0f80d804844050000b209080301300807046007503002000c04000a003400341d500d030b10701500350403010b42594100c50315480b558082103000c8269108101410084408a26010f880030f03044c201401050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 561955503 1250 561954253 561954269
    0x92a03071403031317010c050310050f04091a101202151b03040303110105070503040f12120c05030f25050a030204050d03030f051807090902060c0a121413 68
    0x6001005650108196150700b0001440b902c80941c076544d038449400010001703c130719903080a0366012690f00603000d49105020544400706454034010412070b01688001d849500141e540260b5400324401d5a030090211402c664942054108004400b455203125403080010520031030390000103954001c3e100c00c882c0d001c19030140c0c49000c0c0e48a641810306071010070300325034030000400004240d005440418030405250003000950741c0c25406032070b00d00c4126002040e12201c801c3e40300c0000c04e01c10341c03400d0b12541ca10703007103009a0003055200200c03050307010a0b0011442c040200001e266124010650100c420a02909905400140c20400c0307002d240c500e005102d000b0400480c1544681d041e600108001045000a00d0541c18050b0003012070110462001c0d0501c4006090508070a0261410020b40c0b40101034442c50300081d40c008103941c000403a40a00301300409410190100329100e95580501648448141c003250054006464900c2500c0c40040c24405981100b240030340040482c3d140d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 561956753 1250 561955503 561955529
    0x201150816120809100c05160f05060d0906061202030610060203030705030901090b0c0a080a0c0f0507080418020309070e0606120702030d0509060a0c02010e030d2003092a0307 77
    0x514120f034160242e1418640c04c084200049110558001d03480d40340140540152011951844650f140c1044140140d10314101a00c50401c406d090210043c522507004800002c0c607102c050b40d505055403030700d5002c4d000d0322600102c1c48095107001d0145580000d00030755041000c81c81c040d00607441e804020503050502c41c02000192001600390020240c1070f500c1105000e5500c3d04148081440d00f10b5401ea200084038100000c4241265102d689001e0800307031910072031003e80100031101507018000031a803807441440b0020b0007100800c0b01801030b000d140782c0035880e498a800d00074503140855104050512030403043c0140d64555078126507440381500c0a800c4207540d4050281d1031841884810307030b00c1314907100410808141c04141d00b40521004a02482804072040c1e00300e083c4c0d580c04042418940003004001100c4209511141c1c507019205151001144241181c45898100b00c6a410071a005826600320403401d503417200001c480d5046080300c580005001103039544840b8000c5002c500030f5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 561958003 1250 561956753 561956789
    0x140403031d0f01020703110613080310050402030c040608130b0604020a0314040f12090e16030b030f0105060306011a09040b041107031806050c2a0402030103030201150816 75
    0x100319480040d015411080300e0000816066983c000d5101c4030041d8006560846a14181e00d004202e1600843c507403c900c140303002c11038852104685c40640081021199644001080d8540d0f0025510801002441c2d43d1120710b0440c5c003903d50503000340b035030003a06011403d50b40010300c4010001d8104100b5600183c03644001d19054000b08014564002010081c40400c002c00a40403840c0d50500e200d200300701d8400103490301c29520340b805801a0390360000e8090008400340e44081814066000074503012800540d20400310713090a0107036107081c03126511f401c00c200441c00c040007441d004003c820046802c150795400e01569034043e900c5441e226039103d9030010915a02e035048aa4410f90a8002968030b884a14001c0c143e0703d410040c0d8080503125090008406000794140c84c0e4090a440c050a402905180b030f802c200075085a0f01302d24411000342c10b1500d522103102540c007862080d0000991030301454084084110280c3c040f0307215501c4044000790b903110f1400158203c0e048a605030550000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 561959253 1250 561958003 561958031
    0x30d0e0c150903010f0e0d030902150408100e060402010903080c120f04050f100c030c050709020301060302031f0f0902160506040b01030b1312050a02010f1109030f0114040303 77
    0x8248498603030140e8035110a800d210414001805402d030220000c200784074045207260b050340d420784480200381d000a1090214140650498904544000c11036040c40e05240d00d5865260043c0e084103030b482d480058090303002c0b00765210320300344544018002c200701d03d4290700081401030b181c00020414400414002c48015081160015186000203020b4030b0f030105c038220000c240c0080c49120b1244840040c0d038995410442e030641104100b55440809003107098406586103040400f04494511030ba8400240c11035052002e180a40040c1d5005030707a90500001009581d141ea100d90307080c0d0007040500300300300d504c0d039a02c0070304484450801585480e00160001c00348107402c0c102074810b00075041000100600641d00c079050720311a15074450552074034031525004483c07071b040081441440f070380c501110341e0180700a002108546d100100e00d14155000d0751082d80e11508054a846901080040e0035140900034010a0901c01000700802c8007003030707010302140001a2015041c950b8440019000e40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 561960503 1250 561959253 561959263
    0x61223011a0307050103060b0306090402060f160606150f110304030206070b060301200702131d0604020909010c080115030b22060b0702090403080a06080d11010617030d0e 75
    0x145118000c101940e20541c01c0c19645000a800d24400c0c0a51400440d196000f0700c240340945025071002801c5580d80310600c5000a0003900982c0d210900b8050b40c1041a1000b0040240e03a02416260042c48800d14010741500d12a40101060840240c03081002650001c0450b2240c2201d14108000c01ca070364084609520894001a40100001030200f0a01c20204241c1e40210415802040090009400c2120341401148050060b0f0700801c407600140c0740540030109032500030500041c1c0394180f100d94031240c03070381c142d02c07900d16412400420040d840c05551055202088400a000a1804c1d140041881c0e605000b1b100c0c03c4a0701e280003110892203076001107088000075002c904a0441002017400c518008444030450b98240580482e645000c8420754035640e5001c0c0180714107807540e03138080e1640c8200a10300d1900980d43d06002841080030480c4c5140c01c80c441c0c888401c030385951301400c1c1c2520103542048500001d0204030007100344001003241c2440040b4880050240c69800d580741c280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 561961753 1250 561960503 561960563
    0x60e0103110d11060732030d0c092103021002031003170702042c01090b0402090a0f0213030506060405010e070f020a0501020a0305061903150207111314010602010612 73
    0x80000800c45c0b03c104009090300a5003101d0300700300160401800440c07414410520386c00f000380764009002c14144880e06030419102c4c60390600344800c50035100c25500004203030120180807011000c00041c030501d501408001000d0081c19000d614618040025001402d0184001804041510341315840c003030b5984141d031081d0341d000340181b101110fa142e09007138400f55035402c0c9101048006c1c582c9107051051060102c800c2c0c0c005c3d0200300382c4c2c1e900d400700220304000411950a450300c85444544804591008002c0c5890041034546a182181056450f1040c0182050b0243d407408005000c184d4100d10241e40c41042c900d004520780412040480c103102240d48010001e60011500c8140c2d1501904203034455801902d088040f050858101c18101c2000d10018100c04140c0030800e040d110a40c00030302d03105000342042d2001000840214001004081d1074105440e507500c2c2000c48440061072203401440e4a03c024002c1d141454101c006448031044001c1400e121501c03001400c0911105140807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 561963003 1250 561961753 561961759
    0xa030c080f071b05010e03120414030c0604080901030902040e03040906050402160609140316030807030903140a020a0c0306020702090906070203090f131802090c0a1d0d050a1104060e0103110d11 85
    0x442030701d9001c45185600c2520300b2030b4682c1111030030ac01d68100c00401c2e610305910072001410b4580750798888280650081001c1070415840e1036944016849501807030762404007500080d80e84510b81750881045074000d030003240c440c43c01040000782181c004812181c4846d00444002010281458a07a25134800000d044800b80800303c0d2110031000c01d0548100158007903240c0c04030665500d0320407400c030341c071440340100451420303100f14100343c1e507a6026101e2212a8012909500e01d50b85907100a0740320f950044511a400082e00421400c0503086140c22254041c004c00c0907040448019440c0d014285800d0701030b42e0702040070406599400d413102c641944000c801c10007407485440c00608010031043c142e002d52482d4002c04c91901903503044840c119841d550b60b606032640e4800344032140804004035507011003100c41e03c90201c2e000744141c8003076510499a80181000e040207220a40f10594032007440a80510010000f0400b000b41d100d01140d400c82d84070100440c43e2400b20303032114180516a030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 561964253 1250 561963003 561963007
    0x6071203020714060f0a05090a0308070e04060e060307120f06150e04210f230d020a0801060f0203160204021b1009021f02030406050c10020a030c080f071b05010e03 72
    0x14201c0c001050680c002c00c05a01c01c5c0c04590784028580c81580c0040d00c0010203940400c41180120303105007044e54000300d0502e0111308440900340040c040d101c86030801c4c10705071150014041c451600300300d00e00080c4103050262007924030540321150207801517400900066103030f200d881410130b8119034010103081a803441c0301282c01e060908071049070762000c0c001d010440100082800a0040c04040900c2c4038640c0d4660880700101c1d810158190001c06909841c4418031480d180030445001801c519100350380e80b40100d624204c4010f101d0b0b484551000306640040020404882850b041d500354a50180c40150b680c690303884c1c1d10794030641017078528a0a40500355420003c48034030342246050764001c44030f0340b0b0720044c000c1e4081646015103004401590080104202c0d290080c80607042814510040da400916010350320f0042c0d0703018510000000c0e07610b0f004981440d0b0840c00294200c0403510f00340c04e00e403601e6800500311964240c2c030880f2944821200004003e0250085000e00c40c210042d01c0e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 561965503 1250 561964253 561964283
    0x706050c010b2d0405040b010b070203010207060c0c030207090c0503010b0903030909040501020d11120a090206070b090319031e2d0e070e04080f130305062e05060712030207 76
    0x1c0c1c80b40060506010aa55090050f801d540b41901549000340c0e044184190241d10701480440c1942c081d601c1241c155409011000204000d84501c801021312500c6d05101c28800d072030000d0826119030020440f031407824071850640d90b0b00030107407030540c2c0d901ca81050b030b2919200006861401441c81b026480044141040100701e010340160600e43c05c815018081499401000d0701d603406010844664411230b200082c10070100e03034000541e0540080d0149103800102c0c1c035082904142110b0300801603000080d182ca82d1030f00d07000201e100c800135103010049034611118003501e07403007000b02000034035444403504540301032100b960300d00d07225041c0b0a05030869002c0300150302030710051494240b03e0207040c40014000d251400c069104a81c0001031601d04501c0c0c000b0040683c01c48480d21448041020300880098402c11003240039284c2450046404001e00d0781130444041c8220302d01e03007400e01d100360800894071101c00ba1186540d01035038200c1c0203188490210f0080c00303920005485802070348020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 561966753 1250 561965503 561965539
    0x7050f070f080102161205040302061303020f0a121202070906060306080f0c091f0e0103051b031924050106090e100320030c130c030e0a02030706050c010b 68
    0x960200c4640071200001590b480541e10708034040c490101d855028200d0380300000a0b81420f4031101110542000c500b415184c0d004104076400882c0103203d01d02c004041402035140c0b00410318114503048942c1710100d428a1a110607100c40040010100268007a6607540d46d402407020314050280094204072044e61858014040c020912420300940120441645464004200309040117806401100b16498002110111268604443d05c03070304c59001010449803017a050382e81c001c1d401a801410f4116180100b09034000d06141614440c2d40304464812400c0c040c00840b0307001c0d40d00038403011070810904000012403c8094088400c0034507103400440c801350072442440545100c0c00703005840d039580030f0340907401c0050781c04007812407400e00b40741e8219400c1c02443e03d8041d44001c1c00303440505c1c040e000840c1000d0450411030292030b480d400700b04000e50380b40c0b04451071119100d00074000b03d030841e00400d89a01403406110104040010302616000007500001015040540580d02c91440884a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 561968003 1250 561966753 561966763
    0x10b0603151f02150c090d060501090e0601030c060e0301091a07020f0706080103150209040903110c2e021e07060f030218090703060e0411010e060705100b0607050f 72
    0x5640c1c40b840000c00d201040c800031050806850001e50010b003c03503900c0b801840c020040042441c1a1000c0c1003040341007540365403441506042c070500d004641c075410b00c0d01c400142e5a0ac00351640d0725611640041020458001841c021034a0900341346c000d03c80c10a000c41c0c05800540d201402031503030852140414420080218880c200c50b5017500c040f03070340500072940c403505288a0b80c2c0020305600018400b180c80010341203000d005061005251242580116054440044054010801d090100000780c07400b444043d0140004070b80e0401403007400040c00d08660499254480f101c0300704521140c0050007000103442ca80014618030941e8041052119940c0106025160010f107c400c1c0f4042c0b2680240241c452000d400d0186507003850b890000e01180f0ba00041c582801c05807240b40004440050f0034030b031030007940140340c03a900d030440140000d0201038003c1d01e040d000e85000c0211a001c60070218885090051001022030051082000a101401180c6014182d8083c0d4040c1c0244244e000a03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 561969253 1250 561968003 561968041
    0x91201060f0e24010e04020705060a06030215070b01090504080c12030406150843050f0a0b03130c031203020d06050a05061e13080a0b060409080a0809010b0603 70
    0x70b590801a41e600000888030032512071040040100443c1c96000ea41c000c80381d50781d280b81d001d0001400c0204540b04c0a1410f4004d0b90340c070b5043d550390343c814419410b1081081d00d8088040b501a13290625580e103080a15405115520901d903860020a04107c110000c0390304c000003182c1111040010500801c1041d44240e8040703403098a00403070221030700d006001c00700441e19000c0180c50011260500310f2540079101ca50700184200d41c01c840100c0a451502114010201240c55505117043c8001c3c0159000c07440d8450740310707440880080058401d068102c2e0307488152506214440b0800d480c04585911454000070b003085131200841c40c28650650140c40ac0818407901402801da4030300c01c2c050090034038060690000c0c010803900d604004601841808442540d083c0d40ca020380c802d41034124801160405170094109451304018800d101c0800341c0c1001040b58104800f04180d07541c0c12042c03080e20b04c01414480c80000141d40e0400c00c1d4041c1a4401d4040c0142c0d94903e40611070050443e0614 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 561970503 1250 561969253 561969269
    0x40f0b0d121713030309380c090303160606050301022b09120c03171608010812040e042306013b18011a0f010507020d0206091201060f 59
    0x800915011460501440d018078290110402c001d09142c90407170243c11041801d6585840585004c418000200c0d040305284d42c040355034014622003112440507000d4040c2080000490030311101c0c50564000c4100d500080030502c3e405001701180c0b401c2c030042d01407030f031200c1d42c9035101041e0a4001d043c0138036030203243d012040c140300d5450030700c4070908112140914007501044107072508105540c007511707038011340502038200114004020301100d98607800888480054010b4005980c64580c1c121410038007420005000d84000f41d5400d1314a42280958072440780c80000d0301001c607081c40088030132031520302980001d115007250b241400c10364440c401c2c4a40040710312201111060811080840815080d00f1244801c691000c0e00f001d00300200c001d01840342d2404102004480c0300404d20914502007026420b200c4242c04100030884200340a02c02e85042c8001042018016a070b440400d034000c0d41d0458150382c03a51848404200004040e40faa03400541c43d100c000310708004c42007501f078212603080f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 561971753 1250 561970503 561970517
    0x8251d010201090b01031103030903121201050d030806150c0a030e01020d031104030210020705060705160609050916030e011104090b12060a180c15080a1a040f0b0d12 73
    0x240004908a5000380400b900061481c001400003921441c03000151200c01011a820204035034002030601040f0380c038984483e0b0001600a9400b00103501040c01010203c6200b03103042000d45001c1c2266000411061007011420071103440d03066400c040e640407048480031208098918900030300500c030403002081c05803082d1070342504070b10f00c40d000300c10568454106960904c0e24550070302c21510352240c5590309501a11601040540703440002d028014050001010b01061502060843d1391482d081541040a030480900c000d444400c002c40e003140194103181c0c0155440401240101400100345900c0d50904078005c101003105000762040c1c0e03003101c404000e0802440100040000c5d42d0b8030b0001e803600a0301c00a101d2608651004035002c0420240c038820034900d503541c055055598000d50102c000340c1c0400f0b540c65a01805c0c0a5025061003004c120003d455400c00009040c00c00141d4881d81c0c984916500c0f1014a4014425158003d842610525014503140c4071001d8500807890008500e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 561973003 1250 561971753 561971807
    0x70b01030f150b0a090e010e120d0c08010510110c090705040f050901030f08030a02040b04090f0b0111060610020307021302040810180f1e0503180f0a060825 69
    0x283c80790090b2100010400480c5925000e490809800c15141917200744d5a00c2ca40c0100c05182441105406480381101d60740d035403613101003e411251111501c1d010040300300b0040c0810b448614481710049958100351900c0740d40c0c0100782e840c0441d004400368001303032031609105249400c80301400541e450018110200b50b00c032000d10003200001d1101500035015214120b0115078080003c1d0f4010b103020303002514154584450340450361003940941411075036910340c0500c07509180b042040c0750609103412490214603491407561100041d1000703100f41c0c45140d001800794003c0040ba00c0441c1e000e40140400254508888025001481040c0300703805403410008441c10700344076a0000e101f840c00100002c542ea5290a078420401d0301c01160890140c000034002c804900c1200400644a20011580d87c4080d11301081d0344100d05402c01d0050480b8400c01c1710700e594454480094410382d14002c090ba035180d9842842c1706650009249000c10410310507140c1a50143c40c0040d000440403030008040301c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 561974253 1250 561973003 561973043
    0x30308070e040b060f0a021005011d01060203070b15010903060e0a1b0f030615050409062009150304030e120a03080c1216110d02062e0b030903070b01030f 68
    0x2011042d640d4040d5081117036a0314070754030f40058003d402c464412540010f0110f01c1c8082116807c1c3c01508401c0e4500c005800c044441049190252581d480070314213100450f544c00c221048090441d50107400203018250042e44100340400003960040310a200703146a5040e980d454074503600003622459140000e54090300e0b100b00d011012281e100c440100070900e03548650b1300411148864200b01c0a4020f000941581e490081c44210750140000044103a0094001c66031480384c00160806071106109105090741d401c42d480b118810b05456455880d9141e18040300c1c040403210b24a9400100c0752002c0c2c07032451000031301703004241c440d4803110072684902d1041040e43c05100101d68082c2c0c40d001c0042c40007843c01148282c29022810011040e450713001c010750600d5601030380c10005903c400100440039001c0490082c0360524030a039003600340c07886400c030245407541e401442145c40b03002010448240381003088501e02c40d0800d521b0300c41561245850700450305203402c25584c80011008441d1401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 561975503 1250 561974253 561974261
    0xd200a060c0c06360e0c03090d08090c0103020904060b070c030b01050409110d03020703050303010612110a05040308072f030c010306300c0b03010602190b1b070c030308070e04 77
    0x2111143c201086003580314504c60528800c81a0b103030f0003c20100c000034107800b450135820302034130703d0b490080d441e481c02a03444c0385000d0b03403003900d2030401c0f1000d0148403014002050342c031004a021b00c0c002d0380d100f600001141c0075005580c00618070711000540f48007442040c002c00015644101e000c2d0308540d0b61030b030801064400032a40500002c2c90f5000041e401d2070400c2201c4e11582c4a80180c1c0c1199070ba03a200e00d82160000d9020001042c001c640b910010030340740c0304219440c1c49105483c0d00b00003002e40000c066001d1170200410300e0070f001410a080c0b20070f0b0ba0b06103c0f11407907a4991005144041d400d8450800404106c900900c50301c00f8070322442d0b0007405800d0070384010700c8000300b1200c07141042420300850000c0c445140008010b404010500a0070108064a207a8007441d81e254035182000707141040204002c04001100040c850000e241200c0094118030f034240302817480a5405445105442012002002c141c0420400410142c00c1011503210301d155407141d485c0c1c40c0d104421310082c4c0f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 561976753 1250 561975503 561975527
    0x308071701060c38090c0a0504020c0a050a0b010603140c07030e060d0204090906060608090d080c070209010e0603070f060807120f1a13020406020703060e0c030706090806150d200a060c0c06 83
    0x851f90300c0000380001d00345035001e080d40c4c1c002441203c5007800151100c60820040380000d6405518030f90051020581500402d0004d1001e203034105042c4c50001c402d2006405076500c020100b1203d017081c401d0540d22641500c11a0381682e404641d6036a5510540c0d004000c480300032164241400030004141d0700420015202d48402000781040301c0f40c0c1c46080b03550081c02440f040100e43c046c002840581c4840501902804586c4099a41030500d2400c241c0303445200e5001070301c10340c0e00000c18400c96602001d92a00811182020040440300c80400c80141198a640e9030f83c142c83d04411001100410340d1b00d15007008280c9950300b82c18044da80d4681030344250701130800540d000710001c20000c1c6540e4446c8029085503010784401c3e2185200007800e00203550b02403000100d1820041c811944103000343ea0b00301185404506468080c02c01080c56405419005404041b8003140c40b580c2000c00c006850001130000c240c0c4044980b1200301401140d0b15040c2640e80020f29003000c0349440c018030401c03810b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 561978003 1250 561976753 561976759
    0x1c03030c0c080d11160503091305040f0f080409050a0b010f09060518060408011103091b0f0f0406030605070c03350901020d050408070308071701060c38090c 69
    0xe051000c248500161a09900b4022401c5080050040006445d941100740030b01c180c019590b1001000d041040c404080000d0048051411003404004bc5184d401c000401d580402071090541c442e080400b198015031703002e0b026081c01c0000708034040020360b2045401c1002600d034012041c1010304115449080e0780104400305100300a22212443c80303000c5030103146801000c040c40c181c1c440fa1140d096a642d00d184040d8094044184035a544050050044010440c1200c004500d00c00001910010b0900c1140d4020902c1180c0d46035107031140d8203e20083c581100d0705000904111a0080032070039290760660000b0103030039071482d020180254006941a1414007140e0007001c48032510415000500004100e40d420440e119400320716000d003d10580c052107540d522150181005491030200420381c0c010014561000080c6030019100241550442d2030700940e200b07983d00d050003610f4071001641c00725080c1c81030a10744516140388204400c074a5107598540988860001d941c3c3e542810384102c0c1c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 561979253 1250 561978003 561978007
    0x504030801061106060a09020c1908120a0e030a1214070e01090501020a1703130501090303051014090a0e072706060207080d0513030803070e03010e0a021e0f1c03030c0c08 75
    0x400c421a0b500504050010b54080d01c0843c3c412b03980c5511940800c0b4000c0f901c21001041519501c4548401d03240e020942c80c0007030042684e0024890349034800d228528060108080c1c8002c80e0340d51a41c02000d8120b210040300343c5500f410200605100c00c185071250016007121404101c6520104080400399440842481c10701e62861355100305800c01400b0b0703502500e01c00c08402c08100c0c02d000d10340c0428041e44000946092440d510b191440660300010003140f10750380a9844c40d201d0f100c1640c1d20900014000507000da1350b0300001e00740b034561380c07201e5401903509032500112050001100492848031b0700030064103668038004e90700c482c824460000c258000800380141d007030141c4000d18422110704810070180d030702c0382d680307981e9900141d480340001490001034020301d0809104114400342d0100050a01c040182e00007140100078201c0c104004000000240f1280c440031048030b094480206001644449880b80c0040f50b08910410340001c1d0802e84640030039030241c0c0c80c0451b440c1d04102018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 561980503 1250 561979253 561979259
    0x1050a0216060c0e10030c0318050a0f0c0902040320042a02100509100606051905210412020105100e040305180a080114011e0e1003060504030801061106060a 69
    0x40c000340f00c459140002e00c0045020710720603507a01c1a00c2041c4100c00c1d140010f0315071003d48000c4c100d0704142050860302d064000e419000c10000911304450b42d40c00522402d0391045403414000300c00306680916080c600124010042020300d031241a41d0401c0c440c0411001080381003000192140d02100350708034030070051071018050481c050340310f407030300140100d812082200011604951046414921503041560350703010055090286000800841c036101d81421f0301c0d8840459100e1525a80809003c000078240480c000c004500c60305030360600851001501d800c0c20f21016089102c0c00c10030055103080001801035038141c076000295000052605070760b43e5641c0d8142c509501c49180d584140c41c2e40780e000e05d0913980e000d0070240a4803801e40007042c07590745010307542040c2d40103030800c0c1074180c1559030f980080d03c813040c811402c6645041d81d1a03002c0d250340003e1100c000c0940c0001e8415420002000145504141c02e58125035207aa102d62454000c080c0d169100c900603241c056100340a45020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 561981753 1250 561980503 561980513
    0x901050603040f021f0f031a120a020a0e040218011203030906021308071d0903181f0302071505040b04021014070609060b03060907120f1b050301050a0216 68
    0x165a005115110400f005030407a000280032800c04621680000c048580b408400c0e44c0c01916a100f004050070248441320f01043c0e007280e1070428041310780c01183e810182110348141080715034440c1d6005408039031690348481408000300030403681a40540c04c0d070210340e0607048401c2c1410381200c24001401c1c00030b0b51700c2e5804a015028080041e25996001c0c03109050040c0c2c2d100c24500103120000051034103518150103844443e8040805110540e40c440800a80030004422540442c80b12050070310141c03402030021b1100960428806444a0718040140c81d1942550003440142d0044070155802c009800000040e9030080758002c140d42c0000001c18010704060b490542686490b0600000390050300092440b0f6400061003544d10680307480d8000144200c910410702405015806449a46842000660307592172900c506c41d901c04494148005001d00114281c13112503014014201c0c031f10031610401d10a00c1389000b441e2180d4a000003040c2411031610849000360710034803040c00e1814442e240c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 561983003 1250 561981753 561981757
    0x32304020105090a0e070f0e03150402120a0c090606020c04020a020d11011b05091806010c1b0b030405010b0310020306010e04091403071208070203120103080a030e030d0b031203040209010506 84
    0x125422611255002c40c141d020705e000e141c4986865560010501e580440040011102005c1c450094004540e038882c81072504d42407650003034040c1c54040c10401180d01391032138480215400350024003045004142070655410450884003250b007220311648031201004101d1144403501c5000d64001603060b8071480c0202994070024a246000141c01001050902c44901d01070b81914001400010131076000d2a20715174041c5141d0100c0d0452500c0c0c0b8203c400a000d0740040c0b107015041141d0f6000808551600a920502030040003403a00d40700c0c04c10f0b20f8268040d051a0700c0340c0e03109014062107e80d4009203031090300d1148405940d00520258031905010040c281b1501c140e60b0301d0440c01312005204010001420036610450901c280c5400e401001450000090000c0d401c64204000d84900c1ca03c1d02c042c41c41c1529000b07481d440e9a0100c1c0d81054000f400c140314040900d000100d400751070b1110302e0784040c98902c42942500c0c04201c1c20040d415191108680c020340c46030210b40180310794105800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 561984253 1250 561983003 561983017
    0xa0207080c1f120b040501080102071430130609090c1d010e0303040521060c03060609010e01180305010516050c0d0318081204020f03031201090c09090e03030106032304020105 77
    0xa4000303007801100703011601b550000d820803640c81c3e40024580c1f040140b024070745460ba110000c0500f000703c00c0b030032408800030041c0ca0039103c2e48400d2009003e41588030b000300d03503461203403001618010707070783e000050903003091445140c24403443c02002d60101d6000e805c166021010440582c00d402c141070005540e0b0048020202e5094030090201182070303101c01c0b10300707006440011784000340303404c4c1442c9161034070300010517030f001c4105d050060040710744514041c0da41040003401c100c100801d800004894841c0b00360950b55a8000e0f0043c0041884010750205e8001c1892405075602c010380300c20281c45520400f20341214581c80b414090003403501c07950003426500d01130201c6540b070b40d566480d400066001056444a0780c5900021300013181740010010011078401e8020307500307091100400000c174140500c1044a8661540280d13220305108206400152112841c00c000704c610030f602103036581e00240640c1e4046481c284084c12048590758005064071303d07030b1880d500e217a03513103900448039a081a9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 561985503 1250 561984253 561984287
    0xe0706050d090b0a0b12030a08010b160b0708070f0c02091902090603071206050a030818061e1b0a020904061503080c031309110414030a02060a0207080c1f 68
    0x60b0300e400020f030301c1c0c0601d41d01604413801d0102d6104003181c10007000701188100c2c4044c55008011078480f440d003001015044402c540c034066280c40302c046803200c180003481001004c904214041120080e00014200d00030300e40c41e0f485141810241a0980b9843e4048030007035406440c3c2800a050306654240b0801d84044036203015040148400125149400684d40030020501180c64414078003158400c5c080145801c544410100307103552922911480741c1f0390115010543c48640c1c0300540c441c00708aa003907458800c02d00e81071240403c000010f42e0000702c4e400c6243d90f042040302103684400514121fa030394008168500c0303911255100300007446410030481e11291409000400b00b0603030b01c00740009042800203507603a904241c034004c90607582074002e050b4482c50003080301e407410746250640c0c0554221705034a444101c03040700001d2404862450083d4002000640741360300c0d80e070100321130b4201c490300c60403280d07040175810401c910072014801100007460350042c59401c44d40714030710090300000e00f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 561986753 1250 561985503 561985511
    0x1606050a0c200102131d0903040e041e05070b0711040c051b150703020d053904120c030c1505071707050615030d0507020a050d030909090b0a0c030e0706050d 69
    0x360108429268554040036044500c6d41c6203c5429070803182481e809440013000e1850182400c1301440170807005031004d0146203800c2c03a08a01000a5420104003681100444440ba560340e0400340c40c681c0483d904031580e131100e202d010078900b0280129145404c1c1c03515821306003030040710411801400d200e080700c401d10505a080c210080040d001c2c500506103540d0160362540102c142d203060316009481004502c910030441002d143c180d0000900e18074030701c4ac030112035482492103456035002d0360b003100725020b481d12a07002c20800003d4003002100e10444000c0d00d4140d0b1181070001024008411801080041110f00d00180b91148080c0d0380384001540030f0306000071500e5240c03428030304440d03220180f61030302002c45682ca810000c103001c0103003c2c5401443c0880560100d0b00c41261440344030700443c03000c6120070030140240c4c40d88001c0d01d1200020002c000c20750400e001c90900c03e036207200183d4030b4815650700071032103801a0b40150100b8801040d600307180810456441d44185618520960b407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 561988003 1250 561986753 561986767
    0x60117030f070b091e0102070c080c180a020c1009030201141b0306040608030a090609080a02030319020102040b07081c050c0a08040510020a0c02030607080106080708060d081606050a0c200102 84
    0x101780103601e665009a0005807540e140b454030701c480017045c2c0c00c00081540010084285036441d80b1071040b8411400050009a841e2001c240c07010340030b00c40780101140164001e200501030158460b02e2098041d83c0280485907180305030305011901510b140035001c1260148140c0e10900340011604008041d100103446036840303d440c0d0540e005200d60f540000e1803e642003064552183d4503401404045015101c40502a80000d55a1080c03a0542d40b21849000c003500d03069000f941550002d100004509a44a02600c0c06084503805204616111500d140040440561a2080c10f1042d9420301d60345241c680d6003441552400c1c0010011280c51054000444002000740041c0c2104007a5407203000f02c0c3e80b2140304041c1030100081c8130200300400c207401004000e600000c510f412030428100b181d19502d8076030201d181400c8010000d414a60009008096840d41d03850a60b21540a8003040000ba202d20f000f1030309591030340100a00144401c10013100b80345110799110280c1000000061a00d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 561989253 1250 561988003 561988033
    0x20d06020406050309120a020a15150305030c1b0a2702040909020f03010509190c051f020606120d0e0406030501060e06100f1b020d14060117030f070b09 67
    0x1c020b802c45000a0804024010300720b004004a004054071561103a0400c018184003d681c0c500700716010f0b215004ca514040d0843c0441d50250f01c0351210601d50f020481d4803800d02139980d03801410b16000c548103940c607c01e2010a400c0e8a8008140c2c000d0030f0300e111178544000c45c2001400303114203410200141d0500a0861040e20061005042c400c9011604560a004000700607402c01c400c10b000b40d0500c0f00b042806540840ca4069031000240b101d120110a0708054036005103a807c85d0750841c2042e401040d088402c85039000c0441c003160b0131034089a03907030f409101c65220841000a4190320508482c420a80541174410701043c01400002e2040e40c0c03511580c1c00c0d121558040130301c42c01110248005800c1116511001c202e260410070005048202e00520482001903801030150210400004668400e03110555050f04126000000e0f0784400c000d588403802842440410681001c90540c401710200989a82038800c3d005141003614640750b21200c00030082c40b240032030045c0d8908500d400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 561990503 1250 561989253 561989257
    0x2f0c090106090501030e07050a030f14010207050304170a030206070f05090d0b040201140c0705092206051609030b0109020a0309050303040606050906040e0c01030b060c0a1b090213060c020d0602 85
    0x201e103a560340d8900514100014013141c0d905200c41c0c0558000750300031720490710341c2090441140da000d0300e60681003402d81002c480c4aa03e04403006019400019602d081c00400000340080e00d41da520104040c2d2015200c0503510000040d000740075810400000702114091500700c0894405400c080b4a01401d100010b0000d020111046941031a04010b22040d544e01c01b95211401602c0c50005103094003c10459584580c58454a84035441070710002c1c007519421001107a5003101292011498140342c034200c8090300e81103a500025186c8204c12054241c07050090790212600402c07140041c2e400e264450029500900c0700201349600c6000e01c000188003000214415402034100161103400d0400f04460381070050502c0380304d1402c0c010b4090b4028800301ba0341664040034200000c8042d0442d012584e280200903841c045401a1544076092008503000503098010760400011029201d403002012402100783c03104000c0340c0903c0a0040e28010301c20fa41407140018100c030a403481c9580da0100343c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 561991753 1250 561990503 561990509
    0x50a0602011a0301050915130b1303020d050f0405010305090c03070b0a0e0f0a06030902040e030d270b06011b06060b09040b220b27070f2f0c0901 64
    0x50b907403240480c0d00c0c884481c03000090752808030002e1020342060f07802075030b60b8000702c0908503e048950012440441c40304548100c400d07803001c2c000c640d80c43d0980800340103a020340b2090700580590a4819640b0380724104446028450414050610742498011002000d008042071b10612454160040a5900704040b1001b40400e031942d560711150744400a0400308494800781c012250002c1c10b09042e610b01c0c0c0c1c0c00f429501039180001d2081c82d94000200501142c0240d09000c0c007000030940d1500c035240e004040794200f02c02c0e01c1d8003060480c0c850021001003800014103d0020391012038415031061b07a10125a110400d4036149140d000d8540304111252a0300c000310008002402c6003080c10280200c0e0303944001240c0313491101124141c102800041c941c1e020801c0c5a40ba440b10310150340300c2d111400b001024070451a41e8060500031040d91050554141010883c1041d8403071041e40700f016103002107265850220701c2e00600000390303009402e290010741d03018001c0507500103140c1c0300e00c9861802 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 561993003 1250 561991753 561991757
    0x80c0f0d09080408120a0807082d1f050319031e08070e03030724291804050c010810050d03020604030f0302040b07020f0102011104030f022d0f0109050a06 68
    0x207107074038280d04c05103400240d90041c41c0d8400d081c0a101c041c1031f000001c2a60000740d03801c111900b550390201e074a801e030107104020a14505821144c0701503040d07600d03410748909116003512094481c5050780e8090612144034642c0e041d402504000030340c0c1c414a000880540c400e050100300140204900c0c14901500c7d420f8074001241c00d800c001c0081e90050101c2e8120b0407d50140d4030b000890b489041c0519684030448011040204550004990650100e96212400300350742d01581c1c100700d14000b06032603085410b4400d403c040440c80c13003038450f0400e440c060742c3d1002c0102111900c2c08015101c10000410f911810500150002040e440340e00391070311418401d9001e04003d03c3e16180107810080c00c010b4580c1014810300c02480034001107022188820340483e105440d000100c40101d0140405240e9400780101c04107000080010294501d40441d20803a841d10200c4a00b159081015541c01c0b00c0e0001c0910f0170302c1e401518100510762903605081072400b00d081a88072000b09607952025071110300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 561994253 1250 561993003 561993007
    0x2120c030705060c0a0f030e24010e01091806110910170a060f05010503270a12020d0e0108060409021c060b0409080304080a05040f090c0e090403080c0f0d0908 70
    0x1080040511070700341d002443c44000741c1890346003100181b88000d00d00000f01415501c1000c2c0c4400d00d410000d0189120700b1031080c01d4503011f03014420040081c01c0c4140384000c0944800072801c00c40301e004180900350303040322800c4e01300d0481d158100034001c200c43e0040d800604108600c6c8640340d000c0503213207920302c0c1d40b036040055501c41c010200054000b018000b1003868840280301124541c0003550440b1024640180c032512011107240722101c00805543daa00a15844001030080c003048280210340102e45403500607034000340030791700d4040d9902001d00040c1c000f00ca20425600500c0066000b11010b08001204010303580460a004482d4411103201040302d44110100400c0340115102840265000c1c07224101c0d83c0d489a4940c00007800007448203034086149010035200303005840050000c3c500400b0810381d07a494170402000c1039000e01002400040260086080c0014170724056036140da100c0000356601c203001c000c80d0308140c1142c58200300c20170025480d00d400b40109041740e0701665420b6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 561995503 1250 561994253 561994267
    0x5040b04030c030b1f1203050c03041e090e0d031d0607020102030a0b06090d17130b13080102120a020a030207050313080d020a150b0d020316080706020316060c02120c03 74
    0x14041c03050003882a01410000071041c00003103003217070010381180d44c014511640c4414524055036140100242c0a90a100228001440180400360021581c1c280c0010038805621606081c081c0d81c902e0503844081d52028405c0101035120b03501404507412070061040c1c07114030412565041850566803c00182e40100c1070003c0344d103c620508464031000c5400038600f0702d5000c0031440d14204100090440c90184a01d169201501c00803241c0d100700a03038680414a869078902480c2c2c0d08034041d02c6c8841c40841001049032a81442150308244881d42201c0c1c0039500c86483e80007075402410b00c0700c101502444000c00282c010070107018403100000e0110303c868140100701e4900441d548030081190f0019140c140810383c03c1120f0622010304040c081541c1d0404004501803408140000750148542007508180e0b00d031482405007900c01d0181a02d0480e940c5050481e9039004121100c1c0a000e4265040d20010381d807a84460458042401910911442c100390409036403c41e60903c078550704000354407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 561996753 1250 561995503 561995513
    0xb0109140102060f0c092e030203040f0b06040f0c020105160e100e030118030206180607090513110406021006050307140918061302030c06070201050f0a05040b04030c03 74
    0x100064620204600c0c12a502880000d40d152405400003112030642d03400b10b944500ba480841d8921780e00588420301d03200001c00000b50200441d12800c0342c8140d20759850010b14481d000b26801940c00007600f4a0800882c0c413500c1c949000504203c0e4000c1d91a800804040800d0207011820b04d11500001064030700640814910300e9009e002c1b0003040a0034600040c540c3d40c42c3e00a14002034540350204542440c000480c0c01020742603290864898004a00410544d00080e510300c1101d00000e0007000c072449000440e07031801c4c11348410003c112008000d108906011807184050303404a50045640390b1500402c1d060380d0701980040c0016003100c52000141200c0d0b0040c20010041600184102460f01403050711007454000414030075103101012600343d071211558505140c2c1c00340241c802074280151940c2550b100000102d02078000c0030003040d01464414140c44c052501a1a49490417000b2180103526230301010b0a102808018003000c02c010401d20054406140314560f1200e85500314285 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 561998003 1250 561996753 561996767
    0x40809031005180c030f030a0507151b1701260c091509151003021804060902030907050a03121812080301140f030a0b1009090f0209182d0a0302010b01 66
    0x6000761b2000c0043e02d08110700208a504101285c80d2140d00c410452401d1210411642829000c0a0030007140e44409200300c4610a0384000b42c0d260b42c036440c5c1d480011500c1a010910903a041003885078860010344060a00d0303012919040c1065515400007080007404140081d191844401018400110f090408044c00d54000780c1401d545074400e034503800040c0c00600320002c0c4201b015008540300442c84600c04810101100090003400322a40b40d0500790002c0d08101d41031019807040f20800982070500000c0403064a400110b42c500107007020f40c06841c62440a090b6801000c501c03400000ca000c1c003041010045032003403840503078139450003080300503005c08825103034401c28000c00c026485540c0007030341460503588582c211442d0b65949142044124a40d40a003e650381000c181404016886103000c03009803003255420740303540f03c801941d0700b004005048000300e9440008400c006042c035400049100d48080c211280803040c400b00f60f410002c540c2c0003200581c0d1101500d804642e00084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 561999253 1250 561998003 561998023
    0xd11040f0519150c02012d0e0f010801030609020604030b0c070b0703050114150408030d1508031e0d0209040f0b01080609060604090506032e180b04080903100518 71
    0x50111540d0070702001400c40d4032207080c0303c000d003c2c00c2c407450320459001d50b684020701c00203080104815050690050424189405401d00141707501025001901e00f080f03004d084000180d48000071603013156960380060880300016a4000014400000094510707104648518804040da03903c0f45503511b0404c11500015016a040c58101030050200381c16040c0c000100b2002100c650400e44011130103599140305682059080b4080020301e2003620038203805c10b181044100400300310071550341d600710791a4007412040c152408401100790720500007074000340000380242c0b000146000c10000c002400c43d489202d1184000d9110500d003101c44d07822440309507100d1010744100c4a18600840024002e120340d000700843c195981020075101d41b000c015415000342604068040a6469152843c0c1d4507170141070544003d09015031890f00d0b426003011844156803250032107480751202d075a40c00103900405003064061003044404042c6d03020310300805015080700001c0c1e91950401c05441420420100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 562000503 1250 561999253 561999289
    0xa0b040e0903070f02040f270209090d05070807030302040f03030e03060f0f0c0a0c0507080102030108060c0901021b010309061b030b09091015080307060218011e050d11040f05 77
    0x100120f070110384200400350049504450010320b482032807800c2801085020041b0111aa8060a000c400700f400d4020482940c0210b809019aa03290342a171503460448800d940d00207841400781380001124035019210640c0b01f400c02504140e2204003045030700046910640001d10080408a81418188601074015000030754420781850480c0085025403c05444503041c0100042c0c00705500d07104e8030801181551100590b001a0745d20325015003c1c0d0000e002d4500c4a020704004104081032003003c941000506030094210309014281104090008180950605440b5081180000c1e6640304440d00072910b188905203a0000c502d0003805c540750944a03502a252f03400030702c00700d03030000160144030300340300c02010500310200070461001b81c00c0380c0c0c0015124880421440d080007001e03006070589689420f00100382100031001100d80c1c41c1c540003001a000002029100030274820303c000d04d01d0b28080e000c0800c000f000540c00080540c000e9121086001201e40140302910700b103126407008403020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 562001753 1250 562000503 562000507
    0x3060f14010f110f01110a0908160519152a03080a0c0e0d08070506130305030f10120507080d03050c0a030b010e1804020f010f022104050a0b040e0903 66
    0x6500280901c40410318200a0050880f070824959200300b0142031030045940090054201c1540c100760340c0d4014656160100b01040b402180e00c080008000d0404031103080c01c1030031145440b0078444001d003103010841c040a501c220110300c0c0c0b01c0c02041d44503094299034500c082e06c500c2510145403c0c0c0050180d6a80560040114000c00da1204c691741d0802503030100052008040d9605031001451251500d0b045019407120f0018801c0e44006881a240a2070541e81d0641d00c4c0c1c01c541e030148a5010009000c0741c800d0020401304200f02c55040e9020b11034004030030100c0d8441604100d251005541140c0c2c0e03030b04c080410720604c102070117140c090721044d08080c0658145403542070400d002d05c4010600301942c0703110440b6541e1140031456040c040151075280d01c08654000c1e080451412034080c1d000d00540c9400110651007a5028580c01019501510082401403482508000b4071250854250001e1102084030703030f220404d40c0300400c40c4c45801d60f501c40c41d04c0ca410054641c004c11340a038940007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 562003003 1250 562001753 562001789
    0xe13060c260c0f1c1d1204060c11010c02060c030417010204210314122a160809090c09011409060403030e041814010b06131203090b0a03060f 62
    0x1114180c43e607000d0341003803954840c3e04000710b912a43c4040c030310041c0e240703040403411440c055030071160580180414007a145420008410f202d02c1d032065100e40d00c002000b050100010034031080c90007404400501d0719035041055500098115003107407040442ca900005001c02c62b032441910500c2d07005070458000d604041c540410f110306400446288451080040b400008241c0701c1c8007421800e800d14503000f9141c1d85816444003100c001100d84c41c12104400c00b00c0c1403c01e56541c0243c0c40307100160307003842c58184049040490b154012908441e00340040c040360010b5030398411072900c03405c8843d280030345480101000600c640c10004142800240400c003903801074413600e003100c040d41d030542403171280c091044010034018141295250400c0d600300460340c0410140c41e004840410070f40c8000d20070f0f9282e200810a4074482c1d1020300e2020485c52404001d00400250304514190182c1084501c8507900d02007240d1700c2c1d0101425100007a5240c00a10030700c6a190040b401929504001150042e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 562004253 1250 562003003 562003021
    0x21f0b13090c09061d0a2906160807020f010804050a06180210030b040b0105090f040c1115100b0408030912070528150203040e13060c26 60
    0x480c01000c1100303071501100390a001036020101d004080482c001c0145544e1164030307200c0030884c0d43c1442e001c100d0b050049007a1404500800d000c0c0d080c26551201000e072603403aa82024040f00c511a900401d060003024010305140385040241d500545909542e45070b144104040507544103090b0b814001d0102c1800003040e400213030351070040d501440003e48030280c202760310200c000c0741d0342c000e602c00d0080070180d00096154001c3c15000310141c40600a05150b80d0064442e0b00a02d1561031304881c0700c801020b105c0c540340d00509541001400c1070481d0300803c414050422681800c020070801511003844031030064940b031031008010a070340c07050405080c4503402e81c0340d1050b401e12a02ca003000d401511040c41060114400401c3c0007408800c0e03408402583c0f1a182c103540122041c5c165180c003000075102c0d1440d6407803003904001c3d405503240c14200700c00c00e00001005007501681901441941000a005115002a42c40542c0b61000c0210108170038041e802e03040034113550003003007100c24041d400b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 562005503 1250 562004253 562004269
    0xf080706050c030a1b0c08010c0311030c0d020304020d0b010b19020a150b0a0806070f0809160608070e0d0b0a05060a06140a051c0e0708060c04060804050a0210021f0b 73
    0x440c8074901700032507405140b945400c0c3c003482d2401901070b280420b000210315005610101000e546500c0510414a60300108826404100e030444045081000101d01300000ca60095500c075100600d05800c4040544a034444514244c002e08051840000c40403050b11000d00384040c3c2c0c100a100501e03002456603607804240303400004840e030181d107a07014039055540c0e035003842000e810150115000d618090708028540106000c074a40030440360390100d0320314100400c4d5011a00042c188144041d40b40820440782458000c1c035200070400180c0701409a41e845054610086000c2d0f000a5120b04201070898202d87c00503148231b2007406840000c00042d500650802800300010b40c140d6159030962034155428480e10b402e5044400455410307212580c66135004190300301303400080b03640305502c910046a07a80f230306441460703401e4010705c42042094800c4680652092041090350111319065011070201c0c4140048540581c0025141e03605031200840000d09850048030140034070003950004c00d100c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 562006753 1250 562005503 562005517
    0x5010b072a051e040e01060f0b0316050c1212060907170c030603030d0f14010503030304050606210321151e0a050d030206010806010e16030f0f060f080706050c03 71
    0x182c690055290000d07202103040f14002940940284205d040700c0441d2030081c41c0764020f5140d2402d10020110300ca01c0e01c4429079200700f041c58002c15681d41214400e03161a00640542046031080340342101c5010300220150034078080d866003e1800e8189001000030070348004000b0020401d00030b06854039001481c0b1015000b80341c04003c0d13640e94403980c0101c0e041d0720550b0308140380b031420201b031081491640d0f0711074615024161225100c40e40c0fa10700700b46e01ca100648002e00b165020f040030501031325002400520030228440b070f4203082902c146949007544c21501358841c40b03020201d508042c0303040e116140e540c080442c0d95502c45100c0e005c0e000603002d1010700003000ca00b03294602452855206e1001c54009010000d141d0000b507103803464000c0d55081300340281d043404e004041c0001030003504803000900600303d07802d154104a0305442c4c110000d0403481c40300344100e42c4607044410300503440c3c444c039405045400b000801860508620f10318040c000c0e40994104042005005e01c1130401000b0f480c90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 562008003 1250 562006753 562006759
    0xb090c1215220503040524041a070c03050d02010f0b0a03110d05030301030503030103051b0a0e070c080a0203040f0e01060203070222020316081005010206270105010b072a05 76
    0x1511411810510410301c101c02818002c24410740d4002d0100010140c030407030740211807199080d4404400300c840c02031104500c000c42d0400348410b0020f0208c1c1188800003080300c80d0164109800c5451750a280d0380d5076401611960802c050003180980d0a000319541102800001d2000c0501c5202103074192107144805095031140e8031005070325175580321514402d0b40d00103084a0f12942c4070b00300a6269030081c44100c569118003e010f042000c004c511110410100400b100c0d02103182c502c040383c103d00000c14103010001c5840c00031001903d4200609808180740d80110788990414809085054054224854480419004000711076000088400e5a54140c0d010042441210000c441c1d0210a91031240068004001c202d103001c0400c8800c0c100b0000c80c0c0d03900940d42c45082c0c030000802d0050080038010380000002030320501d4900e02d84901d421086000e1407802c0522021103003100c0742a00040c98004d000600c81d41840915841a9801d100b000059440580b6554410400c10078600c22140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 562009253 1250 562008003 562008043
    0xe0a0b18160819020f0706020711010206010905101802130f08120c280501050c0a0305060405060a06050307020c190608011d240613170a03050304020f030a0206070b090c12 75
    0x104060005c07055440c00d81d40041c0030741d1036051034a020758124545583d021300502c10703000009a040c840d070050600848119816040032070610a440700c010000e00340d01d0040b15003c12064400c0c0301090662801406041501340c006401c1074400c0d030070400b0125003a8100c284c2031001d04d9030f601000c00d81080000c1c1072003103150350240100d0a6221001c0488026206500c0d00c000c00c0394a5001000804e041242a64200040d99400c000c0008480003551300c250414401d510621040b40a80c1c0115000302150046130920f00360400020071042c60030304141c00c801c010680c1000410381020060340540703c00c456983c0c4c1100c4100c298207076580b00510142011003140313041b148245040c88031529220703010341440d0f0b07102409001c1c43c060092a110709240c10410b1002e02d403c440e80420030415255042d9035403072840d1510780801c8440b081c41801c059050044100d800010f0f0b480f0700083c402944206944a0b03640b60200c011410300320b2580c1050b0250b801c0c01c501550b00d10020900943c0d800b80103601300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 562010503 1250 562009253 562009267
    0x302071a060a0e070e0a05041e0b01050d1505041503021507030306150806030c03010506060d110d1803080f0403050318120301120510060308040e0a0b1816081902 71
    0x5102c004240e0048011902d58402d01142680c000c801c40b411050550341940c1c050381e00c0d400d10044031005001041c1e210800c0c1210b20180d04142c004010708041450305504184602041804450b624031040c29441c01c40481001a400c1a0103022206072801e803046107910f1442e0003055807611202c100b030a030044d001070400c04060003036020101500c070072040036046641c1c000004e04102801d13900b4505c00d1062000c0520b85107414060144102405840c080c10846000040390240c80e03500ba0040c8170203001d00140500001501c00c440529603d00701c1f07203081c17805e54100a0300191000c0c0c249404420000204804280c05c001100c1d044040180c21100c942c0d640c0424a0901044c582001415040080005010350011300c21602c0e141c0208160703041c50303103144441f40494035948001000808144000c004c0000d5017040d1070f074040d03040103000c00d40d515004005204101044401d9034806008414488402031808010ba800320b413034204160282080200711001c0d03101001c0c07141d001c41c2c0000744d40e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 562011753 1250 562010503 562010509
    0x1406030a0e0a030c14061501050f040302100c0317070509011202090a06020c1e0906101e0305040b010608070206041101091703030405150c1903020f280302071a06 71
    0x70a0115440103803007002095160060840c4a0f40301c080e0f4000c500d10400403804e03c4046039241c018a1420b45c2006105401c40c0192483e42054004045c2d4543c140000009621808085100d4400c0c0340d0b070700c44460115240103032001c02d04001907884030546c001001520394200781100c80d0200309003401c68440c551150400042d2045c2a00307550800071050f000503206800080c0300c0b05003442294220341d004448001000b00150f03a415650740440e150000c40c1040c00c140c001c10f011400c031441c0290120f050b20600b800b104017004040e1000941d548204414040c0c80500c044c0504001d1520311840c0c100300000a54aa07030181c00504082e180a080328040e83c090700b103003801400c03140780c4090300e0041603090a84a42007210152807038020740020041c0c0380d4414903503c2c8a844c00301e07035403400d2151008032110247c450840c007800740369003006900b1110803100040c0a103180710000b038905004520404941e403003402820901418018402d83d400508109035002e60400c03150320a03841d9680e04400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 562013003 1250 562011753 562011761
    0x131e02040b2101050c120f0a110a05040612050613050a0204050a030b0402090a0e0303160509130c020106080105060f0f0a091104030b072d1103040801090605010b041406030a 76
    0x28032a846182e48a41216689010300c0c0001e149458800801c01c580d034046035260144a51020040c08807a00300003d00c4032200026119000500f45c00009541031940b401c13201d5640c0418a603402244002c201001000c0c1d10103009880b80c04402801e100504240e008500f4000c9000b02141c2065110400140a072813154142c1d4000c16005000024032552410400200d98003640d003039010f031030050300050104c2413502401582d0b0300707440021841c41e9500031400c450600c041c4141070800200300001c1120b50384690b040b000c0205000300000d5030186042001e421100c05520401c0d50b41d0404080141e5595009403680110905441c81c46051031504000b61080e203c9070000c51015142144c0a888030720001c0c040c0050340d1260700882403d445032207060b02c40c28400345030050701c03c800d0221030312005507483e0704100980307c90514022003159560b810b81580c0213074200c3d1505a40da000441d05200720703800303070500500c100c00c0003916150078000364404040807501024001d49000001c1495003400303500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 562014253 1250 562013003 562013021
    0x50415052218050a05010807060c031106070807020f0d23070f0c030c1413020a030e1e011805030d09050304090e03120105030c130e2401060206131e0204 67
    0x2650280c07a54020016a81000c00d9a00003d20b000c000695091840c811941030b0381030304005000046c54404102c0c0c44c0d180584045041110000f01141035503001c0100900684a40d29440103d15218070001c0c9840862100d6141302e0f4000340d6285620b94002e0b8007103c115805003000c0c241c41d2200348004569100f6508000c05001900d10050180400c0da003070041a60f03c55600c84940700d550b4103c1c8480e100101802c4c80c3d101c800800710030001d103016801006507480700e0401040c8181c8024500b4107004051440d510307540c03005101030341e00700c80a114003800c190200c403000a003130309907403500c81d078034002e00228826903a81c41c4801814807408200355402084282ca0500012195200b43c5440c2d030444011101101100d03000815140b4020400b11515000039040940404e126100800034114600c001021070041c40809650382c0008d40b840706001a286000c2015545007100c000c0c43c0420040004007403901369000d0f070001556125020f00c40720001340c520040801640009401452403407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 562015503 1250 562014253 562014307
    0x11b02090c130b0304061b0f0503040c090f050a0b041406060c1c020a050d030605011d060d0c0531181119020d09080d031d0304030b040c0605041505 65
    0x542c0000700c103032000f0001c40c4590320449003408181c0c05881c0e43d400e0b0380e694601e100040382820182e500d149110340041c5034000c0c029080000075a45c0c1e040480c0854080e030821424150300c4034208010b0b0203060261010f8003a094030104000356007003082082c075400c0582118801c400c000340d500c0d03038004104080480200000640b407514410403401075600c42558008582d203003c1c9440f150740c41406442079004031441030b1a114403004018040c81c00c0c0700904401d0035880041440510b00e50111031140b412600002e49132140e0b40c40428031407042800d4480c151510340030221040000b03c2010400100031a0b88845100040c82d4003032102074090041215030b0404180b01049402c4600661401358205d0001a000d84a0b107058804044840081074081c00e0f07419804007803540d050900c00e81c041000481001411500c0c08440306810b0b00b190312030303401503d640100d20309200505c5000a03e9000502050030128a81440c00003403101000060107543c007805000316000085a058282c200a440004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 562016753 1250 562015503 562015537
    0x309030105071809020412020d0f08030a060512010209061605010e1606110601150c020414090d081806160e13020c010605040b1e010504180902040b011b02090c 70
    0x1e0784000d00070340d0007044004200c0e07620710340001c4c8008148221010f6410b20410001d840c440c6400303000244e080104200d8100480c4002c50000c40c84000196000305c406e0303480894060328100030031100b19005004454203034030402a50603142d440300c003100d07402030142d000d840c4540c0c524105a80100303c0550320b1400e50250500d01d0000d600c0012250058503d15100c6000744501b00c1c0c7d11030f981d24802d004000b0002c45400c034a6507214001c000740c01015200401c00724484858600503c00302c841511446090781c043c84069010503044105a070740140d40b101400414417800080c1d50740c0d2034001c0d050002911070396141003006440760132803260303038040074214030203401640c407096001354040c84005c2400c0d4a00000814203142502854031a100003c0001c01ca4680681c4880030011800032510f050180401c00019600401141e1511610440c4400600780301c0500600040d00c1c1c6d10180d2a0402c0343d500c103035141d641e04106034603d44030b8066400c1c0d6036030343c0e401c4201307900c611403071040304150898 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 562018003 1250 562016753 562016761
    0x4060b120111030a0c08070f0311091203040503010e0613110f09180609030708120a02070c090b012607030509101503050d020105010303171b22170a0f02030309030105 73
    0x1150043d802291013200402070003454100480d8250300554000f400100000211030501d031003600b0010408414580382803401a40100044100030b5007501701e003281d0030203d010402481d00303105002c0501040d030b0107442140ba141c00c12031080b402841c00240203950782c5010140689807046404840070014242c40700504001c2d10280d200c04a50500303c0261007214005070b0100d101000fa1040982d000c0702c0641000700106200310b01c45401404150b02c0769003400281c021660b10f0540e00d00415030242c000610600100c0010982d2241502d04c2080c0f03902e2091212900725100403060b488011807400003010b4413001c03503071410015020b0703c2080080c04c00d4001c00041d501f40c128101103900ca0000ca9407001d03200b0300c0c16402d0390710034480038000c03444902a80d0142142c0034189035101250a1040102602ca0075403401d09030044100f60091030300d02c1d0f24a2075607aa0780051b880241550056183d080d5202c01c03c025541c00060307900a2604841000020454800b0000c1d41c5040a008000303100b2850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 562019253 1250 562018003 562018031
    0x501140705071203111206040c050a0c03110a050303040f031d060414010c081908090d0c0b0403050705011505091312030b130f02030609131722061805090c0304060b1201 74
    0x10064030414410b49c0344c81000600c40e80502c0c1102c080150300d03200c0b45410151900c003910700388007104a401d00c9004020325400001c0084c0011481140302c0c00c0c881d6080d1070f950500600c0703514010301c01c8d810340c0342032428480c1d2552080b041d1000c80b81c50702d10800c1d2040d0480b00499103101c04a01c010300c207460110f40480044020b549454102d40155142162540ca01001c0307a81d80351113404503000310386050b40b0040420b456014256102d8040d0400174501010395882c2401c481140080b4180a0000f03602841186840300c41c10745c01051145120042c0c1c410303a241c3d5100000d80c980440c06140d9a980903029a480314111519012400c0c4010403101c002407440002a501c2140c3c2688511035000c002002c0c1203401045161803604a4611005e64400d01c1c0da00e10030381d01202003400101d4030b00c0d047e48150819004458041c1c9001c1d41c070102e0303110168180861000650b04014130443c0b86508010307544580e030b0152030b4019044040450480c0a13070010844802c2c111051a4680d42051000307440b601c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 562020503 1250 562019253 562019287
    0x20a140c0901090204051318020f030a0812070806121e1207080409051b270904061a01020304082503140606090c03090c130609090f050114070507120311 67
    0x24030280c40040310b040149402008075203541d0b4601110082c43c239059805810114426205c1d4540642202c0060507142c958442e04d0700038214000700303084817104201c4003075404044942c0080090320010301c40050001440d80305e1400144062158212548801c0c3c002c804000d1340e030103080b50101c041c2c0e9868041c1031a000642c4603014039070700b0504040101d0850809040c060307a1244010388010304142c0301c03905130409140c29510170040e082d441c0710740c403a0a071fa07a00031311800360b8030070200080d4480081400d658068890b54515056400a120411410b03034007041c80020b00c106280382045041000301014264101d42d0400f81014500010715510808009030a50054001300c8400d015903032101807044c0c50744012503203046c850f0450000c20305207091424201c040204002004983ea5849108842c103e41081c002560b201c41c6948000c42031041c20700c9a809001c0ea082d00082c41c0c4d1130a004050964450382e00700030500d540711006494414403951082c1c440d181d0400742d5075a00c0134102c1c0300392607007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 562021753 1250 562020503 562020509
    0x1090f18031232130c18090b1806060f03100b03031e0c070909031d0d050102030a090b090c010e1311040b09180105030c01030f0b1203030f090d020a140c0901090204 72
    0x464610013050301c00c1c04c4510f4000b07040d94041101d103009424942d91190300f42c0102d00c5040c030152240c04240020703c41050241c4504d0311000e840319040c0003032031500d14043c0c002e455140181e0851803103041946000c00c007040090b000020105141c1400303004207145116170a4071308030707403048034020301d001e800800d00814180321002c0c11502000d85035450001110608403000300130500015101100343c1c0346000881070740c1d400800010721200d941d10f849003a80e0048984240e05540c1c0c2a5403020002c043c1ca480d50030841074002060300c201804000381607210000c0c495481507411225945c603109054009400144e00030b40c010307072215030740c0003100055040440418030503450480b0301d041a080f01800b90381200d0006000340342d1b80745044015001400003515444480780c40b4030420103191500e404036070740221b8010007160340f4605840000501c6002a00300701498000d41c040348021a40000c4041c4c042d6005003150707118060700c0f54034503d048408c00c15181c0068241c5c000250400443d8090021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 562023003 1250 562021753 562021841
    0x61909021b070b091f1b050606031b1806060f070506070909050709170c06070c050f0a06020a1106120f0609180307080f13030b01090f180312 62
    0x12503220385843c00700d802071024154004e43c200c000c1036903841080c030ba0b09242c0f0105040001c110b02900c04140101020254140c4d15984407109104150400b001001c44000c0b501c0b91a0100610032400a203003110042081054a122040401c0042d41d42030308035003c05145401c0c80d075803540d20346041d68544908803040e03000319061820000b01c116403030003994440d000a9a03005d2a0f40d0400b150f0205601d20080008002e10640d00d01c5015615a80028006c0303900803152802c0c0180b900040141c1010180d0509000340c801c804100b002940024105c0121b035848003a242c005249900402c0c0135014111214400781020418091210042c0c48018007880c016581480e80d507889502c50542080281c070005a160b00400203003001ca042907000d03100381c3c0820340e001c91401940709080d4240f0f074120342080e40e0000b03080d401007003507901c24464001c81e03600080050104200c801c00c000c1012000d007901074240801e50130300c1c009114a0303522242000c1d955110302041700402c92031814018458102e0800c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 562024253 1250 562023003 562023013
    0x50a0b0f072a0303020d0c02031c090f0b03060906010c0803010b07170d020c010509030a17192d111b0a140d030b0f0904080c0708060a0f0f050c03061909021b 69
    0x4259200742c04e104140798020700103240c4102402b00540c0c040005030458410450840404544040c2d0440118020000c50f0101907e030304005040180c11100503050360b0512410409000001d900281503d044580007200141c6400ba1428070404a20300408020714030f403000254055013034481e901510302c03815440020010b40d0303151025607030790384100071041003c102841290341000e2881c94525500070541c8003004180201c01e410301c402e80700407011601300d1144d030703000344081090064120942c00300d11070801e0001c070301c10310650b240912483e102c0040702000301a45015805d0700700240144560b00905146010800a10094980d0521041140040c0c2070a040e60314070710b8681c507990103c50005000080c991107542d91210158080080c94840d40640f10300000c0103079090002c580304910103103001c100c041c0d0518008040741e44040d42074091a140c5401c0c0b001f1a5071000a480d8440c1d0140c5100e5507006005103d1581000643d020b031800381c0c00050640c003030403104442c07084080a20000c8071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 562025503 1250 562024253 562024273
    0x2130c02011a0a1a070c080619050708070c0f1a1f0503030a030e0717150c1201060f0c060203040602070b0f04080319140a15050a0b0f072a030302 64
    0x20109180040e82d03540c3c08110100d042c040a2410325030040c41c0c426020340309141c00c41c560303502c004d084003591002855070000003c002e00021104003c1c0c05201200d84104024905994003802004002d46040108250390344408100078040005160044e0002107442074410300f4401030603052002c4442940340d0301419101803102824006040541d0002000b450600082800450040c0040f16000c0c070b8500c00d420001640c102e0310301181350000c6041d006400906180034001c0e40401000d00088281c40040048001242840c0c081505651030ba2516006845c1e03041c40840709901116409000a03100100380300804c070041c1c1c0100750051103208580d080340e40310044448401800c480141801c9400c100185201410f043c0c4114100416000050b850082000945480b41c00312440c0400d00c3d9228000c0d180c1c0c01069050500078082143c210003805e05042d00801140616041c2e03d80e88600031034090308003c0138100e03084e4442805050840d1a051880060071110741034402078003d030127000e1035a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 562026753 1250 562025503 562025531
    0x7050d020705040b0f0609040912170f040f0b0405030d0618061710020c0a06060305010e070509060f041109030a0c0e0a05040f021c0203010c0e0102060c0301030c061b02130c0201 78
    0x40c25090130010942c421300d101800034810705a100c007071420380c0b003940c03140d40d00000b42074240c0c5902408420350301c0c441c0d0010700b190200c106240140c40d12442c0709a120400c40050f5142e0600c16400d5440a070311502c2c0d444a241c01031540c0522542c4040a50400d04049910401c03c02010455510000c003884a20f5485420144003d441541901c3e1504101191030341441c0c00d4008096000050b41101c2c10f6082c541c58460031103c0d1600101c900365110704c40b04905039020882032000c0c0400b240c0c1000d5a0410900054003640400300b0703140a252551800c000b01c1c3c08034001d0324250b040240a403000000949881e01031400d0301d0281822070b02c17036039020440b0114140705651086503c500c2c8403183e0310381502002941d004d2401c1e5004d1070400c0309402c0b40140c8081c001c40070500364035214030003d29040300019003010401481d00700b80704070500042000c680d50f00d80340411594941003020340b0101c2003084c10b40c22001c281019400841c01030600c41c085006520588103229154000c1049007a10928 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 562028003 1250 562026753 562026761
    0x1060c110a060f0f0c060216210f030b04150e01030b072c060c0115090b011403060405071106040308010311060c0d21091101170c0a0e120307050d02070504 68
    0x30b40c070001d41d00c0011100c5140c020a01040c0310091401d140003940743c4d65030340d003050b0b9000c0c0c8201006910840d91840401916070710340503403000e030020382c82a0f8440c06d210091207081031180400401d915000108801c1d1200c0e4481c101c6440045512402661a04240c03551000284811124150010b001491003440b0704104034810649051817181d11100c03038445600900201c1490350321042c20020608404001d11445c018210b6000c41d01007810301e481100400c0b12a210112418000c100300382c2400c1d501c1101c1100c0c0d000000700d4000071907480d01101220b032900b030480544414400e5400344803d064000382424100da1003009c08028920843d4240481400703140c91110a5030301c03c074040800a4000c141c8102c0072030541c080d00d0401000c0110100645641c000b00b0343e140102c1d40c2e8100b683e0f59200d4103254015103070504203842401c00200d001014801c00b100d0000b004981a03881405948070340603080c0d201d014400700d039200c0358242051511000500d441e800544288400080c2c68100b5004d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 562029253 1250 562028003 562028009
    0x1121403160807172d130306200d02180f01081603110720010305070909020d06150f020106170a1103010609060806090706080112240501060c110a 64
    0xa5801d1101c00d5566450055001881e044642d802450000c03400402d10070050005e03000f2807182c1c1c1307041c0302e02030a0f030002500141802d461401c00c20481400c0a2000e0b0143e8001c0360740c480000100c141d590300b0504046801b02c81480799004000131840000e4880d900a81090707900702c000c000c0b2010351042009078105240141c3d40c0461a010f002581c2c0e40e201c08003101e10300c401814003103a0900542030b400d5495003c036000700d07081801d600c50001080d00500400300e26030000c0c20100424141140090894541807080c0c000e0503400040b0080e00c2542a00001c008080c85a82d08c590024001c00107800b0420340e404540040d0300c0d02100148201c0d085400d1009112440c0190581080c2c0c1c0d124468030220b01108540c1641d01d641c0c0010345030038540315480003030114002800203030a00c10380460900e0a41d80c001000c000d031030401440480031516102d280b2a07031000a80b046044090a01007403045100140c0304140c1c0b426000144550f0400c15943c0c0305807043e880b101084030300e54100044980680 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 562030503 1250 562029253 562029277
    0x102041d0c0a1403060a050a06090810050609180703020901030804030605090d05092806020622051513150b0301180f060518010207050309040b03030a142101121403 72
    0x10100b43c40f6083d001000319040003001c0c002000d02e5031100b0205241c0001c6620900000f061507104000d140014000f1000340702c82248144102c2c1800000603280510181000c072190103140303e076a400520801c10000210350107480480b9540c0c3d2401c00010f25001071000780c600b5401c000001d03030316000c0819440510900c0391259410300140c08280100cc00150043c3c5a440780c20900400c111310041c2c140d00020325075540149414901144075981404c5040d080c0d80b00808a213111100040d00850411580c0d40b402040c001d459480311500c02d07040102c1007018200c1c04400000750407004044c2c1082c0344c4140b080e8024000c080c000071200004d52003000b030191002d054801c0b0400001e040350891500050a8144e421400781941005402c991145604482c1540000355210042c2040e0140d1488001d045024600704580800007400516152001107510140000c2030880c0500080d40751110452400880003a0342c1c4030141e603100d01010902c16101c2410310225540341c181d00000715140755940c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 562031753 1250 562030503 562030517
    0x608060a140102070b090d2301150f06031e02030712050106020a2006040b1918080607120e01020d02031b040b0414041d06060108070320070507080102041d0c0a 70
    0x41c4217000c55000b00c44071035885500b0f2616070011505030100541c40070003e080c84014403102c0e070012401c40701c840d40685840846030000f0005880e1034000441100c015081c00300314900c4282d01d00443c40902500300704898070200034085035035480400040007894144007003180d641c941c00180d07a9207210040051541c0b02c80060040ca0341118403c03140f29200103484181801d840d00000b481540180aa41c6c850281c41c80030880f406900ca80c0520324211140d2006048a0401c00f400382c0700c45d4000d081e9014054940802e1005094950241c040740d21400c008640310300a170001c0038040c1d4820394480040c0581c0a4404c401e4103201000c6604840f082c03c1c08600d01494010481417130802c0500d039545c095070720721400048900100c039484021442c80f01510091608900141100c40b016000c0001c02d07160800501e80c102103403140204013000d500744980c5a094500e00035180c07085c186c0055045500100b00083c070202c0345116040141e03200f140d89655659800d0440c541409042c60b0400040c9030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 562033003 1250 562031753 562031759
    0x3020f0f0306010b1c0c0507020f0d080412030324032a090e0d02150121060c020624010c030c0615081018050606010e0a0806010608060a14010207 64
    0x400161a01000009000d086001001a0000381011000d9000941060002600000300e14650b80361105030500d40e0000c00a903100703968000c2080c0101507009004450380107003441142e42d240b00c40c0e0102540a0406680c440d240d05140c214001c40351000c0f00424100040c0c61080003d1844d090f1074044441407440c10985980c5034020aa880b03805440f001c4180303652036543c510464803c0a010b00b2a01102040d240c0720517107518509040d100a49085400c91101c100c030022805021074115904843c01c0f880d09807203604d540640307d140d400c000b04103501d49001c0510031030300803072001c0c41080300b43c0041c1e040d5441180c04038546031440780305c030b4005400c292120323001074013a4030008045130065000140c0c1403803100d02110020b801ea00002c00540c0640c0241c000d5861601440110b011020940342c1d1090356503560035650500582442d05100401868800c140c8448103402c004001ea4421180d035075079248009000850161003032401001c01c0302c03011070440b00103a441c003031065043c0e0061419900e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 562034253 1250 562033003 562033009
    0x711071706130c0b07050307020f040c09031b0b07050f0d02030f040605161b1e050a050405090313031109060d030e0d0203010e0d2007060507060e070306060e0910060f0302 75
    0x8900c2d03001c40303c3c00b050550100788000e00101802940384100000c564450350b82c0100000d000d81e01c101c092081d41072004c02d5a21079445507001080740e43c4420454501c4140f10703103048603604550050003a410f000b2802c1021b2050008000e01a00e081909031411881d4851080f6124420320480080790b5608100800040d4840c600500c61849034022114015001d039031011804000e584584010050714041407094150b0060414846082c0b688510b41851401c000305500c100c0d14880e4034800c65844001404001c0180700f2981a10800010400d40540742e01c0c14034070840741b101405000724003403030000c0ca280c01c26030003142081da019120100e00c01105410000040480c07a412a00f55490b10200811104100448901507000c0d4480b03800c140752100060044c1c1a030750070b1200c841e6019044c100310725904403045440b4180c10000100c5c03003112048001c0c0c50108035501c0280307420300d415030004003980c03980b00183c0580c50100c103881c4000741e1040f28030309641650158040603d4038080400c0145 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 562035503 1250 562034253 562034281
    0x1031212150602010e010506101209020a170601030c14180411030d0f030506060f1606180827030606120a05030a02160b1318090b0711071706 62
    0x51120903021038078164041200400c0c122903448a4050307911030641d030b44528028003c095000c1c1301503401803141020008001c080f1140c40180c1000f0325a540c0b840c0041d5201d120801c409000003c0214444641d103c03012a2746d107a0900c0243e810704214040860318124402c9a013417001001020317150b81d0090183c40700703000300c8042c008803842104c4008a101c1910103100f414107081113605c0c3d014003031447e548064180d407402010584520b1080006181100484007924144001420a000e03900a6450800010108036020b900880341c200300160801410307000070080150100d003118246462a044055840301e40d40006030726810100001e036090030311184088101c3e190000301d4100c0c6d903203512a20300b035902142114005800c402d10a404014941c00c135180200b69002c8094602085c1403c0c0e07000955182c0540c10b076001c08902c6034040c11a0f280c01c5428243c0c0c1101c000380e80b50500c87c00c0502401042a8981c0d85c90040e400c0000e90042400c58a0414202ca68050301d0240da4404e4012409 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 562036753 1250 562035503 562035527
    0x151005013e0303070f05070c0603020a02071a0306010e0108041502030637052215090e07051207080303040209040f0c06080109140601020a020f01031b0306051503010312 74
    0x2060300c1d00300040c581502203000e00c250181d03030000346589040481004002040c0d41d4050418031404000c41c2c0c0c0003c0184203032008440780d40ca00180c4a0609440407410581503503c51042102c0c607943e02041c0b0f9040f4402140220400d89984802d6281c200040d102e1031800c0b038000d01090f00d600e00180c0840c03c1034005503405140240080c608160b94170821600c0c500802006688140507000b501c203504204460002505048520780d04000d61556150300c62000714404100d140d8070b404106643c00c00b00803040b0050304281105100c07000d2075000d01d40e0b82d8041442498400c04100004462403d8080340c0d44090b40c1c640805149140d849801f403281c5840054822150305502420442c042610000182d016044a940700010307035240226200a0b1440f030503031540d42040480070b000a0f0ba03000552443d00355030540d64600f07801403041c016001041803600c4001d800d0102c0c41408070340c503070592064054420850700d0304140140036410219501090000500c407043c1000b482241a00401e10f0801c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 562038003 1250 562036753 562036817
    0x60e13050a12050d0216020306150603011e03081c051803040b130302060318011a10081801050a0b120106060e090a02041a0307020d020615041109040e15100501 70
    0x1034804c160821030200da00c880c50300c1c0f030038030207070361008045180c24001290441c44138903040600240e031a000510034801072040905840207032041e160744e188400d050000039500200b4968503525076184100040107185186c00d8854602000540e40350410024003c88039040c000070750030a4200790300a080ba03400a030032154020750038040000181e50300001140f14280201000384151401070440f030a5885000c000c8011108100d480d0400b515005402c040c40850707803400043c0c0b6100c2c68602080c0c1c41c903410000c030442d4200810808a1925074211031015881504c0000c4c42c1c3c007810041c2030880301300340280340014007880b5141382103280844403913402603405d80d00180f4103581c3d00c0c5502104c0b0071151420751807020100400103165014401c4050310940c5001501d668900329680751320001e00d0004403841155110018440259010169050074401030810415280d114510346c0d0340700b02083d1101c00448039000004c441e02d000c915030104681d41a107900f070028250704a8200c490b2196044007803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 562039253 1250 562038003 562038007
    0x80f01150507020402040609151103090d020f030109292509080d1d09060108221406010905092e1410031202210711060409060e13050a1205 61
    0x541d1302e61000f0300003003080e074131071000651a2000307201034490340a41110a00508054440980e0030110845105807011a0a1581002944006012402c0800c0301c650190b02c1c107440d507810070039009071100404103e031840606184038621207a41c002c000b1140c50303100801010945c1400b07103840c0c0c0d010580e0701050512603d050341ba802140d2901c2e441040040018034014100010030b100c00d4a8800440703810354410701e140c5840000a400030001521481e24402c2c4d18040b619005286500c14404662000021008a603403107561070b42c0b25020302410034424a01130101e040c6d42c0000540128085092000d03c0135401a001070503030749110844018503541e1a45200c0f05090101d00c00113109010341e042e6644003504601b0680c8440720140e4260b010755105074401c0400e0386030080c0d66500d8840c410b034030550b50202450b0041d819180100c607140c07c800007050102e100c50154106005507100800e900784280c0d900261101700c403000020103019038001c1d42400c1c4c00f207445020b02d80071016032810894 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 562040503 1250 562039253 562039267
    0x302121f050316050d05190309050415050d150b10120506181308040306050f0411040204080c060706090f0506040b0a060518090f0610170703020109050d0c03050d0c0b07080f011505 79
    0x907c642e601d8080403000210551024440c61400f40b16060b0500c03890420b00c0540e5081101050000c1d442a0014195100010360114400000e03000746104481c0500700c000d52452918000e4500b004840d03100302c059050000107115410a008104031031411000d01208a85a007044103184c41e05109090300c0c1d2200400003c0040b541c1802014091810324411000038039040c2002400c1c416072544007480341e4010041000a170000040c02d615251080b02c1ca1540c960003843c00c03200402620360700030070400c540f0307460300c040c404041403031445180201d1035140b2540e03902155004071100381c000c00364404050316603408c1601103802600e82c4440c007401150180807078940304601e04142100c590141114003881400b5000101c2d001c18082c103d80c1008240c51805c60340087c08645a501505024a0341311080ca010310044e405400e00540d04036040d140444814517005002d20191030041c3c44d0404048049510513201d64807552082c15460003141880c0d086c80d9801c055420403d101d0010440b05200075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 562041753 1250 562040503 562040533
    0xd030f030b030d0c0317150f0604120c0e101802090d020a031203060b040b0f0705030708041d01060507170c0f160602121603030b010302121f050316050d05 68
    0x80314005059210744410000c2d51034018402d01d00c4600c031b142120310700c0f0207100c1035890301c2c2c59103080d450040b07900109200300000498981e000d154040c08940c11180528001d11121801c102d082d00d40a00e8005441c0da00c01c1d0200084200900c83c4480351351550609414080866024041c001d0f0010811084280213400080c540c28240c2c00903610007032100381d03400301550148180d80040071514200c43c01c2078038120120311940500c0404081e680000621102000014000c482d10305500c600c6043d1205d845458103a4140c2d4142003202c07100c0400800443c005010b04252880c166008880740c0c582030249403801d406410110018000b481880c030b504005410501c0459094005081032250840c40c4c1030000386451240003c41013101401c021094501501300c090030442030f00350070046006522000128001d1141c0c517208200d0020030014411750b100c4031101c08840c080ca400300611082d448004140c0ca0b000f1212000c501c554808500b0400c908084c0c01e0900003501400984080c501e141c91a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 562043003 1250 562041753 562041763
    0x406091a180109120606080d030c0e060a140f0301050307060305010e15041e05100f3f0f05011401061719111e0412200301020c010b011d0d030f030b03 66
    0x12180c01c1c1c3c40c1c03002444083c408008c2100b880310340d0f14040c0043c122810014008925240126000e80300000d80450003a01803110064500c5907103058a0342c2d800e2a054a10247c0c1081c000e0f144a4001c40100240c45407180c0243e505840500d480c15149803182d1b4402002c80080f042c040ea0000c0d1161040f00c0c2030041d140c25041c203e200e01c5000700d0380b458a03401c2079906410580065207541003505080c841d1072041803407001c003c0395201034150031082080800c00f901ca00114400c4101020001960420138040040c40101d48100028013102510440d40c0b40d40f1613090207007800044c82201400138401c54107101c55000801000410718940701d005140e4240e03541d44480207000c0c0000680e4961040342e4291070319451003150103581c14207041440c0fa100303082c40c0704401781481c2e0456285100c0b91804070014203c25100600031591001201349040c00b030b0081c0c1101501092041c01c0b158030180e00c8110782c41c4000c20007480c0d0b03807943c03549640680700400301c5d410342da040554841080d181078400b041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 562044253 1250 562043003 562043039
    0xa090f0803040f0503150c03070309020a0b0405013207030c02040906140106020303040515370e06010b0909270303041e020109060e01050f030c0406091a180109 70
    0x4003840d6200d003003820100e2444141e0340040c1c002d0b40220700151b01548015800303500003400004903035680d1128a0110080d00d0030b000c029501c1303901d02c10700003a00c00040c8000c0c0100c038801e880302d21044000c64a443c12420026102400250004404000c8260400001d10340b55100f030500c40c00e001c0598020404407a02103804550041d40c40c40c180041d04c040e540c40b98010405480114650f14150b42c580e51600d2144068440f00300040e0041040650030301200c610903182c0c0500100000707201540da4241c6103d6000d130b240384901e032403152220440081000341c182c440d00024149046064810302c00c0718600200a1000b600d000400320140310403064080030b000131240300030b54403070619041001040c0c0088002c0e0316140c009400050041c0d130042c0204017107801509080160190480040c0d905118032500842068000810001300321130300b2000d40b00351507041d940d0720405030300c409400c407410481d80e91250103040140004109040e1500480007018811b1610702e5102d642c40c0a000414801c0c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 562045503 1250 562044253 562044269
    0x1201110d0c1815030b0604050301050f0a0c0e0d0b091f0603020a062a050705060a0201021b030301080709050a091401050403030f1104090f090c0e070801050301110a050a090f 76
    0x10514240c2c481098009280721038000d0b66220702e01001551142d500c034905a091549130680403172241c1e1254252001000050001c2c0070b985800c084001003500119024001c0302c0c5030140c01c101d02d91054912044480c0701900040e655101c90b143c1152120005091a03224421036040c8500d40101d0f20711215404c0c00c50002040d0749045104014500441c1c4e0800010001005c0e2507070103844020b400801d54140c51001103a128105041450900349240c01c0307207410601c00503140c01880d505500030523400c42c55680c1502c0c01150524801d8581c8028400c1800c198040741e014414031402d0b40c05580c011800d4640000c114a240d03868407681141030140d48580c1c3d5460040001f4150180102100c1c035107250400c10190110448440207401640034280c510303941d44598070702c00c8201c1e6200420300e540060f1130a10a540d41c11180000f95130459070500090750724000018181014001c01c112005010181820250000302c00c9550340c2100200400f0411a400d0004001c07035090040000350940e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 562046753 1250 562045503 562045511
    0x1a01021b040f060f0e01140603011701090204150905100312080703091209091803020d2105090a020a12031e05090a081b0111030a0813061a1e01020c1201110d 69
    0x20201442c008059000400c1d0f0355404803181040d0350fa0604490640708bc2c85001c8005080981c151070050501e41c8000b07401c01d1401c0da040703400c4d070b2082c00b20600f00c402c1980180300c0c44e902c109100019542c18400242446074000d20303403500368001c10007203a206180b0703d00041e016501d521072040c1e03901300245002c04078000100902608041b4014813248170040410304845c4002c0c0c0d0740080d501c000300208082040030388075070309407200f8445c0060000c04180b103409114508007840358540713544039410b040348250750002002500902c0204000306003500f6031207201841602d46a01444928804600310070806c04000c00c02c1950340e81c0750503402a060748401450090300320018100c0c6110a807450f203042c4039a0001d1080301c65000000c5a500c44001d20b402d0741d071900ea5051138400c2c00c0001c0c400901d014107256494030003000c00d25604450708405c40c4c0203c0c0d00406059206450803802c1c03c083c0c016000001624040c0c142062200705441007c07000280000740e1403645c490316008840c1e00980c198079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 562048003 1250 562046753 562046759
    0x151206040506010309050705011d06030928030c110111060403030c08090a21030615020d02060c0c06041101261f0b1c06120f061a01021b040f060f 64
    0x2007446000e502c04020f0074204640f81c02621055542c0005118241c100b000c109070320b1100100110803503520a2000d016551070741003203402c003600d94403915031981c1301d0b55503406e44103142d02d035001640f0300d1960161640740350203995490740100800901801410310090610603c12020104046441180170303aa001502143d8510001c2011074090b0034003105504c502800e5010510003408a007c0a0803504040402c02c4401c0c0203030054804c6070310101040208801d8101c00ca9004580346c0d5900385194240c50030760766010b0f1000000d00851802e012503a2240c00001c0014000001d40307020007005041000207040c0408070544441d00001107803650b801c40030241305207070b00b0810302030713150407411401014a5400d100040000f030150000c00b102000c2e0484d00003601d420030b60302c0040a4508200350360525411400c242100d174460820803100c0c01c2c035005034030300361405c40b400e0060000300503030203000180117000c0040820008105410341c0180d0b10300c40e081c03c0040383e2254030001d01041c0c909a000c10b103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 562049253 1250 562048003 562048009
    0x70507050c01020321180f0d11060c0405120106090f020a080c160f0807021815030127060615030b010f020303010509041401020c0d1d03120d050402151206 68
    0xd02a1609056510034008029502c1070442000b1041070320141d106178030b603968015044a038103454054042405a002c602685c003002260f98190241c503a1604d5910318404e1261690354a006c4901c86007045040c4824009480c21003000c11443e250500041a080d88841040049905100c2c1400c2d01d20b6001031501e10760368000030825030202510181c6414641883d0111a03038020628000708001c0c034044074541000b5425042e40c03502500580540c4901004035080e90030048145d4000c1030050100d0032820681c5014050700d032400140108031940349103912089002d06188207400c4036129140c07900424590001204148034022568021900958000000d885150340402c01011900308000522480d05d414031400d4101d0b0b4007103403100c2e140740c500c8600d0740280141515106030340a410b0b5000c2c0e00c603a1011040504000c0c54480f41c5c84100491b04142d610409002280a07983d0140100d82101c1c07850b90200c1d9005002030302d20312201c03668141c001c000d58062447d5035100c49801040c06001d00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 562050359 1106 562049253 562049263
    0x20f0a08100501360c1115040c0e0114060d0b093132060103030309060f06050618010e0406030f0210211104030b07050705 54
    0x45000d44114000d044203116801300f5001449003540070165040703c50010b0041070650200e107a541c1c40c0c4003c05420b48490765020b00c030f030305075001802110034030487c00c200d0400344211546c0e1510380f5000d180c8070200e03000030410280c40401444605507604e0f84411b4030310b0440700f0b6a10740d81d0741c0381c154010b403130a030b001560854580420310601880765002040300702e210000c601c120b092032403c1104024504a0050407510340000c480c0100c005102800041c07801d820b900d01e01119502c0d0840d40340c0786c0280d0044000076076035545c003030600006100d8504c40c0940d1081c00c0c41810300d008001400c5021b03040408092001c0c0c6440d00243c1e81c011400c00b00c290201030400c0c41a1562403e00103043c21b01140c0990040359a04190b044051140701c6d5814442e0300c842006002c40c082c030700c060b002030a506074004112001044040b01040c490201c0a1040c1d0b615905c460b902d01c9246800c4d4105 = true := by decide +kernel

theorem cover : BRFrame.Cov 561870503 562050359 := by
  have h0 := BRFrame.cov_init 561870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 561870503 ≤ n) (h2 : n < 562050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
