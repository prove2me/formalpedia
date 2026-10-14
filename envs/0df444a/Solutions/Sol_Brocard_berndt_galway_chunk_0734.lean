-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0734
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:28:45.991656+00:00
-- url     : https://prove2.me/submissions/74db63e3-5a57-416e-b6f0-2d74cffb88c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 131834532 ≤ n < 132014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 131835782 1250 131834532 131834561
    0x504020927010213030c080318060f0c10090b13020a0302121e03070c050f010c20030a080909010b130303030f0f0c030c0f08010510050c0c060c0d02060603031c 70
    0x210303541406509202602100380c0d03c010313848030350307003941080116011941e004900c4c41e841040081c90001030b0121103e001e400c29100c094a40420a0b00c0f100c56000d010402c1e41980300340c6010300b04480050300b00081d4903026100c402a241c03503880c0c4280a11440810294108a07148820001070a00d030051183e40c0c008401511000203030145800b0b46002c91070300b010450b42c00865203c0c00c3c0700d0061102d00043c80c0456070203820030070034000a000b10010400141280241443d800044624114501020100201624150703405031912030803d403c820300036806081e5000c004610b950031402140c0e0a0001c01000f000d00910f940d6040340a0045d192032180344644a03045049807a40900828502d50401d483c081021800004014104018900c08000b004030000041000d91103500c00032180da421840c1459850344120754161400902a10507500400b0000c1c0c81e0059030000300d1100c403a10100c1d07095680783d0703c90b00c04147d501e001e840700801486000c1d1320b6003c90400c280c0e021649502492 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 131837032 1250 131835782 131835841
    0x503060316080706020f070f051c121d040603050c061b0706080f10060909020a0516121103070c060c050f010501030813060c050a0807080c01090809100305040209 71
    0x2085568040903103502c840e120b940190014007280750140140e11240018000400e070707251400d503440c01e04822a00c120360080440c2d251800301d0380b0861075524942500200181c0751014981d03c0102825030310004101461440d2900701528606405100101d90700f00c001404102640030802002da030050200c400d240d0007800d4001e0804d101804404028600354880c0901d519040d8446507046a000b0300b0803a000140303100030301c402c98010b20f08000762131140348010b07100c40a1a0003030341c0c94800e4040c1048002590501440bc111040040c041045640d03540c40e098424240b040035500d00441000078000f8502007002e102081c820040700c1c0446004008490444030022001401c441082e0010b94240d200000d14181406401010b08010100f920f0003550705155a1a1584c88842d114001031400000203803600c240311180041c0c1d580118000002c101e5070b43e0610b001d4609a11801280e0f02989400e0f1080007101c0c000e02c189841a6005460001a540d81c1c91b00c05800720000e40e8030b5002003140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 131838282 1250 131837032 131837053
    0x50903040e0906100503010c080403050315090112050114100302090606120a05041b030b010905060103021306030501030309120b070f02030c0a06060810060f0905070e101d0f0303090105030603 84
    0x9801c0041e0040c0090400b808080c1071072100152044030540015001c2c2e070500112400307159000d40059445a010703e020b80e281e407682d0030320040101620b5400c5074030083c031a0001c2544119001c0300b003d01d52241c0c008021007030310503202200c0301c4800c81c0d4000240c68000010800360902c1d408150340000014982032600c210507408003510102914840509607944003088100013491140a05041464a41141c4145180c0c1d40d802130340014054040c0450302c640208100b07034020303019030700c06214200d0403903601c0d40c8800740100145000d100c164000360703115500280b0880306116052080c1c0d00401281116551603800344c0390718a900f800b0741e0840c80104286441018107000d0307415891b12840011503201d01e040812441e1004850b048090945409410000b2100b840550022506010800f01300ba541c1d0840c182c1e194010712810b542c2100b0712001c0e41100b2079100000022103000da04080134600501414401c0c912050303c5282c0e0164010401d100113036000300051039011500800f250f901d03441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 131839532 1250 131838282 131838299
    0x304120f0204060303030504170405060a1b02150c1b0f040e070e0901140901110304021c0c06080708161b170a0201090b0c120415150f0f060207080a0605090304 70
    0xf181ea000b0340003c2c0e0360704240010040754610035241c61081e0705255062a0400c40001c100d80b24400c4a4414004140260241c01c1040b02c1810242030f0028070314001050540c9503861254000b0b144040d40740540c0f10014411070902d02042c90302140680000e0705103840c1000d00c4000e041aa1304030030544208100041c00c0000d805070540310310650f070004105240c0602c00c07030140c8180588009400d90400a002040d000940c083c2ca5219404031984130312040914005030340f8500c2c1c00700c09017040c44000400b0505540040800d801104180d40c1c0f60000d03656200c0d40c0107040c4a04d5000f1000960079044030084044641c180e0040d240030b04031504e404400ca9007440b220780c3c00200401d002d81d46840c005006e10600d61301140d800011407600c0351604100c511400c0038400014070051000540441040c0c010912394009d039110b80840c0d4182c541e240d04c4401c03122141c1d1441c450640d01d01080f52010605504c0458600115980d500042c0480141da0340d03540090240101217181911092100081181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 131840782 1250 131839532 131839541
    0x1b170c100906020406120b280902070c150c020d03030b03030408010e06010305150c0304080f0f0c1f150b0a0c0803010e060a090212040b0601020c03070308030f09010b01020304120f0204 81
    0xb44145001642c0c0e80c90220301404101030540d403190003d2034902007c5c020780354111141a1144840111200045030300d401030f03040281d13508000c1ca258400310308003081203040078004041d02d002090350315020a03078a90485100d030000304025008042c1104550019004c0d402920f81000014152418140c03182100d608503421919074000d9640f00700010018032000f8401d00d4043e40c0e020b0b4200d4075078601107400b5603ca100140c40102900c50004010140341030480030ba03901d80388201c03ca150f9580c1d01e01c0426540d00b85182400c3c9841d840c0c0c10700d9120b08001c0c0d120f1030030000003042103030400030318215a00501e0382000b5030702010f02003002a000c00241400e030045000c0d040c40306085400742132403405d01150000c1501b15071107441c81080010b04580d044583c00c3d0344240c3c01008044a9582c0b800101d050084c461074440d018892104084100000030009d5880380280380100981542c40e100c80310b00340e900d00104070b401342c0c00c2040140b1210012002d8082c596010311207100030105c0c107a0105007202e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 131842032 1250 131840782 131840801
    0x30c05120a030207060e0c03070b0307020313080c1e0f010c1406010e070206090c0a09021e0a02010603111c031115100914010f050402090301090c08060402011b170c10 73
    0x70f580042c8820400c011803003481c50b082c052500500c42c620070140425964a1603000300c541c00c000210020b51110320070003c941c20100c403401802245c9590b1076580d9078680c1c1c0c450669100d0400348049a0200070400543c20602800412101c3c02030150001903c0703000510300165031a0000d00f6612406c503a040210078001d00e20b500480e480741c90f283e0802410010007a0040700590452083e140b980c3d61440346800035101142c000513600d152520311203081e000ca003000c80d850316202140300e00c8d100b41c065001c4000c41b8000c08400d40085d00b12030800007280303552000100c03e1a881100c41700030030310840c0120210b408240c1280d103441c940c52500e20501d032048a65410404102c4070900c0a410304d40681c0148202402100625506040a03200c01c0280360113928001c2d076003c00c0f101032a503000d4221150454208444000c80754440d400b50351129000c44080c0e001c110403a910b01c0420311748071105c010031031300b04a26003a085240c00d071902140c0d20030340d0b01200e607125010004103c203c692007200c240 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 131843282 1250 131842032 131842037
    0x1503150903031b0304020105120c0702130b040c050301050901060f0c08040312110318190e0906040605060a08060c1605150907061d040f14040309030219080a030c05120a 74
    0x164604450f1281400e442c401004082d01070500038400140d03080420341302c1e142d441d2201c0c50042e0f0f44010004100f4010b0303480c007030b44c44a012080d0076001e60301580604059003081c0c03010f0212050403101074605101c284204d58204c0004801000154422094400003d40d9854445100302c003a07268503401360010341090321286800c0c910085240e800070070313009408500c50099401c0c041808003652060040c0700c5035078020452a00e4489412250401c114050226002e0100890508025865880a0454003103442602d008046080c500e031440c0303480c040b150520001d1503199504002141c0c990000d84080034100d4031049583c1c0020010b02521182c5c06041c1d481013107600c0e10074862480d000950b0300c080184006111079400b011652449004150320944001c1544409140018000c281c16598503444c1424401800304250b03020060000f16802102c004030700c885142c100281c08407091182440c02c0e8003048040340001d010fa00340c498418007c505807910340c12008820f00f100c1d4007000c820ba00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 131844532 1250 131843282 131843287
    0xa12022d0307050d032c040c0e03061008030406030209040b0607050a05010506190e13050d05040f0e011d04141002280801120503040f0902091311031503150903 70
    0x401d003410041e50000b004100c5000c1c84851882c0c070050510846d580100c0980305503480d0340c40b040040420803003c0100040c00401585caa01c00000b0146889064824464094100410928104041c000082d99003103406140f601d880c04405070003e60200b200c41c0d400907190a600c00160f940c0002909006004101401c41442d046c0b17003507030071104014140340c0719140562800c03120805607c1204259501a94080000d0b141c44d10110445002a40b00034990304c95540d03008405039002028000720340d156a002c0c40703074076101e40c941c2d6820300d402d01a500c0084518055500c02200f03074900c560700140209810200026003c0c04281080014400c801602d90002070090b41e8601e030022075050381556140c0b4403040b40d03041c080101140f030184103000c09619800584d105010b41401182e004118206c0d050002c0c690b2201500040d400c2200c1051180c1516068900180c00d6070107140c000301c0100c0c503001c1c41d641e104100241e6130b007101e802c4160980f00300581e204202c00140385050080141070003c54 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 131845782 1250 131844532 131844619
    0x30d0f03050a050108030306040c0302070203010606170108071a0a0513030c29040302010f022503060f050613020c01020c1203093706090807120306080c0a1202 70
    0x60645002034000c0500070b20f810010465800c02005903508507004403804250750303019800480c00390140c00c101035030552070101c3c0025003e401c0440d5240c421030346040011640c0c0e171414100c0d11042d03030744124408558114440b0410a08001c0104124180d0f400c20600b401003082c042c44054030345030400c5484424040c024040301649960b950030348a0980c502c4489011260003844140c0a513100081c10f00600c41000c0c68074500034414107102e11001103002d00c0a80800c0041c40c56141c0318801614110b01d80b240b45022142d0382c0c0910751044401030070701d6101f10143e03030a90300258421251080d07030703550034003003403c2164043c0b000001c7c90281d41c50311034590401400c624108a1b403105501c0c0c0c1400300c2d210341c500e0101e4401550040502c080e5028202c00158181071018041405000301841c0000a106040202504c16a400a0170030395040203002d850704001a0f0f103074800001d01c0d5010305045402c0000c8500c41d2a05101c0d584090503154413031601d280c9480d101c0a51144995034000d0151085 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 131847032 1250 131845782 131845787
    0x20a1e05030105090307081213050d030902010e180412030e031303050114100605071b080a030305060f010203090409110904081c02030103030507140f031303060605100f0f0e030d0f 79
    0x3d40d0000c2d000800356143c0502d640e541c1d12a8440c0503c81442c0c921158001424825124504642030740c0010540d07401002002e030090050107003c004901240c440f4101c41741e070b0300f00b255010042514140d54204140c440e0380b200320040203c07003d90341c205615040e05004000052014000e040c0b84041560782c40c508618107542510f49040e98005041070440410181c00240010130040754043d0800031350300c038420706010090b00700214000404d0401da51001505803c0014524009400307594104815114641000104038081c1c0034580142d00522070301c0b4039460650305c5800c055114180548260075040040307141c82c00c2c00c544c242c409580102e45031844028a00f030000c01d0f030b9087c2c01c0441c03942d811070340e015146018140002c0e020045144100440080c2003002043d107040000440b41c44801e00240808010f500d40412202c031414448000b40354141024103c02070400e90b21055a010b02c02c80045840d034003d520503804115103060b1a40c056242030050f80301d030500e00d030b488641c0c030152000301 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 131848282 1250 131847032 131847041
    0x182e0302011205070504050d11041104060314070e100903120207050108090106060c060902180c030603210d02030603240403170709051302070804140f0108040c0e04020a1e050301 78
    0x601c2e01e050405040190440c0d00030101c4081d0340c030488400300c100f1200e08001d19041511040320760001c1c6032180d001100c4c42c4902c060022240669400e0040801e141500b0810440544d002404900d4500b400c1c0194504441000c2c0c5004d81c9103085d11019a0381e1b2103004100c5c01d600500b4000d60800e0b042400303507591101000d603101d4468002804200c0c98080b0040603140345420241000e691400c11004641e280c000045000740e90114039655810300000b0074502c0c0d841a42e40c40d11038441d000e084d00c084100200d448030a810001070302307418442c8c240d283c800a580b00810f110784c9402140900c5680402c01c018440c1034100e0764540d16100c0c40c0c607250140580750282080d1808240c01e0040103080c541c41415182954020b807880e0183d4241185244040d000c0e500b001000b4400208001c03440c414a6125840e25030011269042003420b460019100544151405844005600018054183c00317045040c4c01500c00381000b807000360380d441c2135080100c640200b0050044079501c1000740e0310b024080c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 131849532 1250 131848282 131848307
    0x5120d090203010f02121008060106120f0c03050702010b01021501090203060a0b0d0e0d0e03031603051b1b0409150213090207080315031f0b03010216030c0c0b040302182e030201 78
    0x44480c1e2803402c00d40303401e0b5510014030800c820412035a9440c1e070692001c0e0081c0f1882c0400cdc160074880b6070001d22000e409000c0031035500d4010b40c030340251001c0301d42c030006c4e40070600540c00c101042c41b642844141c8000e503100a0a01d0340010307003140001030020061000f0481c00303a580c2d100080c2c2111410710b0038240f0752503614001c00c1008100e0720003c6030341c01000f103c0c00b018010781c044034070404602c7c2c103542c46d01540758201c10080c1685440b096803c40842d400c20440318614160b0350486540d001c000c12140480c8000d080007420881d2a4801d0b8125401410003090560070f50300c80396039400e203600503644440d604581800b00402071012414400c18101c6c0100e030224083c0905415082c85d602a0140a20b049d180c0c1d070751902c0140c0030781c0d142981147d00500700014007010355120b908016100c01c039074240446502201c5600060f1400b0305005030f5080d40e41c000d0401c00b4000341d00802c284218005080407984010765a2050100440c8545c3c2031711140d20741e0082c4c2105491400054010040d1a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 131850782 1250 131849532 131849551
    0x16050604060801060309050109051e060f01080c060a02010f020a0c0b09010603050c1c08030c0c120c0d08070314041b060e1f0c060509010f051305120d090203010f0212 73
    0x3209101d201d030842241d80c1550400e1400158280407428824058440800c020b000c038010f40038808210700010307400c0d00400c6190f10441c2d05a40321807039451304650091080d40e1030344d0054190012149440001409401c00c14800490200604019001284e102603100d10208644852100411902020141c6c1c4441a000200040d40c07650b241e203a104c95010f9082440f591042c214145454003441980700c240341c0100701d564503844c0c008881e503113551000c95401080d11a5082011880507500c0460fa41e907600708015020a1500340001d8603140e80241000044c19207803040303d4000311507210003c0c40303580a13081e8003108400d0000807580034102908104108001c1c10001d170810740380c21034242468070200344440c81c8601241011602c110114030001c00e02c80c1030405101040d41b05411080007070244110400164903904543e801600070b0f1100140290404920807118240100190800342025500401d1707540b003e50000e42141c025425a2290702e6000c100b802610840300c0d01141e0021165 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 131852032 1250 131850782 131850787
    0xa150302030103111e0108190501090902092203141c060512030f040b09010e030a081908011d0c04090f0203010f05010302070510020309031b0a03110105100603051503030c160506 78
    0x8a03110501714442d280c002d040c040d0b060003144280d114030860792303070340c0354100c0c42000b1650311059a003000c0d00d2100c0082c1e21032594280803602284079500700048440d1058036a00d589000d65070143c98140000c4502d140c0d4030410b004007060144400480c2c0c00e4800c005000284281c01c110030012821621080030301c00358400d00040c40e10000d5582250140d032800360401307845000050048894612548100350140034420300c0604020700000540480324007a42c1e41c20a0b03e444a030b04994880c0244101c069588102e0350000700d0300300402c10180c00007060000705103099213404c00740050b60807041e107184100b03a00000402080c800360007444e020707002c00d181c00d618040060320780741d55a00e00006c490f031845170700201040201c9000c004076442403621031041e4920500118a464603222a07140a0f0701099107045000c070000300c10b224040c41a401d01c042d404006007000412402420300520341040d5000c0d90000704450383d01000546034071003c00008005d030750501030f02202c404840741d00036400790909 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 131853282 1250 131852032 131852059
    0xd0f06060e0c3c0301140405040312050709030503030903131205071721120604050709090b03030c03190906170c0a0c02090c040918020a03110a15030203010311 70
    0x508222880c1c1c002000915035a100050042460400c50303110591070f107407085900e0000500c07183d020b141203d10651000242c4540441803000341d69086500170001007a90002c100400c0565221343e420505a00e0546484c039200c0e80d481e45103030700503541030b04a60b0020079082440b03006031001c500034109c14007021104d04810703500e03140e40e003207240644603440c1c0c2e0441c40c0b548002130030040c848101007044100c070928180c00c500804250301425400d00810090b03030014490f4113090007181e000b028942c1d20b0303000722460310360f600d0002d01041c0100e82d8107000410000c201d07020f00700b0281030f91010303801d5002001601c113032003c0d02580d1180c1c0321a0500440e4074035113481c4c0741e5050b952540143c00e41c02560f030391000380e00c085450082540703009512544c400d0074041500304020203401a5070440b5810062140c08a0000c2d00314016880000c1d8001103150050000540030b68030102c6400004e04080086521200e5015034a00000d00520000e54080010001e01581d42d00b0443c00702c0701a12400b620380c41c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 131854532 1250 131853282 131853301
    0x6030b030705010e0f01050a110303240d0218070905090f0603070806070903110409050f0f010507090506070221030c010b030c0a03080910020709060605180907080f0c0403020d0f06060e 81
    0x421405d5418008041010280140070b0186136441102d0742c0c090b070350b40345041c00e0a51144d117503a0303444402c0341d040d03000c9030140c9040c003080c80100706070024940c00000440d000f04032650400242020104410034000040c2d649414400d6401682007241800d014500142494500490f42e840078041c0d902078024421920342000c00301c42aa50401d00c2080c0e600301075404100508404070008204e44541c1d50715242100300800d03004800007400d002800541c071540c2d42211045a40e000700c56001008000007001440c0c40c002001e14400300010a905080300140e480381580c000c00a54150f917515031141e8100d501d814085880400801c89050903d14199102c1c14040e000d00310704180100b610b400e034045914020803140d13000b010748010502803030303481c3c90340248560050705056003e2251080c02003004e1a200318460b100b2240c0e55140b04d966501c07a00c0160074000083d024041c0320008110100258441800010314540194200358641c042031400c0070403070b200359010944c0b0360603500901040c1d80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 131855782 1250 131854532 131854549
    0x51c02060703081b040305060709061d0603091e0a05010b030d081612021b0c120a0f11041503110406030b011712160215040602030d1d060106030b030705010e 69
    0x1501880e02c803c00e03036200d110000300740f454800d89644405002c81c0000c104040014036902c00d8607140d0380c51708069580c06003070b80c02c14000306401c6500e0310907414106040c1000406598040113040444100400380840d60010800410285c00c039a084004041c040c02000d004055190005800803d6840d02c1c2060080004201801a015284202d000c40000d10311804840091030500d040443d61003150101402c0c490120700492022401358540c24003141c940000442c10046444010f070492600c20355a07240380e1500e031a000c8690702100341c580017458540c4d211385c6104007151282428068194109568040c0841a110b48150304001b000d20000d500740c140e503411510914450079241640300308181c10024848003512035454003292002c0d101480031951441c080c002d83d614101642d420704942164802c900070940917902c00c00024051600c150f100141c5219003400c005007074250711101c5401c00a00781d0182000170b4540350610354525060008130002c11090038000b006102c00700c086446c19 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 131857032 1250 131855782 131855797
    0x110f0a08010605040302011b033b010e090406021b030418060509040c030b071101050a09031808030f03041103030a02010f0608030405030604060902060408060106090317250c09060609051c0206 84
    0x30b0150f080640c04150040302d250403540c800c03012000301d40880c01c40032203e81d111345e00020000c1e42c03000034206995010f407021503802d80ccd000e06011042c0e9078075250380000e940452035584001f0046100f0300c50040c02032000d40b0150215400c07184100c5150742c80401a0780c1542c000501c40c18a08003400002050030b130b000b800b00c984c03180c807090103640c07845000c1c4c84500c0c0b04501c56049500340400c00100c0c542d030f9407103450f1861281d2182c0b0940700c403036101812032450300c0c01150344a5004201080440207400e02556200f840b07036450981404a60001ca411038108031007100141c0c3d120b4010721200300880c05000d01030034420008600b024a440c002030307500c07400640082c058955580e1203005640b00c500803180644a0601252001d5070746850007070841d010352102f5603d013488075055441d4070707500c181100c1300c808034910b0703040d44044426040030703c03000c0d01d0500300c61600100000007903415483c09844002c00c21a10744510161a0606026140307901600400302c1740c01541081005070749007070507507408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 131858282 1250 131857032 131857067
    0x50106230d0c030612050102030f091207030e0f13020d0b01110a021302040b03160807020604030e01180e01080d0215010806040b1b0409021b011103060112110f0a0801060504030201 79
    0xa800c190041074004004d16003110074568000300420b0140181500294002d0007440d540d42410b80e40e4410300d6850350070010a00384044010801700022a20400c1c24406000303000f82841c0d01134002d1000102e03810030040001900d140c0218400c4201c100364400d04480c80028241258216918080382c0d03100c10000000a00c42c025008080c591040a0b81c151006041500c0c042556400d1003022100321410180141001845a01c0003402032840824100d026551503203840200840004c019656107021641c4003440341f40c0580c1c001103120030812007500801c0f041c2e024281c6140d84c00002030400c10381c004e000341c0d00b17000b00004201c1c150000843d142d0291300034000c4580c81e203541042a203c00c3d1002804842d44a01181c00702c1c4c410390350b50003001110316202c9500e0600e1026910704e400d1382c408c031002c580405418800101e4a5000b0340e4180d410380040c00000401c1585462074bc06543c0004104617209a004140b4605480c2c010f1030040c0507040300c0c1016400c2610f075900082042040e110048071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 131859532 1250 131858282 131858291
    0x6080d11030f0f04031a100b160308040510050a1506020307050c040b030f030406051b0a0f120e0d0f02100513031704080d08041205070506060d2301050106230d 70
    0x3c1401c4240d0070f42d0051a4000707100074140003a00300741c029012081d901480c1c010303e001d40010308d1441a02c2205d0400c10001c1a96019080d951400d60b1103510007401501c02e401820010b14001042e880f480d84902c4520350f00040d40420b40350b940a08030700d0354210000351351041007900e010a00016040b4901c80c4110342c08110884d1400210b810103039000080d0200344000b041c0801e4072038020014040d944040a2148204040600d007a43c1e40c10b910800070306400c1c0700c08840000f141c4103183c07241028003207081960081c0e03480004607103810350600041e182c040410a0103402c40c40c0031109654030b6078076450658100107440241880f1100c99102c004c00030700d00d4201c00c0c0f10700d802240c2500d005100c1e80342a51100c0b404100c1c041d020240484044403a100c40d2203001d4600c0d4025001e0302c000c960044001e10440c0d03a50000e0003800050314100340c1c0c1d104c01c070f200504140c0515611003150150704000203e2a545041301c05000d48181d45a594401400301c54a402d000c41104180d600640b140040400c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 131860782 1250 131859532 131859547
    0x20c06061513060e0103050606120a0911130f050a0204030507060e130606030911040e0309041e05160909052e0b0408010608060a0501050604030b0403020f03070606080d11030f 77
    0x91900c00c0b100c0862024510b0035000075000e410400c8000c21000a032001d000c00e544100030081d4038031a0403a0f440042c0056000f01b02c0308c00d210361000f01c40d07a2007142c0e90182085080005078103105e1110342c1200680d02c0300307a41c0100d03d01d1070140e9030300a81c041805604050950f03403401e45480d031034003c003000c0200103402034416603a02c00394025a210008010000d554550710f0040c06445403038001d48002803196482030080c1041c2c41540407a60005002d141841400390420024024031031071144048880c8450800450a5100c1c4501540304800044e810142100340a03140340307000e40c4081c10300d40c6007008220b14080100c1c4d80801101035001c000d0b440403090a20a0310314030311500320303202d0720b400800e020404000550100090350500c108039541360707a511905800f600c5090151a07000352060004200044106042c40d42003442801a14603004c44060030f1843c42e00440c0060b0784150301c42204115010f414000300d040c0d2046480c0008409900d0400030390b170303403003440c2010707074210350004200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 131862032 1250 131860782 131860819
    0x1501050d0b04050f060f0a0b0a030213090501081509010b030303040204020307110d0909110309030a031104150305010f0905060906091012050a03080f0108120a17180709020c0606 78
    0x5095007034010420409402e22070b41c0314009540407034005002e02c11807090200c9030700c0c00041210441e0002c0c09441e250000c00801100a9080034086c440700100481002c55090054001c1c24007a0058030001c040100d05000e800d6101b1402400401050345440030200705510044200c0790300a405540c0545d0703a0b12011001c541d001e059214a80150013508621000c2941c400351580449082c44e901340007001c00e42e6502020340c4030941f0902c0003903004010120b051030003500108448498000f14508042d958030140e400c400304480b5400010f0741c1e890042c000c006c000341d01d02c0003070141c41c1000c1242d441c00c600402c50801d0040d060741d00c1112603200180442d18082ca014014240a000042e142080f03850502d54802c500c21040f80402c8a290014a0003038140010382c1c1241c0b002d8004082c3d510000c40081440d50281da26001044007110345030810f1000c035820507001e203d54404060001076411156030905007290040c030552801048034407004100014035641012040341d018104d00350701201c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 131863282 1250 131862032 131862041
    0x70e060702061305010f051201030b04061407050c19050d0e060d0f0f230106032301061d0a0506120a020c12070b091906020309101b171501050d 63
    0x394001c0340043c0b0404424034000c188011194280c9490010301907002c4c0c1039842d0f00030021615030400b1000f00400100d42c0024001d038000d8010100028250b1490030340c4903480c0350482d820b00c0440d80008a081c1a02c40801c18601b4582c0c002203950347c0060b0710355686071910071440c0e20a041100380180c45506940b10380480b100d545158404120b15013800e9601030251010440030030a8910300300607051a2624003807107240c0c000d403903907060760303d81c0c03d100d002d80040104994031142e0f8601051a001030280030026280a88110b84511040c890744c07082d0344829040d5000c0480c0240d14004080090740c4800094440d0785605d030141120300d54600d4500d00c000c1c01040011902e0340714541e90410740a401c4001058014014407148045d59074249070165110040614210140c020380800fa01141d0f0707550295400106000940720303402c05580d095030688070448080031400704854000100035412101443e0703151a84807458110b450b001042c0080100c03100d81003030610000198503c54401640c0c070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 131864532 1250 131863282 131863297
    0xa0605032d0102030903040b1c060f0905180606010c030e0a121505040b0a09020117010902030129091c08070803240307060e0612040813050117070e06 66
    0x1101d0195507400421840300000e00700d50709498400e84034a0781221018022030f8483c0c0c5c44880154541840c140c0f030824203030b00014030000440c0c4052040700d030f810802d0052800030321040d1849840d650601114604032107010b0182001c4400c00d4203180808940400e000380d018009080010b8041224142070314920034410301240e122885c00c10200d0124580072a018405000e0009000c004100d075580201300c0e01c0a880243c075103420400041c0040140303411006980b441850010400c0d213003c41c2010400800782c100601c4c00d50040014080c0b0188403140202c20b901c0340805030b0000c1e00c0240c3d103140381d2103201c40c030b680510b0440f07032043c20f174980c01c0e822500b03910703407010501d6554425801c0c101c60715003042c1ca81107410400a907101d1861500004e0740036503810018050800985000e4051b00c6400b41c14210030381000c0c1c2800080102d125922140348214001c0c0c1501c0e540700c0010b07428442c0040e4a80009041c40b011813142d481603050707a41d80b0395020b90241060740001c0d9102002030340034010f03180c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 131865782 1250 131864532 131864539
    0xa0b060a08010509010f0b010f090308030c09060a030c080907030b010308030c120109063b09010b030d08010906120b34020c0a0605040812090f0d030f020c0603010e0109050a0605 78
    0x2404c2c0480040150f00484048a007000200641c401c85001111018000980600040d5200e541403001c284410011b640011926403924035016079074000c0b4003540c11921400000c80c0c0d4465811440d20703088016240c1c040d1f00301c40a014102c3c215540d50a81050601015200b22400720004901c11204400c0303c03030015000c41814403561792480c3d61070242a150255082217001c1c0807051180c1d21400780c4008002c0e04489104d40b06031244a1070000030b0a0041c4900c2096407078100100a940f000d0090507034500c3d440e41d6111243d0306141c0201c050782e803560304c15106908507001040201f42c40b110070581181c68200204d0301e6510403441041008a4a0702c0b071500547d0300d00c01110100d40010385000c1d4807106a40d0560b046d40d442c1e500342c420380168031981909810000c20819000103600040c4002c000080c484031a414410011502041800108402044002c035801000540402c014180710000b1190300707107113604003290380d0b2401d46c06200d00415a0745400c00324605901c19002a8003a00016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 131867032 1250 131865782 131865791
    0x1a0d020903010e0304090f06261c2a1212060b030a0e010c031109010c020303040b030c04051c150b06070f06050a150e0402060a141c0c020604050a0b060a0801 69
    0xa40c540c4035402889400016072414145001d441f1160007103404907000001c1461200042c28140903c83c03580302c090603800c0c0128186841e80c00c4d8240d4268140381c1165442c002c0d20341008426113500e11046620000d1110351701c0f44100060801c071400310340c0780043c0c40c1c0085280c0c200740d0300f01d01808440d000350145c840003008108010b412030340055040c3e070001d0001d120040b0741170710907001c841584a9110081c001001226025401010740c000b4071803003c0e00312841c140e0b403803181684640040e1000c404150b000101040700d458048031540f010400103100340a250701346d684e40e02c038140464003982a400d881c1c001240c40e990390242a83e52540d0450001800324520785061001007074100d4140c440d407460008400a00602c5c4100b16094902c81d004400541e00c40350200714054204200d03000c00c00c82c41d0548160411080310181040b414034011051082c4402d105c0c640c241d0b01100700345000c6510440070040407075000103a020070035400045240854a500700401c42c050a503822280c0c1e55800c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 131868282 1250 131867032 131867051
    0x60319150c020105040b18060103200a080313050910090504030309080307080906010b1204110a08030c06010906050d1110020c180405060604090b19061a030609060303041a0d02090301 80
    0x190003451140744211002e40301b958494059820040003000c040056911620052000402c2d00340201c209a1160b000d454492203a43d001034614a80c0b174221100e26080421810540d07003030900002d010f018111203d00181c684a603107440080e089100b2201e80715191700101c1c042c103010390301020748039810024041e07603413034200c90150054400b510000210321520000003118031652082d00c8441c0600d030b20130f603030603215501c030344800d400d1741741e0f034140d000d42102000509491b040000380140e0082301c6c05002c032907140000d603004650031a8001809607541512000003d540c001440e03040760710444120ba64086410f6080b0720b4031800c090308980001122804100c01025200c80900c9a8031540403038206544500c1408260391a54000410181c81c1d48041289000c22241c0e4000310410050000b500070740e2000c2c02c80d88002c0c8030ba5507151044000082c40600e05101489070340c0502c09230001c62030245808085102054200e0810365030240214030740b400179849404403118288010001d02001c4030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 131869532 1250 131868282 131868287
    0xd0305070506090607022d071212051804020c0a1709030c06090306010e07022425091203050405060a080105031513080306010c0c060e040e0105060319150c 68
    0x312900660751446404009215040c000900c40c1c882e03003141d405840c01e64404070780f4061021085c040c0074030303020b11783d102d1400f00301e0f080200c0c1009000c00d0700303482040d40c800d05103420070032020744042d010068100034035030502d525a0b60403c01da5905440040c0d940b048018018100180048002c0c245480c8840c15821115150003402c1145800c07015503010200240130400e2512030604165015086240100104510050665840b860302d006488108620040a0010a130300030000e44006151740140a800140c415200d2400703030200100060075014500050204501351041d024100819a1043c04042c81181030300c0043c14007500710358440401040103070061a0074000c040c001c2c1302d4119400d1700a80644202809020f1039850f1030700f4140359807501d007165800149130341d0502030103000c0c010000b08842100c000422142d901c03000c400301c01804201c162600c21100d0420b60b1b04060521089503404079200d4010325508010000c0580341e4079000308811070060404a5151801880c14041038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 131870782 1250 131869532 131869537
    0xc05191113060f03020409050304080307030c12020309031c050918070206060d0803070c0317070309110d0302031605070807060216210201120e2d0304060c0f0305090d0305 75
    0x81084070884040c00048507070340210b402912600700c03600d800746020070140c1000c0e400004058044e4017a6490300391506a182c3c51a481004103c00040894200406101221505401c4800148061403510109600080c1d98691007249035000076401000b4089003801441203034081003001d80008807203284c0752030003440c51400310741640c0540100300010741149484100c0d550b545500180c103508589400300b0459051101d032104606000700c144004400d0240c8117140c2d17206030040c0c1e501203a080355502c0c10340c80000c15801490b0048821800c2d520010340c0100c02d40700c001009002c0300c03502140c40e00b016032510f6141d60220600f4020840d01241c669808140301501500ca540c20242c5d01f603a4000d080304108407085000480b15102034104010340c850f074001500b18280c1c0c20b0104e89032182011890170704500d00340c103040c1e2225040f0554500728100003c000d070b50040f5000746080c0391903c980a000b003008808003d00c54203500751b0340f100b05402102a074519020290a400e040d25852a0190095 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 131872032 1250 131870782 131870813
    0x40b011809061d0603030a050306010306050603011205011b0203070227010f06090b070827120c19140108130602181305070504090207020307030501020c01140a090c0302010c0519 78
    0x74081c5003c3c03801c0c501c954105000d140d000d0011440d040400301c08445540011b40190304154803401d0002d55540c401c400b0318040c00081c0300090300d1010070720740380d400c41c0d2070074491701c2420000c0c01a048001e9004000d441c48590103849a651021140205100d45540a003422090310105e4002090444142c1d50840694150343c85401c01d4a0300c6c0c0e2401001030003070a000411900b01001203558030030000003031580c003241c99818a2920194400020f045a00419403c00305902001d1942420715101c51451546181000c900350201d040070004000c0c0100c0c0f191940c14805110082408400408070300342000c0c2c0c1090045440b164a00301d40b20003290340c1c2070020b109070340c1d032822280030012902ca0180140c030350b9190305107403034508a44a000303074001c0c41040c0c1c0d040c021424004040303a001e00003090340100c2e40c400007914074400d03201700c0c034541e0000d414112040d1501d400900020032012885c016203409003485111108180380443c0382403000c00b80f102e0080341980c440c9040204e80024110b59 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 131873282 1250 131872032 131872049
    0xa02180105032416031e0b01030f0218060903190b0612150a0b030304030c180e0a03020c2e181703030a0b0105040b07080301030204051005030a02040b01180906 70
    0x852500d104440148004201d101c4001c030320150108461403a03a220000d103400e900c0c20042003613884084ea0100c05c83c946c0c1550310032903443d41944011903030304d80704003508011090421810101104050b50700c01074100d600900556000440100720382d000c2012040f010204050715221f0132131842d185420080580340d00d8010040b42d403440c90503850100d0607100c0120485d00c81c501e16a00c0c02800c901416003041d4668040c002000702101080003c01c11101508400c002100c050a15036031002c00c031000e0011b07034a41a0007010b010b1000030703404103d074000740104841d030b807455581c030401c0d42546c0c454a00348651a08521f6402903482a0804c0b10a03c840038400c2d003403041c06a0b680555092841c600915444e2900304000040b4440150381c000c070100581850401d08241d202c8100c440c040c1c3c0000c5081c1c941c0d1502000400c00c62410b80a481d074000107000f0000109440e000c00300365101ca41a600a00c61621020180443e0f40308110f0900500e0044e41d80713034130031075860308076200801e02400781c1d244 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 131874532 1250 131873282 131873293
    0x406020606091302310b0306010909120c060605131d0102031b0c03070b0f01080d02010c0f08150301050a0b0102160305150417040914060d0308060607050a0218010503 73
    0x2110714048081c64452000c0ca06480091003c80c0e081210b036115841d0044440607403244580d040607111401940000c0c9610800588801a10101850004140d01c021075250401d401320001441d203280080f021399080c01c10400000703841ca4940d01a200341c0d0000c0f500040d040700b03a000c550b101a0071101c1790412016181d031300d1400304102d1078284d10044401c60003061103030103452040b14070f10004140c844031203800d41c0e091650f0b590359400a8a01922519241000d510052165400900070b21070815880c0c00208142c407913036000a0410030b45181d594007400000b2000801740e084018148801c058000e001f00654504060210010400c3c03d9203203005114014841062020040403107080d130b500b210080c444a0140072900c0c101040061046a5000305d41c002100209912005840a0300d652000855070b02c1c40680c00000c00388004018500c501c0440d86d000000c2500080d407141c0100060301c80783e54908550030311600d40468020001e41090310200c4880d8041c40503c001816503000701d00351003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 131875782 1250 131874532 131874541
    0x4060c030501242606030d0201140112060b04060306021804020909012c04050703141b06130806010f150801032111060f040b060301150306110f03010b04060206 70
    0x40445009010300d03003840000c03402003202c06140b10300307001003201c1a10308001403a80d80314900c404d500401c14100704080700481881060701d4240112119089544020000110555818200c07800188507180001e901c8601070f2090094941000c0200d01c4080c0040c40440d0b03403860250002c0d030144c20301d5030110340c5200341c02541707142a008a600c030300c0008021000903400c02c00500400100c0e20301103da0316844c001640280d4424603002d0348241e000710041c0490b81e1030360a205103015101d0802e0660344e0854048460b4244001440761a201d109031507d5885041d884121900c40c07035150080707003480c81000300010302501d00e001882c0555071218049640050301d4181a82c22060a0200510f15200c44452440c07881d078407c42054072031941e14105480740102c0580900b04181034600d40301403c1036000300002c0c0040b10b413109421a01c03da008016000844044072104445030000402c1c0c40d4841c03e00b6503080c8a40c0381036640c0d0704200c010003652940d486174914116802032140740054003981d400103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 131877032 1250 131875782 131875787
    0x12705010e0d020a03230604030804030201050c042411070f1418070e030304030f08070605070206090a03050304110a06090602010e0304030b010510021005090102120603060c04030b180102070b04060c 87
    0x440319030f41d028000010507425507030382d02e0b003804100003494003090740202007090b803490410005014034007039100d585950900341002420340b00001c144100c03124081008100e01e08190044149420401d10301009080c4c1c1c02104a480700b5180d644010240308608001c034504000024400c1146c0e9613402600007904440d080c4100302180707075aa80c080550b000001100903008142500d856413004081ea881c0035200d940d0044000310724042075801c100046a5181003009610880d030b01b001d52800106003038500540640c0c0d540101c80401030030080d0102c0400d041140c550070a00d4122002084441d81d02c1e12400014042070b1103220b00d030010340c288004010180d00100880f4192a00261400030507030906052050520300452100114810303000d01d00300565aa125250058202d00c0015a40d00d014a010124020000c0d251502c85d030400070038802035481445c110340c02c0302c0d031200b03d00c1030564800081c800011080145d82c4015400041c1020400600b480c3c0244a180704000c20400260400d204 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 131878282 1250 131877032 131877049
    0x509010f06050f0a03140f0a0f052403010207021c02100306050604061d03070609090e0c09070c140703030f08070503061003021602060403060f0c0f0c060b012705010e 73
    0x101c0c008100c0401c41c805543c4a840001d100d0b0061504011480c0194148020f100d14422583d0084503083c40c41400160200c40c0110021400d00070803d001074100b80e0010244540781a0041014014507118034290b51001c2d0180c9045ea0380080180013091500f109000c0c514401c0e001c12403041c0d1700c175a00124654000d101c2c90050b2180a001d2a091605000d8261403039084040c1c030820b03c148489401d80590303820050813014141d140c0d00e41c0e406918100ca00340a071550303d5a00400d5812401c600c0c0000e490b02145141e100c200391419990a5a00303080c102c1000701c80c4046002a8040c2c180c1c0482032640010311101c1c00d032625598405c4e2030392400c00445083c00250f8005610542c208030384c40c42144283c0203498250031800daa0503644026900144003980103500c11500c41c0d44554101201e5041e510070902102d1450410294209940400070615441088020109599194425060391082520000c8150700181f441f03d0714034840c0c0d000290060074030500d40042c040e02e030343c4003903410301d43d0340c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 131879532 1250 131878282 131878289
    0x50c010e0d0b1501030f0c0e27040206072f0a0e01031212180317060103020901050d05040f02090a020d060803040617090c0303040303050706050705030606122e0509010f 74
    0x42403180f81c80d00800c480c0c801c45000105030402d070b100c5d088003207056072921545140d819035840b04070b107907240d840034006043c5408040500c81010761481d61080d0110f0254141e00950441d8500e50300c40c01d5242040e41202c1d40019800d08512100401d0002c0b00c0c07841c0c1b4a582d10344100d0784000040d0390340d0301d2054190400d010080644400c2c4241c074602d24082c540800d40707129a4000880c0003002c00e400ac000f007a118500680014684003070840c4510069080d4682154081c40c00750700d40180900003030b05512402d0b0703175003020700d40d11800034090041c02480e070150154020400206414004605400780d08845040503141e4500603001821a80000440e412139150391965814000182080c408c008001000c81209004104440c070090398280010005144240c54160b120011803e082c0100d0314000c1010b41405410014841e4039600e1780b050301c010019140044603a96038007a43c0594a0440040034188001d851180301c2c40c1001010000c030a845094803100600c0c0e07038840804810031150311 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 131880782 1250 131879532 131879543
    0x60403060506030c040e031210060807110c130e010b0306040b0a0207020111150103152705100f02030105010215060906240c0709060602031e0a030603080304050c010e0d 74
    0x400000d103554110700c2d80424010162070a20812101003002e50707404c803103804d1542d040003412007000050140300c035411801185402c880d0f1070402e0390290507914050f08580c00e10000513085000d45408200c0c8020a0304042c0030f41810741d0050f094080504081201c8048550815203484030908000a15a07c9580c00901b0414280c507159a42d00c02035101e01c2d8140e040020490300003000b518100445400381c00e24486d00300981d851800d128a401c0d481007440328031541801c084007400c078042042c042080d9800d40c1007030f900030554640039140084409800a01c035003003501001c2c2080f00c42c1e0203141210000e03000d998148016800b0300310201811900242c0c0603d83c0c002180c06410241e034020b030942c081450400d0904020501000a40c2098a0307900f0a80d101c50418061641a0f00610000344003c0c001142000b4400c2030303071402c02883c180b00320b10114011580800403407003900071000854020768800ea480c00c050030100c0c0c98040c80214640130810300c0509105604140c948030600c6a00034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 131882032 1250 131880782 131880787
    0x3020a150f0e0402070206071104180c0504020f0909100305010507021501091808070506041a09030a08060301291e0a15140d0e070509090d080c040306050c180405040206 74
    0x84007a00c002c0711490615420a03420f000410050704d80400038030707140c0d025240c8152900c1e40c000401041c0d650b0310200a04221b00c000e0b840001400c1d54001000307840c0d00319405070301c40301c61155018590044640b0264000700c000103100d012608100d805080d00e0107800280030f955106c0900340d031780c0c03041c0c02002d001d080242c0300100000d050645c408490f11021424440c02510292108030719a00617482c1030b141c0b504640c003840200318a2400d181400c0d00f58807508851480c14020482e101c2c000e420300300060108140000e107140d036084d071211852500199044800581000c60900d4034410045054090010034000341087d4055148d46280b003070009040c00e10645c200105c14032411450032658090140c500c0c4030b40e060400100143c1800c240b072460000b89954400c88071450810544e100e00c1c090303082801401140100071500da11030034030600340503d098503030030f8030000988500c3c0c0c00034111600e414240480404410000d01d5000c000340008903c880c00c410806c4125541682c0003507115008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 131883282 1250 131882032 131882057
    0x702030f03090d030e0301020705060403090807090615050702190f08061003080412050a062a110d0f020f0607050a020f0106180c030219050d0c0309050c0904170c0703020a15 76
    0x6200303c070205c1102500150038204075550322494101e05543c11000b045e4800d806011800c400c06c4040010040c80d0f41c1403007424a486060016036000c81c4101d0b0403c400014082d0544d1102c44400c9241000914000c00541d40d940012182006a0003268550300a607030201c0c108604261200382543e40158141c1e240c2403910300341c2d85030342100000c122150b010b45400c030004030f041c51148054000aa03180d0f0070f02000704c0ca00808011650b1408041031106032880c8591102001403030220600319030600320350804441303206a2510340c000001610f507106940401c50b0031035004020385041c00b0503400315401c4070b552041c407909882c0d060244500314100d0034010742d180f01550700716210911460800510b01a80c01c6a9800200007609075240820800580d0102d8001144908100d2100d646000c0207200c1440d50b030640c03100201d100c02ca21503400d0001013014480c0b0a8844244210a02c80c01d65550807411005071b01c13075600e444207910440c3d05603000200305100001d040b003680001d681d000c040380003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 131884532 1250 131883282 131883287
    0x510020a090902030103440a0509190501020c060c0d030b040f0e010c0e0f06030c0304030e0612040c06080106080a05090309030f060f1003030207090504110d080702030f03090d03 78
    0x4a100804100a075003000001d1000d0180300440c00785018002c0c010190201078150120841c1c050b211118028005580c0300030304100381140e1002030070410196070703200c040600131a50f034092420082c1d0b2080c0203020508030241c246071410300b00d5400f80c0070303260220086000c025882c0900308810b0342c0c58000d04030a02c1d140e842540f08503110341e0700520008003131180045041c210b610740100524240e5413003060b4210381c0d40009081034107070021200e10700750356406004112240006004d55101200c044041000c160041280d658100d2014080b40e44601040a001c500d102058900382c840c41003400004c514540319802080c160341150721461810b8179104e03040b03401061300800300301c0c040c0000d204c9811160f40900032058034145a2000740b000d030030a6208075103041806080391107000c074102400c0002980109a0718101c4072108000a510b9560781401c0601c540034a0700c4550001a6280d02c200300700804001d00381702402641140c140085070041e82d0b550340310f007a81141c0c2c040b088440313000000c0d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 131885782 1250 131884532 131884537
    0x1030e100c03090c0611100606020307030503101205071703190f0e03010e0d03060b09030a020904060e06180c010314061311181f0c06021810030b120109051002 70
    0x781e180b400042c19006030b118203041c07540c9a0050700014490307480050b00040204040c54a16a41e0300003002103070702d07104002e5500c0c41001401014494040000350181680c182c030600188020026202c10340840d14080d502e9a1031401220b242d00300024414000c40300000594004442d51217588031030200780350090b20710310240c24507201000a0402031a546480a0007140c9041442c00300810003204001c00c058140e90f401d03080010b81d90014045601d0300c0d500024900c40d0300e078042c0c6000c41691200d06008024103501d4121008502c50403090045261424140c0a056286030003074034050311103100110700382e40c6441e24085c04282108040341451800e14001c1a00f003600e41000507208800605410445c0c1004c043c42d11680e0200070b90340d590b42402101c00039980090380d508462034408010203090f8855610010703007081c1d03001c585110816055584007030030400c010040031110300741311001006482c1c07031480d10340a402302e84004080d100050251098055000c8042c10343c8040d0000ca800094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 131887032 1250 131885782 131885801
    0x10090902031f02040602070503120703030b0613061718101a030703050a0209010b070803010b0901031416120b010c0b070309020a030317070503091b01030204091103060a0501030e10 79
    0x14001d2600306440c01029400800c800481000d0141c0c603a0b103000350180c20704411f544060300a400510704040c859030302102f15030781c2036418140015a90a05008102e40e400b81c00000d009000e003011010a1458026125160085031100700306050380e01c03402c1405500c2c180f81d2110203194408000e41781240075a40126100d84040c0241c01d0b0110102c100003450b01400c0c3e4000c0d10f072508022003407030075410942001809410346100d65850701509940e5200b031840305100c0c0c00004032022820300450384c4280c00102032540c2c5001e925000341440b00c6a055a290110308810100310b01c1c49903491420454007032010840016101c00d04a650300b521030800344c0b07800a116030101942c0b401040016600c20702400003840c000c0e034603040c288684800a155a0002821500500c4000e004200d10901c1c00030743d4580540d88081c040781d03441c06d02070058000e402943c100307419080c1000f008080c030b2000080594441c000c1203c1c0f100c41c0a548200640c01c880900c0e6240701140c000c1050300028620541005000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 131888282 1250 131887032 131887039
    0xf0911161106041d010801110a0e0f0607110109150f0503041407030f050f07050a14030109050304081b0d020906010c0f0f03050912150a1d0a0302010204080d0810090902 74
    0xc40c103072100021000d500c01c2d0000707840b1074512402c456039041c0005a8030b01601d03140000b040310101ca2601c0110714000d0040c107108103c48000204581e49a005804070340741d0028041a48519907441e10540d17440c1c824003046d000480d0301100185200d00701c3c5001030700e940d03181c50340074043c180490112444d5000420980360b410030b10101c0d5002031000c01038140218021000303000090550700d0003900303191841d00390f03a80c02e502450b414130240e0354011600d8101c8001c076482c8245102e48901103405000e081c00f000d4958000402c5c0061594008204410302d903040350785601c203e00d958810040d190b40b2049001c0e400050185c00120194014044041e01034020300a03c118600c00e655140101c5444034004c50001d06d012482089509007840652203d07403810700504003100440d112110390a0005141218080d215041350a501202c04480c649108940c0e058490f440044e0902a02135405445041d003c0d00c5a600f6059034648220f01080c010071ba00c10b0b410005616201610024202071300d4266030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 131889532 1250 131888282 131888303
    0x8030a1104030c0b03100b07050601090905010905150106020d170703051e0405030a091211010f0c0c0e0708070203161205041d010812161202010b0a0902040f091116 72
    0xc529a401c04800820303012440a17a6480e04c4a407503014a0415031080b24540418050900001c41c0800c0107819590201000207070841a810705501601c0c03100c5000d892800740c500322814000c03450314020f0503120150210751031404106800c0b0f801c00400e44e13040d18140010004500114441e4011540000007015003942000c5800c410301d400c1700b4140c80c110354681c0009130020840e80c10104010060104c00c061992616540e02c40210389011101c03941d040003003a07614070715542c0c0034245100c000e6400c412807408040d00d419407036400341800daa044000c83e50145c0010300301e41c0300004139600151441200702000e2183e640d50a03501080501c000d05000c8180400300352100d240c010800b0304403038814002a59450423542c241407003505519204460800c20030000704070300119140d507400d0780c44040711f586800003c030120f00604d401c01c007456108208110001c0c0382031050300a881900e0009511700602d96480c0707200c0c1c080350780007032007203103030503020312802d01a12001ca6100030600e0060b150f164 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 131890782 1250 131889532 131889539
    0x8011502060a0506010c0c060914010f080a050c130801050a1508070e07030204030605090615030105070c02061e0c030d051e0c0a0201110c1e030f04030206032d040210090308030a1104 80
    0xa40f51198000d080000c041049c02c10205205071202c42c4c0c281003e0a01c685c0080020400520640c001082c4400b51612903000c500d00070001411100214817400002d60150384803e0b495002c0c0909a42542d5400e0070907000c550384a400280d80c0302128002c1005217007082c81d0410752614608000c0030761040c507a00380300020110311540544c510035000c1202900700351030003140d50300e08650b00b41c07031060007a032415041144c402d03080300d4400780031034044a80d180c480a500001142100c0c0000e061000d18401241c444c40e03001000001e4401c01541100500144d503c00005002415140212030440882d003008509188c182800820441406100108514110f6030314880c07281c0c44075400c500140d00200c1d18140d92040034065950400481000e2351400800c1503141c000e9004500000e48507040000201c0c81d03031070403442484006040020030092162030100080701e80072080350b050780110618801c402c0c0e42441000381c64103581e4446005419900c0c1c101080c001407140c609903005c408410800031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 131892032 1250 131890782 131890793
    0x14010f0e040c0c03020f0105070219140a110112091101050a052b060602120904020f0d0c03020d0c020c01140306040b12010203100803130315060b1908011502060a0506010c 75
    0x80c0300b2240d05440d1035080e06010b00d8000c3c43d004982072a090303240d14110600221660200d512454003900303140c03001b00c8a401741842c030380360054050359a50603c10072040004000303405c080c20350019001d0f01d0300242c400c000c2d840c03c825284017450042c440e5003004035034072840d800340d40a4240488246042428502ca0701c4110b24002c1d10701811207003440410714800302c65610b03801034401401c07075071016144486007001c48407401e0003010300e01403181d074020840d5651200c8110a0301c0e001252012b05009507100c070880a0025404088116050307810807480000507400055121030001e410b95418481500c009590702460300090862a402502c401d5203919039aa501d80e017000304958440010303900c4c20080400401c040050303004100941050240340c98031102195420304a07074010700d241081034074560b4104001c000b00d404c195010500030685140d103450f09946108002d41c41c0d201c0340e0561343c0302e94898815144c84011380006900460000d203000c00070b0b4010a03081003042c1050030051081ba03442 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 131893282 1250 131892032 131892041
    0x3040f03111902040c050414091308160201090501030603020102030a0818070803120609070519051e1c0b0a050f040204030b072601030206030414071e08010605060414010f0e04 77
    0x101606601e0307402e10303010340c6004c0c49000d540c000c142c20a24075040c60002d080041d40381c0441e07880c3c8102e0902c1c00186a290300c403820202066401000c1503034074850503040c441c5c042d042d110107034000782d594840810654042e114440640c0e40580045040c80d9449908440d02c48000f00852208401d10a9281503c401044602c0c050500403000e95240d80d08643d0700382086000a0415120308d0081d030600c030580b03401c54111031a1038004130010461581103141910300e8402d904144100c1c0080f69008925401e00e0030190488402c200c111004104c1c0c1c01d1980c200b6103580c0c42c81d881d409204040100018500103038000705032a0040c00240c2801e6a035180d28140740411118440401d0400302001c4403424144820ba0305c9121038030ba5003001c0d5045401103016800014401440d003200d407050400d00500801c03198000b0030443d01c040340c40c60800340c0d08840c000c000b4410b2600325030034000c0c007059a28141c006e60703084d41c41d4041c1000b01c003000300c8011034600d100c0500c41c005000e0300007000c4072184c450307006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 131894532 1250 131893282 131893303
    0x306051002032d030f041a0106090305160b09011d0a0902120c0a0e01050c150421140703030b15040e04121d121002030a060e01170303040f0311 63
    0x103182c507440100f81d910849900503001c0001c100c0a228507504442d141c40560741c01c0485401c948880e60345516148194034200001c5601c06590540002513480c1e100d060041900d00c500203840f031a80310025800345240050041c400141400d100c1888a548910f100c001400d03940811002d40410b040007141e4094519003011900c1600080d50301c075801d840c01c41c000d400c50700300a10145002c80942c0e0040500300660850303410060000b403003052407001001481c160b0b40080009080a090525100302d81100d10401203049088001c1c1464055005148108400094008061030b0154a40d01280108a00c50300c240d44014034452440d0504580c01c00391010300600b2010440a042c281416400e05038284114000c0184e000030300b110f82c0b909800c4100e0501c0050342c0c0754101c030408040883c1400005080c08000501c04802c000b007202da19041030040328549000c030007080c1d0303c0d044e100d20103c0310404c8401d559403041001c13800059051005a03141d50203850400c90001c8070b00059420b0120024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 131895782 1250 131894532 131894537
    0x10203073512010501030c08100506031005130c02010605220905030c0712030836120f07020a0608010302010c080f0f0a03020c2b200102040806151005091003060510 72
    0x18014861307940c240c480c01c025070041d4140610303030341b40501480d50510700345c0c01094020741f008400318400b0781600590340d01034440280030068100c0c882c4580340092000c0383c0c082e0015801d02d000054075091131804078a00032113088522692214144640001d041040022105031108010710000c802c020f01c96800500488656440030100504005188860143c191900039008040414020701940d040e2108141d049251040e00c010000166042091801e44160a2a0009040072a040d0182c00510405108a8100440603200c110869a081c0d0900000340402c401c1c05408000c40d200e00b019166a0101c003c03010301c1d2015804144816402c00018980841c2d00481d0b814004842403100407017003030189602c1414100302890803a001e4000381c03604414010021031101d030818a140544000a01c10320003999101e0f55560901d655500446400c1c404807010320048100f8a400140c0c91007112440e5104c1d4102701c1444100107a01c1e8562415000741a82c400700010583c949141c1c450f166203594 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 131897032 1250 131895782 131895817
    0xb0604050616170a09060503070c1b0306060b0d11091c0c080307030503160305100b070609020411070201080702010905100506030a0c03080306010e040b090705070201171003110102030735 82
    0x180c1c0060b00e01c17000c9820550a0040a204218a84d98403407850f030f8070507070001103040c3c00d042c1c560060341000c86190030180113031b0706200c4040b03101080d800c0144a035000780c441c104205101d00320700e84114000c4200d6668070407030000710303442d00a500441484045004a008000c415511041d162556100080c04c8000c114044100800040c0b0503400c002d9181e11402d00384280d290185000380342c0ea02501800c46d5130440400c205040c0083d980c40200500d902910801c141100303c4200110341e00481022070018540c00000780201c0e02c1030144022041d480401801038070441d21204003d404010704c034582501c14222004040b40c01b160610000f18012000aa40c90424100041800400c4001071340194200700c0c0844141d100c1d000040d91040e01403808a484075410b1004840c00030000c00200c1c604d4400d001441a060140c000c0d00f401c59204507039150400031504010f903100d000309040a465a5140b12070380807400ca580075102d00c020207520a00c4406442c0040c2c2080c290003c61350703904d240600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 131898282 1250 131897032 131897047
    0x203030f0a3c050307140d091b03030c0b061c0303050f1503070b090f0a03030806010e04060e040201030c110a0605160206160f050409060b1c0b060405061617 69
    0x90040d10481e0114442c40c480220108541c58141003002c200c09408200c800000946040d10480a190000882c0f81b030007030f5902c13108031385140903000030a803c1d110084005460780c203044030041c1c21011254140c4a1a082c04010b03180d06240f08001400582c01c00e00d5048425001d8420341106074000c3e200b038900081a007045500142031701d00003041c1c0b20500883c8002c0d14050359000070580212206203941c0c540d81c01002000c9000e41c254250840d400040d000c801008240d00302c080144909802e81e254052003203210b080005550303552044041241c1117002041c0954401e8002803542801030030b042c00a8605246110320b800d81482c41501c4059030703803061042103404002e030814800c0c85817005054038209440c03c004615844104c600505c034015008003045070246043c1c80080c0526001004465034494460b40329500810700f00f4000d04050b495422403000900c10100b0024001c0c00d080c0c10181801c084c010307036502101e020065400e01a40c580005209041c104580404ca018080c1c0c442da030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 131899532 1250 131898282 131898317
    0xd02040f0e070f05061803010603170c010f0203010b040306020309070b0309010207020307050609010206010e1e01170d110303070e0607060501090204030b070e01022d0601080f0f0c030a030c0203030f0a 88
    0x2180c005095035118003d041145a94090950311506005c1c0d801c1044984840300185c01400141d00040100920409680030034078020050484d10180400a01c02e040d4810902d60813032009005e20042550184803d00101c0c015501855104100a01320740c521500c404c0c4200040d00101c030030303060076900080c10703404508040c08400010403044d5415420401500000307500c03000c0c140105440d030103401000900102e45a840c01e2002084140b070b2000558440e900d0440c000d907021000311316441101800004103104228130509081030f2030195081d926151000c80d8080d90031400541d0066050202e0390100c0e405208072802025840c0d070050782c2e189145094488004020900c4051101071200c503201a40c001c40c40d55245180304140760000c5000642b42c0c1046131000e1404d0b5410f10443e0000318000000140034a0f4017081201114507002c3c0303c14100340d560198401103500f540000100b140005d0144450b401124401410b503800c00030007041414480d0442c200b2400000d404540d504a000c1d17 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 131900782 1250 131899532 131899543
    0x1b05100b010806181317040f1202010c0b072c0906060708070b2d04050708010608190606120b0105091308070209071b0b060a0e0702070b07020d02040f0e 67
    0x114203080290207460b018000440407000310508511801c0e0381310000d403481d441415003581181e48071410540d4003540d1440160316810070f01039800c1d6140311000c0414014100d00046041c075905035a540f8081407079640e40b400000340a40701c407050000305425120782c001ca00130343e01d01d0040109602495000300c0b07004c01c030307916001070072060280c102006000003244040c01201e0629402c034001090f83c0c3c542c001101005003098021205000c61020b071400c1b41c0420010460003140204215141d03035407075401c078a0032174490b80f02c1c1034010340c85071500d292150b41d03854800304401d02a08001400035900c1054206220141000b11020a07031800103001d1031402c1090103400101c0019003085984e05036a520085102ea0031010b8403c03052000003030821880b4000c200c0c05640207652100c2035460318600203030010801c1d55000d215408408020078041585e54200f403240105a00030400c686c9084002d010701c0d80300b020107a810038070410300070300543c46602400542c90028503001400c84400d42c451070800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 131902032 1250 131900782 131900801
    0xc151306090609030305070809040203010b0705060a0203060a060e030a02180a0c1803030e0d0c06030f1b0e0114040b0f0405040b01090b0a051605010509030c1902060a0f1b0510 77
    0x1c4420300c140110b650062495041d0380d13042c2002c540e242402c0c24100001d00613810b2140e40140000004280f0080d071303130302034480c10f8070440403940c00340c884400940a90004582407904a1160101044030901c50110082407034409030688683d011150042250381070125103204242c0840000d21102250912501039411042e24189804810155032020603404905c40682001001d15482020341e03680d501201d4480d0384a195424026610000070700039000240038840c140d0700e06541c0410100c1e410b402c060000460341d4030086c030614005c0c011340e001c486480300c22807130f50400c0c007010440c0d0380d20710002c01d0403022444180751500d2901003000141c851040c03655041003032f00e00b410441180341d0001c0d038083c200a07003086610b030bc01c0402c0c4220807550150b40030305190f0800701401043c080c003000520340c46083c14260390019201000348012100c0c1c443e0001c1d0880010070280019030301c919002c10f40c40d00c00f440c0c804519510341c01c480c2030318141410300343c0d5160050f94084031201c4c02c80c030a02109 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 131903282 1250 131902032 131902037
    0x50a030810060914041506031b030e061314010203040c030c080f2808032d010b0409020d0207020d05060703052214031207080f010e16030b01020c151306 67
    0x1510300b030400c000e08040c058411800400750708161402981d03141e4005a2070b03003040345180441c0d250b44003402005800118607aa4112501072000b05d0014401d0103002886403801c1c0007850b072070315180590b28941208940c10b9815800480c20040000c4007800110300139030103107860007005400d604241c06c8030003943d88000403039400402d0300c00c640c50000c10700910005a1421321070003851030340f01d0406c1c4c42806605c0103000348400810003280c40340c0300c1030352004411410703a00c11b1213000b240341c030310004c0000b802401c035054410b0104001038000c503002000200900380001d4209586a804952030b1009032000b281c11390003240400140e180d161054591200b4040e90b5a40c0381003243c10440800c880362540a0301d00712445048200e001c030204100c0d545000705d08814042440d0500000f0420641030f034402560038610703000040d44e10100c4c201a03000300700030f180107440c4c2d42526000f9001002c2007030280b0b0650142000d000300c0342e0340700803201c0050200d00301030550721a04481c0003403080403550841d509 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 131904532 1250 131903282 131903311
    0x100506010206151201020706050910020c10050606040306090302010f1b090506130b1b07120305090f15042d0f05090a0b03070f05041b05191209050a0308 67
    0x9050303078000790258010b2100d0368810922000c00000c0b41e00001d801071031038070660000502100704011130344014031461140041e902031032078081249042e8421608030180c00d90150f204000e0505855000e02d03000600144003030718041d1b41c2c0d039603082a21034038401540940d540c0e400600e01c42080780560340c08403842e44041e014a500c0144094a110a280140c42c01004041242400e01c10b81b12407403009043c44103811910f0703401c0c030551051b45224003100180d603405a902c0010701c02c940030404684a5038103456050502185500340320f61019404048d907404544406041c0f200070485006001a00c850b040510004100c00841c840a02c03002c854100c42180e1100c08000b0104044031060903030f2404c55001ca0a6201c11440400cc1e1010070070340c1d41c4c5070041c900006580021041c0144c101c41080e20309001118501e0001004203034281d0a000203e0f400300030005542041c00811103541105041c8840c50008442c120811122074110031100b55010081c6c40e814581c200c8075075540450300306241c90 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 131905782 1250 131904532 131904541
    0x304021c0221010b030304090923070905060103140c03012c0604020306030715050301170f0a020f01170c0d05100b09010309061b020601060e0409020307031511070c06021005 76
    0x12484210306100a61039002c07110070b6075041100303400100d560340008045030740340d948814044006040a610447d10719594072280752070000031100800042c1e601c0700183c0105440d0914400181200920f03030341c1019607526640400c60f1455180314050f4203844800c40d10f0b036051030700c644641c004c00b0410400c0a520304030500c80c0d2405960000350320080c169805071712600e82101007860200c0540246d124228035620030035503a03031302034003450403101c45c0160346200a001d00c0d0050b80720160014280201c1d00040070302405030401c1c4014002c0d6480625100d850a099404d108038451025241c1440e1203000107010202e100c01805056044040034a44500603860710401c02c03128441c002c01c00b81032607190034005d802c4c040c5c0c84c7d010031101091001240b4049081c248025256032090154502013072004611340e669082c60f00c19500400d5000d802003c1e00c5042d44c542c002c1006014000e03000081c0c4a940e0b1030003004544015000c000d02c20005203052504100c800303420010300740c0e41c0900386441c043c01c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 131907032 1250 131905782 131905789
    0x1806090f06060a0b07081e03040501020a0f050301080c010e0114131e050102031c0b090a0504050d0e10031a041506020106060201140a02030a1b0e0414090d08090a0204060603020304021c02 82
    0x203c4400b075101503101da441a800c3e44400c7c0066040130b60840b0420003004000074040190010b00c001c0400d9964090350101071031023641c440c0000e000e10031180d40040200e040c1540150b155000c409414142131038412002403464409a005200790103040300042020041d14003191031220388943c01d150b0b0b4080690910300000e59900039568142c0f9045150350303480c226103001d94840741c04100003620983e8540341052402010300000c0d2400c5605200d080d0b0301151907485842c006d50000360042072043e01140c00755044024005107c00400b4030700079000c1c10902a9581c0c4214014045400c0c0d036050490300d00000642144c085500c40019a41000f40c07840444a041d400580c0c403100398400140c0320b4035034840900042c5080b803c04407440882440c1c1a6110750805d039030000d60002298140100000003041d05080c480c02c0e2071030300c881d034032407007818460301e000d038892940c401704240485903407013040c0d0005400c0d10301c0c83d0700210109070300005020a504048604014515540745868054803c0c3da012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 131908282 1250 131907032 131907037
    0x70f03120503180304060e011e05180301020405030109031106010605091f0e0d0803060307060c0f0206070f0503030f07090909020102100f02070209090d0e090f0703051806090f06060a0b 81
    0x151010071078000000b5000d9201481c0c96039002034144222030b11541c5130b54000e40030b40044410325000c03400050354030206403104141096031062565071941000c00303040c0e00008015000d81c20f680e00d95028040420280c070248540010b041c0a41e07660400002220380c100c0c1402e20607040b910030040d08100c40002e54503240b40000c805070f80200c02200580140d0022500d800c6410882079011580a00003424031010002035806220200d0958003503039968202660f6007000e0090041c02800b14008110144c5001c01c0984001402940580000c0103c1e503500c509552085034217512140226040c0704840c3c0d4400700078005030000110030030040003e50000303591200480c0260400e0760301d480907401c001180d501594542e550103440b010050400d80c0036a6100c0e1950854080005c02226100180c0d14209142314020180b41d440495941c89a0300100d001d8900141506254501aa21000d004404010030751040804601815106661158881c10941d028100510070030b20780909101e9468603504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 131909532 1250 131908282 131908313
    0x90d1106041e060204031203051f0303021506040b06070303020c01060f36111c02030f04080d090f0f0303050601021f1805010c050d0536010b0a060e03070f03 69
    0x10307078207040b1000c0d1030f064001c0e00c515003000386031614001ca1a801c003901078200350300480c030b000659080696225003040780c5000d00d100c0039006034064080144a8040e0b0048250880005080420081e4668000c13030308541c400c0204600003980081d508002980a2003a04040c1101510742028145008140c40d42c0141d40e02c24007400b10003443c2c0d41080c071048000c8070706844400601c180444c090211540c071580d006202c00303400e4004500c0040041142c5132007101d1180ca0705104030741c1c55888070784a1381e44981054040d010195902c04510003c903e00070b80c9200c080b4481c400c04002c0d0015490002c0a440010300710303070b0555025280c02004180c1801016145c0e00c10508001503100c04880222070619240c07001400c1035103440c0480e002540d11600a00c406005144103020503201e2081c00320901050b408112038010184a0144962003140b120482c141101c60004ca0b0300c0c3d074143c0008814028580c040c4002c0b41d00402d151a1604050040708000c2c00b51401c8e0807445455611a00d009600940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 131910782 1250 131909532 131909573
    0x60903050d18031e1701080304030204140105030a080a030e03030114120c090601231612020705060702012105090105060406090203130b100f0305100e0c101d0603090d110604 76
    0x100e003074080d01e205c1c560440c41e141d1030f11840c0f041540c0d1180032580341d900900040c0d0085044c60441c152000715208000e04962000d0028100d106464480902a42212540004240e01d07980c40740e50a0b00c00f0009180030300598500580900000800c000e10804001d00c2e08100c0d0b040201c50070240c0e03581e0900300c3c0c0d05c844203080002010b00076040500302d04d150340440c141801030200301460900b0280e011610309038072a9490840700c035807c40d01030340c0d039035010702c50150b0000e01003007100d0041d44a5444400c4d400800c04103401c80628170341c4800240c074000c40d040070490b9926000c0200c00c0c030700f40c09900000c100b000b01c110f10314186149409200201400f014002ca600c090104039000e4041c8a110000c0c03401d1018421555141e150075503d80502802002c00607003040c0d0314a5862101140e0388289540042c0204010844100c0035181a240000914410316106c8121007240d00c0313850003144a080c1100244c11258801d4501400c6111014001c15442d170144041000290044100115008009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 131912032 1250 131910782 131910827
    0x221100303030f020d0e0a030206091f02130b070f020a1e03020409110d08030105031c080703050c09030d1112041a03090a1401091a0c25060903050d1803 67
    0x4070f01c840203846a46010031006140c800b1303520464001040c0300d11070038400d5003950300549401b002d1680d15940e91120302000d8640742500e5100708195030080c12186084400e03d080e4654804880c901900300c4441a40c44141d0003124904602e00228060081d11004001150400d074030341020701c03135114030700000740503079500c5900c00c040c403000b00200c4144000080051440c00131915000034213404c2841100d000c2c0c4980c0d01c5111004404030901c05981d80315030349402c155501c21200300c01420000c0c0c1002d4221904203d808629101440028169840c584400f59402040c01480746002040b00c0c00c1107480c50184814080ca41031460803100440f003102001d80c4945985108a091001c9180000d00744002218082004181900000030550040d071074086c844451501c0e001000c0d904440500d80400304100c2c5031001502c94040e000108542400341085610310b40da1802103801c46241600850b00c081091215000b940c000c07038a80a40101403550005440e54010340882c684010303290101160 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 131913282 1250 131912032 131912051
    0x30e0301060e01060914010509010f050904061a07051203041101051c060e0103060507022d120f0331080304020103090615080f06040b16170901022110030303 69
    0x250050000b901c490300c18010705503994007010b4810b0201744100c02d01c825408403545d5007903008809403141c440041e1215641188844021540c3d6801841c003158442d64a28000c42d806092043c10101c0f12184070407240d50b140f09040c014035015600300c480e018444100308200c0001c0c0500d06503c0b0b00e100030700f0651b44500540d850b03c03500a01601314040c100c3d1414100140300c0d00854031450481e030140381c2c10401501c51000c100d0722403c05880030500051081001e5440e0034500058220102140d4180d92151038001010410380e44010b028802002c0c0200601041e00484164500d0700c01d0948480303615101508190780c5021450039001d006154088001425a40241c01414145e540114104a041d1228041c02503045450140c0c4110b40b10b5042c0c149810140001e1440c012900301c00d8141969035890301c240c2840a900c010801001034000c0020000d92800c841c940c0102d0110002503107030700a0140001085159213403c406880031041406032036441511148141d030303003514011603206007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 131914532 1250 131913282 131913289
    0x5041703071b110406061d090c0705060c07030305070c030206310b01030303150e0615070804080703052b0e0303090303160218010e01090c020c04110a0206160903030e 73
    0x30032802e1041d0071904031525104120784005642504001210304009150302c0e00c104a40122182c0d00c1c10800000c400401001450180102d980c000307a09a061441d101d0303d91340e018104002520b982034112070100d501810190075014180d804029072800b4100720815480c025a150406803d8000201c4111500550a0a015040410340580001c00d10b01102d1520309001216403d03c01600003030f2605140b144070300c1c4041040c5c0201c40c02c2c2100740718562258410421203400200b40b140c61703500708104403400117042c40b0160001f8031a5030b018155917440e40c103050b8141069140200e0428034101d1100e2500c1d1400600c81e0800115480c280e15030005050200e071951140c042060750501c000b183c646940f04405030421b0405200380c2d240e800381c11580c008074039243c0e0207005544400e01c0540041c8052200c6a1081c0d42c92a81d82c41210612040340300031078101c601c100900312100714001001500c0ca50108203071500208004008581d01d440d60200808011440c0001010848959500d18080c1e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 131915782 1250 131914532 131914547
    0x90c021203040f1b0323030c0309041509050f070f050906030f070c06050a0213120309061404050a0605070506130525090606020120040806010e130c09050711010504170307 75
    0x2990366031194070345a00c1e070400c291100500c075040d0410282c0400d41c06d10181010058450000c00d8000031410000f02d01c003000003802d84540841c41c1e0024403032002400340301d60b010700c1c4e01a10074040c1c840c680d802c1400f0b0080c00701007241d5a800a0040c20001d9500c191195022242e0201417080c003030407203440305a0115040185100c0c06032906080c4802e2003d01c2500e940280004ca10440110110981d034005401e0f00c1c3e018250041c000ca4440f490801680d40071700056a1300c400c541d64001e14103503d55000030054030480e0082000140d0110f0380600b00039040296a400c00003e842c0951401015624540c4d0341c0c049140d60002c2903807502032089600c01310f02c0c164028204a5406009a6403190002802004094840a054042e202132404040080f43c102e4003981c4010f8090310b0030307030308184401503180c1d0302401e02000f80e5060042c0b6000b06200220010140c442e914020810381040078008010300c004017213036240d59141106000000e0b050301010f110041c1801c1810740c07299034029045d075180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 131917032 1250 131915782 131915813
    0x30f06040902030d021614060a030506010504030515150402070b01180207050106170d050c10020703090902070b04211707020a0209010806011806060c0201120213060504090c021203040f 81
    0x10311503406804d40403070700410340c110445183c3d0001013489694840c40c2c0781042c8080031007500300c541009010203ca109070083e903480340d010b04015141a0b560750b249482d059a4994982400080c0300501c00c2d5510004a002040c000899055007000e41c0340d280c050041c401071281d80703e1680001d015a01100d86501503846081e002070080013900c5e40c1e010b103200c84c5982a000c811007401034072505c6190718015420346507024801401001d0303207514a05032000a52082c40c0580c01d01c171107803c0000c0c2c5885680000c01c2c44a04c5610000f07a5805c25151025500030401c10b40d202c0a268203426441e2075500244407000d050900010398620789952001fa03082401c00c1c0400703034201445400115054800140301070403641100d004159980300e18140c1c4c012503805008680c0000c3d040c51800c0e02640c810300703000c00c0101104000524000711038499071000c0295a11840220308045030800070708000c0c2c0304100c14404a4006012160200c481043d180d100050000300750307400d0342203000103100b096698611301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 131918282 1250 131917032 131917039
    0x31109040302120c030903280611070f1101030b03011112100b070b0405060c0702010e0f130f0902040f0504080306121c20070b091201020c01090807020a0603060b030f06040902 77
    0x241c0c0800b0141940742ea010140140c000d00c01c0800e43c518100521401c01c1c0091441e41c160032301503440344d6a08000c0c04201d07406115442c0b0a00085c1c012900949110808500c40c15034001c0300e8100700b0014042c1c801c5010202c3c8030780d14003811514403500100489000d8290301c01195855514045454415100703a080011703000cbe00481c041d4108080c64812900480c001d1084030000d170b40700f041d150b10f0303440f6245000380094420000c01c0070f14244050070203054100144011048045200c80c08100c43d0702e002c91016040c0c68109140950519100d070000d455064482070046103050349620300e1510010f00814012034480b4850700c034a417014041c00080a03415034841c0780b80000c403080104101c000249a185107161001d200c207c54100080c9042110214070455091040100400c4540c038034050307912031903540030460f2940c400001e02c2082c525910552006480c0d40d03450041c055071100b0740d00080e00307040c0340603401d0150303000d0031040c0c0780d0003160021a400d00e680c8000c0420081c000d030080c000e41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 131919532 1250 131918282 131918287
    0x50d0204120506062d0603040201120525021501060e031615090b0c0a080d0f1104030506010f0e160c020d06060e060d08030604050a0e10020307170103110904030212 72
    0x10002c0128140740525011520904000e60348000c0480d80340c0c440d00c8115061441901c15400c604112001c3d40c1d0117401410706418100e511f802d004243c81d01218800c55441000d42d14810786070a103c0710544440c594402001c0040005408080450f410300481d01800a038030410030362540c0800410081c1d52991046190580e40c0d04d010328031420040ca046404030714541c0d0040762030006081074a016039080c4000702548081c41c4c440e22050b502482c07018056503107641413081c3e48030701c60056003002004000307050f07a9907185040081c144481a0030cd0782801c440721008000c44484d140d480c6410080d0142d0350004a40312007000d80e080401d508009403c0500302c80082c2c24002d440d48110102d841040d0504000d40e0381c4401c104900d00c146000034824041840482d003130b0300702a81b06550042e03003518001051824010828035280000d1100003540d03400004001c240b41c0d011b00302c214041000d071707e007600c10f5041d40e4440901c0011191201e01584500c4005802e26200304a03014030a122509440e9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 131920782 1250 131919532 131919569
    0x10512030408030f120604090809220e0f16120312061508070306050102030a021e0705030105010314100c050a180e010b0c060606030f010b070f02040c12051015050d0204 74
    0x104c40c0d8205450340c1c4000c007007013400948a07041a000d42d0b8181a0720104c26858030301c4000c10000720070310405801c0c0c50720014120512000e1010b01c150710007140348000030041c1600e140880340c94041c480c5044240c0740350420081000d032104034541d200e0b45516040c0804030340d180890703050080116030702007c06403e041001001050300030300218042ca165a13020300c8040d1300d800c01641d4074810742c42d1380c1c001a4022407000000074102c3e4490b01a2001d0780041d01c1c24141d0712000079094850030703041a0755001141c550f80300f84841c10484071a4040207540180016020b800019040303015003102c1c40705001c0c1004907102080414081007015108810f031010403942c40d100304900c16040040c5950480c407480010030302c2481c09a05880c418020400310140a0382443c505549503000f40f0422101550540da090005075554052800300d1442903030760701081b84400d000107041c0d800140002400038242c0e00d0038045c0d124444e000c0c8030200343e1410104e95401440111350002d00c100d0b440000e400030041c6552 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 131922032 1250 131920782 131920807
    0xf02030904150602060f0c0a050a0c0b010b1210030c180b03070602100c02010e070b1e0304030c0c140108070503060a050306010b0406140a091e0e0f0a1b0801051203040803 75
    0xb0f03140726500700e8802d40d0b41c6440e03420f8015000c4c2e800024200c01844030008840c440d00052103895590b01c2c08100215035940c403103100340300a070400300d10920080cc500c8000341c5842c080b1940100c00d03203412490030b455510740700b8184880e801040401604039407608103131141c50304510040703c0040c1c01c4581480d594180292a4000744034111402818458140e080324414040c80b00c18814010261200380d20b05003c20b84ea0798004d0003080c048601e0824164601003c01010314401c500030344035103c02090a10b4041604501c5400007680141d142c1030345082a64054065640300c0264207050703941c0d0f102e040014a8202c07865200b56032500c07415001150380c1c0b4405000c0c01c11552180c41d0030140080b4410400050f00414441b2400215070440030070003440e02004403c07154055600c070106640d1511040d5200a00072a01151800e000724240000803050384690845084450444440801c0c41c080003881c2071810f104084c4038030030354541c2c20f10020090048a000748140b8080341d0f035680c42000706 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 131923282 1250 131922032 131922071
    0x304030507021c140703170304060608070b030108071d0703150513020c010b0d0b0f0c0f0c150702071404110f030f10120c180e160e01170d0f02030904 66
    0x1140c50030040070384e8003004d220004000b415641d01c402d502401420f1180d4071184d507000100151341154880400050404090101102500550740403641e81e60405401c1490b08845a1281c942c03203e01e06a80402d10142400407904118a03160200c0e18114a0100c1c1010384125080190b00a030f4088100680142c1075005261002c0400700034001003070a1001c0005030f141140c8042c00d4001c1c441c0009000d00380c081a2254000c0240400ca4204040f84050b008160010600a000c5a120803490610603422103800c0c0d9102040e40300600c800f60900d6051010805400144c0b40647d0319413104507070062054040d2000c80c90817a0500d52a403910360481c1200d15820384003840342c8441c2600100c1d60506090b0a00461a040401c04030f0892a122031408020800e171100a502c0c3c0c1e4880242008000c10b10074102601c108019001069040c1804000e9400d410b07402019003001c0c503203802480c02c00c041824410500b150500286c0c00064103401d074294801d11241a90181c6490400030f20a00e22494 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 131924532 1250 131923282 131923339
    0x30609020f0a08010b03070903030c14151f080d0e0111121b01060803180f0901080106080f061009090206070816150203040302070e0601020313090f050c040303080c030403050702 78
    0x4401c143c0380d0f03032181410014071098a05000040d1904828000303c3e004884e80203e207441070203041c182c0f018106200d0304100050951508000f21802840086030035180203030300c020045040300c0841c524140f405541c0ba07180410344c0040c4031420200345c2d0680c1c000c802040360954050155040c0381405503240c02c82da4404801506100e82810f10300c0031a6005205035811388800e5401540b90000150102c5c1404070a1900207a00840901d10340300c0702e45601241500038424400041292401c081c4e07640d0402d111350345910426801081000032088030b0391001d4084a9280100050824082c004114031303202d071a0014100d00341c000744131818414415400f03c0d070705000e07c1e0f003000e0080c51000c8c03c8090b07101c152800740040e4051001030001d0300b00d2006141e046101401224541a0104410f01d0402550750112842075a01e281da030f4001c01090240315448065138880e24905821560f0103454100c001d81100d0640300c01100050400d4011021101c1c1a50020409660b0704094007500b00803c80510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 131925782 1250 131924532 131924537
    0x150103060606080103050703020105030a020702040c0e090a0e06010308070309080d020312010605090607060c0e0d030c0203070501020f120c100e030304061116030c080d1514010801030b1303030609020f0a 89
    0xd4001a454483d41815050300d600c5006000302614580044a5503040a8241c50700705500300040c20040e03a075482882e80380c200a0b00e82c56440b40c121410044201030050141d44028100030b51200c0d80f01e40070411a054036440203819031951b2003400d0407111000e0a400c1200306100303010150905540000241500050403004900182e0721050119154080e140201d40c000703109114080c0040e00d6500a0584280c407803401c490b0318280f000000320300520100c415001300c1c144038503440c1075040500c810b0014000c01c2c00100460b021100c1200e564003000003c510014601040c090361000c004c1c08003548080040310240540c2c01403c03251902c9500990301181c0e09813a154240c1d60030100001900c40800c40c0c0144594007480d10b48042c0c0d60001311840443c0c0e14078040282c02407074440742c0706042003010300400e0036aa5a00f00110307030f6255a500f0404074103100b141c0004000003001c5c1c0c1d001c180d02c40c62801a00281406902e0705038080c18207034108004139400850511840e03c4030030090800c0d0000f55 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 131927032 1250 131925782 131925791
    0xc060714010e1920010806120a020301230f010b19020109080a0302030f0604060f120305120f0103170705030706230a022505060a110d0c02030405120f0a2315010306 72
    0x1134101421188681d0f801070110322a00000754aa241c0f0340d1010301210005015100169450b9000a08442c0d0740d01155072800c02254002c0b01050040b2040399000c240885201c03217950500c20115014001d401121814a40341d80c540c0646074400e400014076141d0201940383c070744c07440c5232010300a0741084900344a807003e144c0000e080b615050107041c0454800e4103911003200e041480003a03ea46101c01c0c03c1d02409010025505442103c40c08640300b0000e1680e0f29a11b9411858079103403402c00080b18030900c42040c4080004a0004421204a10350001e80003134400195100502c40ba02d6043e102e070b403921a04002c03c0310954054008252404404900441400040740034205c00c1c41200741c060700580c4400001040d50816a02c4403691414244043d400d11405c07910300415190f40002d5240183c00c0031034200320768146021400c00c40010800580300005860500790303a12108030a001e8902e903a61041c400079005c01e684903440314400c40c41594880c12194040585090080c4011100281b0b40b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 131928282 1250 131927032 131927063
    0x601050319020310142d0403110705120a1406042a09020d05060306011221050f0c030703080a1806051b040806061c0b0f060303040909060b0108090c060714010e19 71
    0x1804040d4250a841b15800e40c580300d0b910211040c811456015000d4400c9a02c08035290740c1302c0c602c02d0750108402d0700411800030180f4101c1d9604582000b00310542e4400c2c0284000103000c0b240d00c0e040e1010120b500341108201e00c10080d0114206e6000e44a86403002808010350003103504018820301040e012152140d80e201c500f20840c2c600100c028210fa001d104010311161200f00080411051614100f803c09001c200e440102d41d200400008156000103010000c040c7c010010030742c011000101001001e003c41c094440300d155520006000303e9941c00080d19643c0c1c44042800b0310307441d4003202c0380c03074903214208140e55440580320244164000d03030070110600612480024000d0f4800b080c100c407034650044c032148032900030780019414002030202041d00e00041c4910040d007400b405000c980d2181d07010001d08501c001400031011a00840e510300030070703242c10f4202d60303903154400304120503002c0701040d290041407401101d00c510701421241c4810a64140307000c64000d4002c084070b0002009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 131929532 1250 131928282 131928331
    0xc01020d06092418020c0a140714010804110112060e010f050a0905060a03020108100801050403030b01030b0a03031407060615081603050106021c021e1608060105031902031014 77
    0x10b10b10900c54510040c5540f0340242c0c801d85c024003400305207242103440c61407403a90742c2100e010080d03681800c60303401060104031070000341d41070400320744003820040e00908242d210800d0080c1040b1015060001d402c5001c075030401d40c3d6101c4401003c0354118041d1a503180c1e004109842101e110f00c5114074040c0f0004100b0310796600c1210300491005002104891440d4015104040c0050a8000d1031011400000b200c9800780200ca20442c071030f80e4000b038580314140014089448041150303010341210f100a2000981181c40d40301060340c045103141e25217580e0b2030080301030a2750b60006042c000300892115011a0045c0107a8000c100d42208030000550645045003210400d110301d90040c0d2168400c03401181445450000301c81c054415611000b030089440c1c0d407590041250000b9a50107100e0811501c441c0c41c4055015101b480d01038800c65241c040000e503100700d0480c2504851103040580c070115a000c201c81500307070424000034000c0300268401d004508000b02d9600003401c10f00c8118906407030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 131930782 1250 131929532 131929601
    0x10201021602090405030c01020c0102070b0108030903120c0c06040305070806010b030c1801110313030b0106030603030203030c03060a1701060614040834120525030303020c01020d0609 81
    0x803005481c04400300d12035001c20a05400181040c2ca03139020820007208080000e0000b040c40c40186400565030b4811440c1000d60080c05a102e00741c180c04c10701ca2900075982c04225040440c4106200d507858001d80038070715040101d1210010341c00f02d400200003081082c0814202c085401440c01e4400c517030380c1c0b08048581d40c40201d44010403c00c08000c00480704030710300004520200185852942084004411855070740310300034000046010756401c10800c845900400d0150289103000d11180c0d10b10b507000780d5280000390140801e15408400500240c03035840040300185900040222039000d20221176000b041280151000607810801c40d900b007105150031034088a000c400140005611050107104401100c1a0f107905d82424a6400b01c100ca00515003a001e042940c80303201e0f240d400e03071600a103401103030b94641405500c4d64280c40c01c025900d0341138004890b0103050260790341d601071090306d00a11506c40d02e0701400c1d01e00300020840410aa000120000b0700d00c02c020001c1280d1a06280c00e031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 131932032 1250 131930782 131930797
    0x806040c120203030a0c060b041e0b03010c0e010e060c0d0908010c0507020f01030b0409050102031008010f0e0601060f0915030e0f120f07080705060103030c0b1605040302091509010b041401020102 86
    0x1913008118803c44140328480e0300302024002c010005030507500c1d04c009000d4602102904ca589035004500000d070601b288181c0a01d104110000c001034a40c103440544011400b036801c90500c05280c02e42e1207107403a04e4040b2500d0f8520042580d02c0410301c900040d08220303141c0a030303200310b61a040500c00c505024108a604098000b0700b01c08a03070401c0c3c2c0c011405004c42e0480c00d1b810607110000f510018209001440c0034140403031413906a281000d80603801c4810304410341000c7c9091011103c1071400204a042c151030f49440d264401c9440854140c407901e2855114400407055200990b80c5a50f05500503030640c090482550450b400c403040725a0340b000c04030303000c0c280f0207420045090710780c54102c02400060b1054082505151494640301d08040e000d90058011409202d0204100108880d501d58011441d107500002003103a408010054045da00009005a5018020518a5003280000c040b03401c4002c1000384a503854504016068100744141d40790095012a41c4101c0d40c0180251802c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 131933282 1250 131932032 131932039
    0x3091502030d020c030d0606030209010210060b030c09030a1b0510050c101d06010803040f15020601120609051c030e01020a0804020d020f090f0915160c0c0803040806040c1202 77
    0x10702c2100c1900c5030095112180940b0b0b075102c05c0120814005640c0a101e0040040345c40c0180c46410041c000380c00c1003441228040b05900d029000d12000f0b28000c01c2c5da0b0040b6a21600d50b0300c0750101800710345801805c51001e4403040c07400307400b949109282c07464081502d10aa5000c0c21903942c040e0103550a02030100f181a15420a281c074052b038517142d40c02006c4080c510507141d0503050104014034100344003a00314200c0e50700005428420000f240400000070054404050b960300c2403890005c3d00c03a001801440080c48001c002c8605001403600304900085e088404e40c2c100c002384032222524010445620801300f41064001c00380c0c4541231080d51800e040c0360310740d28085e07a11030f820400c0001c1c1080c8103c0c0d03c0101d0540b41c03440b40c2c075007540d0715100e00090304440e001400c0c035500803494509280c240150b910145010403401c1d031a4403c010b80d0440560030801001040c0345024034201003503410000fa00e00c0082000290311400081f45400b41e4011541d280100c1e4a5464004840d017840c0000b030341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 131934532 1250 131933282 131933287
    0x31409060f070203091315060203070206041814160e030c2101020d0507080a0e031e03130204021606060911040e0c040e0709061704020f1207050d030c0309150203 71
    0x8240200300e01d040d5020600c0e1060703d01d0705480600281403214641c64455116503520601e5140c1c50826100d080074240600003103090100540c00a8041d1184c0c1c000c00b234001400006195864050780c024144040703018101c0650f510744241d1580c11144c110040e48001281041440c100b420007040b00b0a80f45c1002d050301c0e000c0200301d609000780058084580da82d9641c00c1001182202162003641d01031070ba41e0f5039081490074118803a0381500c1c001c0c0d01800c3d99410400c46111040f20803030219080d0054200b440d51641d5400303600181e48040e03084040d404c180000380c04012060091128510300d0320502040058542b150100700490321200c02902d01020b04100034010800745643c01c81e441146681c0461402e5112108501c940f101031b502a030110341d40c010184031258220b0392030f04100820340c0240c40036141540024503010003003041103018042c8403010030400f81e003e0040c417020f00009040100010320924005001481c01c1100b500002d00b450340c0818000f030400071401180407290300030b50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 131935782 1250 131934532 131934541
    0x203011d03030c07030e031b01090603050f0703050601030e06152d04020702060d0c17090303240402090613030b010b0301030f1e02132408071a160c030303140906 71
    0x443c0758440700050f0284a52050718002e6a07400b0040d03000c44c80d40248105014000c504005403001056420440c00e00d4144030401540c078a8410303401c0c0d4028001d24000c170f040d46403940140c00400100d41100ca050050303104000450710360750001083c0a2041e02c0d00050340c0d44400e01d21203c81c0c11411352029510b44850801454601500a040f0880c0010412450218808071210885100c0300d205d6011520301521007440c00088e140042d0b000c4010310285140d440c2100524841c002d5801101c1c04541d00101d5401c02522564103a92128501400250381c1d8180001e500c40d43d2680d03480107e1b0021304020020818040060550341242d9200000303c2146070a40d80351048040510501262000044100405a6a02c078141440d40c14107001c00a01800d64200d0080c1c440008002c5a0305444e0159081107002d00000ea440110740ea40a2400d210300b0039598200350700d1082c40070f107181c60a0580f00c118240044170700028101c9120b601c00304041002d00190480304101160101d60a400240009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 131937032 1250 131935782 131935801
    0x7060203040915120501050412170f07090b0f03191418010b0a0e0a050109050108070303050c012a020d08011a07150509010c030506090f01180b0a09090203011d0303 72
    0x1000104203d88030031483c81c1c483c2d00c4c6489000d00c400007034449a4407101480107000c0030784541200f1003983e240050340d813980b56103c007400c07600c0500150264a007240025640350310952411015080c1d07074121030b035200d0104010003002c1c1c02c00d64513180f03003e80c0c1e10030784050344825200e040200d2401e00400c1e00346903294181303100310041c040b01051141d502c0340c115038642d0f0740324041c01e80030f41510012880c05050030102d54046400c16080170112916010050006100000d400001c503945464020354034408105c0c40c41c050b1146065208018812440001098540c1c400e004842c02c45075084030f6041114490843d29180c0a2188aa420030001000280c1d03502d4900100005402082d0483c11010600d1280c01180e03012201d6010300e95541c1b0b410222682d05024082d00000c0031602074119051000e140400c1510620920143d4134000f00381516456290b08074821074180142001481c83e651071b03000019004016080b4070a500c0c10042004410400b4150754451080c14011401d5a6404904 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 131938282 1250 131937032 131937041
    0x109020316110309060a090e090a0206030c0a0203090406060801080d020726150708010504060f05030d0f0c121d0409030c0204050907050a0902040f06110a0201030902060d090606140102070602030409 87
    0xa094082000198405c1e10340500a00e081b103815512061810b2801c0d121240c001009070200d030a58100e480c42c4405690b0b04404e80e40c100300741402c41d0790303600001c1805929500c500303139a0913040b80c10401c00081d220740200003a0304849020b02504c00700110480201c1c0ca40b01c450081c0905013141080002d4080e049810084a06008100321001041c00d821b01c0c0c41c0c4c0c0601118000002002c100040c081c3e410103000300c400404c5e41c0381e441c03040b45007045c0019440e10403000240e01040a04691056600c1c0300e0521004107580280e0310209864103100020101c400154807506400d9518540d10251b043c103101d9409015019640c154224900b6400c120180c0009000400e8501c240342c004140c9948a9a508004002c14440182c0c1c2e14078240c41d07405a90721070f40c007000a000d02e504070f0114103c408a6660b03602751342440d0000b0400034078800070700c65029005190603198603040d1180c00700440c550250b030684604641030b9048124140049a880c88280100b200503001444204014000c03a0813 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 131939532 1250 131938282 131938307
    0xa02060c0307170a05180f070b2a0d080f07050304020d11040f02040311040203010605041a0d020a0521070507030806031c050d050c0f070803040501141e0109020316 72
    0x14544440d400c100403038a8483c0e401e035042c0c8801d6580d02c0c280640a940340c0e030300d01303840010342c0d024040f40d81c004280d00e03850342c0180c400c020381302d0400150340030038031800808110169040841440503814505c0c0543d512000315440001060a54001c240c40c007030707401c4c2c109121b44210307901c2e03c2c038581e541c1c0d00340002c00c000d44008440300207010300c0c1c0e007038580d43e9030090907518035810000603199880c41c140401d04c1da419103c010b0103a4410001031202551040448094407119010f03c00e0050b07802884501030f00c10382510078074103817022901480103a8007900400030a0840c0c41480324481360840315030b84041c000c1d5542070109000308403400c0064054058543d00081c01020703145910f801d45442e03098284250016800074200040c8600c0a00051050715000888080300604102d070300510a0110301c9004005482c0c00c84c0800010200602500b10000412070b244513141181002c90f0366000300406111010380780340701d003000070a08281500c20b981c4100a00045200046c0d0100703400d8071421a0b001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 131940782 1250 131939532 131939537
    0x30309050a05190201121116150207150e0d3504080703020f01150608130c0801060f0914040f02120304030503130603140105101106040b0603010e030a02060c0307 71
    0x19070540418010303c142e01645000300260948024240300040841c400c64a54503405840c0200034412610004240c1d5a004104000c038105201581046217034080d0001803c0040c90001440c0401c00c9140e14400410906c116828031401042001c15170b00c41c1050380100002410341c49100110050080c0e1415860f02c5503030400119401c01c48401010b80811201500c60141c002200020564100000d1640b1100c0300000c00801d0300ea0300ca00003140d0400c0c0308017020445c2d4007010030b0366001c0c201034000c0103691017035882d0601e5644400c1103000e4040c40c403c064082145150002d0007900b01c0c020132403044002e03100c10703010796565528081e012954200a0b07030050241c00450044410401c01000610300450086845207100c01d20040300c00d045410a404050401482c144042c4500090743d055400848a8a040700c0c1c45003000c071118882b02c07843d580725118080912040c000003040641c000c5105400900c046041d82000d1a03480c414442e000006900920008103031100600c081c5070010b0852 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 131942032 1250 131940782 131940793
    0xf010e0d0b0a06120f0c060207120b040c05120a1101020102070c05060c031213260a12020c0a0305030108010612020a0603020904090b0a0506010e03010c0f031e020c150c070f03030905 80
    0xa0301d8024044113850f504450034084140000c0900c42c40a441200601880c80104443c41c02d0554500c1d1242000d60014444480100420704001105811501a000c068022141da80c2000502642e80307000300001d0701c1c542e411028401481d481802254010754000062620301482e100501800741d00a03d00c1c00c0d19800140040c0c42c1c80500f048020303000300300194030f8101e00380803030030800c441c0c201c404c401e40d0345100805861551240c000080c0d50b41641e03603040040007529041040c4020f4851983c030f2000d2400703070862517010550010051070680e00c0039002000302e10349a41600615224420303019601008405041058500c80e400a1880140140010540c8000c5588220395070100355491001d6036250801c00015580c001100204400124024060005005006490303150380511f903604250301c6508a0340e0301c03128000040c03907075018410300310760302c0e03a07004425a201c41402540c0b82064038118046103030b402100c81511142901700518805824890b5410350003401802d100b03e03400d0103071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 131943282 1250 131942032 131942039
    0x906110307030614060f0c280c060c11040903090f090c021204140d150204121e030518010e03070e0f07090509060d030c050f07080111030f070e0a170109020f010e0d0b0a06 75
    0x105022310040d20b00ca480040400b00c91468482c6050f80c150b0003410400100040c84800300d16000c40242d28008140c400069110603801c0c22144007042d500f0145001101400010300303039003603500c110618211130782618400307804482ca55101d88228070484e41e44143c407140b1091146018070400003203d00c52540c46038458240d840c5070b416078006501130410861940d1a1b030040c000f14000116041e100342c0c020140078103866030007070081d02581280c91041084c00c0800d03000c50740a002041504079005003112411a5550891030103031000700d03101c68459000c000410290341c040c40705a0261400282501082d64400d4180316403540140740540401074440424008920f062290072080011107015020b20390401503424251000000903001d450780030010000b4010300c4481243e00140d2503d010458a0001000241c6c0703034143c0d40000c001e01c3c1c0e20080310606031005502c403500e01403080c0c0301d02072040a454015102c01a41c0c0007031a4003d01503090940004542d8040386600c0041c95800040c01501c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 131944532 1250 131943282 131943313
    0x503151b0415020c090c0307080f180a0b04120c032c04090302070602010501050a0e06211b03070608070e150d0207030c060f0e0d05030a0906110307030614060f0c 71
    0x84036120b0b00158001540e250300e94149000301543c00203108004918500785000b00501282008140a495003010707004250103d040072401e190450001003202d10741107960601200c044401c0d50121400c04480401140d0207000700d241da002c0340d405440c1c5d44003020b007040c40111a4504040c1c428420016a2076120403541ca41c0b0a5804050181e8000c00000781090006801c481040c0c0001e445030981640811000030303000d1040707600c242c0988250050700b002c0c0204102a800e03072880d10301c5901822011340b50000c1e101c003000f658400200c0071114501c0c0d0300c460680d06200c09480d0880000d842c1c0c14030364541d04205410210104051140701d10b80b03280d1401d034004076004128110006141c102e001002e2101d54020b101ca0841d0ad901e08000e004406524a03030b40f442d103181450b003070041c0032000a500d0745841e4000791400d500101d05020300c403041080c5203001d5004454680c0440d2501c4c2001c00c1000030042c0c031880b01d0401031f281a03e000e400080c0c83c01240c00046840f0038904c900701c07000c0b80406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 131945782 1250 131944532 131944559
    0x11060307020307050c0103020c030f160803041406150a030f02032b0201110a1704061b0e0118060917070914010609170a0303020705010e0601080d03060503151b04 71
    0x500076030141d5203d8115180503030402e00c2c01d088090402d401030205000b800c0c0301204443d030400d28449034542d141213000100941248196000d0041100402040b00b0311120f2030400c0c80c05455501614095500ea0002030410504060344540000ca455001d000040b1a8100d5881e400d00042c1140d6004e01d031030f0f0003e00540300c040340d155070321480b240388581105d40900039131080d100840b40e035504000c10b5440c010540c83d1403204910509840f60301103014400309900074107041f12101c502d100c0e240030641c8090034200075000b480f80000c502e2910043c26030071000e880004e854103603403030701d6005141210114103210a00034001395409030010019106c0300a10602201038410015140298036041d000b6003890741c907501c217000500c0c551f200c2c00c0351041e01161094407035078142401030300c60495040103401441030001c0089140704e4070f0f0022540d180001441c00c0c40441c281e40078031a8079100c0d000d241d2240e450702010844118401d0209002c2c2c2415000c0c0030344100b400d460182042c4d510104252282c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 131947032 1250 131945782 131945791
    0x2010e1501212a1703070209040b060d05100207120c020d170903030d090201110304060e1003090206030f010f1703070605070314011418130f020307050406170c01111504110603 77
    0x2000e83d400400204030050340d441104011100a50305202e840d802003464844000d00003003401035440001601c503079034100f010b40f030144c0160803695040001a190b0009500c000030945000f500d0850b020325081c230510400081950207031020754207a080740e85809a0b21808540b15492101c00d005110f643c1d1410000b0384a080390180d4042503090141c0005480d41040500b1078200d07030410481803000a400aa80b1200c0707402c01d0f1041d0301d6058002c0002c500400a503d8006e6000100100307001540101e2074802e03060702e900e042d5101c4071355519101030301107041d00340c0c40e00041d8205000050114411364400c0e0740c801031505000c0380c40b06c00c00403e5001c1c40710907007000420420001203551141018040c244000c0200800d03060503007440140810705210809005060100420000d41151000d1240d40300905004c1d0080c41a90b4950f043c00d02601c0400300d10402e140b1420410100e00d43c4070307005c8500c003c11483c000e0b00500d142e001f0410003540d001003058820702c5a85460800c80d407034620003540325 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 131948282 1250 131947032 131947103
    0x60c07030e0906032503140604030807080402010513030503120603010204120f111804050607020303070801050f0d0b090a140102090a05060310081203040b09010606050306220c02010e150121 83
    0x5d150030b5150118840036107107414070040d031241041000003604a41817035004441c2e4184940300e035071a4401228181700d440503040000713007420400420803c00001902d038800b00c0590b2002a640d0f083c052600f03d006500c5103c101a4080400d00040b03401e948002d25914000c5c07540103c0f0f440c3e09008a400b500c1c100340c001085162110805c000e2100500c80b041c0c01280a2003d50300c2c4d8200171100800500d01800ba251140a1040c0c032484155a02607000c00342c25442a07940d040351414074141601d501140e0740540b0240801852080d0745034041c42103c442c2ca10003042404010b04080601540b9000141230007884840000e010426030300800070800c4202e0742d8464241d5900e0700c1d1401e8200400b0140641285a050400900c01550010300340ca910070025140c400f02d95401c0c0c1c02c0c030036150800203400d0030082d2078030158031741c080e506401c05d00c0500c6181d01213480203038203a00310350b402040910030100c0f2040c18400c0401d0710700041d2441502d082c011241d1860603030180300112011800788400e26803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 131949532 1250 131948282 131948353
    0xf0c030a0804120302070203030d0b0102030d0f240803120402190807050a05040b012a1b090c08070807030b0105040b0310050405090109150207020301150603020a02060c07030e090603 80
    0x80140081c1000700c540f41c149415401d02100340e011030350780d008401e440c7c03107069101d41058803103900c20000d07500c1c040c0215905005401e5480c80356802402550140410202c40710001e01760140900054012604071070015480c00c6807031061030001a0000c0c00c101c0e40300d5002c1c400c1030b01c004035006106014245100160414a291008010300326065501ca81c4c00f03981000d5602c1d089a800c041c1600540341b50000815140441c1000307495458507100d0018541e4018041140180c0407031401c030b1066840880040090b0910820155403054084501c2c41c000745090002075401403194202640e145010304015003002d4813442112030a8000303c071040940d4846001c00c10a80c903183c02140c0d003040001f00201b0009003e070b2640700200c04418a02ca5580d44c00261580c00c64500354000c1003150303999014600820784807100100a5071090355040014403030070011490340601c5004403a011035064450442001c4071105000c0040c0008000d00e41c98082e0800c501e004d0460510311184524071a8658107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 131950782 1250 131949532 131949541
    0x30403031a0f0303090103050c160302030904050907081c140309010e070e1302041113080d0906030605010806040e0115060c060f060e060d05030403020303160605070c0302030f0f0c030a08 82
    0x301d0381c07001214521400084501410300d440100c201d800300b070800c0c81d0100d240daa50742400c019910a4440b4520921203c1c41c08a050690100203448003200440b010312541d240c521045940d80054020906140c01c8400700d110940f10405600014514504140e115080d05101d500d9640c0c0044a042e030b200e9454400c410204041404541c000d0200501c030081203041c2000e9101c6541c040342d000a00581e076442d400c1d011051038005907520910040f82548619031500302d40c644450b40d0609030300c085103010502045d0340307001c0d0050400b03803031041e0f6812001307549507003c01c405049801d007201119507a55801c0000c1140c0b880c41076015090130388400c000500c0078540681241e00981840ba130061901005005005c884001e440d042201254075000d8000c1c181001800c610540c1d200a6241c4000200c203070100c0e004515181c1c91f5401844200500c4c5e944c0b110070f8030446c5520000a0040c2c1042007a90341018448001d0040303070b001e4070070781030030203070b8440c0710918540c01981158003141c0344c2000c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 131952032 1250 131950782 131950811
    0x9040b0402030c19090902060c01021602270703021b0109080301060215010b19050c01060e0f060102011e0e0c0a080f010b010219020f0126060a1d13020a030803040303 73
    0x100144001131300da0680b00501c540b65103007819841d015802c4041d40395500c3c0020b5548010584d40c00004c444000c665072481003291103480710440d90104e0044260b2405000b0300001c0e90007580c41602d82130441c00c0150343e01d150842c000d5118a400e507921036540a1003440c401c4092041c44c801a12507002030342d6075410244040c2c135182e041c4650040842102005107c074902c410180c3e0310304c2c030054840c2103504110600580d414010201c0894943d1320340100090701c007140d0404580503020760640c00040e520750000481c2659910705046240280e141d0071007580c0c041c10b600c0ac402200390107058400119580e8000740c04407003141c0c02131515510115041d22034880a00c54070f40f0800d024001062178400c0c604010040051401c070213880380219241300300c0c690b40100e21402002401020717030709080c0d010148040b41c4001c160303651806201503501c04a207440d0f4041c0c10450b008641c940c01005a034410380e10241c04490f50030100c1c3c00c040c200390300100190444002d1070269119840c041072040b29080c44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 131953282 1250 131952032 131952043
    0x1300b030a020102190203010e060907060e1507110301110a0513061704030302070816030f17010f140307030206190809030313060507020708030a090503060c0403050304150e09040b040203 82
    0x388203400003030607840142e03000034150140f0b07a18401035503010982800028014a030882d1101000d0003814100f00c4800d001040e01ca0940d1103e0700c030115000b003a10240719811400c01e1101690120030040780000c6400f00a541054110050001c1840c2d0031514052155400c04104140442d03400300703015600e034581420b52005000e4a180c000e03104c0c40030440385560f03100040d001406160740000c0a0050100303074070440c1c0c1110b0040300c2c200303150400c5250041c9048401c0c10400d002401d69080040c2404612401904030b07003402d2b040081c40f90801d0700407207010241d070720001d42c1403103142000030040c2c03900c0004d444800340c0700c0c001160f2005100300150090310001d06409080d003040041007040f62400c028040215041100090030f962000c409a1a00080ba000446984030128070240055800717038840f0240c5209038155100303500c0c3c42449c44035500880c0130050140d0410320003800035542160815a0000c00d43c580f0081c00300300a000304807400f01c25a000e0783c02c91403c804000035410304110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 131954532 1250 131953282 131953301
    0x5090a1403040611120a050307091a03040b15060405060a11070b032d160c02130e011404110603070c061503060b01110d14040512060105030c2202090130 67
    0xb403d4408005d18191034144a40f000751007e0080100104050780d10076031002d400780c82003c034404c0003009110020a0280c100300d6040f14569410000510300c81c02200240e40903a034040c0000e41411300b4002000241e4009080000c1000f5031441910301d10310f42040948010700303810540d15682d007400c00382111840f00807a26442500c040c800003901d0403020b402101c5d8000440040c90100c1d40d6201c000312444504c4d010080d50110308103100d04050070455021120a03100c0c00c000700000c81011016100704141128090a80040d07105040680d080c03010045070700900f07034a01a0340c4614160745210842e8410007007000c000c0d1454005000300111841160b402c02000d00f80618601c0000500c1a42c81400241520400150701100b0940000d01810b44002c5c00000707261809022061400c1c1d03a81d910b003481a103101f485101002000740c142022844402070055612014a50b01d402444010307501c10328000d41000b80d0b148041e07145841d044031880d0900c20240b01407010100c600e06100c03d46003140b6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 131955782 1250 131954532 131954567
    0xa080103150f02120a0b100e0103051512100c0903030816020102130f0501030b0f091b1b0f0c01050a090312180305010b030d030b0307090b15030103031709010606090905090a14030406 80
    0x10796890540b13800c818031b054070003800d00e0045066610cc04000102090580e406030304914102940200084042065a9400c0c0c454108200c5142c2410044540c0001da110180105040c01c0205141206a81000305040418000989070850303001000640b119583d000750407610398440b05010a41e418010008600000c461000d4001407140c006014048060801203601c00029050000400b41400b500c45115000c0031070b49141d1b4914030416264000b0700500100c6007d81400030000e90f008a003940c00e000229500c007980213082d695041d03030a01c04540c0c46d000340300002440b80842051342c50114003a501c6403002142641c040d9092600c0c044243c0301c10414142800c11441e21500d0018150045681c6084082510360380e242c0820590550141c65216401000001109054200b80d5442c00c501441d80404515500c0d41019404c8030058001c02000480c98102005281003941100c2e400109440960701c003032801e0b61b0341d0b1052660107402d034482600085420005150091840d030f0b03410b820f04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 131957032 1250 131955782 131955799
    0x507050708010b09070f020703200906040911130917040602010e010507120b01090302060c07060f1b020d021306060f090906150813050307050a11060a080103150f02120a0b 75
    0x82001904d51a0000c0020b01045210003520400a100300b100200640c0c1110811001b01412074a40b4544015018000d010385118070100b605414103100d40102c1c1c507007041180d40002070722410000000041c490107001d464031307080440045100c00840460044035000003d80e1075150040103030a55074034840d01c0f0803691500c0208011645c000b50030400d208602d85001680e0551100169401042500081e4100c600802c51200414000031802c040d10026103951042421102d021a00920303410404440c1a006184035001804c0070303500c0284040c802403031541d0a4220740d902e001100c40c203500280000b165030355010011a08200d4140c0504002c00003401603509211154509101c140c40a000b000810b40c00105640e006482c3ca004599004082d203540e0703c0c41d410926135680d40c010040e60501c0c0407482d001c03e2881d240d421200040d82584a0024036881e68450a1402525160704110251584a103031800c81940c401481c01c0f484503540d81c107060402d038450b1002c0340e2040d00061700075440c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 131958282 1250 131957032 131957051
    0x30c1b1005011e05040f060f0b07020307050d170a03092a050a0e01140a050d080c010c052a0f010e150f07050f0906040b0406020109110603190f140403050705070801 72
    0x40300f01032010784078140c40c00306a82c05140030500c000d008560001c030301001560004904d0b44840c900070907840d0b008504807269a41c88004110841654010090003c400400d425480b04119405010315003124100091b0940084c3c851200107805000d0801c00c1e050b01c648203200d00030001c503041c03016040640318504110b040c0000b4014048042c061007030720b14450f10b4904603071303620810303060007404018100a103088850300e800c1d4265040000004507950802c8030070740e040c038450390070b45a802401201c0030012003d005080005404480c110044d50b000b1164444c060680c24060b402e10450210001c0400c00308100c50020342d40c20207008100c1e05146141401801941326055410407094441c8450740c2c0c00782c04000500d6803049030301c400ca1400b000b00300092510340650100c50b450707008007116101c0061900401c010f605c012035045100550040f00d04c40c07688125070000d4002c10b112403001450070b000082c41c0d010f004040310124005100011309504000341880b0000c01400084d000b032021104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 131959532 1250 131958282 131958329
    0x2040e010c0516020a031a0403090b09060a0302030403020106050a080d0207050303070b040b0702100507110c030106050604090207020d140109050f032a100e070504180c030305030c1b100501 83
    0x250303140c41010121110f810001e43d0b59020514004640c00000024007107030b01c4a441900010485054000c58214580000c0403801c000450700d0200c0010b2240380741204400c0240e00a42025205804540d600d15000c541e5445041080b000b400d100c00c018800f46801c103100906c1c0004a40140380240c000703018940000d010582e0140d040380d8000c1800c94107944203103040b45800aa041003004080c03c040900c040983c000d5401039144900905580b644c4c0700600615003610300324440c07142c00207410031041282c0f0900e42d026011961004114100b14011500e4680d01c0003c0e260481d03102d079544000c11010894100103079041d00c014a0050360030000c402e01d00c1500300c030400c9062540b0f000c800380742106000c8280300c40c00e01018106004c0185084c205507055454805000d880d004501c0c085285244641c440c0100b0107866120018103015030550390200d0b180e41020f13007190904a024040b00b200070140048005620001d08003d0202c08010744070202034800c180d114844011804110034020b12 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 131960782 1250 131959532 131959537
    0x908040f1406030604050408070f210c17030603010e0102190305010509040c0603020708070503030708091207051b010215150901050915010e1f0c06051e1311100c02040e010c05 77
    0x440445e0700150350740e00c900300703030b5424442c0306002891098060340410800c9050721140000c0f0700c403603451b01c490703010303000f0250303100040c8500140540010409940c8000c1c0c144000390780c0000090000720f40003240740007a50076a0001c030600700c03003a18002c02d034104040e818461540101812290020366090075224146498200e006480030181c00107000000d105880080f00c141c260301000302e13503503440d0105000b4103192080d01e02e00303038038000c0b60f98100c4a01d51880c00e035600503811070007504041e07481e18000780c4880c0d11403502c01c0c10750041c404404850044010010304ca64411442500e07001100c008104000f14141c21581c401d1010304180301042c6c0326400540034048007030074020a01c001603000560b03030b0258245081035080b034440c260b42c01280e101c02240b45441c450075042c411515000ca0000c8402c120242507804210508002200200241020358003c0d01401104403404442c43c0400e02c1d90b0814081c01000c80d031190b10000c114209031155500032015100200024800c06100500c5031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 131962032 1250 131960782 131960791
    0x1d040807030813020a1502060c0a090618030804030318060219020603070306050913060b040b0d031b080d020322080301060c050c030609061f1d04060f0908040f140603 73
    0x10b4000059500440a1640d0b01c45030300241740c0c40c1c5c80c640d10030050040d02c404d41d403ca0014010f0701c012895400c05801646d075040c0450321400c482d00d040002c00c07610079055140f1800e4940d01c8060020204002c0c40082c40503601a82e2120100341d0303880d50460030440342e68481c8045500140380307007104110900c0f100d8502941100c1c0140c7d251280e600c100c020b0040ca80107103038002c0c880420301052401400c5415252803041c1014840c0542e4001000200d07000720001c0c0e030300302d20110803201c000303480754440c0c91505d115080c1c2108110000d0b2036248454001120342d98000f03070300200740420500d0542c044002c0c5000d1a216030f018624507944e0a201e07010600c9420144181441e42c00c08001d8103100351803c5680141c1103e0755072910f1818207a44020031f81740c3c050505150040d412009505100000c165450040507841d0000c0f4a5841d10801c000100152403803541c45d5420104075000c0c1c022520f5450182101980310341c2085002c0d980509541d10459520121184c402d006480720f406a13a8407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 131963282 1250 131962032 131962037
    0x910050a0e0a02131e060c08040302041113060f0908010227040b03030d0b090f0106090501210e0d03060b0901080a0903020f0d03020c01050703181b08161d04080703 72
    0x100e4480b20280d2019001c1e60300b00c074003400182e1802090560300c14100c800c0c00ba104001240210755103038400e44030301d07408200c0507105000400c4144050b04240d0815801480c20340041c80c41c1100394030710100c00d1580c0341c2000d80003c0403251180a2190b10071500c00c00b0340a0800214175001018408600101c0c0314281e120481054180074445555180e200d0310385c2050203026a59280140943e0380c3c001e00361940f115108020030740c08108610b03a80d003003d03030683d030150325a8004281080015a250f100c8490b2141d140d180325445806166014007170250500441d0b002040d0220616a000d825103403150070000703090005000d010350f144c0c0e205140c0c81d0000000c00c070000e40080141000c0f420301c0c0508500c89040e104030f209080782ca982c0350780140007054040c0020045512402021070503120010034150b902c61a001e810000b04032560048003401d0340c007507070701000a642d40340b1076824400c0103170380392000342da41d034004111012110368400e100320859400200c032840d1550b501d00d41401160800f03803c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 131964532 1250 131963282 131963309
    0x807020307050909061b0c0d0504080708010b090109050c250b07030b0d0b041b0b03180a110118153501030b070528031401050a150c02061303020910050a 67
    0x11899401421900c4c01411f4070160f0b0100c6400c844083c12a0384140b15501c41e912079003400140010041c0b090150b4400000e080344226441d082018000e00001b038842c0302c05075810040d5450000c2e41240001e608130000f0a2601c1e808201e0804890304403000308101c0a0509002070a80076649000c0c0c0141803603480320f11407016444500b80312100000365010001022000400850002070400180d407040d80712445d811030405128440c90344850321280020002042e180d05520740c4e40c095003c0c0c0c151200d0801c2c0e000c1c070080d076403c21001040291118400400c0c0c55099000850000004c00815024030002d415140201e889151035031200520000d8000031020020501c80da105800300d603190700b2895404448007003083c002541618030904a400442c0c6041640c904070680520b07043d0403104010300410380c4a00e0029554440101001c020080180b140943d000580d1850080c207403071030318100151006411481401b0700c1210140c905070140c84079003800c01090703a41080c0c80302035a070a100301c00b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 131965782 1250 131964532 131964571
    0x30c25060e01050f0c161a01030303060302030616090501050f1908150301060308070b0702150903030f012102040e070e0f06030c01050c060c09040e3a090b13030807080702030705090906 81
    0x1c058087c0903031200d007095204000109060303040d048641034a0080303003500c0c0a6120500c0600c0c8152264070150003040c5002805c1015600030380c00760040b6100d0141d903900d056030074200c03120142d500c5050031010414078002d120b1080c5840c00c0c40102000d0941c0200222130540d15040d41c180a1800020101c0710080006103290344244848129803102d0228140e142c01e02c01c000944a0700111500c031252120030340005994001219030060840041c4e0030203402203840e4080c400640654050789841c1d21400d5000a61a4410b91a4900c40c44401c1d00d5252681421020107007800503124450b1704000040c41280c0c4c407007101007a410b03004002ea00c24a60f0720780f0f014000c1400360100014981d6980100625640084914140c1c54854a0180304540009081050103a10340c600c244450340020444030381480180f2941000b0401c1c03006444c030380b1854503541d5561a2455000d04000c88180c600840e010045044c03c0101c1070240008440003c22450700f0305045980c0e09000b008001714041125152 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 131967032 1250 131965782 131965793
    0x40213080604080702030d03020909071101062315070203070e060301090b070c1406070c0f0c050604080322030b04060504060b10030603030e0d08030c25060e01050f0c16 74
    0x84014121103050320071600d0030341008680c60700080ba0030303402030207651082d0303010510074422a003a1400c014504038094030744c02000c50f00c031442c215044220350359030a0301040018000c1c4064038060701400c0c00d0101a2903110038000c015140d29941d9050040a00c840e00040e0740100740351080d00e9030f5880150361a540c41c070020b0301610f21990301a28480040c418081d056901c280e200013054010390241c1c251150740e01c02c42e03549001c00c450010004070b207000c0140014100b0305c250800d85000e0002c9041c05034407107000844a510a5100c8230407079000041e2034884265078440440340c44c0c411b0203030150062858444508031040103000805c410b82e02c1300064100145540310b110320440c06000c41000012103040503005060714041680461001c41c0940307151300e01540006c026a074440c151a00b180c0f90306c80b00b4055600b010743c01e80b48a070300c000f4012400040c10841001d205004031004582030b00114030b01401c4610242000e240d08180340200096021500b04072108030100300d50840380707517800f400e05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 131968282 1250 131967032 131967067
    0x606030f08030609100e0109020702130606050307140a080604020c0115030b060307050d110108060d080309070f0602010506030d0e3c03030a09050f010e1206180304050901050402 78
    0x500e4035000e246840103004202029500c80c41098500c6805a1a18072100a4810f014800c4071a19012100180017404194018201c00c0744041c1c14803058043c40303800041502e2180d0019070008402104100e0b005501c843c0f00f404d01c2c40d02d1340d41030f4608280381038000c0031010700400441c040c507000514098425001d5224509807044e0210b000510341e22440c02018045d42550007500c02d201c4e52801046514021500114596101661840070100d41005552001c001000c05500c00020700c0843d01003400300300198400c414003c0038220705810a01440c01a00440d0004403c5a2620302041019180020b001880307004900b0010080350700c3c070b00040d120111442041105003804068002002801d040c896481c1ea0324402a1042122200c20b1554a028074405000003880c07042c1e0812560420080c5001c2201d8185408441c02e074503007012034030008250038106a03652006080243c590507103403000036801c204030040c518061510002030a0740c681030184502c034950000f000e1b5045011003c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 131969532 1250 131968282 131968289
    0xb1f050f07051b1315050f0f030f030a180302010f141b2a06120a06030609030503070806090106020d08090307060606050c07060c020d06020703020c0a1e080312070c0606 74
    0x111040201c44850980c1d10f155452a0540100e812400351024030107107018203042180c800b140b9a0701c60b45414100203881c9000c40d0820340280300010002d085440030720415400d9941d110040d0355684800720001d01440c3c04c0744008002030b0201c103040c00180e80c0640d40002000ba030b4035102c507502c1104642c2280070b00c81c0d40d40e2214801e100148421491101050144504041948130084615a500c068459140300301c0101e50003d0200101005000751284107a00000d20b1701c8000b55068480d601e640880389031040a031b000c5000441044056030f4005c28040e03200000707690700e91a951500d24069510568100c1c92028404542c00150841c10304109449a0982191050051558400b40a0b0141d40402880049805207038808a0b6050003210100c140310360203080b00f59825046d4036008000e4004800480840c010015556010380d2150354802c09494510130011000079010003100c4e41d0442a0b100d00c5040d0003e0040c0b02101c01c0c03941a5991001035810f141c07883c0342940c070700140100346070740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 131970782 1250 131969532 131969543
    0x30806011809180201020708011103060d05030f030403051803010c020303070c060e030409050f0108010b030d050d0b0916110105060609010e060409050a060f081b100c15050a0b1f050f07 81
    0x40ca0300440051000f1030000d5030003038003545e24040d1030b5a02d060036210581401c138120070082002c142c0c5401c185261005c01802031f0203482c2001108040c052103035205980a038000380001c24502c0c1c1d0030303890b83c01da401d50310800c40003080b807001800c00182d120b010040c02a024003c030222036038140140c5801c40c603240004101501c0d40d85031500b0760540284810350b1850001c012040001c18642e0051041e1805104010020701c00710643c0030301250030794014045a04026114000042180c44070078101d40204040c2c41c084c45440554140100900e006440041c0e01d681490140080d613111340c021550310003028030704144201d8181002c075520340b09a038003101c41036182508110018219500034001e441490300d0040740c1030354030440b2a503619241150401c04031401c0313902d101c0a140840d410003011360942000c0900803001c0d1a00c4c02c10103c200b44002c1030a80b154100000d0821901c03400d1441442150410b00c069512400c0c4140d00ca220151401440000500340314401d40042c10303155050b41c082d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 131972032 1250 131970782 131970791
    0x70228020604033005040308071a040614060d020d020411040519081608060a0e011104030506010806070302040815130b092103011518030c0f0f050a03030806011809 72
    0x2450a2507816041c9803501148840d181c1c210b5200314940004c1d120051010390701e150916040d41c407016803560200c0021211805d0219042800d05101d0385051701c12070003032000007503a009840c1c052003141001084e481c4240442481500141e0701c0c3c241410b48c180d0165000a61102c18501070707400c522031504241d03800194921944400c1001300c20940540d4109015215040c0780740144014000c058090321001d030300008009038401d030a0f5406480541d100c00004941c0200120420000303034000e800c1950325801c80b40050080c1e440400c043c0d9008521031400718030341751610710001c0d102e01034000c01d00304445251000c90300310304045a82494058100f2400010703410710880141d40c50058251019110004462000494100c041500c4c102c440400c203251140e054003c048403180b6071088520620154110040041132103200c01e48042d0400c1c0810107560b60814601c400740003420f0b80118441e4035554014400294004101030b001582800c0c01d9481090079000c0446580807034020b07500140ca007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 131973282 1250 131972032 131972039
    0x30114041703040b040f06110412060e06151009031e120804020102071205070902041e08190803070302190e0f0306090a140a0501021206040605040203070228020604 72
    0xa202190186100340c05141c1e058120088801c164001101d000e090083e41d20005408200c0984000c803000d0300c2141c00040d203601c00b041c644c2e0150400c0d005021011412800e0fa0204400c074410381c034180c010a0018840380c600000c002c9210154141444d002d03884500242c50f86038000c41c41c550207198426040b822019003070489520003852400c05440c1c24409100c81d458540c001c2c07500d03c4c0a5601a80600703840b134201403200070b050510003404c50b074520401d02d00080410303203840504003400c42e0090034108819440049aa2004980c00480880e04403040c101283c43d40340410f40000781d840610a6101d64400101b60024041d90017000003689080d6105d0400503404114400180012a000d203e81040407090584c0d4290446a58800790f00401004012800c405980f00d10448c1e01800c84110807019507426099802210004022030301c0c00007482481d18050003440c0c041c00f02518110300318504440020755400441c1c1d4140d0204103c0055000e07076050700500d0a4081c1d80160100e503407941c0c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 131974532 1250 131973282 131973311
    0x1031410020d0c03050105040b01120c05040503060f101a030f0c1b07030510140c030a090213060305060f04030e0d0309121104050f0405150910090b090d020304050a1703090301 77
    0x1408801c100004c1c0c039040002c07a50703140904c10701100f0f12060b90f90025090202d42013000400d1b00003050404d200040c480001d40d5541000400e11a0282440700905424840b420031008031180e0480500d281c020f503004244c60a05000b9030f42d0240301c40101110b5a210900b4014a9100743c216103044011210541d02c111003000810300b084074030850480d01c2c01c558600b01034040314038610710282c08014460100341410a1480a07580183c4161000201c0b0520fa5001032050460401c4c01400c103600d58800f04240042406480d6001140090f0301c0c1d00c0b40b034180c0d0010040d4002d60078252040360540208402e0501c2012800041d128544102d0325480046c185000b002d402079801c5440b8500b4400000d038502504448540079a42c4000100203040da281c8804080f01c50060400070144108030392401c500c1050700402c0104da01400d103144003820f020900905144041c2145010f640c4100400c0086403038442e44d030000c461b065070080201e90704c048402400c0d40b0903900070a41c19820b10003444026003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 131975782 1250 131974532 131974541
    0x90a0b0703021b010806010207030f0c05040501080f0d1416050a02030f010218040e030301180b03100b0f03060403081b070501020309030406021501050102060c2208031c09050601031410020d 83
    0x39443c001442014408001119003402c102c0307201d401608410010000140b242c1640040f103807041e414021a0b0703468501040c22a24240e205080607407280c0e401101224050040342c000c20307103074030702440042c408801c3c1104034803801c10b000404041c11000c5000748076081c410007400503401001e8a48184070400c2c014040d4121412640405822480d889070300d00d454030440e80001ca1a801441c11a031820442c900c5402d140758416407020748610301c606456405202c1d80c0c0c1d13030392407107d00042d4103549242802038902501c07008600070741c081001e0202098101070215402001e40744040c011101c14100b501640c060104020450340c00801441254500400a0026142280c0c00c031044040ca0000c3c80e100c0319420b00c119400b507041180415446020b072030003884103401d030b1201c00c0c41024210500300b99200b00750744900a16080850210904c1d65220505440c48072500320a0244c1c065640350719899007811b2100070310f2200941030660716580d003408680007a110005086446019002c040320251 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 131977032 1250 131975782 131975803
    0xc080303061836010c05091005032205010501030b0a0209090610030213030507080f0a08041a0403242d0f180804050102060703020c030a031e0606090815040b040602090a0b070302 78
    0x15424017003e05029032140044c0da00122005105e002d0740044060280c8d16544082c10f2074402464022400207078220b1a0501e4104610071400003c00b0340c51405d0403640c400c405404413900364010040b0011a60343e900400307070450320441e001c5251410484041e4000d02c1020200e100b882c0c01c404001052181c081035802c02c4800203003d54101503020f0340280e480f503005407001800f04009000601c400001c0e0111032004550b078803045031405840761180700c81ca24140c4005a4061640a84100286140d004540c10440c0c072601c00da100369a000c000780d401d560250800300009581d526140e041e401030f0b0704444a2000c404403100c0340d4465509100231725520500606001d0310450020450040c4680b084600001e85040075504244000200324003070701d0001d07080c40d043e1380800c1c42903200c2c04003842000001c180369250003404518000c034050411100c040d0401010151800700004910546c240583c041d034842d00050740e540d840c00c006a05141d2940200c16069004940c0104160300001d1003c00d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 131978282 1250 131977032 131977141
    0x1505150d050a0504020604060c08121906170c0f04060e04030206040b0601090e010b03040609050d0201090204110a02030a050c030f0414040e0604050c041e050408070c0803030618 78
    0x86680b002034030b01c190f032010f4030004d4000748100b0042288a200c2e20301c141c903035840759421a14090422459400403e01600d00c0d03100c2c11701d66803c98014010301d00c14032000307100001c201c0280359105190b0b07030b86512102c20414043c460344420310b200c0c1e42d55540418050698111180c0d15070809060096607808210740403501e0209200201e041c079030241000e40200c50b0154082e4074260300b0f0010701c54550700040c00443d02c00c2d032a801000001002031009032401241c135030000030000070500410064850480c89050703003500c1040100811507001c81190440600c600b8642d554031600721600307143d072040030b41a446007000407070b020034000301c9080b8400c450002142c041c48640c2e4880100d5884480c20b550040242c0d10400d0000c044d0705080d008941c08010103a480d200c041d00c02c40b000c070192803046804495480000911b10100800c00340c4546c05841440300a50540c0340c401c0c0420700d0050000c3d0300c0191041028005200ca410f0981240346005820070088c07801d0303225a20103900600100d1046c6c80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 131979532 1250 131978282 131978291
    0xb0d060e070e0a05060d080a0c02131b0c2a0801050906060114180f01031d2d0a06021602060a1206080c131a1008040c050406080309041505150d 63
    0xb03109203d40034060080380d00400c601281c10b8a036560a00c1c95114455440610081491b41005a640c540d24020b10100e07a841c0415480b003c0c2d4207018040050100f440e05105048030b441000c00c2c844140d03421078035510003102000101040c0d0301d4041409591141443e9070808003040048030300407a83c240991020788550004550082c00072082d8040c02c0320b62101006d0102170b002540c41e0509809100c41d01c107040004140b80101c0748084150703080c1000d810b20f41e0104c40418000c0c280a6810032030007030780e03140c101916a507100c2d0017611507036501c1014000d03c8c0c02148441d922954041c06e10403640d40100741075503485000c00d004e00100705241e40d190a041c50b0040010300d076500403a00b1120080c0040070924021400e4541800420200e40074107604000380c40e500b0041d45502c240c0700e50525682e198016945040e140002c441483d0b500400e00413401d08108000c551000030070354648400444010903075640c0060481d4070911039500c110343c40819080c80051507076000c00144040c0310604014032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 131980782 1250 131979532 131979541
    0x70c090606051c090311030403050303090d080f0c0a14040e061509012c100507060501060207030305030a020c0c040518010b06030106230906031602010c1806030b0d060e070e 76
    0x350980200c410707168050b1110075030f4803d0040d80b54401c10f0414030078200480c549600341841803842d0015003084410354000003c5c01035a000c204210084081d061910b14000e280030342411500342c4000c0d0040f030400c03c1c0444c50712086400f070002300c0d011401c0ea100d0540c842e540c4041c00440c250041c0c50560040400e04042d016100304c007804c0342c01903981030311002854000b8010f40400c00810300240401170381c20100c040690307540c0d051203480100456440d140c0307407007017828424201d0394180d105a09551000c0000c00020742c001040e641e1040b040240140c03a050b2030041542015150300603d944180b03003804005a218074600040540345840008004c296255402e1184522080c094500801c180c61040c070000307076210740652140d0025040545c00c0055200129405030015034100901c19502c004211407540d09111f01c03000341420380360011500354103c4480d4081003441c09060101500c030082c861103070300d44298010106612810400c0850032040c405501c1d195240503000c3c03da0340d0b080225 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 131982032 1250 131980782 131980787
    0x70e030a050c0f01030603081917070c020105070501090204110c010f0b0f043204060e010b0d060507090b070f0b09070609090510030f06050405010c0f0e0904050c06070c090606 77
    0x1000d0300c6070322100821152205100708040c162401d03100074101900d0307890120001e250000600151840210003100031302d10a003010340343c01c00c40340e00c111011015508110b11907a1209030820001d4080c2480c5030b444003c1d00301207014001002000c0d420508200d01042c10000c002c1c02402920a840001c02100102510b4403095482401c440d96000d02c40703040b1044c49150660040c01030b2500080f610211001d406408040712186030b0741c0400f652210006c000030702880380950107680324035200802411a20740005024009040c0300908401ea071000080c2c2c009016103510005000701d890800c0c0c82d289986011030340c2190201d001c8400c0000d10010500c01000050840b081d902c0540350030344024100100d800c014032005049a2000000d0607000001c01e00542501c0e5140e80109404a09440c05050007420b40d00c0310a1048101b0074008218030341141d01000d4010454000c40702032055460f1070800501e0024003205080d03000d400001c54800b003000c00200c40d0212007404000b4004181e68000a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 131983282 1250 131982032 131982043
    0x91c200406030209010b0a05070c080c01021506060a0c0c1703090a060306080d1d090103110a0e0705040509090c031203040308091501030b100f08010b0109051509010503180312070e03 80
    0x2901301001078018017404549001400d01d0b82c0e1189841c03820905262520714490966030704c10450764000d100440019607050094048508070030051240314141b20020a00c644200401c401c00c0100361052942044902c4080c50000e00e42218504561480003840f26107035484503155910480742003500140c0e95009004035000c40b01e04001505200e0351404040c1e40f05902c0071050107010303004260628842c0d03a42001c075400785018400c0d2030240b1800d5030500100310a5a000301c6800d0b00f1200c1088402c0385e024003124261750042c0c40d908825206c030030f20180b4100100055540c54000e008901e51000441005144501e00035501c2c21019201c0000c0b05441d40d00c0e000c5100310b2030100c1c01c01800031840702000702e501b2110502c0d2031000c1e113988441c900b001c1481600401c841d41d44603030510206692042c1da19015007012540c121100e00d040101c05110b20900e9001418000c022001860154200c44101103000f071040649a850819403d445130481d02100c8210200329401112025801c0c002072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 131984532 1250 131983282 131983289
    0x30a030212070c050301110406030f05090714120102030a0e07140d080918010801020429042709050c0a080105130308060607060603050609010c05180105091c200406 72
    0x680240609080010709540c0601d505039000300507030800203241e44003481482d01100e00c1d0051140c955007404d07001404d0341d2004017003166150410090101c10840810500c0488040b030584808802c061004501d482d0b40c24125008a944003104002e05082d40740c0041022110004c156440700f501d66400704003040003031218a400c504441c0052001405040c001e0004a100420840d8330030a042081e00540d002600107180c40c1e50081010002c0400c41401007046140c1000b07010360380d048400c4216141e0095100302c1e030f03030020385c42c445a03140d81c840389008400c004c054a00340042c10300d03800c040d0ba54840d0403401d14050040c0980008070041c0602c0b03550702071200c80c0e80e0101f402c0040d40b03045485046c050006944050101700130303c0014010300c0362100951141e0082c2101d071606003450303403c4680680c10601403203410000581034020010142c0c040a4007400c05584410380700c030104981c82404d4800851201e1030180c2c0c001849403150600c05841c070000084000d0103240c0c0244029141a0300c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 131985782 1250 131984532 131984537
    0x905061f02030a1202040503010e0a020a061b06150f12020907080c0d110903191406070c030f09050d030336030c060b09040f030f05121302012c040b030a03 68
    0x900c3c0c0e021880381d608040c19450b5100302500b095180c038006030840d828010781c2142d07a0300001c008011411f0040301180101f100742040200c0d8100c0d88815a4030407001900201039a40d5a614100540e21581500713000d442c1c001000c04421b5125070b40e0f44100c0c0000007003a4444e44041300051816031150300040d01c640c002c00411030804901064810241c80190135a0408100c140300310720064400308401000e07140c1c410710140c0014a01e0070410500807030041c10860a0300071038200030b6010f0700400b00e07000c0c01d1781c18501540f21140300c040c12078689180c1c5d040140e024013144440014998035800007106916442500b075110900c02c0c0c080b11880c00c68407071080c072203250703101510007080c01110900d0210340107050119285030740400155410508543c2210a144c2c07928140d000d042d408888904004950308000d032030010b8441e0907409440c401000c8100e6410500340c60002c5900c5032a1401e2000300c0010395162500d02c080500e0201d1120300d00300d6010710303e0031500300164500041e1222a203034054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 131987032 1250 131985782 131985787
    0x403020f01240909170a05040e06030307080901120e070909150e0c0f0103020702040203010308030f0a050f04230f0d020f12070b130c0605030402040b0420091305010905061f0203 78
    0x8400d40d0054021040185c8030050744028099100000d180144400074440d602c0540c4c460900000e4041c000028041034021761041c0310354800038010008071407416001f428420070b0000702844050140003001840d035418000c9141c0044c0b110312a810207964948a840c02c1c001c041040407200301100c2e0b412a1050f2581d005140350380c40d50500300d540c4185c151301858003610b04034103074020500b664030030303441164510000000c1001c002c1c21809841d4001d03141c10701c14801810040c0410030307981400381000d0850581d014000380180c00c24411103c0d00c1041400752010702c131540e81b69949580d003d021040c05401611002d1100b200042185076500803c0d0403001c0c188001c83c2c6820510070340041201c101c4142c081c01c0c4d140480d802c1e40807003004014540d616941ca20b05481800b06481a0050442c040c5050420b1003810154420b171111007a42424030081d12503011000082400c0d608103410640e4a16100c00400c00e00002d8102c03a01c070714819a900061011403e011801c001c1d080000a001600103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 131988282 1250 131987032 131987039
    0xa120e060f070215150108070f051905160c050307050a0515090103021c020304110d020d02010e15040303020c031c080109090204021c0504110301060b09010c02060d050403020f0124 79
    0x40105150002c101d032040740c0310440d07024004419544140c8200c02100403040c0c01c504c0395030303125034500d43c40394031482c145407100d01c116400f5010b401603003c00e91200000305840f0342002e1188054412265903070b24411a58205070070158151200d60140300d01a024800d00401c1c9810000841812500050015082907904101e40041500302d03020840c10142c00f000506e2034641d58421f410307a0864110401682c0b405c151600d480b003052485041c601403816000d60801580ea1945091030a58081c02c0500000030400c0004d400d0200060000c14a103001083c04000c2c11f43c00a024082440180e045403011124040c90818040d1214460b80000e44160010f10115250ba0002c1c1d4140b84054005414540081d20400083c1d242c2d40e4225580c035901e400300030621081c611350001da504164008c0003030074140343e4000c6062041006180c1888120504142107482d48400c44403400c811030f03800c1209007803e1030001c1d2101c80304003000030203600300a4400c11030b8064610211412180580c0002181d14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 131989532 1250 131988282 131988301
    0x105010501120b04110a0819051015020c04020301080d08011221020703060603240e030d0915020c01060608070509090403210e0d03060b070209060405040f060f020a120e06 75
    0x8100c007000d508151070b203000040c1005d1140180206044076203499210345480090030044000d0030b880c1201e07250030704050000c1e07d0702c89985101550700314075450707412040c40d417000c1c0c3c40c00783e0810900780c11510001c00050651001300c3e1170406608944d680401d140d030f80d01103c60403940c0f41c0002411154800441c203003c400d000768800000e05060040e07a9201c0e41c1da843c0c903001c951032648155080022008a0303541e149188201900e020564402003200c041e07004010b03a0340e07015100c810341c64990745104030801d0203031140384001b082d598040c040d51340f00314a80c80e02d80a00f000d44907100105003401b02081e0182d0250080d10f40d904000350003210303181e5454a0480380006070114242920006a00c000405e4189010b40000c10740010014070048000c4440101220f4503540080000d010a122420041ea030b03915000382c0107001158045001d4480e030171b2040701183c0780000142070900d00140415a146940c0180c10314a00c542c94002c02c180f03104c45860309482681000c040076070015400211002d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 131990782 1250 131989532 131989541
    0xd09080a110607050708061905180d0e030111210c0c06070302210a090201080612120c0f070906240203072a0305030913020f19030b060301170f010501050112 69
    0x5008100701c0f03140903600c0000c1c0f420241f080c0e0707081009541e07140041381941c0e100e002c4c2c00d82003244004006080d08400484a8448442c00c05010820041144401c026542500003040003030340107034010f60b03c0c4900b040415181c3c00505150600560303200c0041d80302c1c3d40707960648080034001006403240b552034102c04c038029485100c0c060f04c51441c1d0200340e0102d40715082c03003500c00c02410f180001c040303c0300d000150060400074031040c40750050410ba0300706510042208100202d44110316516130751560102410b000310100f01501622480d400069140f016803c02000c5803c00c510121041480402120140711030948140241e4400c00c182000608000c20036504030204100e040d0041c820f80803100031401140c3d10039a80f07980081030507803240c030309911151444100c852085140200c00b4810062a0190303030000e4031010081c1000c030921038084d41041d02c01c12801480166030b5030f1039071040f8024030000140b4002c00c2c41041c01c207003060741d03051003064142ca40584461140f1500c0c43d07005030251 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 131992032 1250 131990782 131990797
    0x9060a0e030a061803081f091d0d020d0e040b09010b03060a03020406120209090109110603040501060902130303030c0207030c0504021810020c030f01090201080f09010b030d020d09080a1106 83
    0x1449510711500200f12144281e080e035801c505410078003010a42002861004c000d44901070442c1d2500144800d080174042c040200c0d080f041d0007107948041c6040d50a001c400d02c200284c05400785480303a01e011940801d407032402500c180c0b0b9221600ba084000e1004456841d84201e03000240da0300180403038040d103009964800d40003480064070640320ba001c1400d98081d0390002c1403203075846a0344811441c010110a900040c02e42c0200720b041c0309170b01c0d0088400d03c0c1c83e095a0068200201103001c3c07180a401c0364001e403400403400d5544510005800300440c01e50b102c00d400207460000e03000c1c00c8a10200300482141d80264800c40c120b418081000000d51080b24104c94001c0f4661680d91036442e012848051650a500a049480c0c85042414144405207030344802d107914202c40b010043c0c1e0440899904070010f011540213030740c0e4070716540b801004000e4069034507102d1030f101c00352031a0303002908030b40d2030f2111f40d00c1c1c00e6040c0c0d8480000c1c0c8e44001b10500240360382010340300800c40b400e001d005007802 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 131993282 1250 131992032 131992039
    0x16050c06010311120a0b2719080c0d0c170a0e100909051003061d06040308060402041e03030906210917040b0c15070e010f0e100302030a0b0609060a0e 66
    0x4202131500000d1a20f40d1503082121052281810000c61402d000040a40b0300300d410100c040c07060308042c00e076458954100c11003001c3c030702c0312607110144000f000568801c00354401c00c079250300c9555240034100403e02a000c4804c10760040c044400b80e00d0001c15140511143e890360714440d070312801002803100c1c0c602080c3c400c001c034810303000a144800e405101c3c02500e0840d80b00000c5411070815400307440720a40707e18560f14401301500340458000681380da1142c0c00d860304030596100c400000d40a44103550144d10007141605500c0280c40503c040f107011644a604c0d00d0003c9a92800c0a4980c61030702d1008a003460711521001421300300c250420310005119520f440042c80d602249a100c0c0e0b00683c204110351075000c2030781800088100308821040201003009003c524103010014000a0455012810800d41032217410400f03002c0c0d1801d84021500034446045004616801802508100c1cdc0e80608039042215402d01420030344215100130b500604828541f41c880340040c1c5140b42d0501a4581 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 131994532 1250 131993282 131993299
    0xf0702030c030d020904150303021203070507210806030c0f0d0611040608040507050109050d030509040f020a050c15070e06030403020f060106090311010305010b251a16050c06010311 80
    0x7000005000602090798000e00c01a115200c3d0818041140e07807521325048a074040034024808a0380004800d0300e0750b4444d0100e10b0b92940c802c0c01c2200c0134001d00c03074000c0444980c111500e2000446481c074500d0305002d545d490055507111801c15903038144031865590466001d804802c91400d04009180c140e500070304010034a8000d00c408160264800d60006002440c00c3c4140010403006000d254000d010034a4060042c9090500080b900385515500902303100001800310b007030f501c8903003002c07100c1469038800b15158501254054442e5210190904c05400313891440d94000d14078520746070007200541c3c3e41c25400700030310091214607480a130007981540308040c1905010b079000c1207510301810f02c03039980c9132500d8078520f0254209a0210f107660f050504100049c4041003000c3c090b11101801410085d02300301e05030b40d074422048040180944894156010520507150641449006454903003000303d102c0345081c811180f5002d4810a0b40168008a0041002c2103413280d4098070102c0080c840503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 131995782 1250 131994532 131994547
    0x30c151103030f010501080a0e030f0d0902030d0e0a080f071517011412010209010e010e0d0605010306091205160602030a23010602061324150b0c01051501080f070203 73
    0x746076400c126441090784596400600165174013100303603070700022080018170070000380c29141600c0780034039101ca2000910200d501c4008081d140c018408064000c1c041d54000d490354803004101c40100c0800d1402809010400508400005088254242c00d4006404124206441c1e442080041e038000420825445102d42c05549a150a01d000b415500142949000c04205000050202421b40e00c0d4592050102c4807140c0d030004100e005c00b440910703101e44c403442814000790000400b448050006407810001000b045916440b5004e40c9000d4440d00702c500008a00c01c0310b8901c5651290540701e01c030103208a000402d40c0d0081d5401440d464004190100740300f40c00982d0581c28411074600426140c010002240c0500c145500301b68189501d010f100b205895001c00c42c44902d940c006e003248000081c032040c61681e4000445901000200215155546080000e6800c050300b100f406510702400304203040e03c82e1007450b07180001a1550000b0707960317200020140c104028a0034096020030080350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 131997032 1250 131995782 131995817
    0x1903050607020c1516150f0e10140709031b09051312030501080c0909120a021c0c0f0f030905041514030a050303041e02060d020a031401030c15 63
    0x3144218980e9008004008402d0704100144442081001201c1820001203811524550000400e10b400c402c5003140c0100a65000000300b90482d404002549810900e28440c400070640121090301c00b0000e00c0590006503c040d200d40d015103484d00414440c0e282000042ca10b002ca000000c0103200103904840c2d581d56038881940d1048500c1e00e4541010440b070020892081400303911500705140401240d8107146980d5940c150100c2064824100d1400040c0e10039020002e440030010041c0400340c0321412000080c0d6903240c51000340705212002c84244550601c80c01e03c03101c0741c42c2c10110202025038903440300514101640c0d4103404000000c6404107094649020740c10030300d100a410a01601d2604041d4003144c1011444c1d0743c440d030030003820640882c1d000815603400070307080f121040d0600d5441e8100b10310550b0803107009400450110310b80142c0d010f10f5018103154200f580f42404440385002019031074400900004248400c0b02c10f0900800e082d12604021900c9107017401a0711407104078a8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 131998282 1250 131997032 131997043
    0x30610051c020a0924050907030e01020405120c090708070c14101109030c030105010b09063f1501020706030203071403090f1e0601060309150c020601080111040b09190305 75
    0xc2d0142980b070306204406817546140c6413541541408070b1807103050074000018040c4c1ca02900d03203820903807901c0c82c424046d0001c0d4105ea000b008010540203603c1c01101ca2940c43d04e0b030b0148082d21031400c107000910928081e802982c4034541641e2258540c01c000e0b911091516280c150382041d80c82030307200c40d460160491003204610301101400945840502041516001491401c10b0299050000400c03244040c4416544440000c0f00c0e60f546030000716a42500e5000700d00c50848406c1c4900d4482c40c020060300d9003244082e8001c021400407541c44943c0160101d00b03511030b041c010f910400d0100000c522035405075812079180d2a1071410b0884400201c0352a0300103448410858202400c0007414a4041080358048000b0b01c0100310960708550900341c80d600144a0241456202c501903405c00907003902501000d541000304100f24401140c00a50f01c4400f40103141c0c1662802c400c0411149503001602c040b5000c00030618a0250060203000d030301c0f8001490030568240da11400300024509200703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 131999532 1250 131998282 131998289
    0x30905030a201506040506031f0203070807030e03030a0c0e0d050f011b0c1103030913090201020708062406090d0312060b0f07020904020112020a1706030610051c020a 73
    0xc42801c0006020011205111054002d180742e50240048070114030891814590240c022140081c09076501030110b07042441c242c40101152408400ba1291660f860303000d98040c0c2159070310040150384102c400e40c03c42e42d6900e10000c0f180d00500c009a8104400d4104000ca020b0034a0201c80c0140d40c03401150351214000c00c06c5865030042204002d90603002d2140310a032040641c000900881820340c003420b0007185110180050300085002c00ba551010011980701400c0038003800050095183c11400a02806500300c0c0140903c2ca070008910b9070000707900380900e031800030460101c000d105490504140003c01c44e608642e041c84000c00341d40d03d034044010554000e4440c2c800c00c5001060800032181e1a8100403c0d580d8144034108002032a04140ca52040d030584600c41035495500050300c7c4d00394140658802c41f800001c1168550341d000d081c441e80a90304602004194594404060301c40000710b0311003944035270801c401c000c0c92070300c00c015103c6c83c00e2a0140f0519006982c010495a01ea00d80 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 132000782 1250 131999532 131999537
    0xb030411040902090711100c0f050c1501240306050f060a02210c060702010e071809060501031b05030105061c0813062328090503010e010501090c08150d03030905030a 73
    0x29410b2800c041c6c2400702d500c6449180030100402800c090f0040d003415980e907100c004020010604031622a001c001901c5900038120300105150703528001c140c448070404c0381140f0440140700c0a400124007901400c0c0569030002c0600900000d0315051043d135401411000d82107129040228200c102c602c0c0f00120b06400c500401a900d18403141014500f135005402401103a15140c002c0704501ea02084200c141c400c0030b04140c44400000c0c4010000e060900f80280a035458000004100020011468011090800c50b06091950b605c101804c0b240220b8101ea04a100c2c0d451000e00301030007240f80e03441a4401e40300d10f03080610346c1c0d40d805071418558000401090070022401d41114403904411043d00190180601c0c2030300d600307000d46000c0309000034401c4a0509102d2540b42501034564003010b044003800070826405404030a41c0604420311034072902900d419016010640b10f00e0b6151b2040c8940c0f4503500d0800c80b20340502c80c3c0d103800c0840c00c0e0109544e80750102d00040e0140000c00724011940e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 132002032 1250 132000782 132000797
    0x60b1503011d0f04051f140702010c0921021003110a03090204140103150c020304081501030204050601080c040303050c030d0e0f06010512070b0f0403080c03180a0b0304110409020907 80
    0x202ea030760244400741c80c1640c824503000030400081c800003448400000b81c05a06074000c264019002d014221181c510025242004108501c40b90b05610441103445a5961500900d07540c0b80c54100640340d060300301035040745040302403016007000700301864040704604d0300081341c641d0000c0030600c0341c010102e00e0000940f5a44041b040d480c05018512449625401140d4154999510901c1c60a00d407030b18403818549940301048130718001d01c01d5500901c10704003904e00451180c00c0c001c9032000c090004910861801020500b594429654148038842484a40703290605580b015219500095440006440200411080842503000d01c03051801c1c0080200030a0407441c112032308141050308034600525600049100c1100e00007090400c40d4007414115a5440440d40b1030880d920480c0c102803c203c10008030304015034400401000d901c001020240c1205040a04020801343d907481202d506030030902c007007030200e51034800b007035442c5800a000003007210351607000c69150b0500711040000324100c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 132003282 1250 132002032 132002069
    0x509030727060602030f030703091112010905010608030304081e072906031c030b06040801020c03090901060e0901060807030b030604050c040e030313030f230301031106070f060b150301 81
    0x1d50280b08060005400074504003201059200301174003000740311404050b200d0688038240800e082080d038140402810341e160090082c0000f0b13001c0d0007024801c6030598a80200014042c82c0402600c0c007466100b00090321300000041d00000c0b83e080152008072030002000a00000b80e032003904c8041d124000503007580d401c1c5030000030010780c000c02000607000350000c480006a03580844c585a04c00e4045043c0003a02989190105420b03001d59003040f80386610001d41480006000806000c0441003164000200d81e21f55404440c04419240c105800c01748010060204da40144545503000c06985400500b490064001903d0550281c800390b44903040900340803402e051034080d9000310a8902d00451460038020301e40d5040c1144e40780040e003004080440600c0103441080401c80d55103111090070550b0044040e880354682c803c1c803084510901242c803420b1503007070942c16640e0743c6800100c6035080440580700c1601410b003502006510000080786460702003010800745029105000040d01007220 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 132004532 1250 132003282 132003359
    0x103050a12030b0901030605090c030a0c0801060f03030c110423010612110711010e0604080606010912030503190b0d05520e04030c03021e0d05090307 66
    0x20501d207000100b43c00d203014002181c503003091482c1101da1003100054140c1d1400085410040c4018035150301d40540d2a40e64203201c50050703a2001e549030603008000d030580c0d561410180e568148030040106100e540741d04042022030b0f1415900c1d000280c808180402c80300c50040700a4030520340d0b01d0410b912030005200d038a074040381000022442c900f04000c1c00e0030480da040e16078060360030000e18259078003004000c50b034803400c100d580b9100040d00050f280e540300c4880300e4540d103045034042e00240400e8030000d00544241181d030340040d055111f05e0b2641e101c00032462481c40c40b00c03075200a055264441e15130a40c440c41c03900b4103054028405050000d410b00e0038a1142c400c80f0071341c4401c8800c458070303200d4a0b074014180c44080e045c0070851f2040809030f14140d020441815400041034038003100401c018150410141c0c58004e10039402d89a00b40c8607520f0450013500c15044020395580300911100c0400d004d90010010000b00404031440255508034807014803c401c04001400c0b01c503107500c10130346503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 132005782 1250 132004532 132004553
    0x60f02010c180e06031524010509010e0405090a0c06020f0613020108011215060e01060219120f02031309090312060510080402041d0d0207091a0105030702070e0103050a 74
    0x70218074140007420010a40d00088800d1070058800c44040300000ca06035503001c01420701d42498802c00e0080030b02d80004040280d400d130551200c400080340d60b07904038a620400450b242d00300b05848440c0c0b0340c14100c06001c0144401082c3e21210701c00c09043c2e0000c00c0e40c030f00200009200a500034503281407096951400e1020140220001e031640320400001031303810aa8207415038a8004501e00c540d41346040240c10306101861400b601031500401248484144044c181a524139808030782081c41d50000e8001d6680780c40c04c0c0900100c00821442e5070440c4126100b02480c106803044074240743c50904e40ca860144194000c203100b6a031840c400301010b030461b1580701c4207584c8880400800d45810045031410301d80804040c00c02890000103821561580d108588040300c02d80d502624440c44950b09559000001d0014007600c501d10000070f03006964004d01c0c10001c1280340d2452022521001995640c101400040542c001d41c0e0001c40c2c0c401d091003106000b140107400504040300b0350300f030186818 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 132007032 1250 132005782 132005801
    0x110c0123070305090703080705010203060913020307360c0e01080c03063a0b010f080703060207031b080405010f0305010b1603090f12150e10050403020a0c060f0201 72
    0xe4091105845418016048030381c0048981000304999459882103070a002c0c00b5040104a00700c040b81704c0d41400070560213148580e1041d540c1c000300781c0300c2e40c00e43d5552100001c8029031503031094030240300103810444514441104601c51565410300040c40498008491190108081d0b441c643d0043d03003a8001410281c071f05082c20450b4843c100401d2032450f41c4001800c0d20f01580c20703c2c1d01c0500540100d0314003441c03106d072000c110380701c4c0381c0c1c41d004a031000720f81c0745099540607107140c004642a807448207503000300c903408401048031500e15903980c00613400c00d42c0b0940c240120707001540403004400e402c00078020f01c40c100442daa00d09050014026408001c2d0741d804051504005224450b60b10044855040e883c040382c010310030b0640381c101c5d40e14050743c109441b464100e4070300045004511091940040c4545410007011107554010002c0303070110412940c6651010086661004a0313034426074125002c3d10545d2200e4555490720382c4068003961101c0300250313888250f0a1019428840c60041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 132008282 1250 132007032 132007061
    0x1605010605040f270b04060c0507061b1101150303031e09030809011103010e07200f03090a12020a05210109150f060501020c060d180606031401090b0109050c070204110c01 75
    0x180b030225115191764040051000b80103e59a241c2211a18060810340d000030354040000d0000781003003c90145082c01400c0400c000c51344000d00b40600880c18042d5008104e03e00c000710004910350b441c01c8020309200300102900c0c124004000004041c2e0703025100141e402031700c540d401424820181c1d42104d41d283c407040c0c0e14920500c010710040305070000081d0000c509207070070340f044885000b5180e9001894007240785144140d6020510851000c4090101000211408c1c4d210942d5111161803103401d11100a52180c40d101c0e0502c581d2400460b01008400c0042c440d0314402d4148400e5400c480b401141a90500940d141d0308c401400c55000344020303601070303183c01d0020794503220010707555030b44d000c04941c422440030a00d95440e06a41d406815800f0250100070106012420104000d1402d40001ea03091f1004200310080d140c8140590114943d111999507203607842d00150354000c1601230001c0c445a10101b01c66405a43d40c1d0064100b200e01c01440035a0781c2914107210303821165a009090791 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 132009532 1250 132008282 132008351
    0x203060f06150306120a0b011401020f100504031206030302030711030a03081b0c070b04031403040b04030807030c080a03140115020a022b1410050c1605010605040f 72
    0x1142e100c55140301c0030309110421103a100d49a07000041c03103448103403500d100c541c4550140481401100c500d901e0480c0c5428800c3c0116071590801243c542c1101482100ca40d0700c00c40e80c0c80345654581d484660304c10b0203860310390115220308650000392400c962090340145d0010800703000380401040f100d00380385002c400400110300039950281900c0300051596440780d02d02d444003804050910221890024400151080152940c000e80015001800141c4501c148103454842c103580000884060301d00d0905234504262a40c1d845031080c1d030000108908010400e8402000250800c018090504d225100440d4102d03014613503889183c5c0503401034081000f84001e454005401142072101103405444820341541c5403d1001c000291a001009a01105116540c10700c4290400c003100e414160042d501c50f01c1840c404d40c030a4650640b10b540d40c0601c1000807100c021840080002d100384100004668079690780005002c560307921070400d0b159516000e150744924021202184243e584081218 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 132010782 1250 132009532 132009541
    0x903040501120603111509060a05180109051e0103020f040e0411010207060f0c0c0510050309010b0405100611010b03030d0c08010806010e130501200909070f021f020c030d090203060f 80
    0x303184411320882e40a000c611170141000e032901007c071543d10300d015140720303070b69018010020010341c0502c00160107201401c1c24669a50322172600744045420040c120008a01410000b82035400900714175414580d00700404480c050340003016100030300c10010441c04500e05801c0c19040e06414001107030440d00270b00c50078040c42da04207a5100441c28940340614040c0c00c01d251425504800c0e030413050b0f0007a9103061025031690302100951180c100c0038003d008507183c4402344404d59a042e10744100c05141411300307114051141007035107500d119074000808d544008001082c256440100e402c0c030f07485c3c0c80e103001c410255086201a40180403400080480358502845440703151006000f000f8025a00c022400511a00350001c0d40c41200070800740385c0e00004007072140b210f54030504409001e04072210004d207225001c5c00d901d8145003025000742c224a410715103440c40e0b51880c1c14800d0103a80d07081c84072000c10001000504515020050300186202841c0101807070702c00700070044e425020000c002c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 132012032 1250 132010782 132010793
    0x1140105030c100f03090213050c0702121203061329101b0f0206040308040e0402090a020c12030603011401030b013201050a0c061406100c030801032006030903040501120603 76
    0x860030104c4503e80000d01d52038600c002491011841d007400303140c2d4100070501401420b44001440818801c0382d500c80f005440148403511359500001c88994008240001142810040070341401c00694010003d03001c420300410000380901703260b1b0b0108400880754050ba82e41801c000420080096050400d0350382501c540b21545492000c400030541008802c000c011921380e0380644000d0b51b8061100743c1c03140c0d2102074a007180740d0304641c01d901c00c00441c400700e250302a00d032086410803001d100282850042d001705004641d84058846c613010741d81c4005000740c1c8244251668040c40c407501484030030b0b500d042d036500c0e180d403881102101104804a041c1c440e0301e81511000d88024005e08129032605080b50b410b0760441c0c21010041e01440c02c048080300d40b400c14141d014400e02c0708036980c05180b40c8000c0102c07814010a10010080b5050701c0c01400410980000314201194034924600d152040c10042280c68105480c04d00791581301140500407503070030001056000443c2c82c0b08100c82da2441c1c452 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 132013282 1250 132012032 132012047
    0x20c0601120303020403080d0c140702030303150a09020a030b040b1912110d030e03151302061b0114070801080303071d030708010e1501090203090d0f0c0501140105030c10 75
    0x10340d5a01030300702040e1410940250143e60055800030070b0f40761203080d40301080300a000040e017100002102501400005007614060310308998000d4000c50969644912000c0e1307421303e0b40e80c0c0950104e807691000480f1034081c0000c00d84081e40e80d801040c1c07404980140400d98264424580c03113404c00300e8118484046001e05030040350155140040200c0103400d040f1440e00c03c2d20340040e00b101403034405006060300804108200c0501390102c1e081005440d40c3c1240d2104251907810242034182403400240c50220040c00d48440d0700c02c0445103001c4440300301c908681c000c000714a5050710345000c00c581d03285c000c0f65680c0140303000f00c040c41c070f1803600410080c0300091905048240080c8800040540d0310100080384c0600094002003180340c1c02d050000b9030381d152102185568145c134800129000240303000380d070701502d22440280b2482c400520b0964031066889055420420310015140114034240034a04400082c140011129410102410300b0301c00fc100846000ba001007610b0004254803030321 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 132014388 1106 132013282 132013289
    0x20030613080c0a210f1b030e03070303230705152e1707050609060702061c0207060b06070c0e090703060905010e0106050a03080405090714130513020c0601 68
    0x20488a5002e101304110001c0ca0b11104c0700c0b1040300d12038403a86e8083c0310f4101800c080c1441070101c0c0c0741c40d05590080d400602c8041050310880c100410704010207000c03542a92519059031203180e51106900e601d1458000e4100014141c0045040003034513550b40191441d01c6585030f555900c1482205002d025080182c60351b0078205c0540000351401211405050142040c00d140200621380e0040c0409a81200c030030170a014800b03040c240340281810300c0d00d00050300d43c841350400c08215110204d0030b0b80180313010000940418443c40301101200c081c224030311040d0b0381c1c50f4803890400030184e200034045800d1005601c10080107410001d0008001e000802c40140d4070030420121200f64131010340419010032040c4000d0903e04203c951280060411002410706403407826032962000000f40d8800c240c4180600c5107180054202071000c1c2c0c4804c080d414071070390114294803400c0610 = true := by decide +kernel

theorem cover : BRFrame.Cov 131834532 132014388 := by
  have h0 := BRFrame.cov_init 131834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 131834532 ≤ n) (h2 : n < 132014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
