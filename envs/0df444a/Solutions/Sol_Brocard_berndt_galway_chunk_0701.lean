-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0701
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:13:20.929719+00:00
-- url     : https://prove2.me/submissions/d1ccc7ea-3f48-4e6f-bcd2-63e5ee939c93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 125899280 ≤ n < 126079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 125900530 1250 125899280 125899343
    0x10905041106040e07020d090b16050f060705070611040506090f22020703030b060f040b030c0c160608060414191805060f010b03010305070905061201140717040c03 72
    0x282c2d51a01c1d0b880f60010a140c10464401c00980103000c0038001c517910071001c200540e4101e1221901b070407401c0703080c2d2400130302d086002c0740d86109509007041e08190410403a0310072401c40d51469074822881c5490400d803185480303a9542c40f0010700c002e000d555074550540e02e801c4c00949100c580940440009518503030400140c04403800c0001c492840c000d403540007404454002e480034842e40d5083c1051044a20074076040c3c40e0007080520060080c000040000c40d00603124181403814911156104c3d410080d09030b40018501200f50800c02416800041c001c0d88044119010000e007000805001d0b590000148502500320380380c0180c0b6007200c11541301c0e0442c500c808601802c10001ca03c0d1040d52100c042d82d40c1e54202549034000200c0000050440341a25032000240c41d40390b01c1d082c40740016040107440c442c6c1c400c0044426004842003441a501c41108601d4903040f241030401c1d0161400040740d94070803a81031000d0400c000f00d0310910801d02100e50060b46403400e444000034150700000c1b860318 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 125901780 1250 125900530 125900539
    0x1020d0504060b0a050105070210030504030908120a0f0806100e01050f041404060e04030f08130204020715060501020123060118030b09122a01150f0810020708030109050411 76
    0x1c0c80184040caa10062416100740c03034449049480d580151018007a140b4000d50040003001182d08080c466084980c11030710a080001d40341c1e441d407049904080458240740741c5400c000c0359602e26140c3c0a00311620302180360404003414208000812089c0c650180c6200c10b1040307012107c10940d2062044840c81c005120102d9103da032141042c3c10003980c0382e4042ca1049087c40300229a60540700116400345a1540755681ca0000c0d81e00265540caa000349480c0f02c150305030f501c040158880307000030035205202d02e140c4c00d040f5400340303a00301c21102540c0105046a1410400e03170340140901441c0191320184a20b088041c0d90b5220040718034050045184100c15000f4500000b044012406140181025411740c1c910b060003072181070507801540b8440e0340401c80042054428100020810800141c01d80085008000720502d0050812640d1081ca0f0031500800c0400c0300d004280105002a46100c0c815440c03c83d842e113500343d0b2400180298840c113070781c03040401d007006164106a060082c0250 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 125903030 1250 125901780 125901791
    0x12150b040305070e07030b0a030f0314030712240e060d02030106080604030e0103090c0501030207030e030118051615080709180207150c050f220b041502030a0504031401020d 76
    0x2d40a601c45160340304110b1040c07400b1002c240000e010303025404142e2070252822040600c0c0d81c882018220410703c040d014041048480d900d0303501648000c5124000c0390716228100710059940c03000712601c01e40d10056245400c2004008929810010f00c102c4405402c51550780d140c0c04001280070754a0310000750b140d031a002000568941c0812401d11581c06500e0341f04103604c502d0b0054083e1000c0c12002071072503401c1c074006d021540c081da01a080d031900a2900c0c42c00f80c2ca1400120b802c40e009a0350340031000c09418005002c214040000500c4000b070b025203407140302d140c2104203071107032040e200c0242841720303040000b0941d0f48168011801400a400c522110041e01c0b040304000307500400d01900e10509500001ca104d6005c0e004101002c43d191baa1646001d0f182e0a10b42e40b0307174000750b0801e200e00d1421484042a80d10704046900642001001c8994491801c01c00c000000041540c410541d0800e02110403140e030402c041da011242c00615032401c9101c1d000c0d04900912138001c070180110b1070003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 125904280 1250 125903030 125903033
    0x2721020f0a06050403110309010c24090507141215090f0105010b0301150c0c0b03061507060606030b01170103151113030c080f100207020303040b0703020606030105060406050112150b0403 82
    0x26040076001314002d448090401c0c450700040358883c07241003c02da007c00d1240300554001005581c40d4004d07052142d04c00f202203c4042d543c401920f01814081c1c48603400000184580f0920546e981c0586104407942500c400400c43c05613210303000c001401e5a010403001c001102c00c08103008801480600000070041503031a003140c1089074000703008082000451a01c20107c00c0c1c003c0310322300ea0068110f0921001e0910744544007032168001007906401860403002598142e1161025019491080c5e00106060b03062410050807607a440a00310304008202010f4032003511107241c25030540380c0100da200240c40c0a07100303000c054416403900c01c0c12080005401c18000d1150740483c0156407180301032071074040c4c0c0c0300500c0d40d039049004500c030000d81048062010710a000d40c01800c41510107819030741010354440d41c0d0140d0307401410b030039005600000100000d0b880c00b0711959600c00380031541042041d00b000b0008200c504548030110320940c0d0b4a10020080c4000881d000003011013102080d52613869 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 125905530 1250 125904280 125904293
    0x1b170c060709120203060f0603100c030603020310060308030c070f1401090309060201060803040e0406090b04050a060e0a0f060c0c120e01080a020405030309061809010303032721020f0a 81
    0x44912900090b032076003001c80c501041d10f40d44126182c004000303000c82c1d1140030380c0c09400c00016054582c1485100c00c840ca4500c03003070041d42403d040d117460000727080d40307540103241c2003810445070082d04501d8a201800012009420349400003c07649007140c86450034a01003d0400424101a10244a0141c9281c40120542084041d0752203580c65440b610380d102402d03401d95019000e4140942c0042c0800c1c0036901403500741c01d0303003e80940d40c0428511100c0d120040002e2040c2ca050f10b940e00401541c0007800304902030200c8190070040142440211511413543d116081300000300042e494aa900000758410411480030136040304078040340d051345602c054a440040e11115000c24214000202100a24400d45044450180180d49402c0001c4104669603120b200c103040c84078100611400c2584485407000c1c0a14460345000a40700b40d1241e40c107000345001500d0604180c05e403d4000002405207002c03c511807001000d20310035002c518030aa052031030780c0900450511480503c2001d0200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 125906780 1250 125905530 125905543
    0x1404050d2904080a030e0a02090a0b0a0b04030201090e191e0f0203060916090905010b031e06030d03050c0d020c0a021912030f03020912100b101b170c 66
    0x51a84075440104518990901001c900722000303082d9000500481c45014001d41000d00000501c5054a8103407129500180c5c0c0c1d218180c540403001d07696443c0c180c14030b081040c0b0174405811596841802c4c00c1c9540d000900044a82c041e040300b2070140e10100e1000301c41b46550100d41707101d106040c4009100d00070040b0114400d015880201d904008215150490610849000f25000b4090030040d6032202c03040b040203c4400b00000c00c1049a1a001a80204512070ba40c0a0203015003030545c0c03801c3c00814010043c06003002003030719141007401d1041690b80094074200c419010f00700860b050340c86c16181400b03030007255800c3c00e01c80c1c000208044426400324400310700d24400c031001c002c3c0c0b011080c2e018920310101d01410901084010305000802e008003e0100e810300d0b546005440d10021101258034401602815043c0b030380212240c06646182d4014a031801000340e40c0c000c24117103000d40c0101607004000c00c400502c60140584005e1141b0308441c02c0b00240380841c10340d80e03001c4890354a65900b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 125908030 1250 125906780 125906813
    0x180504090605040b0c0c06010302090402010c1b0837150603050705040e03031608040813060816030e1b130c0c0507081b010e0111070f061d030d1404050d 67
    0x542d04c00051407204c508002d4031142c2181c0030080200342c0c210341c02d00644060282c800e034140075603490884002142c6062418808200d0300c00d0096880c5403643340391400701003041d0500b01a904051000d1101ca045440b03115550b0000303c01d06080d03040303041007440c0198035041c5c000701030b0501d103011007482000140001110000d44042003282452004143c50340030540301d4103807455002d8a04003e240c441c44141e6045402880e82619080c0442114100360710b560380200c0100d06017204124a10194510312106400242014000940c000030f086803514100050000c1c5255180040f0003592500c050408502d00c080354100305461102c0c00c05455040000c4003110302c0d204800c00480c24090108080010701c0310410090410117107140151040000801900c1c10010132441d1032050000401400000f40803021030350b401e55007400d900910700d5040700341c410901a001c210300c800d943c40010b030343d0680701e0040c5001e4940f1010014104c0180c821035000c1030380a0040d228823401d000381c0201003036800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 125909280 1250 125908030 125908043
    0x19020a0209060103090c080102181903121227030206060409030e011101020f0c0f0d05040f03080f120103120f080f0a0c020724091e1406070203100b0103060602030301120318050409060504 82
    0x8030070702e114500d078bc10340c04020b142008031a804c0c4101030140f9620b02040440c100c010034118004040461840000c031011840801042801000d16405012032508844150b809101002031503e0280111030a0b80b0b0190410807140c00170b81d200e01003035040d41c05117401200d0055440400b042101d80d50604d42202d01d80601480e1000c0e1001c501a1084604860324029100105495601c9565054009003003e54403d401082126081d1101d8590540a548154182c0d009070106074001406000d51300540b106200d5030009220740e04138200c0c00345a0105034000007041c403001c0810104d0805c401c1e94447c1080a8001c0b211b5400d090500780c0c074250304421a03549411082d0f8455410245d14640c292185255414040a1001c1d000100d00801600409032415140c00182d0740441d241c441045810142d0702e0751550807038410340e458010780c03004003030a100a50542d41040301180b00d1141040008050001140000280540100d400d000800d00280100140c03100782c281100500021181102e08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 125910530 1250 125909280 125909299
    0x13110d0c020c030d08060904020609040c120b040606080628030323030106050703180807060e180403120b011803030507120305010f0501030213120819020a0209060103090c08010218 79
    0x82c03c001802c50126492a55180c00513200e110a03c6401ca40c0900140d81005081094980c035031558029000c03003444075510000e403242c0f10358086086402e0001400d200d42d0034003000700955580234a1417a0498811543e145000d45206c01c031001a035645007103004020a03c000c00814150401410000f4030f1610b844060304000e4508c81140c1e91200740241f002241043c400f01e40801c0c81071907298030043c4a0118109200c2e280c0c0c0c185880c048990f03000600160099068007000c0c180385a404007800304d01000d078080e5061558000e4203040480311048103066840c4a0700050340c0c8108010b0b4800e006246504030710546a040083c415071000d1025941202213400311040303640309114007412900c41d4000c40721500c0c10302004602179032003003d680203100d10300803000c9001c485403010f220425103d503107a10703915110b06c9141c00403a4070080c0ca600c01d540000c0c04000140e154080c40390340c0300e10246000240c00350103103000f42c00d048140d000a84158800302e1034640391962000f0003400c58000b02c0d01d074000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 125911780 1250 125910530 125910553
    0x11401020d080a06080a031218170912010219020106050913171204030309051506060301060f023409020f0d020a11010e03031509060a1e120f020a06180513110d0c02 72
    0x900107801700c010505a0200c007502b6250802002401250300020f02c101481c440c143c0b0350a007660050301d075505048042001c0401c02540900c500300061100781c0e0101c225250504094071a50720490000e4507158442c00030300090b0803a50204d84501c120380c20380250b01d08150a0003802000f915808031040e208103003003028506600a0054891800100807614581c2000001c41e032802c400b41e1101d0641c8940ca52031502e0707d07503c00e58980301038506454a04a141d00c428400040801ca90100e603965104100341c0c940341010700e0881da160b003011000980d03912840c900c00c035410141080c198006510381506103211400c04002507018501c0100c3c010700310700121007004010305c81030700c90507403001d85154200001c6403a03101d52083c0c8098071114400c003665802c0d6074801c40450403000c42d8041c005000760002c600d40401071030042c040e41d1034154000d541c10041c85000c151980691032049910f2000c41e40c5201154110701c0329950100e16441d00c0320401c20140780642400c684039800740c060525100c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 125913030 1250 125911780 125911811
    0xf030e0904050c060d0f051302090c0301141e061c0c050c1506010c0210021014091b21030405030106060203030c0301140a030209070e010305011401020d080a06080a0312 74
    0x14007581d00301e8040c0281001c40030400075564001c00000320f6072a00d42d00340382c00300c6000d17110b40e030701c98141a01c0c044aa164244100300720440014540307a145c0a00740010302c00c8000025104000c0d0100340c80003002900f24a84407070404602160055010f80006800c60340c40140044101c041c90039400c007405001461201501c80d03004810039102e55070f110020041514554610880e00700d20181898030500d400368020402415203251a04003607846250415100071140c81900b100e18000c0c0107a0800d030408100c015141d00c00d0b030003861703340c40ba481e0240d03040b9500c03c0c070701803c1040da03c1c80400010910070b0f07110791243c2003403266510951805d140041c1a50020045078818940d41903050325681c02c0842c034400101c01c10705141d0300110700160200043e2502051140103d2141e121510151400c2000500340c5405801c211b4018200b201d84038100c0c5d8000a00107072010a40c2442c0202e6074401d40043e0007041564800c41e054841c104820060641000314017205460892050001c6620703500300a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 125914280 1250 125913030 125913049
    0x406090f021c0216020103050a020706090803070e0301090c1205011506210603020a0e040302030c100203010e09070806010b0a030b060711100504031110030b0310060f080a05031b070b04030f030e 85
    0x1c00c80003c600e004c2006600c80d1307014641c00442030b100103003000e10070f884480480d41aa8011600c10b40000140030855400070160303031244400310000e1160908030b44d510700c6044654030604050807040e030159003c010b829001800c0d00e6040c075112180d5645d8441004198060b0f80801d010101d890014066a040d214003411095a4014103406480e0780380c000c1c4450a2103000b08242d0450106102c090303039000c0244141540852040e00250700c0e94142040034001007000380c060415030340802d0080150400120300981185c6004034629224076807020207030301a20400c0900e96000400040e071904004100328207000400e800d841280030188060b0055801d4416404050b1a003440e1890f00610303450501c140d90f04583e007902d030104541e40d100c00131a103490b07101c01403e80e1280e160703801400011000000a00100f07c242c2c010030352003e42c2d8482544a1003a030040d081c0356441b80c503142e0039021040060704000c0201500382e0f644c455407404d0804880310207080880000c0d20081000610740f83c0210b84 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 125915530 1250 125914280 125914297
    0x30e030c1b120105010306150b031b090a05090a0204081e0a02060703050f1201050103050603011401090c090f06080108060703060e07030b0f040e0f01150f0b090406090f021c02 77
    0xe1100034484944003218a80107005240d00507451071a880101d90280646402944529004940003201075101a1041d4a40e001400c01800510030012507401c039890f010f58900c1e02c6025151f13610104d03800b041e5802c2c41d0f5048550002000814080c40744515130042c4100c440540a44031251314100100b00e8a013104c100c541480e81c8030b07010000140c80d2080040c010f42d4130070b00701249013000103040b0016a800c000b070026102d002c150010011545c040c0186640f200e0704400801415501040d6503050768018042c0124a640e80c02482c018240103c0c2d40348080d20071b001010003803507a00d5030010310b0304009014046107800f5060225041d1802400703000b0584001380f441c01980c0c2d0b40c00c4011001054000a203643c881d05010000d6040e4a45c0c0c4190510020a01c0107880a1400408170609441608010703220032000305008001581c03d450410082d2031000c2441a6180c04000000c1d02800180c0c10120700d1a20f4460300100c051000d5000f810f81c1c401c00340c04801c6010307840070400708a000d142ca9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 125916780 1250 125915530 125915533
    0x30d0c0203031b0106050406060f120209130504020a09021909060813110118060c03020c060424110102030709030b060d050d0c060f05010303020a031205190504020301020702120c01030e030c 83
    0xd01416564441d000d2103da41d8118000240d081d03403000001c4c2030700c01c02c1c3d00840c0803d0741c02c0c0c9482d815a078032242d01124250102415441d141e80e10010940d20300c5804228140e5555440c041811036070b80c05280c07001421848004d640380c041c01d2540c4074410481800880108010050002e0928000c0c91128400e941400c0c42c0d4030268165201c1d004950880b80c0c02c02c0c1008900e29022201030101080d03100a89110f40d07034044030042c1c034640a0320300484800a5841001c050208000d51905050f078140c403034454540000782d01c0100102a10300468001d507208455002104000d917190340b180b00401280d00442c80d00250b40c071503001b40488100b040700046c0480c3c200c809804610390280381c9000410b4460000090000142440c00080b141c081e0012401600700d058443c0c00d26900103692042d03c0b207004800c00450601803000c5074200425040da03065162240005400e40d0b80070b50540b644030380c0103081c0310082c0c54003c80103516084002c207600c0c0420701e401042c4412000000aa80340541004d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 125918030 1250 125916780 125916787
    0x90f01050102060c220605180409020f100203070f061505040504030804031119050606030d110307150b1008160903020d0f05070b19020d08071d190b09030d0c020303 72
    0x104d03054481e5100020811840c01e0806040790080c800443c001d008010607501c054403001c4441c02a580b2840c2c2c403881504c03e5040164807800740e642d100a0382c0002c1d401703d5401e4070380380c11007805a040d8003c0a0b070240c5031500a2511b4814403009401051048149451880c216900c0c5c0e0100f01c2110401c1c4d90240000721200c0008000900540e01096400e41d180b00300c59a074080002c05e0410114001421501074024606020040c28104144140c9000b58184100d9080c1c048441555a01030000c003d001c50130380c1c803603c00304000254002c440c00b20000e8800c00c0000300c4450090038040c0706454290350420100b00703100340c2c07a1080f03c440054a90007005180129015103542c011078400388030586142c000d0341d0f00010a030918000501921190070b40c130900070100d10201a042c2140c0e60103020601104000304441c20b5030010000e01d04c644c5a9800000314031050000c1000018180c0c4014010106401c020030502d50001c05448040011001c80b6080700700000304070340884003542d00a4060f0b0060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 125919280 1250 125918030 125918041
    0x90906061707020f2d0a030816050d06090207170c030409092306010305070609030c0902160204020d0204090b0d0201080f150a0b07020102010c080106080c0f040306050c030105090f0105010206 84
    0x7121640d00310007a4811250850700d440c2c000b0707080241c032000c000d494042810b10500100b1003d81c0b880a00b141c110054501081581c4001c1c0c180d0000520400382600c080003c0301d410b030b0280094030400043c4c14010064541c0320b148002c000d41c040241502d600a581c00000320b882d01c40740c00c07201c00109807800f95080501d81079009020784181c3c9000c030380041140c102044400c080c2441c2c01203010030f600003885c1551450030800d0601c0d0b07007608041e041005048040c404039040851280c2128810031005076a110038881880300d80011003402540300b400080e01c2048a0700940241080c0c8038004010041c51f1100f0081140814056200038041050b4400041d00010000d11032940f180c054020060301c81e0031440020b4400501e038202c40400b00022500c5030a40d6824400e046144810313081580180d4148240501000c0d001010302c4a804030008510a00d0041001030b5001140d2003d020f000d0750400c400f810312503403c03d000d11401f4070f440c20b0015881034455002941204c106801425140d1505c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 125920530 1250 125919280 125919317
    0x5011d04060b07060204170607080f04050c030a08030106090602030408060601030b220c1202180f030a050613030f02030f041e12030e040b01020c0f090a180c0609090606 74
    0x2054600d500c10340d9a040095944140c07030041c003219100e1400140e8031401c2441043d661410007111210320b41c0301c082007209081d0028000c60300110038113015a00765640e4501a0b103041c1781f40c84600d4241c050320f51290b00304a9010003540c160307004e179122084496103032441282e482c05182714003000c0da404040070035959402640191402580501659040c1c0c0001d0030441141c65004064602c4641e44e5120411080d0300280908402950030420b5140c0a0030045180304800060304052244a00d446803021569080001c150110381c08001e880007803a001011014424400f01e054021030032042580a40c00c2c800b0046602c62000300742d10a0406080c802420705c2c0c85101600401050b0020301b0110300b00302c0709400c07503030041d100c0da07260340000300c0020503c416502080c40f664159406190041e400c1c1da2400b202c101d00840c1500c2401c4103544184140d0050542e9880f4032071103e182c5800041401400100001135034010b40350f1007c0556aa42100c08413103107486500e0000f841c030a03454292800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 125921780 1250 125920530 125920577
    0x60605010c200f121510080606300a0b0604140a02030603031b0a230a0201030209060403020a030305040816060e010f020109020306101a070206220e16030b030105010501 74
    0x3409002030945120f4403011492111801002803443da006900c0f4040500700c04110603802002010005002442c18200e00d50340d8801074500b51081454008582d08141c02d20340003000500880442c0741c01d0f80030381400a4888060302000e0b40c44104000008030310381894021012312081d420903501969841307004a42c001e400140a65034103000410403202e4843c0c0e40c2c881004a80c44100181069908900d0000d0190340c8a2903e40c090341034486400c0340907031000c95802030940c2c0a00b40980d80d560711078001381d01c0b07202c1c0d40c00082d0b01c00d00c0d000307010061640c040c001d041078a41040840d10038004440d03100f1200803841c482c00d00014060070f02e10040d94401d401300c4100c1d0300207000210b8005144d90000b4105941151010f4031a41241010011010700e0788444118040c1404003a250880b650045002c501c01d480310b00b504156895040000d03443c1421411004050043d02c807142e03414441d127548603041d84166100e00007820107200240310b14061050a040b1380c016161240100b03050b0280d80300004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 125923030 1250 125921780 125921843
    0xc1305121006270c080a0c0302090d05060610030506030c060a0507050729090a0902131a0306040e0d080402040c120204030602091203030c160f050a0609060605010c 72
    0x10080090800c14042c05000040c21110b0043c0352240504181032103066400d503c450341540c20316880b01c2c281a0400708003030b0003070300c90345001c54442c0245a05401078842c1c0482c0310780003d1009000003e00a003c1001401900d046070407102c09035111104a040c1c85040d948554550480c580381d0801d8a0040c00902c80500e090612a00700111a1a440d0600d00396a202900c1141c1c00e10090050080040100c04200c140a0141e03007480b4040010a688040c0c0d0f001c0e1213000d590010b80480102d00b2480f419000780950480308081c01400d481c1201141c1040d80c15038003540c1840d400d552450f0020840c0d4183c01c0d40345d038640c00159110307000c000151900744400c40a100039440f11000c1c484403400244083e6011314000f6032b988a8000601004182c03c012118680d0014414000103030150011a09103e6190840251902ca01c0c28400480040b10b40018814031a040b500000c003d0b59400190b60300d8000d02e010451150f6400055819603c864001000024442408840c14517032100ba0070544 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 125924280 1250 125923030 125923033
    0xe0912070303090602160507270504030c02190504060b0403050d031e15030c0e06010503190b061c050106091203050d06030b010e01030606050d0c1205101b02060c130512 74
    0x140d43d5030726683c040703901240b03240170344041c20389015041c410204000e00c0188100b0480c4100c214281c262070300d100242e10900c00b0f426858102081c00d0610850110410030340061802c2004107a400d40304c034800304203100d031900450400000143e0800c412043d20201c9030001c0143c0100c2c20500340c01c800828141150300c4071803000341c0d0907561281040c450703880b140278001e003501106411030070100c840340219030210546099500030040c00e03982c030009490700551031211580c02250000d180d2000f403c008151107810503c0031500c031181c881c1c040d81004001090640c204400c4e40c84072000c0b03c201e5198081e403002c100420401100180c4218014510f41509030307000a029600c0e980d42c40044003080e44019442400207005100b0f1004c18407988001703000c00c40b00c0d1940702c1e1712035403080340d007246600c1500070301e0703444020140501c9000e01403501100380004007000307aa00c01c000344000f94083d1401020051207a03000040304001c905084810a071861240b4054141c41c00d002c00440c003100422240aa = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 125925530 1250 125924280 125924291
    0x3040311030d0605030c0a1a0a020a0b07050304030314010b0f130906060809071d0c0f0c070602030415020615060901020307150605040b18041403090307030507060201060e0912070303 80
    0x2034203001e0000e0468010b6109000c030f159807078201018a0f100c588040680f092800322810803d00a02d1100030b84e402c980d88005607110001d000e4203a003040c00800c1d015050f84442c4041241c0d859000e801184641d2007902d040201d860081085260b4100074012040704140400403034841290410180601d200340e0b501880f60039480d810f41d5416903e680c0c0c8501c000c42c002e001403254400c020702042c03000c3c2821041d810b5049100d80e500700030f0b0700b04c05001400740c8600003800d0901c00d20348a007190b000140c1e1404503003060f50365800003540ca611a128842e00e182d5000e071a081d08500c0850070383d020382002c0c801080b031114004100000d642c0664905410f6100030020a0700103500c4499008204da1103640001c0e600b4540824001a14205200107200308000358100c1040d03c40301245ca0341058100e42101c603204400c0000030300d2341c4900e812081d41403103407509c004204000016200252140e550090103100d68400c82024145019204e1402581001e40104c4046481c0e002614610f4082e2401240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 125926780 1250 125925530 125925557
    0x70905040b04230403031d0304030201210e0c0a08030906030a020a02010b030604030314010909121d060d020304140d05070b04080d09080904051807090b0609150a09050f01050301030305030403 84
    0x502014800c3d103407000540002040141909403040704d2904a0725004100100f81c0154155124496070100905100a50340e039140c102d07034107140045018189440800000d0308010000b0354454034100d1551090302c10480100b80e005011041d100583d0000d0100c60440c1c50713055920020390407048100045650710300300023800341c1d01001020b015a009490018075802c1e070711400343c400d00e014ac003e0030465091903000c00c00510380100c0444800c4591074107214203070704092010740b510201d12403107602504c041114000e071010342c0e00843c01035228072002d241c072900229001ea1a80240e44050010800500c4800040361043e5400c0c0d0b80644940906490048600c403443c00b1600c03400c200b5900d5540100f100806810144280d54020b0061500700c1000005021210341d5403600c1e001d0840f101e40c40d0741e1000c60750f848a0040e85d00105005254004c003c0c0c0005200c03001d50044844140050312943c400521424a4402c0513003190040e514ac0b40b84d42c0c00e68400380d03401da1002d0011402c20403401c81c0e010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 125928030 1250 125926780 125926811
    0xc09061b1a070906031505061206040908030702160806070207050922030f020f0a020a050420030403050a0207120b04033524102601120b0c03070905040b04 68
    0x910814441d1203094100b41005001012206040301d400c80002805030107007d00d60b0750106840800600391441003466a034000480d01402c40c40078000c1c40404040705102e0a590041480220035a00d000042030440e9030b00d500d2a0b885e41d0644403140503801c01030040c8420308100030f07002d42c00000300301280d03030001242008003255007600405030001000c2d10402010343d681031201107150b9460a00408152106030000b034040001d07449450721503982c038030500c10808008000c098040c080384030240d482e440c0031704001e0b1495000e50140c0c1c005024038a40424203a82c400000e003a42d98000c142044c07640d0382c0348e40175580301480d130140500c994601e0b05690b005c241c0114624120a25440e1121054103081121025007200c29940300640382001c01c000800c0d485440d00c1481c060f00c00d10f000b1541d650102c1202c0890302c8110412042041000004214916201243ca042910a88520501e42d840c01c548040c0e60005403010070005840400800103032800b40c0100340110801400002e55648418804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 125929280 1250 125928030 125928083
    0x1305060a0c0b090a021314070509010c1a0405010509030c0604111c2003010603030c0605130c0e0106020d030908071101020322080708120f0d09020a03050606040c09061b 74
    0x1800c1d4080d9030007408604040c6d108040307804403034800b03011941c84003000400580340145250308118000c22032080396031040540311002604840d03010225034807446450900341088406545a40c24280420720140000088564407a0340c40040c001c55100d65503082c50621441c0d449035845074611841e6815001d8002c0ca0320855881103074503e41c807440702c245040600c03400c41c1482d4420791500c90100003103a000742c00f11004507405200000e40382d6134503800d10140309045d00040d2298000703000100d0020b115241c3d0a0681d20300340c0071070300d03180144002102560111400203041c0c4130103004540010b40782d20022102000305005890411800c400040740990b0b022a503240640708110307041003072100030f211110240492402910226510100801151081c3d00031407000355800901200d0a083c591720161580741c1c01800031800541c3c908002c0d81c0e5040c250f4000c0c0c412440c0880ca4050203011341020707000c940c0360380c44000b49041021045151901c0024041c3c5522000c0041c448001c40c021005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 125930530 1250 125929280 125929291
    0x3010f06180608011b0315170a110d02060d02090f03030c011a0a060207061404051905010f0809061801020c010203040c0611030703090e220303060501030b061305060a0c0b 75
    0x150821188604504000d407641e50f03220010076458240d602e10019000070078080010802d00b008140011881e041c5019205d451b03011021a81020031a4950110301090b0b04c12524020b4201e180203907926410440501c0351018001d41c0300c90100b0580903102019000780c207207608010300590b103c0c1010b901103410741c1d014000f40305580e59107408162922107019042070150400790b0b2600403090401074042d40e942100c1c082c0900307100d0714410400030104000101c8001d003d015141048185665801038282c1d280c41c060540412045150116080d22490140d44100c070010003c015989405880250a1844c0e5500303005030b540070004030351a80c100740029030103544a00e0480082516144c1d00512404440c40300e07080c9500104010310210b5401030810701555210144d100709501c1b40c100c03104500c00100d9002c0c0303940b4070003040001171682540c850b4040b54000c0e2400e0241c08880c1007081454814502c080c03014407a9400140002e0400602903c03080200e41480f0035075071400d071100205860300300c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 125931780 1250 125930530 125930549
    0x21e15010e0109110301031a0414100203010609080a020d110d0218040201090b0a08040b06010c140c0f0a27020c0609070303030b040e1507180807030c0f03050a1103010f06 75
    0x400140f052803054000c3d40d41e07421a01c50541d41580d5401c11080f81144020641d02c1c0c0040114082c060511648a805251035045480400c201000300b00a904240300b0000400c694200c00502600c011810003800780d40208071174000c140d41d58800b0120306403001c0954021110110000050301c5140102d613020b0007004044985160510004043c540640c001d0003400009000340d012064020304045c0d00a41e0100d41c04000381d80d081d00488054043e0b0001824124815221010603040400c02405d031034070135600034070840c1184d0244002e4114500c140030502046038032120000d04203800d2490b508590500c00340c43c203500c000d9140d19103030f02650303403131240d4000e507504100301034151060202885045e102441140501003035642c4602100c0c031180040c803010000600740d18070914851072584001c26100c3c1406880d00c1c0103603035560b8035010441d40500940c0b40410b07a0036841c030000080b03e50210003481d8440469a41c5240700c0601004280c056480b9502ca460304d03000f501a0303e018141600 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 125933030 1250 125931780 125931809
    0x51e070501050c0703140901020c0411030906010b04180b040b0d3507030503040510060611190c120f080a0e0f0a14040b13050f01030b01060f021e1501 66
    0xc00d9421107501901001000710108010400a41c102c826902c4c00803042d040a51140701c050010703400c0560300c04402d40d00610f05640c00500c00c6425004d5402014181e0440e1026a00c400c40c01c9120f10841c014859000c0200c0700e07481c40706205403c500c215082c05800420142e40391030100395211000b07441107550481c548500d02c13450b4031403140c007008043d005010b03003c64000c3c1006190903100304400a41003010000000d02400000c0003160800c1c000c0312401c00001341c2d0f542c802031800000803180809800750001035000002c2d002d0750880d00310340001b01c15003a40e151280c2000c40b1207511700211800c00b07084000401040088016240c060b100e500c0e1541e8070300d4508104112000118030b000e2042c1c25084007404211040e90f45155105400c1d503002900154a500041c150b1090466034603040f070524042001c0b0003005506941241e208a494200c9a6220b141c01c0d9040075840c00240c0c0182d000311000d410300011021004100e02011f000d8038100b158403030712100050000d07048015180e2444 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 125934280 1250 125933030 125933033
    0x607230a030f031503080d1e020316020f0304090b030a050303070201020418090b0f15090c1e030108210c03030f04020f010203070f0f060e06011403010506010309020f010f051e07 78
    0x300c1422600c846500e41044044d0303031a09030705011040c07808041c2c0031840210310481c1c14501a40b00300980048400b00c89048403d1000c10006544111900c41c412844e12400281080c00020007813403410006014500f00303814030803010000d0024201c4030740c0c10b100b01c0c8058800b088041c802103000da0381d035500140c1d460f803c0503000321411101240b00d03103c26280c04d580c50041651480201d40007041c04a40b0440d90719144ca0b440c0d00c00480c0b181d4075078040711030014010030f00c541034020051002d11b40c82c1d8049080d145900399a0a0000344581d43c001e40101d042e9000217541d155a1007020134110100d1400c118030241c0b40751568104541428415242000340002d61404000c090101c6038248025407401a690f920426a1890140000c1440c00000c4540082003466000f200c050010001101c2c00c80d81d59698a01c61a148900ca690003075280c50003081c0194402c0c003891040742c1c1c000c0d00e01e154424440d401120140b0310846494100320081c41039005d807404e1059449082008550415210182c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 125935530 1250 125934280 125934287
    0x3010219030b031513170903030f120a021c0b030a06141008011a0105280c0c050f010504050f010c050d05040f090506091602010e03040b0301090b01020f03090607230a03 74
    0x5950b60702d20b02d5401204000c2030f913004480240305546e0003038402d144a03405d144290500d000d04610743e50f041c04081810000d0545103405003035040000c11220800343c40f002e2481d4201c1c810503940e59280d5040d04000c7d12144299044003a60443c084d0446101543d143c4900046445506070b40c0c05c445464024045001d400a42103006080500000c000031100b11400d100c0440b20307001000c2c140540440c48440d07511408c101d221040304807100c04550b41c0c03040ca400030524140007904880f40702a50001107000e08243e41c84003200340060310340900d014240020400000610080e0f98104859030b5071840011b501400342140761003280e1030742c43d1120709000394288207242542000c451340386071004124181c1e40c1d464002d1780011200705520f5900350940c2c002c90250001c4944107a8070700c400a800514600d103440203504071042c48504001143c00140126194800f00c20000f243d0386c0280000b0310729250440c014400c151080010f113882ca905201100511400203010105540200e0480000d0540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 125936780 1250 125935530 125935543
    0x121e07050316140c19060e010207080d0206060312040e0a05060609030f0303012d120f050102040f06090e0f06090907090516030b090f0a05040c090e16060e0105031503010219030b03 79
    0x1c04c4031100300b052103205d18110315005a104130b03000c104e10003001480907402800f5400140c15070700207451248a0114004c4c0d510300f415294076002e4803c0725540392201445506403403c0d5650b0652a10050711011140b2010740b00107400c242d8400020002e540b0035680c100803940c00681104059600e035032410035414004081c02c0400124415500c26884c08078060103544000d994100745581d8004c0350ba400c01c01d11004001c1002421903100140100d0503100740c0e4030305000c840103070b51000c40f03846d11080342c42240b030810f4a07030404812440021451901d403050446922600380e004a5030324565900c0103070b0596809503101c0c00f0204086804100b21607150060301c0c00c1d803800f071313135190614203100200c0d540c0000c000345851041540c49000c60204425207003084006d0904110070b214004000140b1a120845040304000a01c50400002016409852402c903020816162181107a454404001c2119481c0c00c03441c0c4e155608200303513191181d4179046144080f8643c1d81c005103011469050500e000c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 125938030 1250 125936780 125936803
    0x160b0103200306040204270c05100c0302031c020c12071a060105070b090106030b150102011d07060309050a08041e1a0f0a0306030c08010e121e0705031614 68
    0x2070311040303841c140e51030018801d900268192400503005081d0300001c0041415011030790303528080c0440391420f010703100842d102500c900310b816818507120b59000b900d44d442c0a41000700541c1060120002c0f81d414200e00505546c2d552402514002c3c0d80c03144242020b40c010301c154111a0041408018024100d0f100d2001c0c04084e03419910034103101001030807600807401c0080200f02040006851800290091001194420b490000c54240041c0e1881c0c04481e030380300c4c0e500540c85d100d40301a4809000c4d0621028140d0000a02840b5003002411800792441882c00c0e00d03140308410130900080c8010004100500442c414001803241002c0b19034144819548030900c0650140d0b01042020140c40494610356a0100d0340c40d51265066800d81c013404080e40050801c8604810010f02c20740190405880024840250b500820b042041c80e92580640c080140e200705490014004a010f0500201090f50040044030b0804550480f110300e20702c5000d500301c4042000b141c0b001c07540801005103001c40d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 125939280 1250 125938030 125938073
    0xc060f0905060405150318010c26060916200109050715050a05030604090506070e0102010c1106060108040302150c0901090506071a061c0f020f0613060f05160b0103 72
    0x907252000048010420581c035a00c5e04000101080d0764201000601c142d02d0b0040d4020b202c46050400c02406503105051055414020118240340c101031814506119820040164105840f802c400194070300384401c41c5014482c1c80b40c2c0e4651442641b42c3d200141010540011450700708074902541010000e90140d5091584c0c6404026015003290072390300281c1e001d19110340c032a0346403400680034000369080500303280208014042155407040c00e0309502c00d0300b03800034030110306841c0c8100d84003c000030100001d500120042241c0b507228500b0960041e01910495100305c000c06c80030710040f00c06441d4010172103000590050196080300d1048010b001c1202c0342401c00541362601e28060654840300310324034200f0710002d00c060390b9281d071048400d56106c012207114041c910748250080c0c1d4404060f840342145200b110500c1ca400021140810b44100c10180c00d40d15040c429194801213044007405d00a060003250b410f0800700d0b4084440e54001e904950a651450901205100300c0748a41003e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 125940530 1250 125939280 125939287
    0xb01060e0108090607050703090b130905101202060f0408070e0618090604020409020411071505010e160507021c030f080604020c19020a050d0b0906090615011b0c060f090506 76
    0x24020440175480941070404959401c400e00c0c0440d40b201250b004101e080001007100d03915041e0342d14558041d1100043d04000d26140c050066020102500c42c280e4800300444403070340142810000382c07500c10060544142085d0f1503240345810b203280d9411007600c2c2c0f81070a0401020703141610030755000740e642c80c8003c0c801c0d003418030206465000091019001300d8031445480c0854607039a1110320074000500b01c040d19a0901c2c6000d000f114a44003050402508040001c00c8d410551010f0500900d5134041d00180000c040b501079610b038219610a81e401200050f402000320a10f0b01d40b028036510a42d0f40d80042c482c0014013420b404009428540524810300a402c0710100026140421855030b17500500710303480030300c002030001e0240d801c1550410b034414089801c010120004034003460300039080d40d802e503a8603158966030700320841e400484150350490751680d075400b510404c01c000d001c0110654400c400f54403091b00d00d0401d5403090000400441c5c1042c2d803264400110005010111402440d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 125941780 1250 125940530 125940541
    0xc0f030b010503101215020c03040512010b030a020d050a0206030c0d180b0604020d021c021c09020612130f0b01140306040c0e090316030c0b0601030b13050702190b01060e0108 77
    0x800c3c103241c002c17a0703043c101e007104460034444086000900b400e031b400002e40d5548101007641c1d0b280d0704507109140c040d42112504860541c010300a08198040160003410080024dc00f0060040100d4606035214015503024034056100c3c076000303521842840c000c13195288401082041185e1a05070f42c1240c84201840c1d4000207402401d03103a40106040b2805a1191303950042c04009110f90701440210101090000101101c81d4000e4800107000d079038040e2142c941d00c00c8240a03561441c5000758001c40c10003410303403483c40c50213045410418802c00001103002035940c90030003028a0301c2c2618035103100001000040145100030007580b80c02d5020704002c0c10580e54003050a031050080d001859111303c00106040401c1094078000001c1280c5440d40c0c503000e04014000303076180701c025298084010002241940640542d51500300040c0c100c15051801d02d065000810f0040c20031805c500400c5035204280c4030a4158002060152002401b81d52501c1e4000c0d0482d24001c00d402d041c021880100305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 125943030 1250 125941780 125941801
    0x93b0c0f03010f09050c0901170607050a030207060c20010c050906030414030d1a04020702061e0d110903010f15030b071e02010e07061121040302040c0f030b010503 72
    0x1a410400d88003020114000800240542810a410700201e807400e90408184400050503c50382c0c0000c1d01c0c0301941d40d07294001001c101c04c11080c24010b2303078030410100d895280301d4001000c654102d4500181069400e660388016100402100d43c001620b5011310365412086125180019000ca80200000741190780301424038014904484d2180c600480040c05200c0d41c0d82039002001d810900392981ca1311a103000c0c1c40205031403081002101030420041d01541485e100300ca440307940003043c2c0c5040c1f81c0c2d00b0f640b01e00d0b00454207000e50701a0b80b003440302c0c4c80c011a00e40940017004c038842d04055160012141498215084440c94012141c00e200301001c129404a0f000740070340b0f40040009c407107641c4028007500e91000f002d08520b6044211116034800f1a81907002c07011004511044c0d072030141c0e46900072951403246607508023868010080303a880046510701070028110260500314109a5241c000404480c40d405401001c91152207404507656418444d180030742c0301c2407c04508509080e01808c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 125944280 1250 125943030 125943043
    0x1204050121060305030c0604120206060109030623101805010b0913060b1206010e01020a170c0109060608030a0822080d09060f1a120613020109093b 65
    0x11042240a410000c003074685030b001000515081422241d842c0d2914211540d900c0d0100da0a480d00c2d80c1130101c5a20544c4045003240c040d0505135030300b4001c5c0d4210b4a42c00020440601c50140062010612124002c1a015a84c4c4920454a901115071f841c203181c040f01e451203602c0d031140e203d1902005208068010003030f148580c00c141c8400e11220f200350700040040c003031030f08a209441e1003c00c00c00c841c0d00c6d04400039442448282d035000e010780352950040e80e4a40101270f00600c0071004441d044004000030380502507040881c1c00101c0c9024140e168513007110b4454201440301d03000040d0f229030f042d40010803d034104d46050004000d000582804102c2811184001000708000007040300e03420740980c01101d1300d1900400200074810728411302d0801041200051803405441c0110b4000c546804100d0306000c5446901600d100e0ba6581580e001510034820105d050203501c07031002c01d029180e8483d00e02050311051720b5041c1c014034403500c4484207450032001c0c06561042d4180d107405140c042400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 125945530 1250 125944280 125944307
    0xd0503060a141f09030f061b03020315040509011d030c0106050a0602030f090a180606030e0a26040803030106180902090105120601260f0a060f060e030109170c12040501 74
    0xe003c0d042e0281c05045a010b007841d031003d001e100c01ca45140091100b96804a0583c032944240c0c201d61441044041d0142d000c11210310300d0185403c400d2242500385900302130b900c0342050000103085041003101c0940c50049030201030803540041942c80c6400c0d0240319020250208640c41c0400c580f40c980020b6070ba1052854200144d074000c2010b0705191a800480c801070411b6038550070b002d0010009c03a400810262007a00c2c002420025011415540842c0d1038000300c0c3c00041c40c1400341091150380038007840541982c442c0410401001501e8402403003d507004c0c00c01550743c03940c3c0005000c01d09880081d550400c0c040f02c8c1c0304010300c52490307070400704132101031002d5510320b04286c1e107802c0182c5001140d61030000c6c0200c920014603194201a00070700d0311071480a9001f000c503445131001c1e401140d2031800342e801060003600b4140080c1d4001c00b00c2082c45400200080760070401d0303076940074100740c9081da0340301e20150108012550755020f100031504e103c425500113003094035040000345401013038400b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 125946780 1250 125945530 125945569
    0xc0c08040312050d06030609060c030c0903060209030721050f0715120e07060f080a0b0d08070813060e1c0c0612020405060f0406080a020403020906010e03010e0d0503060a14 76
    0x140d00360b006024200343d501c43e03e0b16400c10401d031a80c07414000040c004040084031524500811000240c1c001e1183e5516501035680e04101ca03415a40d48100a40c40032070203a50510400da40001c2c10521511036090406031165642460756840c5000c6141000003880d4164903044007405028140381ca12280c01c0141181ca00203040c004c075002a4002400c070215080300900401001054594010807101040d28540d620014a80e403103c4485084984664900da4894801c0c0c1100012a200078040d11305203001d007100d030303103015480541901c900085d41c0c00f110100d500030107030a20301e150034540035042c00c082c1c141140031030806a80c0d000303034501240034041c107119500500f030400c8a4158140c501501002c1c002542d245041204107485400a10504000400200000c0c44640c01d50098404480e4090724194060700c894006407125840715504580541d654034a40f40c0040081199910203030094a44a40e2810003d00740034040303030700d5000700341019059150b160035900e80005940309044444d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 125948030 1250 125946780 125946803
    0x60e130207030c0f03030c02070603020f30090c040501120b0a0c050c010f060f060c0f0f02040b0d0b04110307030506010b0a05130b030105012606011805030a150c0c080403 75
    0x6000c2d62031003000c1502038110548801c101c800c054260b0b00c15501c03800749230201e03045940c0d1313403404400380d00c0751482d5149042d03414071106003403034840d00da00e52000c410180002038003250703101d0200d588181112881201c2e4030406410101e800d0030722820380500300b06048201054204d844030804010b000d80b090328885c0d500c42100c500c0c03074490015128003464100c004d05c0341c2088000d000002e03004a00400701d50062441001881c94080c0030005411a80100280510041ca807185034290802d000c0a0f60000c1c0c80e00610101d036500c0d03044021000d03224080a00b207505007420042008203c81c2840380c02070744128014000b182d0000b518a0440310205039a555821000344120b5481c0281c101c500300041643c9408a000541038000c0e60507140c1c2a40c41d801c0507040c0c02070441c07021030740c3d6412108611a00c0c01050310341d4031a84042071081c00a00d905e504188d91200803d2074070840303400941d030400c00d9580545405065028092148071345240c40d000d901566150000d082c880e0b4032008003c0c10160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 125949280 1250 125948030 125948033
    0xc11090703060510020303060901151e0302071e030311031017030c0a03020f0c011d130e0601120b0a09030f200706050309060906090712020310050403030b0a060e130207 74
    0x20b030451000303040d000d13050101d080000c200103540e98000f17451039841010644004600a2a02c519010611680b07642d6408201c00d41e0506000160300710030400100350b020000b4030b011070034502d8003188a0000c407202104071030203410003c04461101c1c03d1245058010400c3c4a002c03a00c14404109035003072a0b041854024010781103603e94070800c04004130320701030340101c00141500440d25076030b804220700c142c41d00c1900c44d90044030504d03a400075810b525541800154403030705090880040d04204c1d0100003c21844400c0b109103004001d900a996555500d203291040108078110680c00c42d09500c000c0c40480c80569025091154403034034042046040030000443c40c0c0c68a0003000c08140d5001a00c0038651110781c01081540100c03000c0c10b103403103000003196030300500107012441118500003502c410740c1864285801381d086210147e03414413440d01101001031207485928016403103918001450030ba0031042c03000207460b6602c40c0d002d00044100301c2095450b007400592250441e885c0060740d40704903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 125950530 1250 125949280 125949287
    0xb0f092a0a050a0e040506011d0a050619081c030603020a0302090402150a09060e030309240f0d0603050706110607080a0e0102070308151e0d060b10031b0c110907 71
    0x940c2d01607039004a000710009910b50748840f040b800340d8000c0c41990300a03a201e549405440000e00d030144902c1c000076000038070100460f80002e030003070781c02403240307989010302c004c10b011003280341d04076907003a4014500d40c42429038919070a0012079541e080038080310745150009001000c1521010f40904188000901150745482308002c1482d443d1034500e0308e801a400b001001c28070b241c0030300404100c0742568500d071403a000051320a0791200130401c5403081f5401071407206c0100001a4060710680500c804003002e101d00c80500b03100c003200940025028074500f030007840c0400fa90700c000c2c00e101040036604d80059010411943c000c000741000c803c9602d071700a000c1300419000343c000859501c0031030900109644100c90300e001780c8030011a00100b2420008000b0b4061508000c4480e0300056034042a140c2000040c0d00f441d43c0c091500000c00b02c2100c00805c1c0780d070058201c4200000e0755020340c0c1907102c2c90b0300480151200c4601c0c0c18a4002069501c01c580070080c070303d03500d10481038100023400c0e81c0e10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 125951780 1250 125950530 125950549
    0x601140103110c06060405060f062a0f010b0315090607030908070f0b0a050a0b010c0b04050304080a0c08010e0106060c081e0406030603020301060b03040f29040b0f092a 74
    0xba00c91841d60310318a40c200707140c8400003a200b0610450800000c103009250880342c0c0038075594000c0c41c1c41e01e40030742c0220300c074441d000c105543c4034440b20305a1030310400342d4140103048241c03029030004030300b2442030401c060608014142000081c40105d060080c0350900140d42d981c40201801c00040705040c5003420900d03400350900c0104000c544420440410065100d160300031004500284050348407120200c06444008403000d000801402c11000442d0040c91140e400230b004006492426031107000306801c1420010042c1e64000c002c10702005025024450030300704032841c5000300031040c02c00000400b45030980001804034000441c8032110310b01d808055406410300084080e42d02c95544401402800d090722050b0b10075440d000300040c10f81444c004491041e68086010a07040d6410361340d03899501071540d002032002018004242e91072206031961402280118042d0103985044c0d031000a1300d8100509030491508070410411004006100410742031502501d0702042e01003803400b150790a41c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 125953030 1250 125951780 125951801
    0x40f080405060d0609051003030206150a0b0a030e0f0f0a020f0111010507030c1103030603250b0301030b0a0b1e0111030906040b220b040302060d0b09070908010b010903050601140103 80
    0x940c000381000755003c5a60140003243d1803420b0a01041c6e8461541e00c50300750f410306c03024000da0003440004603840c01c0f100303402700b07200d030010004c0041c59102c4404200171f80046017540b01180c0d0b59201242c038150104810328005030864018480070400308515500c401007160000e00070002d0008824183e07000d001aa061220f07005c000700400d15100c00d006002e0908200040702003002505103a0803180c011089038800c1601030014a214801c0c0744a008030b40b2151401034245541c840c0300820380510410040d070003540a889400554140803400a045a5400c0e503560b100389100081c29030700380c100701c0176000066000d0030726260700c40051052500714825403107440d501c60400a408554a5007010203019941c507006045c6054403d0034060380c0d4182d07a01d00901c01c2c001401d010400041c5005070080c40380352182c401c08500c480e421404160200001c2e01e5190206106160a2021000901c903200600000b40380c54a01c041c907689a494448006000e00980d41c030aa840f0320342545d01a82110541a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 125954280 1250 125953030 125953039
    0x61409040e01050712060f0509040807020a080106180603050c0d0819110f030c0304030f050109020604030308060909070513020d0608060c13140604060309030c0212010207050118050303040f080405 86
    0x8441c152069000345030450b0000302180d00c41124003503a0040303114080a580c02c603c2403610880c180f508104c00241c00038405c41ea07480b410030480c3d0051300ca2440317503c020903003c0008141541003115200c00040c401045d052960300e080820400302e680002c3c043c603008020354050701000004d060415072403084405524120f0700b400405600e040e40000d50501004203042901c071b00900d84080a900c074413540c1e50921580e80140070a1010521110075480100c0c03150000107a031408030380c0400c030340f40c002da401900480c00010800400d81403000d0138542c040021809442210308080c00600380c0c14100710b044454603401300d020900e0810035032120014090600403608545082e455459030b03580400e5003407404410500c0c2c00103040d60030300c201020340da0f07006041504041c01d0007401c034001c11401405400300581c41c01c956001da21040610f0541000c60030000d0381e9a03000d41040350075207200c0d03286000d40c61200e00c41400411804002e49030800e034428205c0c00038242d50f0400d0318150040d0b4002a41c403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 125955530 1250 125954280 125954291
    0x1506080106170c0301020c060402090c0408060711010c0c0203030409020903162c16030c03150303020d020705013e060a0524030717010e07030501020c070f080706140904 74
    0x11800b5028494155074654040f1004483d00070103044c282d024000002c00c0c95070040700800e00510b81402000d0703006c000303400c29504045d507800f40245000020b440704008500b15040d9200c404400303000f038841d40d11040c200365102c1810b030781c04681c0d81d104070f110f488106540450a0082644c1c188002c0c2d552100003902900d149071580400084060034007800401810000300544d41d1040d01c464041c0714031a01c0c88412619250f002c003d42c09802c8040c00e180030903644621050144c00f04070f0072440958000d9004025007416203c021385404002c2c1c02541c1031100e440c3c150884004c2042409181101401846140d4000004600160440380c820a4a2801481c00304541c10100742c1c8031500c601c008000b400700d1078180146c0d86040110402882d60550841e580a1180f28444c40030f0008012448000082100740d0480607402c1c103156400480d42c0c0e0f500020810b01000f401c01554016180480303140140529040ea00c42c1d44084500c601e00904c0003003800b000d1071209d0301c010303548030550142c000d001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 125956780 1250 125955530 125955539
    0x607020607080909060a06090e0709030501050f0f0a020f190912060203090d050405091f050a030302030408010c090815090109020607051c050a050703081803040312031b08041506080106 81
    0x900c3d400001060340118003402c0000c2031450050350040445501e034864100181c03c0c56a00400080005c01d00400d0181c02d40c0c0000005400b4071500344100c40e12014060300e410154101c00c003240024200d021f00314014040040d01c8040e04086a00d070120031450390308015030b00700341620100754640c0443c2e5203c103203640c0c40742805220740007103100c0c0c5c011001307a03144405055800e803074502841c02195080985103001400764415060b1240440008005003d00150303500c00281e600344440d007040780181c0000c9030400440341c0034081c440040d8030701c2c10300792061428841d00c1e540d1120b0040345e0355210000c1c3c00201e100014298040da0740c0603000341010341d4622003070510550f10344030404c40340001c180d00100c1c015075070711842c20780d03909020f19a545482e00c0ba03035490840b0002005002c072103400900d2185200c0c911400c10041000350f128140004c584544401e000d0220b811501c0c0701105c020440e005103859581c0004020791090384825400614240d151941d00204400d0700498000d6280400104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 125958030 1250 125956780 125956793
    0x140603040510110406090803030712050a0b060309010b0f0d020d0f080c070311090a0606090909050f0a0c031a0609040611130b13210305091f080708060904051b0607020607 75
    0x801d17038540307131264401c855660b501c003036480c801201d8010000c2e00351501d1079101001a04800d410446510300465907800e40c60019041c0c0d4016180c1405581d0340703100c9500c0760300f002c03400361942c140c0494036a04c0f02d0415401180e0410500a402030003604444d44140402409100396040d00c2440e01c2207403c440e84900d840700100c125030024a2241e0100400220019400d00540e81503500e240c0e11003400078507040d030a81c080c1202d0700e421500c40c000c160303151510b0842040718800c1c00d4011000b01d10918910b06120900800007207545003160442c1d41046640d172260011260026482032002500c0c00c0c242d610718206003c3e601e21020b034481801c00c00107203544100090445404029007401c0300c40c0ea601c200390103c0d081c0950003d80c00001b410345c0f601190007807000c1c207002100038200b50004100d125980c01003a051000d80808100407809000b04694824859a8040c405071408036843c1001d880b20ba40e54404100c1c9085d04c007840284401458403503c0c251040d04e5400b40169031125944d14010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 125959280 1250 125958030 125958037
    0x906140603092e0e010b100f02030c01140a0b060307081501110a030206010303110115050415030209010f060206070f1209020604080708010b030f0a02010f03020f0910030504060b060414060304051011 87
    0x7508142444c200400514040c4607012940c1d40091201c0c02d0000c11402c103903603a15041c40c4046c00e6000c2803041c461a41d00030b00807400e003014100d200300c1706850003503c0302044500121a007402100309204000569030800440303038010038803a420003c00d05212004072010b04003400c018009010b60344683e401c254001130014140d9200f0b40f0303a9101034500000341070032544110307800b402c24403880c0010000c5040c59440031448203400080d011080c0d8507070300815015902a4002c50300d0005085017081401d90500601d508101c0b0303445c0c10401c03514040c0004041c40f101340003506031b040d035500d2a0340c1150368410451340101950020740e10312503900c2018138002c0102142d25406070058552543e15030002041602080e5416100e000b9113402d80d6400310b0003908041001d40302c6072000c0025840582d9000d0854140303902954020075a458189842c80c01c0d80c049140050107100305010500c0588007401e203040c07040e141a02d60036282e50f25410244c0c0381100c41540c1e9899589042c01d603403540d04140000703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 125960530 1250 125959280 125959363
    0x19030215090c01050d0f0f0507021c08040c03020613030210020c01171b030a0605060f03070e04050606041203030212010f0303110304030c09020313021f09090614060309 74
    0x1084099520741054985644640c03500c58002142044611a01c403099030041808040b0f01c0c1d0b0000d40f0640c4403101c1000c0b40d00607501c460259012020704620340c542c0c1d140300b01c071114043c6001e011500b0660b5840950510600009100d4200030503207518040d08050550021a0010900d5030748a402490107511483c0030240d140c0020004c40402c03003003250700c0101d140180100c0041040c40c40c03180815640e5074101401d03814000d82c580340d000401d07a44080240164168075000d072580c0781072005e0054118800c10b108103001d5408c140c100059940c030b1106807800c4405505c5003003204910351604500034070407242803240c031040100000c545038960880441c140c1e0b1180c1c44180610701000440781c2d5a02642c0303c020242c42d4045010300060200b90040c5401c61300c104c90310004c3ca4000d5002402c0d003d0346a5440842a04030b16522490903408004030000303107011003041029038213107582000b00d480c8540842d03010328000408205030b000c040145160800c0950b4001d907101d0552019600d22020200c01d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 125961780 1250 125960530 125960563
    0x1050109150b0304050d0c1e03050310060f0903122303060a2102010c14031804050a06120807230601030b0708130321020406030e01110a020a080c190302 67
    0x1002c10342c0031400781203d020741d0b0080000d2105211214084408008002041711542a130502c0c1401c0c12881c00741804580744a034441c507171240f80442c1445620300c41513226108010159501c503800640100142d000d50f500010301c40a410303031441084d03a00421124a6964004071035000400100030b00010714000e00080320740600056441c0740f085204800040b00d103441d41c079100c02c80d20040d13008140b00e007900c1e449000c10440703601d04a000a4159004064a1600111a0089400180307024845c0a41c00f208406080241d2403c0c44884940c80900d104000d16031800024088280003444405880e181d1240080324000014410102c1e11010284401c641980760103003c070b03c0c818058424a0700c240350b500380c0d001c1e08000b5900e044030300e8183c04100543d4421800c0c1649070400351800200040e00e820344021a8240301c00e900715013119407e5451034850a000d21403400c000b58042031100202d50403031a195200e80454800a00307041c00402c11281c41c00d01050080e0030180c01140c006003080201d0f030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 125963030 1250 125961780 125961821
    0xe0604080321061c030201110304050a030809030f18040e030a0903120507080306010e0d050313050a0f1401140405040c030914162310020a210804140a020301050109 72
    0x5030603914060b0159080c50344161001d0102c09000e110b1048401e00e10300034400440c91080b2506005035030781c8183c41c203a0f200c0e08600da40005142d003040e151030f00700e503070000210710700049001310b40c42c2401001c0c52042040182c640c03981140c1d95a0700700c0160107040000792980c803028284068202d05a500c400c40b0f0b0b0302411451036084500400035506800d0300460414070319039a0b2130044415401d4010310546c490301000851021030b0040000e00b088034065007440000505000810400340016071101d050345c0e29144080c02080406001c128500000382005030a428510b400c7c0485400341c2d40103ea0403d107420f002c408100d91542000084034080c005641d44c100c401035030103480d000840174cc0c3c0041e590040080180b80b5101e1002292103010b040300c0c0488600030300c001403402400141d0000141d1007403604800740501216451a42d0880d03044d181d107128980035000d00160001000030302200d800c55840e10170024103122555032154000c000300075a60b180c2458030024168054100304464120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 125964280 1250 125963030 125963077
    0x9021513060c080f03220501020405010e190e0603100f020d111206060a0c080301030b060909070e0f180d08150409020a050402030c130b071a0c0a08070e06040803 71
    0x452481c20303042e803c81045840e01c0940c0c00d605907a81d00103041c903070b08500304203603c4407150035400600c0d112a1041340056961480c3c1000100f000d0120b444040c8142551600407103001ca44100f0030003224060006402207640e1400080c1c245500c1d0700c07240440900b81018103084041d940d00402030509109400c0145030450b0041082078000c07610780b11204298400492290700d48407000e04092020b80c90507116502c45544d824210750401e81c030483d01103c8050a101c09482c009a502e640b2201d601c0040414a280c140c80091445019080841148804010850840313004445840d4440600210307201007600780c00081800707078100c40090540c4842c42d08a4254a80b500804641e16002808600c1c100d0070541008000c0d44050000030041c130080121060110350001e84800604043c00850380311666410001c08144203040f00400c0c2a000504001034003903540e0588128840a16060055a0b41c01c2405e80321003040000300780d0f109038045000602c1c048008010171610f008011504455800c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 125965530 1250 125964280 125964287
    0x170c06040f2001200106080304030b0108060c0702030307060b061207170f070215060402070b010803071401020316051305040e0a050f03040605090118180506040507082403010902151306 81
    0x1006a500c0c002454181c00c0c4d14401e40403001e00c1c0342c000e4032000024103290340302c80d0540b441d0710170750003120052001401004407940c140249603100480c440d58525150050740040d450784648540280b0340356035903131500001c0d00c072081070712045001c0001004050030000d101410340681140d0409007e4440c00c001448043d41d0080d0900940c0d0303a40044c8240d17188640f40c543d41000042078030b82c205a00f4803aa05c0460300405c2281d008040d050040d550f68011414400c020030000300b91366881c0d0380100184184102c000e03c10500b800c0342490300c10340740c903c0d41e00907599202c5907a210303561207030401044454200c40455152201ca22650403a1504020001d40d10b850380158456000410003c0c84084619401604a81a00703588909546160364846180403a00e100043c1c000c20425515020040c5900b09480740540240c1c0905010340545000380402c0f040718100a2488080f5000d001e120401392403d410129070381e81d0040c429848951194120b4680d90485100a0048400041c0000e40e1601 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 125966780 1250 125965530 125965583
    0xf07200f01080703110f040609051930060905031b01090b070c03050721031404020d0312021204050102030702070e090a03031d0f15060103020406080103170c06040f 72
    0x34103869012555945050540c024503c0241c80248500c0400c8940c07030684a940041c000741c000c9840b101a01400c3c04c044c0100c074110100b624010140c1c2c3c0c0d1003488129044030000203140c1c03070341004440d1011000700784850003074241d1004084600b0002d20604020300400580f2080280210408403020400029803d030317806600044c01e02c582c0500401c5100b4454540c605400e030190801929110260381d6030007403181b0041e03600702c418103041c101c528125454051944450550400514a810960000f03681001c5810b0001c0034490b504d0610b01124420b0740603520460101066203045191505285010b54000c40381301006019004012445c5140b2079102801030070500c008103006022560160300500d08501c42e070b40510030b04036074140102002c0020312001d520582c0a800e282622880895001e03502420392814503006006c284142503103c0c184c48d0442c0d0f048103008440700c1d0f151090f0308151040300b60780c50b00d900602d020032040c0b1110f02c449815062180700304805d2900d062062080030f40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 125968030 1250 125966780 125966809
    0x2030d030b0d0b130b04050a030f05070515100801090b060a05030619020f092101050114030a03050d0906061e0b0a0503130201110609100b0618150f0720 67
    0x46a00b003a28020541c4421959848a01c000b11280708034015290540392010403034045925a10007100c2c0c030101684540c1403c1c012100d414000e041900c1c90b0342d0b403603c1c2c40480f0003008194401d100000d002c0c640c0c200f00540100418002044040b0303407030030001090042150f140c1e00071501020300180341e0400140039440740b0b00b0070020744c0440e041108208040d620403138a141c0d96940a10000ca11540d40217010040b215503e1810080ba81c004d08606094a1050780301021b000b810031403550180e10003090605200398035242440d55070500c0e5201c0d5008140c144c9002d00800d241035804a03585107039445004240031200c3d42d03003410a94890524029114036181d61000603c2400800e480c9403003130850b40c02c2c051050502e440721000380d0071420b00e08401216001c41581c8000d80a030000c43d0644105140d155003559240d150941d0000050004013203102d010340640400388800b8031804011044d00c0303202a5001c411030380e030103031800d18811814070070000c01d4181e6040c007900510342c9496080b481121 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 125969280 1250 125968030 125968039
    0x905190303080c1210030b0703091e050709020a03060f09050705090d02040e01050c03060f030c0a06050a02031201090606110c1806040b0d06020a080906010605071b03050109050a02030d030b 83
    0x3400d540d01215040005082200250001c3c0310140f020f94183e040c0610030074114005030040c51650510003030b1550090800d8050500e0140c2000109040b1914180c40301140121001281c074245880f9181450961111b840244045510707450541c0c55000b0600b20368032900c07a0700314640c590300c1030011102c0540b040b00100d0400c02005450b800d00ca10780503082030000380001307081003401d10b0003420b507481107489501d070700030002c200006894104450411004250002d04403078194001217140c0300300380d00420007032040c04603c292034148200300300d856031985028081104d5a5803040751014025034082e0f1400300e0a480c030404080c9400081218031040020079a0800b0a0b85440241e0f09a10140c00c0caa0416200c9440c210f290701da61800e000e40c18420300300141e0b2841c1d40e9400615440c4003408407c46500440c00405c503003075120064030381c880d0300260000b82400ca0851800040ca85542c001080755007086490b406000000c918190200d000b234090710461580544102c007200c45070019160320 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 125970530 1250 125969280 125969329
    0x1080304050f011103030a06031401020403081c0204120b0405010c1d010e0406082415150c01090b0717010b0c0703150b090907060f0e10180509070207060905 69
    0x180c9010400d442c2412030604044094800c030001c6941503601c116254620b1036184c003030400401601c4c401c000703910084c45000310f080034115596012184981d808554013000c92140c9100b207126a03504840051580065090302e08285150822000303000301c0d03040d10030354038140308052528091040400ca00c40c1d031486684080492000658160700b000ba00b103034019941d00300208107403400b0000c0c5a6440b81900e4110141807001041407880c000c02068a25070300d2010b020031206448174200019181d49401d8110748406e80c4260304c070700404140f0005403403454207905121200d0382001803a00301e010900d2034002281c0c1c898448400c10700c9248070313902c4142d00c00340040002c00c1d0903000e0041b164403101404030350410040b000440002c02681c40d2007181c0c0042204010035500314169000b0324a40b4108005040c03201c3c2c0006005282082500c010310040075030103071000c0790703144184002e00f030020702c01c0c000c0e800c0042e80213650380c1c00b5004640100c1c4c03543d000880d2070303d0710b0b14403007010000b051680000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 125971780 1250 125970530 125970539
    0x42d0501051f051207030b0106050c212b09030314150a0603020a02070e01060e090901090305030f0408070605070302040801060b09090414100609021207030b0a05060a0c08030901050708090601080304 87
    0x13450100c111584817405400d0020001642540f0250b000306030703e58803107845070074aa5038182000c0da140302d080701c1300240089a07603017009040241c48004146034401e00d80c0285240c504020706a0550704800c030180b8011a120825070194003034600d551350348d1000c03001a07540b00d403c08450b4034400729281d0b21440164003000301601c280c000304600000d034419074140541e10703244086905004e03003000c0d01080001595240504080b455580e000c505600240301013600c544001c0c00901c0302800361220b42900c08001011b02c40c414084070450b642c084005c01c00e500d4038240040007134001c1d0054400079400c14a00040751b0f0300c0a020340b2051500140f80c20714a455565031048900b2281c04c50b05000d0042c0e2040503080311461140300003d0070461005665a90f80d00314415001c40001c1a00d0249854150603d1a90715640f1600041d10030030b440103503548550507419100f14071200c100800c114000010040b05a40c190801c80c042d0701ca80c6c40b0803c10345c80e4468040c0e00c9800034007940307d503039000740302c10407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 125973030 1250 125971780 125971789
    0x18060406020315120d110706082a030f0a06080309130b0a05030307030815040513030c170d09050705030a030206070c0201050706090305031b040b04050108042d0501051f05 75
    0x43d046844261245800d942e1040801d052142071031154410350045000c00c4100d68011202048503541d29018064650801c207025241c144083d02c0ca0022050380b503110b101910310b1912046120300d140501c152a861b0612582490101c1101c0c80c40100d4103054002440a20010070fa421044c0e0007842400003e10b0394841e40010700066440e1548150404c000180f251402e100402019000c0d607901d06080c80d007200d044990642d030891032401945407100300403001c00d50200d80c11802d40c7c986401d240159850504d940804103907240c0381e05004000403146000344980c1d000c9821b1900c0348003501c001c1c540e940304040d1076601c004400307809600705c140001d405921440044803aa0300c14100740341814040d480d103100f25035603c0c0040b4041240001030000c2d10307100d01207000710340b0101c503100c600d010f0815004482d1800b40e071107007d050020250103d4204642840c5403500741401c40b68220410b030615501c50f0107a54540d03c20b8a0742d500e06000b24041d00401502c40300b901900d2448410414948005d10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 125974280 1250 125973030 125973037
    0x6040e0405070f030302062505040e070e030106090b010e0306060108011a0c060c0403061407050d0b0d0516050a0905010e0c0d02070c170f0109050706031d100609051806040602 77
    0x2158030707014541000c59160722039400f85010f140030b43c1c02030900e8034000a089600b10a68100b0350034001036054807900440e840000c960a4520f10043e4403841c0c0c9603180c00340e03074008080c0d903502da065090410100b20304801d58800150000c00740c0e1200c82d490a40410325448010a8400302d0000b0315201c01440120080c001111440c0160800c44d4940b6101108080c1052020744540018080000c1d003042842007034001c004481b001000c002072641004600505039204a06074056655255007440e0050b075900301203820200c0c1c012054031140307118404029a0101c00340a031901c40e00182002181070080c0d482028161104000c1c0e2640a07141d144020b42c6c02c1d000445820300b11034003008107400240070624071000808602401860044000c5522420440e90003403410711680341c5402c660100d03900152140c2250000e060000319641d44030210440c40c12000e201c2640d074403a22200c0700d008481070380003000703d680d0300208109945910040305410b10284030000199400003000c54041360307655004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 125975530 1250 125974280 125974283
    0x40b03040221010f050a11031510020a020310020706050c04030302030a05030606070618020102010f020c030306040b0a080d080601020c01142a0a1113050103050d1826070603060506040e04 82
    0x2041c20400b41d02d0201401c1d21030310002420359907200e00074041c031004180185100410348034821070851a0046c3c0c6e8100e03040d0007007a02840750f840301014000c5e041c000d00c246188030703401800359802c400581100704044d40c8485000c40710603142c200002c0003a04501c00b90380c15030b80e250703000e0762800846c07401c112100d8001500b0b07141d001404102202c00151103116015968002c0c1119030003071708050001900711013262420840d040d0041060080f480c8000c4200c07548003d00319800150745a0802c0800d40d00162034000802e1442404008a082c1c5e401c01200b5201f4a826821112100b40c0100111480320181c00f0381546000240300d0031101c07101302403c0c5010801d04901e19040445541026031510385160030681d4a1035039440d4103046810103142643c203400354490180300350752444c3e40300c0b40d84030036402d50b080401c200a404d40800d204801441001003805004040c81c4038096894403a00394288190341d5507034822840700040c594000c1c0203400488800401c620704241c9007400c505a0003600910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 125976780 1250 125975530 125975569
    0x1a03010504120c1127100b0405150f0c0a110a0b041712130e06090c040510030902060403060b010e01210902010e09070302091e0307030201030b0619080912040b030402 73
    0x502144640361174610411240c01d13003061110b02014490501e6162601502d40030519400e0340c0c0074480910b00d1400c90307084600c21780c1c002c0d1040d47c01c0c407110a064020008400c0a07510300080800c90940c000502c5c0a00388c0c0100701d40c0c92002813030020050b030b205851040c4481ea40d030900c81041117041419155007100e15030030640d203004481442d02001548001e04080300d40359403100600860510703028556010b00103545190302810041c100191900540c4211442030b010405000c1c0303d6446070b0004003509078040c1180c0d85075916458a08080e0000b03542042c00201d616080c0c110039817003101001c49507040c10b0302e0245a4107403249480c014288801f816410300801540c00d146a0b220300c24658401c801076540141c803544920100044450408020405610b9500000000342c0d00403c490003240c2c0d0901300003c0010081c00400c042c1c0c003071200700c0c41920021b504945031050708030300224802e00000302600c00ea1928491a2900e40c0030b94058051509828000640142402d144d4043c01c10610103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 125978030 1250 125976780 125976803
    0xc0313080a02011416180302060f090319060f0b0102010209181506040906090605010c080307080709050904210207030f0f1403030c0901030605040605030c010c0c05131a03010504120c 80
    0x140d0a5111200f43c075508901900c02c080c017009140c0c083e505841a11210202c00c9a062450b000070700a4082d007290b020003041b0000ba02001580c04118940c003145c0e03075011005040545081c814000c20301c4e100801141410071003609131030340c4180b0072284240c0005040080101c451296407800720300041c07074804041d9081d01c603032640d40e503038034041c02c01000c075000b012814900703140610056401a40c0141d052100002001000581140030b4030b51101c55441c048500c0e641d08801200e58a204e917101e0741d04291241d0520007400700031100703d44084008404840310f5901c03800c080b41c1d100c900d444080c064040959101c000500ca00b1105400701d8052442034034a00300b00c0f0642c60444c0d00540e44031a86420005440d1100d5800d030140310010700341101d040040502c2c060210f40c42d848100340c0d0504109482c040380d070401c01710601500c00b43c14041c0090114403a010140740c02804054081c2c1c00c81c1d102070240b038071a45814000c1700d1055600030301c190f510154800c426a043c80b40c10f10221900c49142 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 125979280 1250 125978030 125978051
    0x308040b1914180303010b0d0b0105041d100e1605090f0a06020d080a0212010902030604060e0c0a030e0a03020d08070203070615290301120302070e15090c0313080a0201 74
    0x180640c90380c54900480503299414103c9043c200c021515440b1149a00309200407c030800000050b907200c0030300100b0229940c3c1040300101e41d00d02c5190001c0400300000c201004c0c06907044a01140710b410740340c9004c0c0740c5585401c5a171030070310822240c0b405500110600f541071117100e8405801615400790224800001d15400a822410079030445070047c0d0000315448481d5a02000c06a04140e09031811454070204a070714200310300c014010001c3e45034002021034040d403103c5d030100c4014121508004228205546181030075480200740c000028200841000641c10115041c0c0005078150014180c0c1c1d1f902e004103035044200244a10150b000902c840c2c00481ea45014158405c107044803084004e504010032803051060311482002011480c00140c186148146c040303034196210020340c0703e00c000d00c03444c0032840c1c801550001c04440b4200424440c20124980e00310202a000f101c1c1c0f0041d40e50340f10aa0602804115807070548403513048041000301e902a801841c0648180c8004176600584 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 125980530 1250 125979280 125979331
    0x30b0609090108011e02030601120506010c020d030f0f020c060304060b1804060207121704080309012403020f010f0e04050402120319021018150219030e070f030308040b 74
    0x264403e9005035103031103420f1240c45150200d0789803001e000c00c003142141413120000b00346490002410750f04030f60300c0001c02c0c03480c0e0242c030385004000d6000f082041c0e001d141c9e1400521407080c070401100455291200961651700100342b03103081c15405011942035645549680000d032100d50011600710070b603a03c0440064081658641c8198060320bc05682c500083c9003000702c9007047d640c403000b0001c1e4446450008404903041c40e40003500030060795181d441780c400351030040848031100c10022410010b415804c840000407602102d0084075880210351111006580413a10300e04080000b48464a9003480e6140039800160050b001a04014045442684861a682c0081110440020b91a555104644e410400380c407990000d400b041c082c80040c4005c421a0103d0007800a1481e008031080c540500d8095040e100c1c1944554111401142e6101014004005400d040c18660041078000301c0c45100a00050303040300e51580e501c40c9269180e4690400f01400030b0025818107140c0440036035035418 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 125981780 1250 125980530 125980549
    0xc0408030406020c0307090e0a061a03010c090f1221020c0612150f0d0f0f051e0d0e010f03150b0417060906070f0c0606050a09050109050a110901030b0609 68
    0x42c0d0b00104060003104081615240c3c280c0d01a24149003400307500101110b0100718030f040550704c003001260b0f941801601d59090f140b603010280d0190b203400002d428a9034004034500481d6003001086c0550394851680c0c6100e50b00404024000040074941207041c00344030b0403003040b14016031064604035050140050b0fa594058000c00e00d0394840d4a090001c804046125044014000c50305424070b8006600400d00209503c5030207003119a41c940c1040612505078a20440d41354454140c6006500000038160301c80242080e06c0c0e40380c4103e0391014012406104890340700d0030f050310380c0d50071551f110030203d0207000c02c042e44440c501c4d030b080400203000310b588010f000604110b0707000c00804401250b00300c3c50914010400c407206e038418024007040a810644e1080204498640560b4030f00640c2007a0004d00345c00c3d48210b4010b01c412400045018441d80041c0c182d17482c20005128540307035000f51500307440c50903502c0e0801340e4017017199480943c02640002c0303c00b07402520a071b0030301c16a24009002e81d00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 125983030 1250 125981780 125981789
    0xa09030f03050c010f050603010b10020709090317040501060303120b011e031b03050118021c09020d0506040b04020111012310050d14070503030a05071502040e160206011712030c04080304 82
    0xe40341c0d010321100c8d141c203001d07140040b24191008003c40c3c02002000399079001038490b042d074150b51110700c0d80034140309030454281003c035603040074401e003014a080341c02889036110a40009102c00c0760340f01c00410b103018411412105039030705902d02e400c42107100000c0300a414220103060741c801d0f50880c031000c04000c046803858030351000203456240c545d01180507826a000206003e104001241902a90211b40c80d2450300d20700000034a40e0303140c0f011500e58008000050000c2c841c1c40c04001c108105001045e02c51031003a603980d04614100e8150706c0c03d80f5503011500031801d90140880e06d240304002d2215a0000c04008180503590b0340e480412810343c1c0c5528160342c2d030321035401111048401004031200401d0150021850040c41000040450207400c0c4000c28002500c503940140c44000d4040c0c802401c9803894000d03090510404102e250680c4106510142c005c3d10300020b080c1c1000348450903911070381e401800c0d1040e0022400c0000340e100501c043c4914405001c0861120410400f61000c0c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 125984280 1250 125983030 125983061
    0x1603180f0b060109030804120503040f0902030a0b0a08030d05090c0d140d050f0703030905030d1107110f0d0602090d0c151202090d06050403090b0d09020111030a09030f03050c01 78
    0x8202a041056440100610b203c0c10b002920004000241600048900319001180c0b0719081030740b01c0c507245081d48030340e6014000c3d11400707010101300390b11564010350245012400800c440d4828105102e5510f03024801c114464100340440280c5464682010364040780040c1966442880c000c005044085484d8050b108110b40341c0c07d00030501020064003c9051203400c01074103098141c407025505120b48400181010745031207042c400c00c1804c20030382c1c6040c0d101e030340c0034800060f4101c01110280c04c41042034039001d900d00b94502103400c00154802903400c000d4800304014415884000280d0300c40c0f0b00507074020801d18190004a12000507010140c602c0e4181400030140341500200f100240039003100d451031040113284450340e54030708284420307640302402003020340d11801e0030b4a1400403503000c540c0c87c020001d02e09250090ba5485007a030580b00b621901e03040315110a400707507a4003035040341c6400704420807414008200c0401c7d000383c490788640f074030b2441c000032088110300b551403040795030a41 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 125985530 1250 125984280 125984303
    0x3020f150c030711030c0a121410091506030506060402070f05060702010e07080706082404050109020a020106060c0b04020d020607081201030c080f0706030c02010207060e0a020f0109030506160318 86
    0x10000f5030008511444d9084000b04083c01c0c140c00000d40040851213800e00003411610b075079041200715444007012801d94800e86001112004446000e0f0440d0b00c0c04071000e240898110484e5000307071080c40180c0c3d40003070050100750b4407801400000d5203c01400c0d5030b00010f007481ca8000070010000507100c0d2400d0b900110b01d82032a4101030707203007030f0a5400034041303a00034040601085600101040d80102d20b40e05405444441c01c03003880c0d0400550164a811504000000c164410701c0d400900f82030340194000c00596949160480d540444c403100280351b0901ca81c04a809441d00c14440c503070302c500040c400c1c3e01c1e00905e5500c070403055200e00013604e220000c0800400900400302400341c01002950b02400501880003e500e4590f105801180b040c5540d4903500842c9603c00d40c16581d119030300400421280c0c404c0341d0019030f510b0380b00d0012441501074440140081d44038000e244102c0340d019004100a48910002c0094401d07103d03030383c0c0205a0344010003401045140e20380c45242d0f00030000c0400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 125986780 1250 125985530 125985533
    0x10f02040f0e0903070807060b1c0c0602030405030606060711031009060501050a0303051605011805060a0c0f1202030702191a070206070507170904020f0d0501150903020f150c0307 79
    0x42032011640031822140c868400c221070b18402000b00e6900f1079001400310713641d41180ca008c078000c0c000c0d11031742c83e0010700c0040600007041e918481b01c55010b005480c00407031950b5a2034120303a28405c901030113415800a1010640e14145075010340b4125105602c59641008410701182c0b80c6501c85030280c07061134944034082c080c0801032144601512068400442490460310007030060701c01c05042004003209246c510381440429072143d49403100841003c0c0e90400d0724200990f48400039581d0b41c458070700e4100e55202860044000304e0345510a51561004010351225500081d00000d0000d4294021401c0c0c0f10000d841103540580300502c51703441542e07200103807460000c0012009042c1010355020318140000d9a070004d05442000b640b02c180c140c290488850030030454000d802d90241c1190011a450101c00c5d04c00c006000b1a01d07002100308116a0b031601c5a10b4240741c062924004503111031018405030509050707803900c2c00c1000d0310070244608400300b007451581c0010403881d07554002194480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 125988030 1250 125986780 125986799
    0x10050105071a0c13090209010804021c080c0a060f0509060601050705120a050c010e0106050105030a0c111c1d090a110c1209010e0603061020150402120604120302090f03010f0204 78
    0x5c0e103042e5a007142020a00d100180443c50080e00191058080c0782384003802d04144004be080c080e6001e248140c448078a42000782c0c0c0c9803a01c0c3c2c02218a14103040d14040c3c6a812403040728491540d40d03000300100d489a500559088d030024105440a019203541002c100c3e01580c000c014100750369450942d105416184603084440400442003581d040c1718007040147c0c1c0c0071064030341010014500084a12600205648000f44818510600c0c05606c0c1c1c0b03200c2d4441c1c1400c503a59421241d032201d078a22401c0003802c403001a40e2149040d0310801150201d450002141d10030070f4140c0c49071500383c0c5031405044240d0b140c10602881c50150300300011700350b880d6507032010300240c4890040c0e400c20b0541c01c000c0000f410400c551450343c0204609950f80200380c81e032401100c42c00c00c1000081d940c00d60220041480e042200b00c0781a402450009d01d00d00c110340d00016840c0c881c079040660a04c0a0740d0018044001e0f45c0075007441e690110118118011580d42031084201002d00614016941c914145050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 125989280 1250 125988030 125988067
    0x30216090e07050415031a060f030d120c0e120105041e03020c0909010605061846080304090e160608012c070809010e030310050105071a0c 61
    0x52480d080000506056000182c92002d444046a000c1115031210410724020801a4000b402d85941061038044286522241c2c81c0540410340700c00d1200300c403d00926648010203c4800700056924108000c40983c0b58044554041e4904c1c200d4803810041d8001082103003190464502a55900180000c04c101e00c0c201e10030f0002400701070039400107651000703500e6100603000b06004004460004244a001394071010207040c0081056440d0361510316a004d0010003c82854050012007001f8a19404044403000c0761440003403401c0500d8250b5071500d0340556614421340d00541c0601c40c0403c40e1b0001b0710192020b80121040080e03000c1480c0083c0d072504031006512900c0c09030100050060503030042c01705041d24203070010405020070181c0d0b40406502c0fa01c5806006c04202c078280107101d64031020280c01a581c2100900c1080d03143c8881035141d10060313440400744d5800369400c00055014801900342107004072207940d41c0c1c16510b0b0307403071035140c40c02c41d4103082c40b08001410380400a55140007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 125990530 1250 125989280 125989289
    0x604140301050f060a0e0a0b0405040c0303020d141603120e0a0201080609161110020a0305041b05130b0303070807030c1202010c090603050612070306020306040f0e071719030216 78
    0xc1c0000ca01380240400c0e02c00d1518002c0300c03a05881540051400181600050030520000d00204420b00e4070342850410b511841c0001c80060042c48000016540301d40818010300d100d4802031031402c0405110314001007494003086050100000c40e090781d07059144109418500c1a9001c0c02000d030061000500d4044000c1485100b00a620203100e0044286030842c00c2e01c80460820915291060031101c2c603000c082900300e06c600d07000207240b080c0c2c0e03070341a00b0843c0103501c06c00c00d40c40105024113500641e20214010140c1009012418003450740c5160000d0048181c06001d403841e00445482e6590340382d010b5041980403411003001c41041000a17220600b00c1d0949200030001d41c050080024801201ca1003010200341d1510003041c03241e40c40309280c0311020342c0703002140d04041d520f1503e44003070740013141e0303180c4294941a4521030f56840e45c041d002414404401811105042a030402500010403154818910030003100003c014081600b41c610f903030290300101900090f5200c03000c4003d255401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 125991780 1250 125990530 125990551
    0x3010606050f19020f0609030d0605010305041104020906070204140f01050d0507090c0e040f0e0610031515031514180c010c06020d0c030f0b060901020a081305060414030105 76
    0x15141001c8640b0300392629041400d0a9009404480340100c0c504000352008907402c3c0070300307418003003000c0c2c001004001c04840d80f14180a280d81c1d560042d8104c0f501102c014000c002e00c0c0f0740c0707521a481c055004140b4507000610160401d030407500418110340c2c0030f0309080003810b000e00510500c14203150b0018010b2800700c490888480ca1072f90740c00e0f1203517214460710118603110341d000b0310140d000b84103100c0f1140b80580100100807204510102401e500007134644c260046002084000058401980c2581d400c2010b02c12110f440455201c02490000340c851050428510301200194042e0402c0824035503106011803450b0f80c106404400c61000ba14203c5403059240c04000769070f102040d1342c0c11109090130f0552004d107487c14400007a00c03032460741d15035241c5000307044641d2581580c00304407401d403145410001419010240700381442050015070241e030000700108001101c0070010306041c0841c9410b00d0b9150355840c089050794100b50016041810f041700b071806070382024403910380e00407207031304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 125993030 1250 125991780 125991787
    0x7061509060f1809031704080f0c0a0204051f26010207030203040311241b070609080c0604030809060c12030a14090c1c110a170f0d02061311040c050301050301060605 73
    0x1d4000d8002c0301800340c010580e006d42000a42881314000c256525480c0b00742c030899607448400f904540b01c0a042c90201d101d030b0710303002c049001000a100034891916090381c14805036414102005840d0480d0070310034405488802584820500038000f5100142c404d0300119261404e6152000a580c49034901d60300032503019113140c01d04200240300340c5000600c58020790340d40000a1080360b8400504411429900c075059002070303081c0c1c0c01890402125a0380c01551060039240c8100202c920803440090190b1405014056041c685000201010781c01c2c8000c40b02d050700c030b0100482240c2c0023140e00d050110360358000802041c900100940d440120500501446c084040008130800c1c000220000501da06088007c00c00031b01c42074200c0c95a1009044505441e40e50140026403c65804240e10314010b941314101c005030000b4010303640b440580c000d494542d444d40c04018958540f00b8042c0c40b40b100c242a840d505450724816100101420760701d00760380c1e40c10202494203581d8150700c51800c010080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 125994280 1250 125993030 125993033
    0x90804081e010b1e0303070c08061009140402040c17040b06010e0d0309061809050108030c01140709030308070521010303090f03020105030c0c0102070804060c0302011d0307061509060f1809 83
    0x25040c13046020400d01c003440d4031074250700802e1450084040007002c102c1d4480000c2040f1000044491041e0f00e000600d080c1c143e03d40d2418029200b041101201083c080004580103241c5600444081c4045103041c0e40f44100700214502700c507106840a4030310b50b04039418040c0c20b59201c40c004080e8041a107031094418010b5030001c11050703007441400d0400c80340d10b0311030803c1c44600c540d4100501000a060107a940c6403694a5120f41c0032000c0c1081d00e40c82c041201001140a4292a02c68960341c1c4035141614950745080e1110b400041c00e001c2002810000e841c629210080d946058200302c007081100766046260141c81c5103001e4212080d803243c00c900410040c1e030302800301c984c008a08081140c40348080070310315002e8042c4810062418001040104401358407007030b21591240250700a02501c1094a41e44190a4400c81400d40d075420410880000c1501ca8029141c040760324030381c0b485400e43c1e929620084a00a40144840d1440c2180801c02516001000410012551403c1140c2c0205 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 125995530 1250 125994280 125994289
    0xf071b03080d0b061c06050f0405010f060807021006140f0108090d05090f030a050d18030b0103080a270608180303061e03030708071a1612090804081e010b 68
    0x2d00d951403030015119807096040740c49a205803044060010300071041c40081c940c508025140724060140076040c1301c0d55030021071a2a005130390480711a6130303113208814203043d011206148018080419803203141000c008180032441403400406105108500c4114000704009002415010060400040701d00380b000b01c8502085500040d181030808135aa05139440100b03400d55022070000b90706d8081d030b05d130f15400c0c072102041d25444019642d0f11702c810982100f9042c1c0f29071006010240131070002400620008480d80000d0107004454184104d080e0202c2290312101c6030307291009088213203020410800641c00c041600c1c1c110300410034003256810700c41c40c000d50b20300004000e03d200d08034000d2504010640018040c2c081003000e41070700d40d90b0b0340c2814000103d0740708c0300d0100c440301d54130140103182075881c00c1202d008401512844c0040001c0000c00c0f1214041c400809030700c1d03959100800c000524a000806c01081c2e080041c0c0b806100140b00c440d052606030b0030f2400340d43d050000a2100c5d40c0e5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 125996780 1250 125995530 125995537
    0x2010e030d050a0c02030a020d031e0306060203090f0d020907031b091505031e01080303100501020f0d1808010501080105042603010e04060605060a020f06010f120f0212030f071b0308 80
    0x741898076802601417400040e1821560240203504071194013210001e241d0f108407058000a111b182d0303441980d9980c50120226043c1c0e2040c9401a081440382000500e4103814543c140c940051540c19811041d40004114010070741c4c50901203695031a0601c0112640101e503d5108030354104641071900e003040c4c1d18403000741c0b1500f0b54104180040000d696540400b01000d001000d184100f45c50368503205c131280d495000740d50f40380034640b6841002400c0c8d0300c0040c650103001c00391000380c0740c1940410700560346084035886001662000c14404200a0401d1180d50b00a04044d0300100782d80c20141003075054035640214006a43c1d8200c440180244c0e00d1004890441c5c5c62000d03075003030660755814124010702664200b25448a070000d000b00f6420f80c001110388983d08100195100f69036510302c11881e00d0500e1141000780b54600c140a0046480c015200480c58000b816035801e021610041605543c0701c2d0140ca450200b000c0380c130109000c1c0401301a011800ca102010801074215224942d0074003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 125998030 1250 125996780 125996797
    0x50406112802030705031912022712100f06140604031502190807030f0c02070501180f06050d0b030a020d06020a1e09080f0c01170705040513060302010e030d05 70
    0xc140c0704650700c0d07241c82003044844154001c0c2c1602c0d00c5440203042540802c22002d0303a980050121080c07019208130078402c4901d0071f0845e6442c09940061001c903207400802d10201258401c412103088511844144000e040310425030400180126640320b42200b2250540c025035400d1440d007558110640f01e6904642c05d172030700301e03180420066003944040082c0c40b4510007841c007040c04005007103640b0381046030f00f80a402079460901290921114200c200d8101a4030240140d0200c1c2e402c01981d4054545801ca0019007602003e0071074840101e1141003207076900c040002b4000042c108001c181d10701c02c1c0d460040040b00500364500f01900015400d0580600150030710b44c1c0000c81c070005a002d02c46402c90400a4989204515034130b6002804142d2903101c2c0403054022031449100c0982e0100380c105860340144c55020481140c4211410682c1c0f00030010003d0110400000c01d00795142914012082c1c071914010078000e0070762000520b85021100440e000e84e118124001e00700b41c101e0151020304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 125999280 1250 125998030 125998087
    0xf09050a15051c06060303030911040504021e1306080619050106080105060c1006080d0327030818030f0403060608030a0e1c0b1006260109051003050f0105040611 71
    0x7103c94442940104400202c001e041c540741c4100041055003642007003141d24013406d001c521a140d00c030103100c01c4e01c00407540203501405462000d80302040820b441c00802c04060680150041d111120004441107600845c0032a44410204107030084028514040c1c004580824015549040e4010704000d1046c05030a01c1800f01103024400403000700200781132480c21200a1010030764640f40f058558040050400029042101c1176603410b517801c0d0036140d001c0c90040b52001c8021161800c4580c0c10014061007041141d111020b1401a0100701078421070402030181990b452071072410904840c0603500c50815070b0010702505002030341140608032007010544545000048090822a6000145400500c10780b804c0303081c08103250b903020030f40c800c1c0da0703841d03c0700320340c403482e824080e036103140c401842920104004005200104c265084603400c91488003401c20341c5920b82d0780307060801050b07030305180d0b5680d943da0800c0b0600000c2e001c0d29026414a181003031401c0701f1443c912083d60045035061910 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 126000530 1250 125999280 125999299
    0x30d0e0405150d0f020103110a05030402100903050601080322080a060f180804081b1e012a0506010603110405091905010803040f05011706040504020a0f0f09050a1505 73
    0x440c22044080c00500000c00c50764600c9100e00e002e01902081c01405ea0009141c080041c80b1032985d24200d4180e04801c0e103039981582d845908024030300400c01e1542040007420380b4000b000540030800c560180013541701a580303c000c070700031070111682c2d01000788070150302c500c1c01080f0f00240410241c18003500000c001c40c0240480e40100302921001810180307066801800005020f0b4060181050341c04c00d0040d12103100441c140441c10380c0c01a0721460380600084008001e4540303180400140b0170042c1011107071403444000c000135001c42c0544070190141e100c045202000800d0241d50301600950400700192107203103042501a004502032640100c003040d01089a00030f4601c0140310050604d80180810342e1613500c0980c83e604603100715041085810000b042c1503000b0315102c141160680180c00c9990b841c441004060140503109903000810101e010036600c41c4010302c8000380140703680d0211011f103020120310032110000c01c00006a4984a080c41e40100108070340e90071500f0851780e0304030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 126001780 1250 126000530 126000541
    0x20304020907081008031903060506070503030f091005011409071701120303060b0c0c012316060e060a0b030d1b03081b0406020109060b06030f0c030a09050601030501050402030c030d0e0405 83
    0x131071840c00e8003d981c075844080b03500950010740468503a040c403510b9505200095a4405100840c080c608000740759030130138400228001c403c4441682c2c4100d8000031204141603520701c41080321020b030032003417414a550004980c1410302e4504aa0807905502e0001e80c10186550415502441070051480c8824002c03291000c2c54420f4220324007411000d0301071030352070400e17201c0b280d0764a42c01004140400d41d4924803092440c4201d0b190040d07034000000d00c510f44410b070141601c80905a400495440b40e41d80009586003200b004120310503e00c1440016405601404151a0801e0201c41808205441e45c5000c010158481a0580c131545420000501d840e13207034003000500c030000d0f440e14000e800400d0005e025a41500a515024068901000204121020f02049110485840c95456503010209404584032001103074040307000e40c0001450000c43d9200b5003020400e82c401d4480d03039150b506100030352806000200d6070640c110000c1098244103030b0098056001190300b140b2595a0300c00290 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 126003030 1250 126001780 126001801
    0x60509030f010e0343021215190b030a0b04170304060903090e0c19021204030c0305060112031205070903060f020a0e010306050a1a091005030f090102030402090708 72
    0x1000c0e04100e0000340000e054181c9001c0e035070780041903140903504105d035071512402c0d034240300d10028070030f284481070780c040180d155400f04808000e4102c0c4c04c03441d2074212403045501407010b40d00600d05021106d10b14180745018950b6490404490750b40d0500d0209034805590740054014843ca920075584401d6a036a400c04900102e4007031904843d00400008001c1041041d50048440178806d407070b80d0340c0c1c15442d08001c80350700c00111040d00c92410100821102c002d800914038036000600d104607680c2d009240005c810b50f030485d50080354005507580302401081828000740740540001d040214070a50542ca00400340320801040d10b400d16a40c902054259219208000203550440d00912115503c0301c070320002503001300b9024000078900070024100b51710a006a004943d8010000030f540d40c241404a50340642ca4088051034280410800d0300d6078803804a80ca0b2800e01c0c1c2d44071a9100d00d0144002d8450820090105486900c10010040180d4130400d96903000501340c9040c9a00d44d54120078070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 126004280 1250 126003030 126003043
    0xc02040209040c050d0e06070906030e010b030f030d0f02160b04050c15090306100302091b0706110403030f03060b03010e060402070f0506071b1a090703061103010f050906030706050903 81
    0x202e8009042064010a20780c2040040200200c1941d0802040035803050944c3c448105444420000300400020001c2e40d100e43c1143c680f25181d04000110100c040000900c1c0c801c02950382806a0001700b00c1d4101800c40e441122441c1e00070300c000b51300d00184204000b14610030080c00805c5d48260401080a011040022140f510307005008843e096100d040141d91641240098611902c165800102130208154403841103980c0500100c00907120445045c0509610340c1d4640390004083c02410089a13250007580110490752150b29680ca0030f40c10001c2588041860352818141400000c010029601c001c03079044401d02da0b0a0011500c0d9040010043e00c150f46c07000d0900100340801c0d00a1000200d0098040c4420b5110604031900303054a00105010b40c0c18050150b07200a902400c61305641c24495034028018420395120036225901c0000312100100a03e000c03000200045c00303806903180e9101c014140840390f40031a403420400080e5100400d010702020007a003c10708010381d84042088 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 126005530 1250 126004280 126004297
    0x4020d0503120703050a061d04060e0c030a08070b100320010509060c0f0f0d1d010512010303030501090c0c0803060d030e1806031002091528021b010206060a03030c020402 75
    0x40b4003183c1420280100035080c1503800c14030981c9000c1c0000360403404440d4810052402001c540035030390382d644401d0000d05140110304002d01548201c0c40c1da50b5000c2c03110410061003003101d03503104c031441d081c07840418800030403180046801100500c0440e50715440d05074400c0c030160140c9054508200120f84502442c2046904400e01007075000544034049143c010500d909011500312130204940160354840c1c9542c5c4002180070301e010b0032003c02150045503000c21041c10914580b00d0301082550308418240c2c0142c001958543c0184128015806030f0410340b03040d440e00c541503600c06c0d01c2d100d540d4400500018130070801c0728401010140500d81c0c000000c580100720b008050350307281140d0320b640011190244039000cec100c002195409144281c44014401030641e11119103052200e140740c0e40980e042d45100700324140022002c0b4403070340060400d1505070f070242500150701d0b081091062042e05207541950020b000300300300b5460340d400d550112505860b14481031100c0d80041402032149044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 126006780 1250 126005530 126005557
    0x102100f0609060801090209070e0609060702061902102a05180411070204060b07051c0329190b09010309060609050f0709090603020612090f0703051e0606030604020d0503 75
    0x40040d02107011b5100454090003036422041e242c2d22808102c07402007440a0304c50340040140451119804c0c0070b00075120f03603031000c2d013075501d000b81811701c40000d10700e500700480c0107a10501034505c49641501a400b020b00b003c026101c0941c1c0d4200001080c1c14640b92020100000400c9441260b0b051060101000034040c100b00204081c4c003503d4009039005030803d030302907418807100042e4210307821308540c09544c11a000e05411b06001c519407110120701d08962040580712048501100020042d4000f059000604171003e14501e078144003031030100300559041200500010000003800c5402c6075400ea40900c1c00154001a42c54094018991a04132158062810302084510810320148501404170b9071261904259981d20031000d964132400000c2d0000810f000c40912140483c1205c0d81290400d07040c3d40080319000c84091a1030802e500c251880e03030000f001d030805e0306440b0301c0c5080305003601c102501c85844c00300c000c60381d1101c002e4030090080c0e0100c050101030007402d000761341d1407615081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 126008030 1250 126006780 126006791
    0x3030504022101060602010b01050309070302060a21020703030f05040f060b0a0305010207110f150f1818070f0504121e0b010f08100603031d060c03120f0f060102100f0609 75
    0x1804500811030385c0201d030302643c60b002c10140f0542c0140d041d01c0c0b060800e0b800601100342168240b180c190401c8800b001449000c01034070000000d0642070000103410b00740c0050b2030704a28200101a80d01140e1003005007407400003800081801c1d100108002600130700003050b0a44000c02003000c2e10426400504154408a1703101d003044000c400ca684e00ca90112202c074512601b1108108019482884404c4a03160400c1240c01030b91801c0087c4c42c240c041002e040e010740d400a0f004c41d040c0001c4c9495140c00d603482d40c003000328094000400c0302d80c10001d413030b0507802e00b800c00303042d080c403e000c204001d00310641c07a41c2000300c200c030340b00101c8085a6010303400c2c00301540c2da160800c501403460f008240c80c0780a403045110142c1d00d0f501c918400c0301e815030350713048045005418006950025450751034101e1401c00c1000b00c10b4030104010550840000c68606c114079001d2426020081c014080c44080c540b50b4041c00541e1f030340011400e071100208000040d1107065800194018881d41e0701a801d10703420325 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 126009280 1250 126008030 126008089
    0x30903100b04050c1215030102040b0a080405100501150804050a0602130e06041505011d0a0803070b0f0108030714010e15010501030c1e030209060d0f020c280303050402 74
    0x2a00310120041c01074a05008a4a6900003030216020b20b4441100c803880d03003400078001e2814194042c0c0c1031000900018070340764a440900c05554800a041e40209000c0400e0108001d006c0002201003e021101001194140300800e007024a014400900b08610b480c0442c040c05414410a5545588040115501c0b00c0c41112410106803d110b08000710301c0041c001030f01070505005011403104049102c6a00e142414015205600726070107046c0d4040f24043d154010752200d038800400b61038038070001c0da01d45e040c1d80781043c9406401483e030003018035040c1c01001585400002c0d07400042e4040790042082141e02c15890040c080d030841d4001901c1103c0310140309445040f040d034181c1e1404c3e60103121405100700103a4501d484a0a440c80303100e08681d50010a500c02e83c0a031607150002080146083c5440a02009840210000204040d4001003040c00c8210030485000700303580001c90285045405100c5110703101c601100a000e0503207450005046645114100c90401000002002c1c032080b0b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 126010530 1250 126009280 126009313
    0x7170d0c020d0c152d0b180403090501030504030c05070e1b12010504020702010c060c050306100309020d0311010e100b030706080f06041109100f090f03020f0d0303020f0313030e090106120509030903 87
    0x4002c0c6d010f001d000d1911040942c8108581d02612032030301a16106403031454100110001c0800500941c10031440d144000e00040b070900c0420010300fa01d111b01400b0342085820a440110143d2040050060401c0b05a00001080a40a0440798102c2d00140c403840240010b0b106881140c1d401004140350025145e4403d4000d40510f0188200b6a10802e400301da100041d02100c848900183d40491900c6580300003a114803c0ba89082403628008035118a540c014603140c943c0e903140d20350381e031504c43c8a2098982020842000108214034042c911f40c103100d050303480f20709070281441d8004e5488901041c00165071384110b98100b10040c00300608510081c03c01495100c1803036582700010400c4c0c0c4e0002c1c1030745002c0203c0080e650001c110a07100d10001c0700b049580c10100314114145a0203010110301c40c803e4601442c03041e0921910680360711828076009110a0710b80c0c042d01e2051000a0051005551040400005d40100e43e0006003948808649601d9402000109075142c411a03400c0301079200d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 126011780 1250 126010530 126010541
    0x901270302010b0901050f040504080c0f0705120d09090b01030b0d03020d0905041a040207060609061203090603051b1b0105070903060b0306010305060c07170d0c020d0c152d 76
    0xe036000b045203510301c00130007120340d4082c0b00742d40d80000d80d000d000280c0d15082d401181c0041c42030051510b0401c4861200f0b04241c94504400e01e00e400140d8200700909160a000f401a0b2051003c0c08884616180c09020000309000b40a00381da0348030704106469019500518008400a00001c171203641c625000b03603614002458500042c4400c40c00043c0707400e281c05410010900d801c3d030b2008810854003407000070340103402c01fa1202e944071880082d40138014070600b0701409540502c03c041c8070650401800e10a01548614105450101004030498143c0194041c54070103a001329034508070b55400c1d01200c20740070700004041d440c2406004a031078100ca041310032a880741c3c0092001740303c0744040540b546024400901160030140008030080340700304c020b046039445909503440d0301c2c1c442e25100e40b040d00320f030003003048540d1f807040070b44c0c0415010002c075900c0f40c0b070602d081c80b20800700e0f650344150160394610900080c0c1d140d400b0002005a0441d04034031b80254521490309400700144210091314 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 126013030 1250 126011780 126011783
    0x31e1504050c1e120a030f030f0204030b0109060e10060e0f0409141b060c0703060e1504060903081311060a02100207050d030b0913080703030b031c0e2205090127 71
    0x4c01d41d00701c0341d001d0140402d1411045801d41ca032408070700c1c8182d409601400e003c0a442d920f0340c3e030800c404000114503118890280c0b00381c40c000200c80707003045945020b24802900c80d030340481d0b0300c00c0200000c1c1d84c40100d4000c40c003c242c40b1070544040800100d0b0251520ba0320041c0414240d12141080c00c100068030101c842518800c0d241c11003000e001d001c0030340309550014006401885082c1f012908907048000c098840ca011501d141e006d001030030980a42c1a03a04032102500ca00f0100c00381075000e011941c006520b4089107031000042c1e620910030150901c1c3c0540122404510400440e0080c480315035100303440313503007555242400c0c60141d40782c4600036483c1c00070a107400d245071424104002d100340300368880008207107606619155201c45403c40881102010346075070b00b4041c16101842003101418240b03141d604035180c1100b024022203000000e13640500c0b924040c141c451000407161400750142c081001a9a8031140c400502600d00c103445600000c442d980803a112180d51480c1c6204203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 126014280 1250 126013030 126013039
    0x120403080a15090b01020f0d03091109070e01180503010c111b0109090b1504031104050114030a2009040803040605090102030c12130b010801060302031e1504050c1e 72
    0xc0d910000310310704840c2c0b520042c42c501035a110b000e010040450b485560f4240050049415820640400c145000c5110929400080d222080801085005080c01c0302c80d100031140a902d501c2c040c0d4000302000c4990071402d0420440815001c00344d0b03103480c110009080081c000344030070b5030216401360100c03001c40a215214450484d0034500070171061840d0904010507580c224043c1d1034100010040d0400d000580e1b807200c0c2d040d200c0352060312518020001544502c500400d1200700104000454005034000351510442003c0c11403543d401182103802303950f00505000c012003601e8400b4040100c0801c0311504003030124240803e1105003070142d44228030420046c40140c0c1d0b1541164281d00060f0f600d071406010920244002c60952955150b1007010280040061412610383d80c89950003a07100031b0150f51f5840e001d000b5030500b4000c14905072440d07205e5010320b41200680554509000d10044140c10048000ca01003001c14803e04050351700c000c0c00d80380c0340a00018880a58880140450302c41d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 126015530 1250 126014280 126014297
    0x140a020f0f0105130f030201061e060f0914012d050304020307120f2d030906030e0102040b030408090616050114010602060906040602030c041805010302090f040c05150f120403 77
    0x303242050003100e01c1341a040109032192841540d0307200044010300d2085003507549882021134060140c410104021108040c00c016807490104003a2850004411410400030000fa09100f000786505001c21460001c0c604410042544c000d0360450500100c05140005184140c100c02551f1250295000e603008070162444940c1e41c01f1605549184036034001c0820301c4641c081c6000c03400c11100c014100401e0041241220f0302014461319400300440b0841c00b151602005200c80c951511502d100e00b0003500085240a0400075003001501004100a22007c40000c0c030000036201c90007501e1000c80041d15007240015640307440c2d40038048180c040402c0c000120f0002401d24030003d082805201d116000e403186840380d441e0320001e50300040141451980820000441130301a07442031142000b05031000625504620420698640c0541240c40c608480800d12000c5101c0c1d0f2081b10480d4000c54a07080c040e031030b0350742d00603240c01078403415074001c0c0022400101039090120454804c500c40c1d6100d051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 126016780 1250 126015530 126015553
    0x2a0a08060604111e03250206010e070905030a061107020310090219060804020d2a0e011202010f03050411060304080903010b010203030c1605071205030d0f0b060f070201140a020f 78
    0x22a400fa000d440800500615413000b021455003006640000c401c2d4500d018030620b410742c40030407500140f0400c0040e40003500401c491541801b0701c2ea0862603074500005440c0c40c00300040e82e5100001005081d20b076880f03a9103c10501100c0440d003c01e903000e410703a88108083ca103824001c0c51103074001c2e802020708a4038034440c00311482e202c0d0b0648039240c403444c0e0582c4540e002e0103400c0d02c404500710b40e40484101540141c4040c2d82845140e800004a0002c0e410701700b6402400e42032040e84560440841441c00c100185c1c3c00c241d240c03070041018500065035607030b14140b02103403e021a8009402200000610051000078401403841c400c0680080c41448480d5004a90302d2102300c0d102e14001100b840280c0c8031030b03000d4007491100c1780220100c0c1c0d80c158941460f500c0860a011088980d0b520024030308850b5080d6000d0862003c0d00d407034003002828452000b00d0024400d039004c4415101c00014000116070198694115001400e00c01d1610303611821030180d0742c1d182e01d01600403a882007400325036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 126018030 1250 126016780 126016811
    0xa0e1611060601140c0a1e030e15030c030a290f0d0c17010f020c0304150e09010315090c030b091509070b0309101a0a0e07022a0a08060604 61
    0xc1c0100e07010780d04c2680391050b284413503c0a070840991480c550050842190104040b405407408010000c0d036250103000c414038005e4102018285914002e400c200c03104072800c6190f5040c0ca0b840000e888085582c0d9881c0018140180300c400c2605074040e9003042040d1540c505c961201c18650810307181030703001e0352030041000360840b8140c3d0024000302d0b06d001c0c188101c1030b40c034400001415420f000404c503030405143c103500380d81045a60003c144d0002c03d080004001034804081d1104642c100b45841000500c0460b2040b801400046d00b440020000100c41006c42c1c0d01c50031a094020880c1c9000039140e1810103082c89003039a420040d4030821008000d001c940b01d40f8607000c2c4940000828440d46010301d40000740d04000d00902581c021704281014101080c042c5414030303088581301403241d1443c0c40812145030800c0d0130018000c4424000c2140c1650001000380c6c5682608035000603200f8043c10800355005c0f05040c194022030642e000091150000401600410040f142072003a0711780b440c0c501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 126019280 1250 126018030 126018043
    0xc0f181404060b0f030330070f031a030607030504050c03070b04090b03030f07060203040b180a060b1f05030906010b0901120c0e04060b0306090709060f08060a0e1611 73
    0x14050440c40c0082400070345254403214900b10042d258124143c0e405001900f15040300340040d0800441d14a40389904006007260700790207180e0309030b00b1820b0400d000010071800e01031029405241d515001d1041203070100c842440e004100130f040b180c2c58904510020050113040e14206e83c6840307219014404d500e000700c5c1650a4642c5503140c41d00b0545010083e01c060081c800710309403d0300080002101540b0b2480062011a0280c0d9000d65241401e24110907101401010f54620390f0100c12a82d20300380340441c140807581c0d0028008102c51021100041e03064180c2c0440b424245900000310300c42a404c1809544214500c40c00d6071580d07aa40d5000b524030340301d41b40320580011480c00d002046910240c0c00031030003503007603e0014004d40c042c601090486080e5040000e03207010100401c4090314243d00c002d58420258a0444001c92400700042e1810180004800500c1100c900140d19600c40c0c0341c4030001440c40956403411030170480c900c00600601c50480400298905032069507103c4006801e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 126020530 1250 126019280 126019301
    0x12020c0901050f010c0213020d09120e0d02130213171011191b0206070803060f19150201090813060801060810061b0b040308070e0a03020604090e07030c0f18 69
    0x4685d000c0c0c045a08001618540d6040030710159824032503601a018284900008544100500c94460401100c0506500000f0313030010b00c07802284d01c0060050703e85020702c18220700242009a214464078034625000c5409800c100ca404241d0701c0300d680b01000000d4551a0710700740380001c100c80414074021604510400040c0600034a0002810803942e2040c180c2c000c5003601803a0f910400070361940069110381c0a41e5050301c00710070100900900b0715202c03619818449003125005220102c03031483d8015000c0030b05c42c80092191030614003200300d00039000b0a04e01741d4000c1c460707691845540c22204610030745009800000b260807001052282c015032a9500503101c41c440001804d113090380c1104c00003d101d44191055819504600001e80e102421714020761207030311500e000c0d140078880101a010b0389180c140c070565812204101503215001241c056800c0f07808042074100c2c00d90086490f08901c0d510051046040f064001a0214008501400c1c1c84410318440000208188504203842510f1740 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 126021780 1250 126020530 126020537
    0x90204092d0807020904020d050a050a03080a290d02090a050f1608011514030403030614010903080304151410180501030b150102101515051603120912020c0901050f01 73
    0x1101501c0e05620317059005200401881c4244403969a01d0b00b4440d40c0d1004869035440400050708040d0171a0041b64032442c090001c000b408244403007420100c0b003107050541d40c0264040c000180d610780c16420a441074010f8406602c5003003007111036000742000c0742c2d17501d820300300c0c0c0c004141914031a42003020504c02e40d0341c81d070303445d40d0030402840002d03a4804d8a0a0a0201031023196410345000c42c0a9480f85000303490010306185454184c45034174032845800303810440d01d042d042c80000c0e0514190380c6c02039006900c40250050302c20300e002c002c00c5d40c00c419684041880b0700300100b10000c000080b080d81c0c41e00c148026806071142c400c90968000b80802009030410f1000130f654025885091081210144111450700041c119030b0710413622024580501c2620540c03062048410202c003005036030b2a0351401384e02d0110182c05100444650110080c200031003080a182c50540c281c00c03850300107400924043c81c07000044006942c688003091464000c0780c0c01d13800041e092034007990181c0024010386 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 126023030 1250 126021780 126021787
    0x11a1003050105091f0312050c060f06010c060b0a050a150e0114030103030c03030906022a07030512030c09090c030f10050109050f0616030f0206010e01050a06050d090204092d08 78
    0x1000c0401e65494505c4a0501031112400201040c1407042032101100f0a450322503440700040f00050400d9801007181198841e9541401030603684004201c04031604100300103048800000090390400c4e0690200b544803400d10f00105140358410140c501000050316000f40300f00658005494031a13440314180c82d005814001000440d00407122018150711a19000400c00c202c2c0d6111800c0b070700503014100d850081c0386009460b010280a809071200641720003050060305e180c0c0ca0301e68440740a403031198100700c08004034080b9070540701502c58004000b00205508c0c58944403401d200d420498200d00d00c403006601061800c001e1040701e605840c4183e4454856034280010b10441700300f40c3d1161608500300300074a42101e2070300c24040303221920954a203011401c0401000303141402c1a00940140381d142001006560381e09c10414045413001d05010b9129204100445c00030030315598082d412a0401400008100c0186410408071a081c215105121386004900881a089000c020520314041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 126024280 1250 126023030 126023041
    0xd0908030403030c060902040e16050102030c03030a0c090b0409021c020c0c01211407031401080a0b040218090c0112060f0b1303050f0d020d0f02060a0906020408011a100305010509 79
    0x504c0d03140109406402c0100e0100e0b01a030104045440c021004a12a0028200071800e144410305801c0108400d01c010341c200084040c0d2643c403440041e062800441d903d40030001c1e842d0048107001c0060000303075400c688855417109030741c0203540301c007500080110105511586488440c8280c07900403e170380b0028000b816400005460b89001c54440c9000781c01c0f24404440c4030b0809000340390509022803803850b868180880e01409460b2410702440f003516540c0f0061000300e0000540c0f10f4103c0e000f4060141e40e485500100c3c1e6850800c1e18629101400d07101084a012000100300400b840c0030307a25100c100c2144007904040702c140b805414000f542c218002c02244d8001806841e40c0c2a61003200350700c4980e130b641c949103013007951007188589421090890100c03680501856041d00e0131424a8540440000b8000752101c0004040912160741c42c559001030010990540f0f000e4807a050081241d201800c1c1441c00740c5d00c40888051103160070400545410388603000700c50480790b014004078115202d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 126025530 1250 126024280 126024287
    0xd030c120302090a030f0b0a1b0302030c1303030c0b0c0c03040b1c060816230405070306030611040509091b060c03070c0b0705060703050702100209030c0604080706020d090803040303 80
    0x140e000c0a8105502403183c40c82030b98800100700001e5118881c03001500440b032070f001044c0c04004004410646ca851001c495510a4081c441003040c2c0c10700d0010707506d545040b0001040c6c000c12000701c5d00100d0a15004c0105900030001d001414000c014441c043d548552000c1501c1c803c490030711030203070400e0008001c04048600070b0f04c9007041002c085030541a10b007100b0011110030341c0c07051102d940481c074000c003805400b900400241c80600d0428015542400414913882c003810380190050b5a148001040227100e9030040b0082c681c0302c1c5080c8021840403c0015294215011b442e1290041c10040750b8900c00020300200303810000300c00600b20303215807402c00c07100b5040000500c007207020030411a070004001d6000070001c4c10307031040c16076152071031410f1203480d080000307020409143c0362800b031005045d000517100d0346004492801680d50205040400d003401c1c1d92140c1d00340c00c04000306020814000101e10309050380e406030f0884800d1000100100c0300340b03019201d0607034213400412051010034071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 126026780 1250 126025530 126025553
    0x60901030c052110061106040305071b03050f010c031503030c0302150906011401020a0c090209030a0203060a0e06060307030804030602030703020408030a170c0a080a020903010b090a0c08060d030c 86
    0xc40c0c1002c2d814108020340385000d540c40d5000e03004903803000008000c1c003140c0c0150307481c01805080c0b0344545211848070040756201b101034400b0b824020041071907000c000f40d141d500012902280440b50701580e03030340781c00d50742d41941300d04000301942011b0000082a100744030354106241a030280d00c1c0c03043e16580742034900c205542c200f41c0450144503040140510b0031085e01d4040c4814400501075585080c0081508010340200c083c11034201e01002d20114461070b860078184d40062070011f83d540c2c1d4000010f8600402004007c0d01402261304100707440080d03501c07615001c1603a005866107a0307141c1c0d0401d91907410600004016403401c2c00140041580343c0d000d564045481c0c200180741c1600d841c20385103035402580d00c140004c1d402000108460810142480c0c11040c0a80440c2c203200e404e41000d07081c04002070024890b994042000c601e01c1c1e509411410034800080c010409500b030081d003071009031124001082c003040da6400031481d1424042650540e641d0155a12061280d4980c0d031800903d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 126028030 1250 126026780 126026801
    0x8010b01140409020a17040c081204350a03030911040204031502090d06051602070b0406140708041a03090c01081512070506040f03030801050f011b0507030c0e010303021b06090103 79
    0x21222006c002146807100428081c4c2d0203410b074841d503545442c0c0031901c0d1080192861801d640244400c10000c06141410b110f9641003a02c03207402040182942d074000c0b0501c048810040c414115058141030f056441640030718000d40402e51054218030501040c1e11a0344801042440070300354041480c00309601600000030001c200003035480480c1c03280f60907104103a502d4a107503465002c00718074003601003100c130000300401c100700d5091a01d825400f500740c503207188281030400000111141004111801c56016244443c81002d60390091104400b090300100d030300440d11720070403410b9800356000d400b50900c10404e01809001d01d00500c824000b407800c80326202d200710311614101040c55540e120203000034001d50700150400c6448c508004180c810103034442e60062681e40c0440d07200d40da110b02030403d00d440f01e01054030803520070b2400d280b030003c207035002601c0e18212007404504406410030301c9040324041e6088404200300d5030761030390900100c002604d0744113004110100780355000303030440d51040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 126029280 1250 126028030 126028037
    0xd08070c170a05030106080f01030c0b091201151502061303110a022d09090a02060c0709060602010b1f090302040f09150903020f07080d03020912030d0608010b01140409020a 76
    0x641d1908020103540e0000700240b03003c510084010302c2050f50200c60700da84058a68507a41455140da200c06061411501424017059000603c03d00720b5210f21001076604104903000300300b030100f400e00001c20b00100e0300070069101d41001d0110355003803001072801e021307614581c0c0314201095a40da081e1401102102c0d940500e0260302d44000160b540e000c2d00d040311071a2000402c4515905841c070090420f040303424944940c4449060110046000076540582541518195943d250100c09103150101503802422107906100011400075810b41140c0e4003080c0130f80d10600d009030b5084c21881090108140c04000554400f000c02c05458681c11080c840401100005281b08142d101e80c1072184802d441c0400303540e1100100c9041640c10070448201c2180803020303000c00f504001d0701644880110041000f056008100000156a10500074500018101c2103d5442c0b19064000c2e003c0c0000c5c1c450909294070b0320201c81c0382940141c4e00d80361009080042c2614150408403100000d401c10f00088040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 126030530 1250 126029280 126029303
    0x30a020607030902011215091104080312070306120812010b28051e1206010807051b120a0807090503010b06040522110705060a0903050403030806033301080d08070c 72
    0x42e2207040c410f4103a98013012061407e26070528082c4016540c0d914042041c00d00d00304030400100901100f07451711850592400c8009844160046014105a40050341e4101440d0000c5003000b962100030001c0340500f92110300160f0380ca840302911402080301c113051034041440380ea9051030403003801456040a90400c58100b40c0142c4070035120241c03403600075003080c0c000142048800c022441656000400b441d0246840c40c01c500d00916600640401044640e2150310400c180c40d001e11046c401314060000c400d84a10901d003000300b894005590210101c0ca40c1e42011030700f130506028440032100043c106d1842c040c5801c0078040c0e220301a08407842c9543c600081d0f071240c0750150044104460781400c6564648000f13040460600801404050740245071105020000350010f090301d08413901810304020350756a120100341000c4c00003001c00e940d601800d0070004190b4000c0d4015001001d40307000c0645a0b0707212011241e5030205e1035080700c085010a0000382085100718803c511080c03240891199 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 126031780 1250 126030530 126030557
    0x3010e12071106090f06071a07120e01060602032212050309180105090f062e090605042402160b030a0506040212072a05010603030e0102030a02060703090201 69
    0x4044a250048080d400c0c0000c1c000244850015071140c450001c5803031925003100c100000303080e03400c807008031806102c0110fa018280501c05c4a41c0c050500c0340140e1080600d8203c03002020111080d901c480c40920b42410800b00103814843e10040d54038079001149042051410350b5003e10303080c03043d100740090702403010411310f0000ca041400316104030010340d21610304030204081da20303a158980c0c00981800340100415a10844800d4100441001004654599002103a0001c180e032806400165010114032000495000c408401c02d00c15030343c1d030000c10349441086030584507070b02c91010132007540380400840b005d241015404522081c0104c80311000c400c18860004500c036489840300c401c0102c100502a0340314002c450388128211011450403044180d40900d000e0042c01000801070f00100c03460004d11036803014170060403207140c0e5085101039894128045c150500046001408031040200c1c02e500020039114400e8041e0054002c0307070380d00c410450007445200c0b0160f0402050046801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 126033030 1250 126031780 126031783
    0x131a0f0f04060e0106081e040204110f070c0807080a030e060a030e0f010515010c080a08150d0c0302150306060d0e0703170d0b01050f09060d060b03010f17070e01030b0603010e 77
    0x38020611003e0b241801d601d04400944481d10040107520076070303040500ca002180740542da055010394111000200b100c2c2c0b400e0001c001d40502014414003020001d106001d2202e501404021100020708562005403501d14603512030314071782c00043c0880e1000749440d01e1403600c2c001130a850181840c0000e208183c03c000e052400a800c40401080c2c2d5552060006000ea4604210442d01d82803c00486228540d622503402e4442c00c021141000340340c2c0c001c900d8a00e8032851400032030380c0042c0196520056400c218112140c1880124440c496800071070848103400c1c8284c038480c060040035031f401c00075400301c110041d0006120f4110180601e03d0080000b0b2901c0d0700c441031000300c05800300d0700c900c05510504211440d0503500707030601409200980c0351520180480304c0f5031100350b507003607100c50442d280480070703080b503030047c000424000c4004552001902c0c3c0d03d0b812500889080a06000c5280519803194681e008030360045101c480140041080ba40900e5044000a8000680106200c002c00e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 126034280 1250 126033030 126033041
    0xd0504080f031e1b1c0f05160207050f0d02100c0203010504030509030c0a0302090c0903070504020703050c070b0c060708070509030a06060513110301050d0c0806070905131a0f0f04 79
    0x100d1030b525480d5084a8078500a085940060311000c20040c00c02c1e000d4100c480e0f409034405c1c1a9903210002a400394800302c68002c02036152a02405001504054607101885840040540c006100c2e00300006900d1500302d070582205903000d40110102d4540340c090042c00e05038001040c0901c003000e0718a8006850920030513100b1802943e441b500c035030000040600704001e40c40f40d103105290a050034070150b80d6039844036401070311205007a42e9601c15000824209140303a800340381e01510105040c030134503401c80000c1c4010016241600d88091300d54078081141d001d42c094500e12980f1240018540358010014a5005000c40c107000c4d00b4031403924006403625610351740031581315480300c20070400e506014141d6003150600c840180018400c403038040718a40014410640718020071807080d0148880f909014014041c140181d1b202450700201c00b4000d00000e02ca07460289442d02ca0000590300d06106c1d0038030008040302d00d820361301070303c1d001c02421680c02642d4503030080e130724043c0d052141c3c1c661144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 126035530 1250 126034280 126034291
    0x91410050c15010312030903120b0f0604170d0f021207030909020d0e010501140d1b1502061b0708030412090909050606040c0201020307021f060b0c0c120d02030d0504080f03 76
    0x1001420f606502e046805540c200340349109040c1030010010001e80c200c4130301c2d043c0410340840066090741d02400683c0d201c4980d1f0000390006000280800d038100700ac03208070740c101c2d8054103c1d40d0001c2c0c0c0c090202c80890480481e070780142c1002d0b01c0400b050f12008010a2001d00a186c64240c1548410f000300c12603000030400040300c0c0e5201b600c502e92040a00440d0b0041c0b0710360041c142d1074503d10012600703034041c0e10001041902a850004003c141404192002c2d110078030000400760480c20010390b0310384040d114018070b01d801300c140b03100002d81c43e0210391490764010240390951b116a65041c60303003a02406040300348882c9040202d0a520b10b4414241820300031801040f182c103050090001b26580c040c505011039004000300300020350001b4180008480101820302038100c51301c40c850083c02035410040303070144002808000c040700020510024001140d81c2120800100c42003a0340b03060f01410000960418012100f140410f82d0025a000340202c00301840d188035040755002c01e82c403c486 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 126036780 1250 126035530 126035563
    0xf11030c070201030605030712080d020408250b0304021e01021c2a081b010207060f0608060601020708100e0a0f0302010203181204030222050c19091410050c 69
    0x181e400039981d040c041c01d001404294040e0a449003046601010b9803c1c04001405c80400050882914403040c0e0440d0014105107080e100306402210786403e020780f4040c035400389a00546400319844580c002140e0089500400801142860042d19169000110161410340c00380d5503243c3d82c1e1402100e14005000c40f55580d00340d408000d4001c1c4ac55011101c00c1c2c41150030f200c01100700c00684048100c40303803524059041850405038148080c068850420001c00782400d046819a01010a4001c4000c5d68041010780c0d5081d540c283c0126034a16103807148128581c040c82c1c0795500d2184075407103c1d9403990318000390385200c019030701c810303141500600d0200d0050b980081041140c6d03200311500c0340410440800381100c45160b194000d441e000c2e0b8040640320b201e4004c110401d0003146c07a91560440741e80c000601280c034190032501d48079001003000d001e855003544400050140316a6007903099802020800075011550802c0c03003802c0c11528800c00c24401c0c01c00a41441540c100003048980d8600d15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 126038030 1250 126036780 126036787
    0x5121f0312090603050610050c030706090503040608060301051303180302300a0f0312020903060702060f06060412080313081308010b0a05091506041502010e0c011407060f11030c 78
    0x71030003032034500242e21900425280000707000890750348508101040300d062401a4603184601c3d14281144600c4800074212481d1408071800c0281c0400900129400c5841d8142c841e980da00505007070340c104072468190040c0d20b04840b00003a01038a4028078401031070019040c240d490b540800c0c0d2120300f8111218000b04030760051001505d0041c00c20404035902c1d0090038031050140c3c1c800c2c403854410b100042c00c0c00308080c0340c000041800d60503204002c9004048480b14103000e0000303521101c2c01d0340c07000d46805950b00020030504000342201d003203624518241c07081c148a41c840050503000a02201d403d00c02c0210700c0d102054511000e0f200d84005034680c45c1038070f07240c60b20241c21200000710640c002e4800365010401c560b41c1d940d40075070200581c0b45100030030310a080002c0c140d00c07681c3c000c030990500800e60702444c0d65056002e010300d051194111540c03208000e0055440d503480d001e4102c084501044032000050298014103006d2030959008201000b13139110001c0a90400c80d0441060171011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 126039280 1250 126038030 126038063
    0x53a020a2a030f0525030c020901060905031018060e061012110d031701080d0801120503030106050d0603020901060c02090a051b070f0602070803091b0105121f03 71
    0x80d5400003500040014807112030700556000e00600f2941444400f4803c020568845950b442011281442c0b5a2200190030914900c4c1c043c1507041c11000c203030f0207651194000714035a80078403807102c1517031030090080c80c94040442103400909025510942144240d00703424000402601401000b0301107407010301098541001c004841600d030fa03020b50501509075188802040c42e50210001c07807a404c0d00e006090407118101520303401e140d408a0100110300c280001520b280203d103020f80b100b000e5079401c11503603840010394091a80c0100191054004000400890303002e0300003040e0600b03481d00302182503960781d0000b031510f8800b68010030105444003000c42c118a401e2502c40c2c0c1c4042a00c00c100100d0618031040c3c1080b840d1070200e9000c80307500065100a2054102c50f1121481e40010203654542184c039011803550021744118100b1300c928450100c01100440e01445180010780d80c4600381801980b0604a03004080d101446071020158144000320030030480d035000e58002e040318041d40090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 126040530 1250 126039280 126039317
    0xc0111030f2a041401020c03060424090c05062101060504060806010804030207062601090204050f18040303020d1b03050907050109060507060504080c0604030906030b01053a020a 78
    0xb1030b9180c0300c0801181144041c20140e1410f807029580320306140503240321158010317481c205491741203e40c18420002084100280c40f25103e07140d4110a5403810407403440d00c0f021096136041c040003405030000100a1040741064006001c41d0001040c1d80c0ea074034080038a89060702042038001d40c00240340040d041c030045402081e0313250084820f107001c040c2440c3c0364a000f5110589802550200500c50030f17204400020312418071036545c0b203002000c609503511841400250301500c03c41c0d002d80c1003602c01c03254030719109800410246c0b00d50b01d4401a661541e60850003503000c83c18030403400f5500e500160780100d061f01030044c2010641c40c000342604016a400d4a030800b00c2d03100904011040d90103014459012094510f440d42c030800100d4a620f86181056481c0104552000d0621912041209255021950303400700c8065440c104039046134000111114070446280740c10f424403154040342444404072070601c00001141a05106545c19501a4140da00003008800041e103001c19041181d800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 126041780 1250 126040530 126040561
    0x7030e03070506120601081504150305211206152205030c060a0c0c15050d0f050c04051e04021c06050a080a020d1703010b0c0d03050903040b0c0111030f 67
    0x1111034a0510f00d4013000c940440e40001c06081c100403280f8081400215142a05a2170000041003070001c0f129403510003180c0385030b030b100545981c420316500d00d24031a100000324048900c86040c00b858541003290170320300032202420882d00044000300100d540e50f00c003005051502d51880003000b00e1441c0502c4400090039a401007486074022445c021031941d03c50080710083c00aa0a05443c034200b00d08000039a83c0666124508403900503580b000c12540c03000050007a03008071642040504c40080c03091046600496103100c0440c41008244414640300399490250b0701d00301048900b1406400c0130405a13004800f00300200c0d8040031400d005c0301454080d01c000303484c0c21740d007507418039107412a948d695080000c4060701945604140d64141b100c208103400b0310080c3c0550541d682d59603400400d87c55403207a0004402c501800003181c039220b00c40c3c003403d0b001e941900001e50410b03042c000f02c4241940500c0c141c0b8040e40d6110303922952001c102d00503510030680f4600c2c000242c40d01c0d2890160000c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 126043030 1250 126041780 126041789
    0x60608070e041407030b06040302040e0a1704081b0402190509100c150506060408010504050a0c060e010c06020f040e0a020d0507020d140a030605091906120224040b07030e0307 77
    0xa003051640c081483c0c05244040d0f01c00e0480c42c002c54403800550104250f882607800c003075000ba0400004418000001503000000b9101e1400442060396031419907119007d14010881190800d20320f154002103ca00100d58000006100600c6c181154800340d5a165584840c0400b1030301c0031400c03020610f0041101d0016050609007030b945546161380719801104111035000b0031a54034000f25a081c1c036280d082e1800b406035400200b295080c1410b110381d561064007011036042c0a41840420b000c1d00c21225100e0007801a154054444065586c0502a42242400708a4010144400644950143c2210703001e40b10385000141d403100c1040080065800050101c010f540c41281d1042003950f00c90240490b504406c035080740c0b038111842d801c8001e0601e40c0c4c06143e01c41001c60034811084510301444401c20780c554403c0050070f80e01c0900f001c12a0b0307901c44c0030f503004500d00040140401100800a030503000440c03000d10b42a00d030f000360421a00701c2c800c180c000802d4490700c94120b0504128910161 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 126044280 1250 126043030 126043039
    0x21005040f0909080705070e01091b0206040303110d0903080603100b130e01060e0406050901150501020c040209030f1518010501050d0f0204090c090212010e090712050709060608070e 80
    0x581854001c09181040c0d21656440d1580d6000c41400c0c00030000079503510580c003006550000e542c0362150440d6070000e004144015242058070315042c9071050f01c2107d80c0d555030300070f81210365840d20140d00405010006130300741f59082005180360310051040c0320403280710761201501802c060701032502d007804d00000485054a01011603095580d2070380070f05c0301c0600781f800200da10300088030803030f014180c140d001418029072582400104a980d400c000d00c02d20f0044020410416041e9464211071918410240560490700101d0001c0c1041e80040074103c002130102c2e10310035140c2404515055403100c1032480200a0350034040100c85000001100c03602c440c0c02440254146000100002e034180c00041c40340b400c19140d0411074660340c100c080c015030440305040015590f000494046c1d0710415013a402c402d042c000115843c509001018020140d01000f40010707403c0c9144107040500302103094401d441020000035600500c0d00403440948016174810b40706007400e26004c2e1010901001c1d0794400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 126045530 1250 126044280 126044287
    0x31513091a041a0705070501060608041a010509130c030206070f0c0e010506030c0a02010e0708010615020712060207020d06020c01020a0e01171b07050a0501021305061809070e1903021005 82
    0x1c40c00410310343d0312840d00c40c1182d520f00e03111030000f5907240c0308005000300294203140c40000d00710b80002106104a00404640e61380c0b034030720107001d1140d240901039150300140c800c0104290201c06541c0d250302511502111250325201c0c1c0000b5825001910200e80e1201c40c80c2c490402c100c103600b0007100624014038070704459410400002c040b07000060622a0044003c01d1010311180300350804c01c40383c0c4d440c20941c1c11230f07030b159200746010707042c54000c050781800c1030008000003500c001801400c8401e000c1c4040054941562444040e40c0003900aa9100c102078143c0d801044080c0300509501d00441d0006994100001015003100c0c020003d15060010459048204041c0100c078141d02c8000c1c200c0c0706031f46650100d060a424043c4200142003441196420020880154010f049054240c42d00c606401da81700200329080c4904445c0b21728115001000030b000b41013046245402c15990b0804140d5084807001090f10a0b110441c242112961030400300305604119604e0240d1046a142442c42c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 126046780 1250 126045530 126045533
    0xf0607050a122007060f020c03031e0f030c120a020a1e020f1002070519031202030601030603061112011a120903070602040305030301061206031205031513091a04 71
    0x120760804810152500c4202000e42c0002d61040d03041c01c5500c0700d40c1460001c400701c0321403c503036605054000e1901003400b659601b02e40900003c0e03d0b403030780d003001801145041c0c02c003040700140b52201039106003511000e01110080704442c41c05140f2401c0341140054032403403000880a0180d01c060040401e040c810000503882e40d0384040c1f0300c1382100003a02054030701c00d5010741c1245014002d140704d6801d8010704004400401e22500102a810301801c2201e090501403500180240c402e500c000300803490030000885505800c3d0061940134005040010b0419641d1b2507800c00e07114850305c0b1580c25600080d601130160340b0109100d0250600840c0d000c40050342c40810308840c868000080598070002e00083c108880800c11210700c0307548100f041d500c8075540d24089650750000e00640c000700701004041a040d00641c484c0700304036900b1451528001141081c1920245c0c400342c05809045c5019000420684401c482c0d000890340c80c2c08006103620648c1808110b03145940b00307940c0440141d109000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 126048030 1250 126046780 126046783
    0x20a0503101a0403031809020c0a20300a060c03050a090206040911040b07120906230a020319050a020c0a0f03020f031c0c020108010509040b22020616020f060705 71
    0x8090b26810b046c40c4c1400d803400903c94480c90401d0f405000c400b800002c030407055220100320088010f2160303203454010050340745646029400328800c550081028181710f52070619030404a500b4232201036400711240c122124060070900400c0040e20b02d03944403194142c0d01d40d81407041d560f020400310400c02900707800354001103440c4514412103050382d480304282c0341e045105008035001850881074088c1e80f11200e244c81b50f008100048141c0c0858210342000034020300a124620bd0500c540401086440003825003c2c21a0080142d4008500c000d0050310480107841d03040034030600d0181c8423035440d9204250001c0c83c050008016601401001804010f608030b030140200540e98121000c20300c645c42940440c2c9001144440340034840440e246404e6030540100300790302c205000f0f03a204140caa80b21b90a1141c08001941d00406c1d803814200007600004c000c07400b0302c5401140d050904440341c2c2c0754001030840d8102c0144000c400026030f0b13210f811460b0640d445803200c0b00544000b4101a50782e191207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 126049280 1250 126048030 126048037
    0x30903060601180e01090504050601080f0303040602131d013602030903070f110102100908030601140c0709020d1508030d0b040929070504081905010f020a0503101a 72
    0xd06010f07208581d0809074550a04100141c0880e0161006641e074030103a0320b001d0841502c05a4441c051303640040740311403001c5124402c16044c807000314a1510340b41d480500070750002403080083c0b03d002c400890400c5010304018400400d1055032241075040003102a5440c3c0c1011510302501042c5a050145180300b601840120b2481800162295038500c045803e510501030020001c0c3e12034110f850070412841d0440b203c8410a9080f200c64400070741408044030f615150181c60a1810f10010788103600c101c00e9080d4102c280340302e01d81050104800580f07040b605401900c07138103401049491039101c00b446810307036082e11a65007018003854040340c180c40c1d04c02c1180000e4490703101c0020208584840d0080b40700c0540c00181c820f2540490000d24100c816507003084071180e003100001c034440601c901c041d035056404040c01703001c82188400d15102d100480da102102c0954036800a0088200302c4c0c030203030000d03500603142d10f540c03840c298400008009058018200f0b603201a2000c20038190904147c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 126050530 1250 126049280 126049291
    0x327041d0f1c0f1d0a0609060801121502030403020f0105090a030201150f0608100f0303050a020c040911011b0501090605060901120c06030902030a051006090b0d020f0108060d0f03020c0a060203090306 88
    0x5030f2084d80d54060752010000f20182c00507000a03c601c00001e40300d51000400c0101d4400340e850090a98a8000405401c048044080c10503c1d504100c0442c082695000310781051103401140d140309884948507003983c50071a008050f940101c880201410740a00030031913941c4103102226981810000d00404400302e030b0082c01c04001c041400900c9081d031000214000c0c0041e07180d5004007030355074640100690b1101d4003d4006028800a16001d810140510100164002c103020081c00302c035401100d40b41040308000d000005412401c0006c24000c2c81110125030040001250500d4804144202410b040e4880b98135414a1220f400100380b03405d0030345003078460b0307494007080068103800000d1030515182c00152240c01402c81010342c241403544600c0131078a401c001402161086c108005600e4462070740690004003844d8807100540c401c1c82d510741d118400505444200d44142c4030b4a0340303808104002c50242e4000d04440b68140f800900c01c100500052000310f20b0103a81e44046611400050f12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 126051780 1250 126050530 126050537
    0x90f0622020d080706090c0905040c030803070302220509010506030f010311010504180b03060901200a1b08040e0c190f0207090e010209040e0327041d0f1c0f 69
    0x854000c550715003264441d02c58006500c0b5407509940d0a1003001400a03680c02c4442c03510070440000c407040b19016191146030010302014049140d03440303c940c603034401881102011360800c80881401c07154520f14060380d0a91a844d014036040c80c040c0412110180c02103842030343c7c03c0c02001240c003d0101c04a0540350312001c0419000746060069440f809581c01030400b04048280302c0030080200c0d031045000040850840d000da8860702120b0742266141c1c041d000c00d46558400c03c203c207003681d200402c0c00c03016a2525406915540000c0c01080510a508a0354810300040802030400e1114610380c1080e0f41d4125546407801406a654844595440030014003440350071201500e030003804040300400101c2c50500114841d140110300035801450750764441d5207042200a221540082506c10f44409500c032008001c01100e80a60311101c003251899000e1784810002c3d010142c0c1c2102c0c100d8220001006100c0350307400501480c03d0403004905844003401180443d401c1662080555008000904 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 126053030 1250 126051780 126051841
    0x150e040b130606090509060a271410020c1b040204120209060103090605010609080712080a1422050f03010b030c010f03020d090503030403090b0a0503010312030f0f05090f06 76
    0x58100d0151105a011684c243d00d440d04108040101244091007540c110303404002001d0180d014020b1410011414211400284240d50000d040005620b0a02c0d461380121070b0034180300250031080c0e03070109011011315005400045071400310400881d140304400c507402d40c01c003424440070111101241d20040d104070602000300b00d041c6d02991103521510741001c2c2c01e00403503842d0a009802c40303c5511076042c01d882003c50000f403030381944040c1038049511120a03032a01004100448450f05008010035001c2010400400300d02700e0326548141881d804000506854503280401c00600300d040341c40390082c1d05080c440c2149580c0407070400030424090030a82c001108501d011030080c040d0002c0340c44814a080d806100f03004000010750301ca1880f030395980000f940c036a03a41d074619000d16802c180124005000520000d013241510145024951a00090f90f100c070404070b01c00d850800442c90031540d503420902c420380f40107011440c0c0c8148410f000340741c80d0030600d00703aa2416200000e504902d00c00807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 126054280 1250 126053030 126053033
    0x1104020a030b04090b070e031f0903110a050d08010909030903020910091508281113050a06050a090207050304050f030a0c141309031704030315030501150e040b13 71
    0xa03070160b208140301401c01c00140d0024030b480038001200303a0718880814580655003c040c90006445411070001c410045003e42020110380b01401c0c140c50100d090142403040c801c11000d041250b402c44c540103034024184440c1d05000509141c5041e0004110030742001180c0c0c0100e60041110707400c8a03410f403009585a511002c5900310b52401d90009090740e410882008100056240c290065505000070703036080694054480e01c03a1201103414100400030703580c030200031400081802040c400e025000d807040340302c14032408003120001c9492400031942c525051006041c481002005040b40c0141180380c06440d0f2100741da42e02940c881c051240c01001c4119116071400d04c007508003940d104c0280301c21103458032000101d034007014441502032400c80041c00c2000041d402007484942d019201c080c039a488240125148003001401541407540b81c10b00903240722480c0003c7c1d0001c50107080002201c0d01141d142e41c54441d69540700545905c030480500000c6020028403540040d184103581d440e08403070303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 126055530 1250 126054280 126054287
    0x4030e06040b2206170f04080d020d052e1202060405040c050d0b06040510050703020c0918011a03030a050703020c0907110606092401030605090408040303090b071104020a 75
    0x210380110001800210300f40380a00310074503110100d90000550044815141c040c11240408001c0380c0000800611010a010300c0b01a465950800d0207400b082c0c0c500411020700006076401510b0104400d90744400f00b00e04100754100e0300d800c485066064008050b030030310713030819840e0071030003a0b010a405a80e214021903540310203c60003420007600511011401001c080c1040c0c0003040802695400c0c003003000020710b8408200c0d020b8603001044d20a0303070a41c8030b400f29669008480100d042d0301c5007440000c00790b500c2040b0144600008080c1022882400701050b0075198401000c008500001017403c0b016a004019943c00c00c0b4030340350064651002e030a0403450100c2804200c0e0b00315101106214100b940031140c3d00040c8080c2c01100c0e41519150140949008102c40e95a0031030f860034a24021404900005074501c9414075000c10055201c3d40094401ea0b4181c03000c45880740c000501300101a004090303407005080d4051607e0030b02c0210385403002810b4021981b40d210766400101e44502740d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 126056780 1250 126055530 126055537
    0x30f1b0f0303040e0a0b0a0b0a090e070c0506010306360b071404180b0105030603100b04090203060a020a020d08010810020a09121b080d05070f06090212070e0f01030b04030e06 77
    0x4013050600b041e800e110a02d600100510f0341c906000e0f10741715901040703503d5200201d400041e00360341d030b805c2000d1030000d44d174240b800044c00507420890400041000300e0000c12030107000e50b024010008840c8107868052585100c08203c1c0450200c1450b11000040f001c04c1400743c40e59040352051080781e465044c00ca034040c2203640e294400b01400318010030640d500300032003000780c01c50060820050500900555050108845191b03150740007044a070844141c54028030b003040b001038400305106031640d0020b4108001120340882e500d80c00704101000a604000c554400050303400c0c00c40055041040b040d4a880c4a45135522140d500000c02c000d07041d200e01e0310000181014105d520030410740c1c4ca880440d07001c058003c1049116680d80105100c2c2d40400c94644004094441900c2d24416a46e02c04510081402c2601c12950381da41da1000f58403100928818025000d010700070701400d020040b007015a016218415117411440103200241d080100d890b0400d4060a00340991080d40000450303510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 126058030 1250 126056780 126056789
    0xf0605210309030703050c010e090103210509062d030c0a030207020307030c080c040e010c0507022b0b1807050f0127060c05010f0e070e070201061a09030f1b0f030304 73
    0x318102000081c417402085c51042840241c9c0ca00c0740e4294404e0800640c2c1d142030001a2824906070021804400c5c2498064100c1f01d0701d0030024107181080c00081c1107500402250385001d6001c000c00c4e14900014000c4a140c440116420703030950600603810000f6003d41d0307021001745179000503888195a41040220029540042400400c0392100d0034592287c2c244603465000d41e061070781c0361005030018028842c889005079203050030702c9000d80030411403650704044000b94841e200070302d040a45141d00d141401b2401a041d005540c01c1c218031160448444a00d000b42d59003100006000300d65802c04d141490060900e00328980c0da42020b008145421054181400d208240d4000070b80540c0103004541c00740c0c0035100030007802006002420682d803c007403198080d6004650700380440c00400d0000303600f0991500c000a906505c030030a03910f200d0756000e00c80182c00000b0541c00d020317240c208500100d44810801412103141491001007802e541d00070740318070520a00347c0044c0203403010001d840082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 126059280 1250 126058030 126058033
    0x803071209030c0b12090d30020f03090d020601030309030609080c010507080601021915090302030d05131101030c0c1203090203160e010605030403090e100302061305040f060521030903 81
    0x4644c3c500c0d4607880d6520280201d02184801800564211760104070008148415260b015005400c40b000c800240b50400c1a45000d142103030f80005403405074405852002031076403882d59613040c10402c00d807504141c0f03080b980842d4465001440004d072302a102d0b0086039170007200420400c1d4603113800f6a40380181100114107603e08400c120203640d00020716401803000b0f800b0341d407030710840042a401c803242402c07024107000c42d40b5140320850501540500c41260280c07060301c0c1070140c038035020010780f00c0503a8001202d1545100d103005200544030b10302d049401c00d017410800600d0b9410080c010a903030704800391101880004003118103010750132110a09500a050751501c41d00c58505170030a48850103441e0200040300c001203803190282084038090780c2c0585030701c181d01d8030705411100002001800380c914920788a00010040e10303014041c10384000e900c0000e0005c90308040130300040b6524610100e480740d027000d004000c507407102504a103003001ca18204000034044d000d6181c2c903522a100105805 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 126060530 1250 126059280 126059303
    0x190905150a05041a060a0203090a0e040203060c041214010f0212100b040b071101030b0a09050412140d0231030c060c0b0106201e070f080307120903 65
    0x145141140303041149401180c01c425003a80700d0080c00110b943c080300a80b103207400012214500c1c40d000c07019206d00d0f080c602c1100d2410100d00086a54410300c2d5102c00e4200f00380401f80003c51406000c1030b6031251101c100349040601c4c041c122040d0410300e40c005448541003107003491900f075003034100c0b201c1c0455001c0195035802c0c41e102e810701da140c001c0700d0640c0030040680c404546030300c2c0c0c00c044408072264002002c1c1400303441d0300e8a02100c802c110b4640e05256a51815079400d0300e03210550740062641510001d030500c0c040c02d03c40010014181c04004000700e0f20f103200c403c1407008050b11020800300000580f943c0140c04050b03115005807543c0032107861800c054090038030303002045406480c8114141c82886980308410b4842c406004e000a0504500c200180240e52040181d070600103920b101c0c904404035015007443c10440c42480400c1c0c0e80048044056501e4010444800140409200700010300d01d002c8129440c0c0c0102c0000400c2031100c100c040704400c3c841e8100c0c03c05941c0000c0d51014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 126061780 1250 126060530 126060541
    0x1302090705030709210212010902010f121401060e01020c0f091605090303070606051f09050d0302012306030c031606031509060806040201080a0902090606220305071403030c0c190905 80
    0x10005d080031049100342d0340b000116810580600070400d000c1d5060f143c0458820b281e50055070079940e24000b1302880c5640b8007610410401c45850039008080c55202e10003030103041e0307000908001c201c000c10b42c098001d80303d02001e251190b0b6900360744064555008110410395110444561007070b03141440d41440085442c006000e250747c405c400310388044814000082c1220881c407864096400300502141000b0741c01c01007810820641440e241c4030b0301c000152a20f14002034101c508005551000c4075180808110480c02c0401500c075886500300e004106079510241c00e42100059030180404141d02d582001485c2e1019001c41c001404c50070109120309500c2c0c0303030890356a00003143c00703a00203640c4d40042815010300f84907044d0340ba50060a00c44160355290240103c540c0301d100d6400e0440301c520b1414400e44142c20319180614031400c00381054503d850303000c11004261500302c62090b00100700190b050103000446441700f4100342c842106030802228085150707007540c0c0c01031a09074144410400e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 126063030 1250 126061780 126061829
    0xd1d0d082a100b0607050312040221060c0702030f1002070302120711102a060c02030903031209030702060309010b01031a031b06071e0302061302090705030709 70
    0x94010702a507444806003505088080903410000040a21500304a514a080090310381000c02108800b920b030601d4518555952451580403220405650100c3c2c818081146098111790410040b01182c4001341c0246042e60f6841d90b001170185d25243c1070018404046407010b101d00165154074405603801040d00554680180d0f2003000214018003d090b0b0302d15030011483c00355014503410a010350b0f200f40c03481c3c0501026864007c48241403000945107101d4000d0500341142c5018004001c03040710607510305d807441c169144a010641950001d0081e0443c2c6e46000041d40c44a1500424402c1b0544561a0560442c440c5000107508081c0000c100a260441508181260300007030b03034200108a4009030300303200b80071210380c69545600105540c032504451920f0030b0180c0d00005000d14a4044c669441200540065a00d0036040900381405000d0540502c0020b5012491110008510b9240d80c0010819840180198140035000c004604414451001d03080038002000e0024100015280c40b034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 126064280 1250 126063030 126063037
    0xc071e0302060a020a330e0f0d02070f0503070501081306090609080306030c01080705030a0b0a081c080c0301030b0402121009030e03071a03060904030c0501020a080a1b020d1d0d08 79
    0x1c2d00c5459280030000f86e0b104220000c0c150342c062150490354000d04042e582d5002d45000e40ba000c030039125a50380074646850511400950095030340082c100140f505401a114030405d6019910035009010200010b036000360360198004041c00e1400322a40c21403030814020a20748001401091809080c042000044d100450040c80110211112400490011114164102c54803000600d09001040d0020841c0d001081000c000801e10600541c58400d010700d059001d04044440000c82e00c1e000d080075400007071190f00040141d07003e502d5503045803120504600043c0c8002d01503000070032110441c01c4240454592080c20000c2072041c070038a0f08000f0034944400b42c009109000380c1000103211130400403408681c0a000403a41d0555030342ca820440310b074000520543c00d20090500e42d0380058070a200070880040c0e9900c1c0d2400d0f038140803244030110f41660103916030011040510070b060640024140400980e00c3c505240480b10b24819848202e00100d00300d40c0103007240c680030341000101c4014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 126065530 1250 126064280 126064283
    0x100603241e0506030420040902060d0603060b0a080c010507080f030907140d0506040605060f100f0201051302180a0f02040605070209090d080f04050312010e040210050c071e0302060a020a 82
    0x801d11210340312420819584025078008000000700c1c04800c00c01001c1404500340000000c00c0041c080283e40c01103480c0740d102d400740c0034607a56540020f204000407449031805140041d61211525418040003d540d40011a00941400408645030b41041904000c079408003a0650100e038a07070a11a08481e5111014080c2420304083c1c0e9015a286013031029448001c5c1c6c2c1c011009007920740715625480010071001e41141d4105444801c0d044094440316402941c480700c1e0f540d030701c15040d480c1034000c0c01c440020300650564102c0c0222040513a544a450340141c0400211956054503124180e2000b400d041503005a00d41c000726000401d55023010242001034000d5941c0c2e441035403541c451589038880700e140c03400030610b030030f010840300a801c070242c030f921621031811a85071000a0b841f00c600300c00264041d140002003c8201300441c141580b42d001900784500301281403107041000300340c450416000307a085114010640e5090113541241c808011500504001c0c0e4070321030b03c50025111407003d5070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 126066780 1250 126065530 126065579
    0x20310092903060c2b0207030203040303080105010c030507080306040605030f0c04060b03041e08070c090e10090c120f0212031e090f01030903050d05010602030903070e10060324 78
    0x400c54070900303010444510030220394035440d1070180040d1700c050140c0c4111150b048641824200110300c0b1407075200920b0182c2c00380d0021078072180345103002845c000e0160006410030039942002400244c1007000e807540c3da940000c85035140d0340c80c0e40c0442c005200740d07800300780d06d440303005c243c2814203801064090010100b9103041c040c5545030256003c440c402a60020050b003a808d1002d840c03e003a20074042a1f43d81300350f07541803901c619601d814a008140c0e0300a2100c0039621144116030038801c22850203400c455407414400344500c2e031242c03690401c4038071940b1000c13000011001c003007141c680104040d041c0e00070b0a140b0302e00d004041c0165682c005400c80138801480001e04800d0944000c00e40fa4841c800a08107000d41d4600e000450180a040004500f8440148480710152503180242800390141d98021500c07102051304041c500070702e541c4510704454640b01441014894201680700345c9050342804606104044442084d58200385c4480c0941a900000421500700714030b00c0d900003441240c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 126068030 1250 126066780 126066851
    0xf06020a0f02060c09010503040f0b04060c030b010e030d030e2409070512031818091f0b01020c060a0c05070b04050103060905070807120e01020a050d1a031002031009 73
    0x203505a036030318800c0d240341144030405d005610f401d603c640019a4041e11484000c000449039644442004a064078101ea040b529050074496655051080104c1a803092819080584151000c039880e040d500b290f5404040d129011b40065103000c1021800b054110304203c50f40041b03010403010070344815104203486000e0558000780c18a05150f9111802c109180030b14a00060020900341201c43c030a04190047d07904100300300180607111500d8800d40c42c40014296084aa0032008225030413a8100c0a2942c9401c11042040e6400514807101110a4030f040ba80d400400c80d043c0d070170026420004102d40301d200c902081c060000d4000d001100c10170780b000c2c0101c076150140141a1882125030500044d00c140004140501c5520407120b41015020002000c0c481d04400c1c60990740070003000408150005840254a101072040321440503404103448010300911000a0b1200450150441217a40220203e40c00c01e280042002c0108042d82c002c02c403030b044a403040d1207141001c5d010701d0380c03540713084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 126069280 1250 126068030 126068057
    0xc051002160e0a060512010510170a0204020306031513110103060605220f06170f090a080703050c07060c02041407052502100e03061b070605090a0f06020a 68
    0x8000a01048001d22600258104218000500002400c0b83c500320b4484100103000c0d02da00078200141e080f0314001080528000e480703070030001a260b00c14480d1411844445104800c0490011852541260096500d032540701c0068581400f40b03e654080c007044805205000111011400449115050b01440100110010b60450320b4500c0b440d40800e10401540944050713411070107080c940c80c0d00145904903211182c0c0c80308024150001004a41840030101c605103201c50a50352020384203454006c1841c001b64829112440d000d40141549000b14045041600039029207800d19080b00c00c90300801d03560a0000c001032078100c4280e00403454014400905030f00c42c90b10364860540790700c3d00d40c50207940c1c64100c07141400b401c1c0c684840321500e03041040142d4400500c07020020059603141d107500d1411080509005000c2d001141e484d01a80360820848940000c1d1603410f6004000000c16a45a0328110300340309150400415184090301e005003080125406410030862546d00e040382c00805 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 126070530 1250 126069280 126069283
    0x1d06010801020c0709110c07080106180608100203040c0806090c0108070e010e060d061710060b07031d060904020c0a0b010602070605160c0e1303020c010302070b04020409060b0303070c051002 84
    0x1900f809400c2500680e409006826082d00722082d0061a444002d00e00300814509609100458002d600c0d076175181c0e8010003400180507c55103815800c0035042000070728080750385941d000088512140780e500400000c0c02e00a54014240003825000240c0e5000c2c42c000c258180c035849500301c520b020565000c0072400345442801c401a100006071140320403104402d0821541d0f0308100e9000403240d841d5030001c138145507130300f5001492111001c01403055040ca120b203801940c10769006202c48a9040c841c40d00403d5110525088903258030428110031000744020400c00e1294502c580d40260000403e03072140d1900054000d075090182c2c000c4071b260398803800100d841c0c0440d8030500000520500041e8403501c1c0260084501505c5a03184c855074691b640c89505c0c0b1000100c030307041012541c18040d80b06164062001441c518400d10701146031110301d68811f800c800300540043c1c05282da0700c890508000300355002d400444c60050440c0d0b11005145400100012203014890003005a044d520017540e00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 126071780 1250 126070530 126070537
    0x1a04051f030627092d0213020c0303150d08030403080a0509071a0903010e01090302160f0e1501090915210b04031d0a1706090d021218041d0601080102 66
    0x100400c208070008a2403c204002d0303d4004015200c9100d0100d1002058010603a80c0c0c002141030802d000111000b40108611b00c403280404500c2130703004010342002e000000c0101c5e40c0c0140c05800801202d61a940030072003401e000c842c024032400d4000240030034150810030703ca1180704900030030300c642d94a00555540300d403034030710442d02c02d1810600507185120a8002a02041602400010710084180505800d5070703e0607205070096088610303090718130760710a12441c01801046031a007101614140241011080c014103189007502d0b900c520303284c10ba201c0c46010b0300030050414248103940840d1481e90030078040d03116000d01e1014103140081c880d0154212100b00c95042a02d106559840c0e4400b40c0d050603521001c14050200c51059445c0c40e030300e074200480549030850206152200c01000c071071a101000d001122507038407001e9810381c000d5000800c2c41705041808146502c880b05141c11030762090071455041e80c82401c180d9480100d6038160441000062248100d45280e60307076642c0b4034202e11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 126073030 1250 126071780 126071819
    0x7120b0d0b06010f0c0c0605040602151e0903130611010b120a02060304140a080d0606020c0a1a0409020d091a070e0904030507020d0f0b100b041a04051f0306 69
    0xc41410000c2c40c950300a0381c0829803840baa0a1103c8138040540c0c0384038201c0c00e540c0044c0d01052001c10280300030340e0704115a0701c811410f20740500c00ba042424056200b0601100b080c1c0401204600045c5108000d02c140d0380310441e10001054000d0716008040c10b150721000510850398a4620306404600c0c0154283c42c0700360160020b011a02035540134405c0b650700080c010f80e40b02c00c1720200800c003901c0c104840212540910261a02c1e02c1781d43c2c0c103035000d650840e031211046500c0081114883c1ea2410020411201c0103030148c209032001c0d51070100703d070045502403041544041041402094a90802e0390110711515010b2550b081c4462543c22402040d41e0740c000090f24800c440542e810002003282d003090207030416034206140e44c0c0c0015941100c5140440302000c580991808200c54242d00c580c22090740d40c01c009405040641e540203600440c030984003941444d1540361803a484031800c8a020300b20107030501c0402e801526810301044008c12140c0300291805100207403e10421100e5446071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 126074280 1250 126073030 126073043
    0x5010b010212250501060b030a050f06040e030d05040303061d1e070801120f06050117060a020301060e01030902150f0403030e040c05040909060b040204092a0219110907120b0d 77
    0x200380c03d591846402c010014101c5680d980c4007030101ea03240781c803170280d0b100d40c00340c50010600385088900c0c1e1005000250515000c0c6060043c174120b032010100c240d6a0400564000044698a90400b28042c08460b07011009400081f0142082002480c819920a512100440340d07400e8103810300c0d000114084950400040d0050018841d80905809081d03d003030282c1308021a04003207456010454000f82e008a0908600c0424095820300074880c2c16840104034504604641c501040038201c0d004c0c0300c00040c100350351401c003070045680e419041c140407a1741c2d1480f95280c0201480003c07541d80603000507400b150801d200340002c0d2909008408800b18155500c1e4242440c0001e800d01500450b13004903a041c2c2c45503034003410364072188060401132440389000f2941902103030350190b0400900e48580002c0088005041c6440c0e00018489194144901c03d02c0030b8568500744030b80b80c0441082005c0d4050404001d0101c0907a11184020700190310020400403613510704c041180705603000f10000c012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 126075530 1250 126074280 126074317
    0x70515070b0c0a020109080a0804110306010608010512030d1a1e01020a061a090709150201090c0b030c04031704050f0907082712191403040b04020d0206030405010b010212 75
    0x202e0355400180650485500010030110455900c3d04100d40158441c0c6000900c840104000d100b040e0740c1c01d4207041c2c5c007070300030b84025410414014409141400b9003801820078290394030070710074100101c46002200003410008a04010748101e014680f020089218640140c101d00703d9140304014140c00f0300e8160020803c4144540e202805006225403400801002040c00b8186d900c07600b02c00c3c0d21821096039802d0410b800c00001021514110f451001168076122000e00085c0d5040c46501c00e980404e001240c4035500c4503120349a610a81d00010301c000c1144007500140d48180010f80180d601c1290300b499841440000d214280750102d8009000800c0704011442c00ca42002e000b0140c0b0320320400c6c580020325101c00701480d002204001480d00c00e80002c00c0004400b544142c4040c85c260341c6400074a0419004083c681800054400381241c410500400c007190f0340c0403464100550b02610483d140c0c586800d0040c0200105200507015014100c48101d440280c402200c03c500816801e2022 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 126076780 1250 126075530 126075541
    0x2808060f04021009050907020d02011d1b0402040302100504030b010b0918060f0303070b15060a1403070203041d090c03120703030e0c0301060f0609060203090108060d060f050702070515070b 83
    0x2801c00d8804094804c1c000400d9000c510ba40721909190320401442e0003e0800a01c134040003402c4605120781403c43d140700103000854044046401420600040c0d11034500d400201e0000d070080c40303030340c1c0000e500100b00080d0310503664000c005001200e00503130122020303a0765610700ca80e4500c00d0441c50765001e614403138445541e0410024454002c00090310310140b6840810201c0c2c83e503400901d05031010600d00342001000c100004041030004804e031025801c0008202d0080d241c40d031100d401c001c0803031004c070025182c684200306031001055000e600d13580b600e944094101d801c2c071003519481c5450145541c4503c076800c6c0007900e4103006940c24100c519060b1a51812402444200ca00d10303804d02030100540015502401850081c00c40d403802c258001c0d11f080c030007411048880c0c1c08203080d50004d012001007681c01c00000da900c03001c10381d0b800707946480505d040401886c1d00c0004a04a038513140c1400455940001c80388261402541c01c8440c410700380806455901401000508220076200000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 126078030 1250 126076780 126076789
    0x1f030b01050108090f0f01020d0e01090b0c030910020f0a0806010206040206041e03050a05010b030d02060613181421070803040204020a11060f10171011092808060f0402 74
    0x55002c1c40c40c90664206042c0ea040c006d0400c0b03180c440c5140309a40103e200f40f0780441c075104a80e201c00643c4000c00a4100781d03614443e0f5420001c02818100b0360100000d03080c11401d20104d000f582061904658a140d0200ca00023150410328031000000c0c50b03200052a50b500008499004980003000c1d1420a413820114421450240b000a08642841c40000001400070006110b42911800001c20f07c032740c01c1d0051500e0008000705a000715409202400f0140e140c504900901007104e02c80425206040300d0035528580d400741c0010508590214120f403025004030785015091981c08040d40e20f242d8414030040079018012020300b0010041002c01d0042c031b003c0d030040009600d42c0c1442c00b61582c0342e0a07042c3c20001d08403407807607402075071078100f210044401d80c0072000b400b107041c14140101040301c4660360340c0e5000204c658400c1c0d554088241100c0b00d00c001d50700e1508000b054601c40b8010b03c494151500540c0620100781c500c3c010000c240d154010030030501c02c1c0d580c41009503c6990319001c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 126079136 1106 126078030 126078047
    0x130b090306061e010804020a050d06050405010c03020703140a090314030705011107050303071809020408070504050c072004061203050901020d0201051605301f030b010501 75
    0x18001e00c952284a940c03c1c030078a046406035555102084101080d41c20107075001240c0c0198200300501500414441c51080000344010740d6141d00640c00d90007034036401800303e50000020390324085998060410300409180044000340d0703d8403062514100c9030040003180c2c20000b0041c1c1808024051040d0604100480d28506800c0d51141da44a00000d03007060108501040300e81000d0448514503806414118002c640d02d41d03075210225920f1303400d4861140a14188000a03c40503440780c283d440c0d05410002000e00b01c41c0301c1400c04070290324070301d41650156071401c1c0411100580d106801c1341c644a502c81c2c070b940e444000000381c9001201d400c28421a03050108005512344252901c03080d032846420907030348800150f010301c0055483d41d0200001080c0701c0c1103050190240b01c5600c0d0040d00c02120701e5080c9400c00e69480c1c68900e00d07020107088188060010031082d446181311 = true := by decide +kernel

theorem cover : BRFrame.Cov 125899280 126079136 := by
  have h0 := BRFrame.cov_init 125899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 125899280 ≤ n) (h2 : n < 126079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
