-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3978
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:13:50.643027+00:00
-- url     : https://prove2.me/submissions/e8d22d36-643a-4d47-9096-f2c01fe22bc6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 715287769 ≤ n < 715467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 715289019 1250 715287769 715287809
    0x12040303150f0302060a05070f05010216060f09020a0e06010c05300a0512040f05100c0305100803030c032707030507051503161b0803040209060604240504 68
    0x912822200403648008031000040e50b040c0b038002c900503a41c000b03200c249842084841920581e0006508035001d0b0703030b12502400420420b01c082c0401c52200500000036010b030f841d01e0002c54501e00c241d80b00561610300149c02584851900d8420740d019505c1d609140d03100d420040c1d440c100450401442841a0f85e03415180e01c0782160200c1c1c0c0700131060007032070005d20603080011031130044110f21030001d002030040000b00200e0b0075150781c0017401100e018070b401206449450030b001d4801c0c00c1c900c05a4854480001d850f6040c45034550003404100e0204c0b0280c180030041e40c90f4071014000203510394000c40030a1350b40e241c62041c029400720b5040040c1c1c1b00884030350001d803104418441030351140180b800008403400c3c036084900810014000c001d2450303443c0d03401c044d13501985948001c100040020103140c2c240f000c2c03800301c0c10140602400c940300e1070103204001c5440802028580104c609220401484580c40c81a20b6160104400d25800c4046620200c1d01801240e20016003902e0032003600701 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 715290269 1250 715289019 715289021
    0x2010e0a0f021f021002031005060304030f09080f1b0f0307031202010f0213060f030e01020a05070507080109230a150c03150302011b020307180213060e0607140312040303 75
    0x3a031107209a0340745241e20a0b484040070581480c2c500440982c05c26035030400840e103103038003d6034042000010341c85810b4030790011402a40007240c00300c01080042a1140d0780b643c2012003031008000b00002413808101d401015500c910441c0701454000c59802c070795611907501c5210180c100c140c0a03040301d82e029a40d052481d1070592400d521405546012034131600e404c190700840d9000c01c401c40d000c8001a1415100b01e0300c2c03420402c90700007055560b185541c5550307000c1c001441004169078840f034a4400ca403c050307041c070707000f0b60200481c2da05d04505640020040c010380d600c43d81c00b07070110f00c1c4140e140e40d030307a14101521204014283e00c2510000700801e90b903070f8800c8036070800d030303907420072803c06a401c03030340d40001103400301070701060380e07400c64112400c0740100c07481e807203840501914100e03903a90f00789500e1401d8410201c100b5503004100100c400c00c810451800400301481e00340040c000207008585203214000018103c40741c4a9140b404194081044440e00003180380035049034905428010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 715291519 1250 715290269 715290293
    0xf06210b0f1e0604020d06081c0c020a0504091401020c0d090510020a0615080f07080c01080f130c0321020f0c0a090c02120c0d17040b0a0c02010e0a 65
    0x151203940030004500500202010789215903404618812001c9008155016010300101400e60140e0200301c1c10740300c0e00081c01600b0041a940000b403210540d240801095005462402d030704211030f408882000d80d440c0985501121015140040c5500c910b0404841c110380c2c03030701071481c80d6000203040c000040e40080c54100002d000d54400c4819511001081414410402c1c004010380c06190800003003079450b4000300244480c5907441d2101951440040d003045180d210443d00d94001c4801007003070507800d001240c40301000346448141854a0800c80010328070187c001c40c03811003483d451401304100343d0b61410155400c00d980c0300445803c000c4801e000302a00c03001d0001070182c015000c00c0840300003410156940024a0350081d64240650880200111031b251021840390401131a04624290004e0120300b69100150140c6419190b004d42441116480c51622806407000c110109402c02011a003110070414042072034426078104901401c10034110080e503024032400d50003001031400e440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 715292769 1250 715291519 715291523
    0x9060405120a02010801120b070f03150602060f07030b03060118060b1204170301051e0a0b210112020105250c0b0702011710050d0f051209120f0705040f0621 69
    0x13402d003581e212007d4610001040e2001000d5125403404210840e0050118248a01f03807440c0024131140782040703400750740903560301140258102406104000070018651030307001001d401c080c030402c0041008607a803100c05100d003509100040800034003007811904400014a01400341170389820035003030340030050f0700c2c2a9003c84180e240d8a603509040c40614094038100e55000b000e9541032540e94003810881e04129010985c09494068049050040740c8040c280c061084150b030180203900449107101000b040c2c100c6040341021200c6035006031303400030481e80d9102d150300780900e500740b010705046034145000d20300501c5943c885078003042145d079072009440110b000f641e0b0074209802c170a5090181d1401540d1a072244a411003040c090360902c0d4281c40c240038800e85481e50301c40c0d40c030740303400c0d003005004040d9404000000030340401610f404800010850724480242010460005c402680c0705028821640150f403690049400e6146641c030100c014a44403021080d080304040141c90480010781007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 715294019 1250 715292769 715292777
    0x1b0d050105121204270203070509011205040f0f03030e0d180f030c030209180a15050903270a090f0b0114191b0615080d030c120209060405120a0201 65
    0x516900802c0002c1c42040c907250000a2915250510701000303105050f007440e400786040c0c9104c450180c00c110384001c0d84070f14115602c0c1034890000c1d00004040d1803002607801d082e107040a0078031012030b200d80c4074624680c2d40804c118038005140c1c54290060160040e0285060003003281d8070280f140c00205e0b1b250002811350000b03c08607154600205d0517400382c0030150502031150003d02c01400c051200d25004012194000040480c0c05036203031500c40d44403001c450300c0e40f40000c40351840500b8040e058002003164041e5040c030640b0722820720070f000c03031544007100d4020300b0002d03c45039107400361050003a202140b002e003d140071908904024003100c2c4141c3e0700003103884041d10200643d40080e2850300b2074284145078440c42010044031100300c071240e182856407035070381c034200022424424514031b0742c01d040900b60107909c2c100d03896051140d03940d100800d06043c4041d607128558030034038200c240008404010380310700c02100401c03924000e40d0480ca8020440c9100000304050015820001a00c00d9039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 715295269 1250 715294019 715294039
    0x1f1a0d141f080f030f0d1401120606050108161d120a111009030f0203010f05011502070b09030309040e33010504060e040b070309060f0e0c030c0114031b0d050105 71
    0x8400d82c3d600404030100038640044c49411401c074410001442c0d04030700c505c404034007692902c0b0504441d80003a80007482d400356014800040040c24000c3e20003c1609003000c1c6510304d80b40400c0c5099580e101305040400084c214206880002c00c40305100c03078a8003500c0213804c5140884099600c58100d0416030301d864245082888600c0c01145000300c1c3c0344180d44102501e85141c0e07610710100c502000072a459500d4410f07400000020740b01d114004e1074114407203d00d4a1070714030064284400342d04121805582000000d03403680f0000101c409540302500c0000d041084241c2050809401c2600b40c2807208039500b4500c0e01a0381c0c400207490301610b05011000c9030340c0e5801044115a458890041014041300001d0040752200284139407020040c20080307900c61095031000201c3d021389030204c034102e503a00c1030390400c2c9004006026010340160000d0a003121500000b8240c02850240642c6c0003000100203422070110b4016080105281544039403160101c0a844000d80403d0050900a00a0302 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 715296519 1250 715295269 715295279
    0x108030a1d010207030305032211040b0a0b18010507050d030203070216080604030e04202a0309270a0b13090c05060a1110051f1a0d141f 60
    0x101c003080d605800400c8064a140c0c0c01740c1d038a1300001c0410700b0010141c1c00c0210856100141c4490b5548100701100402c0c0e48001040200c820154a503801b881c0c1031241800501e06420417100b125020724010f86018924000480d4503200d0880024050300a80d00007003401505a00554081c00441e003e070780d10781c59480f0510700143c0360781c840c007050b030390011000c203021a00840304c44811500140c07000c82c019684010284805c020120080303012140011224090440485500460016000c42d40741c940381540c02c1d959a8003c00c800c1c0c912855102d0701c1240c89034900311602c541004815010740961a241c1021001400b41d220f48500400d180d440035805100f540c41011b0b81290f00015200701c080c200014000300342c01101451050040b0202c020034680801c00002000c3c11502c0c40200da01c0c6000005000c0c441d03d402c0c40c1160714031803d1001c2c80b4005100c104a101400e10704191a200c1640c621410090600c03041c85445481022081c4503140040b402c591a60b0841000d03400111a9a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 715297769 1250 715296519 715296557
    0xc0d140c0402220b390a030c0308070f0212030c0403020d060204060e0d03050a0806030f1227150f07080c0f0c091006081308040f06141305012001050108030a 69
    0x10444d54040c00380000154020000c0c8410304615a05014010b8a0107210f40e80a46ca015150041038008c90001c00c02c001c200b6a108000b00d40c0554540341080300707111a002d0280da1110388001c40e01120a0100000d66000084410b1b5401180c0042401041e01910304000300258418050309002804801c644249803c03c2d0307803100301c01541951290b00e491f48010040700c0401c400791500760715000e86080c1550101d4208915007420002031744c1f950340c509c0c1c1044207941004890b80e160300106115405e269880e503c4901841102c1200c6940c00ea0311070704511031211350711889078001c01c0500d021466540741d40c4001891100780302c0050031a100020f1810810201000c1124120400d0003050400d0020754030500020790810201700545070310301c1c0300c4d99500a090304280c200c4020011004010004d0a07407002c0d040409000b0400300c43d144c01001c00d800ca00d04016802a80c5c1403080e046100c00c03861400f88201103039151078200802003541c444172110744941c81500d0400000307205000070040e80b054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 715299019 1250 715297769 715297777
    0x50d140708010504020a12110408011b051207030609060308071a0f0a0b03030c010e010c2d0507020d02031c14040506121e07090f080c0d140c0402220b 66
    0x9494068160f882c00c0700b0840658099500d0a0800c00b104d03410020301106c5e4044c044003605c113814010344a0f03050100c11421544000d030064a101780c602451020160010100c03a000d030f599040e4480a5601d020b0150080c02d116070041c0f08062a20744000140103480707000c1c1c0300e41031150f11804080b07422344403080ea401d82c09a8449541d44150b9010071902d030071960003062000b50260540381008101f181082c21203405030680b010381e0751640c540301d01d80c540c8606480f03c4248040d1740c0c0c980d400707140141c2c004070014014207802030080c0010060155510121a01c6280390b000b401c40c0d880c2d80c481146104621101210341012501001500c411211124250b03000d0b81c401800da00c0c1401040c00c10985012400b40c25000c40103880880881000209081c203032203211240ca580c100c051904280c160300d034690f40d10115040e00002d10b448425a80c030031a505889070071000d030380c14002c0d010030b17111f0800b0000141c40707034000c2c40001c101820030400c200d580c0380f14440b08003600045a55038210707070b16442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 715300269 1250 715299019 715299031
    0xf030c020f070b090a030204230f070f0c020604090e0f19030c0b0a02040f0f1509060c110a150201060503010b040203010b0f0c0a06020403050f1e03040302120c040c050d14 75
    0x210300014803a801402018240c0c2131801801076004a9594012408603610084e00440c1c4a1100084006070100103603c507030400c5528001c0c408a18120310000c004c2c000d105400005c1101c0300014000750b41ea9038065602800b03185038100000315803038072a65501c80e003c180050140c05070710708030208a000b44d0440c6401c2d54068543d035000102664688407113a20003000841580e0b803e01c40400c1c2010003460100c00341034806d401c40101030030002c001c1032041c0454203110400506143c10b20115601801c0e41c140140d0010302081c8840c8907600013110801d1940180c40d00c40152560351039500e505408c00c108450b400c5e00200b061040c5001844141d1009009126201c0b10420807516254403140c010514580300c0c0c000d690960311641c3d903443c05d0f41d0144e801076440b603000b00a0021b000c0011301846100d035103800c01c2d080b201286c10403031035100d014a20002c1d115009860100c1c090100070b02401d408043c0003031040019080c0080c0140643d080310401c50401464448186001500b0b990454002c0e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 715301519 1250 715300269 715300273
    0x13170a02011704031e0216061b080c070f0f0305011a2b021002160503030703050f0c0c040f020a2d030207050c03070609030516052d1009140411070609050703120f030c020f 75
    0xc46521108801d03440350485044500c202c010001d205401d054137040500703900e40d41e400d089031560030202e09488540101042c100d1070f0102c1404070780c3d2088103e411281000034829286400c00001620450601c00c010307410113085800040c0e2a540403c801ca02c00c4d008240c07041140c0c0e2a00d00b816502d0054020003800309030208211612007103620050481c606d81c0604035840c807804100800e003070314840030207000015004580205103c5d00704495101d50100400c8071106186111501d6600c208a40440824964005040030a00906210006884070042c085450b1a541c1700801480c0350a244401e43d4280241c40070782c6440e210314100380742200c1c0010503c04c03040c000c815608000c41043c0c00405560310021281c02955156048902080c40d0b0706d480e401044c40c40d00f16220786104c2d2a4070214455031600ca41403a20000c070100f6107020b40c1d0800c41c00943d880d028640146880380740d800141c1a001748880c4000c0740c03075001c900b045010f50079030340502500d031500000340e039550216040301039a1f03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 715302769 1250 715301519 715301567
    0x501020706050c0706080603120403120807020c09010306020913320f0c030c040819020312210c04030f060f0609050112021203090613170a02011704031e021606 70
    0x4074402c225543d04030100900b27640c40d591b03d00c00744d042c00c0e50080e4800ca4001d03aa101104c030403507800c002419400000da0000d401c01c0c940740000581a40703414000200755039030120f1168810b44902010399030760702c4e0a91041012034620a9801040203604550f00142003e0f200c043c00341002540707015008140b074000d600500d1301c42d45407001d9550401010452080021712000500c00703010030607006c00c0800b01503a0429204140181414a00c128001d80b0a41c5002c1190704c20706464400316011100810b0303010714294031041c215a01c9403080394800307000c21007075411141c10720401c2d521800c030750b550f8041d08000041c1d441c8994416503400344140030704420540b0b02c11000d03040c178400c1c0700b40045c02d03c0140d9142034942400640c00e034110740f05e00d03426644003510611521654624098640350190010010010b1503030009010124909101d1043d0751508081010540100b031122040c80b40000c481c0c8491000c038070b00a540306400d2500760000082040b002441601511a045028469503801446 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 715304019 1250 715302769 715302779
    0xf060906011d07120209130519050c0405060304020303090a060203120a0614040f0f1d1b060a11070b04090515090f1f0b030a0510170d0c03020a060e03040501020706050c07 75
    0x1d0510084e26080072680800c200101617031b070140e2100001d01030710400140c9040c5003500e18040821039907031071801481c05041c130080c1c0c00500240c40840e201240c2c0e440c0d6940c0e4620100c0d00307600940d03142a401c88010700020445a801002828130030440100304c100590342d2602ca10300340c3d0301030b11840000400440031050030341015001202c0c5ea0410520114009482c00c84002c212403243c014440341c0b00c1c10710010001c41034140f1401940c081180400c00710f181e0002c00084062080103008800d110428034002c006c0c090502c54a401030031421420354440f95550040301c042c00040301c00c00d501d0511885441524501000602d001d800c0170700021102d41e480100190b01103100c0304c0c0c420001f411080002a03005030000056100f480009400b00740c40c00c22019a220802c46600300b10041c0c1c003141035022214800042a04810a1520301000b544909082c01d0303040465201015001a0400035034030480c1c80008000d204036030081e400c6440d0b00d981c0d003030200c40740d00460007141c050350014041004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 715305269 1250 715304019 715304027
    0x60b0c101505151e0307030f05160f120203010b07110907020d0305060d230c0d03050d0f02120a0605130204050d0f0303020c06040302061e01030b07031d0f060906011d07 74
    0x41080f4030314006180810040c0d001031046850440007078582000030400c00300c986d00d40110700c2c01c418401004c0c01282440280401f00e450b20501c008100010b20744003072030903441106081100400c5840071903803544c41e10f020005560110004ad00c984030340c40445105810004c04240c80b404103a40588011a43d0707034030407000340c0005407000364000c2415068401041d190490645110350307c0001a0a88400e2890369007400050941240300310078240c448001b04c0c2e0041c040342c0c08400340305000107200c03890120341c100070b00500d02d150341118400b804110a10300c0b00e0b40040305a80c012981c414041c070b00200842c0991190b806850781040094a09000040d000400681c0940c441c1c140581040d4020340303c2484c0601c11201600103034060f1040c4000070510115501000520b13940043d00d035819a00c42082c0c40c60007800060070555205d1034003075800c080200c66000341d00b40748181d904000300840e0150795480c05540101c500d029080002840c400c0f0700e03039480044407006a8420903550b5400041c4c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 715306519 1250 715305269 715305289
    0x6040803090d0c08030d02031815010303080603070f030b25021213270f0504020f010c11101d030606030a0206071b0335030105041509060b0c101505 65
    0x790490f0003070102041c4400e00b400070f1303c0082165100141c40745010541c4150005001c190160140c11078901c21402c40185143c05054a426060048240d250000031a00e4415198081c20014540c5a03010041103802c00d0024001c50b45107904e001d0100c40014a13042940d448491200541c1c040705c82e51201c0c3d003600340500100c8008034000e030301c00d55540020546003880a0398810020031007219203c1c28101c00c1c400c242041c0b200e400104940e01e82079010440340d81282803084d041c030800b012040e08101b82c20201c50320b514000340644200003c039240203030030102c1504043c51f01800c8254460080d04000031424407608005006040050072602407140c02e0744803038402d0781c0700042d10b8035101d241101c044442d0001c41c81940d54500541e00c01c0e003050404401040381c011400d03060399080103400e0444040c0c3c0d0542d001107400040400103680c203602080b0b80c46d0f1052030b0352400c00800003104452100a0031090494006503102202042d1002c2c007210011100d48074250345a00080c019810640509 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 715307769 1250 715306519 715306523
    0x60105150c0601120c14010f051c0e010e24040201030c020f060103030f03050f10030b09070306091119060206010b0d0f02070b01060e01030b030c060a14210606040803090d 75
    0x18601d02100d003003070141010000d0f0007281c0c426070188a40ca0030822000c0e030010082c000c1ca180300311401c03540f0000031b108220b41c1d100c0d2000c11201045140f203010107407000c0020180d40302d00400078000016020b074040c20403c00780c66843d008401c1800100c094000180d41420146140e450f415982c81e0b00540007080c411004c5021842071600c80c7c44600420407005005e0b40c0651220800f00e568820010290380d002010350459540810500c90503000c954881d105480e40700381000f47c40e5a40c00041483d24800f58001b0f00102e040c20594800d004141005541800c0c00342c50040310000b0003100c40c07404401922890380141e000400401030380349860084c4c4402d410204010802c15184008001660000c06051b213940c1d020720010001586c21008120b44180c0c00e08081c07041072558000251148000318500f80a00e40002d00314a00900c1010203042c100c072114034240c1c4804c11501c021b2203600110242141c500d0150000c8ce8452a00405807400c840c9800015890724681030244444d21010b00d0007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 715309019 1250 715307769 715307809
    0x140105180414150708011505040506090409060e100f0b010201020f0304060905150a020a0e030601050d030c380c0f0a0c170409020d0516050919090518010b010908060105 74
    0x11800802c12600b80403400f814a40d912070082e541081e00c4090a59100d0900300b003230010402c820003060b02c41c00e09039040360004641c00640d42c101801d10b00080e0620300400a500d01a00343c0c0900780214030780c88402c2200114404200c4001408016400c034031500300880343d00d00080c4000f8001454907000314010a100b2000d892601d03103060300c50794007d80300b5a43c02c1d00098000c2100780002d58440c02e81250072404034000c04981d49402e0104400c008501d0014042140c0610f008042c404011050540d1404140722250014003410701c5c449a03042e1078122114000041c008034400004513419609001034070303d4200d1034482c42c27807416194083c00c114111900c440c5002e4801e01d049120000d007000746030100000d44d6400c07201108104940004002d0081c051400c0614140607900c0b0040e940344074003d031030784404208010000c43d0b25141507801401440c2c100301c1003080040d94410745401c00e212100083c0400440701e0300665111312036000d611065030241004100506e0045450301004d950703001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 715310269 1250 715309019 715309033
    0xe1504050402030f061c0b130c080307060c110106030b151f050a0905031603060518010e0a0201121a040203071202131a040303020d21090501140105180414 68
    0x1c9010303a0030031622440355035008010040c0314142000f044283c0c14941c0000041100c8540c0c4426002c00007401307a0000b03c030310619890800421f04402405400d08404680c1c03140c0301403903c50054201640740d03900060b045182c00f00301c14814095482680e501048a14484d66031641030540500d00b00c4005901068100220780850540d442e08503040026913142c030303994150343c0300103082c1410940c0410302907031001e856042035070540b88004003980d42c00b80e404039141d01c8504d0200d080c010040341151140d441d10123801c16003400004d15040c1d2034400e80741c030115003000e030105a017142ca10913240303000720013160034440c5103203803ea00842e804046810805840384c0c1c45d80c1501e0883e041404207180502d0710040074006d400d440302a8031100c11840020390302d42419035a00a4881c90880d00f0720007480340310050031911803c0320800d42c41d007810110b420070007081c00c0d007400ca000c0c210f5080010400d013854000440c00b810410046110303861100b00500294035150b130b415001c032034946d00c2c158040c001c000e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 715311519 1250 715310269 715310279
    0x41410031103040f140c031b0d05030a0c0605010b09010c0308061306080705150c0a140a0b0a050f0c090a2d06020f16031a130c090c0e0d02010e1504 65
    0xc0060b42c021401085618140d0006103009061049aa185025258000c82c00440170342c1d0000b1b101414003030110020002d17140b01c00041400382040c0e0318001d14501002c664100d00135400180604101d01a0314248581d90740c500f4036171007910031050341c0790010312076000e010f002c240102e4949801c180040c1c2034040c0618100e50a50407070341940c0007642942c2190b40200200d1400001003142d002d41c06050500e0b180c030790105169107602081c402001c10342c104100c42000b20042c440e040c881a00505070440c58980280c299000f03203c111540201c8008800c04070b080306001100b95078a400c1c4c0503290300700240c18a01c0405101c00e1010700355440c0140b0725001c0405400c54070200000b4203140c1c0007000b0b0710419015442c141068401e046034040942e4608201042030155005545444603120080d180c40381c2e82c1115014006000203855469413900005035824a54080c107005615a80c81a14401ca41820041c1c0c640c12500042d00103480c258107000e143c0b03001c61290418107800964146441c1e07482d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 715312769 1250 715311519 715311551
    0xf0915010f0905010f0608130305070b070302070303050f06012c100e2d0d0201110d021f110d32100e042414010f0305010e0304141003 59
    0xd0704001d0720744001100801004645000c1c80d4003400200384044030007810b01000900061006088821032201c01c111801030600440032100c14a400c000d508c20f07103181c0301300c000c0e010358003140c412030001c2c0c41e10002030115412034290314020070059440c00c84850010312054802841180d41110074603c3c1c0d202c0c0041541d0340e810313a05c10107034a91070b15981000620104201d288a80d10440b005440103102c018200b44845158482003500702d40051340c0c40342034001210816a0319000d00b050384560307034a056a0701e0300010400b0241e13110303079224821520005101d42c155001001c52074070b02641801494443c0c903450700031202c1a100080078000640c034894041c400180f2401c000a031151868090100c00d00307009402102514200a031b42c505800d245c0d42d018212442c0f400c5258049801e92348150340c0681c0c81d0058000301001c074018006550311840c078000105480d100480701d5605c0d1400c0300392846000b100740c80848030340b9112041c14152060520415805480c0300c0030070183e45406d949a44428 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 715314019 1250 715312769 715312771
    0x310021e0c0a230a03050d02040b0d050402030c041404021530070306080a030c030315030b16020f190c0e0f0403030c0905130f060806010e09060708040305030f0915 72
    0x10781d2004044501ca6800e0400c3d5200d18002c0e041e20b105020601d001e07a840300060303000ea0040d8585010744d40c0d00e0b4445200790080c041d9402c60b2215280000d0740c80d1455031141c00481c000c030700850a0340c2c501415101080b04030707990b000c40c01c41040000d10001d005403525405120f5440e40d03010718240f0309181e2180400c40f103481410310410341020a0080000000b041040590000762401d04100d00c50900d80c6440d0b913010178410082c00c2101c00c0c140c0d1020544203402c14a80d40207442d450510160702d0745414459090222604499984128a85841c2500c0001c01990046900c00900b15210b00500322291810020744145c030611a0840700258031004e91a91621481e904414050780381050301d0010141c0307540300c00720400c010b181e22040c4015541c200c4500c02c5400c000070001002900124142c0242096a0081c41b55000b0b6600024190f000501094424580002545c200d41d49d064011744070140142c8020380040c40502c00140f8000d032034140640c12610201c2261000807a5201000741e040e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 715315269 1250 715314019 715314037
    0x9050f060f0103050f0a03140a0e060a391202012901170403090b0c1908121b04030b060d050d111e0a03050708070b1f140310021e 57
    0x749400042040c01030900c034001d0b404000c5000380c100c910091710300074005043e400070020b4241d400244076480d00d0141005022030030000d4401c40c1c5400080401414100440c80e1800d41d00300401c0c48827043c20300c000d140e42180c1e51034540311444800c0e030f03032100000e0402c3d80211130190745d40c4d2042003100b02e411001e114170b08940b029440c0518420f013400101512805007207122015450028840000d81002540c0c00303a035410318645441d1030301c0a1180d440c055070b03000d20140000224664109101e42000185464110305540c11642d4070f4485c9002d00d10300a495040403034050034001840056100d89002e50020030080441c0341c80c240303e071074460422218008540204612a80004c0c01c0041402103051410250b80710340f013400350b192003454446402a0303000b0100100051103508104241007034800040c2c12440b06c20841c5491400c8000340307212801145034404983c6000036580c101450070626190000d0098030052034244036a2010b5003040360504015001180d0843c5210710301e0340a012049 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 715316519 1250 715315269 715315291
    0x70c0e01030c0801021c0c05070b01151116060c0c05041e0c170f04020103021209060a060b0c1905011d1b0a080715030b0a090e1203100909050f06 64
    0xd451450701c20314025650b030103044164018000350f08400e082d0610150403040043e00814516180d074002c9496200e0130000403d18040c08001103206010204150042011600c611050040d50341519948810180c00c80709000c2090109001340740c8500212100c1c9845400d528902c0c0e5200d90029080c0c8404c13041804408880000444110405000300d1200c034009003401147d41a80440f0210403c0004200c1420302410501160840e4070982c1124205400c808081442d82000e0f0300f10781e16600d00341e41c141c0c0c80c50304107000804ca0610300422030740c01c452034100501e0a0400751082c132011842d401000e4690703541c2d50340d0410000c8500c80014500c03002240c00707414401030341400c00b000100c01e40080e600620f281c41c410b105400c40014100d05680c1035a603a20900018140300b18094030310140665080200d034000004e17a050a41c0141c010f07101f1107000d41c0e12800c0f500200c9003181c081142c031400941e41c04030702080020015072041e0340046c010000c2e202c989030070841540c5082c00075103a1014003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 715317769 1250 715316519 715316521
    0xf070807030201050612030a0302092b051c1215031506051e01210612030e030d030c0516050c030d0507150509060a05060d05060103080c0c040204031511070c0e 70
    0x15420b01c200c940c42070007200c0700250484490301c09a908e0040c9003011083c0340d0b00040400403903990348010744005d400710075851000e048104900042c8403102030120f400c1e1140d003010081160000a03820b0030f105040d0741e00d107200c5410441c032074081c0035414044c0300d500b4095403020000c56940e040c2c098880199000c040b8200e85403c05004d40401400075031a42420415240245682c1c48160044406450f103036555070100002580c400802d01941711241a002c032070b00d54820150401100c00d00080200c00b5038407030840b410f005070251000c0d000b442000404c200b10300384404070100e004082c40713030007001203d040000040c04245405107240402012400c08078074102000078001660070080750207241031021341000c4e6443c541d903840c0505000d1010341c82c2d80004140c0c0e02c40504605c84950010100c8050307507520b0a280b04e2540c040180c030b2204e0b00801071140028141802107400b00c9510001400078400500c1e15040241904107030400c060b00c00704009004180c60302d030b10b0005000400102049 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 715319019 1250 715317769 715317773
    0xa0b07110607020f0f0c0d0b181f05060405040c0e1f24021501030206030c0d0f1e0c0e060304061b090e0115120504030e100804020f0609150c030f070807 67
    0x742102080d416817496001c0321032401a61980081d10150903400340e0358459503102c25071600c0c0b40c4a10482504000c0c840c0c8094030115101d6610340000c0340d01c40c42d5007005075440d4581800305a5800703e5002c2c0800310714210410080c2c5080311040c0c2d03ca41414040c0400c4034221030b401500204683c4000c4468210313034080100360003941e100c91340502581c0001d001c0c8050b40c45236101d21100501c000380c81454088005111550003000315004d48000321020003600140060000043c55000499124000c8885404d500e41e03101e44034001140d2029110004000e0307100040000986c0000c1003124a2911035441e00f0048070b0b44150103d420503940c49103601305091580e03102103803405a116460480c82000301030381154204041128410350203c2c081000d0341e4608090b1608100036030360941041e503007508486a164408242030190f4400c88852180344203407c2004024003841281648c0080c0f4080c1c18066001d20100500c03400020200741e90074142c084a110905800005099504003000103410003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 715320269 1250 715319019 715319023
    0x806010f090207170a02030f0a05071103070810091109010f03060e03040e07180e0a02041e031a37050906040c0618050604150f110a0b07110607020f 65
    0x50710340c0c01011420070a1903101d01c0740b0071207100602c030f5103480005501031045200340300300c1d940081e00e000503507a12030924500038042d61047c80203072401407030b00c0607030641da01c4d022502c8401c40d8009001400024203807071074a401002910030845aa1148524005643d1a1141710600030850101e045c54400c3c6581080420340c1c20b91141643c42d80c00c100001d10408075410441504a0814030704001c034802c060300f408108040e40d42100031012080e004000b0610960380080c0f007910090101c04014408040d06010007031039500004000c0c24190301d0248200c448080810707030299001d1040b154007001c0e0314031403500c4070114041440c46002525118441d0b0024007030316030030514002c010b000510b0705888905034040b140c01250b080024444000030102c0142c480c0201810300248110356450703969100c00d4650b2014500c41010520240000000d18019501000440e4a07440904000b22556840340300c0c3d03203002010001030040341028240781070410440b15105030666001020340c10444c6a0ba00c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 715321519 1250 715320269 715320299
    0x3140d020f06040f051e06150d0b0a1e050c090a0e04170f091203070b01060c110f040f0c0906232a1506040b040b0303031b090a080601 59
    0x415584101c0c98920000c1c8002081544550800b00c41d80c00c0c007145180c1142407101140d1034400202d200e007207450b1014800715805018811400f01c04030343c0400001031000d480c05421015000c00300c0c0e000040c00249045d040104001d070038043d4132001e2840e8503483c1d4102c44007524100120140403803a00d00e54140294072a0150001001542c0c1ca441c1a949032030b200c550014824040d1000860020804501207041d2080c20300014007004c1004444000c86949401618054842402d03c2c00001340650145d111000074640014070000c02c84c00600c1804a50307010007134041e403c1136440c072180c1c0a046282c4100c1c00721002603513851400e5440c055000b4500301100c0c40c24000540c41c0ca140401d500d06050441e40114107200c0540d000640400401c256005e03103d510261501aa00c0b084040c0d9a04000341c1c1e202e0202160100483c0581e602480100c49550b07d8958050b4802c0003c03503252407044c1401400e000c0c540b824107180c031095101190300788174154003c051990040b8014409038802010741 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 715322769 1250 715321519 715321543
    0x90a050612041101020f070e0603060117030301030f0503070c090b030d0801150c1403070804061803021c150f0b0405090a0206030105010f022a091b091c0605010314 72
    0x258203000d290008414126006003000705410b250b1110540365900034020740e02c2840c046d1081d24542680c4a41302017000d00b0031103201d4864082c507400464141c0b00160190103404800300103504581c25540c2d210001c3c0f04940040da580c0c031041c003600d8000381408003818042c1402e13079008103181d000103051602d0842160300e1141070028110040c000c00c00d5070b411400c620812480c0c04c27007100c81d19040c260a41c030175000f90cd04650000246000038000c20070300500c201c800913a00c4507298007180b40b034440050400c3c00001d51200e43c00103803107200c800d1072100181081c0100310313407a518640c417400314048940e0840440c118a0b00e0341400d000a00d03086c801d00e41d1100380d810140c440712010781e00045041c031050140324140150382d058130071002c4c82004a41c01c840102c0324198940850113241c8a000070110001b2481902c41400180c40408041001145d00760400c0209060151101c100a20071040441095a481c3c3c0c404000c8040307041806014001c5004103074983e90340c0159023400303050008010003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 715324019 1250 715322769 715322779
    0xa110601060507150b15070219060c02010906020106030c30140106080a021302301b07030c03050912120a0f0c05030a0c150203042012031803010b06030903090a05 71
    0x12400b6454984031814200ca41c141c41c0d1f0381d80e24661001950007031a41022546c282c40180c00440c0c1150041c501c615041d000b43c0f00d9004a0390b035510221300384c8140d030200504525007454200400020003080d07444034000b41202100c1000300d45c1240041602201082d00c10b018101e5003103500301c100b8820007018109100151800741625008545489050002e0640c2550b000503140003142d8034816000c0e900c0c0c2c120040a40301e01126001004e68001903074102c0c0e2000d04070664007090102c810480f824554191142920b58000c1d4900745c0701a040700b8503e07038100290024102100704140b282c00d044017800d0f8804c584458003840c004049500014098040c02094812000842c02c0002641d52000c01850680007200061901c003600018034030f01604164000b00920003041402405d400d5000c44511510000c850924200002c0894907900c0c1e200c1608100015412040d150180c0d8200c1d00c00940042082e00b10500071800030780c0f0454200c1100c1e000894607180c00c1ca050b8032480010941100c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 715325269 1250 715324019 715324031
    0xf0b07020d08011406040806010e04110f010818160303030e0607030204060518060409020301032019060311090a081f090309051e030313090509010612080a11060106050715 75
    0xa010b04103000602641400ca0224881480c10741e5a4400701c4028169002c1950800d5960301ca43c0440140e040d6030481c1c201031401c0d058992070a1141d00140562016500c04241e41c0f2185108000c079419107141482c1781c0207000001c10b018400010000003140300f590006030014020800c10b040440143c03130302003014010041041b0b5694800d00381e8032440b09040c50001584515400074400b0303c1564081901c10707001000010900450041020a07070303034180340d42c40c280c541c48020080040100c07915020341e07003546407090180911941c0000b407550b04100c190740c600b80301000000d0045c002c0358050407295101d07085001021081c96600b00f0000b42c50b85041c4075a5041d80ea014150008c24000e9a00601940c09003041c99243c2c0e004194103010090207481d40c03444061650803a0440138010180d8081c1014041203ca101c1480f900f4200c405126507102c00a80d070f0b030b40c1c03010350343c1c0304114520800c590403100c245a100d09119460013001691030382ca0342e45401d480c11184401e0b105040503d0750b07203842 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 715326519 1250 715325269 715325293
    0x42a1d0406050303040b0309010608011506120501240918050402150f0318100603030f030b06030420130f0504020f010c0c0e0a090501020c01020702090f13020105070204090f0f0b0702 80
    0x805d80c0c05403084580056265900c500314070b401018254000c00607503007050710304542019200070580503100b250740d948001d2100c04001c8010f0b03d00a20400c1c403801c0d031110884210410b54100e5070f00702c01d038510b0300d42340c07040d55a008a21803001c0e070f03085140c10039501c1e0180021464403240040990500810590500e80c0c0204c0600032400020900c3d900301140c02c1c0c400203d09401d0180c520810f0311014108021a00e80c01c0040a071705441c0d00000210b0b25000c809440c51402d00c040d203100790b40c0030f01c18212491542e154034000d40301d42e0b000300303402025844440d514000b09000d0120580320340304000a0901d020b00401ca00b01c0e4100120a041c0000b000200340890a40743c1c03060191601010a0703016509d80418150007000030860103411540301049400c031114044d0010111180200c400310f0080d01c44209180120348142c4110120641c1c10b203e080040d400345c0064412a80002e00c0003640c4003107520b480001d00e13040748d8221810040c40c2190301c02c21007000c1343c807a00101c0c0c80c4003c0c00004500c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 715327769 1250 715326519 715326523
    0xc070806070f1b120c06240b250b151e101202040b0409060501020d0c06090218010b0720011b0606080d08151509042a1d04060503 57
    0x111400c070b8200f01d1080392a045040c801000b661007940d010212021000502c14001c003074800c641d00071a201ca042101d0804032420041a940480d443c51060981d5185024181041680880b0000d64200030340c5400604111040c0d6074685014000c0100c20b45030319213440340707003141811242c0461190300c12401c0b01d40b10b4601c2c0c0100d0ba0f181c102c155140790401255810039500c903921070058100c15400020003048086001c0041d20841d60301110600c0090b45810040ea107541d1020714520001d1607a151450104071207030010510540050324000d403449106489003460182600f207400351140006002c0304001c900e01200c0c050b8107001040303141c6d4584240c002004003d1054252680d0f05481d0a48801d10403c2d9200c04020710340542200c0c0030000ea00c6000d008480c048410200c148070000c400d44143c1402405001031156514070503250205030b20411000b40408142603500c1c0901e49a0240c12180c00311801107101405d45410501003100b00800c0700e404840c2d504103010f6414a5010400c90b100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 715329019 1250 715327769 715327787
    0x60f0306050607170a11160807050901062a210215090304090e0c06040603090309120c0b0307030e070305010518011806020708210a0515010c0204020901140d020c07080607 75
    0x4281c0c0e00d5440b00001c000301c07111001400c82d009180152807031800c01f41900380000d01102c00507800d8420450b030b1641003000d607280074440d0030040351050501d01c240981e4903c0070000340502c1107050501c140551202003042400301c115a490b0740044030050302085d0100411003240241240d020340910301500626100c0c040c501c29801c455032a03000d565040c1c413003484800c404001c0600101d0300c0b5551448020060f10522100303a02151340d00b24042007040448c5481d4801c140c01002091640e4030301201c0b0655540000e1000d070405641c2c01d544107a201e401d109080040d400307100041a5400d012541e034151840f80700d22040280e1520422a18241c00924001010343d08107200585038007070b40c00d04004510480c04842a0480b040c014005e9100c044445540240c05040b810421552066001c035181c011700c0d00714501141c04501c0b072000501d003076001011402818903084960007095601c02070142c0007500b544940c2500800c0c9554000810050800180316400081045040c80040600700c904 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 715330269 1250 715329019 715329053
    0x1201080d022104030b040c031112030307140702061305010206180601120309080609061b07020d020d0c090213150302131e0b041206150501020d1d0307060f0306050607 73
    0x70040c1d07200200b5840a4500a5070004c50301e03202c41c07500349407030b100c03001c0107000c2103c0303000c40020111654180011411040490070004620710345425105a0b040c504102c000300e2100020803510700103881d585d01a110b40e10004100c0c0203a5820035002900308400144190a100614801c2946030710300003401d00c0c110307066151181d00b50002401d04803100c1800e60045500d602c00c54082c0000040002411407165076094000e10107502c096925014600c00c0d40b03000307540404584291300c05403030b018044c2f03103580e4450384011444981e5001020144d8000201040d509108103504202e00c00c0d03d07032040850b118181c6821071802820070503000c03006c00140112108000d086083c0303c0035064080c0c1c0c0f84080c1400110031900d0f0b950716555280d03822030760358048666a0400003455a052000b4a811094960580107400d00e8032001e0021a0008056001a500b521010145001d00d407001e100c90400360000380d8545140081c3c000025040e540c40794043c5000380c0c01007181e00c0120743c0b03001c24000900c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 715331519 1250 715330269 715330303
    0x1707030b060301020403081b100204030b010b0307030e06091b03030f041e0b070b0105010e0915040207050a122c01080601050918010f150503011404090c030c0602031201080d02 77
    0x2454180c0883c1c028000c030b810003403100c3c1d00002c0041c0c406080c03023484010341d01c3c00c804981c1c64642d044142c0060740240d1000600c1800c0309001407110403076a0028503442225031400040302c0b005041c041c0e150402c183d4001c40380342c01808a010150b078095070000c4119009030015440d010700b0110f440001e200d507104e2603903c0c10310100000c0300c4001c1800f10100600a2041a0340c80d4809420244101c001c280f0805010400034810310300103007440d066051040082e040d00307114403211034052001940c0287c008840a0107948490740014141509804d580101c641d500491f8032201140300c2d100d4a41c072a172810080100a10005941e80d0000100743e00c10000c7ca0125124a036030808240b5a600916a0f5040d010542002103100f031003007042d074000c0720502e80303214100740d118034802e603401d110a002c1e1090310030304e20941c1d0300c4e6400c090b0842d540041c4120b60725680d05aa0b5102c005070101c40350886001a0000a422031110782038541c2c07a40036220716030250100c0400080d002c1e42c0c80070b1080000e00a8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 715332769 1250 715331519 715331521
    0x1e060f010c02130e010c080109090210120e010f3806071a16020d0306080a1b0f060c1214030601080a02190908070e04172d131707030b 59
    0x544407298480d2449880c0300c0c081c0415403100816074046c0c00c002d00e034440029824000051000300340d001d149000c94019042550200078410110303000c0102e8003111182a447d035011040351002440b900c0039090300c501d030001d1a4900043d000c0c16848a0420085c5035814603400c5c0d80c00070010b150140b640c00c1007181c850344e403113000e8540203584500b907a11905400910004028110700c440d17440181c0000d4035401e84e01268100b00f0250f08866090240c0c02c00b5600548001c80060b00d42d061452445500703238500c09102c0e40c1c4274140035100100e07801c11000212003502c0c80080064161034958074000b10f0914661452010300c1b004210700004080c24100100d950120300918120783c101c0c2c0f100c0d0307a400b820481b0f00028080c0901101011b2142d0746203485511400500c2104859480340919071000a08140300140c0302c035541c40c3d030000005801c0b00d00c10741f0b100040404081c0b012050460200e06190744071940c0c060b440d41e403507080e07922264940c1c80941000d05815070200c1c1900c1900e9122550000c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 715334019 1250 715332769 715332773
    0x1b15030c030a0e0a3801210c1a0a090b0906030a050612010c090e0f0c03040f1b3809040c0c020d081b0106050a1202040f06030b1e060f010c 61
    0x5004900c3d20b000c0c0484038010058503a0f1101c4c002003080007595400c0e005c114807108800c020ba680d03001d101c0c0000d61288800c0325200c2d9041103403000f035400e000d0708000d8074058a81d1025941c0346010055140088070009134005855081640d103402450910206420f0007802c5020914921005141005956441c0006603841e5100808941c840c00140000c00c43c40410190181c480380a90040485400060001401070a0030441c4181314840c411040d90460301c8a40c0c81168402d5400c000701c410041084d44842100745151055000744000442026140340c54050401050134450b07a001608204440d07088512843c0c20031104482000c1e81d00041c81400c0c614115522411728000a600000402c1a50240b10031038000e80180c4030901c2240b543d440000e80c50034221000c0e0b101d1150441043c0f14204010864250a141c00358006400420840030014031a800c60f0400d03041215040c1c0c00806100109803036201ca60781da10300c40d840045a030304200f80068010000c0100c600e040264000038442 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 715335269 1250 715334019 715334023
    0x7090315180f060203011e050a0303080907030605070801050a080606030a0209151e09131a040c12051608030a05090d030302041a03091501030b0a0b121b15030c030a0e 73
    0x868070307070880306081000105103801c5010b54828402c10080202c0144013802c01a000b00200c012124001d00d02001d481c51070390f00351050480144045014000c15400001040c04c0d40182c0307215243c0713503941034641d604160811a400590360040179459002000b00300854600003413040000f5011155440d5503603410000b4002d0a0039820300c0c0703810024804047c660201400c010a4001e881120200801e40e10b01031551482a03c0f018040d00b0044070900303005260388480034450700309020b440d581c0b050300d07241c420408402c00c031024216201c0c1d200c054140d0f500944810450080c09002c0c010354584100303414010524004c0311241d0b84a480c0f02000001018025411200245400c109024550a550340005440d4004655040d400d0281c03041201103100c04045142c180d03540b0031100b04c10b0b0788130341010400800c5218039580e0001107040070380c190410104601444003181c80411405424410140509500c4d003000e80c0424080134803d00070059101400d50340e009107482c10000361450004100c40c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 715336519 1250 715335269 715335311
    0xd0509010e01060b0403022112280e041410261203010e07210209030703020a090e0114130807050102090405151c121b0602190807090315 60
    0x1000562800600142e4420a540901708407802141c5020b00d880c0801aa0120400080c900045a03040072540501d01030303081c400751201d4000c0071075440350060b0101d4010003800221440700080b6a8140c10703d4140d10f0b0030b000740070b20003c000c400050380f824075041e00f080c81c00040c0220251041c8454003108004884482541641000360884400c45007851035115503a0081c021000c1c12a0024000746685014031080a600b03809004003050022a80d0340c0035000750400e41101c4e80c107020b581e00000240e604e520801024100001d4005465007003850301e182100c100382402c2a01a141e001009001c0e0140e240c1401d0b043e410401c040e540720028070380240203114880722158050301e807105000d140c105622549084000907105215104072008503248503950064004002c800b00000800c521449408a080b12140345081d44209260039030700c180c02d076000180a8800e0340d80c1811200b03c407661044e030141d0480c5c0030382000300f803d03815074840c66454405280440666511144e614940320201c1d9918 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 715337769 1250 715336519 715336541
    0xb03010b031f02221a07020a05040f020c010617010c0c0804050909190c0317090a09020a05070f06090308010b12150d050a030201090b01060e0904061a030a120f0807050d050901 77
    0x200f0036040450350100d0059138901555076005440201c0c1e10310b010010f021140c280d03400800c42a882480c0808000103080741080d0303604125001c0c0810181200c0034042d120141c0b000b8800c3d2060244045459401c54400100840802205200100c0400c407102d00325800c1e41d2042d00da0545964584015a01c1c004880c3d00b50441400034110441c248800c540300c1c4410340b48283d030382402d00c02c03840d00c14503c80d00501e40541d906c0408500104403500980c1d00030f145a0029040050910400381c565100c2005400d000341c1e0303480e4861200c2c604250340b03d485140940f80318000030b82040340d41410f980000c00011700065076069402c166900e15660f48400d0b810b5030740d101d4120350302d0201074031303009000c0d01c901d6004403a021001c0c400071449a004507804951010081c1a00c540d036030311900ca80024048078403803130301ca000600070b07005240d440070720030081014065040350f1000b402403400200741a042d4001c40041004030707824084030a41c0324003107075105800c10b40045210703150030320a28011302c801408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 715339019 1250 715337769 715337797
    0x509070812070510110d0b0a180f060b0a0f0507061503080c06010812070816061b020706020307020f1014030109060f0902040e0c031b070c08010b03010b031f02 70
    0x80036600c410140e0080101e14420f006890340702c010384000e070083d104480c265007490281400f803020600f603603900c00c075460b003001000391000a0399441c02c01d0b450882140507010311a151840f004400c104da0061400400c0c4e2030601928007504414010003a03c058a1041d0420000017400c0301800850b0f00004440040d50718400401c5650f8036210140380e000c3d88501c4c0142c011035000040300200450842031145800e01064903008482d0f0b50010f40d940041007a0180324418840480419010320031203110344800c1c0d0f1000c0c1031501e5404044c1ca45036455110000310340c001c101c3c604c01610390f410241d24a070001e8540d449040a0001c040d154030b03402a5003921054004400050301840d01e0304280708950180d02400e00c119107031041703103003640720f540070780c581504400c00420315800c0c4000040d50700550f0a0001041c80d14080030500d41544120426070b480d0101031020b0082803428481c5080c00031003203000304551752464001c69100d5441002807903502900400103210380790030350115a034405852070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 715340269 1250 715339019 715339033
    0x3040e010b0a0215010312050c01322202040f0f1b03150b040605160624170c102105011d01030c0902090f190311030a080d05090708 58
    0x41d031a081500440d00703510052085405281101320401202c43c140e03500031780d94101009040c07000359144c3d0700402a00413650360300e01e903018001c0c0c0f103401c8041c20b040800c098070800102282400860141c00390001030b5408d241c010a580d2103240c550404075031681903502048961580c0c1400e002040b02d580042c00503410a03a84260020004071a42000c2d60b01e80c40c2000101086a1100740025a5006424038810100000e000313041c041c0016003282c0c90400c000c0004900e00c1e42c3d81005981d41001038030040507100440c02141c02000c0c1e11007010b4460340b51110b01d034907261001c10380e1721500b1140107800f81d515090811005481504031059076606e40360300c019100f0401d041c940c0100070034030840c031821821140c4841c041801038485412250800503000c850350604074814000d600c145007140d03004a007030440780ca0f0343c0c0f60342c21940704860602200081040c42e500f440710a14949001c4075110b608181c00d6500001d4a8806a410030075443c8030014850780c07401005031612900d5000f544403407040d030f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 715341519 1250 715340269 715340279
    0x2913020c16150c03020334240902031b0f04060b0c0f0a0b150a03021f09090b0a030f020f0604151206051008073e0607050708030903040e01 61
    0x70a003004641c841260407140360300c440d00c1122003641c014802401600300704103e06074840000324400709804004807008040c14080e00030305d1181a010300c00c80b140780b00c0c0c4803400c100110014a02107400300b074280a0010b45041e900083e154505000907004246442c010050076460710b80c4240c4c00c40e900034004002094913011340da0010b41041f42c4001c028410480114484a00800c0f100c003107581c800402446502c82041481d04007420069090300300301802070000c00b50f51600120320450b040042d6006451850200062180c50b06800540c091420038610a9443c0c8805010703008a0750008280031a410440c80029100d14124084070f6101c3c00105000c552403900d80d01c90345000401d51211104c003c5c92000c0321050342e92038801e096019000104143c40ca501035500c0a50280d40c6142c903030718102030740c0c81c1100325401310942c10f401e08820000700e07aa54080e0010491032904610028070151910001c001c06a00c281c143c003c246185c003002050307001c0d40400544014048400200c0a5580c450b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 715342769 1250 715341519 715341553
    0xc06030a0e061b070b070201020d050f18060405030301181d060613050609010b21040c081e06070c0510050702060a060902090a050f060c07080609012913020c 69
    0x1801c49581c051007000c03a900100d03030311040800018810a20303003820b0468413040c5000300c000342044c0c103654003007005118498282c8240c510584000340200f0060400e5925042010fa0a45c11b0400c3d651100c010700c400329000105482c111051450960b03042d10900b00800003070a03036001c0c60b0043c40b03407814403d40b0704c4601080712440f4040c15650150020024940c6d4416910103a03012504400088014000510040003e0040c120303015220000242824081103694904440550303c5144d0f0140a010700c076418010300464030001c6400981840300008466114500604603a0900000a80c0f9000f040300c1401049010000c0d080200442e00d050b60003e52280800c4405903180c5d40703000d0001c0788045030752090b103450200c003034070301c140c00c60401050241c060a80f10807594480001c0c805811700c403c1c01c200c00f8001c2d15203980030302000d040818041d8251034415100003041805400485000d80c02080202100c1e541222000309058208200c2d100911446d52103110302d018400c02c44160b4046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 715344019 1250 715342769 715342781
    0xc13050412020a080d020f070807060e010b01030908180312040605091f0c060b01110709090b09010902010c030c02130c0f090602060714030612070e1501180608090c06030a 75
    0x2080701c01e815044201c0100d03181d205980c2e000f4110f50b4103100901821701c850340901428500c40d0041454124980c070303200d0182c4c200d5103007110000e0703d402d6007108440c028015100141e10a00381800b841060b80d441500c00e000d444d5980003100100c80aa20091760100300c06294040008043d03039613281c464400502c10380c002400303a4014881c2418002e042e003500516000300c4115544d075400040d850795508405085440700d1681000008042c64032601340078880000241030802c0002440a01d500d000c0d220604000c1c464085a4500411a00540d8000c5c800c0304003103070300d4a40109102400d10000d0084651a043c0c001d90614080c1101002a00035020070b40343e0110391075060100c0e654000881c0d0350041140e14000140c0c07a25040c40003107100802031030f0040001450460329500f05142c0c00c1c42d0000591201100d108070300140415000d01d5100301c00581d0f400e28042c071107200f00320300101040000744120010820060002130400c1d006000c40c00c605180200600c3d0340c0c0c10314079440340c06458 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 715345269 1250 715344019 715344023
    0x512041a09030a030b0a0506030f0a2a082409180303150f030610061404090c020706080a0203010b190309050f071503021305041104031212050703020309060f06030c130504 75
    0x2c80c0c17000100251400001e504100e0380300030303c0301d440c59440c00794a0140c441c018200d403000988034500b2504602030400c2c000c10600310a1340b844044441d002e002011000007401c0d0a49242c7c5114548003490310440510910000c151041c627004d8032048411130100300d819001101d90700001c01404040c107503000700160703400803c40c0e188061380e19101c10036440320016a0800c0e41040c090313504000072030281c0c1603480f01d42c02c0384c0141402c0642d500035a509482040c2110b80041c0c01c40700e02440010303004403a941d0081c0c0c80401c00c50540d030621000c2942445215440610001c1c0842c100d0043c0744070f0b07000490f2180e44070b81aa407101140c0c0c407840f5981c1c11180129040c52500c032405030010b0784a07200383c6580390000a80800c0241c41d00092000820426010403041c0d0010031003c0b0106c0c0a1021036146004950340b4030103050480311a0000b00e03100030708002c007010b0042080c13240c108070004074950800c02e485c124049a032504400646001e08011500b40c100724000300f030300c080180307030340c8214403442c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 715346519 1250 715345269 715345271
    0x30c0c1d0a05071b0204050c0906070b1b0c0703020910030614061e2b0c0b03270d111c020c0301140405031603120f0b01120204060512041a09030a03 65
    0x1845144081e40c410010344c0e10403c00742e07142200da4001d4602900419001301000030058500304200700401d19507440f00348182d4481e00386d0818000d0a80d854500d8540d08184010780750b0509600454050311490b40307200191203a004d0901040404c440e02001030000e60340484d003080300d0340340f01e220310410000481d82e942c07240d10084e071081c0c0c0c455444280c014031800c00a000042c00308a600c0d0400240714104d02041d55070710000e141d400021000c900d000060240602c2c061389a141089202c16100c02907600c030071038050701003250007140000160102e108000ca0a002e02c01002082010b46040c4a092110300200240112121500e80210b0300f0454000700394001d1200312160884000c9040c419a80107005a000f00001003126072480e04011003603219207488540010880c190400361044111034000d596554a03407034513035680000001c000072003911019400d103032030550080d1113400380042e0521065400030000d0100610f1780c5048200740e2000300300148a041060b6170b00d949403c02c4c21090007007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 715347769 1250 715346519 715346521
    0x7030b040f090515070912080313050d180506071109060103090c090917090d03120237080115110c030604060203180105060918010902130c0e010318030c0c1d0a05 71
    0x2c11b01c1070b02d4402c2500ea480c4254111050540d645d128030354001014221140007540c08400003880510160302c250307805a07200e010044172109000d69011490340606d00c944010050180055003000c000503068100f29110003040e965a00182c000d42200c1e8402020320000300c50200d9034940c0c07648055222030180e4182c50681041081c18242e030310030f01c0401c6a00400c00c048440000c1c0c0b2500301c4840482c0030751009410300f00c1004041420b889500343c09201c108640e01c41020390541c280507024010b00525000c031855242c60011020044585a424104444d8050802c2c0d603400c10040041146800f5013120600d16250030030100940040d100c0c0b500d0031030440d00b0903141e40414007030705004100003860700342140ca0b0207240225409092001d10219522200400c0c0940d6662121444008022602080c04080b50100800100303410740d40c5410b05150200c0c1805040258192030441507050030304298548190900d2415007001d64460500300141c0305c4641010341082c80b40f1030207038603106424001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 715349019 1250 715347769 715347781
    0x10f170112052e0c0e06040509060a240e03060423010914030d0e0d02060a09240b0a050a03110607080f0406031a04052413020d09050d080f07030b040f090515 69
    0x40185c1400c080d900003010300050145281041160b50400b0004103142c01141d500d0890000000c1c01401413031a21401e80d50300924a82c1110b0b283d50034071b00c1100540b1480c5008c0d50ba61198020581c03a140036a41c4071410050010000d5100841290304203499100154608d0340043d543d40c461180a10742600f001c12401d556440003c0e14003440741503802403c03d03580e6841b9500001c01c50414140d4910300c0d0304000188400c0380e04500d03d00070b0607901e0302080c0c107110a8107002150042c0c0e48a28000d0607500c43c00c0005c240d18141c00d081d207a004484480d9a0192070034240071034003c007c540a0340c481c00050004031141c00d0f920a0695440620384420100f200d0004c002c00c131401141e0514414a440c988001e15801d5500542c032664401800d94011b0030b255541d0301c0c00c0781c005040310342c82c00d07a6075400c85082c803000300106007140c56146032143c06072031b141c0894218088041c004400f81138541d0f50b82c40c81076031250803100480c03800e220108440c14003030904a603a5043c6806c80d090742011a008201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 715350269 1250 715349019 715349027
    0xc06090f01020309150709030b0f0a0509070f031b030b01060207170102160212120d14090109020f0108040609171c06030809010f090f0311010f170112052e0c 69
    0x310a00c0c600005e403040680c020446080c00348004d102c4002c0082c804808400908089000c9005030355001401c54140f502e070745440102c0d5006000d134003882d44880e0080000342c0c2103c260500b5640e0004039481103680590030b030480d800081c1c1009040c0b102c00307800418070b00d6000030060104c40344860b60400002080760200c0c00c078481e481c0700354201c44d08000014090304005600e005a07490807011619286007220300184260000c400c28410240c0b01d4400941c00c22203030002c542c00c03070305c8440200a10046a80000c4075561403c0503e81403007010b800040600c81e4a601c5524001c0d04205848000d61090688002a41c81000c43c10f00d0101010651500711141e40700b900d0940340c0c08100b00c1e10f400410b6005440b60818050a0020400304a0012a801040c504544c0055109041c1a1140080301002420041008000381c04118100c808220700340c0001400a0440b62225081c0090384140c2c24002d0a10095201141d48110710000c507110741d02e44140c1c1500d29034008842007210000c4280c00321 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 715351519 1250 715350269 715350271
    0x3061504030c03030f05070507140f01140301170f0a05100513020102150a0f021305040b0312180f0402130906060c0321200405010e0a120f060b0301020c06090f010203 73
    0x362021042c500c0900c0001d020784c604210f02091030030020b05001281c1d941c9446e1001c82c0d0400d181054890380320000600389059141c164038002d080c812884003580448120034001440350301104000040c035021001018855020401c4200c41503803654401d81c206903a581c1a41c03000100b04d2458900000d41c400d03108420601020340c16405024280482d039000c2c55240e101a180c61980e40d5240c0035401109400d02c02455072000002c103c0c42228035107810001241d6200340c01038003035046040407220491b0004100c40808010ba0464102100c410011070040d04d1068a0260010701c0002c5020014010310442e03421100440801c1c0031041e101c0700c04507106070b2030101c0100420001c0b0200c801c0c68402e81040541802e07080700010f01440b00d84620341503180c1600c0c01604100001409000550b400b035002804c2e0714069521604c541d1174410b5040140784c15032005031040791010643c001304682608002d0344690001e0003951200071b0005442d888620940d01000706101f0550402e10810060080e2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 715352769 1250 715351519 715351523
    0x1d06060702010804110a1e060905131a040c030f0f0608192901080d0804020f090601021509010633182c0a11032205030307050306150403 60
    0xa0030520a5030040d511076038098001c0b56001e04084004c06280c8a84401c003000740b208039151b01040d20080d0b4145459155604800708000d5048014071080c0c580040c1180a02a981000289290112400d40c0c2d524128281f880d0300070700382400c00e40b540794540c000c0d115182c00510200101c80e0200b410408941e45441144201d8100c000c01548852800903401407842c0182030683e003c03901e03000010f003c40500620f140d2160040d400600c0b28030410040c00d01d11038130a007031801e12428650002500d000c03410032254821204100000c525920902c955583d00b070002003000c4a900305000001c6c040e002d980100c080f40444030005468043d6441141600c503a00100441c072922aa142c08030355030b0ba4004505c50742c28002c0000014940c000c0c5500c0600840179640003065a203440d040c05541c020080c102c0c142d1103003080b00c0c40698104200c1204c2d003100070315690032154403250612440306104c0c41d10281a500010003088030311074000307004500c903410886401618017413596041003280914080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 715354019 1250 715352769 715352779
    0xf0b1617190b12010e01020a08090106030309170f0f280b0a02131d040308130209070327080301260c0d02040e060403030905070b040b032d0906011d06 66
    0x3a0880480e15403080351a048043c1501e003144145040f550f094801040c140c803950780d40040c3d18901280d0100c165034102084a0082c8400d81c65a08d0003049115103001c1d44803655002a2400c0350032904206042c10464203209880c00308515505054490741e644a01c1c01502c90454017103202030380c0e014520612130354800341c03d145503100c0418000094100710034014180c5030400c004a65044000b12110f140007c21100212900e840d00d0001c003034010182c080700d4510001000d180050707503210481a4404010f00d00040e00c0e03517441c0700c044c141d6030542034030601804040c02c038207080c001010011030590b90100c0240805940c1203025001e00b00040041d880c068121412100b41d601d0101220404180020300104012508589030f50500c01d05072001c07000310759280410000c02400b408814010502c01c100c031400c091030070b851031490b03200040c03891040d81020605007a503520401c03101121204c00c0600082c082c46c04101042d80d46100303010302c406010f528948004030701500111a0311808020380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 715355269 1250 715354019 715354051
    0x170a0c020601030f0c0305150912091e1f03061e1805040f02090f04061a0604090b030304031a2505180406180b1c02090609040f0b1617 59
    0x15503000c0d425400d401280c81e40e80240740000824003c00000008c0c03111143e59400c581410348845c0e140c403c01d942c003514410001c0c07048000d2a03882e03040666003000d070101c0d1501304641c4500020303240030000309070300b040250f040d02a11086606601a0703050f83d00c80502d4000007211185654401e0b9000d1043d0480703420352818110340d444480e000203820030310440320990034074800d500003a41510107e40d40c4140c91610001c000034006540210b01b002d0881d0400a4002d5015102007500c503c40c038010f01039180d0b15103098241c1c544041044400450b0001810741b401c07401505844505002900d00880b42519a03200500c500a58818804054040c0e1109403924410000044451640754081d6500035907803000011030160f40c100d4082000c0c8848030002d8150400340401081050000d080d00c1040042001c0c01e0051726804030564001c0012914086250768528010300d03001e02400c00100b00052030414040d05110030228207080100c9601d070001c0c004651078481e100c1a200311001115801c0c110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 715356519 1250 715355269 715355273
    0x90b010306020c0c0907270302210f070312120903201c030b09092b031b030b13060b030f130c03030807200d180b07050303040606120c030314040e07170a0c02060103 72
    0x5400c0b143c01c010380b10141d480272f121a55180f420540c5590040d00d00079464213250712500c1e405024001c00b0b00c4401000c0018228684008100c003e50006003081104444d0061140c80c001704104c1c40d0941101104580b8002000d500401a10340304403054020001c90010414280300424400d00c0b00c0307514111008008040c0e20840a0030a440201d903082c036955455840c09041503c4000d00100207603140400c0004611051003550313000c4030b40b001c2c01c0341e203040c00901c1039014031012aa0002982c0c21a05516201d00d80d0347c10a964008000604004c0740c1e00d00081096048842e1621508480d00d4802502c104070300c240980c406904600d10b130321f070012464085021701402c1d0f0101210010500c028000392100014141944203200507603690b4404010842003001c103008100183c040f60040c9482900a40c0c1c0302071246405010080600c954200c00740b02502005050300d0091541894501541c18182c1018060404003a0059134620315240019031074652400340001e904001ea000b4030a5a11315 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 715357769 1250 715356519 715356559
    0x110d030e01120e0d030504111e040209062a011415010f110703050601170703080a08062706010201150510050d02070501021b0c0103090b010306020c0c0907270302 71
    0x180d850121603681d05100c0c100e03203004110080001103217440000f01414142800e91a61803002d002c14801c031400400301045d400c0e103c04401000c001a540035880d15440d0001400501420004031604050b0745803402e01c6016119003c84508001c90080046001441c010f28429604a0342c90000002e000c240c0d18895100d050300e49000780041c5441f00c025076030008550700b0000180e000748c41552180c00180445000b100c01d44605074007400040c002d2a24550700c09505008400c0c8580503c030907140002c0164a0326100000c0d96483c800c43c1c25034680e00910105681e80307054900500541c41c0c424011884100d641d0301d1020382d00014001400c245419000302d509901c910a800c10b9a5024480d2100154003400509080a07040700700f582440c00c80d1500c64038000c0f4004600f41094142407040c80860b2190180c0740c1520340240000da40c50426090b110b1800109003941c41d04294401d04000181c1e83c044c00407180b1144030158000e800866002000f111003e5020181d400903d411003d00d0381c03406 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 715359019 1250 715357769 715357787
    0xe0606090108060d21031505190312021f05040302010c0305091b1201150312021524030d02061b0304050c0f0102100903080103030305011e03080f09040513110d030e01 73
    0x461100c80120581300351510400d900380380148000706e40c803441d00b003054408840c185c6000e04010740702600700400150480e413080b46644001343c41c68030341c201004502482070041c211070060a002002c43c006c4203070f503001e0041404036015001546032411160415110380070f614003e00c0a0401880e11018003003610441c1c4d20b2004a00d54040d0b0b010b00801c407014000c0c081c2d0241443c011071000041d5196007040c0c80728a1043d1011400c40d00014507803451481c01c212a82e8002a6004442d000d100c001c01469982a91031401c080d45445108003008550350300144140c0318641b08a0a003820768000e818080e424041a940207280da04500704521460400d5810100450300510444064800f40c0c807019088074100c03182a40080d200c4c00c0184181500360250b14010005401308420f1102205102c0800350f21600006090400c00500740400b64105400e480c400c0400a200704001d05014201c01c0c45040c203502c00321001900e111403403050b40303080850100b01d0b5426442d04401050f03a90300442e18800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 715360269 1250 715359019 715359023
    0xf0112020f040509010902040302040507050f030a110408060a05010801061508060d021507110319030c0210030219020f010e0c032808191101110702011d06130e0606090108060d 77
    0x1c424080082c40ea550f04031840c4c002e22400300010380d44d9045005200c1502c0004042a0902900708008202c00307c042d4104e035444048079600240654611207111100d02c00c680c004001ca02c610010b004254000358030a60488200700700800c0925620440c00d04090185a200e00209801ca07000490a060850400760054030040044c5a5007a03001c5514bc2580c11501c401d5980c1e056100081d21582020894400c4000003c40c080e400f0042654000f4504200404024083c02d03040403894041c0d4001c0d01911308540e40070b480c0348004a217240d4001d40d205107003000002c6542c2000300080c10880007040c280007200000d0081d04041c0065011904034248036242d5002800880000d000840c000c034024190460200300c106140640c0d4040061251032001c1001600b039243c4801c0d0031001603100102c5031100d1342803c24407032801a0b60180c1105000d1070b900310781c00c0500040e4031504650030781e1014045c2c036010f00010403203494500034400c00380204500c0b80d000c11000c1c0003040561904007400c18070780e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 715361519 1250 715360269 715360297
    0x102340902070803040c140a05040209041509092603010e070c121d0307060f0311070b090a0201110c010203070807060207121206080312040201030b12030f030103110f011202 76
    0x99440c80060220382c031004040d20842404400e2008000740200e580700140031010003484c1a000a2001482c02d1040384221031186500248492940d100c0b50400c1031071605000300910401c0c1c0da200e103c0301a01107580f00701ca0f41d901303442440c4040075001140002080d0204181b90940e8200700e1130701540000580180c003403007449807410001076070759802c450102403d90341d01581103140b01c25480381c01e40f40c003041c9d900c04c1d0807009003803200f59030240003907542c10040d18001c615400d0600c9128086c1c442c03000b0180c29009440c080083d01800005d6941d80c04c1e200380d0380c80d6a1280c858400340e499001809000b40103030020490300020441c000050020070303003d440c0062404c2d5071907503100f6100301d450660b403000c94408001c182424006105000052000d1000f45150810084061030320681c0288000d061641d41c2113103500315200e00700c0c1c032980c000d0a4412203581e40014803108045410910089a018042c811b901d0454140400f000d0408001a1100b81d0400c0d006041c031000303500b04007400790b841 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 715362769 1250 715361519 715361623
    0xc041103061318020904140f1f0c020622050708150c0a170601032a0323010b0d020f040b070c0f06020303160516030c0204050a14010b0702030106051f09050102 70
    0x90f1f0003070044002c8886543c0007480310080444106880a440c0390312050755034170386144c4145107a004503400e030b070200100300520703031070980c0f03002000c185240e070b0300c0c003404070712950401181610000613461900120200001601d0b903e0b0481c0b1080740c851480c0c1500020b106c800040300f10350610811a40000d01410040307a80c1822907041000c030b40c1c500300e0403221010003071103144541d034241c41040d030740078180312242d984440709030915807880380c061080c52074200000a4010904000b94169001504034102440d034030f5039108240800d54100d014240c9545066500014904011050354406c41e0800c6c0c010798150754a00b0402420142c1ca40c2c41c0300d061000801c42070001a6001c800812003920030b44078a82400e078540184021604010b08081e040d516040b1000041c004c120021411070328000400d694600b50380c404280503112507480607130018000358a0390719412030900c40c000c0454060703a0391540c1603529401281d81c0c04000c1c1143d405d44890303d201042550702520031130303000c152601000d001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 715364019 1250 715362769 715362803
    0xf0809040f0e0604121d010c11041503110d0b0105010c0510061806090e071701142e030201120b0406050604031b0e0405120304050c041103061318020904 67
    0x156010300702c80d081140c104108001c03c000c0344440e4a240c107201c92610070303101880c0d80c68451002608003c502e05111007075003000d0030054440040a00c900000d0011311a0b29040d02d60360100f01d1050004030b4100081c94090000c900300009980342d0307141c11500c2c1420780d919020054501c1d400a4805803907902401500c00c00a040d140140c000404420f012045000d442e8008481113406603004030132018141341001d0700060002580c04152082200492612042120800d0040420002106454804508100c0c55004400e8000f03001542c90405a100784501c010b208610301c003c0c00002d0100c5c080c480000c0c200c1100364404c1103c141c000d08005992603c681c00540f2541150340700b1101980c9000410381d1403888010f01000030400c2400355052400c20b0740d641c580b40d45880d1450007a1840c080f0000341401410060031105a00103041000303100d9401603210030b035034401c60b1150301500307040c3d0a407188900d003032143c03514078104100e2120154815608102d001840030700b0580e0807451081071160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 715365269 1250 715364019 715364021
    0x909010c0f1b0f110f010509030c121509030a14120c1e030903031f0e0403080a0f0213090c0f090509070c12020c10081e0a060b07031211070f0809040f 66
    0x28190060825680c02c0720441c080200404a00710174504000052144e1405da8900241000030303481c08449120b4800700e0610351501d440c0c1100710094401d1911003d128007041c020005103500400c941c0c07020900b080d00c2c0101c01c02031080f000070100060070030000502c01c0b41c10101070884030101c51144582d202d149512501140c0041e507407403840390030000c02d000c0d10f441e5a00d81540c0d03000b91f030304c01c1941b4145030442c44210400001d001400307001c070240000318034030700942c4a290600e02c108070031515010840c502021907601c0c2e001e580c00384e9151106001449000308041108003500c4c0da1003150f0142810f00780074500102502120910500707040b24400a4558aa091902622540280340d40c007840e03020031903810404424481481050010300c00111800444010311007452a000c1c562612040f540f0380c01031650390311181c1805c3c0045a05410168001c040c004802c2102109100e801041718a001306072040c41001000d103940b0341424000a8100c901030032801c90000c10010740c042215104030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 715366519 1250 715365269 715365293
    0x61818071224060207180b06030a05040f0f1101200a0f0c052101050a0209010f0c11150d060504050903040513060e010b0a0206090c1e0d05031201050909010c0f1b 71
    0x40545c01140003030110f04444410916066015002409801c0d1440e01081e01840050b20801000c0d0b11000000d0900c0001001600c45583c0310501ea407034452a81458071b11510386050060000740050f91900400040c80c42e08082446800f024201641882d5030303d036513002440034225401504200f00103200c1d03450704104261300d82d21070a01340384607440380c00d15421140010011030751203205007c07010459030302411900109005080102e1000251f0400e0400c40010f140c600380e00810686074080e107502140003030142c5074140841403003016102e900308401d9910807075143e411a13000784400c01052410f03a001c14a030021b5108005502500c0e000f4213210309030b00341c10500c051000011008070301d5034100810783d48140000040c0c41c0110310744000030078500101d0f1034500703138800c040c20748802d03030f50383d00907850301160b00c2310490b81e070342c1105010406ca209003403040511031180100083c1d443d91042c001c001d40741140e503903070400e0005005000e4615000c2d6995030b01c0c01c02002404000080c081c1c0e0000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 715367769 1250 715366519 715366529
    0x30b1e150309030a090b041a0313061a120601082508060a060315050712020901050c010230040503041e051e03010f0b0d0f020d02061818071224 63
    0x140d6542d042111019050352010361200c207885104010402009100b0004031039140320f107806041d41d07520382107841c010000702000e014101500c1d00b1449107000c0d18009411501c00d400307850003446c0180030113715840d03000903c40c84210341c0104c4043d100300c6944948408505071f60750100c0110588900d2624a071a804030b401256a60741d0340407c0c4148a14400f40000e400750700c40c000d102c240307000c803401404101040d5001c94196008038540314580c1c020016a428648814021901c1da0204400300302d0009420b1000c00300540c0042084c12113941010103940728540040c02140f8040c503114038612a4000061071980806c1d0b1184045039585e2481010f24409102e04404e00f50f0307d4200c82094210b8804002d2020401e2030220203034000d4580b6070381103030728607000400c0039440707006400420300700092000000d60050002442213208071070402c0f4101c8000c016154006005272102c103040c0441c106996035001700c0c10f01d880d1541e0720718064200710094190f20320b50f82c90302c50449061004c900c0c035079004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 715369019 1250 715367769 715367773
    0x12020109030f14101a130f020a030617030a020a0312061809030e091311060708040312030605030c09040b070e060409020903060c120f101508070807030b1e150309 71
    0x580307519504204c9038403038940e207810402000503411903020000781e00340d00c014010255001105c0315a00b01d41c1c0491540701c1040019540c6901905001340145164020303000c2800a00450408020002040c1e404c81c820b0368000b404090380e240c03000d841c080110303440d80c814680c540c14040792100e101d202481044ca4135940204091a5900d0301501001709140c049014a620f4410400702c812080441000142c0249102d42c00500f8000410070318800c2000103410300c130001800100304a158040c0d84110501582d04002d110784500415450340a0442c030550b12100b40c4020502061003510126044540360a10200407840e0402262480d0015409010070aa000c2040141410240290340c1d1054102841501d400c0002400740b0b50150058400d003100461840000c00160800728500302030107004040007068003082400500f80309046600400154980d800300381d02c3c5020b07001d00c160819006015109070001c600c69508850003a44a107035002b114038030f40100340b00e100c07002180078401d2540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 715370269 1250 715369019 715369043
    0x31e0f080307110c010e010c170703051c0915020a020a140105060f03152701020c010c090e090a1509020d050d110a0c050405060609120703140d050412020109030f 71
    0x40503000540c3d00c240b407400e507001200c5491181c1e9000c59a55400802424400360907451030400f6000382c80003150102c0d9210002548005040c2c014019010400c000f0051011f442c1c2d410142d002640c542c00da005000c5c3c030446440c00c40a81c49900070f8550040c9520480d00d038005c0688810030400340f84e219112050f550f80090140750f003410818000110010780040c15002d490348840009110002c060356103001001c0d040c221450b03526804548000c00c01c2d0000d44d156511100d00c14003c0007103580584c081441c0c10400540308030224002031041d41e034a00a890441d1803074039800c21003101c04d1001d282090f030b180400c0c2c005030b84641050741e20502402c0100012030750041c000e41150b0070b200724894503500540400c4001003140f04040b058030802e89000c101a214078000c51854062a0365280d80f0070341d604a00382c20410300007a42005c0700d0098802d00d50f40d1040110301600c421488a03d400000d104000a2101001d004000508c040c4103141c0504025501c1d00d80e050141c018020403118150910 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 715371519 1250 715370269 715370281
    0x2a09040303090b090304060212031b03040302010606080703062624181204060e030703020409050f101a040510120b010816121202010608031b011803050301031e0f0803 73
    0x30b5101984032000c04d00551509080c040c01a507900074032100b508040c3c0000002481c68940040a03070709104003002d0154aa04103071601a010301284c4c060100007981550000702c04921a0142e1000c40d0300100342e031145044010024085c110501d070a10409200e08168000440b20020101d0f107a100c104100d812107060000140081007014a10041030b0390001c0415036003080f0083c01c4404a440904294000340500c4002ca41048403907403010754420315000241c0700348800480d0380f1749040b14bc00142c6003000202c400c0e000c1207820075a07a596a810f950021071a45051642c0840d0304019040d00c0b01040c2569a0001322000420540c1211424488001009199400c01c49a03607101004c140c10030704039003014601c0c1c04001c28040050031000c6400c0003c00c45900030340c001400782c21883c00313407070795001820310408991440b4001d1925542c031301a801d019590845a0304072800c0d9040c0e4401e840c51b4616114034800300c620704010f40c407640c120310090300040c4018805043c0184201540b9444c2d00d4a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 715372769 1250 715371519 715371533
    0x2070503060c1c0c05030c0d29010206090d020d030b01020f010903030b0918030a030f24050102240708040213022212030c02130f090b1b0c2a0904030309 67
    0x40312440c41040c107044c0c1320914250000d00743c0390311040d08407a440d02d5201240048002e404104581d132070901d503400855030100c03045102c0350507140c000c0e0215140d0361240c408013540e642803c3c00390710041e00501408503d10344603400c46038440005204907840010030140c0d043c2100d0b403400c0f0031000720b40e031120390310b4450910103485503128400d6110004148100d221554076485000419802c055985076062454801a449404524442c6901e804d505554120000090060307001c0c0c43e02610a00200c0500299090b05203124421003c0f0940c02e59255940203880d802e9001d00704a90240c0c0e11a18081640d150344080d101141e0203801000c940b0000507500d84440005821100d50036445074840d0000c2034000c4140060f01c1e48c10344802221303180c124503502c0105800e00c4160313041818032400c601400000360019016095034001c0c01611081d0004000f502d100f980f01101c1690030000b503950b04115a07251140402c5550350b00311841c096014005400f1820845003100420390380e00500042c00a2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 715374019 1250 715372769 715372807
    0x90308090706050d110706050a050106020708011e1a1806090604090803131403040803120c12010b07020109090f1b0504050a0e09100903050c0606010c0206030601030c02070503060c 79
    0xc19016100803801e000c0d004185100b50f00d0851103e98491406880840c496011915a00d800090400c0b0500744108200003030071081c070416005120310703030010400e940184900050514814240c0394084d401d41c10a0026000d00141c000361002113440600e0b86450f100880e4901d10480c1d0510000c900e401410000180005403007280a0b910308a64240001c0d156400c583c0c000750700001c0b24992104030314066560a801c0c1c1d8440c051070101290010717440d54000040e0121740365000080c2039555a1f0401a0514010781c2e114070300c00380c8002e0041010100040003000c41c81c4c018034244140315211544003040c1c8440a00264032142e03114080445443c01502d20018a403e48c541645850701d00707070000e015141180078070412025460042515420100030403d0b010751094000d01148030182030207402500846103e080500800001402070f41c8140c0440341c4580c0d00405250445c4c460030011002880e504080e5819403158903c0800d4540d001c0001c40c0c810a40d0038113856946102128206102c81c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 715375269 1250 715374019 715374031
    0xc0f14030106050a03020c0a050f1506090c1c02090d0309031b0f060e0315070806090109090c210c03050f101e091502040902030109050106020c10050a03060803030a090308 75
    0x58244014003000741e001c1c044030b4104403a4138000d0f0310b4410f40082d042c00c080482174024000d10510050006050001c076440c0d8020844e120207180d1503581d48240a00c00100b1112002d403403900304868807400b043d102c4cc950900c60101001400c000c460804542ca0f00c0c1440030075404600040020420048090300f42d141640300d2081c841d503030a140411382d07a1042d0440c00340c041481859040e082464508014202402e1407446054500d41001c1c40064044c020681e880350040403924000b003550350180c00341182c041d500c42600703003503107181c01105611040c0110449650780b01c42c100d0007000c100440b01c024007440c00752000d492800300c3d00b84811314103100c0c000519002403c14050042c60041d010303581e91444004403000c203c1e05c25620b0101c201000d8618606081c0f8804074000c1a04030841d07020354103036480d50000f000345988170401a80d5650020300d00c2d95010206c5400281c0030340c4a0405000c0d144e0540c1008184940c0700c00205065400444508a14a940e2401041855400f61704590409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 715376519 1250 715375269 715375307
    0xd0501050301020c0c0f190b091f020307080d020c0d0305160224070201020f0307050403030306050d1509050309040603030c121b0b090313080f1b0a0320040c0f 70
    0xf1004d901a261a40035000c9418032450798221900344503103a442e5050488511518842a582c6d00d5407401c81031500042911406402125503400200c10803a10035003040401350015810420b82c4c1c1c5d0390600d00e0780712800300d03407565400740401c3d00606003c0114000800c1592030204031460720401c2d49420301e41d1014204115030000740642c1d0042131400385003812000b20060031a95980c1c0001c00d0380603100320b01c0c031800511400010024515401405402968881e075024446542d43d00100402c06540180c054900c6445c8801c46104d41c5040e031184031001e114100741d9040175550341c0010110b80390b5520a0307000c03c0c3c09070340300306c00c21244d2050800c0324103150a02c1b00340c041900405000107120f4210040c036424800d8080b5410400030020707541041c4004e2901c400c055140d44409446801c0d40d0007481c7c4a2160308844900419074081804100b180079001040c07036031464881c4010004034901b61200311b03055142035030550302d550085070001c1e4110f03105d05100c40c4038481c0041961121607400c4002e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 715377769 1250 715376519 715376527
    0x5070b1005180a050c130b09041805060f070206041505040c03080c010209011707021903090305060c040e07170604020a03150b03221106091801060207060210181704030f080d050105030102 82
    0x11b545010244410340b40c080a440c0e031075032000c00115000300040c032031209100079021901c408222000030082c2c410100002c217101184c551010999130741d48255802404080c8040316031491801c3c581c07010f54414010f900c1910306558030303100d007041640800b4040d121a50005103108207540c10080007641000e100300c2ca80c0c401e10300038200035262007030403101d005482c540303441da0001e0510803c003102c090754010051b20000e04009243e4509035115102c4d1100d0990303404001b0f0030301d6024810780520310115450660095607010304200c02540712a0700034050568501072002e00f40c044034a81c1015280380524a41e50381400409120340f4203022041b0032440640310309403000a0343c94030300000100001d07648241c8900182d000100b17280300d03c0c800c81011410581c000075010760b000aa1408a400a03005d540030405450708960654040d2802845440881e00540c00000d2118208410748500b40d1003041c201616507640850700c0040e064150307000072000c10001d408401600ca280c2c01070108500071071030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 715379019 1250 715377769 715377787
    0x2202010e0a08061f2103050f0f090112020c0a0b101703091503040302030d05040f21030608150105240703020d0f1d0909010e190c0b03040305070b1005180a050c 70
    0x4450b8010745c08245014205440000301401a401d442006817190b551a4448840801041e2150058511940010807118200c9660350451086404402040010300110081034591820b0346c40007030429008006030080024100ca000188180514981005181c0d0340101c1010004a4403550561780c03c851402c0051100003600042103d0301c0c002c0c0d40c0c1c00420a0307030f15400c050060013103e9002a0003d001d0589080000300b90720688403400f182ea0710200649502c41c80526540c4000951850942c00c018005105904e02500e26101c0300d100c1c0f54245283e042c6100070703d14142c115143c11805a0b101b90000781510740c02141d000d0084066140c0301c0600c16070340d40700480301c02d02125818010304030000410b00c0c41b003080d080301d103508800c81d04403080007641118901c000c5102420a44180c0d00588000c60490081800c9a01a60309550368909001150301e402e07440704c03070140034203801e00d1b2503910000c0e03191984002000b5120030403004c03100318030b4013030100020b84100034a90400c1200030000140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 715380269 1250 715379019 715379039
    0x3091804290f0406091a0709090b0303070318030c06090f1a0f070c0e010f0812030f06060309070f06110606010305010f090c030f0905010606020d082202010e0a08061f 73
    0xa44107030610a2a405920f0741d0030f01a004000306800038100082501404100d80508120580903d0b40d65451500786070b59a6082d604403245100140d605400c10800e000202c0d1040044003055803036800b01d00d060342e0b0baa940c4c84041320010341c04040802d00700b92007001280c68a4200e100141a942c0030b052144205030b9802455114808007160f2003040800d18409000e1030b01c642001030b2003150404141541c403440c506104da082c511498032541325030010102950015000c2c1c0b4001e00e214070b0042c2060b00c4c0c4804001103030300018a0703400c1911510b40c0000d01081e90548100080c0320f982c81d0007182103580505a800c02a008281d00d05050a1200400034407103003c62101c1129501030000450101d10b910403006060841860403081c4c0c01d0403200320078003206501402c101c401c0394084a0084028100035601450201c031241c081c48002c5032a030b04401782c043c9210091a2051401c080c6030910710f000101811001d070843c2e0003a91140c000c00444010181043c44148920404c003084a460408811 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 715381519 1250 715380269 715380271
    0x60c13050112090b090f120915031f03060203100501030b0a0b0f09030f100b0904150903030e15010303021204080622021507120e0d140309180429 64
    0x103040150190b00e04400c81d41c1948485407041e8060826901c509000190a0380d0f0345800070b01d02c0740c4c0e006030003415214039890000c440070303424042d10103110820580c403070300e050f500010481903000c0c02996040500158030f488c070102941c41000011b8a0381019440000000e0711600018145454908400c0c030a54444034108102c0e5484080d45030345550890407aa154051980015050300c91103007042901240402ca20039a01c410210400c504645c80c010000101c5003920060800450f20f8201888114a90000d0b82205d000e4140892009244812a403400c204140e04151070003800c0018010503506119541d00209041441402c10341030442e102c0d280caa002d0140c0105862566000000c0200a4141c6441c90340040401c00c803070119841003002a07201217012518082e510301041f90444c01450200c0b0032110180035859001030565403002009465800744d200d07444144108881591459451603022000070b0403100c8600342890203c4402401034804800c0c521000c00c0380e0203a2407551006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 715382769 1250 715381519 715381529
    0xf0605120a020f24090310020405010c1103120a05030f0108060c09040504020d140f2a0103020c011512030206060d030503070807110a08220807060c23070503060c13 72
    0x100344000401000a40b000146400c13010010300d0003e00002d85182e1002030010018290f081e0f8a14200082100702248103d020f6207000c200c0c1c14428202007150300c44207100701c410107000c841c0000c0d04108103000304e401c801c03401c00c00038074000200182c100c000b098084c01441004d0042c44603041046082009000e1031850314001c60f41c4d10300050a40d038134159070280341030b08000105c110030642501142c480c2d9074030040c00c0440c814941403002c9800d0800640142e03461011130420302503207031030045001e9406a404202c0a6495500321941c07071f424039401000400355820b058406442c41d03d80a0700b4408014841c9105680c20a103101c0420307002000c69500018620f00101140e0b178828007954090781c00c04c2d22521a101b84500708040000c07000082c0a107040c5140b003100c2a507140241141c102d94113020384401600902403c2041c00d0143d4414004548202c1301d0310811501c0480c0c5200700c1070480b0761098651700001c8100305a06003802140e4202072100d84d8146424102c006115200c0404d02c55 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 715384019 1250 715382769 715382779
    0x30607110c0406081501080f0616021507030f0609020708070807080c030f07060b2d0d08070b01141903120e0d0b01172103040318090f0605120a02 64
    0x50962550028800700d10300010040040040c10b444910385030345c400c0351801644100700c02ea0004680c0c118005020308501a510780182008d90703606088080700c041c2c0741200000d5208040c0c3c0e50401e04ac0341d4481910445590350300181c0c1481d214019070a4903160b038845211684100107403000302c2c55007070072500b00300e0f00032901c160356a4652401c40c21510603c1c1d01030119000c049111101c03100104010030f0014024081400400d08001c208a130394011444201c000315400c0108043e130051402500950b10001000081039001c2a11141415480b1b6503003110480c140100601800081200000e2050310940b001c3c00b50030302c140c4400300301800b01c0c08050403041610314030b07420041c410010080390a1010700340d4203941c9070f1446d00740c40d6010207010f5441d9145c1d9a64641c00c040c10b0000e0842804800d01144140b4060484040d070540c0e44007030002c0e82044081c80c031300d1607680e41942c0f40400812403040300052500c1800c0c00d9404580940c0c014034401c80c09802c034100e0000c000111300e1035068049403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 715385269 1250 715384019 715384037
    0x807030504030804030f0c060f020d0e010915180909030c11040914010507020c03280809090702030a0e040908032404060602032104020d0b0c0f040e190506030607 71
    0x1000e840c207008a42c0010b2803e10002404001c00c48401100803a007441348601d2411103840d0711055840021f04000180140e02428841e04030620030582d200410906040045203243c80c2c0c0051040c0c2c000841c00302006c6400e02c21901c070101c545000d10401405ca07031400300403903946550018940c0f0701c940030113880f80900c00b04801c080d82d5290f0001103072070b074084001c0b580d49030154017090207000111001c00141c003c0d070246400741e09002c00ca1414941030303800320801d200140b040d00f03c60b0f5080d00c03074146ca05401c20300010406449420426014042ca5001035455200700680104201c045000c214000d03800c00050000148c020f10680e034100e844512880c4442064116a620000c01d8140084c0d01601305000081c440340c022004020720f01079141c106092154894445d911280207980094002c0200144500810f00300190681c01c60b47c6100d80c0c80c07a242e03c07182d0340115a0060f420494180c0c0f070350001d000b04c407503103500b05004008441c4014030191912030002526000024104811700c405d5203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 715386519 1250 715385269 715385273
    0x1305041d07050a031a0903130f2d090908090301020c0102030f10050d030e06091816030e060403030c05070c09050105011101052404021e0d0b0618040225050c010810050604030807 78
    0x11048c0c540324044032406c5000d140c0d6500050103035030124030683c2542c02c80d041261001c2150b10b010800c6801c41c904000d500342c2d03c2d00200b0801481446000d071200380c000e00c0390b104d195501303000510101c808000056224101032030300c216081405000c3d0495028065001c0100d6100c110581190b0754060514014200c0500c011512911405024079448902200e040302c0d02c1801c012020b00030b5895003403e9140000701102075048804030400b2490715404400060006803081e08002040307170007071401500b480c43c26643c651001070b10b90014050f0b1034480340180500e503030140c0c0d0001280b210308024451810f00c1c0040b180c3ca00d03810b40745807040100c0024003001c942c4807901120940d15078550308030010012000514000e800142480103058204014021145080f005640075200c5c402d0382c03010710300c074810100002940300c031910124102e03502c0342c140650030050351000503141c0900041d003174103c1084001015800001d11046548040003014481500d8110555050340d601c19400361b5200d10078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 715387769 1250 715386519 715386523
    0x50601030902190311010302070c122405010e06060720030309030a0605090c031f0b04060e0a0f0b011115090a1202070303030f0c0f051305041d07050a031a09 69
    0xd10040d40207401c0040d40f09800c1a600d070034100b00c07405541c4d000f000082805c0114140d01c6213034809072181010320010320501009010401c11244035040850080800312420345803000489410b0301d1847d51040104100e19415492961001c01120304510b072140540c0d070621041215010070000c0c0030040c4000010b910100b04413105850001e0890f1000390030f51815030040c2000315080002e41c01004100b1402c1e081c001a540c11043c01076206000991840c0c0c1645c0041c1030803c082a03101d6120900040e8113000100103a0280e0801d90011846090319000801503801502426040001c1e648000c0d4040030085a082c94903540102c401240d03844080210f89410020f89000e030152a41c940d1418002c0e8001558a003124400c0d281446001100c41e0000201e420070800b040100300c10010000030752340328800400d5050310011010f4035803500c03240890203c91030040c03030260032000940c1034040324500b00087c0c0300600301151503e03019401c640d80c4460800c150071100c00007410441c0424845001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 715389019 1250 715387769 715387781
    0xf0207061d040f0f09031b030c03080c07020a090b031501050a060c0609060606110f1c081810020310050616060c1709030d061d06120a0b1003020f100206040605060103 73
    0x30810007400740d0315203c0c19131002400e034060200d0200e82d9031402115180380e16108040c509406849500c1910307100c0e14252100c1c1e80081c8400e030b441d40104500401651451100e00240c008400700248500258060515029001e03680340d440c20858801000b5541d5240501001e0350710a03d4068065200b900c0c1c40c00c0600780041c1e0080c0f0301e074100b00b00030030220b030304c100c0802c40305c030310542222199418101000d03190038088000d21502103203c2c1106041c50f0041003101e400c41d16070203642070742000c840c00309070410020440d11510703c0d03000020b00100d048c5109012002d030404443c2149800c1000035551100e80c80007000501d160f4684200044440c01a001c80880f150a820548418904000501e8803a44101401100341d0300e01000403481d0a00301c0103011001c2c2c00251141c0403a12500100142200300d00d451000900c1110710760000500718200302d5003d4140800491041350841c81000080340c00c1c00c0c01180255aa4840941190742c0000c40703540094008800143c0e80d210540120058a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 715390269 1250 715389019 715389041
    0x203070606140306070f09050d080c030307090f1e23100e1905210709020a020106030213020307020a0f110913050d08100b030a02091507030f0207061d04 67
    0x1240400000d070403441c41094051584003241624910b6036041ca003500d0382c6906c1d00102c2c00040003840e0520203803c06104001c0e96070300407028607092489420f5403900d03581c0100c61540010794080810025240c900ca0f400c4050502d9400d1594148101d0307034001c245035802e11814885111201a5070344e070724800d04005040f80000f83c8500c01001101101400e482015081c2900440c4170380c40c0d882c03000c02c0b036030424420707540c00074203c00a0501508600002680f1408910f030b682c0104a4009000c010138402012119015000860080e02d58010014000103000d90303003041500400800030b4980e80820303040270300344c0c1c8031038040c0c01244641440100e1501d100c1c40b081c0c000200c04280007601c8040000044002e1003401201e40d0801c007004121284003003611a19400c1c90301040600000f440305015682c0b0180b4980010b041c2001d580000b1034280d0794041c2d07440c42560014005092503400410144080d155000a04965161800040001d100042c01e004480c00d42c1d00c00d150306580c0c98100b0b19200c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 715391519 1250 715390269 715390271
    0xc150a06030c061e03050124121803120903020d11160b03040615081b0301020c1905160503070b1b06070504230607060b18190c0503060a051002030706 66
    0x3544071032026001c191600481e06151300903600c0c42c0c031220f100c0c0c010141a03424482d1a401041d42c1841c1d4108507282003041c00c0305020b06482d071078034800c0d014415403100400810b411002000c43d2704003d0000c00700500e03010310b460b040c032076040d01203900040c10030451417003031900c001f1b054401c3c0710300350030001c2402c4640318002d0760f040c0018003c0c1b1200d0146000320b01810003082442c8108410721031503a26480790060a80007003102802c0020701002d400d10f4200c0290000d4034259586c80342d103091050502c100c110359682b542c0f20340c0c24440304000e581344001c800711101c0052414400041c4c0c0e035528512503056850310009500518080c9004000403441581d4110340c03903418a024003070050b8000d40a481100e0380540f40c4030020f8000e0414005d68240003130a2180391260075110b5901901c0450305980d002810410340900e0001d03502142480b0700b103112004080c0e40b80074042c10301030b81c00c03448150040140074400c0c031095640d030584490490328125a20304482802c04016811409403001c098801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 715392769 1250 715391519 715391543
    0x60f05061002160e09330105010e090105091009090c030b070c0309050f010c1202011e06050d02040e0307080a0201020c010524011110061d2a03060604091811060c150a0603 75
    0x780750041070344040406c0304c868801180c0c0c03600700446204107401c101640c07060b0000010800c5042541a00d80c003c42014140200c0c25110b19601081d180b401c0012200400c00701010001d200ba50406160040c1403403901d9600030205440041400304903000c0c0c80d00c6800e0350b8298003190307030048c010282100d44c8511011080c84071a00b0180c024142032103c04440f01c10310f602424010039520620050750401400144950700a0302408028031001284150f00c0c03004000380d20100c2c5031200a4401e10b007a60340050b0b40c070507178400c01a080d01c20140c0a40d170a107540041246d18480c8901c104030f005a420303e0096420241460551f103021031800582810030704d80300001c110850383c80341c0e14000c5044180d403902662203002d030012101c1c2000804c0e0540004035502e20030840360200066801440041c0354a00340750302c412101c03003211904420351030503410011496080012a8401a4140e2410dc4005081000000b03036a61140d001c240035a141310303890030000d0790085455200c10b0243d81c00031144001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 715394019 1250 715392769 715392823
    0x100b0402070f060c0e03161a0c0601032d020f060706150b070605011d01030f03050909070809010f050105010f0302090109211b08030405060c0307060f05061002160e09 73
    0x184094000040000c0c482017400c88507060008801164407214400c84070400d2501714407001c5c0503060302007210680c004000321100b003c42000458081c2d0b00401400035421807504491f07a17180c4180401c5443c10084c4004480907a44180342058010425200c1c9541e079446490060000c14510349440d40400242501250076014100580701c11485010b0030009a41c80f401c82c0245c001154108020813044c03180107000242c444421111003078440e09055040440d19000900798040c100ca841000580c41030410501d1031090080300900400d81c90100165414540020000c2c4030300c6400c8000e040c1c0002e00c0e16a00d0340304011510041c0700395184c22010400d10010030202d40030002c0c0a441d103070220821101d18051143d0038008036103044000b949443d02c2c08040c0100c94010f412074a02e640001c0c840c001c081001400b540c03450907072042c0000380c280307061410040e00c044000308809c115803005940001e1481c910034240c3c00c0c0c54091004c80c080703543c1d03c00301c00d1400450f0481c152002a000400d030030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 715395269 1250 715394019 715394021
    0x20d0f061505090a05011103130b0a1e02060604020f040902040902130e07080105011809020c0a03020105070507081c060b0f070c061106190204050402040b0903100e100b0402070f06 79
    0x20035246402aa61550aa841d008a90600820b42450361140c0548000c0002e58010465610400c1200d000e81e8105141d4801002d20300c0c1c0168400d13507221200045c402c0c140c80d031007442251005a00e000340440c40351440c0c8003d550760f200404160017558005203101810421b0700036140100148801555038075200d00e44103010f034011032214000c5051000380401c07200090003038207200f03804a9860b003460380c0c039001c01120320f08405188184103070303041240410002002c1c0024805103404100510404c4c4103850001e0854900605c40c0c0c08001c400d11180001409010895103d14070001c511262203000c00300401c0101459031090960490000e840c1d10a0360106007c0c054007400303110385400c6281c2e541e070180c6825800c51106d030000c1c0c20000010301410b81042a203881c0841100c4010b05050700c510103d4203d90040d00803291011300456451170518080080c0000303081c080300140014001410015510001541c01607003d1b52a00a0102d00d0b8446605840e441c5404c503400221910441c28004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 715396519 1250 715395269 715395281
    0x1c08040302040506040207120e04020d05040f0308221b08060106110613110618030f0a0c1202060910020a0c0b03010501120504050c0f010c02040f0b100207050a031104020d0f 76
    0x2c0c0140e05103070000380710f03140c28400e4132070a41e080103100d1000400010100c8a203440c1a0001da40207a00b881075074030b108507901c540b5110310710503401c00101c6607103424090000c8100500d0300c9144001c00c0e803104000c0d0310004801032551341c0640481038058103040300c0307211007200c0d80241c8114428607000049103517018001704070a04860040d40e030305886da41c80c40102ea074903000011b4042c61201d090810700d410030000078112180314481940c960120900087d040c20b05904c1e800085078080e8800c04d05002c5a911603330000e0540072190003440007641d001c00d03118080d040c0034600c0b901200c0a080c814034000d000a0100c1a07104108000e0b603611345162624903007080c05602d0004030110b030041002c8a0500c20240210340160040c1400ea0405007001040382c0180c100714100f02d5550320440043c0c4a90151100120362a4400320742c42015009211440c4c1030095900110340c0108010402a2200076800c01540e4010315194095111103000c43d02034424100300c004040c4c41c080d551075410741164040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 715397769 1250 715396519 715396523
    0x1a0a021f020a11070503030a050f0c0f280f0602030c04120c09180f0213020906031603050603150a1d0a030e03010f020708090907030e0703050d09050d030503151c080403 74
    0x602c2d5007541d940c0c8200d075900e83e14010341b40c1603401000301252050180002c1c0401d8006000744034608000c4501403070401001e9254003074203078880b40d85400d9506d403010941c4907600b5a90440710281d01ca5440b480d001084202019084942c000045214034240780e003142d000d81030301450600302c00d0091408504019007403050080c549d14064a07075912104402d040c0030300603000340c440b00d040d00080d000c004914040d0141140c50560030080265262078440156200795098000d0422140001e14041e09680d4000c01c920f1090704803c07500b80800004510302070304426000400990640b000e1000042803c9a1140041d648642d2a1030010981d001c0c1017404040c0c0160005d101c080c515500078007e80c01a0398001705844000d0021121a04000f02d40c240e118905140c0861981900f603c42824103506810076039190304001d14620805030008141d000826041c0e80303500418805071401416404050050440c040c05508002d0300c0707a4079440003003100400085102c40d000a1482c000c00c550b840b80c401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 715399019 1250 715397769 715397777
    0xc19050a060507110604020f0609041817030f1f2d0b190507020625110f0d1b0312020714040e2d03030f040303151a0a021f020a 56
    0x159810f108540489102c4413400c0104001d855660030405071001d031030305454000c0d0f418401c10107580e6690042182d04c048400100c0c505042a060440c03101001e525812400e960400030b10106150282e52654055143c0e85402d401011210a031880d225007980301100c0350780003008250919070b5540040c00408281c1b1000c00c01d155445a03584854020b0008510805001c150009502802400107210b000c0c4000d00c1d0350300d00140100d40c5011b2030707605005001250403503481ca0003044000f5001d01c4c007015003250214031a4410b140004c040d0080c055004090030003803145107020800c01192100510792050701045035000b9414000d5942406e4400e08407500780034868103405003010300c50310103c0341d03403040a0800b000b08908422405030f08000510300f0340790105007858480106001440c060344442184440b01d050504000b4182c4200500b22851310f006030808112520010701205401c070b9025903903a0721007102d1501a4104040740d80d406803000101050209600b000e079005000002558407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 715400269 1250 715399019 715399021
    0x210809101d090103051903181401020f0604021c020409140303060102160509150109030f060507080109230705090a0815070837151a1e0c19050a0605 65
    0x10401c402c200c42880003030495040900c502941d0000c0c14150108130740681000c4080f0760030308089401e400601d901c100c00914083c40080415030b07051102c0308010760090000e04140c02d0540014528003140780040c40c090a0414411003151595001001c176542c0111720b038001c0448029a2948952084407138900600441140c119695072040700d40341a504058996201e603a1201031440c042040d261001c0d06220071280c0000000c0c11490b622200c0d0f41c450742001c1040c0c1400c0318050903440044c0c120410a0341170440c40b44001d401c0422407540701800407500782282c0c0b01c05209440750310880111a0b00f007421107001164050f0002404007207403540c804880d02d81d80c2c500301c0845100400b500d60040b84450301071905035a02440507083d1441034218450000200103103114412181e140740c02064840d5425820481c030030300003182b4100303503500c007040c43d04e4102e024140500150306040303d045007074004a087c80254800b00600207441100c2d07900c5411081d080e051180e501d104e428800c80c0c40703d042c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 715401519 1250 715400269 715400327
    0x305041203021e0706060302060417010c1b15020f0c0c09010b070804060f05090d0b10060905010e19120804030b06010c0b0103020d0204090b0c1804020421080910 71
    0x4421100c8000000301050003400307020b050708141354004030301502c0c0c1d25118030010000d45e50b10300007400101ba12200105e8020042502d15003501c00508422050100300c060a86140c103c2403803003200150310000c980154602e980b0108000c1c012201103080301039012030f000301281400101c88400200032101c40505070381e160700300d0030f891081c203000900742c00050004010440c05000d114990b95210f080450500c06c515000c2600030085d040c0541d0504000d10502981242062125020b0a0b01c0d24025040134184800a482c10650410250162001d04c000075903107403034081403801600c410004242036444c10300303005020350804e00007a9201c000071004640298043c4800200311640f010350b5400310780c40c40c0c0030803150108810702a40c101c0e1b11524440009007100000c10300ca5601c04042c2502c2d2400e90600b805d880c031040c885e81d03004910411080c80001d42c040598183c141500c20b0701152891507190501e1280602045030785c0207803416020011254101c15a0b164030f069114008038411424 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 715402769 1250 715401519 715401521
    0x9090c0906140a0b0a0e0d06110d05060414100b09150f0c0d030509121b2b0c0b0a0b130504060203060f06030f180f071814010f060309031407030305041203 68
    0xe030f11141d01003180c0c80151b00540c1820a4290b0700705008040c00221030740005501003107684003490030780d90583e44030300f0040f43c2e10b040c0c4141c2500c0711113580340c0030451034802e1003d90311a006000d84010090302041803001d5a40781048507484c59072a041c0c03940ca912121120348015000005841680e001e00900c0b07000c1c26210f841003501c2034118030b004012240d850784990405a00c400905200340c284a06422043c4100b0000301c06030703140b51069031750300c0b02070031151102e6964041c00390020450000c1040d00170a03182c0501030341000441ca40001c404a11400256895222100c84c80949007404100400d10074151301844c410602a03440300c4a508500080043c1480700b21503510007250036401150403603041411203001010701d0801c407003807407940307078407061600e48182e0014440c100194080440d8407910b00401c03840c20310f121031003603541d414040c407480700021500603481059607038014241030621a886200c8240d2040e04165511075a6040c01406040e080300d09031200c140c855101580944a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 715404019 1250 715402769 715402777
    0x3020c03190b0408041e0602010606030c020307120516030e0103180816060b040f02041502010c090303050a02031201080a030f1e030f1b170f1009090c0906140a0b 71
    0x4040040c80701c0c0001507660065948000c0c0c030030fa5816409001c013090032590110040b0317040c001241032028003490560002c0c01d480c2290040400c15051030048200660000b0554680c10b1b03011840e601008440b000c100e505004201c0d440110201200da400705158210b0100cd08600c82a07034144400d100700750012240d010004801041c6680c1080015140c0408815074103809200d1000423034440c40100000d81a104008208240c1c0c0758000381c2046903860002101c207190b11a40004c0c4900003400c10090410051884041e042c080000307030010700c1c030f0b100b482290b1a001d1550708008595843c0c5d801a0755407620f1190450102d10f85007502001e00c4d0140000308034140d508040c490341902e4481048025100c1058078281040c1c0750313803c0395a15682859180300c0c41c45187e0b03c0c0c4000c1e090012002d14180b6001d0101045020200103001d070034410304000c4070a8a944110218951490749003480060b5496809941c80754900a004141810145003449200d2422600c8121340c0d51150a45021441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 715405269 1250 715404019 715404043
    0x60316170f07030b0121060608010f051804051c0c2603071b020603041a01090203090a020402070f05071e08030c03040501210c0e090906150405090f030f0703020c03 72
    0x2001d4000991007610982244402640600d0218100556802002c54000400854030341c03040e21a281441302d00d0b0f0050400e401008c204244000c1e00c1d1904020401c00a08400d071301c0c070301a107000c1c0040d003402000c00c9920500a42036420030f03c40c9400c542c0003030034000424022500760165a11800542c08000450350b0b0122880c01c000d80780da06d0318802076072041e180c1350b8a0098000c84410030300140e644e10025521850040c290b4545c8181c0316100c00c04c19090580001441c20b20600600881c40c10024482401030383c1518010381c7c0e04420304000b0f5010701800c07401040c62180e407101141070305075101800700500c180b8901d04482900e65a843e51680500d0602140552003804208038640c0719415000b00046c4140c407054800c8450300d08103059801c042a1000420001c16512246042c042e100940c0b01c424100940050708111080c803230880244c1072003520a6840d40e002c10070508060120410050800d02180d03540c1038228004449500004410390150184182c441600c1c10003103601140b000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 715406519 1250 715405269 715405291
    0xe13060b2205060102150c030f070512010b03180a050114072d090305100b0a06170f040c0906080615090408030403030c36051c06180206031617 63
    0x1c208241c0100615005000314114030a5400710008545c0f918201030240b0980d0800c195203181022403c010014040c0070b81e010481308000103100207907002815415610040013a60740c0351a500044004072890fa81d20000c41c0c000e855040d801c1000562000701d40c0d0881110381d1809644104080c0c0e1080c10054411280c603002d201c0d0150229243c41107016500980c0c10460b00c2c05840743c90302d510705071030000042d072000e07039a14030074540d0f02d4030000040040106c1e01d400303405400c1020b0301640744500540003840560300200414200704200c40c910000d0620310000b0400315980b03222135542d0300c1045d1040c044074110091621814140f209032948070301e4000071010301d19141c6036021002024070150200800650541100c0c28502c240d80e01055a02a60140c0700707081c0500304400815461580728a201d46400030040382d0b01404280444066078000b10300041c829480100103482d1441103800039840b120000401210b81c8001041e02c0e944002595400c008a40460416000b400180d410344c51030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 715407769 1250 715406519 715406569
    0x2120a0b0a050d030c060f020c0f0606060708041206110c07030b090d0e190801090b01170106150e030703020a06030504200105030a0b0301091a1f05100503060a0e13060b 74
    0x11901030840c50b1401803251100151500c030440f41c6100700d03000040e480400350407480c410400c418041000c66040801190814580143b540d40e100380b0380309502c07a1030f003100410300d04001440101d0b0b101e001c55840031098541d0320404580b4180d11130754103000440380c0024031804107080c2a000108481a8070f069280c0200900d4440204601c0d1802d00300f17603281007540030901280700d0743e080c05400c076007034030607510ba89455040c07914031106903800680345c0500da1715104d010440a02411036003a60f03200c05060900c06103040c0b0010130b0404209030401394101410384000902c850b45070f40a40d01c40c41c081d00d014840f030206600007038803400541100728000f0780c050000c1201400140e00440525070000c00000b054089541c40010744001303080c101c5030710b403c0002002404420382841848002040c0c0d81c090790f041c105000035040f520040c00e0401000f00c080001350301390f124503107280080c041941d5100ca991038072078044045103a030404112800750130b094071b042076030411910002d0060146032080c1c2003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 715409019 1250 715407769 715407773
    0x1e06051b070213090807060c0203030406050a05070c0215041a07020307120b01030204380915060403060f0e03030129070213052503050105030d02071206020c07050402120a0b0a050d 79
    0x1400c920013090319019010802c040008810b0704c43e100d05501c1c1e82e00078580340c4ca030a040c0101218001026500c00c0748c14441004080c0364451026600c090f07044032011001031040030001000c0c0241d401c03d81d5101909001040016845406050158400c808840e544c81c0c491001402802c0b244800920010044006000504e81a04981c02c410401d91100c1c5000b40b4802141944140000c403c05d0104817104082c440d5051100e510346d4410811400022151034881c0428810b2050f840080c0565a0b20001d00100d503c840c0c0103a025415a0303000c4a13181d5840fa81c60750449071240701050070700d0310019220321000003c0341c1a06c031942c0d0010402a83c006c40300c01d07040b000e840020120709485a130300803040d2400c0321044201c4501011a54005401e40c1000141440d00c0c10181800c415944040390401c100303d03c5d041c03c0c00d4026480240503031a604a61500b0746080401e800075603206d400442e034240907035500c540d660300c41d40480314188181e04039941807100210481c06940d40116506100c1c0e80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 715410269 1250 715409019 715409021
    0x1e1c0f091211060406030f0b12070902030406020706093c030c0c0503010606050c06090703111003060f0b0325021221040804030201090602010c0f08041e06051b070213 73
    0x10704640100e070707040900100c000000d0203030380c440d4021402180d59074647c1900d03100140301d400b0040106175040030440c500d40000da60740e50018850300c40c05980000024040203401d030181c51001e5408102401849124075003403a482240501000440318410208003504d400b001c0b022415014090300840318603e2a1800c0706c00700043c4400340d542d101c6406001455880900c1210300409090780d0f201d17164551540c02a08001025240b1101b6a100035024800b06840c520100d10f1548129816012000079440640180600350300c07400c192030b1041800624030070740c0b0004600c0f920a00505107141030a009460b001546604d203a500141d2003541801400c8004000a0084580c6508030382201c40542d01c0c401007031313601142d0844e0b010350041030800071940c111070703090040c00060000b8003110581c110014880d1004a110004020000000c02c0c1800080c2000c05248070b80300200b04000108c2d41000d101500065656031032040e110769a0391044816403058495483d8002c2150901900300c0d00780d60 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 715411519 1250 715410269 715410299
    0x60609030308060102030c0f01050907050a030c17240402090603060f0612070902130e060303071110090306151406090307030b0901060b0c0a050123181e1c0f09 70
    0x4c3c150b200410614051440c200301040704010f4450003c40c0518000310340504107492640407501401480200740000303a10204070200b41c52000e84e0540b0b181c0040d407075040c500006420183d0190039503401d403951207036190322454840ea009540810041c0c03100c5051507034600d4219400226200802d0210781113161080400c1c2224902d14200d030003071911341404800320790041c1d07889084904503020070401d00e040c100b60030713502c10411000713941090b20540b603844081c080d0032821481450f90603e0400d5450140400c1009950421000c2050840c0f216404500c000140126244000c1d41c4a0141107484c080c4c04032403e00c1e070003030301820480c6e1859658050300c803000f80c08020695290400403924081c068060002526280000c062141d001d0400c5421074428001d600841c1820404006240801c0406a03411070041511403800703480c035280c0c850401415000c5202d841c20740441541100350b00244c900040d41600038000c2140c942d5800540358010995109400314a50358010481c2d09110f0210b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 715412769 1250 715411519 715411531
    0x170601090503010612020a1a030c131511060907080307060f110a020d080106050304080703050309071a09270103120908060a2c250513140901060609030308 68
    0xd000a00c1d01d800000b801d4448a80003c042c0720107451506040d80342c0034480400070102400340d0a05590080d40003245440000d001e403180d41c0d00080c40301d254001e442e82c100010542c21611800d03c0d041000700a0200c000341c90448030f5441030384c001c1802c488012031060200c801141c02545440a55030300c480c0a400c0f5400ca5020086c2e03658450301441c01c5082c01843d801600d5406002d401440b030101070046c6030180c1158042240500c1080005600102114000380c1c06060841c0c40e9501e5401c00c1c0e190860980107101403030440214803807004028005440241c1003100d58000303840204001103584266400d050412128160041000c56a5840e00f030001c00b6076458807090302901c4a0702c1ca840e16105482d80c044a03580c505559000c603058503a0034081750071016403d25503100c00c005050340d4801540d07858811a8429400c5c4100c0108a050030780104805482550902c40c0301546200800e2201c0080060b84c6690001401281d01031151000366050398680d17104503803c0d13460848042d0310081403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 715414019 1250 715412769 715412777
    0x906020c040e0f0a0f0201110a0308010e18010606090f05060f0d020a02070e09070e07050703300905281a0a020d0207140f0f031b010b0d05030304020a0b03010303170601 74
    0x41c0c00f0301407609220b500003450060004609800f460303c00104071b81d00303032484603402d608000700d450000790340301103203a046440c9440301c0b03419500c400c084069010b404c1002c2c100c142d8038040c000241160003440340000c59000c2000d00c0540c99850061040a12652801c9a1000710800c4034400300000ca9000c0c01e01500607104607000c45032511010011240c3c261940e40b00790b44644c10401416070110b06050b48422145045400e180c5e980c0d07400ba140501b00c2c0c218980322007071480101860a4240c044000c138610850081c4004046420000e032031303140d405402e000c50f82c2c107155100542094080710f119855841103a00c0010010b58110045982c000740055500355020020515444014005045014050b140921010303010044980c50007141c0342e00c2180c00d0f04000340d0540c0e018404010348000c003000000d0054600c810440c0c030b500610404810503400203c0e0300002060000c004007841c402c074802d075040890346031600300304421408240700090001d64540b040300108125510340039045181810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 715415269 1250 715414019 715414033
    0x190606150e040e1501180c05040815071421090c0109090e12030412021513241407180e0703020a092402011103062107031a01080d0906020c040e 63
    0x100d291062400c6e441084400c4442e0014180d5405911604444403014100503140501e020751b61074840c0709607046008044204400522b80c2c2c0c0c0581e9520f01035500208506030381d900e040755041a04c4003507441c2d40081c0c030300000014051140000741002d0b403280c16110700590ba4944407158000e458640022103060007080c42c00c00c070659440000e1801540b0811040d003402c80d105400914144030300503c0b56103040308000380800c0b00c0341c070003400d03034000e4000e69691401d40710400c2072600711725052105460580703444035400203001000034050007030040c0d942d03211002c00c1c80c40346031b0740701500f0b40a0302c5070790140000800d8009011750700810b0540e110341070900302d0b203603a400c41441c52500c9601e0f04c4408d0005010706401c2030747c20701c500b040d103054a0801d54210700300070000c070b81e0413841502000c03035803022800001e2000c5820090f0000071540030810204c86c3d00300248070320603c40300b8484c0d52504c2c422100301c0d05a00c0c1c090106d680c00d5031031a5000305900c0101d0030410000d8007061052040500800c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 715416519 1250 715415269 715415293
    0x1051315151a042c090c130c0c0803131704030302120a031e0e150c07170c0d1e08092107140307030e0306010602121b190606150e040e 59
    0x941100d482000e24810400c44038456132010014980c01040809960000c2800e0341d40b65588522800d24a0302a18000801000d040800d5a10f81032180780074010035030220402410001e03205d000c00b0309070301c2082e000c001c0b0141c1c0d01c145c15041c01a800014096080a068602d2806015000d044007030f040745804a1180c0950b0039100c01030048546e020f201c152948500450b83c0010002c107529859100e01c00d021a1510178100009401040c00082494640d03020b016130840707026055a681c220340806481c8902061100901141c803640c2e818041c200800d50140303a13540c01842c00a05c02e0101c2c0300a0b00b9145007480444001c42440319410714008028080000819a0f00d4041c41d070784441c050086950340b8150402034140114108000d00c80d40c0b1040040c440140e000c02c0100390011400e560790f031136841420906800c2c000500a11007180f02c0d0482c04420101050a0422251300488003040196100c44200300c0300480d400803080403401c07444920072982070690220748024450010749107000154 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 715417769 1250 715416519 715416539
    0x50304020d21020f070810020949030c020f010909090b061306030519080f0d020901080a02190c0501060312050a020c01030207030912020d020301051315151a04 70
    0x41c09103800b81032440c0d4015001d40410040b400c0e0640c03000289207103881c0c500c440395120030840e0a14543c45d00070841e64290344458410342c00a44284840ca031900d03004143d0311441c1c01c600303804e0704403917130300345070801342e401e074150401909150590344540041c0c003160240306908034842020f504010000c0d6000800442c140300b4040078902c0385c203051280b418450b003000292b6651500c1c000100d85000e20800000307100103411451403001c1300b0301000280300c500b800c035442e0007966031250301d008002034040c0c80d07001140d0040015440980750408543c079400d07400c1e8224050384041412032100707041e145507007500a1a84c01c882d81d1007030002243c0b441c2c0300e503074241103030651807040380c081100031941c0d40c0126010302c50020020800e01e411800c0c241c50b514000e10007225407150740311000300c111264080d9111000100c420680250082c0284d00784410180700008100c0e03810f890504581490300c40c01d01d0b4501825100610060403440050300307000281a41005143c2d1151301c401c400c0100007a10303441d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 715419019 1250 715417769 715417793
    0x8130309080d09060207080309010206071b0210110129010c30320703050d15060e0d0209060f01050c0a05070e0901050723090306190b0a080d050304020d 67
    0x6035038080543d1320f0850060f103046082c3d0002413941c0c10601186600366400100c2c02d40c080d00b180380205032400c0d18003140b04603082405002c0e400c002e440d003070034003183c0c0c0080740100c4404102c2c0082220754401c0e6800706100243c56861000107121840000c0a980f10b00301e00020b442c05904c03640ca4200ca200007510b40400003c01407110fa0710200210164140c202c680469400159a24100312003618031007014440140440d2282401c0080340500a1602c150700341d64000d00c2c11403041000c3d00e080300c1c0051590b44135114a00001701840311140160070041e0300c04010b180d010b0320302841d5880d803604008501b00b010701c2c8a41000014011611040e03002c21094022602807400b521185081070403030b8401080007003004480d0782c1000140406070b58071807a81c051403184040d80003034290b040c1003143d2491003010450b44d40b600c1743e04184000c90302c148501c0c45140d09105020004503082e203013888405451440f0f441042e8001500002032107020740000c0da84a840202132840003141590703059100d0603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 715420269 1250 715419019 715419043
    0x307090b061215042909040804030b0f06030606040905030d181502041401030614010c0302030f12011e0602330a050603060106081501052a0a110f010813030908 70
    0x303643c04124078a030910b0302c00e500c0001d00b10200b41e40b482d201d40d075082c500f02e176140345401d000f00c10000018041c03009807000d40b070255900c0340b0045031504003c9181c0804400c00c0d59400d101c1d00811000c01d44514080c400c5581c00c9074040d0281d400d003040b1565160040c0080c1071070030003240180c40725800190400344010102c91050300e0040c0c446041c0080121014070809020b810f240c5089414816500d4401e0f5107102c0003024070b841c0c03950b03002505d0100d041d4001c0240740c0c650010081442c0764003070724200086040c0c1c1e0499003151101e900101082c001000c0314417071040541c02c4926000e000018009104015152002e844180b02c00c80c1e80c000014500100c3d41c0e04a4907075030b9014060503241c207001407030050501c4d02d40940d00341030140304c401d80b61043d8203096041c80000601500d5450380ac00da2440684050302200d40c06801083d14036032914200c10044408401030803c0100b81e20b08502c1c00c907c10481030303507041416070700c18696289100c00c120080d0b090025801001594082c01c1000c14a540c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 715421519 1250 715420269 715420291
    0x5160e1902250503040e0601170a023601080c0f0a080a02130b0304020f100203040909050a140609060705030f070507060b0307030c0f0e010b090f15030a0207030e09060307090b0612 79
    0x5d458510f0840641e0b402800c81030420100301d100721280c850506030140c01608800b0010780e160000c1e400500c59191007034502c800175400b2505e001001041d00c41c6250000001c1e25541c1081d500d400748203030743d449102c81c80f50500d0018052413041c04c1c03142c0106036000040810040c40c1003600002c0350500e5140d070f0320807482d0690010801c021810000d00000310300030251428240b40d459000060340f01d02030b80c00741000090390703904203806001041040301041751304400402a024041740c03005484800855000195210f410301044169114a049070300c14101c0784442c2c0265240c40f00101c07050360024405030344081e1250036100d119642480441d0027175214030389104c2918a0491711030794640540d80240701c4015100c004005035031184003111201e1804459289050b5403010018203200c15100c40030002e0100401000034035007856004200a40c0680c90794a10040750104006183e10200c58098040d0041c003010020680c0d940c000145034000101400e0030014016100180d541c1d0031100c1103a84 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 715422769 1250 715421519 715421527
    0x3060d03030522060b150901120c140304150506010503090703020d020a1e14060406022508070305030a1e1e05160305040509090a23030d0905160e1902250503 69
    0x82c82c2442803030107241105403000707003009440303800a4200c284140f0656034035520ae98900103818403400281c1c181250040b20140c580c100f5040c51221940000300c11410705141101042280d0b004105803880340014000510b446425a424095105a0406c0172a000f40040c1030204418652517071399801c1840c6a1651060fa910301340c02800002491030402d4010b050400040c42995404a41d0b10340d81f4444840300582c10b40e64407003017030710f880c0c850f441282c2d240a031940200800c43c004c00104003940c0140c2c2c4064174034145000d005002d9446e44c0d5510082010707101e8aa02d410b09034050445405130504005040081d91108102403020010044000501c0000e0034030aa142c412545034020300130100524002003140d4800202c030f04501c80a0f85402d200c981d41400451040084404251441809004085061030043d60751a98218802c40b00010039002007501034800c42094480c8950200d284140418149650002e60200440b041c0c482c1301e65000410840c07000e60100d0400b03210b40001e50362 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 715424019 1250 715422769 715422791
    0x50f0709150b071103030309100e07051f02010f05150102120f030711010f0f050609070309020114090f0a08070602060903040b0702040f090609050d0306080303060d0303052206 77
    0x414919411038100a0729040044a5a94103000c59200b07442881e505240c0d10700003410705a40c4d2452401c01c1c168144800001c11030300c0e01d800303d00c0c46142c6216180a02800194000c52611003141d03016558000036000100741004100d0b00e1402c4480d075660000240d10145d030361901003a541c0846840240e20701050802c001960304001580c1108a42c2c0c41130b03400c0c20070791403900e034141c4000350012041140c40e800f0140101002e500c41189281e500342c08102052240361801c000c0c010450703060b8032454a41e000508640c0c042d005206036207074143d4070302d2441d4901c01c0030007145820007200540c1086100000004640b9030203480c8001c3c000c90b074000d04940e0314000d00240ba0540040401c10395801c00d02003081410107000607946407990448000c120b455203601414003c001040018004504092a900503c0030114083c4040c04140c0d80a201550b15600c24642d2840107898582c0c200c150500c904010a210b680316a1300b101160208000040000302002012080c0d04000e50310641d445403030703da03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 715425269 1250 715424019 715424023
    0x80309010f02061501050a110601081c0f0806090c0d05040803181f39091e03170c0f0c0901050f0916030209040f15060302041a0706090f050f 62
    0x401d4100078401003441d85040c0602481907960208014180030b408201c90182034003030290b200340c40e04a0130880765150b070340d103018554400ba8041e980306038050b6101d0f6018200d1140c04240c4401d013094450380303d113898401c21302c14502c400415252200005003c3c02c4403021441c0212802680602401d40c0c072424085280aa0319100900003809a4044522800d00108420701004000c0d20454006040401c605003602204075400b240f0090450515241c00704003003451211380001000c0c0c0e2000b05007900c840103694000c0385001c03091001000501c080000804070b05610162101c1490364a0400c200f40010f1458410300e00e103103400a8000c0c010071602d609200022600500701125110754001000c0d010880c0d000340035106101d514030304906110b42d40d02940450b003094101810800c14224a1441d282c014401520309060079920020002070f268030900a94098a16400440414644041a99525a0060f442101e5450b10342e5034880101e40423488854240b402400582003000c40c04101c24 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 715426519 1250 715425269 715425287
    0x6050d06060306061d0a05090106030b070203130603021e1b03040e0f0c09090601030506010309021c0b01080d0f080712320906060d0809060a090f08011103070c150608030901 76
    0x1414102045c0182c0031101e000d15081ca800440f00c1400045985400d9170042c05041c0e2a0409014490200140400342d40c2c004001c00882000a9030418581e032145c0040302a0300c510500e411010365103840200401c04504002d101c03c104100d5003145000441107000e06580040d40104444642c000401c92910f4444503020740c00901300ca0038034544410f900c00146c01081c0034203000d040650b1500011203c0c1d02951052000716002020112162200309481d0340861040d2000c0380c508290b80000202d1030000640c041c203841041d01c071140d000610820440729080001d00040c104002214002c0004919100b1103c0402080a5144030000c0c00413101c2d010380c0c010b003a1101c0034000c0074200311120001003141d0f030700040c0c11540c0324660b03c2c03a4201072105d8081c00c850f09030b020b040040d4811220303802080300001c541041812034000c0b0341d40d002c0c3c6401c8802c4580010380301007003003002070803013442a004025200d10506402c94090340c0d00303040b10202d410329000f01919600000e40380203190b070402c8020f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 715427769 1250 715426519 715426529
    0x513150908010615050903160e2a04050d170703020106170606130c0c051501050906010807050307120908070510292e181508060108090106050d0606030606 68
    0xd00103d440d0042071300c10040590031907000c000300452001100c7d6818040f500790204103118809145486084580113118196a85407040070048080f00a0400b400f882c51007001c113200e075250409150a060040801411030111600704400750718543c1152000090905103000f41d00000703030359062444210b10001584005090356002d00208100c0d55550b45554103504480403020980480d0030105680c4007030f190200514078044c5180c100060b81d1541905412180121542c4165480300401540c003c20151211400214100006540303d4003465100007000e40403400000c922011b51035861240c3c00030101141c03607400c185250402084c540c003404110801405c0c44165080401108020415441503024001e812082600110500780d0b40401c1b2481109240f00c40f4071000160024074000c1e040c00f0a40d881600c40101007000321800c411800c0603080c5072039016071600e546005481000000f024040039648031003001c00d40751915010042c21602c074000105840742149000e07001e45140ba042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 715429019 1250 715427769 715427771
    0x1a0108030720060313080904061d0105011407060902031f0912090602070e09030904110a11010b090f060d0c0f0f300606230f04050411010e01051315090801 68
    0x403445035a1214104c80e0880d006100c10b4000041620300110207000b154580c59000d071a10b840080c03880441c510720040c03961041880c09090380c0724801503500c4407030f284c4100c2e440c00040c40904009034645e400440704500040480344000340b050700c54418120702550481e1081d45400035942040764007802c84180a100e030030100d0f034480c14094025038488040c0b203802c4002b070600300030a2219209200310340316041e002c0c1087c0b142c1161032940c98429403020100f8030005c0e2044000e00145041071054588104009040803460b8407001480c0c0341011021700b80c0755000210040390000650000c20721070091500d498160344181c0360000301e100d100b9441d400260700740d601802c41405c40340c07601c1c92003080c144001001c60b0b1407081810440f00907c1c1981103507542440112501860424074000030a10043c00c961203045a4030300b42c144400c0e22030594004024044842c412501580106000c224010044c5803240c1001e4036009003a0111071180c1c800010280c02150700340c2d605034806400b1000e4031718000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 715430269 1250 715429019 715429073
    0x9010c08120c0d0c030507020c131803091a03040b0f09012c0d0908121e070606050418020a090b030f19142a04021c050f090c0a030209041a01080307 65
    0x20127510b403034141c2d032500d00c2a00808400001142194850281c0754115040341000340e16501e170103055000e00b4010790303d002d108005030342002d20743c0008032441158804001e1160b5124112094000c25018044c90415500c1c2c0f40e8241003889081140b6414146540d88000d0802d182c150b06400d0280c9101076604200c11504140940b410000d22500108803d4080c2542d5040c0b4000110032013031404414004004001500070034400c146d00103500f940c8044074100850103500e0221041e04843c800c0094215025a0081101c00f4080d4401070f031903980a4155001e60304240003a500b080094102c514503d03821009180c284450901c0c1c00d141404220300416001400041c1d4054000d58075840a4005d030300303e101d508142e1a0380d0143c0741ca5420f13020708107080c0c900c0b0005500241404644440380318205200060909000040c04ca1404c10041d00b0781008604640900000c1d60b80100261025004203407002c941d84003c85800b40203002d084051615041c0720300d426140010b503140000c2c1d00f030182c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 715431519 1250 715430269 715430281
    0xf1f08160903050327030d02011e0204032102010b0406181d060103060b0f040603080c010b0307060e060d02040509010e18010218130f0e0c0414070509010c08120c0d0c0305 75
    0x44600007400c40030071045c111240e0130740d03c64903000d40070010380500803400300340c100075015086a55525880c040c0007a10b41641c800c1c400482c0103c2c400034010f9a03907805140350410b1001d140d03150740340451002080b2110340c5800308080d2500c1d940304117442101200341080d054030b6441b5a04155040000241810303603200b109a1345c402042c0000b402e00da1707460640d41084e035180c2140522401000e0000e00c03203290740c0d05100354181c010300000040740d401d041d07014102d03180c01315aa070280da81f50303100c0307141612072401070200e0b0b5040340d00d0189600d6030070030012902da92003180090003800d0048407400c03280351407810144104400c40000200780c0c01401750200e1303c0f07407950384906002019602c0041900078030114101804505050003611071500d014940f1180001c11700000b0b86605480600803200000305c41c045844040f140b003000100d051041440d598400c407043d04403c0e0040151a06002d0074195548817114162000e4412907000661041c03600c00c603010b181c00b03200290030300b000300380307800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 715432769 1250 715431519 715431523
    0x40e0402090a020d05040c0e091507050906130906030314040b070b0403050d09060b12031c09051f06060909200d230702061605090f1f0816090305 64
    0x1510080c401c09214000a0b4148065419134208005000c0f00b0b1100c3d00f0141000142c0c180c0c1070088051076a1729000050021000150300142038061400030407070340d070f1100011035283e085202110361140d0708200b80b0581486440c0312038040e01b440400040e000b0307e10b1030050b21600c1100c02c8a0591b64052004103c000d07880011703108203d030407919460045c0c0d211700d2b044415101d800b0100d514280b41120700014003c00398044204240c090340d40740d800780740d5103400a03079034040c9a8074a0004001d883c04a485a2801c0e00b003051003511031800c8071041144210031115039408107a030540c4280e5269000c020031903000a986004020a00081201050304801c6500744219828105259030740003c50035000706060340949005601003444440301070100d0b840c020301c00d0040d01c0010042c480c180109848100c3c03450f5070f005080e89e5898003441d054004080c00340c1038003640d01c9180c0c480c0e6015400c49016031031314000d14a6080e160b468070114a000029400c52500041c880e038100a8100f60a200140c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 715434019 1250 715432769 715432771
    0x90c1d01050901030207061b030c0201140a150e0a020a090b070b130809030a05150609090d080606071a0a0c05091c06090501061203020c0d1101030c170c070b0c040e 72
    0x800e1070055614090180140d0191040040040c001803802d80820341840224180300510191650103100000743d0020481c00e8800c1490020183c1c0e0260f40803503c2c090a542c0444420004038140a681075075503000c4030004a800c6410060039500040d910000661209000014020300e412031410015a9120703036201100040c54099000900d0900106120110040d03622094008040307410748012450281d480305620800c1210079900c070000718610340f410398072a0341f0403403110000704a903084201048030403903030240c4650f0b0800c10400500e400300d2418021001a1580086480c400381800d208030000c8956130007100301000410702c45480584d87c0e5000307034071000d000c04845d4002d10100717040080091441c200010041d618103c00000c010454100404c0594000d400380c8401e80c6030401401030200f000c0c100185000914801440158029401a40340090f01e2070f001401451528000c102d500c03059030540360040000c1044410000c9140b6210351041c3e81c01c50385400c040c0b90211002c52000c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 715435269 1250 715434019 715434077
    0x418030831150f15030605060901080a08181f020f0f07060f1202030412110f0307080a11010903080a0c11030d0e030d0c0e0a0b031308090d0f0c090c 65
    0x44025851082042c2c0340d0008010b4a0b1507150402013503039079018958003100c40384001c8448500709000900d42d440e04152031412a19035002900c50701c04140e41c1c03c1615401001e90b008a04402e10135070380140c403400640c0710180500d0f01d03a5094403c42e00030107850314200060941969008941c09000c461001c103151003243c00504142862885040f010380d5080d108200341c1740701500c04001c00c014040700e0481c5022a0071961505005519035400f00d640307840070129440c410368410040232000800c404000d1848440c94545400c03607608500009080d1580c048042c0d0008040310244515243c403886220b5418105040006408601c255400e88a0085c01d00141185580d031a61080035032041c03048512070901ea4400700314004040001270f205019541d20140540c01030400480c0d03199030307035003100d01030585440301400c46001030f0b45034100d582c01720035040e4100740c0444920780001e41e0100e20317141c4c503032081c010a2411030a0510200c211442d00d95a9010040352042000903008900ba80c0c1002c05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 715436519 1250 715435269 715435283
    0x31201030c05210a24050a1b1704030e040209031504170406091701020712050c010606170402040e0723040b01030c0507080d0615030915020a1d0418030831 68
    0xf485018840e48a05c020003100f01d60a81040c040144a20b900c0e17011401c0f80141c0d0703e1440022140c10720071114103a0084407151400c4a0001050100380100b6290000e10402040545441c1c0d004010034101140c0440c01078084500d1000c2c0010000308411001602d203d076103120f41414030f0134900420a454074070403501c42502d24241010020401c0d0122205180c01805502c85030b05904030003003d03940100c0ca0a443c6500e001c2000c215144a81a00c0360409450410519192516005c000c02014094440f126a01c00c0383c400140e100340c504005c8005565215540a44011110038002a510013a10b900d04244c548809640c025421a007694103080c0c001380c4003625601e020b00380100421003900700352007000e0801c05125089030306810032003c040c0700b00c0464001c0c44240018000742c0c003c28031000007242400e444110001d6080c0000e036a00440100042083c46040d41d181516107050700c0d00350000342d1003100300b20107801c01e2509240d01c01c10301c0c0d181a04007890a0094400042e060000801032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 715437769 1250 715436519 715436543
    0x20406270506030c03031314180610030b19030303140f0106181a0702030d08010e06040c022d07060906120c110f1e0a02060a050c031201030c05210a 65
    0x507403003c00420f0080790b00901200e603590042005040d01187c1c511902c0903e4203038400141c0903003861098103124030139190b8600e8450b2140c008100c000d4084042c81010565285c00d1181603680d0050021100c0c5401117580c81a00c0c114200141070701c1c01c8a102110000d03070386050005c0040b40c881d05074111a0240790030751031005110307191030003a030345603015241940400001c00803150404005001c00e5200f14200c030302078410820107840c1600240300d03c0e803000e2041c0000904070f081503044401c0092052066400301107001000d07001a9034004010300000b2001011005020401c008410240042c3d051101005140400050501007100c07000c118058856181005860045c01c0100182c42031006403910f07100107420069594403908104010b02c12010780c205d9940c140882c005503040d0700a401245003071040b00c07043e035641e4071100f10300c0401e1200300101010600d41410503406140700e410b410303001c3ca02e050100018030951080c0050582289070401a61560000d40c0a0b9a40d500640a08030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 715439019 1250 715437769 715437781
    0x7030f060507090e01030302070e070c051b010908010608060405071a040b090a03060f0f151d0405070e0112050c0402040b0d1d0f010b0a0e071403310204062705 70
    0x102c151161300c08800b4688050010040540100f00e000c2a81c00000991030b040d039403000212660400c8040151564002c102050300380840281e01c1055404103040400c140e582e1010040c0c21100c207503001c90103d07017041c428001040000d00a85000300301040f0740103507411501200891601c10740c0704101e03c44000084803141d503165010740304020340d000b04041040e0b6441d244100090426070102c00c100c4c0f440c0100b990045128090b400003520f544000716408002c2c0c0c26502660004040e006440ca0301c5092800102030f030790840c402c0e0181200b4070f8260150180380c5071651400480320085446240140414058209510103480b003d200c3c481c0042814a07461083c95011204052000940d016960101e0740800c815004128501c20070380340c0400680d610780303585091007400c0d120140068903400c3c0c80001c05007030001440d0890910f00e100013128050f42155640c40940c081c20f003004842d4560040c0a42c82c1031700c0754100501182d91681020842c1c1401e08181c0500c2e410700d90b6540740e0365030100f20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 715440269 1250 715439019 715439027
    0x8010507020d0309110a0e041109220503040e04030f020f0c100f1103162904080c0c0a0906090b04050702032b141603020f0409180f0c0501020c0307030f060507 70
    0x100707001c1c01445046481f0048520348802c1240c0645400701c41007014542c034100f03142102d06c50303400500d004d0608a100b4500c040143c04a10307040d1070b02c0c4010310000c1040c2a8a6115901541c030a445d400040740c03052a01034100071554007003010700e400048022846488083c0c08000454081c41c2c0a81107889160040c0c4107404102c0f80351060b480040b40d502d10582401d820000c00c0c90046403000d0810740d421102c040c008041c1640e0042702540c1c64046800209400701500b40710301d15609a0f413030002c05801180b5000030643c00403106685682007041405001d101e190242602600e0610451030300500196032449903c5411840c009400c9241c16008002131800d41e0946648200f40800109440c5001d2008001e407802041c0d040005554020107009100b2540510000700740e05080900d00702c145401030a84081100700010004219030008000c0025410b010b03210750425007a450800e0f00082c64140d412070301c1c1d0300941c00303c45c0a101065648075a18802680300c1d101140c2c641e42c3c2ea004039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 715441519 1250 715440269 715440293
    0x3020102191b060801090b090417031305030711040f0c020a08220801092108240909010e01050106180b0a0c0f0305070209060901181d0d020c0a08010507020d0309 71
    0x103240032040b4408102541c0c0102885e048808108050252000d89001c018038020142c9005043c82c13411032004c4059500000139650042080510319141100c0392105030840d48000780c00c59481e95000c1e050045440c041c800d6004403642603208020101c42090301958a41036040301406480340410842200c5401610032a4610701080c102c0d0100c1e0f0741e803d41c2d07a02900f0058400c07030f4210380c108107440c1c0c1110218012404000b0694031103031292109008040050328070f07140a00404000c1d00005640d803120200c45000b000c03080000103000b20541d44d80c908540e41a08180b0402807a607071807162025012141c1e005a440c03016001e82d54189050342900d4850f0071600003130068072038035200801d068216002e040624000e641c4036110796507050401074204002d010380da850003d80d49408040c541d95600c070400b0401e80301e40102c02200312020180c9485240d015030801644a08101c1c280ca081482203000200000ca0082c00182400c1801a40b5000c0e010f90b68802c01d03649034070702c4081c001e0403d401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 715442769 1250 715441519 715441553
    0x1a0f160509150904060308090307060e0108070302161707020306070e030d2d0809010b0f0105121009060803090a0815010e070905090412030e12030a091401020c0718060302010219 78
    0x810a00741d45e1f1a0200068201400c07452080c010101c000403e5401116240003034181627650b04401d035551041a00250400d20243d83e800034040800d0f400100c0011040c88030760b0360f111287c1e449402c80e2042500c0c044004000301d003007000c50b140120064a000428121400c224104000303800b040001c10446603a44140085007554060400d20a00e500019894010031507000240641103a900a1041c54900c05011034005201085480000e1404000194008143c45040c8403401e5071400c1c00c1060390007076000940d486c0c000003080e400c2d91078160303150001405820007410034032141d000003050f240d00504c1441150212803002900040c40f40d0121005450700412010203030a01e42000d8294408084042010a16003c200108050005184550382c00d1030b401843c515a10600c206019040080007110304207440c408a1640f90000e0014001000e1030790000c01c2c85604d00784e03c0105005c03c420007120207901e0040c007880580d90212350b40740b40c801102c2440d00c034202280f50080700c0c41d403d0403907 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 715444019 1250 715442769 715442771
    0x61202070206070b180105060604090903032405030c010201060b09060a02070b0705030d0b090907180906090503131a18060f0c010618060b09040510031a0f160509150904 74
    0x43c05080140d100c030031602421054010404040c82d0605c140d003220380503121164000c00501c01007000720340c15000305640c144a1301d00170980400480d01c4a07201000a100b000b40d825180700280154282000a564442d0b401d00c02800803602c1d0541200b128401c580400c0c1c0917002c00031f0829002c5000b0000c4d48004d10b403a803e001d0303603520300781085034403600700181000c1d04604142090107286404844a4040e4145901620b865460904503c0d400d5041c1da200400b8135448840e840302180f201d101d6034049078001c1d0069aaa111356000c030300c8118601e81c20207100207a08156210041c04850165500341c50440b00c3d6225444181c0000f940c02c0c064924820b00c000b00c0062040d0700130350190401d40c204c0d85905e0502c0020348000c0380402c15100030740284c00d1024024040006240b0701504980d030000c01245a000ea0107840e034442d40c5000962064001152000710240541103110041807903200e810104010850551101c000701144900b0b4003440c420740701c14450200440360314080340c40d0390710f000300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 715445269 1250 715444019 715444027
    0x40e0604080706060e01030201080a0c030e071707090c0210110706060320040b0d02240307021c02190201210f0e010b04092301110301121407060504061202070206 71
    0x500724100d503115038011140281004400562411080d902e2816298140c50340407030360343c440e00100020314a140140d410035446002500c1c8070340003401240302400d441e0811842441d12041218602078455201150072454545d2581942d41d02280d880202844400c0100c1d900c8080d9070840e60f5400b070810064660341c90988008100706048005955000400c8140307207205815008100484d1003034000d86070040084880d4200610700020041e2414118226a5000005149200030250011900b084c050b84c0320301628000c000030481013030203001c0700d0b10080607140c411020034042d250410400a041c8441104202002e500c040d00305c0200300c8491804001022000c04664041c2441d601d04c9070043d4600245c60b8603a050a02507200002d410852421419000f44044202640c04903022a400d5583d071a1022380c000d80348004500078079070000324414005880c20498040c03c0d99625001d4130342d00c01303076081101d035800070309030740456007a801e05a6140005510820103440b84250007984424001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 715446519 1250 715445269 715445273
    0x7020117363a09090f20040302120f210d0c090f0e060f0904081909030b0703051b030603071d012103021b01110d0206070329040209040e0604 62
    0x10b928142c1c50401a050060b0082c840c0428074180508030710140004621440a204a012942000515080c0d80600207040000d100030b45d5095020b207100444054000a03041055240411102a4011151014114069448403842c0d6609e00c3c0740046000c3e01080141620300c0003c000c291100e00700180c80501907225148030090400300c2c14000c194140580d0b030030100d01004078501c642e2046101416440703d410328001003224403080280304841c005010008940300b1802c6007071039114920f540c0c440400c40390a42c500041110070003000740007018034001c100001c2c1500501ca8442c5c98160402455490311403101013810481d182d00b0110200384e1000401f4405040b0000700c504a0b03500e104040400c400400e03403010700b0011100080e00507031004592011410f004000584e8018050400c41000b00d43c0200e03084c1001821041400503802842c1000f03091a054081d0520b0005c0b0041c0c200702d400780c80f1303461841b80c0170380c440d200380076560100e1500740c82e80b501c0d406248e044407040122410340c03401b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 715447769 1250 715446519 715446553
    0xa030f09051c0207060e01050f07080715050105090106110607081f0e0f010501050405010906030b0f12060603010c050c12030406090503130602070f0b0901030510050a0b0702011736 79
    0x41c04030100502c21300c4c50001d009441948441250300c4140e65040c0b42911035181a0200d13000352106070f45841c01040190001480b02e000080e050405540c08115989401c041141c0d07010f05a100f401400304204042441000128041c1d80c00f00c010f040002003510355003500d08140041c805110040c0e8904c450100c1e0084440104034856648808000f4160380c0f01d000440d0103020f41e11a007404500e0114040c84006c1c02900801c1c034181e0003815086074080768600094130f2b050000c40c0482ca6401100501995003828000c0740c00000701414528a041c00003210266505c0c0b0100303501c0c1380a08044081410010103400000301f2541100c21640c0310014070000884010a6101c1c00c1e0240c8140b10001a0349424600d120046407000202d03203050681010055028000091005814446080021496030b03224100000a000715011942d10b62083e40f00260404810341081018504000104003041c1c0c001d0050824002d002c1003882102c01411000e4007181c080c000d0441c219002d50706180d501e110007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 715449019 1250 715447769 715447813
    0xc030203100b0a0b070b0c0a0e03071203030b0114030601111603030e1206040803070e21030d060806040203071202060d140a060b1303021005090603040c03020f09010b0a030f0905 78
    0x2c1215000b81c0c640d80c401140c241c0b44210329000f8400c96400000441580d0301ca40900b000480320b00380102c070780b50a80b0000c1d00f071501d25001002103038029130042050550520620307402e070700c0a0030810015011080308541e0303404001c1c40c0718100503005841d1310044400744502c00840c103640c0202c0340b51648078a80a000c0801c200c03009409400106420b05451400051250085403c075044628507101c40604030b07240622901c0b09900640e140e410595951011401906040e0781c61000d1500c49850702102001e640282d070000c42e50390721103c10b000c05030764089184000c5601201c00c2200c260b1903840400c0c92402400505c4004c03501c0c000120803000c240004081c882c04800400300611030301d8141c14400350103414010251045c8508090005041c43c3c800030b140c9044509080342041102c0d400142240d004880c2100d80c4142140c00b0000c6050201c80302c580c4120845100d406981044180c00b058003409901c0810035848840304c00300310125510518210342c001e0291021071003005a81d5802e481 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 715450269 1250 715449019 715449041
    0x13050c0d02190e0303070c050f0a0302130b01031b020c040f2d1107120e010909020a030608070e01080303150f0607060b180c0f0d060e07020708060a0c08010e040c03020310 75
    0x40f1400c5140080c500401190440e036800760543c18814107010a028003d0391140601e84c0083e0300050200150b524042401031124040d0004034003200c1100005064428501c6012191400e1000d002c48154000c18501801082501d0010b20100f102c10844080d1005130030303d1301c0c0d0030030101d2a6110001c01086e604544100441d003404040c20045501c0c101e4490400c1c054405501c04107104852880340c0c0c58407541c5901403520f101c40c2501e80751408100d03840344000601203640c8060402555100388001c00c01003050310400b0758030f585040304154076803100510302c020110517a80400300c01d03620b2212141002001800c400d03201c035003610b4078600030003101000910645035074280d90400360b4445160741c441c44101c41ca603810202541511441034100e42c003030b0604030340c80702408901d01c0d0441d045944248040c0d4000d014261522400c0d60500001900c140e40190805240c40002c0e034000c0d2006045403c4201c00041c213a40318142030741c203001755400007035241c001d4090759080d03c00580c10a0f03550b030b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 715451519 1250 715450269 715450277
    0x4030308070507080a20070621051b0307180e150d02010e06070c1d160905030a020f030f01060306020c0d1d01050714060c0307031a13050c0d0219 64
    0x1440300c500c140e03001c3c02440001018141c0c03c2002181c403900c1810a4440c0342ca8083c14240742c2180010000d050003004d80280001401e5580305c0c1c120100f41611102145030010b04c1040b45080060a4406a00d05014001540c80002001c00c50310b078840c06100b030307910000c00008002941c80d400c8214414805551001e1642d03007a404081c01850a0b403000c05455605850340441c0e03070219410b2100c01d800007141601c1100c141c1c1e4001500c0102d640660400780c0118035005402e0dc4c2c000c400040e40800c1c004182c040008008083c02a81c400140180c40c45404888503e014030141c3e0000b0310344034592040d0517055080080001c03c10443c1e4018205d0103c004081d0f4001c100040c10407591484900131402c1101351240080c80d15501907802041d1190059448074030640d00340e0915803400350305031886401c00c01d0020401428980c18820348880c441e4001d9940d641d0450900004c6100414000c0e0300c030850360707403800b1a0420803814211817408901000640d2918420b4207030300c0d640202e002d07041001c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 715452769 1250 715451519 715451521
    0x12080610030b0a0e1f0e180303010608060904080c01020c0703050132040f08030f061e01050a030c0306080726160306020706020405060c01020a020f0606030d210c0504030308 76
    0x4240240142224814007030b080b45800c81c13900e020b059041602502a44925191405000b2003000100c5070b1400b074540416600f420f41400702d0011028110860300c0403c035003061006102e4143c1c040c1010b504034004403014070306605c0d0303414080c41d80c0c8121708105402c0d600c00286c1e00192500880c400040301e014100802c5114281000104204010760720500d0180c00414005402c1280416054210b401045070400403080d41d80c070300c0e403107074025901524103a0f45501000100d00e45070841c0d0201108100c0d03454014042c0c180080c3c0940140340403241459103d8483e049520b00c41d9000710000c0ca00031007141c0101c3d03030780d04528020000b0b180c1070250a0880203140ca034050400140a105030661040f07500c0240c1c40c5840c0d420082d00586012034080340c0070040001c50380d03642c201810500c100c0d0000140e80d0980302401a241c403d20103c1141c50b41c0001c010401965404207211402002a0a144c0400d9030166403590410040c0d01d50f502c03910b440e00b240000b041d6800005081034038800d484030611 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 715454019 1250 715452769 715452799
    0x7021c021b0a0f09050a020705030406090e011d010303080402010c0c170f0105060a060c11060403032d0f051b07091b02010603020a0306020a020c150903100e06010e040c03120806 78
    0x41c0080c1c00fa001c0036940f516010000418164080e81d8008421500142800510b5840c2d508590141c2d000c1ca0002e000180180002e840300c425103801044081401c1c03210910028520390091414840541803240c1c00c400101564003600300c99a21660203603c50700780d50703112000a028034280c0701c150800c03440b48580300b1103101c4051180d1030044000400036201c0038079200b0708030f845040b00710046038000380000300d2921f41c0d00c60360003a0001e50307c81d45441d020710010101c0058510001104081d04c002e84800000156400203840e2415501c1c51525079901d601d41403c2c2c0800b101e8840e03e401345403080c048000780304030050340014610301038035410b00c000130240c501c100c4c02e0341e081c2d00003e5848850340c0d6003000060060790042c091241c06005503a0514605400140004001915032031a0400090024110315003417080503180c05200500300064400320320042d07544c0e0ba0500410a40d0341010011405104440c8010741c01503070b000600c86501c520b41040280307003400540e500da025200041d90842 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 715455269 1250 715454019 715454029
    0x1502010203091e03070602030f0114010315030206090f121e07060f030c0e13060609082a041b0309030e09041a06060d020a0e180f0f07021c021b 63
    0x302491030000200900d60354590507070f040b100090001c00e024032041081c800012580d0018500c142890552000301b1f61500140001001140144d94105407901c46046203c160441409044d40e406942c116210203003280452444075291855a03802203d0381601000d0031740010700416005d0702d030040604908260300e0020756034083c500850010400c44404420198880d40c0400c0a0041ca450103c5141c3f42c8040800d164000f080c860440c00b6840350f02c140304aa070040000001400ba02c8000c04240c82120048886490110740d40c5800c1d51040038642c6d03240d07807560004544600c070300c5414800000e611102400074406440700b20041a8101c0c0904400d28000040701c0c440e07904902200c550040061a044203000000e05140d446502444884801542480980361001d9144c03248102d1a100c04108100907128070012008040e503003003008082c00e02800c120b90402e03043d261b41500750b2101d0034141d0804c603038084000c85100000070403200d002d07800515179201600039965003080c1025042482 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 715456519 1250 715455269 715455271
    0x120507050f0612011701021902160608010f121109130b0f1302042d0c020c04050108030f0a02030405150403020f0301050403020d1b0f0c06110a03020601031112070b041502010203 78
    0x1c0c0600d251107004005240880e02000417030060b8030300040c9000b0800089258048100242400581c4a10702292120700800320010292440c0c0c02c140d000b41d03141111611280c040c0707015240c0039a842c00b41c928204885004030000d840802402d1444601e040004450600b45400e42070f1a41030000c404201c108640a000070b005504208019050003910340911019240d40601d440e840703402c0108004004003102c3d04d0301d400305000c580101d114245000000e00c0c1c0030480b107007144a54a054010841c000000088842c64003111002c152940490340c820390460165901064104894107101851400480c1c000c100341c81c400c980b82c0c881c421002c0180f600321041114010050780c01000200e500c43d0142e81042801c100c0480b41000c8580301d592a00c1401e0300c0c0300c500f1107030380504040a0140c903130012a00000d070109980100261a01618020340e2580184005420380110140d01c0c00c503500c52400950451080c0022942c0242c0d0b01c28880d0b641b035000d4400d95029040810b40340f140a072043c0200c13 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 715457769 1250 715456519 715456537
    0x70e0417030405030c010c03020a020c0f0a05040c18060216060503070c08181207050117160e040b19030c0b040b09100c12080402030d03090812040c120507050f06 71
    0x6900220300044111040e40060010780e2240b0040c00840b0408009004400108025650141e16901c015602030310300080050103a10850503109642d007030385c8801403c101203500c00c46000c07034070451944003030364503c3c000480798003052009107011a43d1600040c3c2002c045000341c0781e01c1c03038081c1c3e11041100d6900050764010b0010301646554408290780328090480407041e408001c40e59020540054280000041d4040c8942c000940c00c0100d50b801a007000041c29182446d11460314002c5c1a640190140701d05140511401010200190b169030f400b40e00320780c00107818007640511411460014001c82d00c811210b0990145010890301c4201003134a017203907902c804160410100c1804c004070105410109420401d00840480200da41c907030941641c486507440303800f07460400e03006140c18003441950100a040c108055900007450200032101601158540390400c0e1321989000040c0700e040d51301c00f88500e0300c1ca4883c2d4040c0b00012826608a62040f070300744081802e000c041c0b0030b8500483d080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 715459019 1250 715457769 715457783
    0x30308100510140903010c080a11160f0c03150e0f03130e04020d060914010b061c09020307080d110c040c0c0f030507020310050a1a0a0605070c0b0a05030405070e04 72
    0x25506640d00807180054468044542a8240002e580200c2c4c210307150a04280e00180060003070010320100b61183c0103070500180002b500d0005a8031244208102421000b080304032901c0b000e1007401032424070311002c0e40e07005000b280c411081010303c402401500407254040e000d510482103911100108943c0d110800700c203121211840c0c000c01280c51b10f0001c1c4181d070860342d040940f500152035407180c400100d2080518414500d0f0064440c2e0845000803000c0f0702a407010001040001582103c1301000c41c2c10b1200403490702d5051002c203040c0011680800c40a00c11486062000d40c2c1007224405c0c21808601254030550118040000360f03919668054003194001c05000081010b030650075020380d0007820034511f0700290b42d001c0303460550070b1030820340d400c0d41c2d50050001c030812901800d0422035040c01c0688801c0b910070001150000d05216410902c0740004a0408101403407001c3d80082c800c2d000e4031511742d00345000c06001c0381d0048800b11428050054041902a80142218080d641102c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 715460269 1250 715459019 715459039
    0xe060702010501060828090302010225080d050703020c0a030906180b04031214040803120a0b03060a020a0c0c150e030a0b19090203010c0e0a050303160602090414100303081005 77
    0x1000110b01b4003031144031542241d00ca000002440d040c0c02220982d07803096000607500c01000c2d41401d84032020030403440c120003412032500040b540f4941510b0041080e0940080c2e6074a03500b4083d0000c2c420303103242c50454058850400c0525420620701c6c01150007503124500400da40d5051001034031075034003030018100c1c0d050000780b0100308070b40090303540114135080c903080340c00e00c1001501240d00720740c0c48800b40340d02c0081c00b245404450b9440343c2c5c201c4280350003071100060b890000390b00c0300070003088009825800b10b00c29292510403400310090b03135001044140040c0e101c841200103074503031981020209124078169600ca08002443e8009a42c0245102c4c605d912000c60700f140c13a000c400c0c07140440d15180d00034400540c1e0b0a1040700551252522285000020402848180c1009610441c07080d0000c1c00600d41c8040c0240032403030480d42c030050041e520380c130000c00140140311a00004800740501d01c100b05d24200031402120580380207803640b000d00d56602c440c1600c422205d0107901d8100040c50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 715461519 1250 715460269 715460281
    0x50405060912180406080304080a110d0f02040b0f12011508280f080c030a02100c050d1e0504150515180621070314070302060a2102030403030e0607020105010608 71
    0x1264010a800004e00101c2d0141e9103a0340d151464015404c4940141c00081d016010084c890399070350660700065594400c3c4480c44d0326100b40ca00701d00361010b8055501c1e2003245581d60b0b14944a00c07510034004196000360001c02100714000c10000e80a46403c1d01d20840220700c2c5500003420b107810041c04080c0d010106401da071951030980e8140002c907100b0b1000034503680054490f0000c3c1c0000622080110b48606d0306400080ca4600624403c030000303440c2520805202d54002c0031180c00d2000940086120b078280b0381d0b12003140f20360011061180e0314040a000802814005000c1e8001c03c1c04020710075500c4840f55a20442502c0049603446400b4020380d44c409000e4014459120300010084030706040c10500b030302c407029000000b0001a4104440500400122103807509400d030b80e4900510640d030031980401d40a118260640c024400f91400701811522000d01c0d000380002260002d544074101440c029001c1e00da4212051480e029940026040324414400d003412103070305036102c080a494603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 715462769 1250 715461519 715461547
    0x105030303061c030219062408100b0d0212031c06050d020f3d08010f09020310080d02031308190602090103060503071409010611060a1508060a050405060912 69
    0x202e6045080d8046c128410060340c0ea1200f441d10040e01401000c51891400802042c20851410302c86546070b001602c1442510f5001a81d00301c1c290a64100242c191f00180c0040c091f408507040080d8400d000d8039282c0700032180800608400e501d180780c4018440d000c3c80440059680703500580d40c00c00c1c0d2102252026142610403141e0406020b818140710846001c5891848618143c82100c1100130703c00031072024009041141d01c0344217614100c9540d5051400d00010fa40d0b041c41041500c94010003c100d4000c281440c84008040c603000726004441003400194480d0010300003849a0842c0050002d4001c9010940c40d40341c0d61440c0d04552013800e665a07141c0290400e00e00c07641016950503001c01c841e1010099800504a5801c0c00200746a02d00c04100e00e14105030400c1c400c1103050b0003180c0440b4070016000303801c01d02c40100031412042e11a8454440485a404508540703c1c090600284c8a42640403e0080d4040c005403105681c4a5140d15507130600190a00f0b4104c6041154404070600c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 715464019 1250 715462769 715462819
    0x80a0f0f020d03020d060b0711010207170c0409020a08070602011b0e0f0d0314040306200a0c030f0201090b1f05120309130b030303010806160906270e070f0206010503030306 76
    0x4045d8000b80803a15141804002d400c011021915400354002510456804002c400e004110400104d041032031110b04032500d036401c05442500603504c6100c108110b50700d0a0440700a000814115600b01f44d480400034081c103107000d101000340b0352226a9080c0070784a1610300000030f0018000b014401c80b01ca051164020241d24241d041044000c80a82010002e4005000139401200b0116106c50f80d19000541c401c40301c201118100f00070042840c3c3c0c40e400c01303440c04c800c3da018145030405000541d01030303000d0a0141030040c1040e0401040010120105840d040584070220503102500d40f200240b00c820880450803403040d5100740900355951400c00b1544445614260f404100034020902003461600280c00c540d0980c3c10103170800c10588211104080b041000d8036080b4100c91a003e00507141880c1012114509103181e501d0703140701030541d40258001c068080f0909014035008100402c2000b030840350704010f01400c4000102e07850008103072402a14024003030229003001d14002020030300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 715465269 1250 715464019 715464037
    0x803090d0b0a060302030d090f0b040311060f0d05040f120221070503070501140612060c040b0a030b1008061302031605070203070312030207020f040903080a180807080a0f0f020d0302 80
    0x3d260803000c0700580f02071100c0344000460b030b11030044a50030030a02c0e0f08400c07036640140340aca50050100704046051846003180d2707804191040d036512598000600080e1280f03030614000241020107000030015990341c00c4140b5802140c1d854090880046c08a07200c10b54001c0d04d12054805092540545034403078010861248070314201d918060f21079440e61f09651921840029040c0345108100caa801c01d4010010035014940c0038103410b203000d011255080c0164041c1e01210200401c0c3c0509030313802680101311a60780144880c950100345440205a100201c1301346000c0d80d400c0440c400c0a0785640240d034060a62861040000d000d500c1080300c0f503800101090343c3c1440fa50500001080c00004800d040740c070103650250380c0304020700520201000c0440018002c074540940ba901296020740d40c20741181d610070010441901102144034440c3c11140d0240c441c0700c0c00200b090400c05584014a01d01110ba00e80d0002002d1458003a03070b042c01000b80c02c601603048140c54140491080d4000e0081c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 715466519 1250 715465269 715465271
    0x61803060e03040e0115080a05040602041e14040e0616270f0e041101140d110c010b030705031c050409021617130902070503040503250803090d0b0a 65
    0x595a40c540c00c003510103401e0181c03515040000d05100d42d0600d4441d843c0902119204c004d21340c0d0b89a1801020844000c0401c240c26179110701140412609404079001020742e00795407501d4144420300c5a41c117000610803a240652070903504802030030540100a210050038014081c85c0d40c44014018131018180d4451080214240c140798000c0803d001c0410320140000b4108a5035007020301c041d148140310b0300714950301803180d010800010042070500d1405102031800883c0c103400b00842da8207074021500c483c1c6a140c2400d080d801003221705009062801034260082c0110088082419202c500078062950141c11240c800d8403001034000f020355100042d07245c45881c042d40c0311442400c9801000c800c80903101c198100400380400204240c0d0b0349103482c900306207005030110180407400524410540d50503004960141440410300c252001010090140d90000e01040118a81007221915122140304007000200710301d8000400d030f0f9044500601090800c640d1034940c01b22440c00241501d65003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 715467625 1106 715466519 715466567
    0x81503070308250605010b07021306030b0c130e010e06030d030e300325020f060411040e0a21021b0d0323030615090a06 53
    0x30704004030b048850510000c401d00900c3c0c0d2210143c4074503d800c00010b01c001001c402450340900c2240c0050040781ca034a441c00032560107000291010f0030000c0080c170000d044034001d00011580c40c4161002d00d030384203046d01d03100a00b42c00241c4510710040c1800002c1c10b080080440400c1e160900b4072001241c10003003560303500100ca03400703050302903565088044101c11100200f41c8101c0c034a100e80d07078600180120120404d08011495108010101608052000ca42c07220704d1a0424040e0030103441c0d5440c1c50285000442215a0082d038a11040d60502d104001e001c45803803040e04110000062405084c20301042d8404030425504003902d400c2c500c0c1148044840e80400c112100c0c042c80c0880e047c12200400e00c40304011046950300b00110003400f401001d1031240f0803c5408100c0102460404502806854140d6401860349541400000c0c05000c19060380c2605505603060 = true := by decide +kernel

theorem cover : BRFrame.Cov 715287769 715467625 := by
  have h0 := BRFrame.cov_init 715287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 715287769 ≤ n) (h2 : n < 715467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
