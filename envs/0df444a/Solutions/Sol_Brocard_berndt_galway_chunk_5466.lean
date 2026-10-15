-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5466
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:57:11.758356+00:00
-- url     : https://prove2.me/submissions/46354c4c-a3c0-4201-b3c8-dafc8f4d8bb4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 982913669 ≤ n < 983093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 982914919 1250 982913669 982913677
    0x31a030319090b0a0f03051003080c010b0a120308010b07050712030f0f080c03150a0905010306020715061824080715090b040e130606030809090c130303081b 69
    0xe001503030301c041c940c00510b5101d10441c0141c4040c03400a490309280c1400542052420802d0400300760f1602d0000758090b0110324100c000f1039005051075160180c0512a0380a00454006240100c0390101c0c00190112045584180580c250312000410703428a0005d82c25544100c2c002d51b81485401c00016504616000c089401030280d512005113801c8000010700920031101494100501034060040058005003103a4101c4041c11035110700100039408610f070511964050349165250000010a00146400400079a840b84000382105017800c0388100445480d80502c0300c0f411024505458031411039030142c40e603c0c4c4070000004865815410300c0e0341075070b15600a0074150300205410803041d81107000d28060b84484c1e05240c4012820000c020145010f40d1041c600322174040400706405111481c04240c04035000740341408502e40307a003011440c9a22081d80503004c0d02e901740001366804014401e5070b5040b241a000c4d03a000c5807641e10101c030b0b5070320040c1c1880707080c6802d082050302c2000740324010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 982916169 1250 982914919 982914937
    0x1d100903051615171603060801110304060b010525080c0321060f0d0803070e060a03090201080105060906030f060a0801090b0121170a05091201020d05060f030d031a0303 74
    0x10120107814404072942c0d41c1090950032050019469010700d180e40c072590007a0380402184500b05e850f40360410100c01500641d44a002e85502c1d2800c1d0794098442e41e03005522513800760905200741c022040045901e40304c4c1e40b01490000c40ca80144000940e20805a8003031207006a1845003001e11500320710342544d1050001020400c8001191a8280365a0b52102d81c00041103900d10000f10b0301c0404a81e03102c00c11800207040e80c0c030010000d1200c0f4050780240750315101c05805240c032030b144002c01a0040c1901942640410244e10000070039103001c004458840d44041d000714203507252400300b15085007010340907645c000d101c1e03c80842c1c004024400e9a48090044107410200e514087e085602c1c40446a050210701d0a101a03050101d100000000d8520700e51042d195505d48484604841d0f83c058140c200d507001030b0749505000c44603415000740961030108441001507031614010442041d52000f4104c1d05500100c0024100e079010f035001c8034152044240c100141001e24000a041d644100c000b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 982917419 1250 982916169 982916203
    0x2191406332103070b06040606050f071a01080d020601090507050a1206080d051b122523100b1c06060504060b040e0108030f03060d0521030a0c1d10090305 68
    0x50341c180003c00f000682c1141e4103407020001c50741027140090840c842c54005c5d02c01d0060024002d4100481030f030840c925040301a680395015615540c00c5900d030360240701818014410389001003440a110311400340903628a0b00d50b50302d00350b41c8440c16a1000070310710100300d0803640d800340000c00724420700142e010030080b5039481c0c1d40e900010000f114103d0342c48103400034552040c000c417400202904d0403240101311094100100c10441a44140b01c02c902600003010300202201800385002c510040c2c00030860008240c45552118020040c2210340b942c4002ea8421070040146a200d44961f04d100681401510046103494480c0d0101d030641da1194002c10722002c001a0410911011001003805084940c01561801240c0c0b81c002e1140d0101405041c403e18040c4020f4042000400954054040380110020b254100e03c3c07400b900790b003045481b0600c003400c01c1a070300304151203054107003601810206186410340741c40c400d0049000d506002e80052081714040407011490420040400000c2d51030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 982918669 1250 982917419 982917427
    0x61e07180f050114070c1a0c07080a150c0f03050c130b07120f081518150301110406020709050604090206070b06040c17041202191406332103 62
    0x41c41c2008204407190344200074026500091414100788048465001003d2400b00d15101440711f0b610402003015902d204140001495400c08550b84410342d001d0b009118408600741c102409623002c0c080300e500001e4482003055a1a8081e51015030045940d200d1141401ea010360803c50b40e008d5900048030303100002c00d918003000580f50188600c00801d1500e05200d10317140c600a032a40b00c0280c440c044031201c036607528009440707440d8076010686e6103040c42046410800d00003602c1803036601e03c0d80c0c000d5007090410400b84125004940c1203412700d50040c2912490300d94980000d0001a000c07030707445038484c030a801c0565600405816840c2c0148202041c505091742008201e8101c901d60b5018840441103c40040d044d011519034030680041003032203d404842d50803414519180d0000d201031031004410018080b411440040020300c09040f140241c4440c1c4100100c4130140310481078203074000c5495220540b000440c108108800380049595202481d9a0140030595404d4002d843c0d2000c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 982919919 1250 982918669 982918679
    0x150e04061d1e100c05030a050726040c0503150f01050904080409021c050108010605010e06090a120c080a140d030b0f041e021b0d02061e07180f 63
    0x440303010075041c00d2400d84044040d410380c1c07158a5030101001c694100d0740400c08008464070070b0168032014070780e42d60200400e0031110350141c0150025940c0032026460303c0300142d030050040c03880b50b541c09000e58031030308c44010090124031005001441150000c0100e84005540d031010400080c41120041890302e882c03405620351000b54905a02c003a11891450040c0800304803007070201d4040c0d0b0490f110142e603444861050b8040c1e804e1804800640e41d15100000845000651101e4155607007641c60083c513041340410440d060044501e03541c0c0c40301440d2400c002c808a1100d000d5440c6102d0705201150ba40d80d400e180b0708000e8110700a6400007071042c1c030702e90a008240030f45140d00c1d440381403c008245291011940845102ea07020f402181d039040b0107a56600c03090a0250070b09010039003550b541e5003022404117010b0440e644c100d12882445405006c2e14000300d203c44c840e0b1802c0c80b50030b00701a4145c201100101e400b0f45404144142282c0104081080d1070384230020780420b41005290a02e00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 982921169 1250 982919919 982919921
    0x1303050607080f070804031103090a0902040914061f020a080a030507110307120e01110708010c020c0105040b180609062208010204080709050901230f37150e0406 71
    0xf8065555100083d04011469070407504968210fa0149040305440c0c409404540c69889150040387d40100b1942d0001114200c03034008005a90180c0c0b0240218506248001d5032002e09a410650040d13070b01410080384064601541d4001c001403049a050b100142c03124419036018003d4400000c1d140e004000041d03030000d003189803050b0100c00031482c2c00d000752107044180e40001d80002c104044c05e40801096807007446003011000002c07060303401260340c49480078020500c400746ca50250140c40e050003000d6004809803400c40b050800308500d000342600b02e40c500d4000c80007949a00c01001d012582c3c40e0f440700f001801403800902c0c0441001054104a07500c0030080f40c1c00070325640c0c01008148003204001c0342007800c48110b03080c0440c1585a02411030302504e01c00040401420380b80300b064035054070310f030003482c01850b0604015405889015540344847e07a005c416018155a800f100c900305450900001c02c0e50940f201d0002e03010030800c0c0d2a403465003250784400c0c0035111050500c03082c4011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 982922419 1250 982921169 982921171
    0x13140a050105030403051b01110f120c03060a06051c0f0e010b15160809120601141903030804030c050d030e010f06030b0408031003170c0c0a0524130305060708 70
    0x3420043e042d850680e070000c0091207005100c1c08000da10300c82c108640d000940189401e203540c4041d568850b1100340d05502c1da600b120040162080440004c15090300d4400c00f200c0c05144040c0c02c0d96807803400d180c1c0a807044d6001418100c01c54190800000c94512107100e00040c5414421000c99500e8500d244142522646004a032003002c824103118420325018048840f0b01c4c0150040e02440e64060030811b4041c015060400c1e0411441c620485e200c15004c20114180c03442c018500b14007020503010700a90024030b1485088030000002c003400420b0107a01710907072242c801c0c81c0c80000c03c2c0003540c40038240681c400c1540702003600d40007071a0f442c2c00d081c06400e00c0240813400801c4110300e0740c0ca440911480c00f42c009440068008042244401c1c1c041d110b0f80559007000a09090421329070780807581d83c2c040c208041c6035011765401e4000c01e10344004503000b200d0340100140341501c0340410203101d4100e0044001c0303080d8000c001c902031f016040d031030080065028a01814092510150103441108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 982923669 1250 982922419 982922429
    0xc0907020c03070f06020d082e050312030f07050423030a0606091521060e1002071a0105030307121b171b03120a050601030605090f0402010909020f0412060213140a 72
    0x194908c200720104090388113a10b01c14914040c1c02c811081c00301401c0401c4e0503103400440d098042c0041100c106a0007030011401482400349019aa95840b18115006d000d40d0041400038642080750300400c3c2203004500c00b0690740102a03801c0004695984005c8543c158000c48a141d100c0410305884452400d40400401405902c85a100c402c000030b02d494000540005000d15a04c00140002e03010030080140500c20000045540795503a061010540392540c3d85910118981d50000c103050030044190381481364810740b9507a000da0002d0301900c0954003030b1030091703907801d001100e03501207910340002d4880d00d0345440005a0b05d46000c00c0070f0856610b101d511a085a00800c058003414052078541640088101400101c5454050040700584555032050303078000042024407d0100c0a50500d43c000d9100340c030b401c02c0456880680005a0007000c0b81c8100510040c002081341400840d04602c0803446064010311b000103d0b825406071282e10340280b4503842003e6038109183c206180d0f0100131300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 982924919 1250 982923669 982923677
    0x20115080a0804030b130b0907030b06010c0206030720070e090d050f04090504030302070803180d0e0f2e02060403091d06130905030c0c010e04050402030c0907020c03070f06020d 78
    0xa00c042d111107555124521000300495084400a0b002e10402249900d070203038010b0306040a82060341380183d507003909000c2920205540c001080b16903019560b081c48156014058908503a203006055030500400046151981c0243c0c0c80804440300a202c050054074402c10314603120b0500003000d40c0381580886200c004e00500300060021844000c05031800c960004101261580d901e01c1c08602a018501c2c00a003e21404418820300d050503140d041d902154800403524903c2003448102c444088500355241c101c0c030b80c150410880e060a00c0c00400e0400c09900e10020304404c4101d4407000e0f2004c80006005030082001c0c00708060340b0605200061103100404d0140703408503c044605101c01804d690b1203a2459802031a001010ba008200401d07085403d072074944414203081910f03040200507060000b030329540c502810b03103060304c10349000316000780051242040320710a200c040f62000d08070800b5032185100c004015a001c20141000c1c20070380f0701c941d040c01d14140010389846c84040c500d20501c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 982926169 1250 982924919 982924933
    0x71706030307032003270f0d1214090604030302150c070c05060711030d08060a0f0e1305030403061e1b0804031407060914060f010305120904140702011508 68
    0xc00d50002c0d500c0020421503950021800c050404c591440c800c58014581104941c030140310030203049007941341c50150603a009044107909408002040b14100d00081440c0c603801e481c108000d01c1808151941c10703a850803107140c10405400501c1c0d40c1c000f030740300b100168410000e013103c040362081d0041d0403a20001469040c0310255680070400441c034043e46006100104410b4180918400ca04100540c0981512680e0722075580c0280284812188a0300921080c007002035000c070505580406c503202c150180c00b042d00c0302c0c03503004d644140c1441c090f142848240008408116544651b20742e4407001115501e000e241e190302e0a00b0303aa1124807081d0154034985144129540200c541c940c015458502030700c3e03107010750b40300f548103000701c032000b4180500d8090100204051014081650214401110300a41e2000024154004c007404000c107550031400741c044281c6085000340034180002880422a070060940c84101c694080f1180c000603915052000c0e10340c0d251080410291280790050308034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 982927419 1250 982926169 982926173
    0x110304032d08040305040e0403080601020714010c1101030b060301091a010e0d0f081b0307060f05070f030b0f04020c011a01090503120c010f180302120319150b03071706030307 77
    0x4103140741d4002e020b0460002001c0610500032200506030954040e030250800e803c3c0103091600031204140584190741b0007007441078008444a100f10700c16554110000000d07940e59080180007040d49050540300c03080085a0741e1802c010b18060400d040c07000500c5040407076030b0400d01010060071030602205504152281c0c03941ca10b100103450f04580170703c00610807483c040c00603206201015080380c10002c100c3e140f03d0000f0006010f594000d41c818450400b01451400480b07406485120110340019140d0b41074a020350440c81d06018020300c1c944900c840c503c04101641d02081015826035929440f00104082420004400b0710342031805501c1c10342072001080c0c2d600caa1700c0d01c86014081c003007000c1040200c01d41100c425101090804c7c420301a4000c0c60640340442d1100440141c01000a25100c8002e0170060303d100320642e01d003d080030350800c100340d4003d00c1c0e509824441520421008116900035030019030041030305a682d044112401c41008a003544050142d0780b1a410030400400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 982928669 1250 982927419 982927487
    0x111120109020c0a061d0f030a09060f0306180603200112270521120c0a02030d060609180504020d0b34090e1003060b1311030403 57
    0xc1074914600005a032862081c007814a80340c0360440003449181130002d0b100142140a2440070700c084e00c0b8007168003500b01404520b850b409202c0b05480052852030b0704000c403c2c8601c079125120035490800003280d6485044140002000c40d040e18256500d03007004204100d04003a480c41240040604108210302d0034000808103824640c88900040d120f60110030264480d16070000c031003491207204002c8900c3e0f403034411b40340c2001d841100c40c5a800c01c0c0062507000010000c480c405d461003445038040c0d580d020091030f0b241d00103613444001c621003444010040d0a1f588541405455103445440082c1e203410908a15460703c5c3c0c50070715106003000c05200050f12480b0146069907406500c640075980c54104946007a040c400c541e250000510030600b00780a640103203c00011b1240c4e5030ac515180e21002d01c020350400c2034800304032a151044041000c0344d40e5070b1010740403c40007400340c3e01e0000e41611200c2521441c0e0017411b04208000248000c1581051321848044918a08111080c1515034440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 982929919 1250 982928669 982928671
    0x21b1e2e0e01052803180501140c132606100302030708010b0d060506040e030d020d060501080403020a0f050102130609080f07030804120804051203030405010e2d0c120a0302011112 79
    0x600c0010031500d04c500d1300076040503601d865042040c401e1540c40b0308100340644100350641258a0060010549441040040703c4031072980581d9000c641e45081204100600c1c004009030710500301641040b001c40040c8416801200e081c8902403106085004160a0181a90010074140c3c0b40c108540c0c4c054550800110180c5d4020304005202d07038a0802003070251441002150391800001084040900c566024000600b424041009880e4403034005440401007504c0c007502680c811a41c080005244025400761903100c3c60001d401c09941c02400003900c00c142c0c000c000442c030002c00600c80c070b40d02040036240741c00f610300045c01d030f10b071850f12180c00a01c00c2d800344d07c001d2001c00c422407062108070012500107003030203030104810403424115240c80e50416a011030f025401c162020200e400006071900c03188074030b0007110fa107520200101d0043d09843d400c134107046024070100301a180d602c200d2180b041c858044058031102c0e01c6841c00a00316080d60748080050360b81030058180f030845150800d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 982931169 1250 982929919 982929967
    0x1202210a052e08060106020a0c1a09040f140910111603121e0506040533040e07080303071e050d0906021605010c021b1e2e0e0105 57
    0x202c2018081d803851651000582080e205446940c2c00059003070f600064011143e0b010310b80002c429519400c0354104580f9100c80c1c000380300c0e0103000c0700c00030346081d901c0181420601c000000380d4100000d0b807007500032021038a25071540c1281d030640811074068041c011160103000e074804e1805c4800580000720a101074805030030400d4005130106011841e0b40103e440342d14950459410103c1c15811070050507046032824091420000030540e40d46200d0001500100088003d0001144014117414103a008141d01640b258039807030012002c40f014052407015004400185a0744c0ca482c0402803c4000400c41610140c2c91714860640e44c1130b4410f007542c5012500d041c0114030b81001d42002c001078021120a0301d502e0803800c45c0b20040040550207402c2502d40358007070728611a10308103000c407241c0c0030351147c40d044000da0022001c4260782180d075102003c3c004018800e5002d06100e030425100d03000500c0c413a1000d08008030248981c01c1401c0000200d800d20340f2525000c4803c0ca110a022940b03514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 982932419 1250 982931169 982931221
    0x3020d0b030f0607051b070929030601031104060902030c1306180e0a021b0d11010902010e04090314070b1005220b0a0902070809090a050105030307080a1202210a05 72
    0x804280784141c08601c403030000700001c480d00c140c1c80701003100003040e00c03000c9034040d80b045014000c0241e9103415807a02d09d05006001e04500d0b0300c2c50700d401d50300900c1d00006070340c0a42c0e40c0c0342c08984003c240c40558041c28001206030b450340c0c04003882607448440d90300001e003480000e01840c110001004a04015140a03000fa0442038031049000c5003c1d020701c8165000e640e024400c484d0303052900007001d0b002031406541d40404001c40000c0785080743e40c100300203070000e45500c091554a08003072700300201c3e81d40300b03190000705240d20701500300e0309800200381150101c07070400a000c0d541075118190b0002e04800c4600e6000d5032001300d80711980b48180b00111082030780703072000c03010790750340750f10400c00249a108815076980410b840c090392136900c4184d20784c0c800d20300c00011890302c540d0b81c81803905844006e002146801c1040d160b079440c41d0800c0c1d01c0e0004022981c1e0900700180c284c0d0021b00b200c5041c01e0320301d0b0007417900600c0700141500c0c0109107108070380c41e00382001822024141150740202140c11 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 982933669 1250 982932419 982932427
    0x60302040b0a0302131a0904120f030b0a060521190b421308190f03080907180603050c0108160f020a0501140f0a090c030210051903020d0b030f060705 66
    0xe40c00c41400c800c02c030001c2c7c0c041a007204100030302001080001b0603024554490010200c1e40c801503045600116106030896800c001c103029083c0950700400c054541500168a0303002550791017110b04108490552480c070350070740344045400441c015800842011200100003819804865941e400e92034001174588100c60405480000185440004492185c001990f01c10400341404001851441511380c98440e0302c0d219510307441d26800c201c1c92580c3c01074407002d82004070b450840e01080040c006588034084e6020014032000315440d101040d0b0700a0501080c41859414698208440348403400e05000c001400c2014244008464034001c900e1390401c002841c0c0c00b400100c7c60220070100040c140e6103803845842d4030341e81d901034a51003110b00c040b41d00d08990301c546462044d0341e24800000d0182c911401c081c0300610b01180042c032503032011b141c100d00f050310659508004c104410011000300e03030f00050582000803a40210009408140c00070500d1500700c0360000d07524000207164204110000c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 982934919 1250 982933669 982933691
    0x20a0b0a0f060b030601021005040c03060203040c170a02010e0102010207210e031f0c0f0f030b150d06033e030c0a06030c0e010f020606130e0d03060302040b0a030213 73
    0x340c030025407603030820001c100c0552290003660720b075481650914054031a000302411180e1690103041c2c41a503110b80304001e000d00c3d41d170f0b8040103500058001c4400046c420342c0451038420008240d07010303004100060040c203140340000351071440c0c40d00415045900400c2140c0120b48a6440d01c0300716401881d1000889903607580c00c0b6503440003c2000e80e41400340a02c2c9081c4101260804c126501000c1c000700001c4c081c13801c003a102c109509000001041042e107a107201c541c02a403100c0b01034100907083ea400e9102c1c1c0f000040740b5610401c1c07802c1090b03980b6403042c000d00128084400700385410310900500f10f440c09810700c1c00794061a8048801703d0720130b5490032144c0c0301800001840702c4058824031020340c4440025019004d850741c1000054407003845c0400a40c8102480d007000d0300107401a00c1070b6203900e02401800b11090038203583e032640f5400000f903402c80400c64046401c0641d58002445402c41c41000142c03040b0b01c660520461607104140050b9980b0090507605800702640029070003400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 982936169 1250 982934919 982934921
    0x14120402010f091d010e010603021e0322030c0317150402160807081801020c09040308062e2303011e18091a0115180f141f020a0b0a 58
    0xa40043c070350301e040345080302094800071040c4c50503100c12000303030b20882e81c07101d9045040740102d50724052420000700c026004d0072520303002140c224008214036600d035010860101c10701e060103007040703000504035040701e018954400c031106a4000141c1d209401404d01000c40c1e09805c8605884030302c900c3d80054001c10a45006605007a404d9004088076280d13045810050151b4021511540015851420701d02d03207580b000c5074150240e11b0044c0f0b00e044540355601c040b2080000100550b4000281c07044140b002c07401080c0d402a000340c4005080d0b03811030100b6006208074500d0388075801d014600d4404080c0c910000b01541e066504c0c002801d4100781e40c0003078646151034668010341040d6150589054400c04c00d03088050154021500804100300036405072086440c00d1184607918504d540404450f03921907110452146850401c8015258640054030a03041c02580026502c0c42d24641e1059282080244003001d0212006c40440a181e441c40107526103460038402099007450800283c40c412403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 982937419 1250 982936169 982936187
    0x130b071806110f010e0c09090705060d05070e0910090e120301031403040f0905151c030809030918040201080708010f0b030a02160c03141b0d020102010207020910050114120402010f 79
    0xf454024003001c03070203124590700d4448000c1054090020000094050080041e40e201100c2c0094800340c81e1583c50400c4100920018000700c0070490141b401c840f50b1f0340c0320b1013841c2c007c0341c80c0130751070780c0071450030040750101d4003418940d010386c3e00803160713100240c42070106580c116504444c42c0306260340c07030000c03d509500c00e41d0400c21032071100703220214802190764005485008a006800c840203c085c0400c0310b0a020000d45411040388510072200080c800d20b80141c00c02c1c48a8112400c0c2201000080d030101c510407420384960f621001000255a80700031020741161403804d0101065050100207140007040340500d110310600000420b40350312403981100c045403a00704400111100d11314140042c00d042d840300b81c0300e0300c890b02d1440300580c4000c03804102c00b810070719a000c41821844140a80c076140c10300c090341955400d001d018003684a43e41124450030110480024a9080c000094051015540c21490854082c0983e6040304100c0403010340042c0c0908080b882450303003240495960302 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 982938669 1250 982937419 982937443
    0x40f1109010308040e0109092102070f0305030c07050118091109040603230304050303123c160e0108060d05011107031202070308190204030b130b07180611 68
    0xc415000041404480400780040d07410401c0440d413030f640d0b42c10380c140980702040c038080c09044441a1042030701e0715946c901d400001e03150040c1c504283e5220b0008842d1080783d4420781d62900001002c1c08561414004900500401d080c11511800c60005406810489004510780150b9801c00c10103001c1c1c102041c0c0b00d0380c01000b00280091501c81c54007c450114401480c8007a8402e401c03103152030078002c8192002d880d070160040d4105849a0848818001c5c05440c40462030070b500341c0803412081050418035001c3e480c00f0354041c1003000c00440140030030010414403600d100c0d5a034010500740c2c42500d00d5507541007441c100d0059201d20000072600c807076208004001c0e42c03802442c0b1001d001d40c10080c00d0031900945900d10f5403c550000a801e80c41071305d10040c00180d8035800100131070b8074084481d00f404501d007001810141c81b551081c4003120241c52901c880100840d00108114619140e00d5004005281131043c0140e510200d40000000740681700c02e024140c02d444107a91030030803400d001c00ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 982939919 1250 982938669 982938679
    0x807060203071d090105061801050d0e0d091e03121205010905060120030307051303060203090309040509010b01141c050c09031e032203060c030f0f14040f11 69
    0x3042c41e0b000070b03168000000c4100e0704845100d049140a1802e40d103894100d03800503108030700e0600010040c20020641a0380641030013030500403540514032521650705091084802030040d42d264501c041c0601c901e982c0304118989649400d86034a0000c8500e00040740d03031050282c4002c00380c107101070f2504816121600315103071402d03000090300d0070310b50030842c0211004c1c3c840c2d80700d50000d0101d07103910240c0500c64403816401000400d280324070a07001000100c0440c40340004107500c0e43c4d03504041e41d000750b174920340c0b660000c01d00d40c100c1d00c1c080c03107101d80010001000b005507152010019100f000782c8800040c0414010812031242140b24030180c29030710120300d04000300c1c81d00c000e030b00600317030850f0030079038004c0c41008a4001d44044c1e0101440c2060b10060056042010b0b0a0040b6031500603000311701c6403002001c1d40040001d02d03d0140b084070201c2c0340c4010440421307100c1c141c0100c1d00c40712680350980b030070a00e040140b440410341160b0840c4d0003c40801c00d194541c28480c8080c241800559000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 982941169 1250 982939919 982939921
    0x1150e100507300201020705030403020907020f030a0302120a0603021807030f1514060918061801060206070f08060a090f020c0604030c110108070e211002040504050c250807060203 79
    0x946601c074441e600c2d500800802c070549000304a08170700b01e004c0c41400811903481044180058500216142d40c800341c140704842500b00a130b0702c00c5065400450302100440d4011070302c031220780e01004005030300420800080201502d1078001a4012000c00312108030307044400c1c00708549078403c0d0042024040b2009090002d07004200c08002c80b4051031003041103130740000b048510340f4a4160b044607908000180380019007405082c9020090402420300b40d8044400c80c00d44107030350450102c0e207008000e1500074188a1400f40d0002d41024901500c24080043c01000c020b8903644280d80e9130265056008005003100307c2c078900314020300c0742021024851040d001008105a404603608000c603104000032080e065007038005641c0e400090302d100c4041030705800750400d1400c100e11078020449c940807502d41c840150b00c07801c5040071440400c01107505e40000e414049070510707000d02508800500751040c40d00108400f19010303954004801c0c40d003040002c41c50000d00c404e10068a5203140c01030303130455907 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 982942419 1250 982941169 982941203
    0x110a111c051b0706051206091003020603180d090510180b090301060e0103230a0305030a0c05070b01030b1807081c05070507060c020f090f060f01020a051c0801150e100507 75
    0xd00d800c0b84008506d510303e41c20000364142007094444d8040d465108107150741c44d00310b0742000341d81d0700001d14074201c200c0040400e4003149802c000440101141d62a5460580c0c101014014000520301400041c4031511840c8485032000403041d208859054008945500c07034500064007602c01541704000000441c800407090100c401903c07030032100510710006503110850541c50312a00c0044015000c50000c1c00007030504801038120b403041c550245803480ca0000c065030f8008d2285020303017056442022500400014201c2c2c080042aa8085c502c020061240380c103d20641c0c40032405c2c81c4080e0310303ca00b00c0341c0ca4003500400c00c0e02c039070316801415515042c0d00c85500814211074140c050f4031401d030042420703245040c4144030b2402105402400c3d9240e41c2ca0605010940000d00c04450440c0f0500800350081023061183c44644012020800080310460a00030304200041c3c10444030285400340401000d900200c0c8900c0313060050312410700381c1440381c10a44041c01525009400f100c01d448004d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 982943669 1250 982942419 982942427
    0xa05010b010201061502060a09020607050316020f040917070201090305070602060603010b0a032f12060f09010b09010608100e010816062f010609110a111c051b0706 72
    0x30099003a8001c001942d134602807500c810a44103900710150b04000c002c18169285600016811400503101c60b161500c160b0780c061459028040310201c0700c5071a1149001c6140001d142080c004d021102030100c0c0e041303500c40c5201300410800045c01004005182c108590043c100c500066410605a0307503c107550740c101940303442d01262028429440c05c000c0103018030f01500d50205803130300181a0000b200c01c4035488024913540c803682c400180c43c43e03410070f20540e45400002420103030740805004030f41403104030b03552120000b6211003410790410950250945078150301904648451a00c1e034000d44500d40c0b0000d02500e50b0b00000709240c481000811006000078084150004001070030314a103036240d42c01c84640180455840440c02e0075511052940004c1e200c0c50100344400d8000544035030382d038a84504135040260300b9428050003042890100c0d4103c102c00c060468004080c0444200044d2101e80301903801c1180e0003441404164103a40043d20001840104c0f00f0030110f03441c490b2156000340c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 982944919 1250 982943669 982943681
    0xc0603100e0a051005060a0c060e1b030708060f0703180f052109041e240b0406021e1905061501050f0d020a141305011205090a020f03030c0a0501 64
    0x400c01c600380c0d002ca0141e6020703118861180c01c14000740380070300e404d1104100142c0e100c0301d100010407090341d180c0c60208056200e1042e0001d20400203007034070b4500e0f06400c04100380c111a101c1c801e8100150400c0701c0440811b1494ac0030440700400c03040799540711001d40c02403125120802d500c00c80e180342c0c20704101804200c245164010011180f0a5402c9003d104030038522022030f01c4588400e001c07040f05410141c0081c448000c00c00c12420328990044420000c030f07403c0c020140403215512001c114584801c000c5403000c2c009031036805140a04010f4048d44c0e84200a42080c8288110380698070807000600590b000389660200e404a411b0003410003607900d240580d03030030018131000c0701c0c80c170b11640c043d4040b65041803c092840f81006800c0c68410025000340340b2480030302c5800280c07400d2800301e2100400c0012241d841c0350348210f082ca80014110070300d18080e004854640001e024094800040b281d00e40da9048400815400100300402c0c10b601480c240d58400f486560b2829041120640001d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 982946169 1250 982944919 982944929
    0xa110d050c070b0a090c170111030a060915030309061b052e0c0206040b1509090a170301030818060c010e01050105040c0c080f0d0605120f1509030a0806030c060310 72
    0x450003a21a1306044c000c80d0f034020401840440102020002440c1280c04c290420001e40000110a0600c000403e0a9807040300d00707441d402c0d62010203001c0c4020500c120000842d540380014691421560041e150342440c1c00703088144035004c0100c400c019010304000744550350143c155900d05c0d84040f40300703203010420701c2a140350114102181c10124520320a159844078241d00801c0c5986275500c4040c003a000140411411080740a0b040e40181c403280b10340c1d0b000e0740c0342c170000700080280390401c103041d030b5505024071606032010001007003ca01c00009480180d211070300302104405d078540010381c00e803003030070500c1c08030b03500b041d00c295040d8406510150481303005903018400c1c20f1624402303c410941104004004050500c10883d0300f1084a0151400c1d02900340f000900300d4a0704005041007202c002e5500d600d03400040c01c0c02c140001030040400b81c60b0b050b002c80800d810324650407a01e9020f601000340c100859038002400c0303550100700c0680c5d02540917021543e20305008200c071038040024007131 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 982947419 1250 982946169 982946183
    0x2091804140d050a0309020a05030114040501141b1c060b1c0b0907050a090b0d09060f0c14070f061104030b070512060409080706140a06050301090b0a110d050c07 71
    0x70040e04a002c201c000032100b00340d481d0742ca8008002c20070b5004144044059800c14500f0f44081000c0d1400d01c54085a0025040c000000780782030701d819400c0d20030b280c184846a0110b40c0030721401e100070345600701c800c6030407511098523a40e4984604801da010001e01c407034014100740c0001901c05010009105000345003606c40701001c078a034440340907500c140070001d42040408000466440c030a4020b480342c04601e142c4206e415076208001c0b0007a410064800c40420f07030313a002c040c042040c5882100002d81c001300c401d000424a1110241400f0103d00c041031038910001064800c00c00320002d02d03a4003a074844810860a004c501103082d2580190000f220030302c10f0740d40803407481801001a5034001e03001e040300240656800080c08040d01c1821303400c0340c2c0d00d5010f0000c5c0c3c0010742c4602421202c48801103420b4454a8551003030415202c59a2015009034504002e08c0089a2840403141d032160807103502043c080c1888050040d5880b8109103022281c0c82d09040c001071541d020010004a40100030b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 982948669 1250 982947419 982947443
    0x9120e040b011b06240b0a080115022a09090703050706050f0412020d0b0f0a06060e0904060b01020307121e1713060b03030c161707060305090102091804 67
    0x64032503180ca900300800755000443d90f0000150705130040c2d103995011822418401070a802c0007103d00c0301640025400c0300011407071b40441580440501d00410001284040000c207507c00a91103c400d03240b5549519200300c03007500842108040c03416988800303072414680d0718001d9601178440243d0300040f5194042e403800003803441d10840944540c2d03c020200185014542003403066603034920101260030002d02910480455030909840e846111000d6081c55246881c03820b51084607c240c1082c000d0112a486010140c0c8441901a91003640040001440002c40700141d2a5000e0100700030b0071381c070094650041c1c1580c40300716413082008040210410014088094134139240e0700b00c1d0480d0702c0c01d50100183c1e00c001d221000021450103110000341c90f039821000329041d5804120030394016407103105594008007012400800030101050060300500440a0305604c0d030398240320b01810103813070300d0200e0b800f0003080d41142c0f0903210040c81000680d20320070300e45003629001c40d0b0540707030071100007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 982949919 1250 982948669 982948691
    0x100201020903031b0a0804060e10140d090507150518010c12230c01140f04030509190f03150b040c021906020405030604050109050d03060501090510020109120e04 71
    0x4000d03600d04001c0100a507050100681c1e04040c030060070348a07140c8501c80d43d1445000b04e8220f40042010f08026071707034038078048041c0d001e04c101581c420400000304406444040488542201a070f014034040d01c401040304205401e0952411083da00070444246100c4140b03407500380c0120042115030840c910356403001e0a540019692280215070141181d5141d0b540803410340e205012401021480469110b80300340900c500214031b4000207140000c40c0c0d901c0d0b4042d40400307580409a9881185400f807000f9600d01940c0040843c0079000080b0b0040400d02d4031084d001110089480c0070b0420000012102582c03404c0c041c0b0306080c440d5500b0340991a080900c90113041034081c0c24044000340e0000c06403907810210066016609080039140d8a50034040070525a03018813026000c0c5000e40000724091420341001420440710503240c0302410302d070110800940c0d03000000d200464104403101c0107045460380069001d000d100744001c006e051142218a0f4454100e625002e80c2c240545e801c0282d4501c0c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 982951169 1250 982949919 982949921
    0x30908010b01080604020c160f090b04020906040e04081219180f030f02010b060403050303010905010f031101051810020a211706030705100503040314030f0f150a060e100201 76
    0xc41c1c01640080d901c0d8001450380c0c10031760020410040000222800c070400c0d02122003070b40e400ea421989208810410401051080b401071202c0280210780c21858002c0c8000011058880d51244001806005e0000f4013400b040c5415150610240303500b00c1c12515181c0d44410100e40380f9800e08040310316180c0e6811209130382c9080107400c01c1d40300200d001d0f035010729202518100c09140800f8215034907925034650584a0030041d0006601c2000155100e5040200d10400e50340305801a00100000100400c04205460422350900000782402d5583d10350320040c00041c99601030b0400d40000d44414110210350340000e03604211800b40d0b0b02180d086080317a10a0540c0d0f0f400e44120070005000884011060718045903040c1c005034000c04452815642d00d0102c2d86012100300c1d03400110701c01008100506410443d10410a113400307d11910b1441c110719a19503145001d40003e0240b801030002403072150f19000032240d1107100a203404601c955504005108041586540e40191002004c01c0811401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 982952419 1250 982951169 982951181
    0x270b13150804050d2d0504080d021212040203012009011205090d1407060e060f07033305061801021203102706060518030d05040603150314060403090801 67
    0x48a8003400d440500088221901c1601120ba44c21160701207500751603041d11030424215003081900c6d103503102c501d082078003820529184000e10554210400442c4c2111148080301c0560303040500b5004035484500200c0e00401148001d40c0b1491024100141d902c0c2c4a040a8109a1030036038038100300c25036800c0181e0541e0415240c4483c1d55000d040b11940c1140540d1490800d000441c18850824039162514415204402143c42c4c16810240600ca9a1000758080c0740d0f101415050030b205500401b0740e1346210708103078616031420158034848940c0c40a85101104010705001b482a0703100c03803540e01e84030b0b900d94840c01245e0240c80340200c4d11100360058025244691038255042c01841d140c14240c41c4c250110b50780800e204612190f417580c5000b024405d220141c03515503550350f1280511030340d031142205116002c03031080c1d00c946444840c0a50100c1282c041d910320749008901c040c00d14418603848501c542000344101c00c44015104005000107405102c3c074002d40d2000c9125589084885c04c03688 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 982953669 1250 982952419 982952423
    0xe040b04090b012115060f060c0f0602030901020d0e0610060306030b0a0e10050405061605031501050f040b34050d0f0c060507020d0807020c01270b13150804 69
    0x40850010440001200450407080c8400c2c4d5041e4548081641ca035010300301d8480c4c0140b01656912000e104c1c0441c0c01041c1c001524042c141100042c0460701c4181204c5052080280020740020005800c1e05081d0103440c82c8900740030060100c0070002c402d60b9118002115461711b85d0310602c000080c4e1034424040c10301101d03003120581346141c54488900002c0d00342a0201c2c04140f003103044201c400601d40c4120340c843c1e8050806085e03e41817a011031904007030340001c0c000401c6014010312005404600b8291510034013400c2080d62484100c5602b030341ca0085500c00b401014001c1a04020421110b81c1e9a040000040365014511b000c9a610050f900c1a00e102400d10fa0011003035400c618020b22400c80607600d2814142110187c030759401095510441d40c0b0310058124100109000e60041c0d04c5c0c2c2c0d00032a0600241c201550030000082410140129407214400c0c200b4007819210f0300060100701400107411000d655180300100c2428110032882803240c401b00524281801c02c1c070451078a03000e25 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 982954919 1250 982953669 982953683
    0x13080c06091c080f03010306060f0b03091c12060315051015080a0b041e05060a12171218070801180201080a0f020408010b121c08190504030e040b0409 66
    0x305090142c040202e5600000c8608510410500310044010001707103008501c5444c012440509001301c04074141d0031a44408524102403090050600001c1103d444403a10315403044120248000c00f2964402258000400707903240050100a015100c40140710302e40a601d401e0040352102290110240c405204032250710b02c843e00000010307072140a0407900130802040120720010007200140803a2550b03010200700144181d5001c40f04030240c01640d034010000c64103402c00c9450035543e0b840e280c0e1140802801442781d180c2c445c11705140c010503500e480710041c010740c0092901201050580040d070f00d040d0381d2403080a00c00906807005005000d4410b840d070201003140e02803540107450a040c09800c16504549480c01001090b619101038001403a15074000305682c0c0a96007404884501032070511841d421001208061079018015002e602c0007a00e4100230a075107040d00503866015030051424000c3c2000c0034442415800404a0710821084a0400103008500c0412040300c0340c00000034641 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 982956169 1250 982954919 982954939
    0x150c062906030c2b110a022a0418140c150406120e01090f060501140915010c0812190507031b0e0f03030d050a2304060b0406080313080c0609 62
    0x6454004c8165403000301150007000c1c4c0d161240d07000203540807050341031010400450744210003581001001180f0500f2a20010307120341d0862002d08040c0c900340340d00e000b551980300d020b041150100b190012907030000314680d22000500400f64880d61141181845010f4144980c2000c45071002214119503080c0c60f012a001007155040001d84040ca90b81604c955132024a032000c00c4200c444507a18030f118020006007581002c85803125002100041030081d1004070400a400a150801204103202428000742c0f501462400c461140b040083d1a98454444420f02445a92100118940004d065028031040d41d40c042c0440482c2e42503488000264030740207d40811a000d40d680204c0760320301400c0b00074a0511140400d24541c405c13000391010656503010082401400d100320880c42000c170041420310b00e04640111709120000e40060100c43d03803001c0e01c5a03c1d60b02c50303000600504040301926103402c0e100006c110652007030b20403004240141001004689440011039103a454024030030004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 982957419 1250 982956169 982956187
    0x90204050f15040311121e0d0201110304060b061c091e030f1101020d0c0e0307050102070f0315020403022205100f0315060509042a050109150c062906030c 68
    0x142d98000e400803a003100310ba01c1c03481b11303c0009100940c0c0343d500009040f032089a006000901d444800c811001c210391400c80030790440511002181c0d000f641050780855020700c2540012007500c1003015044076a000c0d80d180c071081d40e0b0650000f45e41d080c0268201d52484d004c6d45074914951070905001000142540920607825004911788254800401d0005007000702c40900542200d0b0034640c6a000f1070b0000d00591a540f4040220101500080c405072464a14001507402c80c070545020040200c1c0c04c8040e0020081d816030b06070b50003140c00500390a42805004100c40b0804810801030802c80d00707120003d00c4d84003c0c18044011030360100c0b80c41900714519110a125400725807c00218141c03244000281036030f40c212000c2c0154020000d401c422100c102d03c2e0361003c031545140010094030307210200066a00305030882d04403120b60f0303500e0b54541c10f0b4a00c00c0398000400400100440e152001094002c000c07a0255101c24000351080880e08850300100185800f040304d1007580b1283c00c00410300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 982958669 1250 982957419 982957433
    0x1a0409020307021e01090209090706022d0d2a120e01050c0607050c0706030e0706030e030c07321c031403071d040504030c06051f090204050f150403 65
    0x340c4002d06105550564140000c02c101450001c102d000c080e82d100c0659606520b844903082c0d0708075281a0080c84200c0c40c1c50300194448801c0c150140b803e2488a4200c0002244046684490620201035403d179481074040500491307001203000440141343c10001c61f41c84245115402100d030442c011180004010f0021162880c11445144c108103040c000301c860f2007020859140500303101d494007616850301e880c2151825030954040001c141c284440301340c05060128205040d5007091501007031444508800c40d181d44107c0d5010607507841185400186040c5800c111109071503052121400700981501d13074150341082c900d032240d0190444030020340b24003040c150005080c0c072a0500d0b65200c1c0d01410344100982044130390002017400c075040c1580d1120a011140b060700000c84041140d41441d80340102030300386072280103200a650382c001c600d0050101c0018046048680c0d40041103e49a605100c00380d00703d803144a001e03603007030304800041c0d1520b2188511203501c110080e0341032030b00d56120a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 982959919 1250 982958669 982958671
    0xc081201150c0b220c030b090c09011d060409081201060f020304061416050a15202b0603050c1206040201050f18330a050a031d0a0309030c1a04090203 66
    0x5496903207804c04100010441d80f83d0030002c5000e184640224980322a4060503e404000c02611412030540180404000b0140c02e0310417050382c0e100c20780b0701d95405010600030055a00082c0c46c0740d9020a80d42c10b40400c2440c041c0c141c400650b9007100700a424481030b40c1e24081e42c00354801040c140a01c1c40240028100030707000410000809d00d0301580a074603600c0c18422018019501164900088450786000b409a6010400014010070907200c121301030503c140580e508801e08000c80d45e4448049640784030400350102c0b0008010492190f40707213082641d031a00510454050f54000c151829200307c0418014411501a12490310b44041c0c080742080542c0b01c502030600300e41d0784d03e145541035103640d1843d5840038405c1011030f179004482ca80c68500d0035820356009039041c60030041c2d00070441d403110603920250303130750304011034019259441d64032451803009a4244602c13407010360100b8190301408810403280900c8059030141c0c0c60b2040c00013950b654450203024038030100010070040f08143e00071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 982961169 1250 982959919 982959961
    0x150305060d0611040317040f12020f0913230304031509060203040f0506091f0c020a05120406081f06050307051209072309070f0c081201150c0b 63
    0x11803018191961510100c46052a00d00601c40e800321381842000307801b0348000200106456250300702843c00002c52810000c078020b500810706170100c0c410440d02c80c0c41c0040f0004000502c482041e00c1d0042c1503202540d40c890042e00c0d01c0445125101d54a0741c115124403002100a0181d460642107484590f0811101d054142d400c030fa66601c0030010a03140c0c8040d502940c030a822001446603941411440e190000c0c03d05049034000704c10328400714000e541c42504003000703a034000c6500d420110090b81000590328010700a4011140b1a491a210341c40c010304c15100561685a03243c1c031540c0a03400030004031408181c10586e110000d1100364020f002541c1c0c40741d12440c2040c60110850f0751030000580c00c1c0c0d0860321950011109024901d034200206076151075915012140c0b423010000105480c2029201d0018445001c880032003661140b0403c003041ca07040311035259150501d4030303411208102449080000c00c4a8850700c3e881da8880c0c4285c001c00c603001448411552650f80b212000301c0324492003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 982962419 1250 982961169 982961179
    0xe06010e0a1502100627180828020f060a200703030c0806062a0f03030c0304110604050d0308100503070801060e10031a040201020a02090f04110a15030506 68
    0x40a0708035041c0b0400c1d5050640c0501401d45003015008150f43d0b150300100e1418440c610482e80b4100c40300c0d2076010b0007014000101d9503001c00215410310700c070f020801400e0380000280103041c12001000061005103010041c262041311400100d841d200380d00e11404542c0c11034404a50384018681050010a80c035044c00b011101d08030724882c0c000d0307010000c101c0c00300351107800d508486074124841b1075200b281a5210ba15050200800f0f10312049024507441b500d83c202c0002505070f074010445a858800401e044a035241407981c0180c0554000b203e003105c0640e000814034055041c035406840443e180504103a101c0c4c14a41c2d0184c49080740200307000001d030351444002409070380401c48403000b0b00800000248407414400300c0d1050140c020004800d09100080c200f00080008100c1d907103001d1189003500880d01c80e40700403403c00e582c0602c00307584226828140003088070300b11f00407070140d40710340c0d20035034854080c00038001c2d4810b041c4640043d0315442000100c04501a4000705d90018004003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 982963669 1250 982962419 982962439
    0x50a060c020c041b032403080c010902032505060702060304060218031e150c090d08040e160305070e0303030a110f030109150b0f0a0e06090a0e160302040e06010e 71
    0x8034003110340b8610304d5120207005040d16403100780c00d880340c0401d20b5440240f5001e07401d00e462003141d022100d480001e00d100b0000441ea02174040a50050015a60040c151802c1c0e085100700349022845c258200305040144102c002041c1c03400724211090103501400b03045c01d41e911500d49200035008072502c400d141c86407680c943c0160750f09024030034010b410003810a0300030b8040001603240600e11000005980901c80a0180060340581621405002212021100c40e10b0345440c010900071b961207044480c0240050164040c665014200c512109a07810003041d9201001240c424071002d040d41e030940c1042012906d035207843d0704000c446244201c092480c00f0050040c2080d1503209030305c1060700740da5400c5a00344443c1d00c000d07420000c0410320a49070400284840001151040c3c00210b410f01a500e80701d20401d4480d9002c0c0c90408031700900030740340f6503130700e10000d81c540c3c02c2119011080c0481c81081e41c1024028400d4a058507020039400240d60b60f81c0005540c00302819040325030200c0202c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 982964919 1250 982963669 982963693
    0x207150804060f0e0609161409090f0106120b0f0f06040b06041809060b030a03080703020d0f090f05121216020a05251a120402120706020a0b13050a060c02 68
    0x20081350310941008004003428a0198442d03400c01d4800c0200e001210059007080180c268a0205c071401640200d404d90b25540791400f031145060036a00ba40d038620750078004d0020b9078021000950f299180503200c00400d81d0340700c40000c401180c1c1114566000407010300420018123066200b03025200018000302e01e0702d900c4115912244582c010200009a01e4091050401a450140300b0182d04294010200410f003641c01030300d0018000c044104242e408220f4414001d1036801c684c20322403050360700700180041c1d414060090b102c41001a1140d200d4088014600700e83c40045030000e002241e10114103071540000410f013110f07694a42070440c8942c0d8042c60104200340f040041c0060200d4080303241e546c1000210710106441d42c800145070348a1a0420445052102115a007083c0c2d0300d004005a91944005103030035400a10042d2203101724100031400036000030307003002c0311401100c1d44003040d5100d030800c1251002c0300000034102d8101c84500c400140d01078002c2c43c04c025030380c0103039181c0c90461 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 982966169 1250 982964919 982964921
    0x12030e040605181f0602030d0e0a02100f0e06030c04030f050309040e03070c050301180f03020f0609010b01020f03090609060a030e0d0c020405060a060f181d160207150804060f 77
    0x61844000c05809a5051002d00303e20030300894290099130294a41a6140c01c0001e502ea01802119418540d100c031501040c03650144181c5000c15030003403407090020001d45009105818405119000c1000038200b401c442c90500240c030b10071009050b01c54607060542d5a072075411104407004640d90310080c411400180d03914041c007180000b45034010340d1104520302b002c02c60642d255010f18040d9250020180c401c1008590f112186900054507800314101407408a10300712203100c15400340e00603801408050041908403844240c02603003100c080000c0d032480c2a0b202c2c031400704850340c03080c2e00f001210082d05200700540b040c1d803070318180000ca110030341031403a051041e030b0001d01e800502540c0705841140351030700c926a04210141c0b00304007e9824040094034481400300f0320024030400c003a0080d60041d8840c1003002519440030710250310783e042036201905c0e0b41c00351244070800c8108201c44607590310006241c003c0b1001203c00c412278800305d10f4140c540a00c003070b20550b05030b615100441144552 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 982967419 1250 982966169 982966189
    0x30e01020903070b070b0a020412060506031c030f060f08062712030601080703201c020c010606090e0412052104050a110f01021f09140a031202030112030e040605 71
    0x504129035445c4102e10703004640c000e004152240091040c081404110001d0041030901d1307900070000580340d112480040c2c5032000e150012076600f1540c0207130301c1a003549a0400d0491440913001407040d01d81380c140c074040640543c01004100e50000002078810f844281c002c0300190851000c0c00caa84491607500c60400068070981480700310000705020055a025007000e5000d500b6150400608131082c8240800c040b900500b2081c40c0800315048032103402c3c28060300d1181030228001c40d03885507042c0a440c0680034074410b04021920030440060f1010017002c4c90362080390300071a124280c40c0c41c24810745442c0c00003245010018001203031280d115414403020b034021809980100440852440c10300403843e108801c5500603140608030101e06e0b41c00180c41100703901022428a040a49000058010491080040c0c2010a03400707184040c1500410701e000c00c0b80c040d0362881125a040700303003541070744020710825459010244d030b400c0201c2c3c0b142244c0e442e15040100045800c55850000441c0255 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 982968669 1250 982967419 982967429
    0xa09050d0f05060606090f01030504170c061509100905150402040902030907090e0c0f1c03080f0705180108060a0b03240a1a161502031807031101030e0102090307 71
    0x203034140301c40090100c2080501d82c0418100d980500d04071340d07140487c20345489000845d05140e00c800101e0200900c2c140c0300030b122040090055114900c1e243c506940c2c890680b02c46d400002d008101903070f80d081c001000f6202d00b0344c403001e000d0001c1c50041c25400502006200c1c0c0150544c2c80411016540c03070303000a0009141884003d61a41461032001e41401d200d58054040395180120500b04082e0204055402c01000c948645404441d0382c0810310150207034001c103c07100003036031a0008045e006400640683d00b04141000703690307602c0c1d07016101480f40c0c00000c0746000102c03d000360603600c00c1d1002540a100036004100d42940d0707611401c080d070001e85045912041d49030f100c00c2c6051804101590441d003c40340b5800080ca410b401c11008510b81c64040091070001500d1544030a0307680d02d07402261b50094a10111100c0d821401c0020f40058405000c1c0c1002c2d40820000904d0001e104801e40c0e802c4101411089035150040d0010b08840c1d010842e20b5400b4020055690383c18002c4c140180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 982969919 1250 982968669 982968683
    0x9040f052a030f0d120902040f020a120e0a150209090f0115090e06100203042301110f0d08150d0b0412050c1903050904020a030e060109021e0a09050d 66
    0x1c00151600120480440320720b4007961002500c008201030004240b4a09030030f030709100e0381021401034540301500040b00c01035000750070031038900d2401c9400d500070300c03070319084d5614400e9910701144910107075601d0140d4803580c2e0f032160f8001c1c408030300c0750304518400c5203074020014038041c1d1110114000c1c0e64112042c2011245980c0104560200f860a1412208140c90190743d10b904140d10510341c54005003105014986124400308558020000c42d000351411780c1c0c2d500102000500c0035000204100c0c0c025000505e103080100c00994002040e082d1005904003420810140c00d00860f040c0e24000e0150030040d0380040b0451035911800c00714514140218000c50703084c40d25090004411100780148000c102d01080781030511440070441d00504441428144030300c00b03550070100c0c2c60307009002d48668440d01c00900038154582690280d0340d0706101d0b43c2a26500c2c0c0c0c1e0361003520124007a0036038284c00401c0591401821142070f4004000e903554038240203021545070001b0403da0642413030b0454800b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 982971169 1250 982969919 982969963
    0xf0b04050c0f011d0312031906170607030c210f1b17060112050a050402310b061207050a020c0d120f091a04030b060405010b0909040f05 60
    0x400801e00c05048009030a0782c08900803900c60000a0290103251544080d4007042e01498196a40501c41544118282c2c96032a48a0508404485801c81c0031744101000c10b2070560002801214002c607620f01c40b41c102e02070710700d907910201c0036030203003803410864801c00c81100b14044401f0002160020b017000070b0b010003d0002204071050085400b0b920414001160901c84e040d10f140e4481c48a5046035540d4000c420366450b03103001640c0f410818204205070382d00702420044966125880148160f00803608080040010403403820b80a030004c030241c3c1019605048481480a242c014485030400a0450741c904034500d1100a031010082c0d9903000040d40c00105000041c0d4100140c14610038100c50041c0c5000c0540e48107a01c05200c1c10f03202052103c440c842541c0b95004000f0900182a40c140414192a0003034400481e90b005002c110390b4440301c0b101181c040d05080c881d40741658010114613103050481c034100540300340002c0c4103c6040f4800004c040000300e01340300b203a03c41956070588e41d2034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 982972419 1250 982971169 982971173
    0x15060f0306050906060405060a03020f04060c1b140d050a020402070506061f1b030c0f0302030408120f0405150c0a0c0e0705071205130e0112120c080414010504030f0b04 74
    0x60320501d502c003038030400d01c0d042400a0742e603038042120212002210030a03503412184006401074020360011000200c0085000209a9041140300d4001881b4139400c0300413140c50181c8003841106405001c402c0310742c00b40500e01d50b0801144411031640030b0004c40f01003501650000e0140e9000442c12601908600180f01d0b2505108881c4403d00200100d41d2030301c068103000040c2102c0601e1211940007030403a40710000c0c10f0181d080000544d802c404c090b41d1050b91814040e41d43e501c1841001c40b140304403592000c40384503490556100d482031456142c81c0c20728020410500006105101f440c1c0340007002a01a0700c0300c100702140c44648a61403e0201754600324460604070401404503040c04401c02150000030700b0b00751911000041e030b0a0060312080008a5140160065001118020b440c1400803030114120661101d03264819070400180008000c1c0c00c8074070005650300200302c164180030070b01000607600b20303480007a0010b241450419540781c6607001e15202102c4240c88030b01c100c1040c401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 982973669 1250 982972419 982972421
    0x204110d05160507081e030901061401020102072003150709060318110d23010f06290717030c07061505011205060609090f0a05070e0a0603050a15060f03 67
    0x1074402c2880d151880400ca500e0700c09070052044a000a00b01c0b80000742a15040c0310790600108402200c0590f03945a160460205000b40100d001d660a0407034509800241903105008031162150b03c45c00c0303d04017030000e4a42115020000c0a140d9050042000c2c0c08803048034591b540d44102c0444c2c0e9600141c91030500003a089400e034403500303424180309111b0b02c1c0c0890326000c41031134940c906692030500c07815a0705002d5440e840324090190341400401c0782c0d0083c800150070041d03400030f070428100b042c01d07030f1070202c80b240c1c9a001a0721051210a0201341031500c1c4884042c0050038040c1541011a903400220100136a0049030341048564000c01d06100340107480c415034540b2105c46090214480c100000a805117a612012840603034440000400e581c640805a4101e2300026101c852030782020040078041c903004691642c42d0f1451b00303000543c0303188103906845000c140644058115418400200c0c003400b0002c10312810f2a032200f20301920502c8183d50007008120740c0e6641740c103076040f03a10010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 982974919 1250 982973669 982973671
    0xb0907020604030905040c080c0a030603060c0f0908010c02060106050f040806010b03040b0a0b0306130318290708070b1807091b0206011d040f0b0a06031203090309210204110d05 78
    0x15001b5441c0ca00f0104000c0d40010030745030408038001409803990b0000d4012405080c01c0d0b000106043d0070407583c40056030b000129410308008503190100c48940f50515503088400141c1101c0050b8003410040140034000c0c0c009004081c0404c4034545003030f0703d8550700c07490044281d00082c90014000b0801c82844401c1d00a55003094803c036050042c2c022050019a0390b02018010f6400118a18860345c20076001e5a001c0c10100021015a80c1e080c3d556440350507000f030095802250346140c00722801c030191070901103c00b21039008420030700789102503c50302000a402031200c0d030804a142d00c3d40c5241e200c03c0100000500c41d1210114203900755920a089405842c81000190f42c010740040c8001403421030a9910351003800c0313039461241d03101d041072814500c1703010b40070300001c0c4050103128011400d40c1101003580d000c2d29802005030136080c070840440380410320180c001400c2e40424030400c0300040300a1003580f0903081560f01a00c80d5000101194640701412507030703040000300714042100c140a69 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 982976169 1250 982974919 982974929
    0x7050d0f1d09062101050c0a0e09091f0f0222080705010c080a021c1d0a050906040921090e010506030c07030503190f0b040b091003020d060b09070206040309 69
    0x114a1054000118000c4403010340319130302c242100c2c403441541400c81c208480b0040e6540c4000d000354103003968200c04d80c3d8000c074a00c03400201d14041c00a41c508064192038080c2c0407210040034251150351101440d245d0064000b450580c417081084501c4103140083c0440300500c0d01010201c81d90041080503048540d03000340032175003007500700f089203a801035441e00d841074101415a545154041080341400750341e200400350110700d1440c109007141c1c0080317060140012048100c041c40b0204003007280750541441900d5200800c1c50024001c0d0515402000c8040c1c4240400c50340400141d4021141800040050001904610040100141c0f20891070300415003503c20f07500c0c40c204564181800d02ca203103805810310000102251340a40e00c0d1010720310070f201042d0100443e001c80e02e101f4003d81114004c1600c29414000d4003034040c0760100100b8003c1502d41c00c600f003007910b11341c28000d010b900110256407090352039411160703a4903030301d90103440707901d049d40903140914107840e000d00900d1054000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 982977419 1250 982976169 982976207
    0x604030321050c16060f0608070603060e0f1603320f0106050a231b0606010207151211030a0912020a020d140f07090c020106080c06120c07050d0f 64
    0x244035015150904513912402a0380c00c0d036498940c00c2c00c11001811819400f46034440c44c00b0400640340d0300203c1d52000b035030041d5805224040d507549a484001100f5200a107607031040d540401c141002110701c034216200c00e4240131450a0030071041d82a031041c41000c0c410582d003090564041d81c1c59000f103007548210b078808136800c2541800d034010309034020000b4230010710444205039880c0b01c0003041f29070b02c40c800040c100d0365980703402129132035031412000f5000c6640c031442010400660010a090059410034245a000000d040c07a0843c0d01440030b4103082da50f00c0d0384114410b40000e9400080d44210100c0704049000721051510304140c48444031010115044000c41d07c005a49190180c0f40452b0802661030f41448103840a40c2400c840c2c4101d000b09100d0b52500096004940c1c100311200c0c101600204105642d4000243d203448141540c90b070310060802a5100301002301081c01e401c005814041410035451350394180c90682e0100c000340c0400c00103800d110400b0b0388291541e240d0b034171201c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 982978669 1250 982977419 982977421
    0x9031504050d0302070c090f09060506011d04020a030e0a060c090e0f06060f0c0303070206010305070f030f0b0c0903070b041e0b0a0806040b0409110901060306060813080405060403032105 82
    0xd50070740b00d002408228041640000d0713050b040c4282004040702810340142c08202101d4001e00c40030050201020407034402c1d0500b07000620701e600814000310b81440c074000c841307078440c40c001c200700c001e41c0403408400030700d07036038000300e80e040c4000304030300c002c1e031841580d0000c1c010000150151104650f03512468600c0c260300100005034030300c01607140e00030406407985a1102d051a8454409004145440400d484080100b0440760b0b070000c0e8443c120ba0013641642c0066071101a2605000c040340805004d01c1880d0440800046120040a62140c42c10090301e080000d403500090424449a000d21031004d00458148010044032107000300d51130460711038083c001d1502c40300610030f00805000385c003888032074000a08192515041029403000080003041901d21920b40b6400003440c03842d405003d49080307800031900724060b10904050b40d1031900c8000455031001c10074045c40c44505411107444e80c0c2808005011780352500035001461103521912006544255407000c2c0402140000c0341b19070a1030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 982979919 1250 982978669 982978673
    0x10306152303060a06050a0c120815040506010c080c070b0703051b0a020d080702180c13080c0117134e0309021f0507021201020c070b030403170c09031504 68
    0x96208882030746c24415200d02d202202503030b80c12084900038145902a20000c015654043c5d2464401d20b0305010301283c0b0390482050108441c2c003140c000703020500950001c0003060b004000360030080115800c496940740c440e6050303081034119006c21800b060000c94810340c401181d420502441418000426400c010341d000285003003400c0074060802100021170746c003507440d604040440f0a02601f808007031030510f010040c4032a4400282e103401060f10303840c0824604c8000c555002910016911203646602184d1542903000b00a000035100c81840d080391000101c2c00c4400585200c100f4411845011007401e00d596a4000035450740780041c9a8001c00d403241042250305014000b1a03e0000340c149460310124140c0400780034009000001411802c007520780c07080041c6100c80c030954001e07021101c4404070790b081c4e01496030480c00680100c4c0302400480c440c2400745511601920300004404500f0301405411101500c5410b501003001850240c02d0070f00704845044101c40f01c400c941c0914007a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 982981169 1250 982979919 982979929
    0x613180e0d140f0715050705040801060911040b030903041d0a0506120a0308060f0a09200715091524080703110d05010603080a0f1403011409040201030615230306 71
    0x222045030343c40d00d00030502500b4001e5603c0000340303220081404000504050402501c5a0802d104010f101c0d0b003000408110200540640c84504402006490500e03050030a403040c141c00081940440d40700030700000800304c2180180000d00305800c0200c05070340c01c203a004c00003900d100501e41d90092600300038100ea1640001102a0141c0e010f16146081e902c0d03160001e12180103c420080c0d0104050354080344002041c0c0c0060400000c59900b2400c2e0500160700c041d99020f0210702500d00c0c220301c80440c51120040d08035482082c031441442c140388000c401901c084406940340300340c00003804420301544e980c0d0500c920014000f107030b004000b17562035a61060032100c100640140a040c0851a0300200070094102401441c0d0014006490b02800070000744001180b4040000250315034064007a40c1d428441200c0c16528039944510f044035000c002d2009070f50000c0e108904142e6968000030382d4840c0080c1c1c41c800b01d8125500c00110002c00f821101c1501600119425901340030418405030340c0e98 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 982982419 1250 982981169 982981177
    0x40b0103150906030c090905060a05281a0109060c061808070b090c1914060706061d13080421061e0f051519030c0f061101050105030601050613180e0d14 67
    0x560f4070080b500d664cc04800c1110f0170500c042e081d400c0c1c80c071802c9901c054509500a0081070340030a03001d4044026800044407203070800d10800001c210260800c10200c0d0840e00507075401c0070008128000f40b806681d0303840302648081d1341551100741007414040443e6051200c41ea0080342101d203070b85442040c03041c444900c0348610540803000003c0100400b83e4551100355510303e83c10040c1005025a14000400d8048230310741044200c145580004810503160341900300440d40102c9800e04141c1400a000d0000c0b0011600c0e410141c180c0b4403e80025150f4001c000003140038010900c080f419600c0d19109495a140c003c04050381088108000744142d003151002103103003210b20359102c1c0c04903241c90864107825000070703021002120b03012452100b0b00442d4000c0b02c5040d0303a41000201d04ae0884c40c2218820f004680e4160000e000402032880c048014085030010b940101201a41d5100100440b091203030b68280c00c1500d03a800b42c02c145000b40a0b50440d90b286007000d0550b0a803940315918248a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 982983669 1250 982982419 982982431
    0x5180c0f070507080d020f06010b040e0106030b0d0f2009040f030309022707080f1501031d03040806101d010e0c07240f020906040302040b0103150906030c09090506 72
    0x40401c42a0501504021090040c030004080c0e03000195135903402900c2c2c5005050b541c80e41d10038440005602c2d081401141c0444000d034203c48100d908080d801c40240ca1400e508950000704058180c010401d005a001c200b41d104480f4140c40d540204083c00340581c203001c2192003001041c042201290301c0a4512102030707407520300002c600c5224070002d45420110308080c41003a85081e000b03451640046005402008161118802079440c510015100b010880b404c0003c00310700e002a002c070b0350103600526a00441d10294000541020001c24070b141c1242d44100034651221041c8800c000c11301100c100500b6003803500d07600d00d69089484801d1920180310f09004901c0900000b040340007800c059a920690004010300c0101042d11840341c00c1040203c41c9010526003a440500304807144212000d10300080c1c109403c15246400300401800c4000d001414151580800c02ca0086e160400c8006481c00d860300066150650800b004004441d401078450315140020311808a8800607000394450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 982984919 1250 982983669 982983697
    0x201020a0c120207170f011d0a0219122a0602070e2205030d11090d081308011107030905010201113711060a050f060d06061a0405180c 59
    0x2c6101d24100d10300340e22503118401d036000111003c680a0303004185040465030700e200038011644800c2a0144000c0d00d014401e40f150b1229180b030300141004040901d48030308412104c05070540d140715107000440103042c211007116102d0504801c240300f42d07000520500303409800c0381d070320350a18101035564140c5010341010080c07400c0010742c040a45078600c40401215507400000d40b901031602031b42e03941100c060700c2541e0382071042044658583c10280c070403068008013080040083c0342c440e0b0070706610105856048000e11a00890707010024050315100003601c400441c3c5d0f801007414024000b6815411081c11a4148401034441c1c0c190301080d14081c05048408603000300810224000811003050000001400d600803904140d03040316542d81641c0c6c512003a5401951007100e07040c103c4208565094844c00b48a0214699003130600d81c041c0c0300c0348655030006015841340480035469680314180a48001e0020f404e02c071504224007040c1146828000020083c00c0a80c0000c2ca540959104100c0c06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 982986169 1250 982984919 982984943
    0xb191505150c0a020402071a0601030e1018120f170408093303070320071e0b10170c0f060c0304030804090e0613050607120b101e0201020a0c 62
    0xb0401803003014a400da0042003159030311030b240b600d282107400c1d0100e00c100b1810000c1c0000c0055000f170013090303c0741d0740c0070002c0c1413120880ca2001c0b00a01543c0500e045441c183c00c0c44e82c00007080310301c81620f42c502039201c1e00116050b403c00100202d46290300d400244802c1814000060402d90645040c1d000403590300b420000940225401c1181016a41c0c500140c3d000c00c041c5040e20b400d005500805440d5030901c40098105808002d2881000849141c1a000c002a44c0850400319209140400310306400a409400340c507007100e840e805540d0302c184004509820000240189280c0d502111203202411001100748005081701c01c0c041c1280d40201e030009a0b01135601c0003801160302565028482640311925900d07804010030465940403002c1c0b2929020a05002c01c00c2c54007040658000b008001030354943c40220313600010440f01801840d120380c0600415903c1182c400816000fa60781c01e015120003444c2a10505c000b001c0307000969104001145800c1d0f032201000510541011009500d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 982987419 1250 982986169 982986187
    0x6090105070f082d041214160605042604140a290c1f110702060304060f2009040f0e070b0705160f06030506180a180b19150515 56
    0x601c900c9107013a05880c0034194204000c020f04007007502c0b134901c00c60703031040540c4104012103192840741d90b40a00000302c540f8030b03a8000650316004240d11610400d41062142d0316103952001990031100d070340801c0000401d00784020614400c00840700182140e04005261074505800c24800d4501e000007400214202043c000c01001400c40e508143ca120807542260010a0f616070b05081d00c0e2850b0010904104c01c0c0380c0d241000009580b10244c008107030034a59221540d8000080000b031032020440c603120800605241007036007012801c000800156551381e40381c40b042004454118142e001040d20f880e1100c00c0c0e41a0004000095030102640d1070743e980c800d4140070b803614850402d070045078103001c000881d00c80808022001101c00c3c50314141310b13603110f50007003100c148035409500c0701305074184000400d0781c400e0341c1202000a03407041031103581c600181ca0328100800103c81c082c15652020f00280c400e2021807045c40500c040c0c078142c0320030890505000800246640c00100c00a11010845000f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 982988669 1250 982987419 982987471
    0xd0605070e060406210e030a0507030e040c030f0506030a05100f0b03160303120204060813140a0b190b09040204021e2a010b0a180b0a0806090105070f08 67
    0x4001c20010b110365116642e501c001448544048400c000d107001c040c462821310f11031405650500740300f680166081801c9560222203c0d00102c0d01035040058682c408140c548a0380f16116000a01e5034000c51001b40511015080d100040c03e0203019a12850508000c01c00c007144802480e642d6507004540040c40c0c10007079010b0040f12240503031501503000c0e00c0252443c0c0a200300102ea00c207845071400c01c1c882c80b242d4000c0f400340e841804003261003a40003032442d1850000d9080c0d2140308079032030480c8140540d002e92a04280f0101101d0701c00011042c000c07407100f00e1a242c001444070f0541030001d0885940480e1200d240984028029500031520014511100408981020000001c5915040b810750f440e2481c244103881c940760070f0b910b001c03405d220002c10f003d44a0b000e00040c080620803031500c0280e0049003040c0d1645151a0750701d0008100700c5d079860304080700030101c41008007400d003402a0010700312000901204103000100303149002d0580c1044000c1e50044295500009148445000306 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 982989919 1250 982988669 982988687
    0x703023706110d02180301270b180f060601030f020c100515030d08070e0406121b050a080a0b091f11300108070f170c0604080601030501050a0b0d060507 67
    0x45469002044c05c4111038071400030303401040400c40c001d0102150b000d0441281070314202d4075100d0301e807106440001080140420035000003c2c004143d10105004030080e00b410410460000903402410500c4455a403601034070f4916004041c0461410003900441560f80d00034104003d4583d4a90001071002d0060124800e129003001e02610318010480d4002071440404a40b40c001007045080c8026481c00e252107400c0554440c6210541c0c001d10340d0300d48290311014101d441161a10b15200402c0c143c403019024402050000014144554a8981040601c00c010050b000075030003404040c443d9680910b150940726000000010700c0b152200040e06a4407c0400014412900c02c21000c4003100702100109100c2290440c1c1010340d0300c0315251a180c82080c490a41d030b0a07250141400386a8184070545403114691040b038010b5130207000401c0064015a11802e0982c00450040003070000a01a541e802080d0400070002d41c54540002640c95050f00d0020f01100c0e5a800011040c40c0280e03162 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 982991169 1250 982989919 982989937
    0xe0304090921020703060509030307120902030106090c02100f1b1404030f082a0d051b100c021209010f030203040305090d140d03150504050702070902070302370611 72
    0x31070000302d400e0040d6a4120902c001c40f00c0c24604000941303c800040700ba0390092004e076941f519020705403104440907000f0b2540c00e0783d05542c1c0b208c000923824910305c40d20703640007042d801500c0c62050089000d4221251014034147d01403e1003c42d04040030014244003400c840c2d401c01c241405512904200d427401140c00041c80e00038000c0d40701041c426114050903c80c04a10340141445130850b582105171400d00c0d62210741d07680b2112501408600030f101402034a01e041546002c400f46041c1c40c203180800c82440220082d59440d019005140d0500100002c110507070100e902e0302c20441d00080285044640c1d503003c040c1c2c00300206082520600403240582e50060800100c00c0c92400c00000720380380c1e801c858415110303c4100f0011103010f80215540003910b10044a0317203620704000d0102402c4018036038411801840004503503030320b10b4070151031094040da000b48960030350f44400701c0e800c3d1441400d443c0410500c00344944001c040000b50b010640c1d00030008500414012031017203450243c8850 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 982992419 1250 982991169 982991213
    0x80708030301091d0607030506031203270607020c100908010504111309020109051c0b040b0403170c0d1a0a080f010b09090607231216030e03040909 65
    0x400101004004050750503034460702e2081080d1100c01c0342c07032070340b01c802903c8000041d00a600041c411034040e51140b640f204c00038054841c0101ca0540801d02548102c8288640a40c01402c0600314010280f00180b00c3c54618010429414604401fa540e160300c0400030307104844210501ca040b91107841380b00000c040f40d00091046c0d0901c2d20742010060f07900f00381f003402079000501035100034000d130084030141c0e601a11307881d03d81401c105c1440040110480001900c00c00c508480b80007800c01c00c4400c0c030a501840d4280c2041c00e141c500248102e5a68410001e80300e003001c1401841d0143c4002c4a881591006c000140c481512500d0f81032040034040c11a440003200301e0020f00b0b00d40104074000c4041b020402081440103503420004101d80a9510700c11a42c031040004030340314044d8000a0741c1c0094000076040700c441a1212010650110320780c4c05484007180c090281c40f400c06103c44d04148000c0c1414000d10034854a40c60744c901907807151804a81c3c07103186800134801c90380c0081c182e14900b214 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 982993669 1250 982992419 982992433
    0x60e120d0c0216120308071d060d0917070506150f040905010e070801020a030605040c14031005040f020d0c17280501080708060a09020f010e2707020c09040b130c08 72
    0x34101e000781030544c800d0300841c0c000d10002c0d05c2c1a02c01c401c0c00304005000c00034034000324090806d0144a400417202d200305107580d0310001020543c41070b0305844011200c41495a078013414a082810700101405200d5400d901d1a400300c59a950040e03c28180281542c0003d07015031141003450142110320500007e50040e2000811260b1064005000d40c10803901c061040c1540c60040c07004640f400380d2090700040300e01c41c101002c00070350740055410030024060315200c10f0f1114001000c890092034010500b03680007801c2d06e4000c4950003480344004060a01c42030000000d110b501c0300c540000c04070810511f03100c1e0b00682c10034440b420340d1031010407210200714541e1075a075480d944013094041e1a0300303480b5801c00a200e0710030078000c4610056001d4021442184000d005480003030311010160360141e02c108404a080401840710080c800051a03c0310917810804030103410500c00c91600e078080d400c01c004106c0850a50020a0382041802240c014962440d0905d00c0d4450915001a141130140038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 982994919 1250 982993669 982993679
    0x20d05010b250203060106140c0718180f020f040e06040c0504110c0706050a0509130b01091409010e04081201060201060e010b030403080708040618030c060e120d0c0216 74
    0x41e000d08103181d0001d1241c41500204402030300d0848203500300a515920850041c48002d21500300c005624440034041828010038401c803038107240c599000b40c450307030021441049003200349008802540340403003a5121b840300c094403110940d5029040103406190628400d00440e06da9030320104240c8072170411380d4050b041c1450103140310300c0c0d00d11800384550b041c1584111501490403c0f44d0309010b202c0c00a00a441c50b100c02030300e007074000e8600002030010a100c0c2c000c440d118003014035100c5407040e030002082e07a00c03e00050003040c3c068108c00d01400c002441100365480304107a050650706003000d209615500c6241264a4ac49082403c24514400400000d1141d07015040300c0d05030b0340c904203011501e81c2c81d0f454103841c074002140d0281c0045c8581d0040740c445400780039000c0e04140035203004681408600f0b01c840d6a00000300701140003840d524588824041c040c4034111051505c4806014880040007a80d202c40c041c000005814a64480081d44102c0c0204040580d801011701d840111665030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 982996169 1250 982994919 982994939
    0x32007030f12020c22203601030f0213030803010608010b1215150a050d1104060801050907090e01060801031e0c060c0f0c0f05150427020d0501 63
    0x3110700316445140c4501d4a8a40c80c00455001107003140500302444013076890700b500304481c02c005400000303180da070958441c0d15101302240408100c0c04414440e656450801c01e0300b00c02440c0340300c809040b50320380c044078a0f44081c882101d070048800d28001c40c01200394480312000348112400108030080c010400000c010070040554121186d980300c0028a82c3c1e26500e4240794803552008510440c506400250030300880016007141d120050200a81250032400781e4490b0384c4102e42c80d001246d030114000450003441d0055582e00441c0a11107801d1618003003000d010003906004152061205d81c0000d01d0302885800c0307144c001c054240072000d465075620300150101500703000036036100308080120010f03046420316142403607600001c0d00741c01d0303490580212050003520f10102c50007036000c40c40401040203090440301404001d001885d4035842e01040104204440041000414050204000c4e004c083c25880c805108404003404444883c030055400902c0b441c03000f00041e91601d000410031a1074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 982997419 1250 982996169 982996193
    0xf1e0d050f0a06060315200f09090903090f010e03060703330906050603160e060c0304030c0f05030a120e0d06090f110d2f0907080405120c060403200703 67
    0x14074082c2006c4070300e00f881d40e4182c1700a034029042c1031040b601408107940309100140200e080c480b95181c00c00307110100098428606445a1035580d0000c145245140740c03490860040c200f09003862454140c0102c0072a4071100c000784020185581c0390308035024401000301c101c0b400d0170200070340b1120010380c045d1038034620b445004008000c0d14040f80403c10b070404900b12030049505407030116100c1c010400480304031a641e02010740010080c0880c90a04100300702030400b4511400725078001505050200c01450f0450340014400d511101c1c4ea0004110480501101003c0e40c0c0340842c0b228180c1004903680c042c10f00f4000305210302d4103114009009041c04451580340c403400c580003e01120000704003c0008066024110b0b110708071020a403640f202c040200c56404103409404c842c2010000a51421412a21540410030010422041040074098904030710b880c210a0f6080c250302d00031859030340301c00500003814400170b072200c082ca8040b503890450303210040c0c004a90742c45031240341824038031017 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 982998669 1250 982997419 982997423
    0x72303010306050a18021302040b2109011401060e0d120f020c030721020f040e0303070206060a030b0403050c1c020309240a1d03030a030b0f1e0d050f0a060603 70
    0x45007030046040481e0f01c0c01740d03a155920740848811384052a40800004041609032845099820440000e0302d02c0020081c002d414013050099000b000c00d59005d4402c0c040050200380e10742d02d04940d41940c82603400b03400b070640e4224589080004808004503c000c8411100603103021b02402c82c030000340398850b8103000f00450343d03426185511054014166508241d01a210074404c0c4168000081c0400000b5108140e00092007803241d1050f140200d0b040302d030031213005185038000000700820690100186504080d003035501070f603d5455515007081640c8054001820820000360380d49060710100032044656002d0404030f000c45844200180da298890078150703004240c4510080d42001140f1000790042080b00031241c9018007004085510000c0058030b8100c84400981c2d010203034508201401001c965600c0010b0b0440e4910104403020800d014002c0c840c10305461a01c8201030039980c030070358144080c1e8030b200503447c0c2d510b000c50501d6804000e40c1c0c43c5219401c0310900f0f00c42d4075080a001c0368 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 982999919 1250 982998669 982998671
    0x101d0721050c1807031a03030a030b012c100e03150a0b13060513060f0b0703090b071b0b070c03080a020a05011823060103080f210405190201080609072303010306 71
    0x1070309614106c1c1c1e40b11490304446034507404c10721014030068025000f8801401052401d10301c19003410081e02c0ca645802c000722050311054050b08401424030840b4010006140e06100c01e100e54003034006030380c4606010080c0e040341240d00c041084282c0700c0c0c004084070280201840b403003079060050800208075501c103051183c08020301b0b807200c0e100790b8030408040c2c0744c61070044d10409044c2100c07a816980690000c5082041140c2c2c0002c50031202c1003d40b04e558442c4a4101a90000554201c1c203d00190452000281c4c20051100001c04a44102041302ea001e1103880c2c80d8a501c0f202a8101540741c00b010741194201899494106201504081428400c040d050304211280418009003070304203040d41202d178012801071012400040162800ea01e164030175910b000d001d9502503032901202d02d16100d45008a1043c0010032000b840780501e964065000f128000e009500001d0010401034981c3d40501c09410118580c24810541c0b81e480c0b290442e40400c8602c2d442e090302c03005a200b444142e4003a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 983001169 1250 982999919 982999931
    0xf04030218151e040b0102030f0d0507090501030621020f04020d0209030d0f1d270603010b0f010e0d0206040503010606170603071203051308101d0721050c180703 71
    0x14607100d03983d01e08918580c2d8008003841010004d000013000c0b101c100606610040c090061204804070091000008050000c10141000503001e40b003094503801042c14541070036004d00100c0b089082044500c100c008084044814a001042e071003941ca001040d006400000c40c1d1b681015940c0090600d41c105600b10f4186c0c03960040304076280ca1035400700100003004884c3c084240c1034100d14184050030024500300041c180c940e150940828013869039244214403d04004007071400307207e030603a8070307100351307503960300c04403c800001c1c0f084a0541c0003074410ba03410309034001503490b03402c25280985009002001000d45441029104c900485d2409030000000f03400502182000701d80f5004450b188000e280401c5080c1e40c041d505508114a0f05488079190b60740021144010040001180f90740000000c007070100045020410321810721240c550f9111200c100008c01840a00c0b00e9003140c01d0b1074021070b40312a45003850801c425130f241c01d6800a54144070003c0942094212400b5403602c0c2c03070400c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 983002419 1250 983001169 983001211
    0x2180604080729041a121503150415150308040b0423060301180209191517011a0c030f0d0509150a020c01090c08010f0501060203030112080f04030218 66
    0x160fa02c01e00c07400c0c48035a00912003000385510601d8480c1d001c0c4001110313242005508020010400300440b41c40802c04c00da035084080070f0070306000d0090700420070040700e0b041c3d1606031981c200c0d41400201c03000c1c02e15030703c001c40303141840c03506a00b60245a028484030394695450301c05195542103809082e00d041d03904030f66003083c014540020310088201502c610304681c030380750006000c1c1005403c056041d6408126130411039480f8482c4186070058103001c50701f5030b07050088941c0140114502c0209000d5070352000aa5807030070680d01030441c6c01e900ca0000300d40c0607102e5400000d01030400c1001080c0310200c1d10400130b110010180c038240d04503600402c0195140c1e640d05607214034101070154402d09600c04210f144105800402a400c0750320008178a45115684500c00110507500141441e55508040149640c05000345801001c0c548011401c550402c40d401c520101050002040c030100052104a03400187c0c050b14011500100003a10030304010600081d92a0120750002034160754120442c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 983003669 1250 983002419 983002469
    0x9050907080d050a08060628090806061c12050c061305150601080a0b1215150a03030906030c030f0207080a021507170a0b0301051e0f0118021806040807 67
    0x290000d05692014026100e100034805c0940c404482c5404101d503c2600300580c07500c070341d007418984500f0f89d07400d5070441c81e0802c0182400d10251171244500300442c80d20b8103c0145010100c030250b0001111030742183d10407000c2e580c81c40f072031401d18100c0c010201005040540c266041001a000320165001500154581d45072110201c9445010600000c041680402a5481070741111000303020f119848124111a81ca030044104960240e441031000304180140052102040050107036180e0048906550b00070f002441540108810150b1340c50070ba01000b03120b03410103202003a240108666409680c1401c001035840140c03a40054410f000f250700d035540f00c0500b036600c102c150f9501e0548802c880c01c110000300c80003806100d006511000c907035407291b40c00c1c4245400380301d29518400c60429000e01200340180002d006000041c0711800402c01075a0034403140500040b100001690b07508000c0c03e504041d040440025040200403030301103008040040c0003401da940c410016000c2d41151103580c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 983004919 1250 983003669 983003677
    0x606230c010f0510080c03060c3109060f090b01090b03101d0412020714040209010201020c1203090f0304142b0c0611070b07030c0c0b0c03090103060504020c060609090709050907080d05 81
    0x1042c0b41402c001901940108140482c40d40c84000b01c0324821100071840e0142b0b100f0b854100130b08250382c6120070411041403401c907074001c05a1240074414001020700190800e030381440b880402010010002c0c148400062048001d8034101c082c0c000410303503100300c0481c0305504541c03c4640c1101c2109203070220b400011400d0468a2178101100d107401e0200c01d0001035007050780170341e0540d1b400380940301c410b0307005000b8038a0900c01003d09035228600804d0062402000382d00c2c82c403c980007000240040344e030384e414031a01e01d00300351403015885400600c04141d05845c1c060b11010034a07801380e035074100809040c01c501114502da459108400d05403c40a80340c1e1814419428001c41c20845800001d001d8aa00b04140f4001d40d00e807800d00343e55024120341d40e40702d4a1601d010b60400140d0050640e010b103d13040c0501000d030740840c03c1c44801d02880b903a4060182c000d6200b0041c810004900140c10130040000e840381280501c00d9091810300660b5460f01e501035171400d03001c2c2624421496120300195 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 983006169 1250 983004919 983004931
    0x50601020c0904083006030d08091911060304030e03010e281106030103050a06050a1107021201020f0d05041709090f0621030901030606230c010f0510080c0306 70
    0x714510f40f115680c01aa50707000c0f82e0b42e4141c0000000c00b403401061205012030b11043ca0071402d420ba0300d0311000309418007140e444440c05110602091080d400c20005410048407204c40c1e0548035410070341008642880100c080390303401140002040205503000030310310702844055009000d80241e81c10b0302911101c11a51180002c52105081200b28091915032401d00d0f000303100d9140c81e004500e001c91300550090300152000e504c8051800c003001540e2103031903400ba0340a6410032140c06030f40303601c0d02e06204100340a88640301c40074803021805002c4d070480f01c0000c240c0801e1a9031300550304444010345811901030ba1a6480d08200701c101c1d08000088501014000b0301303418071a503a03007407800da000300080c1c0819001003554280e0f034080c1e00c0800300c903004541e581000396154011003000505585017900b00034200a10007030342c0384070300d48508042903d0a40d0f0310b50003034440b0b151440316401440c0b0a41e6680180e1708002c2403140c910007100c6c68205641d11002940d120302850801c0c556a98801d07150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 983007419 1250 983006169 983006179
    0x3180902091918150801050103080717161103070b04060e03120403211403070306030506130215181503010509180705013b040e0c030304060503040c08060118050601020c 74
    0x840c04610449600a41d2011015580711385541c5d04c4082c81c40c211002600112841d417000070300305081c84a44182d4a1303543c0010200a481c0040c0c00c02558001c40102c10000c00d0302540e00c0706000c11740d0303044c0803070342c081e01e01f915506440703540c1c0e402c000f400303510081031150280c0103107401c0307210310301c00d10003140c0690341c1180340300600410f0311321100015009980004104000d012400000e686410f0045004442c80d0350007181c46821800e1003801c2030740280a030000c1d104a400c02d44010b0f103031121100d021001c4061219200c003000700c005d601d040030f114605548040c150742107074149003c02d0017846c1070f1041583e156442c2d40c1c400c11071200301e1300c881194110703550015108108542c070880880d24070b4400074151000140040030b40340700906038041805201c04680b2000062401e042c81907140e00280b580061003441307601c1c004030740c4a03c180e02172803042000000c00a1309100541151000900d6681c085400e03541c0d5401038840c05125500b180720708282040b001c036002d5840000c80240034100184 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 983008669 1250 983007419 983007449
    0x708030909090f01020414010e03010c0918060b0c07141c0b04020a050402072f18070e06070303051b031501080405120c06040507151209031809020919 66
    0x8010002600504440003031040c5083c10101c1d8000380080c1c1b004003400f13503020b0800c003c07150000d880344440020707080c0640c3c034100e440140c5c690701c812020111107508040c84444a68680b054000e0301541d00a002803903000204103000480000d803102c103d60040c000d111004190004110105e080e0b0300016121603500101500070546010716107030080e00c02804800582d0340c40010174103031f0b000300c02e0a403041222511051384048822400310f410480390307200140d81150b92000180c441501812000365030203504001a08a0301447c01c001c90b00c2001080c3d0b50302d400c00f80c80c004015110481d018a001d00500d014490f00790301d03401c00e0740e0043c449003e101c08004161401152809001802030b520307485540b171924014070950380140100c0c0e04981c0908001c1c41c244c03c00340e160240f1a48000b0101c16034240d0301c041558056010381044100c01c03004980c2030340e281002c456144100801500c2c6001d004000034a48401d0381c001c0101d072100342d410581d8046003000354220342a59104114004201c85 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 983009919 1250 983008669 983008687
    0x530115080c090307030204090813050102010e100f14010b0414060a09152318033004031b0603050604092d0b0901050f13050a02010e030307060c021e070803 68
    0x1d07016102406014003200c180700e0b41c0e82c0003e0309860961200b5181031000141117a81d4409041d400e0001c4c15081c0000d12040c00b90400311992091411207401c5184e0f550301d0f03904511403482e001400460090320103000d0951b115900d281c0d4660241c400c0800160082403001e0482c00d094042d18400700701234849070f0b00365242c40d0600390026132402071031701000b070180440d240039482c22203110b480b10001d00449449900783c1d180c0201812509402500c25807060b01200c8144401c290100d840600085080e0b900320188041100980201d4000400c001505001c80000740c0c1c0d0034001c00c040703404940e41070115481d4802404219050690080e10f04921601d80e00f24401c10443c0780300c07921110310300c402129109030716800c5130b0900c282c40d8440d241c1d44410a1200d004141c1e9040342d00035441c038541101d490650350754155580400d0b00024180b02d07864900340005c2e50140243e805003038200e0300500c07452000c200c0003511400e40482d40c0d003500ca800000c0080284000a6044c2900c107400c000f1803038400b841c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 983011169 1250 983009919 983009941
    0x705014701053403230301030c051909110d05060108060112150b04030506040326061309050f0a030216060203040509151005030a05130353011508 64
    0x1d200303074503803c446034000c5071000b00c911081082220700982d05d0b0842d844d458246102180f2040e1942403d54000340014070214902074100411108203c481401950301200407956501080e44202e903032525040420007100304000c0100801d041034842004a50354910040d644081c083d2005400100d500c2030250020400da40f0041c500003907284d0080540c0d94520b441c003403551181c0c100f10f03035941181007440f08064000b0700d074a0b110488030088801440e00250130504010004010070700c600c84c0042c40001e14030241d40300c00801604441035644c09141401e182d40d8400c081c0f82d04400510586100050700000ca09100c003d540c540e901540c9010328100410442c1d160141540b540c0114022484c0c103141d48108000d001d007402d039250a61a0320b0312201460845000a00d0050801980000c0c41e001982c064000c03100085005412018910880f4a440c2808400710304c0713420f003040b18400100c40c0a181c09503000c41d103008220b501416a00c81a0040410300000e5140001c41c1d031450110301c01803c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 983012419 1250 983011169 983011207
    0x9070f0e120d020304150507080a03090f14030c1509030d0b031219030b060a0c0f03090905130212030c070e0702013b060f060105070501470105 63
    0x4010404500741c08440301041c1012002c00b80c1c000960700010b01041400c40c20008004882d2032400d0850520039182c0b00c120561007240481020907589921003010841402d40c03203441903420040803910901c0051f100756495001c0c8450000c1889154004c8843c9010590102e100e2011f201c003541c10b164000c42c1540107003040310200340e0305000381c40e40030000e005420064040400c240070b41007800035040700040d044490845040b40152070400c05001402d4106a00c0c0c0740302ea91010314a521040e003400c049450040d03a41217005c0c1c0c00d05101c01d0028513103041031745034200d0b0b000b11003289201001068090340c03441440740c00821b6401401d8100b00e46d100d00343c480c0358001c1e50380c000440d81d000c024001e188018149a10601c0400580d000300300441046026a02c1001c10007004200600305180c1c0b011170000001c114604100c00054001c040000c00c0d0040020040801501541442c610308501f00003070b04011000d600c00008500b60301ca880210303510411020042e1140c52404880c0301c0e0003210906 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 983013669 1250 983012419 983012447
    0x2040f110d090609060207050d1806051c0902280509150904030c06020a0822150e0109020a03080d14130b060d0b090a0c080f0c19050a09140609070f 65
    0x10b5900c001c013000c280140010803020b440340001c1c0c0800d101034a8080c1c6a443e800114032820503003d4800d0140035000421164009014400d40c018401e00c1c0500801030308084000940041005d500300810000048013500b900715144030010580741c40e4401c1c405000012201c900c5807000407608100c4030b0a0111415812601920f020303501000b40751280b400760782c00812000c0025201000b00503001d84005101400700f511402c03d0940d0b1001d5403194121082c1c4814a88207060745c134617110350300540035482035880c4da0b40a440c800089641e0700700001e103038004e00c1580c49414200700382c13a81c020100b4044907220f0032859200c840400749030f894800c4404401403685420030100003c81b4080340c640c4c00c50300c0c81455200c00901d03440d0001d150440b84200243d00c00d40d0140c1c003017208640014004200c0460200c005c5d40c2e82d13810868440145040585c2c1d40e40115000960448003041d1501a0341202280200b201308aa41c02d459804c21b000c02e07508100c5030a40080c8084440c40c48452040b000038400079 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 983014919 1250 983013669 983013671
    0xe0f070506180d0c0504061a0306101b050106080f0304030308070e0a0302040501530328022503030809011b0e0f030105040309030206030a020f070f02040f110d0906 72
    0x800c09401050845a440c1030696100c00300f2113040100780303828014100030344142c05d07031540c0000442040020358080605280e2040102d003102d00f000b00d1244001d003400f01c50918080501c01d2090820500a211074092103059024241d03460080310400001c4404403503056480380e903665a446012210000b2403840240d200c54082c00010241e565401254040c244103010064510042404585084101c2c1c0d04200d0a40fa20b1000c0400200c0c103140030031120400c0d04115480c101402c1c01d0509600c180895003031307100c3d0410810105200301c01074110068800e41c0889001c81c03480508403030031036803017544002c1418000c00140700081c450394030389030080da0240010503030042c1c8400344203200c00c0800342e650000395070304c2d8445100d00c0c04190b0386141c200180e001700301500b4a51001014a0340301e01001c1d001d6a0004040340d01108030794100c074090802e40034401c0c0c44d00414948008007c0d82c1c52030a9201d941040322011030814180f04100c14102c01050f80c0c0d1514002c4d4204001500e405501a00c000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 983016169 1250 983014919 983014957
    0x2070b0f1e0301140a080d0c061b0c1203060803030601030e010e0607050d0b0f061602010c1b050103060605090d060b030109020411040504110a120515180103060e0f070506 75
    0x581c024a10061008440410880c0c072581400b680710000302405041e5840b51004500030091200b0124440b501d1854074503002c202c010460818001401c00d0a8004d500c3d035400c4c4445541c0d4035442000000f0fa103124112010590140b0707a4100c043d03403058003c450254108102080c0c40c3d600030343c000080c0350026800441c4840d040361045042180464a102c08070348002164245240e80c1d01c100d0415600440d04065030120380b01c0401c256003d001d01c413040c1c0400820049040d607000700c20307000015920800c40c4c2904606018852a41340003841201d011906205000c41d10074010310a4403010007029000340c60b003641030384410000c1c001c0e1400c500c1c1c00d0b5603210307029009030725180980e080040400c51816600c900d0300080c0000c645114103422240081409145542d60b0b005850902650440e80f0100e0507443e20350320821115040510294400c40030b00d0307040c40c1e441ca0ba60509048a000d0b113802c100206002040340d84400c400740b41c800c00364001420902582c50300c2c03006403200222441941d004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 983017419 1250 983016169 983016187
    0x9030807140606010302130e041a09010605040c030e0d0c0c0b0d0b0a090e06010e04150903120f06080309060f09090907090b01051602061803060a021206030d02070b0f 73
    0x8140d0000105440c49200900360801c000070070001e0b80d800c12000c1c039003145051100f451003400f805942c00b4030a40301440c41702240600005810114401c814801d91089078144602c1850003004280b0030280500c1c00c040c0707074060742c500911454144001104c050568140e15a004441e01c5042e0300080342d2a41c0603102c0403504001c2c01001d480c0041c0c3c035090014014502e00c0070842c03006c90550040d81c81030304050b440b142500d00442c00d40d0445030800d000283c50740b00e5103400750a5240b4040707080081b81c98180c3c00002d155100010308190210500c2c1000700400907403140099a030240141481e99000f04140d283c1420540c00610f6040151f01c1002c1c203280d9001c0004102c20b2098440e0707045580010350178842c00c249441130301301790b403004d0803c24980610010407150320b07900303902c000c0c2c450400402d150b070941002200400800100806503070003464511041700081d005138001c0490f000304003000581b241800101282940380540080c8000d519100a8982541c410000501400014045102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 983018669 1250 983017419 983017433
    0xd1e050108010617070f0611031e1803120f09010e030a0f050d090e0c0a0c060501062703170c0a0f0602070b060301090c181d0102090117091c0903 64
    0x10103040c203400042220b40c900050b021444030400c1c400e10103508000701c01c11035901c05105030306c1141c05500307040d0013150f00c500702a4110300030701220601c1c0b08a54004c2007481c1070800018065441118141d9100080100a150760389882c401140051313841002140300d5490601c01520305450145001c09403a1040d1001c0313414500060804c54980c2181e00840042143c1404600d07250003042c903254400318034024480c5911000540000e0703524100203802c000d200d1090790300d081c011b500004244141d5030340314802003600043c9006100880b1210712012040c0a00b842000d040300d0300032040401101c02c91099141e594000b00030001c8520850911400088810b482040b135540220401038507100141003118040e08000c00035407080c1d140041d0100010442046a030949400c14003c3d0a0066000e19031401002c03544218550f000725040c02200b01d810540042044010a1761012103502c14100c400e9081e07001903c00c400315410040400e20b00041440310004940c20030b00d4410384041c0c0e41e44a00e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 983019919 1250 983018669 983018671
    0x151b0307080711010503090a03050a1e200a02030601090e010b0d0b100e01030f12030b0a12112e0c0b07020d09080d022a0a06051309020f0d1e05 63
    0x4400700701c0030503454240a4003901c1c070300a029007800c04034510310f00002c1060326200240b400400380200840d000300d50034466003241c481103000000c001008101c407107000c0d06d0b0b41b40510304001040c2003503641050b00c20300803510010403903000d0024425a4200420080a4901c0c00c0d210304e940d65039a1000f40c0c03071f07588148400c10194040c001c0c0c1100c83c1001e00032132034402a650080000c1881c40030042002901c080400310343c10745c003c0c50f031407440e9001c6203045010389000d203079569010400980c04a00c0c2c4c0110306100c0c1c1454800d84809144100c00410b000d40e9840200b000c00e4240450a0034107150b14038811001d844901614200381000100d54071043c180f07c0940d44503005a005911000c1c0301d50b08218000d020307041010080101400f240c000039580c030100240002c0301c1c9244401380c0c8443d03540d0940650b11f44801440e030a0204d0f190800205036070400144800303020501c03400000d440d0040e1003107500820f880725026150440d203c00715400341031604c07050f11851440c046035020940c990b00c586 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 983021169 1250 983019919 983019923
    0x31a12010e072601060605180a090c260903030c070507090207080c0f010b060a0e010e0307060807080a05062b0b040803010801241502030409060303021006090b151b0307 74
    0x70f04054000d60380c028007003c030f8440c00c00d403060307250010620200340c000066a5044056045135600e590441000c80c3d2400c1c00399010f41c1d031182c10030081e81585600191001c00042d4511107c80c0c5224203140b000d41c8001042c0c502c6140d40d08204007080b034050074800107002d51070150084031010b55035880560224be01030f070750030f4500e5403000c00c0703400075000140800d0001c041d1840090207000030840c00a0610b2288401003010301428010740c40c0c0303503401110654520300000741661946560303418041c00700c00d400c550f10b4000541c008001002d94415100301400749001400b404000c91508200c20704610045000134812045015044001085194210301c00e510401c012a203a5140541c07860a542c02c0341d0342c101081800c940c8200d050100400e0710822155440c1c83c40010402c1008240d081d4410358000300105800d1010200c14190005a03460600095000402060750b441c0394031021181450001c2d94080e0f1015072040203915a480504400e4094109005005550b5009a461903006640c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 983022419 1250 983021169 983021189
    0x1005070507150e0d020a05040509011416080609130611090d03020a021c151107120f0f110604060e10090f1211060106080a1404050a1101031a12010e07 66
    0x102d0b101d220b50156107560782c440c2c00d4a83d680546000c1c0d0005a0390641405540e00450b9503000250181d01c003508000a10300703a0380c2c1030700c42d242082c8903804194680025014041080700000c9403040c241094828490242184600104001030ba10b64014109034604400161000c3c4080507065a401401c0824248250000c140f14003041c41480b20b071031108101040d500c040e1811800109001600c096500c2e9515040021203040c04010303038003507000f03400004d40301d89090b04408580c59000455088050645d40fa50002c940b0b07154002c55400300e0350104654260030850200d030000c0d100b504010140b248042c19a940c1481c026006811a6103c40c1c040c2c0c1c0036075030003d40e03000384840c0da205d03c560031444c0d01e4403510712001c2d10011a44d603c410311a041c10011480e0000340d08900d01d6001c540a4481051450f410741000e040155841510387d5042c2da0140d00c2c01c00d02c02c0150b00910607aa0f122824a40d804940c150300d408108010f4089001c42095540f148014083c100b010b0080034003610205403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 983023669 1250 983022419 983022449
    0x30a1508060f0703020f0d0b0d39030f0f050703020316060306050402070c030f0807020405041a060d02130903090b19021b010507060518060405100c0c111005070507 72
    0x2d6884002c1030040d02d40d0090610402825804001910488103804800c490208000181001040b5138160780c64000e03000740ca180c030340414854920184842500ba0381044000210f00106000c00e482030341c5d200040030304000225030302c00900c20b0341281041c1c0740584142c450040d501d401090920300d60a51041480d402d8540500c1450b4052080101825003582e00710708201c105d9981040308030060201420144442114008006141003200c115a0703003d0420302c41800c1c2460601105505401e04881e240b01010005865052001e581c10780203030004c1400071481c1c0792400400c000d25500c1015000c02c41c000c0720110780940144000c0100081503581c0d900c0c24100b080c0024200103c0f140da0703001c1c011900c0028170f8140c0c0e01005036131200b0741010b4005815241e915001d01881d10303c4940035a90300599080206204000c500c0d140d0303801c8000400c1c0054010b0640494960403103100040520855413124002c0c2e06025003445000301c3c050800924040d82611110325240c119130001c1c94041c9204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 983024919 1250 983023669 983023681
    0x203030702071d060120010c030b09061009170a05031305040b061207080a02091011070f030803010b03060409151b050307020c220f06090605180c030a150806 69
    0x848000107003016994420700d00481c01000c14540f002510703a60402600c81145100c68684035035038005050160020003c1d241c2003100500503080d003515161050300f450f000101c81d4100040b2108440085681c5c6050803400e1000381c085911440c603103600c840c4500242100010390400c01046218034011207001000d20300000c0009072188102518001d000600400c491070090400b06034000c2c240d400c2032070041c3e95240c420750003800b8640c00140c1c0301c03a070020560917480c4c001540440c0d603401b0505a8550503111418030800001512000f80464420001084515203103006980c00c41002080401c03181403503100e0419280d0a0418859207698032005c050140c41141170822302c104203030a2031421803414000181d1240c2e00040703982e004402003018002404000b0390700349000514180c0070413001440200140081c030160140800480c034101e00400da40c030b443c43c0700311000020315100e5030955441b0840603050fa00042c121b0b02016480b040d201d07065915031000103000c1c0003400001c00b0645040d07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 983026169 1250 983024919 983024923
    0x2041511160303200a0b07050703020a1a2505040605030604200d0501050924190906090f020f030705130312050703021510050d240e100c02031b01090c060203030702 72
    0x1c4441820303140c0c0030150300d400162091b400b66504c0360840c10b183c1d44a038014103080c0d0400c1003a540003040001101140c01070307410684ca805000c5c4a030004c46130140d00d4083c5101583c41040010080402d90a00042000a00c10402551f0001c8003a10214510300f8460f0340c0710b9080710140d800c1d1020000810002090341d02c5126150043c08100c41d92619410700c001c1c0202c0c0302c2902c0340104045081d03c0e20900c100e0700c0324444103284400700400f55074010340c0e030194100204864021007526a050860041101d1100e000395555145a2141c1501c0d54441003015a101e03030110604049042f03401000101107155001c080fa160f60302c030f40300c2d29a101000c1c50b0007420706005000c240c401c4081d10381844400c80f542801142076800035641c07000940300038284035981456541c0201c99007020022880d11004094100c02440d2403040125036460449001c0c0c6020750708403030560001a4000d000440740c681d0031006008000b101030000084600d0152900c080d540342542050000d60300000520000b00d41c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 983027419 1250 983026169 983026217
    0x10c05040815040309150512040b070905010e030d081f09020a080a050f060103020d020d0203090703030807050c30070506071223100f031506060302041511160303 71
    0x102050001c042c5030135980640020420f00454005030b0751034400380340c0540540d048410310740d4091400c0307000d45071034685141411b00c05c6902da000920807010020b981e500407040c0032142031000b80507125840d59030000300d0b8003490013401000d80715000043e09607011040540c00d0050700320107002580d5941d00d500701401e807800c05000e4007621450502000100c2070000d1103550420400d03e0301580d500c80d074050100207801a0100703104c0445c0300100740004000001b034402c0c2124841e0b2a4145559100c0d2010780d8940251118503649802c054045c682d6200080754400742088081c40099a171420844450115003010070116850390192040c010803a401143d011095400f0713840522480005c5c4140700c000d1603044010b411412207040224204516404060b009000342c1e080c451807082d56401d140c00420405032080c4240c5107020000705142d4070034021201034503405c1855a10050f091102203425032401d004010b0280284440d4a021940c0001c18100850007540c42001e40c510160066211802c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 983028669 1250 983027419 983027443
    0x30c011103070e040b130608100c0c030903060e0a0b090102030720120d060302060304050303150a0f0e130506160215070c0f1403190e041a0d080c010c050408 69
    0x40c052007000003440c3d108200b003c124a00351804a03071001c050006c11883d1201004480105040c00303008034000400040704010745041d2031060080141184050703800c207500c080e0140024182e44000e02c040350881c3c002c403212010603000c40c0d054a13020b403216048104151201c2015035000400d0000c0d01d0307803003081064486e901880c2c1b0001c0c0d41c0301d0302681307a403080341c130340703000a8400081081301042016510070740c01190042c280568034901464050380342d41c011140d40b041c074003007154624021b051042d00d0078240d50303000c8214104c450924441080031040145171302c0d8003042d500c0341034000840501c01c481c0150b41152142203008003c22010342084400060207a0030402d0004201400b0b038840e601c0c4a03aa5000f050303c600240c0c403410140410340d01440010691f100010702c15003c061030680b01000d20249a44410400001100b0007095408100740017900f0040113520785010301e001c00070010050f109035a0340f85000c029014180c00e4038610040c0ea404507001003010840882c01f4130220710525 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 983029919 1250 983028669 983028701
    0xc0b1c110a180e180c060c0a0201080a020f0301051c020a14120f030d11160b1806060906011407050111070203010e12342102010606021903020a0f0302030c01 69
    0x54108803841074500c000404104195444101030821381400740a5210b10300b030040d260566841d8480c08056480a04440803800150300400050408249201799008243d0758130a161542e460b00e010889201b40c010005141507410003103240c0140d60f2403162900510035030007034446809920041240700c00144ca4100c026030007240d9183d00b01d60300802101d490900610f40000c200c1c401000c4003000e800f9261214090044660085082c0044002c586210310312368690003d204281d4812305d030b00d50109a070010b030048041804113407558041c049416520b6031900d03016042a100d61689400e487d40100413100a0304006040d074290304007070180070000346107040208015142c240c48a6100e120308a000300b01c00036040500300c06c2030400800c400e040058000c80641001c4030742403002071502d0750030300301d00e640203280411081d490040c05444226022500901a0b64881070340709400311001640442c218024029450006070350607200000d02c90080d8000d40c7c032415002103450031a40440c00110000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 983031169 1250 983029919 983029967
    0x9021002030f030a091109150a09090b1317040b0304021804120c151b09060206130618050618010f11090111010e0d030b0a050406030c0b1c110a 63
    0x40d440000c03c0320b4202134900c400107001038507802c05560f451000c48071994041c00e03207000c1c45003511664082d20002041100d4845000340c4d9841d01e41d04645440100070441d4049500258081c8003800704044500c0c024255240803581508007801d1070b511903000315040c48000701c248429804d000808054130300f200c804258040c00e05e034545881400c0c40c4115002001265658081005218800d0100f0b0b80382e500d0041c8001c2c0c0406809035001c1c0044200d14001542040c1c000440510004080c0d004885000704c1a4880307207a503c4030030140c00d5000490383c4c2244080c080c2c20020b0300800690348035910300d005c0007216070310700740da501d09451850700740741c031480c0c2040c9106940300e0001d021510003a10908000e40c03100c00c480a400d000d0030b081c00c103844d16401120740002016801d41c001c1c80305054121451112180c43d80d00700022200d0070b0002802c160a885400d10a17028000001d055225001d034000c46400c44d0304030190140d8000010080f00c15001180c41d240746608260728024070030079080d803030f140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 983032419 1250 983031169 983031187
    0x3110c061303020f06010905150a030803010513020f0a02070f0b13060813210f090b03011509030f03171612050a0e160f0609080a02060a030b130902100203 68
    0x140300809080031000081e0003004108260003080540ca0100e0350105403070043d03a4031809070004001c1219000881244072500c0c044034949216080f00707481c2e02c40c01b02c40c2141d00300300034880600300c004101c3c0c41c542c0e400c204004001001001500100030340c1d600508255007015142c510300d44280d0311030011014148806009144503145510980d2028501014565a40002c0200000c2c0490b07016100b4640c110204481c2c02c0d13010480b100c0c1d0512a140d614242e805c40e00200c40300f142520814a411070207000500c08128400405c1041c0300180c548042c10315160307183c1c0d010ba4204c4402c03c402107003040c040e0b000f40705d0701d1088850340440415101c2c06003520030b45020b01004560422110010340d40d00c00504844120350080201a80210468041948402842002d60004d000b0b001000d00d12031000910303988519060003d035000b0002070f1440da0400e500b4808245c10400800c2e05040c5c560001c0c000360b4881424460080c8001d110114000710f060040c2f00c0c40c1e011541c10a0210b400401c14004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 983033669 1250 983032419 983032423
    0xa0506042d050a0b06010516110108060621040503121603111603030509010f0f0b0a050405040819090506161205270409020d0c030b160914010e040f0c03110c 69
    0xb0f04150402002022540c03140012030303051007a600308a80190b900b18503002809501405901c0fa403c003a00c4592aa886010402845009240ca0300b0b00c0c0d00300308121210401280c20070315401c00e1081c1c00300e071f007030001c107040d1100c1000045401400100080d00300340d025681c14001c561a02d484103807414600b0440501c032802c280100070000c0e0038951183c0104041c08000d6221201082e00c0d05e500308044214a0310140140089450151003806200d102054614103442032a004550280a0318502940b814070000a20309050b100000e01101c0000008d160301d9001c010404460b82c411031104101007441c15034118031910314400c080000902c1002d0703032100004031004a450140b0704000001120200050203070035041c000a41001b01c03204060208010002070100343d910401c40c12029071782d480c1d1400b158212402420001508a03c8200031070100040500b40100d4189054000368500c0808542680e0b091790549110559415120a00d59850300c01c101810010802d001d10382195130110729 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 983034919 1250 983033669 983033683
    0x1205160f020f0316060f020c0705100504050301060e01061107081908070c0e060915010509010e033d0204050609040e03040e0a0615020606010807110a0506042d05 71
    0x1105212036100000a9a40200310034a0200c0b0b5200c11260390b550303086920b11810301200e0040358030504007020740c003a8441d00d009035000d13004c07a600141102450b10b800c02c0101d84807111042e0607c44100404501a00c0a001e40c10107030803400c0c2061415450520001d0441800c4d5211142981010100b4031000c140411020034040b02000c2d040c00c503403c0c41c28141caa42c824074200070120ba0300303014001038204541d24070741d120b400101c030b100c00e0595410366518042c840c03c03100140016420042d0404560050031604410b20001d011520004074161181c10542502a081d2200d504083c0c1180c008180141c6801c0078200030f10400d5041618010200304940038034541d141c40f503a110480388400354800c0050310000c0403040b544803c00e05040c40c0f48002002030303006580c01507800c4820350326020300019070309010742010394541c1c0741d940d1074480888a5135000040480213000701c0c9803000200c0d2003002202d0041c0d008001c080018581c50000f0f001a03131002101680e00d81051050801262000c2400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 983036169 1250 983034919 983034961
    0x3031e0e0f030102130801090309060212040b0315040f09051606050403060509030f031807050a03031e030f0e0f1501030210030507020712080306040507051614030c03191205 76
    0x4040444100c1c000280640160004440030240c000c4000903044015003101d10031500a03242c03030060545804041340c640d40042c130f4200340000c0400041080c1012107005540c042c0ca40c590100c080942000040c050316000d8690b042d842e40c4809035081884410300101e0307030f45002400c03030f00c003164908803003d4010b000360320000e081c05a403100000d2040e44140100d03142640500c1c001ca580b46030090700c6145000104001920901c03079580f01080c2030800308800004c0c4c90301031722008103500031100c40c01320302443c080b081c00401d84c030b606140d006003c1038014412a880040090107a40080303030b02280c0340c20700d460300301d6510030001001000980c07108500f8004003005440c001c0381b00d0742c0d02c69007645002402d41c804083d240111075072070700313101220b000b540c06030000301c60074030207074803040012541c7e070145007400040510316001c5c4a001a1410102489000c2007100740c2c1c2c00d04580c400c010341560440f80943c1e041d45881e0701380440665201d0082c4020603c00c00c800c0125007440050705010b65201c01e20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 983037419 1250 983036169 983036179
    0x12050c10020133050d11580606050405011220060316031103040f0b1b0a0c020406092301060206150103050c280318051b0118080703031e0e 61
    0xb08060000c200762a003e244800b41030f1303e0540c00c00b0400e00c9001000c0d40c4842d030078691f09265010000044841e41c0c0c1d9481a4031003820007080100340c4c86110108807500c112443c03551070000180c0d5480fa8010a4020b000082d40070208881604241a6505006100791140c41c80c01c2d20b40700301c90b503440342034a420048460442403442c2071520103800501102041c03151500780442040100400601104641c80c03095600c40d01d20740394411b843c40b1004a03014502080402030040b040400d1040013401d2080380010070205200b6910406041102c0c20304490707400c5880ca48110904100785000001e00405040c8000d196610348400c44000c05801c00c2c800e1810152180702085090424100340c3e1003038291042080c45007880300102c070314a40ca8441343c140120342410040c1003031b40c0200300c12884454109024124892003001351a5503981303a180c07128180a90b07460400082d20120f00d00001510341480105085420f5040203404c152050300103070098103030f9280c1880225804511100310b60000d0310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 983038669 1250 983037419 983037439
    0x1150920090a09061401091401080c0a0e090405010911060f0301140f100816020a08190c0c06080103050c0901120303090213091a0601020102030c030112050c1002013305 74
    0x40022a400040c1e0310030b1420500300407000c107440c4080506594a110240c81d4441c07440e03600d101d0110b2000c023407003142d40400c00500c001030b4603540d150000c11106e0694a00282c4004040e0005158410f0590301038070281e64820b01d54040002450003111100c0e0116140b50a1034200c0310208800d10050080640b122900b440045041e124185030302e080c031500a21991005c8900c0100070010030048608100c0500c04e444401510340c000b1501d242c040d030300708252601d090b40c100f014925044100340c10200b04403000b00c08502082c900116000640025500c0483c50f52540c00c21a2404680c071001501c51000b00c001004281180d4529040700c95060401040003021030000070070010220781d541a8150401c58407070200241d00b00365100d006100300d40c02c440e6403541c2d00121708038082104c004500d02d40030401130141075500c1200300d1000b4802c4040b01c42c180012004168250b124080728000750307446c1c00304004100030486441e150000401402d41403000100d0080100b00b4051240500909c600c02c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 983039919 1250 983038669 983038687
    0x606170a08071518020a050a060c08030603070803040308190302040605180a0515120c030603060f090309190e090a02061e0c060f0402030f010c020a12030e06070201150920 75
    0x5582c2c3c01d40d1141c000c03820000d4003280c00511144406810040784281c41030300c070118452908008800540d00f07641e50308645d456060b510310600b5400070305140d90510030583c00003840003080000f080554425030916481c0c10440f110a2050403c200441042c54014401404410380c0802a145c039500c1000e961070007441003401290100c420b581050341c0140b00100c40004801c01c00c00205103190482008000a560788182e48a441c001a5002681070b0410008610f09040c02c0c801540c010020b80180da203004500030029001c80708c0b01c0103170010222078002c200505d41c00d803001d59900c00e000e200030701031400407a4005481803081901c0c040200c4402c2848644407185442030761480c00d2004119015402c084510030201001140e04a110344a8940020f4807440c042c000e0b044441001e0b0028408070001c0ea884204607030680d41c40c801010b58881c003280c0b100508210441c010f84281c0c000056800c150016030714051982d40244e00c01605224010345481030254401030003500d802c074201e494000403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 983041169 1250 983039919 983039933
    0x80a0f0903151e060b04140f06070210050d0903030f0507020f1203090a062915040306021b031207080603011109060d0209060712030b0a060e010c080c16030606170a0807 74
    0x3400400300f505180001c04030300c21141100400070344515000e20100310441004000056500c80c2100307030080c0003031000d0801406d08652a0f40c03042007a0810608040440c0c001e00121001c1d20001e0300002d403100402d4148056903c501ca4100d25940b0207003200d5043c00300900d65528000f482403c12410020006401e90f400788111402c0551229040c411080b03881895400c2c1c06458055030020428400b0b1200b06141c040021104840000002402d05d451030b25010004c0d00074412144041005040340e002a050134001030004444c00c860220507424a401c0040010340d00408040c001d03854004001e42528000095409880049a19951300c1c6112000b04000c4d00800140581004011034008200b02561030b1138880002d0071360b4100041d071044410040302c600d15110342c1c00070030b51064642503654814001442c0c80c1f40102e05091400489264030382c0740c5900710b40030320310100c45100d007481000070a000324001004280000300c01c5d0401c01c1c0031103459918000c0018004600002c40000300201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 983042419 1250 983041169 983041211
    0x201030e0304080718090c1401051b150a0b0a0e040f020a1d1f12020a0e1302130902010e12010e0d05030103030e0d05061b1303080a0f090315 62
    0x940d015203072100d07902e40c5000d50b5819a8014201c0f4154145002c13104100c0a00c01d03c920390b41c1011140681c1c1c1d1a084404041e0040301c1650380c1088020000f048540c070160074a0100d90001c1c5000f01044501400c1032041c1003c00341038150403030b00740160001c0310350f43d498180c825900020318244d1945c0310b61070b00c58408503401400075007024104000042070702984113010004000104644040d503500c0c084615801107a807030314800e0151822003400f1001b0f103004240f006900c06000240302c3da45805074944280c6040328034440d80c406504242c400c41c1082a9180003800000509200040c041d6001800d2a04422100790181841070b68000003110250003246203003801c01c0c1550805011440020055442401b0580c04914005100c40c190305003a000c60911030f03040b101900d0162503030b8100c0c20426020901101c244281070044000d001e2000c1c0f8402d00552003484915582c0c0c02003100030303282600101501d801e00803003080070004142406002028070445810000e0711030f140300d44100d0240c40e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 983043669 1250 983042419 983042441
    0x5060a030f23010b0304150218040f1a060711010f02031c20071a130501050109020d14090a0f020a1707090e0f03090f01140d02040312030506030316020103 68
    0x401c0c001140209400c0350300340c1e8602e41c000101401c0680c0c85080c070221074030003030f18001d00790940b0303d444200c010b00c02d501070b040c00c040d0180c0c403e2084a40800080c1580c080d05514840c0c0e517600d0701001d111000b0599410031050090703516604007007940d25854090b6407182c455074180560303000c440c01d5a520900440d000038030440400d844c41d0305101c0e4148000c108030740040c1c40d41108402c0840842072f000d020384070080c3e4080241046556400e40c3e0f500050401b41c00050f01e5503000b0318247c0081e05c28011940a010003030030040e107a200c420003074029101c4400741070941250381c60910407a5207001c180d455180b80c001c10640c40e50456403022882d240303da079010b41c100b48040080381620810108180d8102d881d210014002000c901c4203140d160851061240000d50040141c0784c42410300c608080b0b20760b14141405030044202840030301343d075400b801c4121850f944c005003d100300b0081031080f206a20faa458200514a00341000c03c1d904d02c80c03046d41189101c58555180b08580c0311b9009013031281c1d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 983044919 1250 983043669 983043671
    0x1200307020a0f0608062d12030c01050a1505060d1109040504060f1401120308090a05030c030a020d020c180402120718060e060d140c0915090a090c05060a030f 70
    0x3d540311031110498809024603800110050085071032480d0901040c1c40000701d111091800c142040420000010721001044c1c010025180580c0c10110a00107407000902040000c611031810210f4002203c1c11500700004120381c0040510039a00c82d00142d408440d4900d100151042e80110121454018a040d00f94001d0400f1300b0801086040c1e001055002100f60703051020740300f01410041404401d004040018a100305520040391144000581000e0b040060b15140303445512000e065500580034514198000601c11f200716078100b200614840c420302c041c1070384920700b0000652240c00d025034480a002104081000d40d0365500c00c402411444500304e810b003d41d00c140e01c01c1c4114040da05610250b251170300000d12100c840c44064401d03d00100380d04030380401c66a903000512813040150205228480c0802c040361581061a4011860061851403000e1301d48200203d030320000707141141090901040100090140304103000341c030740440b10151a454020b03011001440d144160070700007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 983046169 1250 983044919 983044939
    0x3190e10020705240a0209010c06060801140a051009111201030c051c05070302090702160305100507030c09090c030b0618191805072d110c0120030702 66
    0x50350481d4024190b4521440c02c0d1a030304000c0741600d50a50800c0d44078030108501e000d00290020803594002d01c40c1e00f6050400311600b07070054403180d040b20030680000e00300303070340d10f2443c001d1340f0082400103a80940c030b0305018002071a000c05059083c248a116283c42c3c0c90320340423010509a02c24040e9490ac03600880c03018400e41c0d503400e04403a800c0c41c50fc40c00d80039801030b10a40130111010036004100a4202c00100f5140345980d0a010390b129000340098214050101c001204800b1030700080019400740000303204114194141100711007014145038289483c00040c04580b0b5004100340c1c04075001e8000010302c070000400d09901034452046441e034084000a01c030341a10b10101e080d030a242c113003607408103840d041900f5012600141400ae0501049103044450700c040c826420680d07018030300e032801803004844843c00242c841e05e1310303400c41507060b5581d590444880d80500b00001c04012480141408441d5100107402c000c4103010003d0040041103040c95020810400c44100b603a01820201079 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 983047419 1250 983046169 983046193
    0x9150d03090609050103060305150709080d03020706052d04150f1a041122051507020102010506011e031116030203040e0f011a18130603230303190e 65
    0x105800d94081c0750040f400308080031850303510a101d49401d03a58000010700f44080d50701030107802076000402003010041d0f190004241034100b0320241443c0d40007602e004d0307143c090a113059001d5490040c0421110080e02c0c1240c07450010040c001004d485021481000585860401d44280c20f00c0d00c52260080341850f070416414011a4400062210b4070604008400242c00800040e6031211700d10b558129001e0040030040c403482512204541c010585104015a03200c003c101e40820400c2522f131541d1000c12075205651b0203000d0b5660022003480c0c100d02c0900e2400c000c40041c0a45e04182c000c143e0780305a009016198a8201e40d1055410006c00b0700d648082e01e0b009503254054080e401070562101c000c1074140c07095103411070580f2038003084481c041a044c10844119041400c10070380002c0951802c40c2c49454007240a40c0c0d00000c080b0105d441402c40c1040184402490700705034115a00d15a182d2240344048190703030f00b00140b02c0c41000001c105440900182800201e1401140200580b0301e003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 983048669 1250 983047419 983047427
    0x804150e0c0a1712030a061e231c0503040e01290325030b09070914010801080307030e030a1712010618031b3203120909150d03 56
    0x2481000c07035501c9250740c1c8034842106603060903c04102d81d03034450a0110500e2030318130061035100f114803c1c005034880d03072092000000343c02e1418454a081800c64244001c001075400707075288002500080040030803640102d562600600410501c2c1c171640c2d00b462041100c2402110b005021040101040c3c0d611640c02e6070801e0010203007401145441400c96541e01e940340183c911840c0000c545d44080344090070070803c030200300b804c8442016583d001308045950303111942d5000710803a66451484c941070148c82484140404042d0b41800f0349440104540000001100c008d10351603d88105150482e10100e407a00d045564000e0910484028040086420001810030070402c64004585642c4e50f040030b0790341a211060702c459040c4840350038400300b80310740d500c500c2e070f02c490b00804041d00355109410b114000c05c04804840301613540c2c800c01c500802200790004140c80c120041e201c135080a1440304120300c81c180701c5034025000c0d80c0000310300e1a1880c3c5c010000c03400c090003003803d0454500e0010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 983049919 1250 983048669 983048683
    0x1090f02071703090d0c1106030c0c0d02011505010212030103151d01140f060f0d1b09150806011215060323011a180a0f0606050a0201060608040b070804150e 69
    0x1920b10800e02c100c001c11b4891240140a6504880038460820050b81800b4213680001d00503201100d00700801c0c1e60b503600800102d001d000c1d450380001003089482191001c0ea292a90105d070455001c03072840e5143c44a50b0003201d044075484450030302c40c014a0320404018101c1d034054500303d0b9910748010480b0034419041407072030a18550811a071a660405882da101c801610641d0f082506a6600c07201420101d511403001c80c000c0d008012040c0032000c0f030303120701c41881c1c1103008075540710410400c5030f4000c003141002418484001e060103604211900c0102c11815070f020303204010f514aa4204d40c4c0047e88400c1c0a150080449005420004c0340c00b031341c0803500800000658641403446601c2644164400704d2490002c14000080d4001100380703092500141600160710b54a0303889011010003403050900030301d96600c604d600d90002080107404c442c01580701c0001e02554804010005901444441d4420078509240c9855141c5082084441c0502c400c1c18803014641590082042c00004040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 983051169 1250 983049919 983049931
    0x106140c0712120306050301180f0f060c0e12010b0f1e0301090605010302031e2a060c150f040c0612090c380a0309031e050909060102031201090f02071703 68
    0x1408201c2e1b0310070a0500725410000e2275081040c0c2c21a420000460746083d4044046c02007141e0200e0800d16258501191030421404000c40d00030715142c5a1800c280108900e01100e00b030080001e007003010b02003140002c2800072940f2440f40010359102e410703500c1101141d5035a002d0002c114061070f40c5081c1004000c20300080c1d01c07d1003084950304100e500c507072400d090004d001d00901408168514184860399080849543d941c0801c8040b0000703440c0d2401404040102b18014501d20034a1440092041000380c4500f102c2d0464104201c00701c1d00b502c808400303c8041d890014603003d4450700d00e0000b4010aa00140f0406082c000080c884040041a2401d2118541030301806040b00b04100c690710003d12008155400a01240b54118040d80c80040064000d0400e440c40d000c00130380241c407202d0301142c150082407004c64880658205215a20351000003030005510302245840082030380d00e0305100c0c2142035500d030045044501515010790b001c60380d0000030300c3e100d400503070701020098000b1501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 983052419 1250 983051169 983051171
    0xc28080a020615091e0903041a0703110a0302030306010f03021213060b01030204050906040e0109050d0c030201061220061e04081011030c0a0c080c0d080601080106140c07121203 78
    0xf1200c443c0c50301d2460345000f0030060b10082c460300b1102400034840d04000304a480c06001c140400500c0022a0040584409401c3d4006503038251500e4091f00c2d918292000d42910390110501e500060303000011290044401d083c459008012030400b10013a01c078050640c1c2c1308644c3c40d4148403420041024420320144144401d2040b01d141d68011801c9016600c00c142d44003a1520100300e284c00e15610001c8610406030011030010b08a803249071800f8000040c1d08001001c5a0008090586c28881c2c94040c007112030200c150388a66407182c0320659a0a005902038030b650884803102030ba504411610450610324001400c980c500f034400241e80c02a10901401e8000c1940d080c240180600c5186608030902e0030644c00c689481c82800700607000342540310306210341204002c0c04a1000784c040c00c0c00c104841d0040c1032640000c40028070444005e018281030040050042c011650803201304022960119175050f100c1d05c2e0100b40514091243e4007200f056410f0b440c00030103000452410070b840c09000d441c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 983053669 1250 983052419 983052451
    0x150236040c2001020c0309011407020405040c30060c2a1104052701020913090614240d0204050106080f0702071a031e070201200c28080a0206 62
    0x11443d0903885981103d0034035801c10000002d032580140c3d003400d9003054120600d03090141660120b8125101501c0c10b641608244504002d5108004c030340c82408614038480c411180e403014030060084508050003402c050703c0e000c0c0b40010521500350890f0102c40341058850021700310f00c4864022300400e4040e142410700a00000c4207090501070329008038a2040250028a40d040b400d03c0318003100c0401c18101c0d50204102180c0d9a9203004681c4800300100001030158203524000d0219140130461160701d1640c1000c02070b51540810324841c3c0d554503040104c1221007054002071100c041e14100940c010300d4a400828400d40c0300005a20806501500910316180c02d00300340da46042d14032403804000c142e1031208421b200b44002440c0c0048c40c00c46c0121001940d001d020458480442d00000143e54603e4072040d00540990362025004034014100d240c503a1442001380c482d2041c100a00100c0d1425580003003240c1c20034007606810390442d80194448a44180003500e9100c192503850225403003031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 983054919 1250 983053669 983053727
    0x120601171e0601090c0912060c1710091d19050d0203070c030318091a0406060c0b0115110a1b1520010e010c030504150236040c 56
    0x55051100d51a07030041c441a031070301c603801c401340c2110300d041030401c0080000012800300d20f2051100152051b240404c92500c0b0f0000100b445400503013500160003441c060146842811800c501592001034001c0f9004520380e04004c200d51820743d0741c503264410100c201410300b480180841c6558802c1e8284c1d144001c501e070007240d0368000d9070400780c0390103c0a030781080040e000c0d03009480c0c01d00780c0d46685400f0507070b2442004e084030380035110310564203640280046c1524142c801d800c090f069034144010450f0b420b40391000030300030501500c201440700c0421400081c2c0264117404200706048200e84850030207252810b40c001034140201ca050b143c1c0c1502040703840280b0320000502629a4405d902031321060b5062451150101001500b03540e1034006103407800c001e00400380c0c0b58015440101d224285032801c1ca80450081c1c0701c862940344140584040c82842121020002000444042d14a0303002000f240081d81891101c982c01440d0090340212282c0140010340380c150a4502004404405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 983056169 1250 983054919 983054953
    0x60403080d060b040b1c060f23011e050d090605090d030b09040308060d0228140607110d141c08060a03050d14040b0a0302090321071112060117 63
    0x1409845e03290402481810000030800c0e01541b10100d0b01c2c0340104500e0740c6c420381800a5000d640168903445030603c1000c9004202034040f0240041c00e00c0c00c041e0b1020380303c4424403440d40c504681401c01c000054442c40040f1035801002c032454012031b08004504250034060b07510580d03083e2081c00311b8240440f0b508075213050b0140a1055415448045660b0f07151001c1200e80e142d2058101d0740300c61030002c88104101464100860600c85081106800e42400c11065104844500c06071042a0401c40078002440111100526010a4451174403c3c1c00038500107201c0e901d01c0281900034070410442d070540240c1c00c5a1034103c45101d0702d541c00309480d0340c030501039076201501029100d580000800149148101d15840510748515240c80c1007988550f60440d190b40484080310001342c0120725481c4901d024410201160324540c0c01e140b5071150410002c009015840307001c0c01c07000038205986200e8849034560060070f14407005550896841d000c6540e81500049141c00e614454944408401032075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 983057419 1250 983056169 983056177
    0x503040305070807050a12030501091505030703030e210304050a09201c060801060e0f0906060f011106100e0a0b03030f09010207080d1e170402100e060403080d060b 72
    0x5980d000d161907283e4a0f0307403d1561006034105c54502c1000745450103e88207544043d00c2d0201b5690108155242c0030444042c0c45481d40f0801403003410b0340040245982c0001c2d0401140d85c1400c10350700f05e5207040001041c501c0c10403541007000d61007013488030900b0340100041040d99001c55001aa00c2d8603140104219202c0c084400c11010902c0304400c225080c02c0060300074019585500b840d007141440440050302c540c0c1d80030311141da4440c40e0601009400311000d0358082d0a00882110502d0010701c40b46c0d407038402a0595010341041030004940740d00c81c0910441005001088400c0c2c0e040c80e2090181e0085a881001c508042400100f000c0e8099809100b40c0b501c4010029414030f0000b01740220141d00440b40c9905600c2401d60010b4501000e00038441e800c4296101e0046d00d021106000a81004030101a0f0130007d20b1048151111003840c0d40b2074009405a43c1c1c400459100384040e590a149032840503130200303010400004000d003031002407400700e1004500b400016a14841045d042c09 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 983058669 1250 983057419 983057423
    0x12190201141f210b04060b04060f08060106030507080106080c0f120906060301020c0c041805010c2606100804231b0d0201080601140d020418050f0402060d0e12040b19050304 76
    0x3e8910500000306a1003088150880c1c06a0310001e510305030400054111000c0e58000358039400707100310030000ca4805121460040c051801c0c01d000503d000d000080651405002e10414442d01401040c0440c1509083d0f520f40c8044618540e600d80c02a91001020101111034006901c62440080c003035082c1030080d900c3c91048a03000b461440003800030000034110521500d80c040090008002c0403c4090250b00c440c800c464071040000020620a407030314001d5180b80c481004248003e002c1203841720080c0c4564443d080c605030100fa100c3d850115a480b030036000880d10005200c0d03035201010b070301186045441c002882c00d0b403100c3e0625030074010504031800000c1e010904120006180b075000e0403000c054180c080304041d20308412019100101d8010341c000c6801c4407400407040507002e00324440d21f40c1001030100c004415290642c000313401c81c40f0310140b4000c825142e224020307081c03004209041400b01490100c980311a1180300030b281c0341d0040c090640c0500e506412041059008030101c0380115 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 983059919 1250 983058669 983058719
    0x220b0f0c10020d0207030207140307031e0506270a15050903130e060901080f0d120902030a12080709080d181d0a060812190201141f 58
    0x2520464808a9a4000440311655802038114214008160b4801030031203900848005882d65900d0074020303d400056040b101040b002c03410649010758000406000320780d803100c0c4418016407044402d80c405040410300515a10a200034031071034002000302d48284036403841d580c0c4035030310024650a80d10041c0c00710241c000c00d00e4421000080b01c0c1c2d0381029a0140164044078a440298507100300c04075096405251040c0b4000244202480c2c00c0c1089401446031400400f100c0c9451100c1584880e08808410140000d445142240c85116042031100c1c54000b0b0603988405480d040c205000a40d10a5010000e20003100092950380900c82c0d00c07003510340441c0140321000c8106400e0b0340d402204000e40d0821604003100082c59042901d200f42240850701d4548002d08000810500761141e45c3c12664584d00210110300c480004803003510210320713164500c421181000c4206a004042d00000051000c0c62001007000c82c01d40d500b4952101d0f80725404031101c40d561005684000c044200101301a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 983061169 1250 983059919 983059927
    0xa030e040207020625080a05091009031208072106053c0a030b07030b04060f12080306060d0e0a121404030201050309010e01020a020f0c060405010903121e0302220b 72
    0xa00d02c266052400c0c03800c810803040d42c103065120032009403c102d0744440011400103000b4818107119503c810ac010040c14611100b0381542e0b00c1c054104080100c900c10040100e000070559481014800140d07803243c2101c05c040741c80b804c00c0310003411640c001c05004941615100c8104446405000b214054070007404040d254502e002e010719485914000750b0204d508500800407481c5040124000c88803a1400510015030105002c203540c00307030303028007130340607000d5000c100c1313800c0703c500b03001c1050360200903140e6a43d500c20001b4401c1c00341000c180d10711450042c3c9001320071030004524419234010b21040382d030940f103420101e501c0301c0c1403404002448801c7c00104010b5008001464101e400d00002040111042004a0032a00400040c60069011900b181d4214000380300741059190240d4501b1716080c11b220028211110038171006200310082090655118460002078080312020000c000203e100c3c100024060b401c240407681c42c5244140450f220085070b11a032001316030b0160b41c99410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 983062419 1250 983061169 983061187
    0xf0103030c0f0812150d0b06040f090b04030c0b09010524042405011101050c04050d1e110a0905070e3003120903040815071b050a030e0402070206 64
    0x580814090480b0300c60303405142d21001400c520080c11086080c0004a401c51174041064102d42d0b000a05640c0105540034140b40412405401c00c0d6120400f03403404a0201522540a0010311040c20060017448850007030000b015803103a81c910b051400341903c0303406ea41722601c14030308861081d18400000c10501c050290800d544042c0d81507030b290b000b80300184038072a802540c81c01e900365009040c0e5180c400c2409010315a00285041c00008900c0000c0110313140007104001144528001e05200d8041442140104a814000f00c807000441c10280c0003038109030300d401c44c0001000702c0d2142c403490102c1c8000c140b41d400351140383d00c140300170381d503114801940f4800c0c402c8190003002915000d05000c0018009c2e82000741110b49410404c0005540d2001c44030066603507484040e01c00010354200f00720806c084400090035a000e12280304410406450f1100140c5080001800c1c160134141c001801c034060280110305da01e0264081d0300d52140000400007000202e1042c5000258000400e000f2000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 983063669 1250 983062419 983062427
    0x408100b060c1b120114041506030c09150b030732040e0921030a020f090d08130801060b0706200c0601061106040b07030b0a150504080105010e0f010303 67
    0x104040e4007400461502081180e1581003484450204850b1540703e420800242000e44005402002c103600802c01085401180c00c0404400b41014010301c01090036607894800c0c0b0740c4518000e44d80150702c1e1a51a0340c40d14488064451202c0008030501c032600006501203003201101d210303552958500c0790040c2e0103000344400754150340c824912541070314140140c03420000002d001502d231800c0010781918040901518081c00d0030744140314400f9404032045658202c0090700d0b04400700000c05a11500b9010101c4040e0180380c03945a4000c2c2160348a00a1102e094018000c0007218443d5000e155200c40c6168203888052044860400c0100401c03800b081240d0b10400d49490810041254100007900340c212541080e051406c00d0382141004001041e04808241142c10071400500883e2405444018120303000414110a05880d003c0080c855683c1415040242540c400003c0786400038070b2005004d60420f003c0c1d10065864100045400f41441c0c038030503c22070004a58410507130a55404031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 983064919 1250 983063669 983063681
    0x215070f1b0b190501050d0b0402090406021e0d2004060e01020f0a0317070c03050d1821030c020703020a030314040e010816090c02060619080109050105010f0b040810 73
    0x4240d5032248600c00c0009140102c0a500901d003000101c01c0c401102056141150b0341a031107548500c2030b024030f000024010348843c641c81601141c200455035240d05109000c1c0c070644039107009030389030028110048000b0308c0103403101204200301040311000071b80308003801040f0074281c0740084406102c1081010700c90402e1503450401031041d900b40b1040c0a00941c40c0c115880b504030f02040d600004010924103658402e64028054545000d0b00d4046480c064514400c50454000300c9440e20803179040e81ca001c58080c10459442030081c00f114516100541c03406a032841260002424a100203100780d100046078002e4a80081006030140e00c0d41d501030b10000721080110003d103006002c0050701d40d4541e00c1d42ca0080038284082e2030000c5025001000301403482d080014034500e04900b210409900003403ca920100c1500eaa802c4030350803a401c644020400c2d80406a01d60805a0744010070106400040c101c4000140c8500400e8444003a100340f8041c600580c2207a920800b80c8003c0c0c601140c0050f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 983066169 1250 983064919 983064947
    0x280302070b0a1a180a0b12030a020c0f0a03080d022203080a09050108010b180103020c031c0606020c03060f0a091703092b030504050f0d0c030215070f 66
    0x10324280c6a80d0701e0030201d44089500600c80e641c1e0340341c01a0b444400034003c0c0d00c40f40c4100c5058001444030300400c070602038060310880c0e1050340d48407859032640382c0814901858000030100c07502c55074500c0000b50340d4000004814004c920403403000516080000c02a030a0760f40c0004860b040032441c00303511009412900d6200741e110700f504140f078400e08541c03080038061802011042da4a0748140300240200107160f00c4603040002d040010000d50348148141c0b5407220011080c94940c0f0340760f00040300a4064000b10b90098000001c039569103d1182c0c0c802445c207851780380c2c284805c0d566098242c0c1c960303d8180d41c440e056000a00010743d403102c46401c09a000c50303011400138800015869005070401c540074131108100c0001309200c072000007080102d62400d010140c004441041040418903540c0021000c03062540b44d00c0131404022003480020341c041d0b105d00c21240103800000004003540c4900000b43e01500030318420714620307011070306002d100f00561740300d8129003003000381700b214062050f02c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 983067419 1250 983066169 983066171
    0x7120b06070222050c3615041e0501050a0f02070b0d09140703020a0902091c0f02180402011b080904050f06010201060b07020315040c0308120411062803 67
    0x41180142c1c0d489011101d540c144580d0185036843c0c45070707104120f030700141c141c903045c21043c0b10142e0302c500000c00129001001480c021000307020f8820800d4459552154513500c0b00f8414a2000b0000300c0d44043c10884140141c1201c4461040b0300c1005581c0043c090030340010000c01680a031140114020550b4462074812a00e52581d1031303103100c0080d000401c00050b00e644401d03115013406003102d4140055522140600700142c5141d00042429020f071003030301c0c08250089044a440c1c2d0721000004041e18840b07180d0b02418001d071916a400c0076241c90101c3c441c6524051042c0758204114207030b44115410b0b1982c0c0c1d141e900d0b01250b0568040b44600455051400f00000c400d1611103010319801407e00240c41d0a8600b0407100282c01d68015422410503808280b004c000569000038020b0700400402403051500e440768180000351240540000d0140d0f074000800c01c80005448459034481d078014484948140b4402007042141d00c01d0b01110b18a0844005024408888848401c80d814a803814 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 983068669 1250 983067419 983067427
    0xc15150f330c030a02010b040b030c0d061a061c0e28080f0c010e07170709020a0c0210050a23091327021906051e0d05011e0e07120b06 59
    0x100b41d403850b4444e0711420b0060351241c121201750b080074005c0d101d0058086005e00340e0952203001103903016a64000c007405071604c901901c1d00000c200c02c65804100301c0a0840343e0f0b11940303501040c110b0ba81241a040210b89884140c00c001c0c4004550b169101000c0807969a000b070800b0407c4c080707482016000c2d5210a000c00c11141c5040c0300c0c83c0280402c3d4101c1001040040e441210070303040c062680d20070141d4030000b28004140540201d808001d076800d8000c01600c07540200c5080b120b024030913400035080707440c1e801c1e244030064028020304003180d050380d1a01c0c00070400c001c440d80070708000b207003050b04040288940307190307450b0204060590814900f80010fa1184251244841d510110403018a0078a880506829410900502005039a00d0a00082050f20b4000014054424240b2011002d42e40c6038034009000d240b08121104d10a03407140c180a1540c5409610008680b481d803000070521502500242d01c0c244008207a00c03514641e12042c234081d13401c600d0480680500d0900380e41c0900100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 983069919 1250 983068669 983068687
    0x11060f130f11040f090b0106090b220e010b0c010506061c20030a060504050105040e06040f03090807030303020c0d14030a090c1806080607080f0601050c15150f33 71
    0x322502404032000d101c0805c1035121400c0400f40c00c1c006070404410401050f03c24400e820300a02150004524050440c0012f20306803001c1702c945074907800480406a20000000304c102929018140009501c2d000300450380350035080051500c9070640501480d03101d1450840b1100103613210104080494170008412004040c8040090b070040307a242c4a4a50398400074804d6041c14828540500000c0c2d604002d400c0008800da45d40c0c19000304002c0480381001000c00130944981c605070001c140c10317401c407260151640fa01402941284c0c861141c1803240181c01c0c4007403072042d1400a0b10219200d4607600d10b031200142d0001500034420140c2d5228030241340026500c0351054401c240c9160001d00245180c14001c3e0b80d814000f028148108220b41c0307400f4480e0040f98500c0d4560440800d00380160b440640000b12410a0441e0408078420b1a05404100c3c40559000440440b40700c101c2e03030319400e16102d608002c0b6000100500906103204508c17010f20860001c2042c4501100c0b0100fa00e003049442c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 983071169 1250 983069919 983069921
    0x7181701140a230408121003120903020f0d03090611160905010806072c0f090403080403020f0102270a0b0705070311060418090305130611060f130f1104 67
    0xd69018803595592140c152000f484480366003a080a0000c00d04141c0c2000e8480302280c2c010003140c00e8800c24102d0210301e0640d0f50300030403001150f011003041c2d460b6810200c00707445040984002c0c0d010350810700c0206094034113042c0d0395441c6541038135552860f90a0800072180c1411303095591100e840351140708545000e59036418801408481008140c070341c10300e98100c2c18070402030210720901c078881500d41403c001004500a00c8910000c80c03580500940c000500310352a0070540b075420007025014401850f0f8400c0440e031189009801b02d881411140090908030301c2460007043c12048482c0e08000c0229030107800c40c0c0156001040040c405031501ca0070f50300d82c1d0154108582c258407034103007001003004071005c008046000321601414a854032690303c181d441280c12024500340c0d208001c0c0101401181501c01048840850704401c680f1a000901084004401c14030345114002c0000c55603800c07540d04902c20100580d010b2407c078141d41d0741b2000b10007211812610309002040c02c02081d00c0d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 983072419 1250 983071169 983071171
    0x60607051f0b0607060e010e030715050603101103040c0611100b0f040e03040f050f0f01050a0903060f020a0e060301031703040c08150a140c09060c01090c06030507080718170114 78
    0x1170500010580d80c1030490314212030002e181c911080d0070030301100011403150407190342c280c850800042041ea0340c15000070b042c03502c0107140b16481443d19000d0a9207541000180d44218803600503081001d4a441042c1c03112112200d945400c2d0384075160102440c00a0342080351812000360801d03050340080c2d000130f000c3d540b031914040b41d5a800031804001200c500d6122000410059410302c08908407400841c1c11500380e14038444c14010001200403803d40319007142001140c00c01404c0100040a44102020750b0003184001c0001e120070313903440ea503840c003182200e040f2948107005006101040b03031070400c280c01c001e2003620b440b46003000c001401070781800240f0300d54049ca905483c141c039020180f01d08403000c0051004900303416404006000301a41e0481c0d011a10845046450302c441100c11390143c03440d51001811111842000a00b05801d5004180030b00b5140d00c0e10006690360620880b80000c0644c0e140d00c0004500b00c081140074140c031500300708034850000109410311820341e80e0f402048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 983073669 1250 983072419 983072423
    0x231e040e070c0c1202060a2001090c090f0212070f1e02150c070c0603051005030f01021b060417070f0b13060507030c02061609051008010e060607051f0b0607 69
    0x440c00105904000703083c5400c40c0070386010b8052851002880d0041201ca01807080440c0a000651002010204134881c42503901d4140305d0080c01450020f1502c2c0048a03038a1152010381400c21000480840c1c290094031052890120743d0030003507880c1c03032040b5110fa40c0c984841040c040400b4240407a6581c941c001510031109400074400740c0360814483c00901b000a00040e0503d10910078500050a02b0741d0345011140140360100701d9440f145035445554850b5400305515104046075502c85240640107010f0a05a800700318a40980d40c01ea6140c8400d130441e40203043d4800c900d03501e01c2c003442e003002408825000d2260401c40040369681c1c4180240306035120310600806001d01c10400005004440d0312100038603052003038414050020350303960000750403080e1401c0155600841c1d071348209184002400c00801045a1440c4130001a212a1080c028010910880c6c030000e40d807400e003041191082075000008180802e40306245180d0b41421040a1540d103031a03040c0b0038010ba4448000d000c10724 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 983074919 1250 983073669 983073677
    0x30d1a13060305061b0328020c07080c01030b030304030f0c0506040e0a11193e0f0106030809060d092102010e06040305070b180607050901231e040e07 66
    0x1410340c1803c51500c40001e180805156001c0e0703103c0395000d07400054a8108844480b00c2c4507041c801c68081c40c500104c0c3c41128142403004c990006200381c00507880d4115941002a2a5010803000044050710070b05030321a609035108020410008202404d422030243c00fa244184159840c0c0e400128a640154803808510100c1001d100c041030240c4100c00d1840c4421090078601400442400180e034984c89807070003841503c40101c2e40e0403d004011402c201c078190071041b070041030804007400342c8504009801041c030640d003605001150503c91102600d81120200e420039402000304440ca030302120244400540741c2d03008400141c000c00d40c3c00c408003403440010003850100e00c0001d084640a11102c101e5a00900510000c207800c1001c42d0388040d00f1446550f480d940d00908151059482c40105420717204981c2040800c650140141c080404244c2c0c51442da905e948900d0750588000c06050000302c001041200c4103911164110541c00d509400e002e8203150303032003000702e81c200c108441003004a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 983076169 1250 983074919 983074931
    0xb04030c030b0708061c050307051c021203010810050a0b0d050309042f07050a0b01060203030103020a09020a0e3615010207030f020f0d0f061d0a0302030d1a13 70
    0x745030b5401d03602c1089450050760034503200e000554465012403041c403144000601060134048240112520b103030300841107450366854000d100c0d18205094000340010700803145040551002103007240d049031114002005501400300d208801840b01400c0c0c1da0010756581c80000407a118a00001c0b010ba02810145460f01c1104040c0000da5174018019006106907400341e040c040d00100140003103e40500720360b40c4500e01d030300c2c0c00340c50282080000f40140c0c070303814000200d4075400001103058074803e8a0442484c1c0c1d0f10480e1700c0a90103068091000310b680c4c1c10080001381040c1440b0010305170520b1410240c0c004411407800e84003032071103200c07211240a90030481d0440340c1c4105125a10700a10013421001e01d141c45202c44c22a607524000d10480108103d4a510398030720a070803007010b41000f03401c5251942031501000401c21684170555004003000e8500d0b003d40c010035400c0c200c3c1e825401451500744070b002c001008141c0840080c0444103001c6c816480360b2140412054074010101001406e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 983077419 1250 983076169 983076173
    0x60901051f0501120507110303010305030d0c0309120c0302011e1512030203030411040b040501150f03050705041712030403051c051302220e011d030a021e070b04030c03 74
    0xc100701003610314002803801c1c03410022a42d001d420340f01044c445a01c00250743d1942902203440c00d9400c041789113180703c040008020300c18040001e20000403060401c01110b009458290181c0b851400c019004503080f0310403404107800b0f9000c1d01e8a55200384000a01c44164401c00700e001040b030040c1c2e0440b903503210f104101d03a9082c0480840079203003c41010842c040241d50007542c074031004000030440510035010300700c140ca542e002049081e01c001c006000c59a100d224024401c0307040e61440000032107500c030003402140a4401d0600030340b003d0351118981401c12000b03040303000406032003201500c202180c0c841b01c034174000b001c0c43c040c610030b80e1941d83d668030050b0902d101d03142032800f400d082460242407000b42c8070f00010800143d079055030003500340000000c2954040c3d41d80d286600e00581020300c840120709041d44030b0f00307010001d101403c8011852095040d903038061f00c280c16001d03901011051404090604110406030446421540c0740c9071102c46628042d0801ea200b11003ca02311241441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 983078669 1250 983077419 983077441
    0x21030c080901020708031b040317031906030b06060906040801110a112a030f01090303050a0609110a03090c031208102909042d05010602030a0c11060c06090105 70
    0x1801001c100002e6042c0b009540b984a2944009001318840c0c0803c002d1002007204080151001542c00102c0c801030080075805d030b10000d502c101c50000c508000600300c140340700c00611900042e80d400141c552059540e502c140a0140e1011070a40c1c0d001200340b000140012007400360f0b64425140081440c1c9526001c1009021103000c841e030342100b42c12010041e40d04445ca04903840c034103206d008900d504203c01102203420a04c0b4101200800e508264081d0b05150301608414001d401090301003026550b10403880080f200c0300ca2001c0e140b6442007014150480c440c0d0080c1101502030441c00d10640d50f240e40d041024014070050501003565641000150880d00415400034032140d441c00b1254102906103a400810f4810041501000411180c0d03154440758400c1d1440d49402c0c0c48980081e204412001c5a406411051204542000004035900d80301000b0385450100d103840e901d040100e2076545001051014070415008001849401d194480c02c0040703e000d0041c070b000001d003e091860240c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 983079919 1250 983078669 983078671
    0x3040f120503090d050a030e10090201020d05090a14181602060a18060c02210d0509151501021f02090a050307120b0c070602121009090f0f21030c08 65
    0x4401d109051041101e41400822090302c8001c4130310b040c80d512410240f081c0c00230f000c42801c0c0c044503c901c0041002c0d055066000d404010300076001c0751103489902008699078880c0c05003c903000402c0c0f95003081502e250358000c0c02c05c4030f0000d08840f060040300d44407904c1a0300880d2010441e51030002c01612583e0107000240e04041d1004062000c050300d83d180958001014400a01c0f481e07807941000c040034820310028036110680320040300b00c506a001080a650880601c96409501d4840170807042040010845c00014084900405c4c41d40c072016440000c1240d80030080c150b024a1030302c411074407181000311a107205900401a200ca4080050040000031908003602030b80c4102d07424849403120861214a10b648170000408030342c1d90141101450003103060080802c3d0000c12264140c00b00e80324000e104403908034003a01295911860350040e85c01681c0081e04003201c1445040100d09203458410405000c0e51000480c02d0101145440411f403206607400001d581e8201821410343c0503d142e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 983081169 1250 983079919 983079953
    0xc0e19050a021e03190513150b010e10030204090c0507060b0102010911062505061e060618060912010e0d0203180d020d0b0a020a09060512040b07030902030303040f 72
    0x210f0400507591560403022816214218144001000180c1d405004083e103482c1d0707031560700090015050848600901c0c015014048a60100e0380c0d8480241100a01c103950701c0035416541c0e8158014180144a48114042030040803d502004040f6aa402501441d0348803003040e9140b55650500e410040c0c11110250aa24116418061148040b40c00c42150441141081701c0b0342d80d4a15000070741c0c80b01070100004280c50080101120f07001d01401180f030781d1143c500c0010960b00040100d82074100704801720fa50701d0340a002031183c092032200e41510703070314858000b52880f40391001c840001080510740346403040440e9107030900a8400701c01030107400030085d443c0c001141086c0a42e04000e12030781c40e00025a01452001c030702c1100b555640c694400051f50840840000d604011204401950100b009030001c41e941d0580098028408d0b8101c038420701401806007001c3d16580d840d19450903019100d20308141e115552000907940620055010b40e12680c1c1d0140c410801d0314001024610803042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 983082419 1250 983081169 983081171
    0xa0207030c06020105093f07030201180b132d03030b01030207020f060306010309140109230d0311091c060506150a0807020109080c06100803030709060c0c0e19050a 72
    0x512005040020740207121887c004041c02055000050000c41908040c2c6044a41c00c40700c0202003000024000810005009900902c05c80383c1c1b440da0100228039a02c0002c000c01d030f460000070692095005101c030314a01c40e010b2941000135030301094aa114454030116101800440309100301901489001589c0c0300c2804c0035401c1100700c3c1c0004125010b90403403903001d94800400118135a100b540701121065000c842c5444020303104490a0090604000440d10751510b035000b40c180001c0c81500d00f00d05081c4000800c40a5240b01003100500000c09400a46850070700a91445603116410600e403144031541e8442d0340041801d0410a030341026020754060840c1c1c40d0342c103040311650411a91001051b0030081415101c6d020100d004201409002c0c000c10004913a0011404000c52241e006001e156090a80c154645100c50b803640300985a100105551440c1004001d0080c1c990481250280504980207680c460304141d014204503056411b00c3d0b108808020307180d17454411980c0000f42a04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 983083669 1250 983082419 983082421
    0x1020106140f0d0f080301030c1e050d0618021002100b092a09060415030e060603100b0609040501030602090114070b150f030a050f01230402010e060c030a0207030c06020105 76
    0x4690300007a4103403854040e8145a4043c000e1002da0b5031030411581d4040c0036140c0d01c0da9a030405464406440c0609044280700c000b1801112489214010690700c0052410718001004d80c2d0b03000060488540b08048807040004000242e52800b24040b2070200c10b03000ba100600f20800c1c40012140300c1032000c1c1c425020700f0309010089132000c01e1580000c1150351402c1107034a02c155030007500e0107080d282c294001c0000902090380041c10303221006154135502c05110821450654540301c901c211a45a0140e2040c3e105002d0301119070000d001301d006c042c01c880e06e001c0402003c9801e0b208260401c1c2c070556000540c088041d6401803a02c0c030490020350742c46050040683d14000301e203002600c104607490880240c40c0c0d03540d55200b050040601d0040c00c4a86010f03080c9001c50301c5050050800100d9440d1a002c0c141038081c03580c040140d226000501c0140d5a07441c1c0c010f482c0d807140d40e030806130400070038040240400d90030401008100d000340c009008a0745107141103156980f80303030004001c59040c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 983084919 1250 983083669 983083709
    0x607110703110d0c0b0301060f03140f04080a11100515010c3f08040516120b13051005010e060607030807030c020c100305011a03013f1101020106 64
    0x220450408034040741e03203c40c0c01c030050511840c0ca00d0690000110110000f0000589503004501b401466100e510188006d4028a41048a5003070440e91000c2403003a800014001400c00701c0107065244047c244206e1aa0320100b01900c0c02014100001c0d180796640c05100344007000a07401c0541100c24a0628100c80141d9540081d051745061a490b00c6450160b0503c1c48030103003800e6209003401811000000c0b0026070005040d14000c1c1c1d002e5a044c000c10b01c480b06c400072050544010790303130500301d14004003a05681d4142c0d04400241448200742c4d0f48121200010804d000c40c0030714007035103900400d065040c980b03031103080440034100703034800c60040129000198100d06555440f50f080d007000201c00ca0385e110168200102441401c1d80262502c00040c103080d0546d106c107060b22014000122454804401d4120030b12082c081e00c0d0303c15041424120f0700d650101016240003e001c09a020038030080421860030020780041180c03188090000c6680030750382485003e0040c0710b41d00380400101c0740c0d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 983086169 1250 983084919 983084933
    0xd02041a070818010219150b0102071d1e041a060105090a1e050907020102040f0f032d050a080306010f0315050d0c03140f070905060a06030504230607110703 69
    0x141c40d10886008070003c01d002d913802804590180010b00203100b500d1205450083c0d01c031180b07030808071461840c0c40b8030008035520000303c1e20141c030a40700d41c41c1c1d590808181c1d08803e5250040003000800340160566030000c404000990140d071140500303900340303036910000c0f52050000a16150403c1001d00400116685d0780882030112203000c150000059a00100074040440c1500103d411080d10070502007502c1d81540103008031442c0d040144007040d1540b1119482c40024440a0521594480300c601024040c00405502c09410034200c900381c80107907946400c06141900a0340c0c2510040100450340d60443c1070f182422a13286400c2007140c8541d28910007600041c0661801a41c07041c2801d0204404130380785502450300500b001d814522110855980d603201e419010b40c260240b00390004070340d200740c00740501a5000500702004a800c10f0070490003050010f005940e0030031402800c200000c40d1440e410286403040c03020b00031918001401824204d2400c0c1c8840181d0300000e030410201b0a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 983087419 1250 983086169 983086177
    0x111306090801150e0c07020301091b060e0d080903100c181e0902181206090f060f0115090504020d05010321090504020d02040f0807030b01060504081f0e030d02041a0708 74
    0x7010041044640318541d0b0720f081d40c01340b946d009401d5860b104003a410710100d0f04044c12000f21010945015503103a10303003152040303c09400329400141c1a003001c000604400064a9001c802600b12040503660003203075019220040100001f203884204a202c40443c0c000e190405891054155488503038007041182d55503229109400723510342d0102d580c0d0a102c000c107440e4010080000e2850800e104490340e000d03190442502c03c02458441c180c0ca0b803040c0e81021400a1003410080402903140c3c0c42c0042c41450740d00c0100e405400c000302090041443ea9a03480500316416030940001002c0d0706514100c150190300100d80000c000129582d13803469130b4442c5064060310320a85025840d440f50500010203405140c00014051b41003000104503e20f000900204480c01121400c4561b44e03074a4094401d845240070303800b680e42100c00008100083c1e0030103686160b200b10b00004a614030800301d6400c680000c10005c2280350006810002c410064a46d6030180c400400700320b24100700d070b40d641c90107445 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 983088669 1250 983087419 983087429
    0x501050f040519060204050a0f05090f070c0b06030a060501080d0e15070f060612030f030b0607020907110f1c1701060215090a0b19051303020709090611130609080115 73
    0x4240002c0034100990b68050b40c00500008d03010f0a00c141c0c0301e580901c020740ca540a15402031004100181441e0002e0014a001e48400d0b02c1e040c841c144107480c0c0848216001b4000703605441042540000200641303d030b41e0081010b0b8024144014940d44024000f400c05102c541c4144070008880000307c008008440144d0b9018201c1b0060380e031203240050280c0141e0303010907264503001b404101410381058011a102d0344943c0c0400061040004110080c01140f202940004051001521503801540b1001c1e2900321803003100d801007004101a440d2007115940340e004040c2201c0c41e401c00540080442c442031003001c3c213001c0300d98100140295200c4200c10080710031003818000c244007207800d1219070901e0350130a618203020320780110011180c800d19008056640e00d48070000383e03203445800c0c0031043e03e94568040c0582910b0400c125010309090102038440f0f070341c0d45d01c0000d000500640109003030300d204620403035983d01d00680035000e4041617202481a0b41051288002c07003120840300c1c0e042d50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 983089919 1250 983088669 983088703
    0x1106071e02190503070c0b0315040902060c07060e120304081b010513060203030106110c01020d0809070e010f05010807050c030421063b1f110301120501050f0405 71
    0x80c222580480c0341c40301c2c02c5160511002d40c541d8038001d0103008001040301c28021507101e59010f5944514400c1c51104980d55034003502e02d03e550182c14135098104140c2c132030000304143e0030080900f00150038900031f03600000c0841c250b959401001d040161902103503034400030141d401e0a03e0040300e6030301e42603002c0460360054995409210541e00810603181d00d040481d201d050301984444001e03603651710170300940c40415044284420340c04400151403804403010b030301810042c01c1036841a2460a400703442e0148500501401103030040010640354001c4c06c1480750520020f180000240490340041d004a040102c1040b816100b0f8400004070380849080808180a0400f07043c0d80b031148400b444c00040c41d085c00c01107202c400e0401800484034104114118092803c045005030280f8100031803200c0182c0c00c0b80213483d07011180034a0166618040d114042508854110a581f186c0e000b60040307501050b405807030350b0911400340324403613119150103403c00650900b0b44409542d121005a140c00b22 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 983091169 1250 983089919 983089967
    0x1d161701140a03050616140a1d010e0607063315051902030702120c1804020d050f0a140c0612091006090902030609070b0417280201110607 61
    0x1902d4801200c0c00858000c2e00703139070441c1082c0900440e07aa06e04c3c2d04540c00a03040051b042d14101d0301c070782210129012074444030400c0d464044c110811818010186060004d403c20703031615a00d03030130f008010181c42000c0020302c2124a020b85c505410240e0b200111800c402c6802d541203615400105042c0d44440300c0310602440034480854440c031580231603004109800c091400401e4000002d820303654401c03100c1d600701e04250b001150b900c1c00e03043c8081c1d03400905842801c84001c0b540045540190000e000500c6809031500c400d45005c04001c0380c4042c03644200d10781c0c1c0038020302d92007440412038020054024141c1d1000000d070345007d54442c0a080d0300090703011514050341003160032440f4103040300c103110490365610280c000709a0701c11300b43c0c00303070160400160078200046180740a4420000e4418181800c10300740c50501e00c03050062006a11400d10940094540042c0190600005600035200010b05100040001a90720800000790b03110300c0038807840381c0c0c100c0e1800703800c0c480916480b409 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 983092419 1250 983091169 983091209
    0xe010b0a050c0a1b030210230c150106050a080c04260a0c06050a02010f0e06270a0609060b060c10020d1107231f05101d161701 56
    0x18400e00c02da00a0144180c55a14036240c012440c00c03004903402182d5882e0942d280c6c0c0000e54201076040e084552100d504240040c1e41c12070323907000c1d01c40c80003500c1c100c660f10002c10003100b51440003a0081400305401003018030046500454440d40081c2030104103003011b141c080ba11903090142c01000d99051113002001060f54410840b49150a40000920700c6680e590100a007813035008000c0d802c01035003440110b20040d0f0080c06800b151034106001002d03d42d07150b040c141d0343c110403401d10310481c4440f80c0411804500c10400480c0c200e01070840002d480d1103528109007103410400f10716000ba4018400814070b104081102c440c407441481c009650799080c180b002000303110f26401440c90701c030b01080740014004030b00840c81814a1700350f00c2d6005003404400b00f5580703d2041041d40010b82800617a098494615005141c220140442d244004e0ba260b000c139400c000291003540d42188000010483c4e40c00e0103414202003501241080d881246400c074005039030407030500550842131110303045154 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 983093525 1106 983092419 983092423
    0x506060f010e120a050312011e06080f041e1a060d0f0f11130b13051902130b0c06160219110a0f08010b0a0e010b0a050c 53
    0x2090940c60b00400100c41a401c0d40348410f0b0241000003000620100003a02140c0c1e600000900550305114400030350411320340e04c445c0610500303641000000d800604c40d58101c107404501090550316420030001c443c0d10707881c4002e11010460320203020700c5000d109074103c0c0c0011240b00e81c15501c0c3c407030402c00180c4145001420900751101c2c240700182045985a074010300c50007240f0711041e0ba040001e80070184400f81c40d0042501c406510109140001c01440d0f60000d8030703003c100a08119080c0c1c1c00707110039440d0b8015013aa000901400d03411300041e135580108100490143d66544c0d1032003660725180240d803440c0501003107a51410b0300b80d001281860305009988150310b920b096903111103d4440b0002000d039040300e07408502003034140003240c5103805400907070000301c1c06000e440140110190707143c0c03004805110800047c840705100c101211102c00c080d28109032101c100104442c = true := by decide +kernel

theorem cover : BRFrame.Cov 982913669 983093525 := by
  have h0 := BRFrame.cov_init 982913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 982913669 ≤ n) (h2 : n < 983093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
