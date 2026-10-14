-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3582
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:04:43.671255+00:00
-- url     : https://prove2.me/submissions/86af1fa1-bfe6-4372-99e0-2416c93bb7bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 644064748 ≤ n < 644244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 644065998 1250 644064748 644064761
    0x10c300824030712020d0602120a05090309030a02060d020d1d0706090b03010b07170c0a060f2a020f03130512060709051e030d02070e0903090102120f160b0901 70
    0x44260408600486882d140821442c0548600407504d0300703285110700209007180c0412100500310b910000302d50a0900f17400c04020b0144410b00301c1480980ca0300b60400d5904d0041119087e490b400041c002c50045ca0580300501c9410f03107a04015045c20740889480d0304944c2c201402c1000d0801180b9003c005100030b00001002d0301c0c0c4d03420b060701e0160a2114040030350105000c2d011144030005410b00c01c3c000120001c80e50501c451420076511400c0c00143c50321000b81f41c03421a070203420802600d407c541079000e91185118106a01480040340000c07201d0340c010641a10019809114440c2d000014240000e0094a0417411050801c078178002c1401241915015406203503000403042c8104940d00c00401401c03030341c049031180ca10500c0c0c0c1c1c01c14001c0340c80c0e01844aa2600c01ca01c4002c60301900410b90200f2180c4409003210359070f0701c101c2d989483c2d1048041050050300000368480500c60b806002e4800b034404401118142150480355104958140701c064a5681c288010085190403d01400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 644067248 1250 644065998 644066041
    0x702011b080f070e010e1e15090d030536010921080a03140a050a06050306150409061107030c15020a0e1309081c0c0509010c3008 57
    0x240151900c24002002c6102c050014004c00c1034141824030141e00c2080e00d00d0400900030815142d120f85100f201144440ca9144180120340c12901d00a41010b5030080d100c0c01c05001d00800a00d0101e942c0856440c2d116280006d42d6194031000966952900d001048001661311010412084100005009180203500c402e8051900c4111100100d070b43c0a091489150700c014031940b10039a402d0113501818102841c2c00030f10807007500300b28030728000d41c00540c0942240401000450340320b0080c0b41d2501c104481035515811420140c10003418554012946280502c00001d40c4101550415103240c1c810a4180c0024a84003420300a004104516492030301c40040e0840c90326a117848098903000340f83c46014480e1741982c181e07a61010b101d0300712129095001d0101c907519801c60322544a49154549464505442c291100e98910300800484001d0340c0141c40c0d00d95039145a540b104c28403100005d40d00103440000041000724080034420000d0741016454607404d501c0c003034021520a681c0306100c3d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 644068498 1250 644067248 644067257
    0x10506060a0e121e062a16082104020a090e070302060c0c03070305030d050901020403030801170106090e0c03060c1303030f2109030e1f0c0611030702011b 68
    0x1d80405500290380b244050340c1615202e0f02c551200302d0342810441400204c624612120702504d1842d0f40c0422010b1084440c9040d070b07080380d5aa681c2c3e507010683c52025912500c08108600741000762081d42c500012481174800c145054544108207144244410b542c41c841e11800c0140021403406042c0c0402822081400304444114000601d9498205100c003034010500050b1032511902e0600c003180610801800300e85103160340e8545150b0365480b001180c0c0b01135180102145d200401802190200ca800d076680d11116403c0801078034803c0c841603203002c000e41d640c4100040050203070080d0307181009200c0240c0660703424041458100000200324041c0303040e04000341c0110320031022012082c1c03601451b003049030150040301a00e40c191600342000d66540003003c03030005100160170015000c3c0c40b966a07141c0d05000e10703040c861034440156200710400c00c4400b240007017500c50100b010f901c0d03014920105448841e407000010701ea1090781c9030070050b5107540480000c644001c0e000415205203150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 644069748 1250 644068498 644068507
    0x907030f080301320f1201060b1308030405090103020f1201050a200403120f0c080325051309020c12040e090c0117161e20030406020a06090201140309010e01050606 72
    0x1001880c135082e0480d41d511488000440c0f5044d0345800b401c03074409041c0305d40200202512020a444290800c074118001d000c000d14000c03810b1200031080e03038211000a090300d03403176074210350070002d1030f4888a00c0641c025400340f500059141090240d140250000c031800034451500e410f82c920200024028410303200381c201310030000101d90a080d0002102d5910b0305000d114040c040c1212099003255000d803d0b031030040709104c4082a1031140d0300c0307012026070030184103802e8001c06aa0b58000d55841c01040505140c0030003920381550010310b4516205003e40c0c98a003020f401244040c1c001c0c0d00441c080590f003d04002841204000800c0203800c00d00305607a41800b034131011444120700070008030380302d03142d08456181140035595400c1d03585a8011a1491404145001800500c0d09070300038103100c1801e6130641600e200441220240e85003503000c1d0000408540314440504103000c001c03030402c65560741395407000102401071401b42442000119082101010710740c29100c002d08524484d450401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 644070998 1250 644069748 644069819
    0x1090303021002030a0b060309010506040b090108101d010609140a11030c07060b0603040506060a151409061e04080c040618050a0b040c17100e0f0907030f080301 71
    0xd20360304038904022003d603480d40c1d5a66110083c024030b00240b03800c100f02100780702c1e02d044190410b6204001c00e803810030848a0380b004018400100b0705c03036100c20703400c80300461502c00c21642000400810008144e9602c44540124500b180c241d5440038614941c2e44900880c0703580075003d01904100210028401200008030340e20709840043c10722000200d0000d287c004100381c42e0001d1003250300050a854803840c283c10820340301c10b01200c180b0f10807103680380c1c04900e0004440e001100d10920756203c0e00c0e0045407080c11032032a4001c0d24826030000c028091140d120850943c02ca4065004409403500d580c80c10601500e054104400c4070b1040381443e105015000819240c460028503107040841d1070348a00c0084001803121711200ca40160504510010094018080c19030901000800040c1590b031035001d218580c13202e02901804940c7e002c0494503402118100b59004901242581c511076920703940d00c90100d41c900700480d55400048010800c410704260040980c460003840090070400c0311 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 644072248 1250 644070998 644071003
    0xe1b0a150f1d030d11060f041509144e0a0309061a12150402010f02100e011d03070f02040f09020607051b0d030f1b0803150f0109030302 60
    0x5940030700401c861620458652801182c1103050380300040d05941e20303071440c0c080c005c181da110000704c999248140408136409401d03640e0201d101715040010800c00003588143c54000d0000381e2015103000300d0300c002c00007030107100744064603141c2d038800ca082404043c00108510900502c5464511418110794400784200e13054000c50301e05034104010301e544150801042c0c00900030414060b0050f407a1800301c4548645580c980c0928013011980c00340142d1007a010669949006140c1071030450705080481c0040d4040c0c954042d5149280c01500c44101c12501585c0485007480c10542050303440d40c00b40380c2c450140c0700c0e5410b009040c00c0081c40ca040019210320700c4035210751038001d0049613034561031540c1d14042d50103031540070713401000d41c0c1da2070700319040c5290f0368101e07034800030031465030080812880e103003419103002c0300b07549501c441c0380c00300144005580210301a108440c000b9440b03080751000403d1000250701c60f200c2c941c240031802c43d101c070a02c0742c0030352103c44960510070107900078000300303800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 644073498 1250 644072248 644072267
    0xb03041b0605031f090e010c08010506131403031b03030a0606170417041512150302100c021c12020706181a0c0604200f0105090f01030e1b0a15 63
    0x3043e0302004004240d80e800b02d130a2409030302160701c1c1071500440003040d4006422180b40031480d43d8490026980707807000c00c1003a1140e08011031099814201c01c004031020840840e40040004003920b04003034601050740d0038030f0061000e03540503400000c1002030200880c0300d181d01400e15031610210b400c0c800044400d1400300500041c0110840d416101c607085428000c1300c02406041c130700c9001150410001608040d01c0d890890305240c01d000000240c440c0c18074081046039001807404000d07052510741594045003120090741c001c03076403072451801155004100030402d403080540c0702e9400031045000b402d040e5a0740040042020f80350f0060301d4440a9a00c180640d81c11102e003035020b4403c0d040f164858070440c1c09d0746816000301d00412003881901080500c41e0b8040300102d04081c01230800b004021301004603d40d020078002d000c050000e0401c03414030403007154181000101c00d8803090b00c0510708904000d282450614803800c0c400719041810f44540141900c000c45030002441040c090003a814 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 644074748 1250 644073498 644073511
    0xb040b010803210912040b070c051212070f0816120c120f2105180a020618010e0406140f0301061202060f12070315242105010b03041b060503 62
    0x43d0800440c41044050041c0306454070381c2d0701007558540d03582c1100c81c4c0d5500400790695459030000c80020f10390806010074503098080101030071000c1030310b508844281d0400f100964502032507004110008031124010817115480914034460b2803018a0b0054070707031910004d0007080200c080007600000d01c5492039062034410782c5c10711000c1c10013240011a402d04d60200620204207580418030f2800300107501c918080c1943d060f00505003804860b050b9640c0ac41564007e4225a04220f0302c060b403911580c42c10042c000c1454200f0507201003000040542d1000d401c80c0c410001c00e14241e40407442d00c491b003450b0015058001340030845c0340c035840c02c01811500d04040d020300000241900700c505a14200c40c80c0c00d00a81199009090011005000700980400c2040040362240c010814200ea402d070308070348005441d4401003e807200d40013140d16050040b5880c1312190005c1e0280285000b82c0a100e002c0c044454566840b4505030821030041d1070714540aa1201c2c204031802e0090603448000c072980540c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 644075998 1250 644074748 644074807
    0x90a061a010914010c170304030f0906390303141e0a051806070201050403081e0a090203030427110f270a08030a080c0a0c020112020f070b040b010803 66
    0x54224006845c0d03403030200c0c40100b0451b40c094200d1007007001031020714001c0d03009990f070840030060990140d0f4905924029007001c502c207071820b44640000340c00c0b8010081030718103501c1c0300900d0ba101d5010448031554800c40110340c03502800c20004000c0000a50700450b60040c526a4881d200130488034401e000e001100c115407034000055800000000880042c0040320403101031f4645010000d00a04041e28120001078210011070030100070380548035941c01d8110403950b404d80340c6015060040c04120412a0140014480058629080101c407007c60360100c0001c0031103414021070100701c50144140c14098442440a10104404101601c01c1d8078545c0403070800207006154100b6600391030044455200d0851a03010410b040e000c00640245141901c1f030100d15110301e01403007024056040d000d00014201184080558824000e07040211510700006107024000d24a46165600c650381c01d03691181e00d003048c80100080f50541900420b204d102030b5040030000c2000540d1182c8501c6216082d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 644077248 1250 644075998 644076029
    0xe0f010e01051e03040b01061b0b1503101a04050a020a0e0616060501091a0906101808030a03060501270302010c0819021b0f090109051e090a061a0109 66
    0x3100f0000c00814200400b01c0c41902c81c50305141103600c0d01000d004150002c0c40003d84e0b03c2403085151803c20700540d100500803115600c141d01c1c1c88000180300030b0316a0610400c5103600d0b10301d000e8410501e07600352482801d02c821100c0014042503450180803540070318030400c0703103000301507000c01c0d01c3e038543c02d08548281c1e6402e55108403d10b50714250402801803490280001035030850b5911803080b034851202c1c240c44500000d02089030103c0116803268014031030104140030244070b2440880c0d0842088040e20506440d0b01100b465a0401c1038000c01103669075006004d10340e008100e0211845100320000882c80030190b034132f00060414030009040c810511454020441c0c240196404c0000070a41c071341d0b0501c1810301c002e650b132190f8022100c1d003415072006121141403d10805000f114007070a03004050f442c0c1829200104030041540641002d5a1910214206c8aa0301607018212100003802d01d011581041e070203c4031103521010745042101c0500c44166004044201228102d42c982b8188 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 644078498 1250 644077248 644077267
    0x3030406050603331f030201050d090b040b01240f0e0d021306140604030305070f0812040302152214011e0504050f06011d1510050a0e0f010e0105 64
    0x106401e0380090310304482da1100c4c1c03d282c403032004e485050401e900c08540e0351580b100d460b464525484800e0341c0c3c03a03003040c0000500155000b43e004004411000c880002c0300152500c0c2c140401c17400391012555198210010400c0580311200a078502d10b1a8816501c0c0a0802d9070150080a00080d0b100c07c1c0048100405242e60701c0348860b154168000e04204582d03803000a000f0014944e0303000ea8101601411034119060405a090300c0550740d06444507403410495854490b4610001481110100e03000c104c624007806000d1540ea00517403290300200224150317207202208c621300041012525003079880145d441c8002100d522032034250841100040c107070303501f8145401f401075030130100c600d0403680004098080d1141c0c8400e203c0d5000d14143c50a80380f59a01d004e448040c01e20407480701020318441d69170140034540c0c42c640c0020851482000141985000c900c10303030b086071a03100118802185400311250040c281902c1d031030b42114070520401309040060b029084d0174010030304029011a0030fa40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 644079748 1250 644078498 644078503
    0x209060d051e01060e1315030f02040e0a140609010b1008061305090c0418030807110a02040903030c030b0306040c06050f09060f0c070803040b09120a061406101103030406050603 78
    0x1c0728410312031946981c40e000081c0c286a408403ca0740506940788400781b814005200d180c180d4a219119065034920310b0711900c0c44104281c00590740203070303241c0240c10712a904100a2240508c1284086400400c81d841d15040200007800385120764107002c00b100c9569140907950907001000d043c045040e40318000403481e245800c00d003080c03001d403030201400456500080c80006041c0105d07410b0150036141000e41c0c4402c004c001000780402d03000f0020803840d40c00340c07804222030740e00c100440d042c1e0790468000a05640342e9503004c2d40420380d24100a807981d81d040c05984114081600103148030b080039991050303c0750b520702c2070f03008014011524500b4101d0010844402c80c038000c010b00c1c2c0b1340ca1210040001c81d48074200c401c002c1c0c40f1f40800041c8200c8040161000c603400419040d00341800d000501203c81440f05440801c1d000e0540b551000030300d64810300c40246800022040c1600d025824807040e0f41c0b81c13555502c240403182ca0005409040041101e51003903100304003080c10784078000404d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 644080998 1250 644079748 644079781
    0x402031501080a06050403030b0406230103060f0b0a1106040b06010801170607030c0905150417060f0a0213051011010b0616020f04090203030f0d0f0504080a032c0a020f0102010209060d05 82
    0x641c002e08003000001c1ea80c1c0c1894cc0c403002d815030450680c0c0c00c10a1040150100c80c072610a46181001c5c0c2ea1041091100c59406084401c03601d081901003225000000e034103100e402c40d000c4038089581418070100f03581c048030f11800f4200314590b41b55a206101099941c68200030180820181c551240604803071099006600030300c4090000c0c5804103540c40484041d0708075004400007106d05404d204004040050054003442a0769100c044685030460820080d40c0250030400f900f00d42d0361000665074582096125840030250f440e02d81c04a8491442429204089201031262030203010000c1080940309142030165811039038001e42c084450013140160001010103581400080b403000108220030300180080040382d8000c00021b00d482c8405070441d6410b5601a10303080381072050307a030814060792012180d08804168002038030103a00c0203441090f0301000180c4603801010030141141082c2c007070790448203000d0009500b070160380030200d02c1900031003501c17502a548400c0494003424450b04e03400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 644082248 1250 644080998 644081021
    0x50703020421081b01240303090b130f0602010b0f01020106180203062e1701140d030905100903020f15030f070e060f04061b05370b0402031501080a0605040303 70
    0x109000c0410440718024440d12000c1a0800000c0540c91b40030103010b03070350740c040e280c3c1611a07458442c102a8014080d4110081c00c0392001c2020070003141d0b040315512140000d01d2554004101401000248040054a12042415a030501c91700f81715405603802c000280b0360003c400140c9a41c1c0e0400004c2540f80321200c0400708891580340401c44a005143e00c1c0d20030241ca46821011030751b00841d202008800b4441c440801c002d42821140b0351410f5040400100d019203414403882d5102d00009500e0107502036170b0700c00308603034190810031030610745041c1c82c0d100d00c1112904070801404680c1d4806100051080709910480b07000266598000c440c0300b0820030004e006030742c55805001c00081c1551142c040c074070111b10841d0000c808403030b260941c941c00e1a0700c540604440a40307000e115441c10300e45010008200d540364810765104400941c2c1a02d40742c011780c4100d445083ca0700505081c5440029050001071a080c018000f0290000356040a03a501c26400a265692814110300400c400c0c01107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 644083498 1250 644082248 644082277
    0x30b03030d050901090c0f0e0c03090f0f0d030f2c100507030f05090a050d030507210203070305010b03240409081207020f0a1e0c031407080105070302042108 69
    0x1400343d6810154442c2c100188100c0302c524044c0d440f0500e240401501d031103003c1c810b607041c40004d000c460300d02010b11341040e49002102c0c5011980304c1d0540c01d017a03841e806603079039502c00096a141c07290705005110800300207041c1000600341c8100c2160610194180040c030030b00c814800280c8214040001049031040301c58100141c2c00d0116004000e00a80f60b6480000c1e8242004900c034000080790300c403c1c080d8010010302d4000f055840c1039028010003400340741400103105640054081c038020121020010410060b40c1c0d02d41410302170115281038101941c40c11050040221408104440240744404070507004203407004000010301030105600d00500002e008540004880b11084205000b070245409450401c01200e0140303070b561000000280c50b20000260419280b0300000d40c000c151801462203110f501d849840310301d00700c0d0f009408100d241d881288100903034442031041a800c16150f240551030702c1d107001d042d00750286012070009a5104400e03140b00400c08400215070718103047c541c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 644084748 1250 644083498 644083501
    0x209090a0b01140f1219080d0c030209190305070902130b0f0d0b010302030c220902030f0f011e15200f01050105060405100807050706050a091401110a030b03030d05 72
    0xc4040b40504050f802c0b03002e08402d00c40c84041c0c1c40d288540e2418800008000d000c6001c3c0c20000d140c203456800015200e981040001c003496441600882c41704440c0c0f42c80c00340e80e42c05105c4c00d0000e280d40300a240341d11000d00c20310500000d05d02260300802ca9200310005a01c81c41401c0000c825100c290340045200c490008112040560318000740032807500c031000030041c904040c40150f09912086403a480240030404c038500c000c00f00c0307060703440c03205081c4035070b40d0745450311540054101d91060701e0580101c03194500b002400c0c400e081c460303409071803e9114522040500301d101035011485000c0c43d01d84100c3e00390840161403003031038507a02d14038002035060034203642c41c44800d8a038402aa02c000300e550a082c0041a18181070003120201c030b00c05007822001c900c3d0054111010704002c0d00c04003c0040c01c0103040003143c40350080c14050013108100142e4900540751004030014401e8480180380d041500050280f805034041d110100180d08012908500190000c0c1c1144190713006603824914000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 644085998 1250 644084748 644084759
    0x3090519120b041b14060a05070b10031b051813020904030f200706030221090c10030510170f03130f170c0d02060906070b0703180c030209090a0b01 65
    0x281c1c001d038060308180e419590700740019040c0d0051400741d017880c05c0c96580400d1070790802c4401807080758403614025081070959615100c4460701a11020181ca10003002030040c0007402941c54500002d281191034100d18020100369040c50148044244008100c000b070300304244010f1600c50785500074a100c00318502450041c1c6101c0102d0859030005a00035070b00911014500050780c24030b00500b0040180f2481d00c038045021354002c0d41e94125a07a0360100c0c861280601058185c0940d03401d0b000b0f0408420132001348880c0c040140301183c101070400c400e0081240515440609543ca2902015100c0c0f050352030580c030b00b07205206411140d104c00038403a0101003403460000b09444140c2c0c01018160703a12200191103410b44d2038040820b4203e4514041c4a180c41c0100e20b0640e44080d00c0582081c44901c002001d41d08026002e0302d0070741c5400d0810a0803549817003410311241d0a080a0b1036a140942c1390702d80e2000d220300000b4000c00301940030803000c41c020401c450503e80d014150007078568403003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 644087248 1250 644085998 644086013
    0x60605040c0c110a050a0909110d0501020403021005120414011b020a0c24080601090f0902121b1602040f0510031a2202010c020a120c080601030309051912 68
    0x515090f180c412039051195840d01c2c00080001c110741c1700a024429503820844402e00410b003041003207031946040c40420086807901d00d0031117940740c05640010384551079030042c0816200c1500c200800c0190030010040564070f00d03401c84c2d40058010817218030b4126414400750040078060450b1400c28103400c00e00303c02d5a40010240100c610800031f10914607510b141651281c9140b8a82140b02258048881e20785131141507140d902000514101c09116a01c124068415000b600318540480d00042e688441c5070f18010a035411403490103202001c201c029880395014018030080312182031701c1900d00c01c103564580c0c1058091240c01c0b5001c004a052502c0340102121852100700e070b4001d4041c0c0040c49520b83c524089118404c121480b540701e0f04d0300d480d811009240b02c103040381070241c0140d154000da200e50082d040a4899086c500141c1314290412902c0000c1580c400407460b0b00c004018000245c0c4040c0d1641201e00680307003504a02c1207920390300100c55158000d4896110782c09220f0b028000003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 644088498 1250 644087248 644087267
    0x130b1b030418060e010614131508160804050c2202031003020109080c060901031d0109080309011a0315130b0a0c0f020102070209150109090e0321010f050d060605040c 73
    0x1041040141c26a100702d69059031390701340704500201d19800e002c500300b640a00001c040c06081e82c40030100144d110165151418008541800002d0410301042109810b42d140500200507a017040350191405544060383c403001d02d040700e4020040720320350003000340384800350500301c07030100400390340740c3c035240b01ca5010b601c240b80f0069001400c0c0800c0083c000c0c038040340480051f00c3c0a8040c0303140c51034180054014000d45000c4e10b0154200700b00720a140507003031107061440c1c0e100317002c1e15589050080f4540d0a480000c00c11811380c0c0010901c100c010307900051a4042c07440c5042e4140003a07502c0b00c101d8410448185000782c107100c1e40c00f00b00710726070700303681e000000140c0ca03503c1e10030b0300c0c10120000304d080340140301c00250040322040110703075840508044141500f0701450502241c81e190500e220941d40e0514010f040380d030000c00d464404507410001c00400580703604c01008250314254081c0d580d00f04520449010703035000c502c107805020040e0826405041d0160007800300d0041014010f00b003124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 644089748 1250 644088498 644088539
    0x3020c010e01090308060a0b12100302060d0e160605040320150d0c05090303090f1302041d0601050723030417062520070905010b1905130b1b0304 64
    0x101d1000200c6c945806040c0400b55001002014148a000d201001e410b03040904803414441c0c06100c00001070307030350038000c144401c01903c0200700441c4000c0003510b004547c880c1c0080e0b24410110a00c14154003005580c1100e40254060101c140154005800003001c0490a03420001d0090851020340d15a401011402a140c03400c1203001d4540d1030444060248134070300da0b4143c10130064500589040e0010064080e130007006a046050000b03600e100b264426800241d03c40c280552441400080035035060b4052401c1c289a40350080541d244400b0401c02c6040d000c00311241c03182210416000c2054130301414443d007088040c400d01002d1560b48400846810b01d030240ca01000458800040300390300914807803a01c81183c180d03012626140000440300b480e00d0203201c0ca0000182c17445880c05004d000342115240075a80d51121140c540c07c01c0c1034091018203100b0f0401c000c00c1d0480150b9406400c950700b244a00c1e40340c40c003c80a6410080701300207120010300c0003085c04601400d820b11120491340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 644090998 1250 644089748 644089757
    0xa1e1202031b030708070b04111905010201050f090604020d050a02030304140906030706051e0708030103060c0f0c0b0106050304050307050706031b030b030c0909070e0906180f07090c03020c010e010903 88
    0x2c521081180e40c034454450300506641c404e02c1481c001484800030b46801c544a58081c03000d003003901c40815142144c1c0a407841d008103100200704910358080c460140c00002c82c20031382a0301d24100b10400d60303c1c0d8003d04020b0040c00c20b1040b410134013200b8090034490756401416a6034035075440401c03c1c0c0c85000145000d02c00d07415000032900b42d00c1c0000700101169016240c07035003401001d414207a1102c80e04a02ca0b50701113400c000b05800201ca842c020f502951040f5400284000019002400c1200700d00000d0140000e1481801c0854510325000d411143c507842c221303640e9503503460079031304501a640c0d0060052049000104400b0303010703000002008443e03201821241ca07154030071070030303114142030841c0c150300558100e400b541011002154403228880031108100d640c1d00b5102d01c4c00904459004183d0814001e20010032080c08036285d0448800000b0f1412030f99013420140c40f0740007071003041c80283e91091581c030003601a8060f1805e54440030020810344402c603410a0207071003022401c90008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 644092248 1250 644090998 644091037
    0x130e0c04060b0a120c0c0218010e0709030c2105012309070e150f0915040f02090913060f0c0206161704030c050102090a0909020a05030f0a1e120203 65
    0x106810b402d680d0740e44141c1e503510ba1451360b4112003c0c02014182c1c0780104003c1000e038803002680320007050011038070030741d42c1c01c000f15807400d008800700a00290050b404c01003410401c0002c00d03000344c14242520f060103c03400c0f00d9003580e1131002040c000300500820a500345150300000506090300e689155158100b40003042c1da8102c9515102c0e0640d001d010304031501600803c0e4164403961080304401c0000e0851101a1140e60016081700b00450320318418164a8440300c40c141418014500040407600301076086c01600000520b0140b80204485880c2e0920500c000c240030b0203400030404165100003c02111001d402c00a4440c80d00700d8100207070b401d003401484425449101000b07908091800c040c55951210f55003241d92142c242010f030759941d003c0c051182140d0310040110020090a1030014114202d132061000c84c800503440319201b900280070985200801007408a040c0e54081d4000d488a40c07100707010882c926124034094100c0480d806902000c640020040111111000f9150300a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 644093498 1250 644092248 644092259
    0x112101050603071e170c150309011a0603010308030703111902061806010e10030c26060402150f071a100f030f03050c030c01240e0c0414130e0c0406 65
    0x21451409aa4596106410010000171680c14200c440c50310102042d40d84c0d09030301e440010341c500a08180142140c0000050001c0c1000c00d03c21000c80c80a149090f075501e81500000501d03e010501c406040b002000000650192290f031002813900300b4080d2941d10703400c03485030035510820141c102c1800345c465030022451800481502145141040c801000d0350b0b03007888050500488090540c4440702600400440003440c0314403d00c3c058443c1000303680104030843c80790b20401d00482646130080c1c00001c10b0002684900a000d0700501404a0099503095070360110760052048a002401204680415050480b003003501d141c01644401c550318081c0e0348500d080080165103120080503c114800e5101c0041e000701c01401c4072070007440c103480c1804020780d210750a5071031b060102400c10507440c4402581e01c4604c2824030142030340d075070b51a0092600c80c03901c0b081c6210340c2c0114050b16846220190841d1f403402c1003241c2840c2071860500480e071603c0882d9644550000c1c085220342c0c01c005000c2034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 644094748 1250 644093498 644093519
    0x305061b0301080a06091b06020d0905040e0606010311071a010e18030403031404090c1814030a0809030708030403140105070804021e01030e1510050108011211210105060307 76
    0x183d840710780150140b0905995003000a100c21a012074500c148a4000b01d140355a0b0307800600140381e0358020348a44000850001d15142c0e0581045110358a40f45a090040600140803580440c007801e00045809106c40c50156034001c5000c010130b442003a60780340e614030b408504040d04880f001e95030310b0015242d00180c030030400380c20512441c5a80c000d000c10404288110094080b04000000561030513844601c0b40003a50900c181180104541a2400c1c81000c400000c410042c001c203000d0f4051030a0003800a034680c45550742c0030384034842c003113030260007a601840004000d029100480e40d403565a842d00303956a00d44440300004552804001513202c5000b10201d6200304d13402030a00c0169074103c2d502e400b1258503103001e2030400d951f900c1503d500e280100104804038654059408041c5088440b40b040009650451410070220600400c4080306210749070310a198403040c0750410002c070340041440241e80ca0702c0c041c0f084070b1070402a0b8880c1c9040d40203902403c2c1c01e8050726026038851300c0454 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 644095998 1250 644094748 644094751
    0x7080c071403100506040603141c050c0d2006091c020d0f0809010b0603130b090114010b21150301140c04050411070f110108090f060a020a020109020a0305061b03 71
    0x2c1d0190031034414050340c2d18680d48910f0303004400410001e10142c8940b504400200c40701903182c01944007800c1d0071889003000e1034101d007408107072030018034180b80288c4840d03d640c09803420720140301903a140c0b81c07183c64460002e88003100b0500125003140ca892280141d540c1000d092078402031440110a840042c40810440101d60f146e80340c180401405160440d00d9050041800700eaa559550b417003030b005e03902c900081d806031001c100c00c50320a46182c00c0c541d2061601401031140c980c0343c105244070014000300202c0c11640b26480c0e65403500030389115174868440c0004102c280c586a08104416030b118501c060102000c10f600800515084007180c00000806a9940848181c24441045240b0b0703d90446001210711021301402d0050540d80d00c000640a08000c4402502c0d100e442220380d644694203960120440000380511100010303500d49506c1c1c040c01000e001030700026007640303031b9000b5009000d43c1503000d0801e41826a0700d040880e01e58006a84110000c01000c1c16085413580104c03d4a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 644097248 1250 644095998 644096039
    0x11b1211040e0c120108070603060e0105211903091a16020f19090209040b06040303050706050403090e040b15031f0e070e0c0703020105011205030904050c040b07080c07 74
    0x3203103000e0501c556064070800052044802d05802c1106807291841410f03400e0080c034080c0f00600c1100d0404101a040d94080d4000c0d8440060000042242d503694042800f0b950710700000000c41600c003601002c1c1080000070804802626007501802010360001642c2c01b200c0030840800c030030040b0003803508018400c6004c1c00d41e5038440300240b03c1c090300d8100c2c441014028010440d442c03000e1f503900341e80f600c100e203a800f8130031140e0701080e0100745041500076610b19000407030b41545014155a0b016040d8094008080c1c01c182e0b8450000341014013138100c000190000030400203162030680f034424442501211607143c403281141051ba80e904000544e1010780341d01c0301102c440c00040c0540300005140d0340f000d0803441e216800700014950301c42400c0034000c0752404811076803418642400b0703082d42e00680c020b02040480300301d0b60b401700b2404800c0e40c041240854012071f050b210685200c02501568101c5020358000003a150700300110340c0c000702040c44018080d01c110700d544003415059018280c3c41c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 644098498 1250 644097248 644097281
    0x31b020d02011413091506090305060c0f071a1602010b36041a090604020d0807030905030d021e0f1c020a21120516050a0e03011b12 58
    0x10310010342c0034443d07200034404050015070401c500110282c48035510355200c80401e950301c064240b400e5144521040182c140d50070004522441c580e0b620381d03507840080041d110030705d020580c0d80740481c501048440894101c00034500c40c015480350720200a100f6544010a84d491240d0041164010700400d44485001003e00c031604441f00000c40007140019504100c1da400b0110b020810a88016801c0c000ea0007070540c01d40d0b4071915440004050f102a10b001c00580c048010040140e54014007450352039800300201c3d417038030701c646001e403820309198001c0360781401761104c081505940010a8045c41d110252207003030110750203a0752a02c5441d502202c052a8001d03445804200c450b071580740000074098412a4180c0340b05803203200807003001c00c801c00003889141114080d034644c0030822280382c0d03a02e80020020b0b03080c945442d4582c0415010220180000800e030030503514000d80b816400100080c0081c0a8480f2032002d00030071140c00074545010400720b00300c444d000d00003842484400c0c000d2454 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 644099748 1250 644098498 644098519
    0x409020609120717030912060606030408251b06050309122b1e0219111005010810051305060112080705030c0601090b19050d03090509090a031b02 64
    0x2800100407110b14001524800c1e004000740c1e0102000550385901010f078043c548030760000c2c081100c00030030302c9031341d140e40c0e4484d4050003001d65610045a0b00f2560022002da5a203414445211001c0139545a0aa10041d100c00b00340c18801c2004150400b040790f148442e001d41c0c0c0751901600d603130105036034080c01d5506c640b81105c0006c0c41d9900901e060100d1807484940400d009501701c0541000c44140031780107854008103072051020702050035400c503001c1815414001000d1050481e005039900f10001c00c031010400417044071044c80603e007008034000d4244969a1110140c3d952541442e201d46441880e1a001808504650700140c0041d40c6c42406000317a0392130140804c40140100c102070b0b521540c01c00180c000108108001c000f00381c210340c09800d4641c5001010400c442240c0f0195021340c5054000d9120350300035100c40343c2a02c1f000ca480e480d81c24524101102c000190790011a000361a03030b421301415240000d4419006842641e402c0210758624800c0f1445004d0050000e401c605a8074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 644100998 1250 644099748 644099767
    0x6062111040f0b0a09050406080a120e19030c050f090c0903100c0206041407050d080f1905130902071203050711010f0b2103040611010b270604090206 66
    0x801a0800e101503954036820203440342180d2407041440d0b40003862480c00000c032941101e030800003030b00c0104021036003040102d103000e04954640d00d079491b0017041c10b0030305030503419098090010159030a8002e170501108010142c802c1c3d51561a0b400107541d10888844000780341e29003040e03050b010035005071800d41c454844d4000c0580710303002090324a6041c090703001600040c070f85ca44650494803a980d07000344030b14146030500d000c0c0840300f490070050541100400f806951200d150100f5010760061055941c3c610700703040d130300b40c9004110401501c00707415807185c407501c1d5010f00501011403c401c00203d400e680d408a40049208641e0000c0c1100d80b60780c403800d203460199112992100550a007506210041040c807801c42d0107003091001682d903030300307860b4440e81003841858100070208285182000041c62901e80c0c1ea005034800c1204202800c2554900008290008155944090708081641c40c003020110340c0d040d0f1031080c0704800c042035400075401e40f03440c2c01140c0c09150043c08040c0b8051040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 644102248 1250 644100998 644101001
    0x2030106090b07030512070c110307080c10020a0b13150501262b0215040b151203030f01170118030e0f19033f0903140709060621 57
    0xf0056051200520082c1c08440104490340c0c450400c039591800c0c01d00c010305d030510a44a07003500c250b01a170b0220105104089000034407803e500c008485407c02d800825900300c0c90f103100040c004185100d60400e2080d45035860300300401d41031040310701c0c0d0110034036803111b0805c031402442030440c6545050311174008a0b094000004680d1010001d41d5150101c001e0745039140d01a000300c2c50b812505036040c00080079814840091940e4801a06030043d007401e444842c001741014060358030303c4401c288582c0690780e4030405182205051000e4130388900e0141c0c80c0025401c4244103010944d103c00011024908041c8103000344507044402c2d1284e071110684084034000c1482802a400291b07080103100d45584000399031088042200e5640910360561915004050b10780400420611400a00c0c00d2782080000d421004040484094060300300c01c0c0c0012140300c0c0042e44080d060000b032034200c5864220201d1018107543c0f185609000066841700c0c11514850300340302080041c0d0886102c1824900766 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 644103498 1250 644102248 644102257
    0x50a050f0d18350f0708010204050f060c01060315020a09060c1a070e040608070f0f03021c0314040617071d010507060b10080406050907030308060f13060f05031002030106090b 77
    0x1880200e204140345002d035100706840700c84103d1a43c0d4011034103141130160803c200005880202c00a50800c2d2804020840320104041e001d841041c010602c0640e10700c096010340000d5400010040030550304c02904030080d80034107441800200042c10125040b400380304a00c04c200d40c00540900390084801c02c407259034801500c4c002c20068000107003401c1755036500a05000d03180b80405801540e1170700180c16501d103203070f51140c0e0056407569030400250b910b0000c8007255440d6080d0060840c4841e2404903a500344241407201031070000b14000c6481075006468a240d49481c0e80039041c1c0351250041602c150708143c0020810034102007820901703500c1080035100c42485462301003602c5403558005010074140710b011a000841e44001c0105002c200d024007500000c420740a488400c3c2191001811144010002805080c00182c1c0207569100c64005041103001000300b040038603242c004603203601c601841614443c0c410300d40307400640e12306031080301e0485029481c4d40d1402c51a2185d0498240c12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 644104748 1250 644103498 644103539
    0x1507050120042c0f1b0d06060915020312151f080a051909020303122a1c0504110307030b0106021006120b0601051b0105220c09051003050a050f0d18 65
    0x445030707201ca4a445c14006800014542000814502d06000e001442c0030300701d0b4880f0040e80b100c0458110000e07000b108030f1300e080200c84a1001507580e0080c84224440c0300301c40c15034001e1180302c1d140507002000311100311004000d640e6880b00352580710154068850039140c6010340140c04020100b110f800d603105890091000e0162801d080d0031240d890f000e148112605499402500e89414005040c41c0d55808000500d0195606092000001c0856400342c42c2e520520b143c0c1c1c50000c9024040780200d420051107000741220061601d078940340d2000c1c40c1c00e1103510050301c81e101c62003032072405601418007a6403a8110146c480071588d102c000c090700028102c0e5040c4001000b0f40b00110124440794424046114000700702400c2c000740342d03400c558501c0d003505c07400c480d080e16410004110f0407804080740c910b40004511a1224444851003c80d1b030b0380300415903c24108a2410803001103140c0d1180e2200710300b42ca0783c0310203240d020f50741e00340d03140981072131000950b00034044501d14402c2c2c0316030502c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 644105998 1250 644104748 644104771
    0x309010e10030e1c23030a15050d1b0f030f060506180906250206070309020a050402210a02030408040e0702240906070e1507050120042c0f 61
    0x107001d12005007030044180c91202e00403503903100381c80c00c01e03040803500c0c04042c41950112103492034005810454080034101100423a15601400f00d05c140d28000382c00034000090690600c110149440b208402c11540b40f0460300c0c00095000480e02d800010b280c0440b40c01c02801840d807405941c4e65802400018866580001c05100c42da10403406055207504c140001c100402513800d000c40030006425040340141101480002d00211082d4045040c82d0413070054100843c001c212031001805002403508001d400c548042007058100d1411106a080328081e43d811f00074603110180d0500a902c800c031400782011408101c10021a06002c00c40c980c441c0b410310598054420031610603103640d214034442a18400c000381807100440c0305206041d0031007030904106005501d0200401e80454100c11680e0312107001052400521030203400c10b40700c10060a8104148074401c0d00d10a0050f04035010f070f00c03a080758041411141c0e903813151021f0020325001c03080c0b110f0343d80c0d41074808094000040480e45d00301d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 644107248 1250 644105998 644106011
    0x5090c0909030d05010b0a0e060a050702010309150f1a0d0b010501050d14071706040e0d0e060c01020c06090706141c0b18060103151203050a021509100b030309010e1003 74
    0x10880f40c42030b94040c01603174144540c1c0301c200d410014801d1440340007451140e44100605104035400c5012949610f50a08000c00e802c00e035403c21001d001c07282201100a6800d02e10201c100c011030b60300601821687c00120210110b5070b00a011401d240c1690050211140500602666010394090402c3d44500e400100301c0c55181c0c019490206000c2e207a80380440d1066114109800d0740011f1143d03c020150703010440e0642a101d01645ca81c0f0480d111b02c18412900c0604595454643c215204c1551100096584500b2245040d5650000300c0e11100c0e00d001c3e448010074013921600030b04000026041c01107051034aa0703041200001c612000c02980c2c65a500c201c0b5071161958004071188503890048190186070103c005815a102d8500642941c18a48010b101000c0a48460000560107281c081d894134013008007a440c080742e000200803200070603010001c010f080012501002116860203108a02c10003051594038010741540030b000c80e500c15840000c1d401c0002011502c01410318010482 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 644108498 1250 644107248 644107267
    0x6050903040915050103050c0c1b0102030f030114031510060e121f1503020a032306010e091c02060a0b0418110a080606010503070c050c060a0201091505090c090903 72
    0x1ca4410103450540c58490110410131983c1502ca60b96100450b02001071130b0003042080141c8a10420541d00c040c10108952034010764420019a120040300000d0251749585405903028481c14425000c0c0c0319114640307241201d00f8040c24824042d200d400f000c071380340782d00301700701603610b100e00c809411b4120314446e0040c2c04101c2c0c02c104044e021408403030100726403422541c80b00c081d07030040003640d584103210386130400050f1a207a5064007180d0700002c4001030709500702205100750950154122030391007424008905440402c030080c3c0165019411034043c00d000e190b85000c22084625120702682000000030801005038010b0182444005c000091010085440d07140b030981c88002954030441100210640b428103409060240407210010b040602d4998002400d51000030502ea0400c04062242820400100a004002d58000740b04548410f1003000c02802070012600650f542718501a102ca2a08502e2251174014101500680113202c20b103000e11050103405095011a44420032900c000f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 644109748 1250 644108498 644108501
    0xc02192009330105040506030a09080406020706020f0606100507030c1707060b0604030206070f080706050c090f09010509161e050a0f051305090a0209030a081b06010302090103060509030409 83
    0x41000903485541c0035034400b032089905a0520a04400c104007075078510a11a03030000140e0f030840340100d58069480c2c0e1000d008401409002c5d01c020038078540480e002c500c031a0003051031015544c581d402ca0703001d00c44100100e0b40d207110030f4400319045002d81611644d07281c40382d001008014001c0c24452030041081c0e6810840a20b00001c0c440445c0000c00e20208000c41c5010750f44444d8021542d140c102170454000503036510131000014528200041c010041000e6542541c1109402c04c004103c0c0c0e240103110780560744c1c040d081c0248600d2014a101000f1710f08904890f060b03e8004c0c04601e080d80c0c80388040b580000c2056032103402e21000402d0400b02020000080b040010180e5805464046e6044050074034030600300c200c01800320030300c26492800304507281c1c0b00465070304a034001d241e41c54100da100001e10655034119054015400c00700300f4000c090000f070550030403003260503000641d082d20294039450203000080d4491841e40040000c00c0040e08409c1c1c020302c00d503040d03920301646e88203107a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 644110998 1250 644109748 644109751
    0x4020d060b0307080c0f040212220b0f0a05090a0c05060913060b0c0d090b030c0d0603061406030f1b0d110a09051506040501020d030f180b0108010c02192009 69
    0x150191700c4620148250f0410641c041c5000c3d10030b440560609003112841d0018080040c4042902908003141e000c4401554510b1801190002225112410715000c1d040b007400048901113541c1d1b040c0004590004ca0000d040001c0750b811002114900e400c100802403070740d0040c101e00d54003052840c43c3d41c084100d00e03c80d43d4001d02c0b542c1003840c1d07900b018024007420302e000502c0c00c1082c030145420030480c6030090000c036548980c0d0100099962800420b90100403c1c15800291040b071500350700900e40e24408004500403481182103400701c6068482059903821504100094840e500000302c0b520704201902c081c1280c0309045404405030610007040d0070741066031082010680710014091001106000161100010b4402ea49054101070000c1d5503a0150003d510415591303800e04006060603038041e020304034a0740055070f540760031410041600ea10a002d000040d51804d10950102e9000050503600010b421082c041c40020725169175101094080022a001500702041041903640c10240c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 644112248 1250 644110998 644111009
    0x2040f020d0c11010b180103110604030b01090213090203011a09060c060f04060f1407300e010608010504030912050309031207120804020102070b1c11092704020d060b0307 75
    0x100d43c1c0707810390ba40706402d456131030103518000c900d40301c200c1c00700c8031085500c3e9054a8000902801c05648140840c240340309039840600f29004910001c60f6030002600142401c81d031821540c2255a101c0c0240300481c0304c28400c0d4441d1064400140b0002003003440a0052a60010641402c1845200d005402d0030021191403001c000d000d0100410000c1710310800180b5440c0c01010801c189041d18802c5802c400580b41c0414026a441c0760000c1181c1001c016001003442d19001c4011140c3d5168170000d40420401000c00c2e500b4881c0128441405101c1d6501c2aa010b9032514a003c1ca03280200400010703140c000e40d4980410400440300fa1800c01c0140ca82c1c59607200f015540c0c140500b4030054403c01c1803070304820000420240b00150fa400520b29043e500000e6040d40e45000020248135400301c0003e88060705c80c28014070041104030080608031841c0305841000c058071400c00c408500d18920503101e0940b4013190042009800c1030528103000b2032040c480010340030a0170740040e15200e01c1c2e5000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 644113498 1250 644112248 644112257
    0xf050306040e12070606181104060e040906090b090d180b07080c06040c09060e040317090f070b0316050703020d0813060f05010603200403120c0c0801140c0c030702040f020d0c 77
    0x3000591000b032451000c00a04c800100212108c3d4610f40205110b20300c501000c2180e03204100300f860b500c0394420071403075030300040401c05801289062951403904170340c0301e03558bc0500800840000d00502e409600c6540102281900905004c0c6039165900140805c1e20700d11010302c405500684100100d070b018501030349401c8000e515100005055038419008205080c003044280030019405c0304052603d03c42c3c20010301c98a942c0d4112047c07400c050380000f4820b500c1794420002e041c00704240103501a11011804200c0d0000c103903001e45444c07155420040c0140d01c0f51001d4000203100700c00c0300741c010000c40600c0300c2103086900e80600f80c0b4001100182096510030040005540500c1203e1301c00b9a02c500150b21500d0030490b000e05e90103a4840a4400c008101003940807900c00e608003050568040715a400321038882d0b894034001d1809501c025090805140032070880d85010041c0ca0101c409080154646041c42d03007404060460021091503050f000c1c00000a80340240c0101034030111070380e41c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 644114748 1250 644113498 644113511
    0xf07110d0212161403180d11041a1003021909080307060c120507051804050c180303070b040c03060c02070f15090b0414030c0a0b09011d062106010f050306040e120706 73
    0x140206c2c1381d450006d46201340201c000290000305184240480d003941102c0014008806040049494a1645115038862003181901a900350140c0c0944044403032640381040d94000d4000a80c1c911120740550b80706a4001d001e800c0004d286d98100300505107007450300c010710655106440068860941700d40010070008501c4186501c01d8850348203030200116010b0140e424842c0075031000b485004003418021000500070b00c01910304101f103420035980400b414071a8039003420069403400300c50004580490030041c080c402c0d24030002c5c2c1d500a03208200c104076040303480d044510342000f109a143c00c007400000c80340050180300b032802510043c41e030480411160300343e01040504010012410500c2100e1a001c1401440c0c80003044c3d80e13030740e007003820030a6200c00c5859072070309100b410740541c41e844180041c0c10701140c007c0c3d400c003854210120500905c10b4440c1401500c00080d000c04070400243c0a000044407890260003041d48047c030351056681c000d0740c031541514a9800076001f036030300d241c5412 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 644115998 1250 644114748 644114767
    0x1707030e041e0c080c0301060f021203042103020403050c041a09160e0a1a0c0a1e0309050111150c310b1309050615030f07110d0212161403 61
    0x45043d2410310f8034040203a480c0991210000d40018003401c000c020b585200d05460030300821025248607075003c16181c03603141074940404144411420b9240803002040400d000c507020340262000e40340d2100203014050050002e0000030724040810003046002c100328107455886500d040c6005a0110340c840c210440144070140c4a40807404055008034001c0204008a10a50140f0701d81c031204a081d140e50744131070303601e424a071126035140603107100c10101000d40003814000f00000d4083c030a1303e401101079598030042d101244402c0070019550400c0214140101020b00c105520603215a03059007070448552108411a90400a20b46044000c41c04001c51400c3c08982c82d009008540d2154035021200ca00034800c000e15214484a50307855a000c100300c0d40e26015005481d00d143c20b10561a032a140100155030002a140c0303070007042c9041d1603001c98440c007181401703a004403900101aa010740070040b0700c45a0014400070111544c01c8100310018184e49012540241000003c5480b481e000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 644117248 1250 644115998 644116001
    0x10902040c0c081902010204330306060509132d1404021f0e040f0b0109060801080d050721020a050606040501270b060408030a0801080a1707030e041e 66
    0x214030001444202da40040001e03006004076281c01d107011007201e009284014050340a400b0701e410000351084d04d07a500310441003840e000f04032030040d1414046565481404181c080710001d010f080300081c02081300481b18240074000905c80c05d00040c0008040220801110301a28158050800818500c01001001d6001c1c021603104071031701c0f4560317050303428a03500048000c01c1a000103504032181c64600312585010b030f0f11800601d50050024000e690941449600070000024824046001d1000204d14282f14002d09416103007090300512016a40c02e03000c0d5070f2030704200c0045903110302003c0e296140303a281c150b41c8403240c841a00140f01d008610314004d414090700801c810700807490000104040100b580c2c2c02108000c0103100c5e000740e88071110503840542841d00043e40c11110000d000501d00764000b00801d0742441c02d50751034910340d8031081e45540b01d550b2701101a148849107a0000d9510f4560f90040040c580319042155240151402080a5511001c01c041d04980c1055031840c1c4140d05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 644118498 1250 644117248 644117261
    0x170f0901180803030a0605210a02012303010312020f07060f1809020706061701020f04090b0d050f0c01031107020a0b0921031e0a02060c030c130e010609060f0c02040f090209040501090204 82
    0x200d2040c117811141c00c1d549d507603040c444400303410040100000c03130702d40c0d1060074402d040440e1101da0655960f101e09000000440140300d6100510880c00503880c194404180d400a070340c5a0750386c10002e40c1040000b21044034200095620003050148009100c0207240b0091407140d101d41c030081007043c03804002c520050400c03840709507980d00400040d0556007640003140c0558001d001c0018811040b50301161140100100c024032a101c1c41c0501c101445000643c04031940702644c0602c90350f4620300401809002d0080025040b10000d08144842c00e01000505059800504013144001d200881c500260b2000008a2655000001e50400240c1d580b604c1d0041165012910752501841c801c1c001e580d0b150050a00a51910100100fa50620901c045601140d40301d4100c502886e2140d2149213010400e110b04004680100b400003060fa024440582c2e051000340c40700b90462100b0b40a2001034008210034a540700d42d10031715140141e44840c0014003481c0600c00000301c0324118410302c800c030380c0c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 644119748 1250 644118498 644118529
    0x30306080a0314210a09050613150b0609060a05030411060f1b01020f070501060f0509101206141306060509060a030303020f04030506040b04170f0901180803030a0605 73
    0x6203154000310303401580d00c440d00f01c0358448a540e140207081510b8440d0320701d003650560140c1500c050241e0820150020b840040c022020784280c1c1c0c54000101c1300d00c1c030b07007000300030542c01c90704101c1803500480e0362040c124641c0c0500380030b181184990002c0d00903400349200f44040740002c03040c0270611151900d85250103805a138254074241d1a08407242071400344841d9803a83d00081c090410a0300707404e4040c0c52a0314a1031440c540c6403161490024060306207401080003125658000050314940101e605001c1d013448a03940e4400390a0244066541c001c00200341c41498484100d04c81d00819040c5007840383d0315031103456169000301c2c50000140d6003d40e00c80c0740b14072000c905001440d920349100c1c10490341d05050041e80d4000c503000340d4890303018580c0068124000e0604000c244038641c890188150f2080c02c0f80c040400da072201c00c40035802801d240030801041444283c80321350003508502c41d89201d000c889100b0703503983e07103200d03145a00441c0d850321455102e4030200aa828001104e614010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 644120998 1250 644119748 644119753
    0x120703110c0a032003070b040f080c040203160804030e0a0303030b0103050711032209050703050415060609140118061d3703080703050702090f15060a0905061603030608 74
    0x1891501c5149010413005644450042030882190a60f5420040c1e2001014420441b5480300c0e620a4003442c001618401c40c0b03c54060742c403000e113141c502482101d1160450081031280e2500c40e420880c2d030020018012800d0100c1c0c005001603030f5a40c0c0b1030900045100780d50208202d1220b500040c1074800c040c2404c401d00c262a4a0400c25050100235100c50394a1790801c140180c503a56207001011429030320207900140b4050900000c4e80d859044a84224050000c03800600c081f01d5000040321042d11804002603001d00d0b040c03006400200c684040f03040145810101180ca6070914082c140c601d5200d00045074462500444421181700702da0a02c0b28101c032810f5207141402d03995082003050300701036103d00c52660a000114030f400d00d01c5074095070b000800c55466401d0b0b4500600755074804041648a04011300000d030840786036184051040c00d59040c4004c481a142050203e5a0481906101407111800307000c505901e400c8041d1902000c00c4000880d40c1c080e1341009822501c807a08524041d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 644122248 1250 644120998 644121019
    0x70201210515032103061c0c050a0e090715050702030f01060305122a1f0903140f0703181e030611132310030b0307060519030e120703110c 61
    0x2c200c00d5113004016403d00c80550340da99210b03400265860944040c100d200c5656408079018440d651060740d0a4444c10750391003400c9621035600c19201d910403201c5801503844450140006454815403545031001400c115040c07160560000f810944051071101c50b80e07644140410038030208103c1c075030600c2e000301d6030300380b40c200210160022810001d500000d2445030030820900350904104010340200049a02544811681c80034000750000c1442980061715806d032002000140000301c50004000003061441c00c48036aa058807454100c08505403c0d0052400000d244c82400d50403c984c0c142c9600c03004007440c218501a0201c586c01341c5089681700d01403151561841c03c2c0c1300d4840c07e6846205803448020104140e03094421000c2d4882d0b034105409602400415401d508428030303c0c6022800e44540588074401125540590100321076000340241f05540100c3c025807101426219450681e01c01c1d135032025460405a018030750032000202e1920760100d54400070300412032036040484420445 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 644123498 1250 644122248 644122273
    0x602130b18011b030c020d0f0803070809070e0121080f0403050f01020c070e040f120306090b04051b0c010905240915010b0d021b010b030c030109150207020121051503 73
    0x3c86000203401000c0c08040103d18065648441441c030740e15521101c074501120a5107030401458005450980c0433410304400701d503a144001c9031610a1302c90020010701585e1a244e1010a0403001d40d14070861000042802c0b008104104004c00c004c6210782a00c6030b550307140d40340c03081c41d28199081c0740741c10381d00c1480f0005000d83d0105006045443e007140100c034940780d500300050b9840c3c403400014007003a800301b4916400c40c6c045c0c015900700c4401e86000c0041a074a00c00344070a0342e0040b10058203c052018407528500b005070301030000303080081c000107203c1004d9036550341340c0f054070b00003502c0b80d003d41c11880c0b2284400c100407a600020400107016000b10b000c440054100c0c06014640c03c445021901d207080d19025815070b8803000d046c02c007034020140da6441250003007800e03400c114028081c210701d51809003414000c0c1d200555203e00759841d255440260782000750014401281046840349070440046c086294104004200da44000380a0420002003603544100000c01c50083c1c114035100042d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 644124748 1250 644123498 644123537
    0x16090b03060a2307030b0a0501020d200c03030301080102091c2004020c010516091d01030206090d05060a05060901060c02130b0f0a0905040c1202060a0c0602130b1801 73
    0xc100c40102c101080680030600031902d21a000c0d5003a40316182841d0801803950b5240e001000014026209841a141c440c801242c481907444111b102007000e4030035000e00c841018403014411401c0e00b09807502e00540e540000d045520a922154a41e07401080c42704280c030b0722103030314503202c0201003500c40d81c8640c50b6101c00f021160104240544c2e9900b40200c0304a44494040340c00310701a0310b0007001249849000b0a40003124040020005103000c08013040c07104030741d4800a01c450542804035141e07880c40d420864a40d200901c2d0540007482c0383e070f0010014408012680c05000c1039800480c9500d0000c00f40901031405074020b40030000151a07500141c0c0300c8015400e000d5103105804552440b02c940459455298044099009181c8500020b0707400c82d5503224034016032180304000300ca02d5035140703110300c206410800a58001410802d4418841c01003200010680c89040054200041104180001d0201b90301105100400055200c0e0740501c207409401c80f00d000f4244880405452002102c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 644125998 1250 644124748 644124751
    0x2406090a09030c030305060d082d0307140304080f0c07210201080a0b03010908040b0d1406150c0f01150302012c04020708040305060c040821030a050619060216090b0306 74
    0x81c1410799886c003195160f01c0e03071095261141c0d000402540d071042e10340124200e003400030400c2203190982c0d031940c54144c800101140d00400c002c1c0c2c1c0b10a107c50b80540744041c070f80e001400403250204104956800980c1d85030180c001060700c14040c103903541c0b805404203410255698040c001021060106005030f8010003029007102501200069992080011a0041109400141c1040c0e4080380004074914000c000380100c1c0c004d540305003d1101e00c6442c81030814416140c09510254041d00840d0300b05d0040c002d8041c205616084031440d01c0c8100c1040e0031220b040c00c10303150145a0340f0041c010740d41c02400130800421701c40b84c0d0807007880a1807800316400380c0300d1003001e00c540e400080c030a091001840545000e9034204007038445038100900819100e60080c8104042030113503004000000240c006107019041341e0400356132a60b5500710b1450018240284816488080c2130303114150100c103040114058507041c3c00070910b14103e601c075034146010307944c42a149182048a081504d03100400c149 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 644127248 1250 644125998 644126003
    0x30504080a1202070b27011a01080403200303071713120e06040909141203131a090106060905030f12071a041203140702031207022406090a09030c 64
    0x4219280003070b804042d00c91a8009000c440010050041e01000c00d5044010141c000f10140051103e20805034281d0701c2280902ca03030650b500c1040d440c95405070043c1c55015100340743c02c000420001940451500c1070200361101580003104101c0084d400022070b08461400d40c0e0349003c1840c180f4015042111900300081c105034202081c0000e1038010140199240d0009003001d4403240c49880c00c100510b07400000703075900c15103542006041100401e0031018460800f4000d441c5540f070311801c5244e409000c404403120301d82c1904011300c081c134082d502130260b0340104c00420068a0700e08020100112a04803038400d8020a140301b200c0302d4000382d4180d034055405015910340480b0b042103074494502d42c8240a214513141d0820040000c10740c60301c0700c114400d4404002c104004014400094400c8541c080541d104000304c8011104200565910040f2131044912014251101d10320903012110703800940c2c03075002c09209007031915000e038503840201c5040c2009413000a46000b00a0302000e20003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 644128498 1250 644127248 644127257
    0x80403180509070c0813080609011812051e0301060806010f18120c15090812070c030609021203130e0903070305220312050705060a0605150a1e0e0a06030504080a 71
    0x708040000c2201a110117071b08064114080c41c0d55403031700641f50308080b901c2075025442c201c10042d50350480e21100101da500550800e140c40c516400955207a40000743c0040790180301d00501c1580b9500b000114060082c80c0d40d0092a41420390000d00822040070140003031100c050080f00d00324000428070800c58411602c40f115140c42d500745000c3c002c000360044c10f00d41c0850000300102c2a00800b0071401c840160017294204070300050700d05031500480c00700805424003440d040012503159085406440e00080c061040400c203000d9861940d400358528481140c007407202000b01003003003080154824200c0c8041e40c900101c0c0c1c0e030000c29501c42c1000b82103004241003121504012050320300005103038019200c1564001441d0702070300940186500700c44a04c100c0000419441490150400301c6201a0100c2c2600690400712500303500174101800403c02c0d07640d08049002e1200f101078101101c0d6498bc030701102910b009002000d6410b40250042c1401d003010311001420348800c83d51000ea8a04d413 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 644129748 1250 644128498 644128517
    0x50a0f03150e010303020d020c0d020f0f0d060501051905030c040c022e0b0d03200a080f0d0b0303180f010e04231f0e0709050a030308040318050907 65
    0xa4008241d110381d00c04802452440102e10071a0810805060741e00a07000c8400298150000720b0340d61400c10f10407500611603010000050400382d031070102040d4002c02d180c04124955000c1003480328044015511541c45400400250400031070b05503020f6801c20320a00484e050401083e40c400c0d40e0006140583c2e6198500031480d403090201c161040d82040112030300803110f0707007050001414401c0ca14101c0c3d2500301070050b6407504103440300740b02e50325496084801d0300000744084005142c0070344042d940200d01d920070009002600074001c0c1500c5100d11901c8a0b0241c410800715020000428003035070007000030300c060103521850592482d2044030140b0a03040c9403c012100f8221904505402034200360100f9841d6149440c401500e00060205050311b69440076140311560402d00402c412520482003030188040640580303900407010704007d00c4103942c1d07001140710440f00781e000383e0002c2e405509101c00c05034814520014846010040c50f41d19040400040090202500a8050248100c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 644130998 1250 644129748 644129777
    0xa12110906270a0e071205060325080d0909060b031e0c0d110904050f06010c200a080d0206010603050c03010e06010c050f0703020312040b041701020c010f0c110d050a 73
    0x203002d00701d0200083d03c0c0302c2c03a00c2c1e0390b1502000300c0391050301c0c0000454020204035402c840548503c0b40311705c100500800d01c00440140508034140350b40001c42210032072040c0414a1401000400d40d5405696514045a80b07020101c8080b20381c82c0c0c00808940b0b40801c18002c421034ae000380403100e2031441d031042040b511060722070881449180c03405040107080141d8420217107001000741c007031843d05990600c00c55849624004002d0f4088640300d001c0b4a8408030080460700807000d0b0034156600040100e110701016000a28003d1316901c0080c480c0d10890071410101d906100e0b25004000600b4140300c182007086824000380014000c0d81020b00c0401d001a500b0384c414480c5405081c2c1000541d0141c41c41400b499071140003500041e400780c8900011115240d40c44001c4034102c038045049503041c2070600520424501c000300c0010b44540d020700041d00480001c0c030a201283e8035004000840407010a4050305c0001046040311442c2c1024440f0324240d5004001c90710340b4403062410141140c043c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 644132248 1250 644130998 644131057
    0x21305061c090602091002010b010203031504090c0305011b020a020a0306020d02070c09271104090f0501050c0306091e0105011b0f05060105150703020a0f14030a12110906 75
    0x841e4905455400c00d8201424092981e00505408009883c00ca80c3c6200e8114280d007030b2001c2070300c1103005074010000190142000c1c00c505242a83c0100007090041c4035444502c1c6003110342d002566580d55403010f1001c00f801d1030341c80300d0b038428240c0040d0084084c503070001091011680700c0507200b15000510f55000c4030a583c1112078035503000340c9868000d0f4990b070154004040c80c0b103850382034501100e506031a00c0c0d80c0c2040000180d0344102079074004145c0000384000340c034042c0350881390480100e80801c00180c1c21f00030588507460703c2c1c030f1031922494840c0411402d014042d092050903440c2061424007581c100d905541500c800303081100181c00c0d8148102c0d00b005c03040c80c010300070402c1d040400c4200200818454100d0703904440b0340e20b94026040c9640c84600c1030000c0200540d00500b044800116180b1004e0748450040c00600d4801c0d4107041c4141c295071204110800003450840007210807201482000c1c0c07500004094941000101c10106820303200e02e500452080d02a82c96031242e49845 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 644133498 1250 644132248 644132287
    0x30f0307050910020d110304120609020a050619020c011e0f021018020a0501090513110f0711010908030a091403011b0906171605030916060903060f02130506 69
    0x9003182c40c80d054103d2000703440340009024240000d904400458440c480001a6819134203989000107a0420554502004000c10441241c2080c01008005002d42d18040038054903400240704d000c001600d40d0000782000d00480701c1d01e05101c10804200104404c404603104c120940d03040059031800c03c1d81d421b83c58150914508400b00c1d04001e44000300d415091025052244213494140e030982c0c4800c0103540e924868003c058100348120311202040c2d00325040007415100e2a42042e01e8905100e940c10910740c800c00007035854995885c05030146581c031851304001001c40c036004e03509000381e178034000f4400c0a00748078420f00441c041004903030640e829402050641d25030441010010410302028024040b0380c41940701155600e0302416050910ac5440317803064081c900e401000000e4000140c80540016011030140e21840c005000403454001c4540c0181c1495250800098a546480000c0c1c0e001234841c0d082860041c4480c0c0b00b500d0580010f202a00c0b0704850321a110702980020b2103201d8203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 644134748 1250 644133498 644133517
    0xf07031b330c1211070b030603030715020f04090b311e0e071703041409070e0904200f1e151321020d02121221070809030f030705 57
    0x100c94030516406401021925840d6800c105079400c0e946e03150b11018150108440080d0150401c0005400092032110808100b1905400040c10002d80b509034030065000380d0080e202c0955130325400d42c000e103418486004505003403c01e110507601c10300c0d16507078900300d400f040c3c01d001c58581401c9250014401506103015561450402045801c40a800e0780c03055507105402c2c1e01d0007200d0042c400c10b213011040324107a5000030400c2c600c1c58108005d1100d000c41c014040d01c100003042605401540c1d40407900b03800786010b2407a950381b80c1d142c5c8001c40d000d155061046481400b440c00c1d2956207172145203031410281600c1460a07028030081000c035841d02c0910040705011140003507150050501c2500c01c6041d101807a050722500035040d170b03009a60804000001e90700c420951101e50051500704081c05582041400b82d8050284c40b00a00003240c101c008144c01220300ca4040c00b4071741c0e51004819500040500d0600d10301d0604503402c9c4c2c3ca03446480380c400c2032054000006424a8054002c8402c0c224 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 644135998 1250 644134748 644134763
    0x30e09061507052503030c0803060a1d0105010e040e07090e01150618061d13020c0d030911220b04060510180b0301060906030e0f07031b330c 62
    0x4841d07190007074a920740300120f0081c03c00c50100e5602c0c440003096180c0113403a415107d0403001211511203582c0c0341c0004003290303840450020042218041c8406d6242d405d000c8005544240d41050009000448940b0300140203074502a20348852440020307050301105e0700c840c00040e142c08010005400b600624198951061242d0000103141c2d610400305481144840000c010346074031003008840d91000210190f024610700d140099075031610380f070032000c0d0360003021005281044250f1483c2c1010705001e60b10380032030381c0c800580040c0041c40004220480044452f50080326001803e40720000780c0c155001c42c550796410964450382c8841c0d0091014100040c06114240f40c0c091008007042d582d003091110320100903100181c04407014007942c2c16506030751500b28680f4200901140140528041c9903a14800c44440c03000c0004180205409503000311202146003038255a02034036069903a11400d00701c0180000701403002245184e45904100c0d40300112070010300003004607154407807941d0282061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 644137248 1250 644135998 644136007
    0x19030b0415060e1015170c120c0c150711100b0f030f060c0c01090c090219020601050a030623071115101a0c010603050304091404030e090615 62
    0x740d04501205031103001801800041d440d401c5815403410203035241014000080e2040c03141d0103000c43c0d0710303900c0d9050b4902080604a0891445400141500c0e41d0a00b600e002800d00341c04076902c5401c0d9444820392806516100c40280401c3e91080406455048107658a01054040340f00e00c45540c80c0c02000411a55001105001d08000f00060032003144140d44046404509040100d4003810b08603007100074242554071001c282810b5801350301c1d81e28040d5600c0d0000303400a80c0701e0001c1d0020300044000181c0f46c0401d07810088000d2038001010041d0361000740100815500c0d040e064095030b5001f0390100b40c140c0c0e0349070007009105420f25410000966103040013405030b807240000c0c1d102c003107050880311451880501e502941d6020b071400c01240c42c002000380300d5a030384e100010801840e0401d0071450028400d003a2403c441c5546c108944a400000c4c0420000c0904e0080c1c02c0040d4450124035218242683e01400d00c40d4a0b001090140311020000b61999035452807403001c444c201815143c0e503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 644138498 1250 644137248 644137253
    0x3031801200706080a09020f01050901020a0209042d110d032604020a0f1d0c121302090f22020321030117030a0c03030e0a1202010507020c0405070e19030b04 69
    0x2c2d14200e0140c10006148140000c018025034043c0142d1190040d1a5107210021580111515481890303080d06501c10390003910016140c4100c5184a140900e86000341c0c00b1140c03042142c03090a00515100e88038400301203401103141c24215001c074240483d40d98280d80d010b03103029640460141e101a03068850760703080c0040703842c010800c184194070032103204500e581c64107607000c42c4040d00d000c0d240c1d030038040300c040c044114010711a20f60170816011070241003a40344070344441c2018049a082441e003204003150001c604001c0021500a80101c43c1c486041c03515240f94541c0c9802040300d900000804002c59055442c18803000840c2000a01209440d812102c0317240031541c030038480e104d6140d084401c61100c03c04040142c45000c03000381c0e00c0589800d1592812030160502c80c0081c0074900481d40c8401c0091610b07490000301d000d0f2900041071030300d0180300103400d1850000300705020f282004100583c80340c0c07103695410903800444005940c203e50864030582d03201c46401c0100820ba952091006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 644139748 1250 644138498 644138503
    0x40504051605031f0f0b030a031e0201020304030e06090d050f011d01140105010c08090a060c02010201051305070501210203010b1c0606050f1b0d0503240303180120 72
    0x40c1c4903140280210466848050598030262403202c1e0314203405140211103e4040e0713800000c1c00410038403002c2943c0c1100c02c002410944041d00031800306d4108009041030317158600301806900b00600085085281c261000351031002641d83c0f9a104003400246400c0e1662820304503924907421504035080238900100d8503000b46400101442e100482040502c0d01c0081402100840703040302050305110792820005481d18120403104a401c4407051010840c103403140aa140000c1005035900102d40b04103000186c02c5400103000070000a851050000203d080007800d03c017241c00038600303061401402d2403c400c1100c0062104c0090030300000000500d0410003000e442c060f42c01030105a00e210782c0b00c084c10100e034014800c68022480600801745a40a60701c003070310200c0c00e451451040100c1c00c052030382c00c00000c00720301800710320080180451001005841100c0c428111000c1d03408a240c0f0340000c0d520f010312030f050050360010b904800a540d200c0c20240030f803803400709900c4c0388040100705400e8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 644140998 1250 644139748 644139763
    0x60106261602210d050408160b0f0a050609070e01050d050c210708070f1116090e0109110d02030f0307060606030f020a0c15060b0403050709060e0907060c0201020c04050405 76
    0x80140f08007900090000d030350351200c1c070b046042c1408840c5803070f00b2008120098040100f0a03100c3e0340d024010502e0308034102100009161107450300e014986008400c02103403000103000d0030056882c0804120389501ca1458868120305175007403170000a400000100c82c1c920894801900340350400c814030141681080140803807084540d4049050304006201ea49540d400715081c0300020032040c003184c01e1901a40030651310480903e08242560342c0c4a008601c1d2a1444c5000411a01107080821003200144640c0d01111100c0000380108002e9859a128007420f050441e0701c550340c0d1a45210840d64208900385010307540200392922081541468401081c00384201030200b070401d94108600d0400340f003120750f4203070503071500d4034a100503840300d103803a07000018801609680d070000480c0c0f2099100c050002503104a00400c881824584080c0503610a076100016402e035000a10a070002d01280b91003d4404501c4c4c12000c4c0c03211030004074901304241c1103554205141a0501081c8080403132442c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 644142248 1250 644140998 644141041
    0x204080105090d0c031704050114011e0603020a050f0306040e0a030809010506090c040b0a210213080a020a12060209152101180b031e0102091c0506010626 68
    0x83d00c140000010580b10103840040007400141d19803042680902403180c41a0000d000783c00000d000c0c20401d8011501c800c0a80020400070084100042c081946002150141180c1c4c6001e50401420b0a00580980101d244144014001000040301600ca03980480415120001114001300050402802542040e07a2220040d424800040c0f580c0c104601500d01030b11503c00804d10307152070542c2e90211038001033700000410030b03244501c1106000403910880000c2104800595455040c4070081c50720704654456100c0350400849039000d07a8038a001a011949214013000c1d4144580c941400284144501c180e4800c80944680da10100800050100c0581d110b80118543c0742030b428030020b1050034490b580c0e00344281c49010b01d1003800d64200b181c1c15900030341122003c0d003003c41c01d82c61561020500030b100d40e5012807055643d1a00d03115008040700e02c00240114100380b900d44c1c517165081401003006011080280d0f0300e010300c806003040800899a1940030780da04010819194075000728201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 644143498 1250 644142248 644142253
    0xc0a0305130b16060504020d0203060f07120501150c140a15051311010f200d180308160c0b03130203010c030e0a060c0224010609150c150f020408010509 67
    0x411100c4110703044450183c1880015402400c00d41d541c8006880014800ca8011051001031001600c003045424080c11070152940b06038500803800034800440410780c030810343e08090040044e0206150302d00903044c254074014100154074248410481140202a1780038410565860305104284000401d50328450606000c075444a00c0b03088a07210461070301a100c0765555044480301e41c01550480070f80c011030708201000000c280da203000010b070700060480040e0080f0040804569005841d02224003290101c00c0700d00e03066440f00e4685004524010202c401c01c44a1002801340c110842c0c0010005040115900c3c6020003d03100302c3c400028049001e58200080c000a06001e4004d22213019400710041c0040c04481d00e4060150415400341800c2d80034510203000c002e030104800007241d1140200740c21943d4076043c0d000740b840300a0391143c1c050040a03080e21414a621030b035060340c02e40c2c000d4019400700d2040c00206000b0111082d190000ca41300150010b02140e064003c03601c035030f10b00b005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 644144748 1250 644143498 644143537
    0x9010906030209130e07090216110a080a0b04080904050c070308100506180a2c010803031006030222060306050a09050c03060907020a050115030b180705060c030c0a0305 74
    0x703809900034100043d81c8480510b811422080055110700e01c40950901140c0303d0590311110b1300d040b60301c00d10070300c03c8600c0403400200a002100980c80351410080e207946200502c1c4c00e038010b440e8464a00010042d1241d02c0101c3c1c140b298103030584c1c0400000600420a5050881d0155a5a4010213048010440d200d00244202012240400c12568041c0036145441c0030040108180c2d2144181c050b400909130002065041300c0c50551004043d00020210000c0d54248203650380280507800110140d10800400451038009004401120b074182005130311040c40c82041520003100a412410390580003a000030402d5068100c001200c03009c2d40c014090517120250041501d100701d1300c5900e11300381000441c081b4180b580c20309611160510665000b000c0d07603034a860030368202240800301c2c0c0b25074140510a005034005403903040b90f841558100700c0e05104401c6601c0d02d09a11070f061055001152540f410340050040300e021024100950b482e0108500c2c0180c1160000b82c43c2c807043c200c2900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 644145998 1250 644144748 644144759
    0xc051e060702070506041e091d061302060714010b0334120b090a240b040b0d02100908100c030606140301090203071b0c03060b01021902120304031502090109 69
    0x40ca083c26642d014000b24942810f140c541e00d651040b40702d18521329000007030f0000304000f181c80740402c50015080c0103680e5404411401b440c080b00500114409008605444016a520300448030345e144c0c0108101043c10045400d10300501d29501d4441c2c0601403d800c0c0c0c0e01290005c0d04c5905070080301c102c0001514070480182c1282c0c0c8050054009440303030400d00c4004901c2588a40ea88120b43c0802c845004250b07036520340011a403810000c0e5000c1d0100b446443c1c1c2001c07400350079108503040ea41002012071010000341a0340c02c945011703000c0c1c01240204c44a90388074009842c040c000b4802100c46020085092030002e2080c1000c1c800041e14054002c0f506602c0360308400d201246586940c1d00b96402c040a0400a500281000f4107001d4607045105011200d103542c106001c0c0a4118100b6407407560400a058030502c1c00c43c3c0341190170100602c0c4058003100c0f5036090721341d01070b00c10b109218420520707945580304035000035140d180b105030f01040d06c08a54000f81042c580c20390311120802d0303649 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 644147248 1250 644145998 644146003
    0xb0a03120e19053a03090503010506010c020f0409110409050307060b0f0607030f05130801020c060a02040b070b0408070501050123030601030b0604090c090c0309020a0f06050406050a0c051e060702 86
    0x38007456910008080b40c0010010701a0b0803082c8003800c03007900130008910b486555054500100045020900a00d01000646000e02c500382e4007410a0a00880107081a03002501c1c5401d9500c40920455403161058140203040d4400410000044d00400405074141002a913035000388000b2903090381480069010780c1030001d260011844050700182c10400130790b50070749016480620000401c00c5c2400b21004100c100320100009040100005940d03841040189007418801800d260304a801081304101c290800e4084908040e0009a032000315112841d00e800c1d140b04109026210303600700800401c2d0b403110201c4004591b0f1004070341014030b0135001c040c0b6807940300034403001c0c00045800c0002007185c10702d80c110301c10480c4180c0d903010105855100e00b00c2217030b0407004103c00081d901c80030360085081c00003250000d44610a200c00036145442c000900c0351040b40030f100100720000c0740040205003d0310030150704590110a0314104075801500d80500c002d425101030300c6105c0c94001c640c8641c000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 644148498 1250 644147248 644147299
    0x10204060f0516020603190f0b1e0301150f0f14100c0f02040903020c030d02030705060c0a2a200306011a041d0405070819060b0a03120e 60
    0x1e80740c450600660850540e20b507080150303180c0c0860034010200300140c2d00d0700300541c030030b1324101008400c641c0810f41a0040b0f070780910020107003514000d182952651101c402010b00c4826461540011039014080b030702505560520011010b034003e07006ca070080440340c504095650b07500380160400d9072282c0e42e000303808a0201e081c0d001300400704d00f0444584940d0018182500a013001000c00c407450740840c00f10781e000042a80182c0040d80c00d903c0d5450184501842040c40e88000c60401105844060700c540c001b070800300c4183d03000100e44050a001c3c88681c540c40d0158214900098110b145400481e072101200312942a80d07054540e200c508101c00c00b07112500d014004103c035a0078610090484000c54910560500d0107201c00100480904038294101c0c50405450b0464141803a1951801311160821349154008200110340d0301d030b82100d289441d84e000311001c981c58036002d0104040e1481e54102a10001003031408048494201c1600c80143d2400d460007900c0441c035000c0410148070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 644149748 1250 644148498 644148509
    0xd09031b0b0c1303080d05090d170a150302030d020c030d05040b0304120324081e031903090804120311010c020c130e0706020d020106080102091f0c02030d1d03010204 73
    0x400714040756520312004094101e20818000c0902000e071291030b070b00a1a0010b085000e801c6466004211610200780304120664005003404001d000c4e0100000d4624940240b681c00e00a43e40c22089803681c0c001b0042034006e64002c0e0aa841250303484100a4441c003002d18a60300a108003107220072443d10070b20440d402c54266003400f0703040d0348a55903400598012541c90004164640b040b010139030200c4600c0c1d2810640c5075140d242664a4001d4042c140036000810080501500e040085280c9021080354200662180c0f10803810b10504025030082030690b8014060030030201d00401d00080d03540a48180c02d000782c4030000f40c2d140c6040e00c2400d8586103090700c0b0050300321b51040d80d520b040c5074003a400307170106058000c0f070464090044689000c6841d40100010b0b8003a0100e880c4054080c46180041e080050003075150840d070b6004240c003898540145522500040110b5038064815490300f24030990040c01c1d260703005090300004064180510501540207806030305c0003545c1c42d05208407000c41c0e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 644150998 1250 644149748 644149763
    0x304080409051902160b18250e010605120907050f040b04020c0312041407051008060619020601060908011401030f0f06050f0a0506041a240d09031b 65
    0x6051185003030180a01401041242c8043c10310b0b140101458009801c02928488818144425904140e48059406003420400210b034a840705506c46000c1950403400c0c4a0980240f51020411003038080a0060b80c0902e48000d6148000b08030a0b5104000704210f201102e001e00c2d040d101c05038080c0d1201000e1280c60351003002d0007032000701d500f010341003002e1404004000500701440b90303007500c2c15a4040c80700c0c841c50f202080d04100030840030381c1071a501c54048074020700b15030341804042010b401402110300188549080010012303034403072040700c6040341c204114840200c0c407040040c0d41e40710f080c0201400b003410607102140c0c1d032105200754120410202206d10030f5918544502d051003803c82c04c140d8003e44018400f4010440c0e1307000303d50050040301e1000415160000e1104220b8001500303640c030850808000c0409003a00c2c610080206100301d070480d2045155075018009041450341c05490070b8004a0b0302d900c1100154800e0320000c1c0282c41d03103824844190900415040d0741a8010281d6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 644152248 1250 644150998 644151007
    0x8030c04050f0306360f060103260307052b051909241104080706080a0c08061915050715021204030e0301020d050a1b02010b1e2b0c050303030408 64
    0x1a25250f0340d03480c1e17040804c581309440c14110500142445400b201e890700c00d603c0100100104003402c0d0403007c0102c0e0250110b80c00142400b900e0035544005440c00c7c0030440046000d09031010f5920114854804006085101c1502c0e80034420240c04101d8411103120b2180800b04030401c5603014402200e5844601104d90b01c200a01c00780019030056820750031203580d05034455880b140f400007807000c0c026074001800301603e05a401403c04034010203030b440850070980009890b075000403149070040f4049821421000a41c000511050f41d80d0b80111001720030300102c5504960040014001c55002d11518002e07104000c0c4100d047e88582d12400030f0440302c480005e07003c02c3c0720310b032070340e80301c2c0300c002d00241c41c00ba000d2036008140c45055441403001559060240c07007042d84420f4403d01801c1c280003c4c4400d552007000075850981844441394840107030068000f0941c0e4030007440d15402803445191034a40b4880c845039034017402c040d41c05c4410548100e8081100d00d00002903d1140e0351001c04640342 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 644153498 1250 644152248 644152291
    0x61c150c140a08042604090e0705060307031e020a050a18080d05070303090512030105040f14010b07020604030f11011706100c050f100e070b07020603012108030c04050f0306 76
    0x908600420640d2054900c000210250881004030700103605e00901307064130f039820030840d04210343d84688582090792100504001036119042920b511841e1070500042102821920203404c0c031b0f0420302d000a5900c0000d48161268000300a049a20601e580d01400c103280d084e402c1446181d1030207241650b0b03010f05044244248180c0041c41140d11901d070106880005544161030601c00c0c044040c42c0701c50110041c0590b003458401c0990502c003201082c0461502c0e00304c281255101070265034407201d0000707a00e2096407601d00032200150b9203c00308541c122007600346990540c4180c2c90041c005521511140300540c141344005010b81c2005009070340b543d81c5404260303a06e502028046440340500010501c2d5207d041c000b000e149a03000f9000b1541140384025103041c014075030010320254070240071220240e00c1d8281524103445070403600b91f06070381d204e041c1c000024225520042200c14000100300d00703403a02402400c11a8425600040402880c0d002c26803940d504032000c0581ca5800d07810701c2803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 644154748 1250 644153498 644153507
    0x90509010e0903070c0e040b09031306030f0204081c0318031209111206070305070f1b030e03120909060409030518190e040b0c040b0403060203061c150c140a 69
    0x4101645004591814825903a00b800070300d03161b80b01d0001091800c08020901c40c01e0114182d020040f00055407508041d04074400a42105000e4001010343c0c8140c0c0300d03400d0b0700c03e504440103440f82c40d0441b90a12041e418039100c8040501c3d2440000f804c22069102c0c0c51101403010810030f5240e2141844000f00e80784240050594aa0a840740a04901c9000094a1344096200100b800e07c015103294605408003800341c9002801400810407400b40c1b0708180f030750280c0314500c010496100030840000600b03007101d007418009449a414000c800c5840c258010a2008004e0107105803030036035030b55031120100710895509140207004501b04000a1215500c8400d4001d41e0260040100d5190b240300200c402c403960060308040205002d850600c0244454254030310b40c0500e400030300c58509414407011520758040c074440203040c0c2c3d4002c40482d483e69030f0385080682c1c6900200c1561124151410b1080945008a04111050349460941d96400b40710700e0f0b1400c020781e20722074610f1038010020b400700c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 644155998 1250 644154748 644154751
    0x702011407030504170309040c0e031e070803120a0e03041a03130c0b250c1502010209060f07030e01021209120a06050a0c140c062e0b0406030c090509010e 68
    0x1000c0050030007011507903404000300c1026000007a0006d40c0c9912103030045c13004641e281c0750310300d050008012400b00ea554001a00345280c0d41102c1d401a80141c0101d0b000c2d140000681040e22a40008984000e0700c00780c9681c030318400d028000e01440100080c2000c00d0312881240943c5045081e05102c1d104500c8407640255081030002242d210308402d10b0301c42041d000c2e0f094008025901d400600b0402c40d001050354020b1030340a0705045030034106030755141d11940000d03100d0150008541c9004a48040c002e50590700c41d04c201818881d5902d4034007142035440d9010607411000715071190031000503940300040c07030b004242c10001c03a00d20b00b00d0346004011298070810b042128a204095520780040c00e1801b030107008801301c81e03004c5140d103220100030b0b080c00c1c0c034880b2004810606018148104000280b40c1303800400000075849844031440592840010b00e001c82c005005141c43d0004149034036600400407101256005c10030880c0100c81110038055610070700d075109441c28014011420a200103d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 644157248 1250 644155998 644156003
    0x30313021206040c1a040f030209040221030304030f020f060a021b16080622470105040905030f0a051c051b090102250503030706020306030d050702011407 68
    0x1001d4481402204901d03091003101d085070300130b1a4920801c0405241c00b42c1068050642510504150611401d00c040c9038080c88080d12881003440410300399110361840d89851216030140e03110714041d1524040d9281d209a81c110700003441c400320b030b141da0ba01c041203d100b4103642030068001522000001030207900003205198001c3d0220b00c51441204042040308100020715510310002ca04e413020060030800f0041801c084103035100c201448140100c0350310142c8541c4050424203c11441e0507009080b01c101c003070308010020145d03003103403440c405040005045c00c4241e9162030aa0b00c503418001558440e100041441e801800750014500502c009480c0c3c011081c0f0708a4100a011034003034910003841c4000c0c604640e591018803580311031a00d01d0006410350003031168030742000800001d5403140340681e116448507145224800c0c0d07180c6082203500421008045940380c4246051900095105030341c2c032486442803a20000080d800b88040d1032590b90141c45071400625201c221480e01d52040030704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 644158498 1250 644157248 644157259
    0xe06010804050a02210102161b0515031f06030f0c0252090c0c2111160e1602060f0703020d020a1d0a050a12031e020f12030903031302 59
    0x5240d07070140c07d01c01303010000200c00c841c00d6201c0d80380c204140d6003840780005111070b4111200a1210781c42e0080501030f0f10031107442c0705940341c0c0c4035000408045e580503075044c3c095440d1180042d180b130b0305411012040d45484000c114866603800203999800e51a03c24254910020054400b0f400c0501c0c5000180e4094100c0c8010903403116004280e42010304140034042c81e10140140094451840b0798201e9201d141001000b0f0030301c0b51541031041381d481e1000510200c04007a510310081c0300ea0b000043c0b1039034a070704480c01040c24041000c58002940500d00d40c116080380050442170034100700ca041070102c0d80182006807550b02e940032a040004200e602852740030094211503450360b10041154202c0c65861a00c00c00010425954030810081210f1144034003c0082c02030f42c0e164070065048444040e0b0420041049203802d0781e40c43d201180d0070521082620550002c03540200d0b00d4030508605e202511030340705410f00b03180320b1070200342e0702c41c0f80715802403001602c550440c801501030b042c001000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 644159748 1250 644158498 644158549
    0x220506220501060803070b090304180c03022a011503020f060705190c030308070309050c04020306030705091014010c0302060a110d02190e030f03070b18060405070e06010804050a02 79
    0xd9042c20354600b58081642d540c4002101d100340949408071981205031200130b146050b1503c0101045550411000000740b95034900d00c040b070074066170458003c0f100d00035070880c0506031400b003003009107001124100d2a508120501449079a401500d4054030f074003d250440041e822030500036603401201040b00c281c82001095800011030a00c800d000e640328064140d80c450842c5002422001c0c0980010141402d00e48290002140408c9030b60904c43c080ea40161030380d0350a0001307480c000d01e81d0f00c4250049406814025008400d01e864030607504180e00da98120503200c00111014a01c07001c01a0045e0003040100b4181043c42d040b11aa407458904081d04080d081c116403c100da000c00800d5541c0f100000030001c40580015030001c141c40b003100908840100704240315103d2086460052200d9030980000f000034680070b0350003000c64545411140310745050b241c42c81d0740b58501d0142c0241c081e038500002d209584920702c0144142ea2040240031000965030a1007044a50300310344900031a400318 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 644160998 1250 644159748 644159753
    0x1e090d05070308030415060b09300c090c0319050402030c0603250e0a090b0319030804050613080f070203120c0a020f041122050405070822050622 64
    0x20201c003560040c10581e80d03d042610f020040044030f11640b0b50080e081400400c09030141506840d20580c1c159002d1049503080d1b922403842000150b444107420911040c0d5100c4407c0015260a9107001035403001c0c83c81d100c3c4a508031950208590280c5141c481c440320b00d44c0b5900d41c3c0c0100760040d02c05011100350308606400519030381c2084580503a40060001e1a450107040f40c0c00841c0f4810b100d0420100d104a40e80c00b003021024140114016151140c5401e022a181000102510140c0c3d001440340c41c4c4252500510104e070030354044d1868440d11003c18458640c00c40349550140c2e000f0170003860071072200e4802c03e90360018a02039900d40075200561410260400c000c20300e1008042c041c00c0c40c2d80c1c040c410840d00f600c4401c0014000c80c81c020703d100800102400b1107800c000140950b520700360340010405204021500043c0c1c1043c00c0c1002c1c4280d2941048040b8060100030f0707103841041c00d01500c40b4000015000d8007414684c00721022030010600c505a07401100c0e10003101c540d040502d43c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 644162248 1250 644160998 644161003
    0xe07050d02011b0209180c15030c0c0a0804030309030506010602010b01021b01020c19050103180210080612030f0d1d15060406090525050310030b070c0501050f0103171e090d05 77
    0x201d4103903d03a840486000c6c4107400c004d100c1400c01c107104498894080081c0448803406010051426071080c0700012140b080c031700e00300842000b0b96030080d4401d9603644c403440c0082c0b10888912080311a0701c103000011407098010b0140700d8080106a0003002c12058042e2055601088000c40034150701070300480c0d9110b51203d111002c82c81ca82101440c040c6031508000400300d414032009412140c05900704500180d0300c010094102c100d03240b4000301c0c503440d0300001400c8555a01029002c0f84000500440c160741004003412030141d442c07004000365003032030081c2d04580120500e003e0003a044201444480941004030319000540078100040203a20f8500c0a0101c070001d0f039044c551700784528501e011080240320b08001c40000c3d403802d0303411400c00007245880c0b4085804014058910200014092403052054820140c0c00800a100c00d040c545100444101c00703003c242e628000040490560b85507020440741c070441010091180c0c801c12500900494110032034565012111550035400b25108 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 644163498 1250 644162248 644162251
    0x50a21140a140d050901050405060a020c0306160f08010303270906080307060c090b0a270e1512120f0f07051f050112030c1b06120e07050d02011b0209 66
    0x5070141903811242c010403240792400d01c000580400c6010007031641245d034400f081c2c40032920199100c2d5140d8481e20b4059040441c036024094041c401c41c020814180c074002e121702001c150036102e22145030501175007121058424040a00410310b4420b000c1c000b043d20a07003d07040000b098100f40e04458031410b1003c1030782d00a602101c13442d80f011424005000306480b6009652034503047c52511185450012015405000c0381310050200d2201320b04284a601d61002240d40c103400c011141071610f680344055510710a403141c0343d5110310340b01d502038503050070b0300c007100840c1002009004034030100c030320b8504c558818550004005018480c0d4104041c91034094003d8920660181c0300e1480c0c0401d54401e8140030b00c2c00034a0ba00d05280c010000501d490200711030894142c54031004181d89130601d4104080300200301180032607900c0000622640c4000303a0f4401e9002e0b000c0c14000107412800300f03035540400f80a06584480101c8076480150f0050788c0c4d4600354140d02418040342d13052500040ca40707400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 644164748 1250 644163498 644163503
    0x1d0c03131704170a03090b03070c02130c17040c15050c010501080f06160503010302010e0619030614180601081003120f0f0206070f031802060f090a050a21140a 70
    0x1d0209080c04030466041180c2c1c01d0742d20010041400e01d140b500c0041920751076102d000030f517010000120300c0d450b10034202840c01e03d400bd040014410500304011004000d109901c10024508100b903c40903209003100500458215203058080c1741042281d201c0c40300050981800e0050403c03170965040420300480d4001d102c0303240a003041c4081c00d61014206400181807000c1c50741c00c0f040c010a0241c100054238156a0207280a000403491400442c9062081e00e6402000b03402d40c94001a00a034107422182c1615440d8940503c00c81d0314000348000303241c0301c1c035102244840460000b40e15503c40d08003254480e4180421018481c1c4e6601d6401c1c6c0e05800c0444480003550500c4942142030b003000e00100080e646100030074061030004c00c010900303180e001c00c400400d61114203a001078540d44104035002034000b020181c0d00c80359040d4080c0d207503004070081402808165000691450710683c030074215002061301c8242d400c07174076412401d041060b07a02158032801d034007a101c0d84400200442d149492 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 644165998 1250 644164748 644164793
    0x60a09032a050d120f030f0213080c0406030c0902070f020a0f0614030c0307110c10031a090601050a0f091208030703060e070f03020906190503101d0c0313 68
    0x100007600c24030000568100b6400703000c0c5011003200180d26404540e0844040386400101040d00c9802100585400f104a106050010494144400d40c04032040202d407045000c40740040110001d00080c6c48003440050300982030507208100303401c0301d9001422038034822080c28007800881e0380051304c5130100e40c1100000702e00e55101845065040307200c840d90200040708040c21403420b004100e826100090401c0304001d02d00c4d40349590300320208461111240010040c044170310100c440200142000300d20100f08042c0e4038821302c09410600441409040180d60f10b03842c4c100c10040039613510548243c10320170082c00200c00100010040c003602c00940c0b05840d102c0d960308282c2d0005060b29441d4115201085502e420310a407550481c501540007892410007503103552010300002c2c0e00b03001d040c0350302c26010340100f240c1c034900c0d602400840c403800c0f040c0e00700603101c1d4490011640081020015106015100010580d510760140c09140d2101d00d400007000c0785c0321b0f2595000f0340c3c80480d210001004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 644167248 1250 644165998 644166053
    0x60203181011031f03050304171b01021504030e042306010215011a0f04090204081519020d0b030d0807090501020105041104050c040915050108010b120105060a0903 72
    0x15060254100380407549205010299002140704141d1001600c0701c0f01544200103500003541d50b55041c0303002180c0010a40b62100d9607401d1b080100f52000c21402014065031b90300d0301814112003c1e4448500042e4010304100114114008540700050010f600f405440f074210f41165440303010702c40301c28040c540714070020203003e540025207400c003070041410b54120620a9000c130b800703100b041d8112002c440700d2126284088082d90110701c00c2a50b03d107800c140003d800315502000d80c00520403903020b50304541d02c891004000840003c401d440001808495204d12407040c4030a401401c0b1180e03845900285602c2c581d40040d207444a10710082020403c08001c00080d40c3d0070000041c01014280000c2c0500d240c15628841c05113076013214144229135600200d00201280c0041e03a0107000b402008012001800c0d5a1002c040540d101d000c1c00501c3d00380001c1998902d4805540c1401e8410328003020076400d0604119254011503080700801c0a40c9030000040342e0000064074640540c441c00044a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 644168498 1250 644167248 644167291
    0xa03030f1107052802030307120e03070609061d031006030201080618060d08070219230f01031e02040f08120a201f05070e0301110a08060301020403060203 68
    0x150381c0d07a0302110316044400d10050010400125650601490b503560003c003082c441160001c00d00001134000c0d40510020924104010701420511400c2a8944403210032410b204105651980c45014000000c0c0803068200300c01c9001e1000100300f2051024054204030001c000300b480d044000f029140490740b030300020015540c00c181510b400c20b01c01e9410380f080c90303461041c0c0900507402401650003070365400c070040144601e1a0540b002d03168010020030b044103032080d2101341e2503200d009000d8911038101010300034083d1459501c10004000e020709003120256001076008100c0c0201c2c845030500c1d818600e00007400513200400180840c04101c0c0354042c10641c1c1d04d40350000c0340104080c0b4990812118000f26000178282001010814003451100c0c10542c02c9230420a840700e0f036000788040300d441c2c01461001c50300403a02ca0b8949940d10342008000d83c0406080e6203080e6500da8864000700902261607128040f116072000c80a0009854240d480d40c2d00e078200d85c0119580d85c400120010b04224 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 644169748 1250 644168498 644168501
    0xa0e1b010e0607151d070513020c070e0109110301061e11160603060b040e0c070609061112060906060a032301080c130515121f0e0d0c050709020307020f0a03030f 71
    0x140c0c0b184a5110180b03200040b03105c50f6441c00e02c1d0140c0c074030510400820204854407501210b60f0000310f40d0549a01760364032051208049000c0c02401881c60424500403c041001c40599040300c1d400d503582c20982500344540740420301480c0704181000a01d034806030808030100640191134200d1503a042e0342c1880c0a2004044a2490b001132455075802c002c1004543c1020545640240c2030700601c07a640c04081c50524010204128002d003107904110310241091000000b4114201c848045a601960b44400308140b048040700c2c0242d100b0400c1c054156110710035400000c0390701403920080010142800002101c1030240d10800300c1c1d078482da10b8030a260410011500040f1401d800c1444141403502c0d040140030340f00100c0c180501c41d0751800d5044200c007041015000c015515100b0586000034410401030305a4a085c1036003403103442031a40460b8031801c1e6180304141c1003006011100c1c100103064019510283c52502181b043c070781c09403161a01400303071000c2103101c1e890008040c2d00700c140c0f2a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 644170998 1250 644169748 644169761
    0xb22060515180f0a18050a0614150904140708062d0f0c1602090f04110f0105070f030e06131401030509191e0c0e0a0e1b010e060715 58
    0x82a500043c0b04807503c0c0050420341280010300c0200300d40414000c0110b0240000c42c01404c41d11452483c001804400e6015840281d01c01041002a41d516024012146040100c0c1c0390800840b80010b40881c40021f812042c024201c025201c42070754610b1581d107411002e40340300703004140c0c5903001408103018110121100380c0c000260b0701146444514501072600c014a243c520303a000117039400a44100382c03008044254001c0840701d440c185201078800d00c41040302c0442300000340141c241034500e420b5210310f0407180141c1d9424545105039a60050401441004509108041f0911a482d55a0394050402c9103422800601c655140070b44882011071220445414540b43c8020b0101408d0086500d0780352101c0030b104810020350a00c0e20a190100c1d01107120500b184020807841040702d9041e101d000c80d0742e0300850302060b840d203110325011914021099280c9130f2101c03005071064146100015012001410124100e240c03200218040b07600201c1e080391081c0340700d402045008018880d20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 644172248 1250 644170998 644171029
    0x180303030b1216290d05070e0303091e120a380a05090c1905010801150813081608090103050f01051e03071a0403020a0902070b22060515 60
    0x8000020320211030603c0c0708180c0c01344544070f680c0489000200f8882c5001401d500c8103d0181c1542c81e01d000c50074400504040e05d103080051000348255042d45000001e5079010403004104504040302c640020004d2140c40c00f0541c3c01c2052701c1c001004580080c0503214005001d24110010703409991008850f40315410104107000c0086801e0313152440b040d4210ba648110540c0300007605869821000d4030f002c1035541810703804400ca40f214424180311a12400840e2000c0c0c03211402c4d40d885941c1d0001c680c03c4648031600003507541c00001d00c284106522502c4490240c040300e454503102681030b03c002a08520291100300b4009144e0240d542d140c8242a4040400a2460107550400000510400c00009004045442d80e0254100340c2c0d41844000000d14101141c01b0042d031030003240d4440ad41142c80301707900c40d906150b000528040302d4000c841c00594131981e9140e03d036558a50103c88104c2684d030468000f65001c60300310000e0414030405008003580d07201f20407403400c8081000001600504070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 644173498 1250 644172248 644172253
    0x162307031716060b040917041503050c09010c0c030b0c041d06100e12030304050d09270207060605060c0c030d020f100b01020c1806010806040b011707180303030b12 72
    0x21a401c4020300420b03500070359407020b40402e035904402c0004018210401001c2e0905140d44007080e11606024001c208490030304403443c0c181e080c0100107804540d000c54407102c500030100600e9100c0c2d0300c82c20030310609601c140300c50100f40d612074440d80c808202c00c42d01e141554070009010700c2024000208943c0c0b40f800d00403000345034981400840e10718003481442c50203202110f02c01a21f6035a0b00d142c0014000303400d504a070f0700d900e814201284d44640c3c1e6000380010500d003150100d0102d40c0300b014142c01c0e1191103400e09a8600e1803d440000350f014480a4071102e686d0b02010420780d4031030b402003526520303100041000c0000e0908050811142070046811740d4020169100c00035000f14240c5c11600740c01070001003015250b00140d040c6400f00c00c0d15584540c0c2c0342e00ba8802e43ca5a00b01c2d641c014042a070380d01015030f40c2c4c0000c5c0421151001400390220b448244040b006801c100e4209900c0412850591140c42c400c03048888950201e8004a0100e40c40e0a41d8001d107003080a514580b40d02900c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 644174748 1250 644173498 644173507
    0x1e03180a06020c13020c0d0c020909210304151d070504052e05060f0c01050115140913060603021c090c0509130803070816030c02031623070317 63
    0x78065940e02a80c42c0d001c0c068501c051400ba0404500c0e0305482030180d040341543d05030941000c00801035546441c040b0b00c15200040032480344080090941000264040c0640c1c01d40b0803264201440e8000034070441340000110103d0406c281d41d07029800310400b210104072807012800c4c503844c0c20940250001e9001c1d5280900700006814001000c035142940d5001c200002c82c400c220b202100b4031141c00071608000002042040c40708480b006100520080000300030603600c40c41d02d50b14001d030009026000400d1401c0322903061840100a100c01314000300212403d200303102e001410743e1640c1d4442000719901203402c2e0f0940c1d44d00641549001320aa00c100020401a40c42c068100250f005070ba00070b4909030700146402c04980300050322540c000005940707900e0000700c001d1403400c08644074036064518212403440b440c028001e280400381c0c2900650b0410041b600f2202c03a0000502c0151034100307108150108001d41c486182142c0c0d0500005050120305500307020803040007445418101500c10003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 644175998 1250 644174748 644174759
    0x10b0c03090d03090302041a01020c010c02040608071710200a030b0a03050102041a090307060302030603030d060905070314250909020705010209150a17040221010e01050702010e0a0b091e03180a 85
    0x2f904a00c00c002420815020607050000c034000301003640190099228039440816401d01441002c60840c0410341101e14850407030800303500381ca415071181aa240703001c03150241d0704c4a034180a0319110f05580b5001a15034000e000040403894a07074404d48480e540000c0c103100d07220740a4641480060851900ba240c580a00046030b91511107201d81010135034040085800e42e42c0910464841ca159000184030181d2950910801014240c8101c1c012a181411380c800840b03013041c03000e10810441040d2184100c03900301c105109010342640c0d03010040c0c6080041004552440a00300d2940580001a2200050024805845090300d0344040081d402e01200c5011039201108092041018204030600e407611320115600d08c1d005103003520400c207207c2d5230301d000d901d05510034190581e96070024000e0f80c40301d1505900b00c0d401c0c0718030f80121f41c00c2462414080383c0e25060044d001041607003100c0302016446003d04803061000040506c50f000001d80d00300560503119130307486800b800c88001448501c0c21 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 644177248 1250 644175998 644176003
    0x3060f0501051207090e040809040b090103020105030412030204080f0c0909030c0303011a0d14190e0a0f020d06020a170901060b1206010e040c03061701020c0303010b0c03090d03090302041a0102 85
    0x3c5404003625090640083c0c100342c0f040c41010010300c10341d242100e00b4100351604a56030741007085014003e5241210035182c910f801e4054038100c90301030b10348602c0d644640e15030000003054041c000040c15000c200006140780c080014140072a00e420184c60b201075000d04126030b4810140c03214429501c01c0c40318402580e004000c41e4110f50030f8800040706c00e10803400300113060203100300c5c0c101d0541c40c0c0181c50300c800030842d641c00d200d290020380c0c5a29000040c00a041119041d001e11990380d8007000e81500081d4040c42084480d80c0000e2a000700f0261075030b1031401341d03440f004480300050b009030300e54004129002e04094100003980020f000a03070034040a03101500407100409441102c05022602c06c3c2d010f961034004142c4080c00c2030000840241010380a001309200300c002205542c0101c8007103080620035590820143c4000e5482c40c2d20300801050241c02200420080b40020490001942e47d00200c6c1c0041c18420707110420030b60b14500400c802c6542c0b4000038032040701032080150302c5a070701 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 644178498 1250 644177248 644177257
    0x70306180509120c070515030103060b100509060924040e010617072001050406020322050304140a09051510020303040c26060109090c170c090a0209040c030c03060f050105 75
    0x86200705911800c0420082e45050959449250050719403840347c1e00e0344070904011810b0340d008242c1440b082c0da03103200303010303105131800c1511000034400e116080040c42d100c00100966180248204074002c0010703e1183c00c08103d030780c01e0518410000d003c000001340401580d0042030282465003801c080d080c4504008000204284100820480c0c04580200241307000d6440c60a0800200054500703880c240e0003d41c41039400302c042c2105842c8010580c109035809940312640040558241458041c1540340c0c2c036100814a603100d0f5a594010030324a402e071040d6441248264803800c854113441041c48501c298440400c2e085400800401020030b201c0c01c0080b08492445140055244070040240740e105881a85001c0324085c03a8000641520b981c0c21500140c0e005004000d01c00703035603010740380036542d2620900031a900003018001e660312304003c4265010220000242c034001101c1c0001d022a9403414001c008030b0365840358418000da00d440f82c40040c10520000e800c51300d08010029295024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 644179748 1250 644178498 644178523
    0x20c10060f0b040b2512030b22020d1e02030a0f29060c03071112030309061306090c093305040b040b36070e040c02070806070306180509 60
    0x2075440e070300341c1d0358010707114400c0c00c800388405d07215102d41742c00c54025030302842000c00a401c0141c1c50046103411030b2852035819002d050640703080c4c840c80458010f50401c69103000c45036607444648010b09501003004100429a5400596900e00001c1c02c1c800c0714808481c440700503103803100110f4000d40e40c081060006034010300e80d1007070700345807000206144035800c2800c0c1140404100ca0003040b08500c4421492001143d4580041d01245500d5642e404201c6603810140e004d440816802641071122281c214080d000201e03183d00b0944a4906604065000c2881d40303585d01800d00310042ca40b03844003040c032040b880c601038040321b1200141c55000603000e0745101326502c81c9450b0b455070f51903003d80c80c15203020305045c107041495240901110310300311480058540141412504196012031700b0b104010686500810400040602c030003040003050000940c07158920205015808003d40c5100e00c01e0780c1d0b00801d415042c960074000010044c4600e001c064100004c3c04041003010400405074078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 644180998 1250 644179748 644179769
    0x12160f0e06070f1e0c09050603070509070903050a0c09051003150221010906030b0702010501050a150210050c0315090408040303030b060d0216020117060d0b070e0301020c10060f0b04 80
    0x156505090003291035944009000000c0c2c1d95801d000c80d2070484c0c81c100d0442c02038030b00d0000c40e030703036240b400341a900c0460f0015403641200c8014061868514003181d006905407038a102050703200d03503486180070750030303007042c2c9098071100170400240c1d0960113400e52005400000c48078a0346196034990130b040d0141c113086101c42d00403c0307100306900054a00ca0306603500790303810790040d42d480841000a0406001c16100b00001c1000921380c1d500502074981260b1000d800c000030b0500d41290000d601c45801d49520131409450300c9000b0008083c090305006d5030110b145d01380d0328282420301c82d80140c80103084a0013071a01e4010400800c29002c29101207903094100810712220900c00940e0314480c0c10040d0101d04e10100d03100f00450170350100080e44038403c0e280c00703803140001c49140648040c103c1d1101d600015900820f0000351010b0309890b00040a810020244401300300001d0030398211040c1010300e94042561001c074011940291402045601b00003502c45042014a070300038841c0d4000c2c680c101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 644182248 1250 644180998 644181007
    0x50a080a12110a0c0e04020f010908060106140906030403081005010c03120e0118050106181a040e070f0b1207050301050a030807080706050a021909080a03110705030312160f0e06 78
    0x101041c0f284603e0320742e001068000060311115002c01c001402e48003a40110a41c0011f00129405070140c18103880101000b00313010b03031810400b107540820103403500c41c10050178443c0110351348444003c2c500480c1f0a17143c4940e940761504149001003010b83c41036040100d00c1c1d1140380071980142d0444280710741500040380c40504c80b00d502d400340c880041414924040251218103214040d444841600c4400200000e0030034030314419010f940c0f40c00f02080c4c0710150b1196280c01307171038180c0c0304421952050701030b540c0c02961842d07268500400c6a00460054a00085914a00ca0760402e85030740413006003012400e65062030049000000c0786e000045c1a0301c00052818144044003090741c00300c5500000510842c50b0015000c4e0280d0850303031101e90912280c0b03107519000c0e0f0140300010706444501006001c0304404d43c804544030091458410402e001728034011170252801d00003420700b011726000b40030341c5003810000c580f1441f0303074042500100804401d407851000e41c424440001010110740c41c07030703c2c3c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 644183498 1250 644182248 644182277
    0xf2e0504060f0c021c0e31050604020f03070c03030603080a020708151b0309030c0304061d030a080d1a030d05070c0e07140307020f072c04020603040b070c080c07050a080a12 76
    0x325640f0520b50120b100c1c0c0d01c07401220032070500201c080d46e885247c4062086464840912003603004a6600c06001001800054815889452110009402860003080c0c05540e91200702040c0d002003081c00040c0c00460f810310400c20f00b084006981d81d8a501d5401c5146800410031440c4c800c88460803d20350000400318100035002c0080e02d02c08c003112800d807550b0380e69a050103403c1e0a4140c0d242620190501201c8078145004240c8a103a1a00518020300c2c11140c0021280208601d030b1940b01029035421100406440070068010300b8490340d01d40740d0b500c080d58282409000020323400805110701100422500d80d601001c1644603c8481000e50b45944681d1003d03410076072100c1445040703218520000806032a141c1e5400c14186a404044041001c0c810351642c15560868000e90410010800310f800100c9400c18107500c4031302864044101c4040e5520712000e80e111540d04510307944407500a000074600003002034000c180070001040c074078030070f6610718039009000788506042c0305008050400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 644184748 1250 644183498 644183509
    0x3010e0105060913020a031b020109030212030a090f08070c0e160c1505090703030914010c0f05070f090b041d0d0315050a06020a140f2e0504060f0c021c0e 68
    0x100184c0710400e41d01c801d500c0000a0007001070511707210400c4150411140e030365006114240c40c40303800d507025084074400d01c500000b183c1d0010300030441687d9242041400b00707111001e45403c0c240701d00c03142943d500c0301c0d08100d4840000e0381c0180c1d030101070400c28070000280200210001031041c1c20300c142c40000f9400c107100b00c01a03d102c440d40d281e09200410484503000701e25030b8192403003070f201c40b442142c9401101f00090701c88075510340810090400740c40400c403141d032000c42d01403040f011168080d455045c420643c40c2c040c3e0058030300d0b1707464080c50300c000d10f0140a480c407000850240108114400100241d8078a410804001807643c0d88104503419041058400301401014020103074007035991034025a10541c0c500b0958030f148600511a400c14404103d000e039845549000f091400d070f00e8420007101d042424a400400c000342d5030a124000440d0184c20300c5140078850008503083d0303500950040d40c4411341e200085402100c00707100c036002802503100c6001300910b000900035009601051703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 644185998 1250 644184748 644184769
    0x2010507171905041202010528020a050f030a0e0f0d0204021603030501080a0203030708030705120a0c1211030a1505090a02070c060507030903030e131d1203010e01050609 75
    0x1045801c5001c00c11901c401110020504005202604850b104000408994078000c13401441c1015540d44818409980700c1c10207441c0300349004885a00e110320700702d04903030003c102c16045005604000352035410700c1400d12114921100c03a001640c908200c908000b0581c4808000741403045280410603075050701d9549a04a00b0782e40600115628403003e481500002591201200004d0518001043c004404a84150141da01900441c03c3c00c03019914122a600004d00b084d04110050210170158960030091a0048481010010354141c80103002050884c090300c20780f001500303009000001c07134500c80489910804072070000403102480c0c1010780e4a102c003980402e034401303140b00512614041d158003c080c0d45101e250980540e698400701034a8602900e00d02901140e49035000308007003070041c0c0903001042001449103d6a121803074000003103034621b20f90f45c2c0c030301c600044508004007410880740700c070307900c182004234250342c505040c945428805014007805186e01280c00d800380d486050500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 644187248 1250 644185998 644186003
    0xc0a0f0c05060703061a0405030706140c010c120e010b0904060b1903060527062205060f0f0702010603150b060906030a020703030515090711162607120b0402010507 72
    0x1030b415400c08000080280c02c1c0d500841d942c5c04151246100c0c20143c2a045808445c0c0240c00b400800d45089016201424480d11421104400b040081c9290f8400e1040074468103590f11560b041008098140c0704844c0c0085038240540e2400a4140c0f003941d0315110558802d50202c80410040e900300045041d01c80600301d420892416424007208100d0709030803103489204503245083c03d03060701c04400d61100f1007010445000e034201802040360412000900003013240c8500f00c2c1203903401a907440618040c8100e4182c0c641070080300c24000221840c880641d01f080f0144000d00c482e6003551100c025240c9407141458101d80d48444c2a405500c031041a603c1008008108039140d140904003d00a9804400200c000a1074030002405000f5099080b522a4402403c2c020340c0d641c42c0d0000b507901d02c14403120841c05118628980b0100841e1820302401f034001c007040c40d01060319802c11071002c03040e443c0c880e41ca95007012209004450441c141d407418a03802626404407a256800140c616100300a0003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 644188498 1250 644187248 644187253
    0x60f060a090213171c0c050a0b040602030601120b131a0607031d03030a09050607060b19060201060b212d0402101106010b071a0f04050f060c0a0f0c05 66
    0x1da00302940300107a070004882d60001110780e8008134038003c075190440c084035602020200c84c0c400e041a449091801da00c103118200700c0301c540e022511010784906040301d003100c001d6000810401c56507404030302c1062840a403a4144440c8a102000079001c40001c40105c15841e50360000806545d886c505807030251030003030449aa43e04103414010854805290720048201690854400d2428004111085050705075214103d0a060008214255115a0040e618180c45100c01412580d402c05417040440d014566840c501e0b103886000703800d5070b20550003440b5041040c09401c0e20548c250f1490b0540b540084c064003d00d541c0c501c1441d0b21020300ea214003004031800e540e1241c007050040d880c20b00a6008490b80078030980c50341400c943d0032402c409641c1c500d800130701c01000310985441c090a0344900c2603c40b00500720402c44c852029110440700c08240e40031500611092102c184004402c181342e01c409000c0342d2614149550a40c41040300c0d1500304080340e1800c030001071240c041b0307500c4158810709 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 644189748 1250 644188498 644188507
    0x501060c03181401050a030b03010606050408210d1805161706091b13050a0501061407050d14270a0f030201170711100509060a0c02060f060a0902 64
    0x14014100000c24404030007145412510840d40c070782041c851422a0000b0071102a000e00460044500d608040f07441c01c2896201c80141010355420700646015041d1947c5540d161450014540e2a0400d09140703210354400300c01000c1d0744180c0f0a400c40726920015080402c0d050091035010102c01c40d46c1101403c00c0c007070b800d00510440390400f130400131030b201503000140501c4546160340d00c404064402091a40c004c148460841c0c1210310340c5554503030018403203c84a84141094410b070365040b22550b01041d07503200117100c400d030061340f0480c0c100740141800d070401c203096a44691300e040c400c202d03100340709060402c19003206144085541c0103401040000c01c4080400400c04443c10003045c15102e50441304001c188954842d29440460b90140d443c882c944100d000301c19007115014002c10204512a0110400150104080c402004440100140700e03d8030803507075410b29101a0941008a0800c0d00e1210010b030f00041442d00401540140c8820b61200d00000d0803440b520b42c01042c0c580c0c008035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 644190998 1250 644189748 644189759
    0x90201090605120621060a1b03060b0a110c04020d02071b0315020d020405060a020d0201060b09030d110115150201052d09100c091a0406230d110301140d052107060501 73
    0x42103041d140344100c5080d01064050f523025820355019001e44000c02d2000d2042c440094420755100210320000740a80360f8400c11200454166070024400038082c40d000540803080194806c0d20200318056066203e180d2404c40e603c1e8684cd010811118a407a5004155440a042c1c103074115001400010061a075591007a20040d4480191841400255203811000150301602c0c0c000c45201400090140c8450300c1419810390b09040b80e640030360019941c95120172080765010b803220001e807032541520070f01c4900c20a402802d4402c020400088060300c2140075494508002441c0b03a100c02c4180c00c8044c558461451900c0e1400c0c810038603039600d0a0226607285680c010071040d00740c906a01c151a030074142c03020b0040703480c400c0d8070031040051002003c41d13010304400b101d10b008920990640c20301c2c0110b84404042510f5080c48a01d00325440000100955a404504c8170038401064500f0800450241c64454545c81d48101200f645581c82030289502c1c1d500701d044415456115170100290758686 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 644192248 1250 644190998 644191001
    0x603030a0c03090905040c0311040608060a0c03061703341e061b0908030705070e07090f080705040c020a05060a0c0309210206060102032d0c010f090201090605120621060a 75
    0x5120544032020643c9c850040e40c01c042c01440161920350780140015100c2c0241980207007490046441015680c40001c1120031140901d800101c003158001e58840a00b8141c1d0340c8140340007501c07101c0da050904100c8804514070f45040318016041800f201041e08558119800c15020780c600400e40d502d00301e00104030035400c0c03410109078409541d03100c01007516900c0c4d036940c034492520301070300d01d601100c401c00c0002448007603994859410b00e028002c00f940c0c0c500010714442c0a410410145c0c100040611050401c0d200c0c81550b20950320042c036201c94603803102901c0d9503011304040c610b075448005514031507007e6044814802da01580c8500301c1104120700008012181d042e80006000d6400860000d40c8008141c0c0d90030420301c4414100002c10354801d40700c075900c00c0510511060240160050480c082c8500200611680000300d01c108907403000504001c40b6400c444107201003404030010ba07014220400703501420554030142200700c0d855420320050503502d00c800041c4180c004001815a16 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 644193498 1250 644192248 644192273
    0x50a060602010c0e0a0909061d0102030a110405011d01021e060109050106111506190e07080603031c0b060f0403050d09050f010f32071a0603030a0c0309090504 70
    0xe80d00810810105210072500c940d460783d4419803040403064140a00e00c01c03540452601c9110f02000121401c0590a40c502a401c04680744101d960200c100000b54245005200d40c01074000360352441c050402d40042e001e4034104106095200003050b04185a90007084012410300000f50b500c3300f11307516540c12941d50700d0f0074092034005c5814a4000584e40f8010a03003e03a00500d07140c058050811646904880c054000f4070b6907600c5107103c1d000098400b4910074030800741a010310741862a16011201403e034603005462103000e41d03c00c0100030441d4407034000c2e000d110a4241d82c08500c4008250004510340102b2005d00d813031400c0050000700f088000140c81c0c0300441c0b651103000b9000e42d64000c00000300d01c1d081180e401311703034040e0706078055511440180d4500030a609803007420601d4401c946500e5020110b10708603000c4000399900510911406404403c0b0013103140e00070502d4404040382c5c481c004d1520303600034407103004100020540245811005402e581c0002c0100749010305141914481 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 644194748 1250 644193498 644193509
    0x1081608070c021f11010203040201020c060a090b03010e040302191e05070e07050405130b0d0b07050d090302010e1e1e120a08010f050913110a031e060e0a0c05090415050a06 76
    0x240c510b02c2401c0f1510600230f032446160143c01500e00e00c1210b0041c032000740d01c040200000c01242c090301041c04080103019501812034540c21010320710b03142c50068a000c0a140c40850344c11031102100c00040e1045040401480c7d808080c010116020f00d001440c20070a50000900d071210441000b004991040140007140c40841c0d0500c038122181c07020004944e04480c1060b086104c0c58041008184000c2c0c21a41011451070440d15004005458800b250ba104c4007c0380103035160b40400218000c10803d000d001210550f030100c4002440c00001d550305216a00049080400c0445200c1903200340246c52103403104d20440caa8540c81c4610040c6404001d00500c217080b1010000443c1c40d0520760250b6114070700d18200f146111200e600c446503181009418982e100490090100002d03200d955101002c0084503406042403802d442c058041d5264a01c007d030b165400800d00002160101c0780f14411036400ba0303488102c035150f5082c03c071000d040500e0040b01c40c50804e824003064000c0f50b40150304890 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 644195998 1250 644194748 644194757
    0x210a050411190608060f04150e15030304052b0b010612022104020a15020105040204060503010b01080a24080f0d081603020c01020c060c0c0c01081608070c021f 70
    0x421080c200700a508071400349000700c07034240d0002d110f82801282d009400c000018100301c0c84040030000241918000c1d903070396010380e06201c810810100d2030300100e904210311010b191b075a030f088040801d43d05c1c0614840c06104c1c0c000c0451821407505401c000300248a0500c079002850a01030600c540000700070320a0200103080010440c21a640c01d1003501c456081c9203881a18200c102c100d42c83e4911000350040e80e115559480024107400d41c6034022044000d15000072800745003500401c0308842c0701ea40518060390400ca884100c5a92260b50a648410002c000181003042d80001c0007a04403c0709401d5003401166002182d4401c0001700301c0b1549845a04841c11340c00441800c4030403038003d03122111106405007005441c00c3c066000340c440201a80d000605200703241c7d101924042094686001141d00020541c800c0e884c00c7c00340000001c03080c00c1080c203d041c411126512030022260650070404400041250705102e41c00090007560001c28440d80072056064184c4401030000140001c00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 644197248 1250 644195998 644196023
    0x90908070c05040203070e1014180306130b04020d080d050c03060301151a090303071b0f08010203010f03080334020c0d1e051f1a03190206210a0504 65
    0x80c5014005c60380719800c56960740403141c9013130701406107080c03101c01d00600707100110b01c802241d41300c040301a02c90004090820041805c0e24010325003002c00282422045c16030f050001c801182c803d0f070020390403640c140d90314a42601d103414140c8003402038455044070702d414001404004030405002d54080c201c00c800803c40072585c0080d0108611700340c0b04240e01d071440420048060003144026124448014007541c0c644071b0ba035601c84090840e5415500030350040020140000700242c4180405008250001c5240d9410885001d543c3c8004d0321000f8929a00040000c40300c4044054506000031401c410402d0f040c6107008003414110602004001072181c1030f120b4400c0d250108540e00c0c0745800011600e8030040034001c100702101c600c034060b900c520405160030012802c3c416590344880180340005a4a121021305010618142c02c0c1c5174800c0e40400515a40c1190026500c0d0985a040314980e80d5860822002d0700d001c1088649540f10841d030804024042c0e0a98001c203209234484c40104110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 644198498 1250 644197248 644197259
    0x40305030a031a030d0f020c04182312130914010603150f0320090c04030506100510181511010c14070305071a010602011401170a1506090908070c 64
    0x300d6862003035410b500c4000701e0f01c41d150103212544045c1940b0f20660300c0c2d0407101c1c23021500391800d801000c603200008200780c1c01030154612840203040c05d08141c2e01c80c40c0704031203200b59540100c400d00c4101441c001561010800900d60070303100810100c0014480c14461401240c548203003440344001090900c9c2640002d61080d0740301d10165041e80ca0303808005802c581780c0b64100c2c44402d0390580301c0c540c8012480840d41c0c0310138180d4424101c40d010640c1d21800c5252503814020094600a0f85a003d4041440700e50341d41c6405000016052404050761041450b1080001b038103640b00d15009031594400100180e80502150b0076940d88100900248034460000c984a5003130486c500e02c0024240032400c0024450401041458040c41d11555102c948400c0380c02c64180a0b80020003507951358441070940c1c9100c48150380107000a620a00000e808030018a4581080200c01403c600001044032a903050b41e501203409001050810000040a0300d0b221a0301e51200324107644819002400090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 644199748 1250 644198498 644198531
    0x6010809190b060a0f150e0f15030a06090e031e031627090c020f06040c05120f030d1d031c0b0d0203010c08070e030606180c0708040305030a03 63
    0x20901440c60540e03003548035501d524400c0e10000e00f4142d030040d1030300c000003480e03403440840001074021382d00c429100c00d2801a01814449103400c1c054002e9050000b240001d5440324075035580c032001c10882c0c03590b0f580c0d0360074010001c02081d0005a1203d10309600c9002c0350344000042c10714a00101040c606582100000e240b0602044507860440d10801103c20742e4107200d00e4504c1c0d080034500448a968001c0310b02220300d2521180c204511003960b5903641603007141d040099082c0103448c000502028101525000d10202c00340c02944d00902c1c0f01c0b50b00d088058030821402c40d02c4000e8000b03680e03c90b00e02c0c030f0700100038010a003000004d20b03204a50300011400d01004540ca901000041c0c5220a80b05141035000344c10103005190740104c4030100c4001584081c066103038250300360b554603003580c40c1401000d4a88800e011850703019500c05010402a92542103075a50340c1001c0c0c54150303a107030341c1d101e588658070b200b5010010000d21000c00d0010801000101800d41d00c100307a1414048100d402c803080c007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 644200998 1250 644199748 644199763
    0x50108040506070c050f06010e0406060b0c1e0304231018061409030a240908030c070c05100c030318050307060b0109050d050a0210020114010306110403060f0506010809 74
    0x1c049402031008a00914000e88881d14214820000d5510300c0410145050514109900510f6048111070410003001001c2c800c850142480c60b036094100040c24002c4c560b10400303c040702d044e081c4810480e0f54880f6081054500829220302d40c03030070400500b04007000c403040300c0305041d000321100308503144286d01452b514040c007240e401d90b2141c4245070030007c6607188904610030100e03050403ca045c00c00d450611032141c2c5180103072a9403113b51031524502d0000d0210f030388001481c914146c0d03403400080308401125000728031400580d49a489504150b82c0745030b0a0b034415a4044015045410b0841e00104148a09802502d041060340406074610349590240800140031b5003040040f000050160703480101d40c060189043d01446403200040303605a0541c04043d512940714a1120003103180c03d400c0715040046510080c0f00300c0284c401307408140d4106010003011961900b075001c07030541e00f4800f524001e6400c031a05210f00c850541002004050903210305000a80c1e400025008410024089 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 644202248 1250 644200998 644201003
    0x5040504020a1e23030703020f04080a0210030c02030714010f0501030516080a11101101150905060406030b010e04081903020c150f071b060608010c12050108030a0807030b030a120905010804 83
    0x1141380309181d046030000744d40000c08071014154207003c909554640880544041c04850f4002c107000c040341d0040041d100d120b8400d100030141000c045190259002c800c2e20017041e44403201401030200782078028058200c03500c0c84e180140c80c04000105000e00001c1c1402030031603080036010200d48501c3c1d855101c65032060050100b500c103861070925403c0c0400b0b404a5042c0d2898100c072000000080f6500f980e0f08190001024013030494148034105161040ca07412250403078042007401d107941c1e0b49802201e030500c03450300d01501030340008060024600440b204810400200035180703c0b8484080c0c000d402c800d0440345980300300d82900c00414680a0b9950141868075003a44059803455400c4858480f8251000300041c0415643c1c07001525600508000c0d041070000852104465070740101600383e59074407482680d050030010004a000882180c50525492400b91400e50369050198045c1c400d0001003509842000c0b205020f00c00f495010800c0800c696480e0004556648011a4031200c10b0350f01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 644203498 1250 644202248 644202287
    0x41b110307032321180102130b0a021011030415421d070810051c290106020c03070521100b010e01051c0c05040504020a1e 54
    0x819010041c800c140c10741d140d1464800a240c001500c1501d01c0f8051319540e480c00100d5842c0610400c500409a44d403c00100e0704002c50800705c08440254121f4420300c58404004400580058900c1c800e0020031031282145409010542400105009507401240d050b502034501044680806050340201c0070749040c1c01d00501c060340087c4110b0340019030707100840c00109200c1451401d40701001c01400c40100300302c107520301d00b1503102c5607401c1001c00d0040803032041000d0207040100443c501149102526001d81c1c400c07030150303c110001c541041ca9440040e00f80c00b900382e2440355485c090f191215442c051405842c18a0740d0b290010303a550354031031041c0c0f6415001131809101904100480680c420003040d4041000d10103843c6550401d202c034065803901ca41c03262050386e040d5030040207038420135400380303440d0345024410524214400d04d44084070034100d40326011030b14060300c5a029107002d401300400841d91413004c10806041180c5540b180e0048064059078240320501890700358074102c80007102c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 644204748 1250 644203498 644203517
    0x30a120f23180a051809010506010c0201140a03061a0c010606051c020c0309040c020604060b1804060e010e030c03040602010b090408091003020f04090507021005090d0309080702041b11030703 84
    0xd410541c1c1c071a102c002c030742001d0921000106641c5000c2810b103052a058000e0340c20b420b280d28001d0a450780100a82e0501406204c2c10b80182d0b400003150440c45117841b0f00b60f80312494281c0480140c4002e50009151203810807110103e0403400005140d010b2820000b004165910401510f007800b91514090314422000b51601d10882e954006041e070b13246030800d0341c0c90403100100140c111406100c00c0001039200504000803c0001d102e81201c1490444000c0900c000c5410314a8007110300401c0204a9611210441c601d03c100b50000104c00098805032600c608004069560341c1d0014400e18006600307001c41d0328041d04001041ca80110b403c41542443d00e01c0712000c1c0194090021122420180d080000d103000304521009440500b80c0c2e6500400c0d641070504000745031000a2020743d890302d140c80c051060803c00000c0f03140e1100d00a007000703d190000d5060018040c040e6800c080d40140c01c000003007601c8c00d0300700103c0030003108039100c242c25104207044607542c9000d240c10080c0860413403c1c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 644205998 1250 644204748 644204767
    0x130609050c2d0f070804030203070b09191410110f06072a1407030602030a020301090b011d10140c01020301080115060207030f020a080f0a02091e04020906030a120f23 73
    0x20014401c003030080030546d18040d0b80f5400b00c0d05d812050303030020004000104410005251002c0d40d0841c1d13010074044070810a0034410320204211280880a114100030034072041e015018524510360103a0b800e00303071041c15801d00c00c2240ca440c000c946800015041c05503061005520341c0e00028040000091602042e40d99541c0100b200300440500c28244500c400001c0000d01e24001103110700400000540c595240c114070406a074214218141846215455041340c0c0d4541c02c1031002c1c81c03200720b45021444c0c0007240e09803482c1c0d40d800c62003205190006070030103a440c0150010350480300c005d0020000c03103e5019502c072111211303000e0720340140c1000408001082c00c09000b84071240c0014001803850343d561000f00c2c50545010340c0c00c0140c0c1c000b00e440e0703425072400a6403154001064541841c04481d12241c04041e81801000244113403000070200d0f20b00d44042001502a03a400800e11341c80c007140c210f01070304c2104a07201f0040002c004403501c0e90a1703182c0304221940e0f00e88020b0480c0c20310f107007034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 644207248 1250 644205998 644206027
    0x30f060b090d050316060c020d0801030b13021f03060807080c0303191e0c0209011a0d0e0316030c0c121a0402010c0512130f05010509130609050c2d 65
    0x1e00b06650902c01802901801c240d8219804004c07403068000003500482c0c0172010f8201004003140301c007400b09010041011900440406d54807092008102d012031402d8070000f009500a42811a0712000d111052100260194800d106884403182101c01b0a5034810801d9601c02d400d40403c0d8068200f03011f2140c0c07801e0f8010141c044212030b814803982e580100034181242007240801c2e440001ca40c600d110b029402c000a61901404000a041c850a20410214030441c842d01e1424200d0543d03490948149002c01d109648800100700701103010b903041800e00a214640c10300060703441206280d40003031062440413419130b416900070389008200c5502c4503141c0702c42c1d0b4014000d0b81400603040c0e840000507014461000b510000d41c60a54640d0b02d081c03541403a510310358000c0b4600341d1400320f0501282c2e801c030301980c060b0441103410100004629640c10080d00f000d6101e41d134594101400c0c0b024a04c1000c0140c40f84484852110402c101c290041507034503040990340c850702500412502c0c0300321a05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 644208498 1250 644207248 644207269
    0x5030f1507090308031e060405091b191d0a0905060a09110307061206062307080c061e151807051213020301230a1a040e0d030f060b09 59
    0x1e5007000001503070360340c0f42c0c0b00e00c81d0700c00c035200082004600075030303140ca80c810110a500240155010002031802400c05941c501420446001c00d802090364010641d6601d124500ba22081c081007100703903a640d9568040a001a000c2d058511100034001050751f401841a2a4000d03001402801643c40f06c2d048c1c07200401400809944489d42202001d00303d490810000000741299a20482c5916000c08502c0407a001508420100300380c40000038942e100d0191010b045201000c610781c6d880d02203160090341485001c0e0141d8080c01020200408001d00658500003140c400800100580e81e4a044d1301100109840c4a5405040074001040307290014a03c0c41d400b2445041c15460121810104900102c0c22284c207034400a0300c00d485c20840c1001c2c09800c03e6200300400b060300c01a401e62404610302d40c01000054065914542c8415010170b9041c0d01c21030302e101800400c07400019420301340d102c10072400084042428200502200071a41c03203480c1c2190038150980d030908185008100202c001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 644209748 1250 644208498 644208511
    0x30d02060c120a060e090a12020c03100513021906091a0d0e0c030307140d031b0c02031018170319021605010608030301080d03050708180a080a030605090105030f15 72
    0x13039601d80031070000d102c081e17414020740210006100e00705503454610443e1405849450440d000020082c0e4180c500203081c4203840007c1c0070124096845056090700703003192075001f03035010703001d0001142c9010309020a202a10780e15960100b1081d01d03400107144542c00c41e000044a860100300103094880c0d668018400f0b644080c00703440880820342c000903d141c105a000f95054502590b01111500040002c40c180c04041e0606014044101840d00800c0012801c80c03810f0081c26001c0604540d001e1007a00304822003220201301644041c104400101c4050404031082c010450129560381100303001d03280700b49400600b041c500101241000f000e900003ea83e070041c000810151000640c0030b001742c40180036400c1c0259100e6143c8a0039070301d0802c1c042d0518085c07500e00760500902e65440000154804104107a110040004640e4246450b096002c06807822501040145005601d60006400c41d6001c13102c60302d440c0d80751010140c0746d102520042c481544074004002c810212501803179031145 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 644210998 1250 644209748 644209751
    0x9050f03010f1b021e030307110c0301060914061905151308010b150903070303142101060e0a05090a05040213020c031306180e09120c0c030d02060c120a 67
    0xb400900c2c040607036000c0c03000d01c038602c2c01106040b8552030381000151101011007003105551803170022020703120300c00504408200002810720a0050b001041983d08a902c060b000700095035441b00c8600c000c000721400515901005004a0041d190440410f0a00903440d4100e1034042d18160810034084030240070200c0d526028442d44464440642004006081a6002059211220040100003809040038420460342480040c150742c8002440c07105503541340c10102003407112780c00380b8140c5025032188801d50b0030781d0340d03d200e8001d02c413450034904803181502c2c1d9000c00b9281c44200a000c0f10180105508400c014000620124040d045141c21900162001c0500e40342c035031001c0c06a0b408080d52541139440001e10742c0310b20b40070508610080900345040482003c2c0b8108100034002107210b9036012954001c080b81c00e10300d0510603c3c882f80c60107240340341c3d245815004103441d2540348070007a10034010340420000143c00400c1e030320700c20790504280d145408400300c1304101d5400081c01c40c0c244903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 644212248 1250 644210998 644211011
    0xf0e0a03051902030c0a03080703210207061d01020a120902011404090618020901020c010c051006030c1a0a05040605070809090c19020d0c0201121b18090c09050f0301 73
    0x1601c1805060a40301c1d0844180c66441c8442c018507207807421a0380c4507802400c445004001140c68001035401c4d50742d140c905045060704e10056046031400000c59400c005100250030ba040200c503902c0103c1203010000b80881123443c400b0010300700d0040851081c0414101101c24105040076482611194814101b400c42000321703101d020340d07a4003d9003148043c1030b82c503c02409065035444213080d02050001c030951800c00c40c00300007511202084411030602c09841d071490700b0424140308000440302070600804c041992402c010203d07060900c180450844180342c07181c0b60700c072540105d13003900e00151500e61400385800301c02c0720207511204064a400a050042400e56940c1000070f50040ca000115540c5804c1070b08054040328240a1b03400b070035541301c070480c039210540143e1041c1f038144d02401e240207410400f076034110190040c2001b010b03e20000d001c0340310100760022100308562080352000d803501c688981145040f20400642c1c00c01103051070b541000f4514100303c4035008004040d0020850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 644213498 1250 644212248 644212253
    0xe040f0c03050d03060f0b04051e03060a0906150609120606031a070f03051b0c01020d050f04030206090a050303040b0403021e0c19050d080a0c17030f15010f0e0a03 72
    0x11440c160304111482d4222a0790005219454041c2c03001074400c1000604400d4684007900200744150720440d401001e400150f03c81c8000101488240704c4000740070740f5860714010340e0040080041c000c0840d402031414204281249110070880251851a00c546030040e06180d988011440c000c2401c41d40300d0f40f81d54000c800a008540b11100700b01c0079044046c510700b01140013034551045204a041010700c0d000030010740e106d00f4611051101d4111604030f544600040c01e2034068402d840751640841d08000034040c600d080b85010501c510700990039100a600c2e0030700c0e1680c484035502e4000e0003aa00500111b0045600c0c3c070a4075411603c2401262440200741041c19401e08403c0c0d03c0c01c0e441e40001d601c211182c1403003681c480304140400003021410782080001020202e10110181c214200400c00349005070080000d2526942c21440610300313540600002c03015940102c440300325600c444408034448440f000c00344014000161110102d15280c0c42084071000e59041d506075100180e281700001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 644214748 1250 644213498 644213513
    0x140106060e1035010317180103020309030c031c181a1008150412020111070f0602090616050705040e060f101502060f0108161a090a08010906050a020307090e040f 71
    0x64484480e0300300c02844d859810604800b0791200c0c000c15900c4010840d12984582c00032400d903991009003401038594850a400303034918010708600c41d9580c440050022401144d4611112254011110901c0203000e4160000c1e114078a500b0f004001c106400c14820150b01001d0020340d004581c2c41851141d9980c1e050024070304104500d41c60300031400c030703000d100034408040840440ca40450000380a08100d036029120548101080a00190f01c2d40031148204040342c0c04998110304c00903e00d9446070808410321018031054602190a4855944002140e04140c042c3c42c480881617070160006d0380d20403a0080c1c0019000b04280d030b00c44d2421401059030790741c0c814100185200c59008005030300d444000741c0c1d54804181c1041324240d02407840982000890b40305403050b140c002c4150000c500321f203c1c3d0040140201005141d0104d2106404100d100c415030048182030b014180911480d214a003400040784420b503510700006011074001c1c0140d100e004c08568009104200c404411441a02c8407070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 644215998 1250 644214748 644214827
    0x91a12130302010506100c02221e15210f080c030c070f053010140a1109040902030c1804020a0f050303040303030e03090409140106060e10 61
    0x500e59880316450600345542441001e034441401c1c0c43d60f142511142c0d2006d40b8100d0759200c0241306102d014203400c2062481d4001250040c4581d405120030403e0020b120440c805005040940e0b500d0141254507407040c0010482c100c41280e0107a03c010124130002c4090b99206400a880b031011034901c00c4c0000b134151008000304054030b4095900d504207080a41d08251460740844414003030641c05224540d5903603140d84503061a8000850b801d0700005c8615452100c884103c43c0038000c203440204140586d030800000405410985401543d4183c031540840c1d0120700b1200d003814050248001505095202e803500500040444240f2081140002c1d24040f03201c0b80c500180344070034140b004500308800c041028019800c1c10200741410710000c41d541b409980b00146c20141c8800001c0050a030610131902c0606002c4c00074450300d001c5082582034500074407002541503107400000903005120fa10b02130300d0b8139001000d056207200d4094049540c404002c08828005e11840d44001f0040491900d00b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 644217248 1250 644215998 644216011
    0x5090102191104110c070509090a0f08030a0c030c080117010905031602040e06091002090d0807031e020102090a1206150e0109050c0f0a181d0f0c070201091a12 70
    0x1e0340e680c0b5041040c00309a4042008112011030244180e001d00c8038082840004c0c1d900031740d13001d016641e8540b00c09280c8081ea40b40079006800b504c120340d080c080000c004500c5080486e000748083d500b10f01d0203e0480391142c00d9100010718410052140455031040c43c180b403020301c0004141c03c4580c3d214281191700c40d241c0514101e6100c8140c00c2141098020412048445005810540303086580d06495000e030110054501d0740c001480d40d140c0d510404032107a1950040030790340e1103001d14a07010b054450020007580c42c40c0c0b00000078a01480c414000c981505101030030803518146010244000f07941c441070216141520b80e51070840c10403080110030000c0c18144540303042540350072161400c690340030f001c0020280041060010120205c822201d00303801e0b40c500810810694403480044580d1500071149000c3e210310000283c051001d40b1600034040504000c2c03181d158101403005907c40c110000380402d844410800030b1360803207001401c0016880c14030318903007805034031468400b030411601e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 644218498 1250 644217248 644217263
    0x3190c0c050612040609170f03040203060108011107030302070c09090c0303080903040b0708090d0b070504080c0906180a091e030824060a0c0f0b07020609070b09010509010219 77
    0x222000e0202010050004250503140e0300c1c9040c99084100051010080000e03000e00c0d1030f5010b08003004124100030014556941d10241c4a045014101c030180d4000c1e41d042e0310034030444002103000c4006106104180d030b40540c4052510b006550290080c1d00040c205545111901000040004083c003071002918030404040b9501420741c58007414001014240420590080c4024001c480c1030304101c888250b00701c82c88a445410a500140c002c0c0118180100078081503801c0c466000d4010303020300305490395201928030402001040c445c00c428110f8500344d0055040f00c045a0820814102c50703001441106d001c131310351906803a000441c510300c150030700040003005d601005069100070025044803541c51350081c8102c14640200d032a40d000e0780050300c100c00000e4060031070342c0107203403201e165580030510760445145404d007482159000ca0381309000d4040c880008220450106800098504104505e41012120f000446142e08150442410b5200d05031041d90408802c884240500c1d00c42c008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 644219748 1250 644218498 644218517
    0x70c0f021504051f050403030c020f040f050907051807082d15011d060307031508010b0f090c0a3b03010608010b060409091a010603051e071704050319 66
    0x51082c5684d0541c0c40d0291030420703401c882d03a110b511004540c210303a050705e482d050100d0300d0b000140351760b258503080d41c1e4440d11b0205449095070254005038403803401706040c4c88182360b550042c0603504201240f020f00340065000020181c07070203814040d03000004059000d0324006c2a0a1100c0d8420203804109075888040c010271120282980e004200b5210030719000c4601d01340c001e44031043c0d1610741c034620b00c079000220000b02c016229500c01c03214821070303111021640ea0b441c040e041c000c4c800d80040d64080d100001803000b9a060050b4102c0c0201c42c1142000c3c039080d40c40804980002441d04003a51846503060104190104036090503042ca1160070707110a845000c90806085500325401100c05905140041081e6514442903074200d50b002d4901140c001e5652918860150038040c94504021030200042450340d070507440103118010000030001040408e20160001d0303003003202c84c08001030112403c20455484c40d408550010706c00c1c070440b4100780c40822140c10340d804161501e0001f903501d10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 644220998 1250 644219748 644219759
    0x30b2a0c0c0109030b04020907270302090c030103030903080307020c100206160f0c0818030304120302010b0d0f121e1110020a0503070507030e0307030804230603070c0f021504 77
    0x100210300c1c0c07003428448040e500d1030362020407981e80100080c1c03080781c2d0780c4000380686010354000d00c203000c82250a646140d82c1e400c10603003910401c1c001640903d17801d80009000e103103c0c1003107a041c0c903055100c0d00c004a00c1e696030120181d100510180860180f2010001c1a0b01e0700391200034500c8180d0060504d0346854804c080b10101440031100411500f100d100c00c149410000070f01d4440d410001e40c95485201400145101d00440d540541500c000103000904110000303110401c988694002c2c08403040d4403007001010801d604001d444a0115801c0c03200203031884d4400d82c1c401441e414130191020300031043c3c1c034034100d03017190000100d486212501040c2c00c0c01d0003140300360b55410b08118107042d0902c1d0010103031700004188205021b070000300002414051440c507030101e600102141c00150b10380c40d00b1091070f0814803030040001249042150018043d00f00307442c803050b000c0c0c102030456542c140120341c05018080d00381c980301d002c65110005030312011101c0c410403840001482d0b0781c1d440e04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 644222248 1250 644220998 644221003
    0x19060207020a091d060402100e030c0a03051507050c0c1e040e0718150905060a08101a03010c1e0504170738130b1318060f030b2a0c 58
    0x42c44903113007600628100f0005940c1da10320320340c24441624166283d2144403010900c0c3c809441d402aa11040700000002004400601252141c0782c010000a45884130320040c0c40d64025420b160482d0340003c0d020000d00d06101c42ea2001c80d0101211800c480114140030a04039141500454090b800400c800e008010250b100440c41e900c1c4424104514003403501d4100840b03c80740104c1120544510100e0a43d03650326002d4000342c1101000e5540140e8041d070b01c0d100400c07044440304802c00092005c04100d113018402c0d40c030117003003540b1800e0001841c4850844940b10040d001c5040c4203050001044450320702942d503610726031250090001500308414201d05080ca10083d030850168000c0081807105480001d200c072201e03001c42140c40d51001e03042c2c43c64400d060307004141303044000304242c92110140c8070700c88110380604000d03244006242040400b0345125001d21410640c41c410100001411920036641c452004082c030590005110b15022601828065486c0d0a20021491014400c4203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 644223498 1250 644222248 644222291
    0x40603150b1b01150e150402041a071205030402131113082d1005040807060f1a031621060501030302070906050901050a060516020319060f02090319060207020a09 71
    0x844160744c07401454502c0601000ba401481070b80000145001409981c0b5240c060700e020341405c044010440c01d82000c01482c43d00550310590f800e001510007a00341501550450b400f482d006014114048030012030340014000401090740030843c01c08c40e207000a00701e0211a00075020b10000b52200b0701d481400301001c140850f249441c900c1e0b0f1102eaa81d10480c0000d0f0408400819140110340c0b5911801d0040c0c0d80d005000000d800380d400c044082c0b25003c050360005200020030214905544410b0044c10746d158612a66600d85251200c030170b00810a14035061264a182003010360008000c0366101c4c07094a40a0b40700b100542c0c041c070420301540d00c080c012207001e44416a0414920f6150000098003230102d882403100340000080c1e50070340c03d11560145016640c01404070741060010646c83c1680c4055148155842c9290507440f0340c4c0c136055402140c03c072020080050204004505c108460414054004c03900300d5803c02c28480143c90301d00000004000400c0001020f050414074101503085 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 644224748 1250 644223498 644223521
    0x5090703140706090b13031419121b020a1a0919180b0306010303030b0112060b0c0f2d0f0f0a03090602010c08010e0c0f0c030901021c05040603150b1b01 67
    0x1d200740c14065900c2c0201001f201c1d0080c0c004004182c038580038500300342030980801d6040c00381c0c143c9a418001e6003a0302102e48200313540c400c0700d494101c0d44441100385880f60000d6101840200030001c0d10b8011010800694840401d149801c0301040020303811841d401c500310024420030004c01903002d040560f440501c3ca0220180915501100087d440f076405010060905503035240e0003050740d20401c008004282004010081503482e94480c021035000b070100c03010f07584956500415100b40c08140034405c24040d100020340c5800d002c19a070f080800c0b1301203081c014031845841c01c05180c010811003149290310406480c090700b1a040051845070b590304124150ba0424a41450041d40003101e1811038200200c00e400316140c024151242d40700e1040d10300c1c801c40000c42d01014450b0302200074114007400340c00f12144d05d40021005070451090030002400314a041c042006100d0181e08809052188582c22506a68580410340100d40044040c04589416010309480803002403240c0c086000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 644225998 1250 644224748 644224769
    0xa0515180f06060c031909030203010c0c0b100b0f0901030b130506211b03010e1203010f0e04020a060c020d0606030b0405010e06010825150c120503010302090402040509070314070609 80
    0x1139400d41c0300d40d92845510081c142c0452200e034003040d028890140c00c0c02840e40100240002400500020246240300ac401e562203900b0001080310103002e02d605000300d07003042c44100c1c2066441c1003010a1034100413011414140c80b0401c0385110f60301c0c216801c04108000c2c41c0081c05040c07210602c89140078040d000c10705401070107903400c01e040c8000f07040389507421100f003400e10400e0b032400400d02510034403400308154400d260514090410110140d41031303c07004980d40e04442d690b800124003012040c0c030003940101b5082d0302400214414120004224009003c0c1ca6101e1440e6032982c0489441d0b80c000d8440404480c1404104402030260794406544040201440d5052003840c40e100c140e400d5441e020401c082100058035260342200d20020b100145007051003016640014288039910360040328240c080b10304070381d2100d003d0002c0c3c0c0c5c1629006407200500b951603070700780802400301a10500b030b50f2103141400000585060018000714004070007038010a86064000342285070281c100c4400315 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 644227248 1250 644225998 644226007
    0x20729090705030307020a0e0925060806061626071101030c1106061c0c0f03170301031a15090a24080d080c0c10091a06090a0515180f0606 61
    0x587d500c4031000c003500c0e16440001940d458a0b1030781440c01c004800210b03901942148092011b0724010880c80844025459900c4a0360310101009440d1061100d45041a003a11101001007094014413400c650201c0c44410b4100000f10742442c82d0390050141102c100c40b110a08a20b203586c18060503007541900d04000031480341d9050010380381c0100038030701d40c000c0b0140d2581402c0030114500010109801c80e1480510907210034000842d982240025605101d00360b04107800b0201c1b06003124120303034024400034141d9644401305070050394094a06882b8200c41001585155900380c0054014030b54050f00060002c1c20445151452000b0107403041c441d008600c0810195201044601464100340791403240c59403008144030060048801c803030b90a20840150300c048424903803046040500a80044210812012003010400c00480340c0c03e40210041c00440d1202d0807681101d50800d5129144512801000b00030840061440c0144038492100000f07011601c013450099541048051f120680f41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 644228498 1250 644227248 644227253
    0x190305060a0b0906150d0f14090607090605180d1a010302090a0b09040f0c1502070e0c030c07110f04020d02091305010e040f0501090f0b090601080c13020729090705030307 75
    0x300451140c504001e80c0000c103100c8032103d550044c0d00c0c1007e04e000800c249008000e5800d100c20b41269418032070b205608c00b00e40003d010f0100c01d001c4446a0b80c466103003011a030031008032143c42d855441e0704001c3c03c0342c0c1c0f030340000c0e400c0d071000b401e005446020210940c95070041000c541000392100360310500d440801030701d41e2184030b181c55100b50440c1240090321200e140c0040c89500c217600248005045900490120350301080755421603c47e403207035100079207546104032403d200649044410303450401000c80080c401c506c680d400954000c02101400781c0ca100814140ea0010340480340e45940000c03e040c00e4500b02c40c580c000807881040401081d810a0341403925050090001384c8568400d80401007006070035040250b070654020321341c2003902034501d846142d01030107560302d040c0c5009141c00841e018038001544408694000c00565154080d1a100d4000350300a02c025121140340943c0201a0440d508040078541a5903503503c0c07141ca02122441c1c03d01c7d045802c002d00c2900108548400f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 644229748 1250 644228498 644228509
    0x90212180a0611040b040312260105010c03020a151d0601120f0618030e041d0d051b121e090919180b0a0608030c07090b190305060a0b0906 61
    0x9100d601a80000d103d600e00d88180707209009903404181030100002d008402c0007000daa950003286c50741d4070b075140c0000441d01107803c0b00c4481c0964004550710030340100259032050300300b00c0c2154001e005644800e0340715240c4034411030f62524121f14680d19551909a401d225900f0700d038003800c281001e841d031941003100300b1524020b8135101900b4644840c0d2408103004040d80300a000050070306c103403002c6101ca460080c2210382c011125500c11850701d210b0925107182d20b0800401c200408000d040c012404a6040eaa0b42d0000621a0a40c0036109a4800b5104c4c1c10411440800302c2e070750b00e00303445007503c1d0011600c066415480c4d8070805014451101c45440300096540c00c2808013a04403041030a8240500082c020b060360495980451000c100a000398200e2903405105104414050152603428003581c0b03100d1000c01d001140c0c072031201080707806800e44c405443c4001c024000850340d03142c100c200c080c542203508240d42540080d024007481882c14070802200c05c3d010b45031808280340001c000350707 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 644230998 1250 644229748 644229763
    0x50906010506070812090106052106010e0a090c0e040210050c0a020d0311061003020405070c020607060b0109080d05030f01150c060504050102041a0706050105182404050109021218 79
    0x207000d00c60104211003040050800d8030350f00c1680022900f07170f6240c950300c2940a04202c1c4a414043c5403007503616100749019050011070381c1400390051490780d10385034840b00c0c030480007042900541e030344051201c000742c0111300341030080500da4109243c1d41414010000207054041d0600309010003049641c803110008100444402d404441a00b4465028142600d400c5c1070032201c074880380204410070a80700d4605a000080c1c034029035081200d50b80340401503921140c8000d0181d0311a2040c0008400950203800c0400102018500800000d40c1c03028458074081c2c1746a04070010400c0882000442840c0e00f040740c1c010148800d2543c8175051606c405030040d42c0c40b04d0068419510340d40080c4c03d01c0400d4045800400b8480c400c100c2400340480700203001c0c0c004000488200e41008000036051510071074180ca0081c03541c0302c0225545500b407803034900d030014920241810b101400f07100c05569070751061354001d121444016a444040c0c0701d0101144100070030b8031030048440901450001400200c07031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 644232248 1250 644230998 644231009
    0x70312080405070e0115020c03010b01050f0f090901080a061a0a03320d020609160b0c0c0303070803060f010f050d0f15080d020706032307030f09141005090601 70
    0x300c0390381c0c03614200325041044070b42003100c8000c010b500005107441c0ca4114010740d42c4541e403e4803a6103003514200b50981d0703015100c0d40d00084050209094070f00742000105405c80c01115113a103456020b40c0403503451f03103099101e8289604900d064806011041c00384555405481130b00741014000080000c00000075400090314956500c800404194902c0300500c15242c0202020308407040c0094090780d851006142180041c080d034008240c640f00002040c4204205082c007001d806030500d107079095907400072484c1001610510380c0860752341c1c80c240b008212803402200342c40e0740c0785441c1c002d006102d841c521100d8104400b101001e010f080d40b000540d801c100c42c048001c81c9002800740140064040d9044240c669071510300c00060704074000a40034191604c94007600c980d103584c0e0b4816000c8807000301602c03a44415500d40300d0700c8416007082259003c0d40e01d050009501050712504002c44240910869441140304807501003840200425100720140e45828046803804500301900c928061044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 644233498 1250 644232248 644232257
    0x50a06020f09120f160b04030807020d1a1806060f010305070c0b0f0a05070815220213080c1002070e2a1315082e0306021902070312 58
    0x1511400c015420444800040042000d5034042c070481c8000d4403403651518040f03003807151040954004022080c4d00085606d103401e150300301480d5881f42900e980c03120700100d07800355251800e070000800702c0c7c0e00c494a1001125260f44c02d443d241d08034005081e08900320211582c00301e01008815a55403500200c4202d0a2a01169680f9128000c1d100e04440850003454020311504002181c150824200c0c4101c041c50014005516221020b4079040d01c1998071584500c5a010501100d043c070429070010760b02d1014034040a00003100340e05049070061003400154400c1d41c1010000b4140400c010300f0707150011211000586400840659990500d124207800c440c44a400200214600385040c680c032030513400d0005480080c0d0121600179401100100b001d5000070300d020440541105210b07051083c59201c22000781c03103046200058200c11800f0109142c1031850136400020f48119403002544244000368440e815064160740186244c010300e411036206c10410008203000e0040e21201c0e43c040d081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 644234748 1250 644233498 644233507
    0x70609090212130203101a13060605071b0b0a0c1104110d0f020c010e0601090c0e0d030e030c040609150504050f1803070503040f1e0f06120b031005010e09010504050a0602 75
    0x42420611b440c041c1d40c40c80c40c940503440c041e070744a80c2c181c1a00340c08202c5e5542030a0828035050710032603000d40a1480011002d200c01c2e00010718071160360180c40c10b419095100e080d40c4410b4441e0681c4686440c4000540c160100382c20842c80000000e20403100300e800f4811508221024292402500c00150f0344685030040800c0048460b411510503096080090218000074803500c2c0d0f0f200d03000c1c450b00c071045192841d51241c0c24030808000da0302c020002c243c0000488075440482c1d40d8038031840b920b5454043e01c00b03a5a010390700d40c4030b010b005088608012075440440c80020503002c0c0907521250040e13041c20108014010020041603010310100800440b02e221004160b00e140913182008041e4400094042401d00005581000702c0d10048891007221081181d450791540036849500b100a8460b40f06010190040b2600604941e040100154244000f00000c0c40c040c0142c152200c06030350303a03006109481c0ca0704003e80c0e0003807070f84009000c9401c0c642d491a950321003607a000380400e0381c00714 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 644235998 1250 644234748 644234753
    0x50613020d0204080706080103140a120e120a21020f070b130b2208010c080f130614060a08160510030b0405070e0f040902030703021201020403080a0207060909021213 73
    0x2410742c1c000e021102c4c2181c100f00e03100c18010f40001d50a00054071b21121204120011032400a0341c02c0740b81e980408100c425180403c02a6030400c60903210031382c00980441c41f0121100c0411104100500442c0e105140710b400301e0f0820491184182c412046400040c08114510400115030382155103101d06c2c1d03556401e0b02c0c030aa814840f42c6800c1119280300000349840c04009110396a0785075102e000d8141c99042c6d5030495682240c510f030101c80003042c5817000081141614804203988100d8051001c184054584d075180e044822240201000c8108202408594244402c400c40075208070001001d060b2514400740b003201404c2d108461194207200f5071802d109102e900030408540010f0818451400e0440700038085000c0007100d07500407407607484401250b02d014040e60416035005000b40c039403541103800f802628615054881d006640800c4000b000400204c01030a200f461a4043c200d564280000100062003d40c4052211801840301941c100b00285840f600844001000303181141c061 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 644237248 1250 644235998 644236001
    0x20a0305090d060b1f0f09261c03020c010b06040602060f0703111603030b010311120a02070c1d0c030103110105030711060c040303030b0603040506011a0d0513021201050613020d 78
    0x140c2c8960818200c800303e0000005c03407849404900801e403640300d5100c46101044030500701922859200e0007580a401520020140c04441000702810540305000c0c501a01025654904000c50340082c0d4000b6501905080a2084401c0e00c14119002c030306d0180b8000b0025901c00c006001d005e0500c110310007040d80280a984841328031081c000f26503484131a0307440d03030b4841580e06007419400320f4140703008011b0310b40c0f10340700d14210030031240e43c4241400d200c0c442c0203d80942c01020030b40181e60801055020400310701c13083c03005005084008418550404900c03003034183c0a070110000b84d4050005200041c9010003003500c803002860078a4507036840e6582102c0910f800d810040c0c1030b01800050011458005000b0b005580c06a1800e002031400e00042c0002031000703e40183c0240c014200500051a0b40c0112070200080385051718100289803d50305c00700c86055884002d40c0c4441d101d940110300344040c2c0079020b028071000030045440d2010100d17103913400c00032119002301c1d0b000441c0400414103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 644238498 1250 644237248 644237261
    0x3070312090f0303061d0402100e0102161202011709060f0c09100306090e0a05060c07080c070602030d0b031c2118061503050703020609060702042406020a0305090d06 73
    0x641044042c40690801500908160098140075030190b041c455480c40c560300120301555002d032400b034403058a5a000c985c4ca0001c1c3d0358050440c0109032584041d401081014400303008102010000c8a40a00c005800c4082c130750080c620300c513006010801103800c0819150f80c0100e8130319241c00e40e5501c1d44c3c200324052140b0b2040613400340c2000c98240c2400d03415030007003040e11030182040050010015205640f00e8420000601580c070040c0050b5004240d44050100240703d98022810b102a112001d401c00105800250040e407022410024140c1a8080c0d860f900000b83c001c3c141e41d100003045900d884041d040500240071141c141410046000b0f960b40802d0b6082c40810810f00b17681c071780c04048e00a4501810307218141820b1801300140c1d00030040d80300700c0b0750003c01032040d0ba1459007844071640000c410268840030030301c588401341e20b40c0c1c00b5010203031164400c8003403050005031200c503804005400c1f02e41154001024000025002412180d4184040703540300c00184040c5000c40c0a044c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 644239748 1250 644238498 644238503
    0x190b06061b01060503070b040e011403030c10090b01090e0606010e1201060e040209060a0b160c032009090f0d03050c04080d020f07090525111911040b01020307031209 73
    0x20140c0c0003141c01e110640c4810182d0364100c050b81c0059544141c411002d000701d005040d41e1040e0440100803030101568040d440d42030140079a030501403080c80302d03800d08140317542101416071200507200030480c049a200340503005481042004840f02010299030b16001040070741400b41180c89003405a503101c403903103510030182000b4048140c03661003146a2a4050314224014003511012420925080840b0001d0307a91000e0b0303c0341400280c44d41e4000305142c064003550b11104100c008004900c10030701d110300030038038007481d01d000b854004c0074003803940c01c01441c2c4091074000c01c3c03102c040d0a1000c101141010564035021609455102410500e4840c50b4409040da210b100007034809250041500c0808007000341c291461980d84d0490301d4240d48041b90022500487e1000b0105407140c544402480549580351220b01e440c2c041c0510b62070b04941903a4900c0d024814207070756007000070903107072842c8006082c2d030184600030305100080d650340a1194000e05000c44940c04100d009a0b640c082c1460a8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 644240998 1250 644239748 644239777
    0x50c040f06062015040305040801110a1803050606220c1715090714121911090904060b0d050304120b0f10031401020f04090212060102190b0606 63
    0x200c411181000600ca41d12403a00802e1941d291030380c030062110030708420741400038060704400c00000c412810095000380b088007400424840850441002d100703116149040d581101c0c0c0d11540c080001c1e00619502c0342c4000d000c80001d0050000a20208100d40c10101c141c034201c01442032a1417030340f03101030340400d50103085142510709030540398030280910b241640302c1c2c1058056201d10261020301c0441e60340154100e000d000116081d10704c00e41001d08148041c2a10604080c41d0311740b41c0b03542400503520841c044c1c17440c2c001540790070820310800500300348038a0105e14081c00000454014503000308050403850b80c80c007a80000f515000c0280c66102e6000095941e220380ba6050b00d244041e000c402980c1c0540d40c0c400240e070001c203005ca504e00036240d2120180030503141d81d9034400e00986411040f03170b9654081c0304c0003920403107900144c40070301a000000758803050909500481e030140144041d04551021001c0e8140c0011604920500c1f504202086003175036880d0041900f610a4079400e40414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 644242248 1250 644240998 644241011
    0x10090203190f0527062406070506071103041d09010e101505090c0d050a1506020a17040e0a1107020603010b0310060807052502030307080d0b0411040909050c04 70
    0x102d00ba4052072090044840b014803030700d00c07041840c0020300300c811046229480352012500415140044651210003a032074000d04600f04000f04003507802c1090211000e074041c205020656421004085c3e070040d81c0c0009500f002d00d03115405a14051040305010305000490108005030000c0d0071215070516041e00703d50003e00d401d1108401420318244000f03544c2c810800102d0185003403600c00c0c0c05290510401400c2140840031500105005010558801c3d51a50740c0300b449104242c1100080c0800c3c1c010748a045590b051168200d0030940036209400740c200414040c1c021591384158228480c502c0020701c150783e8104120b524440c00b04060350000002c000004c0b0807018100952040c0e40c51840b44810a81d03c50342030b52042001c1d210040405e00601203126403642555000f01400401080b0480c40003071600400c2c15644070f01d100740d035007042c000703115035900007075020b0b00c00c11207019a0108140400383c0f407004c05900030780c010013180340c0e180d5400c1c50500c002003002d4030030f00f0703001003042201c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 644243498 1250 644242248 644242271
    0xf030109050d030b010c0b012c01080307110604030c27020f0918070e01210509010b011b0c05220f020913140109020a02070b0d231009020319 62
    0x550300b026a410000a0404040703c0c641e520412500883ca984103451000302c3c0d0038804506401e07203850308010031500d001d0380d06610b404000c084045c002c02a900155503103803503e042c10046034135071070b240d1400b03608100020000a13a035a07800c60100c0f503040c000001e4180041003100a10812074000786800b40c000715042000704210300080c0b143da81c04a03603075612285080144101040101c03110070118003124151840e80d40508246815101414089450041c2040c035084c200c035015900701010741e6442404808558002c990b51058010002c2c1042100f00039a0303804046581d035000d018001d0007a403d442058140c14140410000c54003903040c0f01c040c43d6070707007240001c0d04860391491080400d0102c0d01240000d038070407070034100f2940903942c61b1a0300f0322070313820702a50000c40b00008601c076900c000079503001544050700901c118901c01182c0b04400c071949111165600c48504d40d264035240c01d2102200c1c078461070304219a502d40000d078032035454103802d000c014502060031404a04101c00d4088 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 644244604 1106 644243498 644243503
    0x41517090c040f0905101a0319060908070221070b1303120905030d0e0f0f013f0e0d020c060406030203221203060b09010e040b0f03010905 61
    0x106944144c0d00e1510789001040501c6c50590f54040c20841d4142d011000080721908400800c80e241c159104403108040850005106a0340e42c00f841040051807012360f0b00c501d40040c110408407030084141c41c030f060401d4090031014000c1400104814003640c058482d1042640041c0d48071904680e82c5803a07120490004005000c2088000a0196410410142450005e40e2000580030442e000d200c1031480f42c0001520407000c234005c03454a640d10000101d01169411100c174050420706554095210f4409101d0007000c822022045400c041600054624605841110b9074004244400c0b038503116100300540d0300c003e040000b0000070388241c0245800608010884581e000b80c5030402c0301d5a80100c50480d4613020640c10080d0f03682e05442110000c0c0480c1c400b5601d0320380038400090000e80d4004034107208903981c008e00511519215254061600050020001c2d81c07024206950b = true := by decide +kernel

theorem cover : BRFrame.Cov 644064748 644244604 := by
  have h0 := BRFrame.cov_init 644064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 644064748 ≤ n) (h2 : n < 644244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
