-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:19:18.631995+00:00
-- url     : https://prove2.me/submissions/0a16a812-e4a0-4adb-8cb3-6f2ec06c00da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 721402877 ≤ n < 721582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 721404127 1250 721402877 721402879
    0x61a0906060a051e0921011a01091e030515061201060506030408070213140718030803010e0c040e090a060f1a1002030702030f03090a0f0806010306110d0c0c05060a0b 73
    0xe820000c0c06881c3d8032101e070000507105000c00301403044d5901c51b1030741254000c80d441c441c01c10740480060541c40301d08554006409500c00d07560315154506e01c0c0d801c50390680030384500342ca02090b8a2190400c0c048400c0b0250310040c801e1040403030701d034100c002c4c1144850040f44103c072103200c482d40b511202402c1c3d40c3e160180d168030a80c04c201107400616818010408184003400000c105074030040044100d4918045508000080d5801c01083c00e07030041003d00b0420b10a100340743c655081d600d03070704918003050043c19080d90003d004160031001c48025038006102c0c0c0f0741c030642c89140071030100d5119848454110b40740c5d0b04003035440c01c071141240180c1410190880fa034001305050b0000b002030500c02c407444141940030800008025890621480800c10201c0c07006698940c0d10f03206008080d5103c0d4007400c450861545c2c14403241e81e022800c2070440b07400010100da011500c4181c03114500c0b465030b82910052400c040813003842c1c0c01490210102e4040c00036280c1a80e2420024401d030740342400c1d21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 721405377 1250 721404127 721404137
    0x13030e011701091e020703081005041107060923030702150c0303040210111605030d0309030c0311011404140c01020d0903030810090603081b0c1318061a0906060a 71
    0x600103410140c3c0040136075400604c510200b0b500d414200f00403640108419000190200108032602d100300c1c00400013032805540400203250982c8010391580103c00f801405280c44070b2411041c0106440390452104104070310141440700887c4640d41ea41c0a10780890203001c00c040c49403038488072107060381c2c1d001e14440061444c0d41c1c0d882d801c2000040045001a09000c14000c448108003010030506640002c010a0380c4000e9080c032040614001040ea010790806040814400000740e000c4500240d003641410601c101c84809405176000d008100168500d260408081006004c0000607244000040000303843c010310103e030049172102c00652004022035040701003000041d100e5000e072075000804062083c81d0700d4940103000c05a4400750710541d4402d5011810a5507112980c01c200004110b110080003000e030f1900200c2d407049021034481c43c2c210707503900c0000914008607146807405948000d04010104402c180b48903a440c2501015001d01c401000003003280c10400c0c122583c0207082d84030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 721406627 1250 721405377 721405379
    0xe03070321021e030c0f0102090a051302090603040f151b050706020f07050d080c12010b030702031605010509070b030c0708090d062306190501030515060313030e011701 74
    0x955924044250300808503c12200d43c41140c510340c555810340040940301459840340500c2d0702c5482c0c980d00c005448501e900c1001200345035035551004200b02c490554400c68607080f03040015009010340c12003543c01680000c108001c2041a0141c0c2c40454460342140700181c1080d82c2c00400c032181c0300940c60a442c0c00603042d0907294069400350842610908000d450032180c512440555000072404450075400034810000e003135001441941d00c0459940080e044c1484103110501001d810320030514000c80c0000400c1c0020301c02c1c811103040390b549080c203076a842d50b2440c1c56402028211011400d03400f5292022503866045812203000d21201030b6550708025854a95040c0ea1b40840d900c650b00c042c0389055400000d406c1d01a13103116036a01884072405600b07070882042c8000004091500c90524102e0800100d20010000401c1d00d40a2800245642d8bd184190b090040f100003056408180842004030401010464030001442a503999202011403030040da1a110101984e401d031302082c40c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 721407877 1250 721406627 721406663
    0x6110c180603030405030114040606170c06090a0308070c081e030f09120f0307050706030507020a0611040f080f010b0f010f03051009020304031805011b080313020414070e030703 78
    0x400395040080182640d140580c0c440010f401c581800034010800702c05c44080205001052107084000c04191510311080e1080d030001c0347e25441000b1070340b413103060003144002280d00d030ba5490b100516071004c0314941c2c51f80783e41480da101c600203200704210f601c40d4481003014007018032428008020032000450804812910058460700000c0d055034005001162410344810104911445240040d000d59564012814020708010b41031300709034141814041405949030340020003070034294001d0b000084089103030200c41001d1090780d0000e1203460405502041d101c01c0070802500701012540208070031220342044c0841d80e0003045101780440c01c2e5800480a50b406604010b03444441024501c002d6911403a0880481e00255001d400007150340720f4814581482104038005810709080c10142110524012595400c00c0c09009149810101c08101c400c0c0801d080c40310314560041c41803140008400c0200c000310f07000c41d480400103406100d00181c1d4280410340c034044d25000140301c030001e800c9003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 721409127 1250 721407877 721407919
    0x10f0507060e070b0d052401051e0a09050913020904021c12050403030e01081027090302030c19050307061e1b0f03140a05100b0c01050106110c 63
    0x3906954190312444a0030b1401d200340301d40b50241140000c1aa1550000e0300c0e41001c4480003043c4403003e06c00c0b19441c286540507031104045002c004d1034201d80e664010448070300c490645030101c5980e46400300d8814580d5400401400c10b4910640f4000f070681d80c1d09000e0003c043c003da40203908502c0c61004034015040400100d030100c00540740e0303100351b52000e1380e92503240c41c03120001d41c0002c1e0b004a0306200309544800040b02d5a082444c050040303050198901b40c89a5480c42071102d44200e450b035100d042c803a140364416440314252004c0044110a05001c0e440b13078041c15609409003e02810b81c44d9182c02e103240054880c1e0400c2c029400c0031071070303602c1c42d006150616650448200021003c0540102406004810f01c051242d00c610f5698400e0060718040c22501c1d050141410b08000a032441c81032801c80d81c0c015040c0d00082032a45810b031203d00700c600640c110f17039003078400040e00700b14420054100504036680c940c0d4060b6400700d13080c2031649030144003a8656210f018000200f08a081c22 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 721410377 1250 721409127 721409137
    0xe060c0a1404080a0b0f0a09111003060e0906011e0b0d090303020405130b011b0206030f0c070c0603020408070b160b040804080d0306030203010509030702031c03090b0a09110a05010f05 81
    0x8007240c0c03403506464101036450030301c51003411142d0321950b404020345490711542ea26000404c10b41c090103008583da446c0720380000e0070001c550044089a62248000340f01744c00482c01800c512000c0c0110741090500f0b01d454907001d0244241d40803071900500d081100c840e4100c01200c007089801402c10b04101d1020f8040c017000708041d01019000d12000c036403aa903041041001d003e040c0380006096881400240c440c0701d40c4604040039114a82101e40943c4801080300e50208001140341c0b02555401000d01e01800b45840152442c1c0c000c0f2004540150141d0040c001c1c0e54092045448041d510243c04065208041000502104050b540c000113500e40c41c10039000b52103001ca540c01c25489501032450220301c2448071000a031581410000e5085c01e200d61600542c02030013542c604107a54011980d030304641c10084181e81400f07620000924400d07170040c0a52588020064240d045c4a0f5680c0081c001200003603c20201142d0110224074014029004841040c1c6404807014070400f0291899048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 721411627 1250 721410377 721410407
    0x60623031b03181501061b05390603040f110f12030418050f0c0a030b0409030e010f0908190317010603020703180b0904020a050d090b09010e060c0a 65
    0x1207894004100c08100080c0d48124260985a01c40e41c001e58901440c0940b8001c002100503a902c00521820ba8040c120118461201160307a10707001a51918900d0120180c60200e80604401c8070b04200b4000440b1030055920443c48413014610b08100300800340c4000d4400400440107060014000742a4605e00d10450b100101044c107083c815901107890031020380000c0150340c100003010700411100c019560b46d0542c3c0344504100354613140e00d94842d91038010300021901035002c105011a18440e40000c40c510b003000d4808d00c01000103280c058405030ba0190106c1c040341c03289000440041c850701490040b03806d000001d0600e01e00204142181e51111720b402c0c0c0410100301202e4581e00c1208011500070101075500581c3c81a82e410020403000720100c5000e0450000c400403c44020003409850410504850041e52400119001c0d5060f104000451030000d061810581c01d05c420b400d50b007846041000002d0215032060740010b0b8039003800300c50640030b0201c14801c50400d148182c8101c820348038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 721412877 1250 721411627 721411651
    0xa021002010b030d0503070906020105010b07020607020316030c060f05070c03020f121203011e1a03062e02010c03140c130e1911040501170405280606062303 69
    0x141c00400720b0705142e081500107000c220000188801f0340e0b4802c5c008001060980700800440d41006240850b61241c40d6001e4440d42000c02c540065503814001e180607641c4240d54048030503644c0c9030a441d010000c0c442c4202203000a10b40040080c01001111949944800d910200f00e085a0070005164210140395070056071000c403505c2164ad0402101e410040d0b070206a507182c0d0300d800000301540d0380a140080304504080d034204820307600300d040000048401303024507469690340b00c0854800000c4442e000305904942d031068082c3d000460302c1c8420020294000e02c05024018000d8044d00c482c00b01c40c8a05140f01e10004803081c50601c058401c91070a40500e105455964880301a00d100580d41307024000c6188110f584108041c2c0310344001107004011180c107181c43c0c20006010000001d166800440012000508211003441040c0d140d5204904812a11002544000d900c0b102d0329000c8400c0391401d58040f400380e00400d0140301301c401109003104098480401d001a6410181052804003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 721414127 1250 721412877 721412891
    0x1020d0e092a0f040302190810050c071a04061109060901030b120d0906120908030105041503082b020c060103140c03010c05070b0a05060a0b0c030918011d090a02100201 74
    0x440403900030503e001c0380300b00180e01c640c00c1d4010000700380f80c44000403e400481070802c024a05011034540001d182e8002c1c00201c2d03544014000d66103120b6114024140b50310b011102c941440c1804040340903e0113030000300034880400d003c004003485002d00d050b46c048001c1c40410143d41c40ba400c0101c000b030000e0040c0d480c42c20a484040c1c40d2031484443e800101c2c242a9091201550003c07501300c4d28810030b0710a00c082e002d6900d4403c1d032071006001e55405561108900018800f103806020002c60b804949596140f14030912402c041d4848100c5c0445540703400304281045119000b41c4450170f8824000c0d1580e0703480e503501d19804402c0240d0004040c00b6189080742076540c2031240c54032100080d01c0b2160303074013910710340004c0a00c00244900b030070b1841c1806114998483e088400c0c2641c0d0591821070b070b604d1009941620718040c0310851a4031444082c6444a020b1089130894103d840351941041c900f86071801c408a04101114003800b00d03800805240098a000f0040590207800d90000003a15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 721415377 1250 721414127 721414201
    0x2010513050c122109011d0f040c1b06021801090f050103090312020f030610260709080f0304080f030f030c130902031512160b070816030e01020d0e09 66
    0x842c61307000183c00841400310300c4c01050b50304020581d4400d24800082070389215120300188441d00c820903014000c0746d603107000da8112030054081c4c0100d04082c0348a581034140303d1400d000a940003a00750010b15040114421895029800c541d090300e402e54952000c0c64206001180206600c031070640800c100307465560101009032004102413101502001e90303a140490902c601c91001c2c1e0b02650403c1072078056902c0d82d0059450021404424008002c51a221b00c4400c4030340c41d406810803040f03401801d1004821000020040007200c000304180e43c4034010291165860f4003944120200300401040000c1e010340a8900400b10301c0351005035515025291900c4104903002292600f07204e030107d4490000e2403506480409900b02c44400901941141da104200f07452024460382e880e940003c224801080308010903a030510042c240300341d42200c07a80c1002071000d40300e20030080c05030040300648a056071042c103141e0300c0704001900e0794101c0e0320b03101c444071104481d19400c2ca007017140080d603028072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 721416627 1250 721415377 721415413
    0x60d020604060201060e1b03070c080c011a0f01030519020c03120a1a0303090a12080c0109030206010e10061d0a0b0d0b040e1b0105070c1206090302010513050c12 71
    0xe030007543e0000402c58102280d8040d90341018041007104181c01c400780031012410801c80c5c0d4070100c02c0c03078480b40594203450440c00c1d60080d490b80207455401e20100c0d8900a9805c0b09401c03030000c0460b458006210b070400150b0032070300c2c1514403200c2c464010700449024101c42c2c000f000d1505001044034a0507280840e003081c1c554040d40da18801c00d4842041d02e07480e0410050318201c2d040110f010314074091820000408242c03c6110300710b0035200101d110000c2c84a804203954100c02607000038440c01ca4145030083d104c00090054aa8641500e00420b070020100700104041c3c500380d49035007080d0501c0f4291081100703081007416600c40c01d020303400314121440030050441905070703480104070b124840e81008256410108101156404203012a2100c0852002c05810180c2801c4c02130356100b00d0b081078113010601da0454141d091440b5044001c0100c10f07808241c0c2140640e00070441034945415484510b1505c0201900d26032010000c00742d6450000401002c25800300202e800b440c42200c2500c02d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 721417877 1250 721416627 721416629
    0xa120f020a1403010e011512030c140d0f0c050604030e061c270506040609050f01020f07060b0316032916020c24070204021c1b0e18060d020604 63
    0x9540b822a1150501e00f002d00038100441c800750024481c4886243c42c00040003894031400c0020f880e0200117406041c01070100305052034002228000c11010728040741e64030b030700040c403074030000d501501840b00751441140140c1d491640701c400b030455a15103441c201c40031502c0b450351a500400c2004801c4418524101148009004107800300d41c941000881c0d1300084c006036403951010718003442e9800083d2010900c1548544c1c81900003800390072504041d46401d0440500260540c800030b800d510400f5011302070803480344601014044124490b09141d01d50902007106110103003075060030700003c0d401c490580303454100615881c02030603461680c14484942942c00081030460b84060f0350255038144403270200c802e4180c0b00c601c0302c02202d500d240e098218100002c0c0240c0d001103400021551039804036400c0a00524400d080b200700c00d0038000007000c0500381c1003192456284002c40c0540940d500c2039000c40000c00c2580a002048442d105481d401451603a002d54164090801030790b450380608 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 721419127 1250 721417877 721417889
    0xa0504080d0e0106080606040608061902040e0a200a022e110405031e030a0f1403010905090c0f0f0103050612120309010c03020405101809051303030b0402090a120f020a 74
    0x205104c3d18001d44681000b102400c2c0f2401141030a80034084110001000340d0002c4080394000b4441c0038000440000340281d030460410107203610103105489080d03070040b14041d524411482c2015101501c0200d1a224503012180947c009400b1010f0041744120000c1d0703410540107001c40c1240c10201c0c030004a40c09580e65961b60b41001c2001d00807400c0070882e0380100012010b504039618038110074942d0300c0c0201c4225004001d010b06129000d980b0842400035840124940c0d15104d584801c81c0c01c0151500319048000303803240b8440742480e0f107412000d00c000010050200c0003d000c59900450103800300070a41500071000000c0750100e18801c10500e445006e20a0b4426268102030707a1f00e50940305074192180406006002c20b01003a52452510400d040442c01c10050b115000d100303070b9000c42155030205040504e4402040b4814000801c5001c0b8107109a4040001c1407003202040200e00511520030b0700174003880414802007240c11007074005a40102c0804003d805a0760010324510881c0e0046 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 721420377 1250 721419127 721419131
    0x160c11100306030c06200706171e13060b030610060e030106050612071805030c010c1505040305090a05032d121305090f06310e060f060108040503030a0504080d0e01 72
    0x1021240c1886c014250000300c0340c0c002d4000d040c03501c08020580e61010141e0a044405500484e2244038079500300c01510b1801003c3e00502e213003e0014a60342c0c06186025a0745a0501c180441c10b2301d00411402d1003035020a1088580900307001040720f0100510402c290150340e1882c1c0455030742c0e29070340909000741c080c695541e464640003c005044e548076410301c1071445044e00c02800680d90120300c168608500380f030504540c504500740300c2c00c107400340b0b00c820304a01e10385420300040c190320400a2059000c1aa510f00034650369000385561002c1c00700864542c080c041001d80700e1810000345000400058108690700501c1d050a08007159104400328464070140b603c040048d4201200d09603881410021000760740c0c80c01c000802c10104480e4803070403201c418407a090800e1841150b04070b40f69810000c042020bc0c1c0c280d00c0070307a6035107000d940d045105902d110001d0469032042c491a882107501c0000b540c00e64a40c088100c020b0103001d0b00c102c448050030b00640b4201c018a2041c041e03c1c45410b800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 721421627 1250 721420377 721420397
    0xb093c01080f16051c18141605091e070c0309080f0304050d060b060a0815150d051b0706020301031a0105060d0902011412040309050108090322050907020303160c11100306030c06 78
    0x1040d07000c41380c101f070702d1090740c1c01440841340c1404485011400b20340341521955100d65450000d025030021707030b8809034480a0080c0a10200b141c1c00350029158610079251501400c2d03c48100035070312042602021f18a070700030002403015040111100701c1103841060007007500f0414400040c15900056842400151004200710b142007d01d58604008103042e501103801c580020910368040c8903401c0c20103605901c2c1c5001c16050814109408020b1500c81c100396144d000031710b0024040c0d8020703c015034950882191607105d4840c06000c9034122a0000d2540b8a440005600c1d00003a0120b4401a814060140020302141111400900e69554485003c03482403400740390280c0000c216801190401c2040300c00c11a242d440001294104081a4100703ca0380d9084041c604034440b064000326040240d240c240030583d074000003d1170080c0a110100012071481010031280c500071880e003c0c061302101111040f0504104643c01d1000d07405143c0841d20f583c581d06c9a143c080107950002e00011480b4038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 721422877 1250 721421627 721421633
    0x30706240603110301090b0a0806091e060f18030d0f020c01050a201308030a11150402090109020322050f10060b093c01080f16051c18 59
    0x11400c4041c0c031460400700500307840c002041c03202c0e0005000d2015100d50301d400c0100c0075525403012800800300d40c422280145049032400e07854110500d122110103015071640c1801a0f000b01c2c18620039550b07401c040c00c065941115107100c4443e84533081d40c550000b0802c0710342c11500783c040c0e8002c010800301d000d6500c2242000d03450850f0300c01040d00c441c003450030440540b10a1840130707682e094801400526103484117001c100e90113610641c400368443c8000141e5445c81c03900801c2800580b01d000c02680c12041220a6a07210304c00210b0b00254404e51141c014080c100840c2e0285800c0000c0741050030b0040d040003c40d8000300ea2921055441c3d0340074585101c0c4a801c20410714020103d6000c052080511340711446405020f111026071080e6900411001c0061031401c034400c4405020034034050f0769600ca8100040c000d03112100318001600701c80000c210004407881540600040014400c11401000040740c1c1c5401680d00112062030860442880d58614001c0c4c0e528204440248607003844286 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 721424127 1250 721422877 721422941
    0xc0c0610150509090610210f0608070605030a050a0b06161101020f03180103090f0606030b0703020304050c10050c16051c0302071208090618090c091c05030706 70
    0x1809881041820080300f08903440700c505190300310409455030002d01c0c4c68002d041d1000780701c22001241051441c0c606890803a400d070010313169040c035444200901510b5441c81c07a1200410301480c1c001c00c00410201d000c40070310345c1c041075102100741800100015031400154050f40140e094030100014800d00c04244044072400c490281c000f4002415800103401c10551a401211441d408601d00300311131324100e901a401048100754043e512030558055840d01c04001c280c0343c081521489180c0000840560280c800c4a00a5401c14014008020144100000d2903031000920301006014040001001d9041040070099010b0101c4c20701e48904002c01d01c8840300115016803241140d64684801294000c03c0b0302060714400800e00903000c1d60382c2004003031031003080007940d08008000f07601050303100400103200510004907a48080c0d5100c0c90442d031294018030a03000c0d1f0100c0301d04c10300381681d100c0201c0f21603018490800e407402c014950b118101103850100180140d60500020340030141460 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 721425377 1250 721424127 721424159
    0x703020f0d0806030a150b041814010212010e1510020a0203010b0a03170a03090c0e01090b0103050906060f0409060e0d0f080408041a07020301110d0f09050a0b0c0c0610 74
    0xc2c60702801a20b031100011381c1c1d440c44220040c001c000b00f801004000c0b1601d070001c45080c00050002e00002d003120412050b2035071080b2099481170751410a01e141e800e418002c07601c081c035200800c8003059017000b204451103400039001c910140c0c2c50001420b40e64035038456260030034020703030090f21045031580103141c02c3d03c8940c0c207003600c10000c2400610008500ea500003c0920340d203c402c81e11040c110b03200b60000c121901001e441c0c9001103600092003961200701c00d050740c100c8001807111100b920f00640c181c0e1f100341c1301c01c0510340125000680504210030304141b40308000300042004101038a0361411161140030a80f060340140c1e540782c00743c903004005000c00c1081c41c83d01c00351034034180c0c85a25180c002c5001c2e0810401c3c40803a030859a080d00e409541c2640d400600070044184070180c0a10136a101075000840641401d0000103e46680c4c03082e0021107800c0300142c288030589590b00998800c1c01440000b000b84240001c02d103158081103540d21035001d01d818a10417505142005805042e5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 721426627 1250 721425377 721425403
    0x1707081b16141207080a110d090b0a0c0212010203072d1404030b0a1d010209010210240602010b032b210e0c0a061812080702060703020f 60
    0x400c1003045031003105440041c1d15801080801514100310a0541880086024000b2003840401d120040c0004c020003490922840d4076000104840001195281c1d28030620b030b40081903500d5401c008010000d80106000403003840d082c80d0300141c503070001d0004040c0c00b540c01481e81d404400c0100d2a90004035142220480b071071120f030300c1c802d203d0009110801c2c5005420812100001200d000b031061400d4a02659008484283d075181c0809908014002c3c144a1040440b00745400410b1802c10710845030b1800301a030144c08102d1500d56103101600d8a40b6002181e1011640c0025034506000320000103000390b0740c00410502200800c1528007011070510128609001051004404c41c00304041c0794081c407070030324240c041410141c009403110014000e022050410040700145040070030349519030a4112005c0b4030103501c90030f0466807100219510140b810f44e0304030501c414258141414510b510406400380b611038030b40d02080d6070b50060039080f03000d40c3c40f80b40b40e01d405880901c01342c204010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 721427877 1250 721426627 721426681
    0x30906160c0816031202010f020309010b030c0a0b2a010e0d0e01180905060d0c060c050f0105040c0e0c1306050d140402130c1b03090303020d1716170708 67
    0x100000f411000b45a50b1000074843d2814090002506000f07400c08071015141c0d001c115228074001680d18040d00313090040610070b01541e44910640e10704010302009640541c00c0d41ca042010144108441d294100b900840303901c807800c2458010b14003405a445c0303419078103020708070900f001c0c140648400c5c8090001d60500c40c1c00c844c111012000705a640c4211402244049880d4442c00080b074940070840b02d000c1c141141102c000725140d500f081c10030151521540886041002c4075082e14221071040d40c1c000d0050000034420803402c000e40307900d035400841c03600b0401d240811640318005905010307440b8801298003c64000005110303803040e501d82c210040d5458881d45400d50005540701e2090340d9510516907198061403880748140c802004510702781d4038460200f0503d04001d08000783d984011001441000390071400b951189080000f114904d00c91001c80d40c494000d01c90205040340000c10410501460310003e440e0340146003405030300c03243c49490490074052204083e0350389a031090003042c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 721429127 1250 721427877 721427893
    0x150b04031704050319110a140a06021902010e0a090e012c060c0f040b070c140d0515042a0311030c0d020906040212152103090d05030906160c08 63
    0x103200803d4881c0100d620007030404c04040c45142c01c01c0461104c5d4103a9401000855000c23905070b4a210b00c00c80421011a00c1600017561984102d070b469107034030035003100190b110b11a000154055003c10400c1e103402440010340c241c50300310080895003080c4000a55a445038000c140f1042c50140306110044940702d00c0200300b04030503c49a80e1880a0300c0f481c18140f0005c4e40d1150940303441d040e90b001c1d0120800343d035910142801e091240d00402c0c00384562240980e08450703a1031414801c44880c00342e008004d46407900d200d00c421589450300500507140b10010b02420080d450204a464440c1032680c10004d01d254110b080640c81e5495220145001350701421000d0b540d503a03031081100354654101c03620516a038500700860040d001e56147c0000b56140441485620440e0300089202d071030302a5203107915560380e080e403100800c40c8080e41000b603400420000b01a4106004921380d041c1c003e00450349040200340c04240241d014008442404074082000410400c6648070f107401403503500d004060314 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 721430377 1250 721429127 721429129
    0xd0203070305070e011e03020f0412150501050a030b09160306051005040213050f031e0a0b0f0609040609061b051b070605030601051b100614031f0f150b0403170405 72
    0x302d0000c240d405840c3d46c50f80c1184034094480d80460f11a03240d800d155940312583c404d81c10242014055044800141c0c000007104002010b01c54035040312002000074071120b140d52101200080040c00820b03043c0500f504451940714641c07004801180b00e4140003030940b91a00d011000720080b0340281e0310640c0108401c178150020545040300340da108641c41e10300100c0040c002480c05901d6483c2c1c1d1034407940da00b08499880300100f0724080580c015100a0803950303031502c0c40c0d80b403520200c4415509c040300c0790110340419529400b408a641c424200003481e5001103440c08510804450b000c07002510000c5c20b8410f1340b803070440480200e01e03004010801241080c9002c2c00500004100c6c0f0304000021580c0030440151000740090b042d09036040d91003030325090556a018100c43c0c081c1d04c0095500d240d10440c5e90078000341c001140d01c03018481d250a64080744070040505070b58801c1c0c04045031180d0685038a002c001d64a10024031f07140024640d12407540c60000340d521142c210701c070322030401800100702c1c0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 721431627 1250 721430377 721430387
    0xf150e01080601030b0d02120f3a0c1403030a1805070e06060d020f1801021c080a110315040b1203070b220f030909060f05060f040b0d0203070305070e01 67
    0x100c035090070041001c840c088041b030b100369907044001c0c0d80107031020038601240c040801c00301e40c0c0542d0f18068070203c480a01d0005404243da903c80c54200da402060000c229444803a1030540701c0700340c58415410300d66900c1e0621072221404081d01d0035000001441642c45080c4281400c1002c040d100c1800100c65440360782c0c861003240302e0000a0f220890028025603217075002c580220f0500c0701e0854864841600780b0003150414412500740c60740c40706a0b40d0b01507000180070100840d03201c101054480c0350b21002c54003c44050081702c0001c0d102c280b02c0403c0c21400307002d1480340e60740125002c00440c4c00c804000544240608e054090000c40e0384454000380007200b100c0358950040704e0112161600c0c002c3d00c940482c03602c107001203d607040b041003003000b4004c000542c169002c0e54415040c00d481d80200c10890760503100d05103448581d08400c10082c1010790282c100e02c461001403904043c1e6440741540c1c10390000c0c41c0b07068600d60000400c4803180d050b00c02daa40212591031300d802c5280b040000030303017 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 721432877 1250 721431627 721431631
    0x1230301050f120f0106080c0108010b1606061205060f130830150a06050f090f0f090103240c0503070c05010605150408010501150203190207030605010f150e0108 71
    0x4060030040700b2425035038a0320801640031140c110304550110740729050a030700070140b0303000d00d56241c06081ca0307598403076102d107071044c3c1650300c540303001440e100100c2424068003610b000102c030040d03156000000c07038445080300d078800b00d40554080c0107240b07002d0540c2c41d0f409000601044141c189061400041100b030000d48035000410418200e4102e600300c0900c4038503d45001c00303031100d42c8020030401c1461811a140e001580300f511640341450300d508d42074a0340d01070b81540801a600612244503207280400c0400e28405d0041c00c005044031400c00483e605840c01d80094510000e604040c50104000341104402c81e64206820090145006401001e9110180c0003c040010fa181e520080c03007020b5200500507c00100050341d00007000010b00890b030007520907001e542d40307040c1c00010703220481c0103c5a00c0f5107255010310f01c4d003c42c1d0b04400406410b00e80c20501103105191001c0000741c458860704e4040d19150382044c510610700152600046500024082040000505907030141d800c0341100d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 721434127 1250 721432877 721432879
    0x1504110705030a080c091f080709053001050106200a0213110c07030b10080a12051b010501030812090312011703072a05060418020a031107030e0123030105 68
    0xc0c03855102d140508a46006ea076503c0f070351103c00340f1400030f02c4d1101c0c100303000354041c0d954070ba0000c2a80e56413415102c2a090740f090580001604000b03401c03500318070300c01c0b00d500340d4a4480000c149149400145c03c48100b41c015601243c803100d11164401d800100030707840c640c3c0001c0103100b28142030b80403548105081c078000115035190000305161004000a491401401c041250b041c155281412030000717070141c41035400c03411200c2d00451400d40205401e90340307070b420515447c02d03181284130440e641e1340482c00f4251200004481442000000c0c02814001d50045030078a4907004000080c0c10024409070910701d0a034000c02841284030801d84070725044641d640f0781d203401c9180f85040a8254481c50b031b4014180b140c007510200da400e00c004a01034049000c1c2e01003940b8151128140401ca2150b4000e1040f4a50001002030000045800030a00c00c038282c94045030103500790351454215000354800710041681d0728007200e05943e1040303080310b000322103181c410708003082020b0329029440103014017 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 721435377 1250 721434127 721434137
    0x20c0103020702010c0b04120905031203010b0c03210901050c042706051c05070b04120803042301020c0f010c0c0f02270702070803030402101b06051504110705030a 72
    0x8025680105c8555850380e41110900b5003c2c6094038240c0805000e44c260a004100300e00d42c041101d0800050101008000100c0180303583d017400d1b4507510a8011411250407403208200c00000344000110220030854101c071461101c0c14172201e41030a403000200b405000d0201400104070350f0b041e0501256075411a031603000c207050340d28000c0001402007a0006030f045031103000c2280c030341d08506105074800b03401181075460640e1156a0303112140300314421440307000480030824021030a034030b00668000f032150890346a071450114908400c0c99109140d460a650b010800b000c01003800e000b02190b0455076002007084504420014007005841703c4051f241580840c007031000c6486010500c2d00a032510340b00007481d0b0407662890b4100000172a540e5005000351103000800c01400400c0e40d001341e034014030000c0103020102040724500c082e0310621010f54842d0100d003022500c02d20441d13003d400c11400001d140d5030141e080c0801d42e80d9804021080c09410404d00000c54808403d542c0c03018024580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 721436627 1250 721435377 721435387
    0x2010c0c0809040914331b04050d0809180108120d0204090905010b10080402010c08070609061418061e060d050d020106030c062f0f010510060212040303020c010302 72
    0x8103004004c0540c00620200b1160079010f041800000c01041016540c18001080d403c880c1300900301030305003801500f01213600004581307041c64000070212082e445518481c2820307510400101c4c0c208040b402540c20040024845400b4100340390001055031022010300c140d5494030389815900c11041034201908980410701c4d400601c0103404072401402c00070428406001c6a041a50007415041400741c800c25140da040307058207001303540c035600c5280c058503040302e0402c1359220700207d5030181034100d03801c1d03030754010b914002242c6220b011030110030000c1c001c00a180c8159007180ca40071407240b00c545540844100070903c0b01a0301c40102582d60320127100459140c400200700b600072040401002401640c11081819505501c03c0048902445402c403680780d56032015100d4820420641c21040780314441b0318011480d007880000030090351800c480c280e000034580c203421601c050b80e50041050402d201007100682c1009581c0032440300040c03a52820386140e401a540700140100340b4103040e00420b03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 721437877 1250 721436627 721436629
    0x6011206030c030b060a210602090a1d0f0112020f0d02030c0907170604020403200102031b060f0606160303050c070f12030f0209280b040806040b0702010c0c0809 71
    0xc803004681c4214031036002e98603458021031480003200c080c1e00801400000140f0502c1494084908aa10700d00d202900c2025441d09006503100d44141034100c184c1090008110100c4101c004001e1200110000142803804924507401010307030101024648881d08580980d4507103010070050b0b00101e60310304d00e200c114030200c1d0406621a030b100d80e00400000400901c07980095600151100308070300304041c0e80e203120401003203000f83e00000e0801020301d1461003500000758400340e20342074140100c81c02c02d100031540030703650320040360f8541e11908036005206001c0e2604451681002003214a1401c07c0c1d44401802d010b041d405034050304150300e81000c0382010501a046503000c0d5040100c034030002c43d031410000d96910000380c03214006450021103034900045031003500c81d107660007088a000d02054111405003a18211a04440c3d010b04803000101d003071415005000500c250f8010f402a0319207403c040115060040502007564101460011610f50214524070425400311585844d000070708 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 721439127 1250 721437877 721437881
    0x106021015090920011e080901150909060e01050103030c0f0c0b0a031a090709060f0306080d020604021008060f06160b01080f120c060106030905030c031215060909060112 75
    0x16105200c000d203002c030140700f802504000130f00c1d40ba0319520020115285000111102d42044c1e05008031060704901240520384200a07068015104000200f400c483c404c0102110407000d900426606546d4251501006541d000740c94802c011035008116a600d07644018100000e0240018141c03c19181c040040010f02c01c1518007601c0c5104205132500d03800080500100b12549401e0780c1e4075500b000c01111894550351980c0b10321f41640d11881c3e41441c0c148140c0d49000340c02102c070280b40d21034802040d902000c01c000700c0341140c95070081549080c1030052024096211103008100f080c00402c11000d61038185055909000c107860362543c41110b042000350703080c11030a004103800150800025244000280606d6000c0b0079015100c0104000042c0380d4540b04000c103040054003d1401004814000e80c0038601c1907004500f40d84c4bc22400d02c80c4181550300c100c0034040c0c104203403024000d009000b150b01d500c460b40142c0e4000d01e0404c00800080202c240208810b040200310804a00d03055295 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 721440377 1250 721439127 721439129
    0x1202032406070b01120c050409200301110309011a0d08090d060f1409240105090601020c0d05060702160b070b0a1107030c0203060a02090114091915090e0106021015 72
    0x3105680ba5615456512296405e0071810703035104400c420041503510307240c070a10110384c1c0e1203000804050500281003c0000780700140c0f5916540c2c5408075240702100300011846980202e000251056407008011404021071021500840c074074804807000400b00c030102d450381340044403050381d2100680750000c080c01400c1c120380c00076030070408646543c400c0c00c5010742c043c100d500140c89507040030100e0b10361006084040c4580d40131000004010724181036540d690041d0062041d2000300280c8030202d18681068141240e5543c418010014590342c1442000ca003090f01040d248a220714049500d6001d00511704060310401c01c44011581808060b8080300d005d0f042c2c1c0502c15101c00042c203010f0000c80c00c080341030b4024000c503000a4140300003842242c0e01a44140c507040c0030000d0611148660350005050b4a4200b41c6039100000001c0404501e00020f04e82d44050311442840c1610041a4509661102c4903e0000d00018454540c020582505d84003038030341c0000360070101e251102100c00c0c1c9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 721441627 1250 721440377 721440383
    0x6010b0d111b011b02011e09060207081b0c030c060a030b041508010b010306050a0305150c0c0a11012d050906040b040b04050918120a0c0b070e01120203240607 70
    0x281d48035070b0340c14040641100d8169091910600e80b070304440c540036426143c1407000100e0581c88070100a001118541c00818128002c8000608120040e43c0380442d40d4003103805041d0056040584000c004410005034803464010740251079040281d0300422558080c6184501c14943c030780000d0700c1140c50326403024082070300501c2035011003640c0d07050840c02064545203075800a402d11102180d5414110b40281c00c03640d11200906584031811056241040c015289404c072000400050504174000c01021024a0240e4100c8001d00400c2001400c60300311400082c0201d004200c03d035034041c02c070114500120f0454180240e98120000003c5e0040c404c0d600181610500481d0200c2c80d1528000a44241c0f5400d841101840c1c035140d07114000c8040c00040000183e12540e00100418038040c0901030340351403420840070442043d541d0140b5010f0448e02800050441840785c4159a8881051400440000011031450508003202070030702020455180d0000e030341c0311040f40580c8900c802c0f20103860b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 721442877 1250 721441627 721441657
    0xc1a041b0e090f0a0c09110d0510051816030c0e06180f0d0506431d03150702070b0309030c0c010504081f06090908090306070206010b0d11 61
    0x2031982801e607605a0155440d46030b601c101d40c42d5a1141c0ca00158208203241c00440060b013061030301151001900d41600348100850040c003084441e02800e006286c0940c40440c0c0710b0700703558104002e104070f040d400390441001c50b0049050003031020f01c4000e1401101840d140c040340741c0501000c159101c1400d100110740040c0000f0340b100d503043c0c0c40301c00e2000c3c1c00402c0b03a0011217070808008015801c0c00c404000341540d081a004641041c0d4031b000c501900340282c100c9a140c0b80060070084240505100c17070f0106500c1001c0460f0750702a0301149103484002646d100c3e5040d50a9080400da0311303010100300d00d0644400c14040b0344c1690003000010020031011441941d81c4c80c2c000500f50312030b001403035040058841d12039260260740c0030301d042c1d9050360034003001008160b44900100c0702c090a2090080503c50f0f4422000c01d00040078098010034600170807110380e540c9070420915142ca2000ad21490464000f000140180e480020450700f40c00c0c00034401054090200c09032501c20b2049040042000c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 721444127 1250 721442877 721442879
    0x150b0a270b030a02060d1a040f051006050412080903030c0a0f030f080c03160c021302040f12020108280606080a1a1c030e06120f070c1a041b 62
    0x390000900e00e4184056150900041440d0740a0580d81d0703604440c000e51101c000d00801080792a9644003c0c40c203414420f0810480300c0400c0801c085920501200b200c403a03c9138108658880300040e20002001940382c900d00e801d107400c0244241025004000706160000034203811199000c000355008555403d00b55004841c8620781020000040441140030031070700301e915080c0e0b50086142512030303818104030914503900c00781c0c050a01c2100c19810720a102c9652000009a250021490580d21316800c00603503a5080440c52000c07002c0f15400302168000440f460b50040c4d922104064103c41c1308002140e035000720500a400d261000ca980441051420000007000c90b0b101e03420902030321400d507082000c101601900c0c8848548002c1207900160000547e1a05e46041340d84140294043c0c580740071b0004421303002034510ba22903042008001450001d00c03c448410240310ac0d000b641c282401c00314461070340e982000401c0409032114030349003500c0015060041c0c94200b1b040c2034a01c0c0303180c0d10a003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 721445377 1250 721444127 721444169
    0xc05060f040f09020c070e06210c04110c0705090c21070e040b0d14030417010209040e061909060b060d090312060f05060d1b030b040b0607150b0a 64
    0x140c000b8454000100c07115100001c0203e901d1007240c0e03512116902500c002414256044400f4001420a03070304691110400d032000c84020701d61158881d68030014140c510130340400c10003684c106590550110004226201c507110340020071504071902a030301c110f41965085c18007074190141c03504106004c185001e20480d511881800588151840e455650482e000030b8280f0084400705000300f50000c03080184140030440700c03645040d1868400089034500354545113800c40c20180840c24880b1a9004592500b86107091b0194140c1c44440c50020440c03454118100070721103100c804030030301c0240d4400c07150041c0405604041d8041001034001c3d956624991414401001140c10070f900140300c401d00c41003849800d0180004a80c1c00303403a41218079080104210180d44403000c0d414481e07a50b9103c0f68030705100701240100c00c6140d40c0340002e8007801e4030144000d5807000310019118400400040d40002c400040d407180388889400c0004d13680c4512004119001c070940c11034041d00400403e0340c144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 721446627 1250 721445377 721445407
    0x30703110d26101a0c100227040e07060804050c060f030c030a060e070806132d090f0c0e0108031c0f060305010f020d0e01060b0733020309160f050d0c0506 68
    0x1800310b00c0c045800c0c1b20b5484809100302e01070581210100c803d0701e5104080c2c00c1c441c1408400090008000040c0b040c0c0c480052442c09034154800360114a12008020500805000c0320001d070900b0740e0410b281120828613141d15110003000148225004004074004035116407025005e0580740e40c482d082d40c1403800025242c008200e07204c038403401030041c2105d50f0070304d01d000b8010188048030005402560868421860461a82c04507180c1640d4420841c0800c903400846001c07207009804150440341480c1d421030312480d0582102100340c1c000c000f010103500444246000300d4814130000680e900d84021024050907035680084c16030343c00c00d03480501e1801ca43d4001d28208403500b00030041000c021020a090303580030b10440642d0704040c04503001041c02c403544142c0c0d526000f030b1020382c494460048441540440149600c401380d0100130008142002c1040c0303410b0702e5124180c0d8009928003000c0303080404c880c0c000c15005100e20103c2c4001c220320340c0c4600c00508001000a80c80320003503c04612 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 721447877 1250 721446627 721446637
    0x60807050903160905070c0b130f0203010f09030210050f01060507150c031a0d0b040204050c1b03070b0105030115090f0b04060b130b04030c03061a03030703110d26101a 74
    0x4055172503c2d010400503401007150240d41540a800700245565079000d4020480391000251001c1044000d6000140c3d800c3c49400e41d00c00d42500c00144556032428001c2ca8610b94841640740c1c14501014071150041035640300703046a01500d0300700e40c0c2c0e601c98584000c0e80c848008461a0031410940c1895105030160071600c0d40b241c403c0c1c440000700b0310300001c00c000c100c51200054500600d00000c50098100790304000d40c4000c02c030308054031300044c901207280c000f960724640c0001600b02050180070000403241c15801460201d00170b00560b409114059504101c601c5017440c29075980d103d103003144a00360418441c82c0c000900800000fa66500c00c02407560150100102e0310402c000f0218420810b10262070584c0d03081030018006a05640c1ca0400400501410044d40d46407501c0c800c5c1242c3d001c1004250785882680c030b0907440b5220003011403802c40800032000c01d00a080d81984030520005209084c252016114007240791113002850440003590f4105000c0e0300441c4007a1265401908020310b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 721449127 1250 721447877 721447889
    0xd05040b0f0903040308031b09130b0a050916120b1905101704030302070204140a020904050603011a010c020a152616050309101d060603061006080705090316 69
    0x403403980d18002c100362a803003107020050101038240049010403606c01d45144404101c194a82c0c6400854000607501400028030400e125440b11103480b12030030f0074200c240c002c002c19604181a4140310b00d644201091800c0320904008002900c0c0403461324540003e4140b00d00540000000440c4403c0d0004c402c444c5e0007401e02070400c242044401c5841607030226040017818041c0d10540e100e81c0d0f8210701941c0610000d0f680329443c1d500f00d03510450b00403c581c1c040e00814100588c3d40384403000f4003054510040006100c0d0b40360021540d6002c40605401c42c0001c024600321140d5545840011102c2c8411303003280e410b4154030030081000a401001400a614468244a224507030301200f20140c10005c403118107041c00c05041604e48640500041c64202e4000420784510203084819401110406031070b034800348020750345098040006000040e0172050a401406080c5400c2c0c1905010007003a100300e2007000f403108001003001d0712450544644100c014151420000306a04035000c03c0c250f40070344 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 721450377 1250 721449127 721449151
    0x11030c040819020a1203030e0601060305250522080f03030718080c09040303021b1006060305010320060c250e0402010206010b09130f0e011104080c0906060d05040b 72
    0x2182c00c600d008019080c0c0c42e401800881220f08002200390780c0301c00b40c1c0089040c540c9800400c02e10304402d1200d240071741440d41e130004071031400c003103c3d0400310b02d4864180d500440e001c801007140c0e130380003003210001503641303141480c19566511021a46d0400354890000b84c0110400780000701c101100450240e089950340548440c80c0180c9070b101070b05a4031072803046a001e07420030030103803e00e011026407140c021300b001130134070302e080214142d80203c005149001c1d401207920042421458441d00d8080d02d84e80c07030100155030641e61450800c1c03031084d1009041100d10b021924003030740d600341118940b0004c14180c0d040002c0034040050034000801c040481544000da000c01c3e04640300c0e418601c5140c050340188166488c0004a0200d5402180b110350090311614001081c0e07420b40c001d2400405d0030400c0000c2c507440c0c8045190071940064402a4042000c0008220383c517400210748030f15031012500d08841c0e03122100003074441d1181207200211a42040c04000500103400300ba203110b0300c1c03e0a42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 721451627 1250 721450377 721450393
    0xd060509010609050d030c121205010b0a0e0d02240904050a180204050901181a09010b0d06020c160b1b121204080c120d0f090201050412020411030c0408 67
    0x10032429034401d00561000405560041083c1d29021030f65800e41030181c04e005140b902161521a200040c82c0c0c503c20200b404490030f402146c419224942c010800356403485c0c00d2013440300c0010240382071700c0c0f00548164944d000d00d4066548006000d4041820406181e040d842c007900020000e40180d41642c1c41280f0300710014001d05668041c01d050703440d0030300407038a03841c55547c02c110003400c0107044070195658404400da95182d030400c1d901d100c240180014040e000150f404000d481c04002c0c0b4020301c6905100750241b1035117038801d24001d05940841d003d0f0700c4550940c80f09140040c6110306504d50b02450400042d81d00b0b0340d400508600e00820b00c1024505621951150780745012009900c001c82c0c20000c031500c600e80c0c1654144c201d4441e200c0c181c41c000f407200c803151501f0189003c5150381c41c0c000980400f00c8209110f03800303500003940d905200c0c00d101500064164000d40c459608110710b03d40c0d40c10110b40d51a070050b9400105581b0298403800c15542040c03243c6c000c0c0c000c1050382e11400340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 721452877 1250 721451627 721451629
    0x11010f060b0307080417220f030b040f081204060e0c030d0815150c0601260a0311030c0d120f090c030f15050106080f07170a020306060c0709020d0605 66
    0x910000d41d1602500e10303141da250000d044841c40307002007060750604444c503203900015900070300410040d06002150120300305000c039440901e442a500c551810640d9040c1000000d10940c152680107402174801c0f2011803c50810000c180720b28800451420030503070400c41008a29440801d80020728411075030141018400d06070794a8441c0210008a40080c3c00a0003050100c0c00e10f0514610283c05641d001010900954294000d011581c415404c075400501c0b404a120f0220b40748840d01a14403012456074032000c0307854240e018800741c01c00c0107001084218400420031241c0c075207901c00c05c4940d400c08035200140000110a410b01e0181d08200000850b01100d008a081c1075070080d1120201c1483c40e40c501191085465044550b010803010a800b8a4410b2007041d00800e81030312820280e2904a8418280d200001c144a00f84024052042c0145000d60380c0329034041024400165a52201d200240c040d0044c40222021481509400b00c0c9012450300541555001c00702c060204645403c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 721454127 1250 721452877 721452881
    0x70b040f0608091f020403020301021c1b0815040b120a12020a03050d02030a0b1c0c0510081311030a1b0504060602030a0f030b150306190602120f130611010f 69
    0xd96041c640c4d0f0700410322021456651083c00b40c0c0341c40f401c280140751540d603a02003400d81e001915440540392400b4001d41902015000d01c0303247c4895007008c8402d00000400c003802d007031006815904012006480c80c016511550312011030160000e1080c4d500100c020f0b00955030b90458901255603d0b16250030b005e1841c000242c5a1407941e05450ba142006c1c0981c4000c802908001c2c03101030700d00d845485643c00740e120200d0802c00d0070f010b481e1000300d5210b1400c200407060308590206004c0e8140c03c840c03076800340d4800c055540290100752159000c024a00781124030700d80310305025915001e00805c0c0400c02141c1c4404002c1c1040000340180c80c55510010441206c0740e61140c1c40150f00108610301006104013240440c81425040008001c40786801065024040c551092080034000090003941d02d4500484c0c040250702e00c1c3c03002d0b0030609101c8000e4598080385e0507440410800f1801e0325490100a0580b0b0f4800c001c01c0440201070358a4900400000d6802d400c0b000b594070380740f03503401c55407418 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 721455377 1250 721454127 721454131
    0x902030c0906030d050f1b0a0302160f050f01020109120f1803030c080c03070c03060203060301050a091203110f0a08010e010f0e16120603060b0a2301031508070b040f0608 75
    0xf400383c030f200e01c50306006581d140c0c41071940c040010410000c10221200f08010f526051100310010240c4040c0d901d000ba20b06a881000e6441c1d90400304410401000381c0065841030b00e0080d01d49240300400140181c0c0942403034080100481d412030202501d8541c0040303074200c2480c480ea1850405624001c241c40701c40c2c1a4000500040c40019480c808510700400611524421404407032810320540c82d0458424050703082258016000010b02c5a0752400340a42a000b1003581003c0010050325614031007105c80002aa809142c0c40700080100014010b099031818120601507544c1d49800e0710008100c10002d01506c00d040380414000310b128000780e440c1c242500c1c2d0040140380c0c952105452007207000c10a00400041049501071050312000500401000398803c0c00081030044500c010000d5010003900704e203401c1d201c0403090345c000749461010f030710b140d030028200054010603440d504ca1546059410440d403500c80e05c5800030b00003d0b04002041166540f07a0307540c01c000d40303400c01143e1080003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 721456627 1250 721455377 721455379
    0x1050c0a0534150302160b0c07060e0f07050f06040902031f06020a080d0b060702040911090618160e0a03050607020c0603130b07020304080111030907090b03031c1d010902030c0906 79
    0xc50390760081076034001d90080c10801108001c41c07106c601b1940d0b0720640107504803015886080b02140c0c0c030040002c1400740401c0135085001a224040130340d07040f113945112501c65217108038900e01c110301d01521500111800382c810780409540d24a44011900b00d00c450340d03205054001d998101c001403661000c2001400316901061a0349440c6411005001808a600701d49502c0714040050b140160765070320400e4401407046e82c0d07002402d80380ba0f040015042000f0100380c0605070710041da440303501d607075148c0d0750384400d00e10030880c0d0310722040170b00302c1c1c154400e0000e03613030801c1c2d1142020091100025000c0d200b1229582119035a00d1102c043c45041e00080c0d9040180070700f00d48196002502884003079034081040c2c8100c0b410150303189016400d48044500c1040010000000c0c04242c1c01c0c00d01040016003034006003801080495404240d4034070501418040450394680a040c0e10081c80c1c000c1d0a03030060003c80c0c0c41c807150040f410a4000c180301c0f54221702c203208100317482c2d0050500701e480d9441500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 721457877 1250 721456627 721456649
    0x1b020a0803160201060e150a0e10060302031504110418150315110313050c0603070215040f200f030c060a270605030f010e1501050c0a0534 61
    0x54058a0b51070350095030305860255500c0b03010108030880004075480c802c403021010000d0300210f0b682401842145ea41089000c0b545141c200400700f07400100329400c80340c40b454010b07603a90b140d0700c000c0b45c1c3d013000e4503106600c00e04000e902c600208440f8003070825139003001c81101c0c02440070154403049030070581882d1020300d1100010804102c2072404d03802c2c814010240418130105241c3c0081c030540c022117890a104500c1d003800001e2207000c20840b559100d043d90003910754200588042e540b998010b2079954910301c03c50000301008841c800030f01200b54414018100b500540c5690b046c1e50325001c0b1aa0300503042c0c61040709481c038001590052040010f025980b5051a407941116442150ba580101403132403002c02d640c0d101c0320100d1b41c0c2d0090099596694690514102d03c080c503410607800b81351080ca40070280801c0c11114061050048000d0034215501d1842000c81801c0002c240d1010301103003c1d54644240e075140b500f03000601820880154401510038815600a428a500803400002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 721459127 1250 721457877 721457881
    0x806010810050603010b0a080f0c030a150c0c0503070602040501030b030c151803100e0105060306041226090a03020c0103150308130527071731061b020a0803 69
    0x10354142d01440d003094001d40042259054940400c0c10000694000d088591160602506c0400d050117203004080045010748140a442c0d00d0300345600840344a40d481c0540d4880165503080d006255907010b1590110540703494041038140400207410034403030030f40840e06100143c4980d103004103101e80310910052000172203040519410b00b80c2d0304020071004008900110710201341da0108481c0c0301c08078000d2008210362100b15000b070300350307200504158003e9101406101c00030b0100ea4000ca100c00c2070385000310301000548241c841d070403041c0415510603014281032194001001c140180c04602940031250100206001102240c2018021000390800309000f840000c1d050401010f01c150001119804181c4910004010b00b410314540c1e051069030310140f0241409461b403ca41c09005801d0601c020694820400f01020000f00008440c244080070400f1059980c0c1c03080d503e0708603101d080891048a0300e002001051444010500521103100c80c040072440011010b26455125040710300315 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 721460377 1250 721459127 721459153
    0x20a0b010f061e0306050a0b090a05150703030c020c2d1e0409020303041d010e01081f09030c0506090a03030608010b030a0f05072112030b01050f09040e12040303020708060108 77
    0x1058580603c8410507884640004142e680c8a00f5803003c0c0c0003d241403980c1c1d829003010065159841e42c001c60080402c0380100040701c0c2002c0944190681505000c00c0311015444101c0c2401d80c2e00c030106900441e0303492104503001e04205650500c03400220149012181c0f0801c000d0f005480c0381c00500e080650041c2602c0790305286d00070190b040e1024081300d04298644004034144000c1d00b22004440e15a480100070320f06105180070300601052015014102d2039a581070950b8054150350400f031a01c5502a104240c8035000c00d140c0f594110056135124100b1543c40c54441e5501413007500081e041160125142d04107100340d201c1c0400045c000e2000e08400c0ea110501c1a0b460401039519010743c5000241c1c0003d01e09040007000b11460414414095a14181007403140c00981707241007500e040103810042e600802200c0310301c3c0e00700c1c0e200317911421204c000038042d00007500003414500941e2640403c048040028100f90f92103902a900c0150329a05801e503580801d1162041360b5114081c09603007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 721461627 1250 721460377 721460417
    0x70e0d0c05040b03030c0604060213170a0303110c010509010f0c110c010c0201021203160f05030609040201050d11040306050609130c0504020a0302120702102f03070915020a0b010f06 80
    0x1500f5020302540c0c20400d00003141c82c20454222000d44035650002441e9200c41034407c0010054880050040311800e00552441e80d90040000010141591981600810346101c0243c808444480d4024003240c681610440c2c00313020070324503a07400b003403c150b0340e030b8402d07030151442e4a1184000c400030003960031000c004542550304840143d05500403a00c004581e0019000110310030310b000ca80125010000c084000c080007150740300d6600f0850300740113100c095680c5000b940e4000d41c0900c3c0c107540700c84156800300010011141c600340ea00e03200140000402561303801461152004032900952a91002403080d00700065000c01020000e17055000d0283c1d1900e03030702800c03101030689801070400d800e001d82e8480845c010350b0020090b0340115007107207044030325025011013800c035140058402c9101039026140c480803503070446000c0c1030105c0054016803191100900805a002c1c0d0b0740d45400d180400079446032040801075400581c048004513164120042c444111201079680000f14900d00b0b1311454 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 721462877 1250 721461627 721461641
    0x406230d030c02060d0b010909060b18060d020d051f0e070c15060b1b0318010c020f0d1406090105011d1003020901180513022803150203070e0d0c0504 66
    0x24040d0b078403030940141c0c03503402c00340c6800722280a000442081c0c540000d00000180c1c0d005011aa040c40d8051001001240541c0e02c1d0f002030b01541c0c40c1100510b4002505800b070340000d403841e0341c4085040c0d42c03100c2003504038070b0003110050110a01d0140341101038140c625a80641c030308103d0719201054000f445258182c440b00e004102000307036160740c85901030075030741d456001c0c9600d01d030003140d0800d405905131aa007402c41b40d40c40043d803401c2c905510040c02210f0105425040c4203039105140d040d522a565441040c0800401c0e80d006c805c02490f08504c0c182464403400c5051107080001440b00d0f0341441100c2c103aa541001c00c070000c030f40500c0086a061401002d03440c10030902c080000040e2104510580604440790b6150210407020045504840d8002c080317915000609806001503100c010071014022100ba04468001129500343d11410700a0f510080c02e604c0c2100002404211541c081c50141d070841d500c401c4c40d41c25075820000c00001d20f507405848800c01002c200820b1a00b640b11078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 721464127 1250 721462877 721462883
    0xc1f020706090311100b01021b01020a05070807031205090f061605060f070f0815091b031302040b0405060a14031213141005180d080c07050406230d 65
    0x252400e821a03440e1426100300d804110b0205440006034024030209100b0521390000b1040304101111320100000d584102200c004442d0300460111070b0010b0b4402d01050812a401ca0100e4003020b58441a6680e00d00c0548410361301840074035142c0c0801c0c1d20400407070384590030041c041034565040d40d041240030350104901021034200795210381c0000d1418400d4900c14050203c010341d1342d103007082c0041e210940e0711901344200704525040118800003070030038036845102501c080f142649e030700c1000b2003048440d42c801001c0312404000c05c14042010140707200540d100f40c800340207080b4010b05000c140d038030030b41d505540030300380340801c0c006d40d06200c00d10b11800300001c04507120720000518003607041d840300e84000b80c0145130700c0c81803042101ea01c44d0f04981120a854400c034416180d180100640102020786103d00c0c120403810300285e035401c01680b8681d4103e5503180d668810032520a40d6007141c1e1103103a016908140c1d001518110704d0310101d205251140110070b03a070400f001040383c0141500811 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 721465377 1250 721464127 721464131
    0x102062404180f0c0e060301060833150a060f0507030c0507050d080d06051f0c050a0c1d0f0610080a090f14060a11040e070e032d030c1f 60
    0x4030080ba1924102142d07584c01460b80d82c00c03550824a48412900f00144080d0007a81820002c102c82040000e9484030110f0a2410300c00b0142c0940841440003001c103040341e1003603442028009100c100c00710700c40c44204100c810921140d42e8400c00d071181c65030280c40c40c000c01e81c14814000070a008060f10200c4c10700c25400d4406040d202c1c00060b02540c600c610607607081002207032400314081ca600c03548019080440d81c1c038580190508020305030034440e0104008010340c0445000801c9410800303e8070495018823680c00c015203130f1110218070400584500044000f0b04007250300d070584070f69818002e403c0580301b076014030b0491905032042c120182460401640d07441c9031401040f8100074110301103110700e5120b00304041410a0714a4400090700b05900589004801d9149019007022241100c40401103452590383da407000390f03010b1900750207450b013500580881d201000700c01c1a031468a07401c52440b501c0340b88801c0d44801c0e030340d0149100c40185540181505d520b070101c01154929610000200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 721466627 1250 721465377 721465421
    0x60906012d03051b01090b031302210703110315041101030c11070623042102040e010f020a1112040e130501090302010f060b0310050906010203090406080c0102062404 73
    0x240515040c60b9480c104607040d4401d9184c4a0b641e446812000117040545190381141481f10207070421180d12103000348140c103c124079003610080690404040050380c01034408a569030b0510482000101090902c00e0080c44c3c400e083c1d80b40c2190040380580d4014156500c0e807150200150000c1c60038500701c00a00c92400c2c92014800300400194011305590381c0c4000c3c0d58a2070f032141e0360100140402858080c46c0030b0005002c0c410504500f041c3c030802e01c4941001814883c0046402001d0b01c1855555950130203015103808000e03078004004c80c0c1c40941c1c03400c1c0400008500d03a078a070802c18409003e0300324104400c10001d265401b0343d541003810550780c0d402d5450366995045c2102c60700c94045000d81d44a0340100f281131203500ca6900100360b540741c854950704c1c0204a0b050084254000e4902ca03002c003001040040e4404c0007a0b5034410405002004629100e080d82030382c4040380e40c1c84a0061042c1800580306065a0062018203d844540780c0a88d81001d001c20001e00062401d0352100d02585003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 721467877 1250 721466627 721466633
    0x2150703060909150617060619030f1407060509130c020c0306040f1106040302061608130e04050706050f12070e0d06050601020106090b030a15141602060906012d03 72
    0x850f400115100b841080c520641c058048416203810b6030003ca46441e001c504000f0201c000300d0801e82c41141141c0c2217410441c01d880300e41200e8100d810250140c440c01e40d100c0200441000e40c296a0346002088030135440e41e503031044465110300d01145810008841566040ca201c1e40c000000a5005006440348980b851011030302d0000100c4044e5004c409005110080c8050408620740130842a1442031800d810342c2c02081175071084901082280508030308240c10300c90071038250ba05210a6082c440903c1c3c0c1e80b8020290510310a41e41510b150250030400100300f8002d604540e92107002c6500c1c0750400c4054401000340040040c6200c061288041c0381034115503403010807040007441a071300000c480c248a0300080c2120310316085060420324002c0b00d800d41d640c1c001010500503511603516028001c03810311400c0030700340c01000c82c41c000d0710030310900c440c0104070110f0342141401a401c6074a1039803525030b03c42c1d54040a10902c401c01c02c081942c0d608500c09819580100c40b030107140380e80a1a540e0b6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 721469127 1250 721467877 721467881
    0xc03030e0307060905060a05070801030f031206050a06030212060a030b0f100b0f040e0610080c0c121303151103070e0f03370c060e0310050103030c020f10021507030609 74
    0x11405c80300c0360841010024088170b14443d0710b40003211403920003501e6043d9039985841c514082005821f100403104e40e21943c80303035074120402600f400b0781903c6a0f1582c400010b806500b0502c0f03000003160b00000012510f0030305101c51000c0700c4d0408030182c00368862200c0040c0858010300b0410000b90162004149141c1810040142d01da80420309603565250075004064998080c15141c820300110392884401940f1105654100c1d0b007812145039070f81480d001d683c0c40d040007600750960f0303100d0114850902102c00800c2e081100d004928009808019101917000c40300e04500c000e840c0d0f4414400302d404c0501c80c500c40a054603000e040d4107203040c54017000034a00a40c420104a008503190001c0c030200e030514584000f6071013004900e400441c0c1594980d00ca00450b80035500c10000c1d0700421403040e135401c1200184030b0900850401c0556181d00b002003c501b941d0320180e002c0d00f8044041020b505024000707100c208081e90140c0600c005080e446400c00780c0180800d4101a02e441c000310711400380b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 721470377 1250 721469127 721469141
    0x607021e07032a120b0604020c1213030507030b0414030c0703060f021c050403030b0105280e10030b01020714010e04050a02210910050f04080d02251b060c03030e030706 74
    0x3d8126888134083c5240140c0c00d60402021240118014000c902c51840c0c005061940b210107074040d05d803034180030720400c0700d82c620542c806000b80c0b0840c0340010510405000b800d003d5030103203c50701c10410412584075540d20482c0c0c1804481c0d840b500080020821581c00720084002c10b00c0301600e454481c882400161840c2c92080455550314000d000405401d8460808401000c1c02e10905100c0e14501e50181c0814103528014070888140c00b400300d00d4071a00c00c03400060001061643d45c4491050010010020b03844868058842c40070081041081915000d05070702d0165501d400260301e62051002812018101007000c40c0c09218000194225122403100400218003024952400040d1686441340300c801c18640603180c5428401144410f0100390351043d007011140d6030303a90864007900c0092048543d01e100502c100036910305500c0c0c46c42040c80000340900010900812920440c0d010000f1511450300400c0ca03241c420400207000360801a182109001640d09003100c40c0c0300c0209880c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 721471627 1250 721470377 721470389
    0x20a030f021f1505040b0f240c0a0512040e391c0911060307020a020d06060519060e0f060405130c0816080f0c0712020607021e07032a 59
    0x22281011410083c043c6003a0040004540a100020004000c00c9807100d012400d0790252441d80c001079800740c060785426940c1100399200c1caa9690500ca0007a8032208890030494450203041140d00d1900d0201040e681038070f02c2200354001586a0307001183c02402c0030710845008080c04001d041c50340d0305500c0103850414545120507503030840002001c0d072107158846942c04071751a002e00140880c402607000c00c010101666070903a00e44074a0740c1607280042c061402540401c02c20428020000780e0b030442001c0301c41c159114458034180780c0da882110300c0c050003103800080300185010118a4003000020f40020003400c12440c2c1600e420100384190a0803164080b06916068800501030784038019561050003035080a2640014034001050810060300d0302d4440c1150402260310400914100c1d9802079001000d01640900c0d100c3c044c0d1254000c0b101e440160141c550b41c600e01c01d00c6811081c1c4a00c2114000e0003400d401e540e02e030307500080b0001058041c0f04400280384100d50b00401c442000d844 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 721472877 1250 721471627 721471631
    0x310020a121505040e0a1b050f010807080a15090f061e0b0418021603020f100903020a14070b0c0109050d0e09070e03010e0703031206080607020a030f021f 68
    0xd240300000e0705100035000c030300800c10b19201d041c01600c0540c980303070340c1682c42c12500810003481c00300c0b80c245000507011024003020300041070a40d102001d81c0b50107003250010346503035801da0710003001521400f0040750441b0208850710002000e106076980080543c000d004c0c1c45551158a881109080301c01c03080c140b04107113a451070284288051038286401020140c4640103d903402c0c180b8922082c001d6220303180c90301c144210902540c0c038498041d40d0000e00400c80300c00465950b0700b0000d5442c0e070b221070b070000f4030700407020384030351030b4030140614503911b071305034005101c0d903d416070ba00d003a41c281c0e440944010740103a00002c1203008007c070081100410900001c03a00e070903242045c40c102380b102018141401801c1545c9040fa84402c00307000d038080040d0420308914205440420302401e200c03840070300c0501540f81c000c400c05401105003001c0020f500410418192200759850b0380e040265a44000b592020190f28006813046c0780c5116a000213105464844150003905040310800780c0c202d5441e65 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 721474127 1250 721472877 721472887
    0x112020c0303040501241403030706020d0f0c090807060503060d050f0d090605120a0203070309020306010b071b03260c0106061707020d0801090f09020307030b18031207030203070e031002 82
    0x40902039003000e61b03403810708130400303144028003045400e015200b030385601e4044014041075541c0a2007038030011900040c05641e03ca541042210042c401c1801a9101c0362601c20550f4042d841103017260282c80907a0001e00c071183c14000242ca00e0380008090607481903c40880400092003445900701a021010003003a400210441c040c1510845030014020010140000c20010b10960b60240d04403428450040e6241c943c144114050652200003a402d40303d9000005040414040203192041c01003c00d00c0b40f014480f0031051808200b88006816403001c04010001c10f482d007101c1e43c150b240030304001c6190841c481d2009084d64460b6024201040101100018008140f804154040140e10250a00e0401c01c0c101901020041c010900c5051740d424251b11a14810791141103a02c0e0000c04590400c0c0e035034909608610000c8813804140e00341c94920b10410351000040d9840a400d50102121950740c0150440094000510900400c111258804101d440c1404081c043c061030140150ba14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 721475377 1250 721474127 721474133
    0x1704080d0302030c0405013b04060602010603020609040507110f0601060e040c08010e1e0c0c01060b04181a041e0b030a02030604061a1c05010b0105090f09060112020c030304 76
    0x2086886000d002450300401c10812503900f0101264181c0341c00b4200085030210500d8040210344060075a12840c4101c050007500814065070344240304031040342d05000850b2156001c07400d98405201c020b4000c10180b100c820140b4058115035401907191422032003100c00070006c545070000118070b40a040d00001e006002596110b103800100c004256010b21610b42c9000f070003021640705100e0407040c4011003011400000806502040b03188200308404414142003501c0300d1030303501c4a08110102d40c0380080002d00c03c4c11030000e507821a258680500c4a86442c1d60103040030b00380d011044107050b4102114030070241d445224145200b40d0000300341c84d103070307000c41c040c0000c440c0c2d0007000902c070358007640c04600107940000f4541d5000d5440702003c150f01040c1c00114103111342042d1740640c017010361409a10816490104456440c1c011300080c001144244015103441c0302c0c6e6400c0d82d4010f00715881841003400c0515850b6040307801854036812622a414014089030050f4a0a00c81030f000001803000f4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 721476627 1250 721475377 721475383
    0xc070504050f04060903020c040914070618060e030307020d030c140f1209030109060c080703050a110301092003010603090b0906060303120405070f270c120f09170408 73
    0x1410080d9010000782c2000403848415400003807008000c80d84401000081520a020301e6441d82809001440003040718649075000f038030701c015602458450b2140c00190503105411000140d030724071010504050601404070f501010340c40000b601032104001140060f01c540c0b0042805a02031341e14a91108103920745401c840720400f2040403d41e0100160603242c603008503449079410b494001c0240e541040c0c030040b9024151494010b80107034500701416110035000011240f003002c5e03a41c1c041001c2da41d07030b0907580e04941e0000c2c115504c0002c107000501140511344d00030545140c0c1d0000b054000d0406509005280c0c1c42600700600080e03c0d1000c44080205028480390054940405040d82d80303401000700e9941e02403440c00c0c07850080780001081c2880414440700014003181e440c01c214243d110000114620100f01c02c4070000d04c00818074441c008903920402c610241107985000030329616803900805003035440468811107a8036440400060466005805910136107034070707962a64640304d01141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 721477877 1250 721476627 721476629
    0xf141e061008062d130b071b081b0601080c0f120607051b03030405010b0f030a0b190216110a0b0403030c0b04030306080a03020f0105090a020a0e2a0c07 67
    0x120218500c0c814040203001150f00c56205924641c80d42c0040024450b000e070180e210300007007040e1074905041c0001048000105206640919281403640d196224111205071441d1507459002125003062400070b101c25008100444000710300081c0040c0c00503003241890020f9001c502254080608140e250070001200010301e002100c0b184103020600d0800703a142c1200508181c1045000030766840c1100590680c042c460081f402101d4582c0f038180b60040c000c2120b03c61081c07044109411050703851a001540100bc40d40c000004120760300c65101c0d162004650303240c04d501e9a40c0034803200440003d880302d0070310b1803800b41100117445514801800b00da0740f8281c0002c44054000c00c0180042070304107401c41030340d80c0d1051010b4590f03aa1410708400411013500004542d0141903500c41c185940003c2c002c1700314030494001c200c1900e034008a01c2d582c4040d850029040844580f080001441c002031143d1b01140c50207821010b4420340000010b010404000e607409901c0c0822241c042030001c0103900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 721479127 1250 721477877 721477891
    0xf05220f06090b09040e03041d0a11180d02030c18060405010b0a020a08070f06090602180f010f03270c03060f110f181f14030f01030f141e06 62
    0x581c02c9080140454503807146440440c01140c4602c1d1180d421142081240d008200c201d01e40d0741232100181044115031025148000741c40d003000444c800702c50240c2d080341c50f00c0108003070000301180500140403480b101000203a900d4040e1480048c2c4c241c0390940e00c0544008040801d18203407808400700021901d040e080203513041801c1c00b43e00409131700052459101030700f1214503034850702c40340381103850400451300082c699801e04458030200820342e000384c14816035060041410030518010310003030b440816000d40c0020040c0002c0141a40658810701660324400074510480313a61030b2010030243c01c601021141d210340030008100b8410325200b40d801039070307034544213004500baa030302d0894160045040b8924507440006080703010318024030000d801402c01500780c0d0501081860525640042409804042104800200564078900c01200d10441d0030550480aa900399244d1042d0810300c9281100c0c02501043c44013080382c01045000150465031580043c501d424481807801c160018040c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 721480377 1250 721479127 721479137
    0x717070506040f0f1a0a18020a0b0c1c0f02060f01060206040b07020f010e030406020c030a33090c050406061701030303051009020f0a170112030f05220f06 68
    0x204002400208a6030340040c1c03c440c0c080039840c402d08041c4800780042000514a1141014821403200b03055070f04d920a42d8001c2c003c01c9103600007001d11002c0030b00c940c0020340c840340045061000c004070b440540314203440780301151031650b151801c007903003c00403c5201001c20030842c49c2c40300d52a81000307a80d80c000c071624041269940b405201a640c0c600c00340004040c0418140040c1c00540300f00300c0700040e001014001e0005258003101c680d12940700d405810014000c00101d103400d0f080001d00344e000c0da9440f81c0c0010450118100008040071b2044801d004040111111590080c1a001d8802c2050041c4d40c03c003086454502004102c511541c8003609103c5c141c2010580c25080000007411660503050209940e40c40d001000000d005640154448520110f55081d403621100041d16600c1c0890710b03110707546441481e0080417440c09200e20030700703480c29140c4e450000344540b4482030604502d0800a0618951000c0c0e201c0100103140c078034401940d961800c00c500c000c01210800180614109 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 721481627 1250 721480377 721480387
    0xb0a080304060507020121141f0b0412240212060409051c02120c0a060507110304120816050a020108010929060f1207030b010318060b041e020717 64
    0x4003805034025403101a040c030407803640c85030703d07c0007608442d0846800c180041160303100103910410291000e8842c5240100741e0300c420303424140c40858000940e000080d04604043c81c10000580010180030101c642581410039041601114030420301040c0c0400405a00d40001103145003031040002c2c0b000d486a42002c1618011640218841611000c1c008e903403642d1040414003640740014549804801042c0006c00c4200d0050105602c15464810740f02402541c40d10f21044900007082e01c84d03140301d500204070400c40842552110100240706404180c20b2400d806854107050341f0004080d640398008111102c110360b40091b50601605110b4000c0044028084134400c0b40705014a102c00550140150a446aa00d107410b880c0d12200c1d40c410207a45d128507031922582040c0650f0b607100402c2c204410b14401398024000d8400b4007d4107210007103c0413154484d1000b404004040581281d5680301e0481c0c0700c1c01782600b17502600c240f07900c0075a45415500e40701c0d08503507400d42d5010f001c40c41804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 721482877 1250 721481627 721481639
    0x120106080d20010b0f1315120c0504051b2206050405040509150105060702010908060a090c082a0619030509070b0414010807021204120b0a020a0e12010905010f0b0a080304 75
    0x207040b6410740d1007035581d51200b00e00211040010031036104803036a0118002800107548c008001d449900c3e912440014228503920001e10058800aa40210504a50021508046201001500c4140501c0c0a44010441e08030048074260140d0307007045002400c0001c06101c58140b500865401c0540304005011006600681c040c25900c1030103514400d01c0001585420340e8407c00c0150054600b1000ba83c0b22800d08100c2840104004401101c3c84068090001820000031400b11109811400443c601403007038800d5592801d45081a13990100040c0191030b9400040c003550400c48100d5100041d245c20045001c510f040d0940d0301480344e10004000c00d2204000b1a2021991180c082c2012282034988040c140d0410160a84e40c0c18810404a4005407090703450340c0c01c055583c0595010030a40d120301c0034840c1a80b08007032800011441422140503c2d0518002c1025440c11070800041c5141d1160b44041c00d58160388501c40c00b55858180107681e610344660020002d0068800440c54540b03060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 721484127 1250 721482877 721482889
    0x31608130b0915270411031302030d0c0519140a0302010f1b090e04020a1a09211506010908011e0506011809020306180412020c1905120106080d20010b 66
    0x4d8001210035044107020f20180c85903000300041c450103101d001d80300d02d08004e03a0300d03115150000a80c404d2003000083c3c3c800f42d018500180d403090300f01307018110407003c1c113070b141e00c00f503008031011552400982082c4c80000014004400740c0c0e4460380c000319503081d898250005171203d41d01c80da00c04036401d0800c40d59640c1c005604408945040004404507520740c000504844095400103803a45220f18200d580c0741c003418000e21500c10100d61418103044000c45416541c000b039280c2c520301d680007042c580c0c22006910441c1740c0c08401403406070307202501c907100d0034251903068102c8590200840c03020445075050713000f0303070750b00c543c0c20302c0c000ca100c8205210040c000940c1c4d100b450241c42c0d00101107000ca84607041c400d9032103074103041d43d020281020710b09035804045040801d0014007954a1180252600d042007100702007145c94a025407900301820440d805103422031048056503102d40c0000e0450b400c2c811000d01c50750f00d0700c5202070b100c5c0090840c0c1c0d280ca20b044640003d07915102a070700b40d42c0c0e68a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 721485377 1250 721484127 721484167
    0xa1203020d0311070b0a061208040f0e010e153f0d020604030f0c0533010b03190b030f011b09150c03030b0d0506010906080f031608130b0915 62
    0x31145c0d01d403a11031201810042410742c110048149130b40001e40148641980104200e0b400c00c5c00c80b01c81a0381d18411010443c41c2802908400300b41100845c41e4400c1071208130360056401030070110703070304c01c90f06400c801800c4014981c0030341c100c0c02c402c0400a5030412038555111902001411560000c1c100007521244010030003024001740d2611210b00074480c15100c8200c330783c45805c403003041280321012075400b0f00084a030403503420706034400c0c0c040d0034501c2c2e9954100c5442c10111819034490910061030ba211000a07918456926050404282e404003c80480082c00c01c0000591540d20032840b810300c3c0c205107046050107041d980030002c1600c0040c42520200c0c2900d000c51480c5118942103014000d0140ea0590000e1140b0f01030051000101d1310743c0c103c44000c00104003042c1c0d0b40c0c2c0b10b241c841c00c94400d40020750f0024041c2418030b10001c1803001c0010f104030b0942c0d2070034140728503518518495801c032041d07001c40400c8081450521010701d4100e216080310b064100082d40c01c04206120032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 721486627 1250 721485377 721485383
    0x40c05130e0303180f030c01090b010504180213020f040f031a0403080a05040305040302190807081603080310080601120605060a03050c0d061512060c030516110c0a1203020d031107 79
    0x2c84e598501210134000882d84015507000c0c0c1e6600c80c40701c000380e40038109406041d04c12541c154000030300340c42c0c684250280002091032110309100700343c0802400a4460341103a01550b005c000b4000d207241018001d0010b065035100740403d15040d4207042c180346410340052940882800240310100e50400c103d036070700031090039000c501e81e56646012030346030140b030b031000790015080c030b48035081011044107400030b0303602e01c10071a640c1c240d452007000d641e4821140c440c1c104019110080c404510010700075648a803600318a50071903580d501400380340c100240d001c20018010f21080c08100a07490280940088c2c00301e400c0c40c44942182c03105610356070744000443c030800e0b58031034010401c000c13500562000707190402566030440c0d5501300c0e80741d07815502c401281c20030301e480301940c0054042c4c0710300740c0101d5041400d1410803c2c40141990105118000e1415612443c03140500c26500e004c0b03140301401044100c80703e20316551402914095220307400505050800080d201082c444030299446133070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 721487877 1250 721486627 721486651
    0xa090f06050403051c0c0e0108060109030b06030f0d02060106141c0207060b0603070905330a02010207050a15050609040b0c0f0c010603080a0807020318010521040c05130e0303 77
    0x48515080d10740344121400c54103800c01213420fa0b20300303c05d564440e0140300c0c0d4070784803e4a5a40c1c004011030b60f12404580700c0d07000c103110040070300205604100155015102600f143c0c88040700c200200d18005078074005c000144c0c803034801804040e900c02c07071160700742418a244606080d140a00c610001c49404046084036502081140901041c0e4114074490308002c2d10141c7c0d20700f06150028814246405402d00401141c4009404010503480c00c44003c240d40c0080c10030407070800c5800c2c081e94000c40c06202159028888440420400d108401e41f0764840c0f40c0180040c0c502d085c031202541c10050006206580c004108004201320401070342c2d000e81a03509060f603401209220881602071792802e2100d541ca400c6001c420481c090005103244174040e150101d442d905d10f40101c2c4c2d00e101c3c048030051000c0444c03011040f654010b41c042c158072006980d06145811019010107280c1070116010303a0002000741c010015410b128416245c0085000401c0c01700100c40708010303a90344800350881803610 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 721489127 1250 721487877 721487881
    0x20f0a0203071a073507080702100c080c030405010e030a020d0204020f0705061603050f09190204111206102f011409010209040f06051003112208060a090f0605 70
    0x264100b41190280d0754080b40e0174001646500d00c85511555646200300c643c02d0b148800001c01d83c9503416941402e5000aa46240413219400c2c4080083c9a248030300c00c0c41000742d1480c0c00104c2d844080c02201862800540d01c4174030b86070004200c0702c448041d1078040c0d0000d201070300c050f032a0b2b421041550394054030007607078035000f900c00c0079103612801c040607059004803400d0000b4090603003038100c61440256410722082e1107424120f05a014140c41707440c4243d100ca840c1d2580b840101c00c0c40d03000c282c00200700050200300101d00c00c2542c0c0c40300181140c06142c072401c02c00d0764070709088015250f68852070010954500074070000a240e5070718080c01100c0078016500e00705d1403000d4200d001490034908150300c4034180741481074040c0d0031504946226500301302d6001008002072003200201c4400504021b400c45200364258004e00c80c0c010002c50840040000c400005862807a569400c40e0518440d00303420710700340b4854142a40030b429440c0701802c01441102103145210415480c5400c61340c0003c0f55 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 721490377 1250 721489127 721489169
    0x1e010b101d13020409200c030a030b0d0c03060b0a08010501080705152b0b06130608060a15020f0601080c010503071b050105040303050618041716080d0c020f0a020307 73
    0x2842d00520220000c0c0c0000b40210748050b80d50000c0da048220b01110900e4050020b140610500800c5d143c005136500902101504600c07a40128554500152284850011f59214004911170b580c1003964800d0b21140180101e0610b4001c11002f0070307804000304025418060380d581c40d00014460503214821001c2902248503401c0101c139440200c1c01651004a4459118000848050207154883d0740c039210035601142090002c56aa11841350943c024070b500f441c0b810750b8002c90261040c1c0d0004001c0b4800b05400c030040541c1064442290000c05001c0c80311a005841c121058010700e079180c016021480c05a6005800d0742d0f0005900e003407041c56803410140c3c01003e410110340140840d03081101784824140c1541c00303280140f90a0718503502e240d20040143d40000e0042d980240803c5414a00c010000800c0c0c015194406810209a180b0b06242c0c8034105250440300c4e0145089580341c1220380413507010807590400c1444400038044d420003030f40000340ca400c0d0702d2080f6840c4d0031000c460343c140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 721491627 1250 721490377 721490389
    0xa020a0e2d01090b0406080615120703051503101b030e0c1215100312080906012912090610060e1e040216020108060604030b1501050c1e010b101d 64
    0x1a1841380b208030f880f02c0d9a000014031550040e200140251070300b031a2080112820400c81f4401854603041c48955200e600e0100c000f030000410400b2100d01e0010049141c3e5410301a020100001280200741b00018510051024503000d00c000d06141c90b100055441d40000305410803020001c440c9203e156440740b41c0c140c10421944100c1c40c001c149441085074403030860300d000341900d0064483c060500d22103a001d641c545030583d000800c84e80180010000c092401a00e031240744407000b207100780d440c400c40340c80c01c2d02d401003403041208411603010880640b1003004415070201110305401a000d18019002c0c08502600107907501903101090030740d0032203000e011b542c074a0440c040c2045699200108801480b114410740c22800505803402062661800c18240c60075240c005050750305d50346174224203015054280c07070118140101800132803a0383c01d040c850011001440140035841034030101c5903e0860704d1200e0390078495aa203415120320030303a000220584514404407441c005559100000b80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 721492877 1250 721491627 721491629
    0x902030f06090c0105120a0c09051c060e060f0f0408040f0803030412090b091e0406170106060302160b1005100c030210050105100c0c0b030a020a0e2d0109 68
    0x505803042103038140e03502400241e036a1080b036100042e100f60a071072900440e814400c0d50141e5460300f01503404100c0c083c8103640080c504010368200340c1e00300c5a403500410072804904001019070082c2c40713014410b101c44d502481071861580380103400113191000003840c5030240540800c4108104400103801c205d0b00358210380c083d10721001000d440075640d01140b952940115801c8614034003840203203d00500404e004d109a60006110324180400a030502440900060080c000d522002c8444003140d1980c3c890000645999128110501003624809003514200d0303001c40704040c8100700d030914110601c903205280640c030500c1040c1c2c0761601001256980707103d40029510491a00c0030616442d080450001c0451103502558405225031200104440c0c00b4410280c12150034144403060354403c1c9001e000c01ca100f14054040e103500c84040d001390340c008950159400d58000f0b28184070f50f0b040fa00300240c010f4115560036550301c031140100202c0d6000355000e4001d00020a40107041d83c05070748894 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 721494127 1250 721492877 721492879
    0x3090306050a0605031605031906060905090109120509090a0b0607060f05090d0219060c02160b180f0a0b0306030114090709051b040e131a100506041a0a030902 70
    0x3110600b00085a400245a90310840e4420b100784004080c0042c007116401e0304807240140038151a89a82e440001c1e00c5040c1a402c817180c0380d40d064041081e000e603100f143d0144501c000000780f800c3d8585841d182c2e6043c52803000d0b0600c4002c0c0175052290b90741140c40d540c8960000b03400b003110403941011a2580c000d51800406941c148090900c00c504c05a12107840782c1c0742c0808981d007000002205030707200c504004100e02106800901040070500940011400b124648100da441c000fa207074980f00c2c403402e07070f40111072a2000001e145410b000c503920940d000b000d08481078040c800021000031070301c2c0e105103d0740e0b41545020000925a1750294070048c240c1805800d07400301803400007043ca4a8500c28022184150b01d81000b142c41c01c086003a6044801d5a21440070345094144880012508002400c1007211110021a240000c0390106040b0300c1e0307030703441842c50140d04011692080f2030450350441402140144810011448071a440d2a500c8040c00d541c1a034401107800210007502c2030b8000a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 721495377 1250 721494127 721494131
    0x30c0d09050d02100b0609030304090b0d0b0717070509011d221e0b0d06022206050d0605060a02070303050304050c060f0a0905060703050a030b0a150306210f0f03090306 74
    0x40d0311070395000714010040303100d420005c000c04c0d58410200b0115000300003019800d0f40c02070005100d0140e81e50b00c140e906500040241d48002c0380360f51030281e155001c0302c0c43c40000b030821130700c2004141034546041e001545410410308000342480001c0c1808008500554101144400b0503000e8880300503959212400c40340d5074001e148414400c1d80038120350756032264545030a11401d522440749200305000000e00070805e5500140d40e13102d8101a400c01040e080c0c0303a6202c080c0c1610040d00003000107000f05919214543c45101d00440c0400b00d407107941c004d0b030040c54100404113141358040381b00001e0fa035250030210f48075183d0303041940c50301c0c1003d81c5107a0040d02c0058010740c031180c5000907010140d1190342e008035054980050040307501407404010302084083c8480641540aa0041c000c1000d0281203c900d41742e03140c5000d02540e001c445110046691000244000002c1c200c1503065589000e001c05440503444c0d9507042c840702c100d44050412044c03043d04e8010113214584150023140c00c9882 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 721496627 1250 721495377 721495393
    0x201031d0102090f04140606032521111611030106080f06010f03030c020906040b0301151d0415020913020d022703070306050604020702090a05011502030f030c0d0905 73
    0x10500070360101d000c03244544d080d00a031038070a18043c015201e04403141307006001c45e51155018000c00e40c1002e445514149181d0b0306842060301000903404000320550340300b848a1550b94400000c003050103005846603401c0801101d100180c0c18121280d078400742210302c400030418100f981a8400d0384441542c154240f01001940c00c01c0040c0000d0382c0001081541e016903a51b40300d101c0d106440c1d101c0100030505290800c07015141001165038000710107800840c1c0d036402c0700c000a003164820b5555400e0450000000c0c4502d4024104000034644450b503940114101503d6020004810002c4001941c0c0c000030a503015450b111460b69108000035010b54803000300c0580d600194010329034440743c0241e03144c051010030303a4141d400b08102c100900681000b03130840c1c40741000380c44020012904240c00700b061800603121840000d01c5020950307000a699414910300034240b081c1d04004c501154001e1100400c00d00d103c40849401001c6010350555440e000c85060000d801d08c9000540079020f0404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 721497877 1250 721496627 721496681
    0xc0304030e010f121103060102160602070504110c1504050c1008041b21031202070807060b04023105010c03020d1b020a1805060406120f0c03020619030e06130b04020103 74
    0x400745d8001d1f4426000ea4980c4409035803225a040149d115880042c2d12209041060303003081d500600941c1c800c0d030a6070f8a85819074109a01d0448000c174100c0318003003400100003d000090002620f100012900428500d48006c0020710700480030b0005000100041849402072024030058001030940300e840c0c80c0364010001c00c0c1034038084c03108415004102041d006400200e1544212291142e102c0200c1e030900800751a80ba0080843d40800c03030b0041d508000c00904600c455000380314901902e415004556100300c0440c0d201440ca510040c1440703000543c20300081d401080000d0280d940b881c01c52103801400e1055080045624406504580c21503070100d5007810b04c600144070004000cac000e002640f40c002c1800116030f40c6100303200d0203038407010040c800108034181c2d0040c480e001d030401c80000b68590b00050955401140b0400007004000400a280d43d018080c1400c4030010390060141850a0411106d1201c58483d000f00503400400024085a0003179010780041080d4118843c000c090001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 721499127 1250 721497877 721497911
    0x10207120809011422050705030f0c18220618030305091915020c0a0c0b130b0316050702060d050f22051216060906020a080c0304030e010f12 62
    0x1030b40c0b4048a5080a089000320855410300f680124400240c1281e02c4c2ea249180c40c1c031000010b002202e0034001c00da80016036076420002c406141040e40040d1600200e180b04115a44c82d0201080f032000b0208800c01c00d40031034030781c80b50020500720400b00900188600d4a0340c01840c1d038025142511008140390002e06505a01c01c61064403080c1c100c61844514151201070b051070148001d1500c45a10300c0743c400200702c0e8002e08480d10005044039481003c0e036132600380504c8a80c1105440c0c0c200070402d01c2d45101808480c000400c0588211403460400b129101307035210034091a0700034401d00150200454440707030100e4040ea64035180400441c1070207000840c0040d03096442c00c103c20601d902140171003207001c03021b00305113501070018040c0719441c1c030f41c0490315041001d58480400c0c4400d010030100e2140d01031040000c1c03051400680e601c04c0600082c0c03518202401c00500c0700001c0c000c000c0040d400842540c00040c2c00d0032f1014240004c0d003030440359031804c1d040814906041280d01d5040300c0b10a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 721500377 1250 721499127 721499131
    0x41403040f030c0e0108010e12130b0f03041b0315020a0c200f012105040507080a08031b04081902040b060408010912020d083c0a110306010c0b090102071208 69
    0x444c2c04402c20390741e88240c40e00360303000d66080074103940110403c0140c1c00d110100030f140c000710031400b05a80d00d9503908801943c0c0c1103c2c000d100c1e001400810081004110704040149a440000240920741140c85001c00c00c44074240c00b68015174009400b0120354064111840000d51240c0c62444034100080f407407440340c807056149800343e510844409820740c0100c202014065a801c405001d05102030a10005484081e005451601903004085056081800060310590081c010301781c0c0c9080c0201441d506103102415048814010301060000740f1010807070350142000c0840c1c40c90240000c3c00024028038151043c103500c400f00150006e01e020b819007003030310441c0c0281d00c046840003000009a890710716001c003400014009100140c44029281d5010302d0303010424101040c4032521000d061080c0c06c51403c0802495131843c00c00205a250b4021140382c41103032414942103051650020b080c4042500008004200d50000902c1e8100c0c00d41c10744050a0300411282c0350301400ea02c02510034002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 721501627 1250 721500377 721500389
    0xc09050a1515030e0304050112090204060801090b04120503070f110f071502100b030607270e0f0601020a05060105060a1b080301030312050108060705031302040c210b0603041403040f030c 82
    0xa0100d030b08000c4c070020058400711841030b140c0721051031181602c0d6000303044000080ba801036591002080c842c82c00d100c1c00c004981314044642d0513060074200b0410780f160782903220042003800c004000006912415252a117251350078450f0980111003840d900704040c11034005806c0c403450100044ea1048110840c0400301c4680035140c240407016214800c2d507081c0c25203141c141c0c1c8070781c01041c0c455209001000b0752000f6a000d00c9580d01c6024560210030805600c1111290041420b11a502d2480d43d00340350007030000d00007440720307000701e544d43c80d01d035881442041e100d0706c80480d40e0b220030341c002c805008450008040d00040541c403841c0251198000307000560019040c0c83c2141817010702c1307100310b9041c1c600260043c181c030355a05200320781c0f55000030107548004c1202e043c42801a1500e02a0606070086629400000b081c010580300707000c40c20034912a01c4500302603000d2402d03154241100d400a400c02a4200111304050745580340d40b10b60307071180b413082ca400e01c00003060040c1d03000601c040c2c0b60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 721502877 1250 721501627 721501631
    0x1020a12030614270403050708071109070302120a0b12011b030e2109040e0f070e060402120c0f130611070b0c1b0f060c030304020901120c09050a151503 67
    0x3e40c00c103103c4031424210140d12000d40c4044c241c1480180450303802e034818820303d4481c2c81c048555440005580040d582115460345403024940705140089540e64804070030319017142000700702c00040d00582c0000d007004102e03640d6a001803405403169200c2c80642d5100c14024000458a08002c22101419404600001c1c0c070b00f424000d81c078880450a00e0401c003924007a102c0043e100c0040d00d09940c00b11052503442565109405c481c2081880407404d0f010720440035084c0c0358a4914003000c5004020310b002d12032031041108200c03141035040e840340c1100c2d40c90000f688031451039150605600c80d50641521000d801100041c40a43c8214070b094030f115844241c40c0038541d9884c01c00310318007500c40510510380001514103030004400800b810f901c003005144c9444039601070081003a0354002000303c101c90300000100025424104070450051681c0324245091032200d0b2207a1115200e280108a04c942c1c4a1010491403075040d0400c0d101410007000600d1000d41d41c440e102c0c00d08241441d0440424 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 721504127 1250 721502877 721502909
    0x5030c090903191206080d03050c030108070e1305060921070330020c1023131110050909150f120106030501090b01030209010e04030c0602070201020a120306 69
    0x104040603140d000d215400d00031400e000707084840402036000240790404201012000f01d03507129050180c0310081540c4805001c11015900b001419120020881c6200380c2040004121764140040c07640d00b140c5c00d0b0002031b112500d86800c0c2e990100901349020340075110f00401d000e525980130411f28142c1c0103940144540c00c0e04070551a120380a2241c000d80840c0002d1440d51500c1280c0c2d01010900d82c0359030343d80801080340740e04d02c01260400c5074840180d61246206044c0040180701300c2441c0090300101440f04000380705070394170300c640040c9182d008000b01c14075101044031006130000c2010700102b09540e20480303c0300003003a40d000700c0c0c5158820032300071000c21100609400e80c04482a009020750140c250400305100307038602400f404052641d6070310000808102c00380300381100395109803032280302da51460041149150b01a00703c1e00005800c40c0503c00020f42100c1007030482c135804840903032a0721840c0010707802e15031a41d8010703161402c0003080903852036056000301c0942d030190b00c90710452 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 721505377 1250 721504127 721504129
    0x1270329070c020108090f12040801061a090d150e03120606130b130f080a0212031c1104031a090601060311310b0703080f2401020102040803120105030c 67
    0x4103200361400004200e0220301e09000d035210380e920603400500e5404544080c0c0d0484002481c2588402240b4512032005c201886030300002c0c01418001c19004000c041000328941108050340310b003140180c1b2a0751248445800c2001340001000400002901080101042010551607500441d180340d61440c022000030031603d0400c00b5500004c01c902607282130113040004015031903000900a59540140c000c0002e24038100b240074801408071113020313220310b01580c4107202445d08100704484494109001400140a403d00e000f0342e4424802d00114400c010203620030b40a22503504090300c1806846044501c60024811490141c03140000f111803da1742e8441c11402c44540c3e004013450040100220841d101103680d40940d000040d61f004180005400d541c00086c0300d040c1c0c04428420000f0400c20300307058101201d541e015000b200218240d24140075130134032080c407405490000616210601c4c10318ad1003503055401030443e1004581c1d4805544c0b4103202d5281003441524485d200d50300c090009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 721506627 1250 721505377 721505453
    0x10e310e0307030c03120606030e0c03030301180b06090409030f08060f030a0609150501060c0528081806031504050c09011b03020c0904061a030714012703 68
    0x12a2448001c0e41c00c02e4100e96080302e607801c00038801d408106081961921200b031310b01c03940000340221348001403208864401203050445030001c0c140300b03820600041003d0a2901441004070201140c006a24a41800080c442d4010303460403540191402030300608050700500c45090303e04050719020150740d40c03c010820002c000241c1036405821003140e172000a60240c006d08140c0744510840c1440d1049500c07014100c55003680700500040d801700405003802402e0140840341030b002a40052007a0348400784151000d90321300014118840061644582c40d50400e07000060007000380420780d282840b216024001c101c2c0d4010a10442c600300206154489c103e0443d400c1c0e10041c0c403014088111150340854182d0180d5055095003d403480505050352804130061055100358030001d519170010906001c0151201b0809002c0ea20201040c00fa41d564183c48090081c000d10300a502e942035010b00d52012501e480a540501c000400048100444501382c003070860106c02000c1031070903d50340074600b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 721507877 1250 721506627 721506641
    0x307030305040603090c0b030907150c0302070510120f0509070b1602060309150405010507080f1005090705040f0b04030311030708090427050d08060a0501120506010e31 74
    0x100341d007000100b00c00e80c020340060300080d000345010f0b00c010b5074800382c00303040394000c440000e125000760030140400d449030384030410b000c19a40792054406e0315a079006036890301c160250360710580b119000c0300401d6100d102d00c0c0060503e200424004510b443c81da0001030001500c54040d40d00526802144d243c11410a49114001204006460300026000d0100b181e2020b030118109005081e0244580c20800c1e08a9020b0343c4210300010722132604e040b00410b5803001521a00305810420148440a42d11901e00d41c29200d04030f5080f0315a40ba468405e4846100350b51058000c804207541c006852400c040c0075208a034000c0c2c60b03004d88103856910040e1244a062401802400c00303011007641400c00d944401c07a40540c0c03448891302c004400c0c82504140140607401c60f1680c0c8120380c006103042d1301c41c10098010038103584850200e030030400042c0a00c1c0100c412114015a07402c00101d851703105c1c5941140c0703000c000e01100100031150b501a20304141011003120020300c0707003585482c1a046841406 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 721509127 1250 721507877 721507883
    0x1308130f09090809090a180305030106140313150b0307180f020316030f090231050c0f0c0a020d0c060e030318010c0c0e100302030f0102070201020a0308130503040f14030703 76
    0x9407408a06000304000d908024000070141651000b510511644d0040b0004405001c1d0300d5275030303e940c50700c80c0040051540c00e0011000f001e081c024400201400008103650a40c07040201100c40d4504600030014a01c02d1826541403060020012356190b21081d114036003200c0c8601404a80d90345603c4405a00c8240c134080140c0c1c40002d83e5000e4148683d110300140702c40f0240106554002d0b40006801380802c1f0308c90b00088500038046030300c4002c081070041017000d07500820701c071618050404c1d6040707004501c07007518a4500024042c40c0c0290600885280c658010071070f5020030031600700b0052007100e9000341400b151403401c1d5941e55281c004182d5001807002c02544a6003841c800c0112803030a1611000c0706c0c0040040700104c2c1560240c8407c0344a40c51907504da40d000c5195004252401000c080c07110320780c1c0d104000303030000360760b0110316a06541e41504148000380c58441e69900c804056540c060800d000200b0041129040d0a180000300c401000070000c51201c070008240c0c0b540071a00c001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 721510377 1250 721509127 721509143
    0x60b120604050108210c0303161d03190f14030a080906010b0319140a020a0f2307020d051b041113060e04110c070302240406081308130f0909 62
    0x108491200000805c004441d10241c02d40c2441060a0018596042070b51910000000451040c80745980018001701c080707031065851a04c042101d000c40d0b116003080702203403000b47c003108410b014003c030f8072120309960703a05c000c00c030140a41150b034464480d002001c6290004031000c0104035249000101c3c207050700d02d4440442e01c3c54645180190b48e83e00c038070b10002511910303568134281002c48201d041e40f041c5850b19015944401c3c3c90300c004d10100d2440390940512071b4a010264508614007451400805c0070040b099032a21140002100c0801c1040000c0c05481074450984040b00c020b41244c10b40740d019101440031800011000000d805034503050b440544c0340000822413103201d00070744090000050000200b0b440c1001040c0d00640c0a580c0d1248554801c010810450404181080c0c01c40c2441d04264154881001d0042043c401c0340b082808000d0010041841c0d80c510000d6035482943c4640c050795203014218035814449168441c404403010b00c0c600c0004d4640d183d00a20801c01e40c0000340c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 721511627 1250 721510377 721510393
    0x90c03050d0917030a0807031b02061918060b0d1509060b040501061704020415060203042d14030c0a2903060102072309070809072c19060b120604050108 67
    0x116046c0724004c0040d410181c88020358440d0b80700c06100340e064142d0075800380c0220b240c8840004032101140d0140c84610349061141240021118100481254416004903008410000041c070001c86003402030182c410724440821002d095612455069120300000d003d5410340385c00708000c84400348661b5001c24a0710544801d800007200c078080d8000d100520000d0403c3c00c0103405425101280c0000c0050b0344001014001e20032200d207440c410301ca10b0b8145030340030b40e002c0001513003105640c842d07600594100074852815580900141d04e0380c12020f00500151903655403100c0c03102242c14604901c0f40030340019038220305900e800700c1e4130404041e002051110300e809004442d1080701c594414841c07485600030b030115a60400450b000c2c003070603501c03500b1600b449103c0f6402c0c940568400124500361044100001c2d40d4003446e080340e111005c0140900340c0e10342682020140303140112424043c500f00000c82c03203c00c6840600000c002d000740598084d5507030824401281c6080c0101c07000c80d408019 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 721512877 1250 721511627 721511647
    0xf0a0303110a1e02030606030a1707060f11122a09030a080a050702190e0117010e010e030c010f060b040e19060806010303080f07120f090c03050d091703 67
    0x114504212280720129031111000703450740c800c00048140c0074030307001c2c1c184a642030a5140c20400303590000000c03409010707468407540da981501400b008210110400102c1c041c070a1244035484101c82101402040c40100319244040f0040c0e07000c0044079400c0c210000108940300c1c0948080030030f1105425084182c41e13221001ca001a420000b8119418484c0d880c249000841200c0a000007100c0c6d03032213282c2c50703c0c805d00c1040703c0b4181281c07500003250440e0404000c1c5128040300581143c2400b071891003400402403030f85000d480c60500766503156013002c0350590711b010004000e01c10314921000800140075912a0702c01594214840d0400c0f201d070070310040c00803c04010b2100d4100c4c941c42d070001c0607405070702e00040959420342c0c0182c0182d00498010024560015021640a1122403405149140885002c0d0400142c110307034029040d511802ca02010b421a444400f0312500800300355100c6941e49805640c50b1802510b1744001401c0d0075000030b10b0f20302c1c00307001c3d02e1070103c1401450070301078900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 721514127 1250 721512877 721512887
    0x10209010e01050f07050102070b0a200313031704050610080d0e04020a031d011e1b030504020f060c1f06030224040f03030c03081005030706080c0c07061d0f0a0303 72
    0x3103d4414015040154174000345003440201421881445030302668502000440304a5075500c0101005d8600092101d0481d2881021268403500304840440d2140c01820100d54400042c03040800c162120018042072000008019110b483c100300901d1003d83c840b07010584503009110321314085404501e43c620b0a02d42174000d00140056450b0000d02e04203040d03101100800c030910b28001e680d54403e05054419070425000c2141841000240200d555000c1c40151801862940070b041665032401702e0215900d440e44110030030030082007192240d0303112140a8540b0310034402c5000000060a00c03d0807a40c90f0700500007141d800800840082079003500e000008015515a440841000c101c0402c000605482c10009035000b5030325413885401c03524010300014005810b060300007052000c20040e56a0004004082d2042d030700d010f00042d101c3c00081c24035400360142e280402d0040c0500482c040313500502c5084100315040d4245860b400c82814000404040001c140e0040b24a41c001c0c030106c4d000b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 721515377 1250 721514127 721514137
    0x10606020d0302072d03180303050d050709030602030c0c151b030c0c070902042c01050d02032a010906030212160c020a0311040b030105010b030105151b0c040608010209010e0105 78
    0x30b500745c2092982e902e901c81102031482c00405007000b400390b03510818558401000400c000d52951180754190451310701403c0c600494101040305516400014400c1d8032802500d002903a20010030f64603030a111100d010710343c02411000200380314010140d4403c4074805860350260140584040d08881a04450034a079400140140900c2c01e0401c94092640000c1002000034200c901d80140c4a07400d14582c500c1084456540054604488541c00b44000c02083c040d41102e1040755010a809850700c0840e051161541c00d01511508503034441c25071540368018050980e10036a510311146031102001e400302d000b000140380c4421004030000740d4440300709010650003d4039040c074040c102d0315a4001ba20b01d0005400841c3c5a040021202040c0d080a014138814035404034002d03c010341c1040c0300e52045020511555204140b9002d240a0040c10300007260200c021030313030a0482c08403200c0344041c1c0d11286040d0a60199183c1440064151018401e44124003416503441c60320503461001110300d43c01ca = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 721516627 1250 721515377 721515383
    0x10b21011223070602060403030b04200c12032a0309030702010f0504081f06080c130b01030908040e0402030c0f0d0b04080f040807090c0512010303110c12010e010b03010606020d030207 81
    0x58418282807841c4204420f00041280381d000348914135041c603000b01600c2034071005038051402d01461908071481d080425407940c1a6200c00c503195005403039910304d420f0803034400c000c0c441c00000034800e18814442912001101c0c0ea22600109100861000d03c640310440e040d6095070800c1c8256401588100300c41000350102d490b08500302a200d000d51420a80c1041c4500500d0390000c1040342000c0d4079004200042100304007402040d4140000318591240c3c80840500e0140d032030f0f40000c1103030302a602801d900c6400016407602c2c0c4e9142c4d0343d41c444a440946040c0d103e0b01c5581c2500b01c0a15203146192141301d005042800b5164442da00d10503040400b420440f8514010b100001490716404080e00c0100010b0000b84001031500807004121000000c0800c1080310405c01640071600014581d81142d0345480c10514001c448c0c1c0301d41d414000b80e11401540b003480d000000c0c1e42c91700150000840d420890008209801e61001010700321000740c421507000d60400c00307000d0383d407600a43c0030780340c8140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 721517877 1250 721516627 721516673
    0x3042702041a090102070807060504090f061505072f06030402121c1709060601050c0c190e0610081305010209040c0c120912020607080c06010b210112 66
    0x915564624201502c0800380081403101040003540c2d503a040140b500100a280c0c0030b020001d0409400401e1442036000381c4d11000d40f40c0152204403145079000c40020f12900120700104161004000c0080d886080c0940d240140d10318654402ea054220802c0000300c4910402406d030096011f2010301d400c01407091762f02604040c0544800c10043c4500308000025140d08101289000c034042d1195060720120160401c40700108070a44000150715900f0680908016440350040c1003070518003072403e4480c079000726407040c0100169400411240584071000c3c0b002d01d26a072906c00b400114181c0d08440000103920720082030643c0c40c15011400a50300900000d0700c6c1c01a5903022805a03120800401c0010b484024a1014044c0c0070108900160441c0340080c4468a8804c40303040035103441e00c0c045d00c02c0c400003a01d1010440b03030b14100d42c80e01a4040070784e4840d695481c10490a03030007030242c086c601c0031103420744c043c5030000c280654165203003211051101d142d6a01d030300c280e078251421418a200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 721519127 1250 721517877 721517879
    0x204260a0f0b1b090303040302220f05060f030c090705090a081507170103030c030509010c06050709031e052104180209030709050603030307080a0605040603230304270204 75
    0x1561196075200c145005000582540c1003003484602c000e0404040800281c006100c400400d03034001c01180d08585d01290348401c0e80c5401c0c941007030001414189842408c0c40d00c030200b982010123800c101d10401049640d03c00000005e4181034035502c0c4401629407007001c500000e10110b008001421106d48003038a403e000b692200152450203024294211103c1c0c420f40802c00301a40c01004861201c031088003c0c0f91551650398042c0022801c032400030300348100440d800c1760691044403c8080035400c84400d210030705000720050b203440310b640015101301c0ca4804245107c00803c0e581c15581b154084010200d410289a81c0a01d24050340c4004281d19420000028810074031802c41a90301060440103035980005002c0520304070455008041c2d0b41d040408109040d600403060740d41c03100182c02d04060555540e0140030090901e604141d43c41840e100010003448a1600c0c811808584c2a040c0040f040b02a01d49039030381d005621a207203400402c000030035811090805095811004040c0250500b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 721520377 1250 721519127 721519133
    0x310111303051011041508060f090a050421020709050a020f210912040b1305030105100303020111130315230406150b16030915020715030204260a 64
    0x40390241e1040d01e0780c0d4030240150b2890302442c441e040492225503410b51a0074603104400c8080c42a41e5402d009226250340080c43c030b46c8916030070022600c80100003019900d0440101c1c401004251000d03a4902c1283c84000f20341d0034048143c4181030744540090441c2841c0c440c1e508050400189551403203a0240014400c4000c0c0b03902401059090b010000080100c2d5000d094010f0b400070150a12548201d0102c01c100841e0000c4506903044400a259201c1070801c00e4005034001d5800b1a400d07610b01400c02031a5100300401c802a80e200754002d01042d2408107585155004000b40600e80020383c40007000083d401d0650040c1401440d076001c10b48800d883c58141180c2c030b6072108030380a0640c040801c405c0180502c03031702c07481d001c040345503203010fa04014001841d400340c00c4034000d02c0c0c00300c0c130007480a25000f41c0074403008200c1410300c00d4020681010080d01d41ea031600c00d1402110004640804a078003070b0080c3c6003a210411081c910b00081103000281070142c01e040c1c4070050040707031811408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 721521627 1250 721520377 721520407
    0x50c1c0c1e0221190e06040302040b040e100203070f030b030d08130813050a060206040302060622020d090b06010c0807170c030a02070e0703140a0e0c0303130617010302031011 77
    0x510110b40300183c6070f28690300306140e01c0c44e91021031820008610f511107426900c80d000d41c1c003602c9c3c040d00d00148440c46040401c00030603c0740103c209500c681c01483d15100c100c2e400131407050301079543d00c8107c15442d00c02a002e4464084200ea0b15401010702da60b0154403031107140341d0084071800813690030300072500d9182451703001001d5000410741a01091045040002c0500010249031000713040914040d1402900d9000107003526100d1482245121030b04d07441c02c900000006002207046503103881140c8210000d10556a045170030950010006400d503015000d0522501d8000344028600400ca03130301d00180b1074802500008028080c481c901c030381c40081000e040c00c0100c940082010508100c81c1800d5080c0c014501e608043c2071200103055940c100f040c090300001c031080003242804440c82c5503800c00825460707454061001003500c10b000c4c14204403120440d00591070b545403600c008080d60005040900020350141d0002104940880d143c3e8003000c030070003210345100d040c00000c2141440e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 721522877 1250 721521627 721521673
    0x10212041d130f050c15070308180c0418060f05070203030a020c0a060905060a0501081915020c03280219121e03020c070b03060d0210050d050c1c0c1e02 67
    0x2810b9440792145e4103480c20000075918086403001317062401e05d0b080d81e80041c02001c0090031105100101004050f02d410200406440844010424401c8202d0031004d000b00908121007582ea403410445a03c5001486100701c40c002c1600c0c0d8051490740d903944144c4c101030341c40406600242e1042d1800e650104001c0d1045400503480f641c040e003801d06108628100795001a005403050750071000d87c002208446543c0c034403034240d21480c1c1f041440b1b09082c00200a000320600c2000c80c1c000051007036900e40b00104609114040355140300038260104d1001c90343d45200c120005100508050500c1c042018401131090038106440c1c50096122016180c5800081001c4000c1c0400d801040d880d0059006009800140524290690640c034fc0040040d20301038001001078050020700888070f0a0b20302c94000c0f40d400d004000001c0c481c608000b51380c12802d40c484540581e42c00d05408000c08e080a4500500b140581c0943d41c1490002042048512a8050300000d0003035206500421042c00c44031807501c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 721524127 1250 721522877 721522883
    0xa0f03050910170a0b0f0f12011a030d0801080706120216050d0e090402130518030301060e01030e030307210605030111030603010b0105030906160c060e060105010212041d130f 77
    0x1560f000a030701100c00c05804060608000d0500788591907109889412850210180468500320342d01c15044c0030071500309481e480c0742c07455400c000d00d074500301c0d20103800f50101040036002c0300e145d03039028807003241e41260078021164260410b81081181a119000c1c0024615040e580140380108424103a038502c80000d81c1100c0541061060080c0c039500440e10049443d000e5450850601e05136000407143d001c80e5850b41060740d0b440bc00b1441c1905941a44010f5815040407280c2d00d5849a001801c1f4141d03851101740002d04011350120040008400c0da4054099516040750100e02e851448000c00c861401d40f1500d01e42c2c0d03000025050340c00f400380c4009030004030300d83c0b0f50b00e05240e0309250075907c6422005040c40000c10610855030400524603505c000395080700300703003240300703400c1210130740e80d10400901620304000b0704640d00c00002c40c50702c0c100d070026000c03640c9622880c0900422800307140b041d40c2c0054010aa202156005260841c0d48809040103081c0340108036561071000d0b91032032000f0717 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 721525377 1250 721524127 721524137
    0x20f0c0706080112080f0d1409160906060c060b3f0c01020d08041b18151a0906040905100311010215130c0f090c02010609020a020a0f03050910 63
    0x800c0340c1c0d03800100c8507001d000b81001040d05020302c2c3d1180b0140d4414200f44040141c000143e030001e0200b03e44c03091040c1c2c010b00c00c20101500701802219510440eaa41132181507510020010390034100e8400c82c07040342c0d0580c65000341d90710b10b9212302c00103059070361510740c00038075000400d180000710b03002460400c02e2038089080380508000546040d03500e1050941000ea0003000b1841c4540c1e00003c2c020010b19017490010403039544ea1500e44042500c40102c2401203a40c0c00300805c442c2000e0740d210b002000304030010070914220380c440181c5584c05225202800760760200b54803403044024024201340388040c041d00d1806690343e0b8141d04482d4112817143e4400c655090600401242d0303800c000f018042440100301940882c01000f1906501400d07481c401c030081032007602004518038904000f002c9099800c010703241c0d44c11041010341004003c00005500e8280c020035594030b0b40c8240c403004135a80d0300078401e00d8000c2da106c0010082144054050000500240718030740e0b208045070b000324280c0d03514 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 721526627 1250 721525377 721525379
    0x10e0a09230708010c091e050d0b0915220804050901090e060901020f0418090f081909080d030209010909090503040f24120e06010905040b0c0717090103020f0c07 71
    0x705800c000298014501590400b641d11700c4843e4450358000568240f803046140b402903031002c00c49421890b92000c3c4d0841510541c2200744645d00704024449c080e510151001500c0e04030b07030548424422034840c2400020a001003030103006000801604a00c10000315180584800c0081d511520903800710243c00e480301c8204006c68800d000780c0742c2181c07512009505000f050100280795004500652140401b0307038101806860040e0444010140c20095800f20b0301c0590800304c001d6440990014204203420718440516072103400000c0484400710041d003890480d0b208200d010f94040b40307015040198018003c192080c90744103000501c1c1c4140003c507900c0f80b91805030076030030140e5400180010408240c144a0a40c00c0c0c0c10b1a241088074a40f0001800710b8560760700c02000420020110b52248600100715112a9480715005d24041d500703030005d81d6501d2501d00c00c0c0d4850724a00802e5085261850441c1540100240c400424141405401c00b03880d0154011142c0106400c2c100300e0f480084 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 721527877 1250 721526627 721526693
    0x10c0209010e1e0708010303030f1b0c050c01090b1602010c080c1f05070203180a120b0a0513020a0303180905040809040b03011104050d021906080f1e010e0a09 70
    0x5240c1c01040d0083e10394002600d0081c1c0040c141050510010f824103031104d0310b01e000220349501003848910620403195078a040c23260010b1460452800444044c03141c00910003070742d809203280d802220b103040c501910702419069442d0360140c1d6074404905204085a107240000c40b418040c103e0841014020802c102d452110903541a028041000003146881d05000c0e01c280e002c400c0710361a203640c0680c00400d541450100e9803c90541d400340080521001c60b03501008030001c1c107540030794031075039042c0000d0326034001404100c81d4200d0b0081d0300017000141000042d0003402e070001080401003810304d455554030b69080035a071b0100c40c200d0b0b004100184411070b5107010310412034000c1d030503002040b00c500301d2a1142814030803400707032500c0390341c42041245c21503960034100c3ca076120b40d948102142c00e642c1e0402070038442e02640c035014006094000240c100d44408122040107104c411a043c96034a494980003000d0800352402000c03680320081c0e00c000c644e041c501462101c010000309425048510 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 721529127 1250 721527877 721527901
    0x1223090307080a051621030f020f0303010b0d050f1e070c023006060306150609130516210504081215010e0a030521120f04020a1e0311010c0209010e 65
    0x141019200344040941001e4500c0c41e04814446c10b0343c1410148c0b01c000390801c6c142d01d0b120510146007490301c00000042000520400500100b00480e042409946c4408401016114044030035200600031a583c41e4003001d0302c614407a402403a1428408514102500030035580e0800c00078111502c0003032540c050010001c1e03013010f510409568040d000d242003040000b5100e1501502c0c040711003415843c0010241d685004036803c0a500078000303039800c010f180180e00500130454005a400300d1103001313120b000c2e006203003603003030041480d0710b481071144e01d11590401014054800e844000c414081c0ca024410250307112405074208a00542c40d000c24440010030801803426600d01a4240003401c200003440003c1481803401004480355404507c0741e004009409800c084001002c00e103018841c01d43c0340040549e000380c1c0269510000d21361140c62229510791460808001c1d640c4020040010410400110080400525003c41080b845400107107050a00f03130001000005640103001d5005c1c080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 721530377 1250 721529127 721529129
    0x2070c09020403110a050f0907030f11030a0e2503060f0b0d0c030b091204090506220209040b12061308130608160905011e03061802071223090307080a0516 68
    0x4541000f040710f03913400420b00a8002074589e20a05444100384200c0e0b40d4075400c0400282d00c05031100b500c03498441c2d84030001d0300100c03d402c211070081c40e007007c4200c80764a920848440e14031003a50661441d569035000200a01c1c0c8020100a9135000b803158503984004410440d14041d0030040f08260650901c1d03500000c0c09040d84141da440003414185064010b0140d5048440c000e00000e544e5449102156940c3c0700180382c190125100928080e9001965000d40504c180a41d401c2102d0140c43c400c0c040009007284014080f60701c0301002a842c40d884d410300e802d1142c4144956420103141207101e4901d49031681084020a41e52020008503078006940300c0c90700480f0b0b151060300e1a1900001038140700d884a080c000300c0c2024810122594080d0300110010540380789101c0b40c02c0004944400250450142103134010702d09500411000e200d822011000200c20b08aa5a03010151160120651040140740d4140c054402d000032114401e112245610b8020000b42000840c044510f0280380e803a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 721531627 1250 721530377 721530379
    0x1205040b030910060b270303120c18010918050a090615050114040302060a0507030201141806090d0815010e13140c03070e040504030c0606030804053102070c09020403110a05 76
    0x1040c40001d650000009108041c6c00d003036140c0f50140c1985002007400c52165030400710302c2e001c90005010078540d12500611507500d4004070040c00b620b118004580ca9100c6124000000c22088201c1d0605034060748050341006600d00b000990b50f000e6a2107100ba00d135590011000c030065039204012658110010018409076440da0a1405c2c1c2560300240b03080c0035694111080000204800d02014002d61100c880da5a2000e0402c01d81d180801083c3e0504036600703100c101501802010601902e00000c4620b40c0307500c192580c444695070024949206210071401c40d0401801d400301003440d4642c509042c03500c3d9003110001c40c0c10342403030780001594034018181002d04201001044152039001c05030a4820104881c0442d42d600e0320b050480d0450384943e005031501d464010000100f00c0440001e100710f500641d02c1c208112907252800c0074a0900082c140e1400c0e59054040b020f010300e5500034500070348107100003603030580c0751041c803012a001504105c0720340341e410000451601d4012a128000c00b8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 721532877 1250 721531627 721531649
    0xe0405090d081f0306060f050f090105011b02130203060307170303040f031e02010e01230f07031b050c1203070f030e030c191203060302030303041205040b03091006 72
    0x41000d86540d4580003018910304100030003010403501c4000c42c00958011210030300d4922215100d04091004080030f2242080064644c01d00244a007003040c41daa5103804010b00c0c91748075030b2070000195685040130000b82c480f40103402d40311006989040c484031408003503150061300da2070f1010500d0300c1d11180b03401074109064500c4100928042c000b04683d8015403282540500b10f1f03040ca005d807046031000440400303201c225a40c501c0c000d83d0542c40344c141c04000b000207200c810001d008078042c2c6040c1030541e0b02426062400a00d081c00504041ba40000151800207004142c03903403080090400c2e02e14a400042e0001202c22187c2c40402c45c10301e01040398104a032950800c540c0140c841e14582e80c4070f006150b2106406c03d40d08009105a031004881d07002614060006840711103e0280e0010302202d80c2e154440800b035480b8460300c80d40d02902e5010b401180342da01c868a5031548038030880800030030070004200c04107a0311203405c061402000b04900034180000f03803c03070341c5040d80d02641200320020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 721534127 1250 721532877 721532881
    0x30506070206250315140918100e030f0415020709020f120703061802071401061202210703082a0c0d02030703020406030311070602030403241506030c0e0405 69
    0x2041c900340218109500782441407007424003003c00e41c080d140466510360901401100011407001520030405810805c03a0445401c0c1e403540d0381d9201c0034403030083c005c80951100801102138002a44198445142d0804903401d0250007481408164010317005001c40d074180700b0b03540900070780410455014000d50071042d07007080c080041c00301e000d010344030400417000d868034045000240a640b1000160043c0c00402c0b4030210030644282c003950190b6003c43c0d0300c2d090344100d40b0112406200e43d105941d00f00c2078440c02008580c081102803c100d05a003011880541e00340c0b40e841a04100d4236004501c20070100d42c072080000d08005120100f052480320011180170701041051001c195044405000c1b2030b485180001e40c0080380c0303440c09035000290020301e800c0c004400c0c560405002510817210b070301210310030741d1512400c0fa01c0340118480100b00301c032610f4034100c4203040c0740d080ca41800001c240010b10603201500002c9424481d03481800803070350b1800c116002661101e500400c0c0755043d2802d0202e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 721535377 1250 721534127 721534141
    0x10203091b01170903030709050105040f050d141c030b010302030423100e06180a050d0e1201050403030b03010c020705060d0e3301090504020105032815030506070206 73
    0x1a00100403186040000c080419a050b0f006000c0310040b0719200075030910900d402162155258019911400031589090b00001c1e5580700e01c04031403e80785050071884d030207440d0030b0502a440801800c125180c0c01e00c240720103810001000750031076198004c481c04108001c0e850018040ba28441c0c803c43c1010300410402c00412501281c448000c2e52411002880800c040121401c1c205100d005a00d01070920781019059100001c049028065038440344400c12160200c03075940301042e5000900641100311343c04040d03400340380c03201c202c0c240203084070a400c0390b880c0c109803c58000f01da04901082c1c0d140400e0400b41002d200e141c005007800c0c0010000d040c1001c0020b031841c0103075415502d03916111600c61480810070311091110581510f00c19160f0345684d07070020340c1c807460345203250703a01079002e40000f5185c1500e01920740034a8040c1c4070744e480c54550080d008500344131b005842c40815100e6080380382e4414030380b00705c59a070800000761501090840c9041414000d01401036002c55004006010103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 721536627 1250 721535377 721535383
    0x190315080307121809090b280504050307021012050a020406140912010903090e09011127030d03090b0a020c121b160914010630060f031401020309 64
    0x1480390054003083c031589550764100c46860f1860b41d10402150344920010703603140541c0051036514031a42803401299245411540c1c00e4032404240b904c000320034080445d241d02c0c1030348a00d41050082e01a80d00d800c081c0d4020646541080d05140c0c00900d1301c0ca01421801840e02c00c140d081640d908040d4a45403414000800781c00840060040310000040e40b407a080e941c1c0944502054070f000028801440c4038100038240010f107100700806040c4d010300203040b401c0306200d1510b87c400b10f26004c504000201800700d0001e42d4541f02041d450b01b018514280310355041001e4415580c0da6580810000c6087c681400440c0300039005c2d00350345006201d0301050f09004075035113a0341348829062540703400f5615085841b0003c0c0000658840c0a140f42246c83c4000152880003510b01c1f804060045680c032301c02c0c100c00c50300b0904c5950002401d044603d440c841410b612039101084511041001c20300380c8a0000c00c8801551050307142c841480030070420021080795a82d440e100c000000c5085240884203035031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 721537877 1250 721536627 721536637
    0xc060307030b0d0b18120405100c08121f081c08131712061e04020f0405040e0c150a05040e041e050705011407030c1b0b1903150803 58
    0x14141c464260042c41d4503050340e6009990781185a0f0303419414003603201d001c245000c0da2900860701414091a910208003c107c0781100d0000d040960800c1621340200c458010300481224001d60400681020701084440d00740140e900720703c011810300b4800d0300381160308555408210160000300c00984030500c40c800213100010141464080c660b900c01c0c10340c48030003414100900d100000f0418130156901000605003c1c0d5607001134140b00e13210403040061058082141d40800761041100e200d0034186134001e0001e804840540d1402c0036102c2000405542c03209466048a90003502c0307501c1c0902d020240c6131501d508800009150107100740e001480c5206c2c5004800080d102140031400b08180d4241442a2030700b80c81d03800c8650880d43c40c1154903842c0d24800c807400590031501042000d034041c81200c20045d416103e50340490034075940c06000600c1c030818010074030403a03200019051a003d00400e0f480c41c0000342c900400440f900c0c0a030407100a0144600d103050001c406001841c000003c442c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 721539127 1250 721537877 721537891
    0x70605100f03110d0302011103070905010806061204060902030f01090809091509070c15180c060f0507300906020f0307020a030f020f150406080108030a08040b04030903320c0603 78
    0x5510f600070f4101640503002c03003114508e840d1000001c0100040d409500746042d650240e070751031201d4403050b0810200b80a103001c400482e104240106000541310741c0054400c40c80907064a010190f06160782d82142c0c10241c00780d07542900012003024910782000e54a0b8046106002000d1564280300400d00000b4014140014803500c0c801900c1841049082820704214111003801115060304a44050015004044403800d2860310b011500701d00403030f801c581420140e942d10342841000d80f1080b821901e9141141d281448004400812f0032507610b00250301c81043d140c81711a1403511000038074010780401c0400701600284401001603076241810005c480d00504d41220f00e800798000184003100d000000b070b500210308256040011000300244c01100c1950300c0f169a542ea07640009074403403181d03c140d040050031074000540080d0103e248590094024130340f01038050346a0b992001d840e403081c001250365035851820031610744110030072214403004510203400040e4519011482d1400086c00103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 721540377 1250 721539127 721539139
    0xd030605090a0e191713080d360801060905040209010609060e01120212072703020f04150b2115010903032001020d0b190b041202011103070605100f0311 67
    0x11350510003204248984d00d980200d8481d40d41c25070228951307a080c2e2a00c07030004a4041c070281c1419190140790326281c8483c050700301c102c0001215280b00100440f0b04022440601403c4000c10030f240244664006041200e4000406084c40c0c01007054940050344020200021200103100d50ba0384135001c50204182070a0003480b0506903440400a806090003600c0611016030800414a034480d84141940c00c145040e40e0103183d1072010201c0240b62030001a404c00303144200c800c205d081c15489200c01c40c1c6100400401035071240006040c070750200c45180020428080002c05104112840a400c214515150014081c0c1e001c0080c1a44101e844041c0038005101200300c12150b8018010100012020003150340307050b521001d1000340038940019006000c0800562001c8441c000760703034160b030120410a03043c00d19228004200e85e694040c01c07410480c448115a000e001c0070000707045d010348103840110b99458440c00c41e40307040d1420752144805030b4031683c0400108400d106450100502a110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 721541627 1250 721540377 721540423
    0x3020108011517071b030c0314090607170f030c0c07050603011203030b040e0f03121008100c0c0b010305011d030306010e190f080708010b061c0c110d030605090a0e 72
    0x10603a400713202c81001617000b00420304483d08050b4080c42602a29100f5290b810000100813241c070b800b03028039a003840d0442000c10100d00400c24280c440203421400e08045443c0c01244505070705a0781007590032101d000c03004030729480a003c0520007500607100607510781d0b04640c500301c1880000242d241000d0245503a8550901403a02c0e0360b00540403a8944000302c8440303aa1448915507207600158807000c60210b5000803805102d80000f0820440f11607038010040b940035504d0510090014224a5041c03140400320304000500c9010000c1c02035005200002c3c07140341410f0549111000c02d1108106074000b0402c1200710380e0070182901c000e41040c3c611525043c06000c0a132050403158001c010162406d820006203403500268a81c02d40e03001000030b02900e241042030161501851200b0074080924085102100c0c4281d8800041c10410f4034200901d0490f00b080c079810001d22050039000251580300602c03490803c8085150000c28582e0708003c86a0359021203516079201c01c400320855030503a1340d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 721542877 1250 721541627 721541641
    0xf08010b070f02040606120b04050105010207151e05190e1507020303070f0602040317030601090902090423011409060904020f0d080c06100602030c060708101e03020108011517 77
    0xb003004502580940204042078440707401605440b40e80c4600700760b1030305000f040182801c15000c0c0504071401a00240065030a105c024580c07601c0c0c89100da010042810090301020100300b18080490301d0f02e844d195a146070783c074018101400011041411f102032a0703103e04c0140c50316414050700c2158034980d29241e0440e813000908501c0b0389003019000c0011f080400c0305020081e80104201c0c1e104450640c01403040d885000c1d440d0004440c81400309034019002c01500c240c0d90020f2514040c000d0000070400442d0000b01d500c40030154690805621500050141c400e040005500c41b01e07040340d1200581c60000e001800c0c100d0014130080c00741014003100d1465480c2d4000300d4a1155000211980300c0e1194064160303118003c9a030004e80f41144074000580500100407101603040180140c02180d540b1541a1210000900040d8560745d10f540009480e502e80700c1c00360444015505014652481c0d400010901e80042e08006101045500071440c8a90008422041310200b0f07900c3c81c00ea82e80f502 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 721544127 1250 721542877 721542893
    0x203031501140d11090f0109060e01050d140405060403020f070305030f0c01020f030c0c06010e160c0510060807090b0609030303010306090f02041b030c030c0e0609121e010b010f08010b07 82
    0x40c4903201042c04c24500020030b40f101340241c010383c54241d41c0c410800880400440340000b20388641004110342414446055228200801c480300002c0404036801d4106c0142d11110340c1c080307409568a810207020712040507030510400084c101088000d020782030031615526200e210f075182020f0070081c0006c4c03070020f00d902901994911800044c280740c40789803c1418000560102a078441c0b0b0707024501c000700d6030001041546000701030200e41d5242c1d1074540c1b40d050381c4e03010007100e0568245c880c1103010310402d0498080c803000b0b442d03800040c2030010324107030b001c1041c0c400312181c1501c1148140044412502c00205a03411207410020220f2888a1405c126211b00e10003400a90841d041101249010000d4030340003100e10510f950400000d070280d40214110351048140800041c16615041e800d4541140900f8403058010f00d107010096200e103c0c1e91802040040045001640c0700801850301c01c00c0c450004c0d000003c0c20300040c3e05c03528680c02040542c0500a000c521440419070109101402d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 721545377 1250 721544127 721544137
    0x30207050f0a0c0315020a17090a02130c0912121b02061813060b0d022802070f080703110904030c050609010f061409040803091006180c020303150114 66
    0x50003611401101801c0030038400c02640010303600c80c00c620354171840c0c3c00d17446c2c400c1790004001a5a14070b8080c160340702040004602a1103000c1a10030100400c0140e03403412050321480000c40d0000424880b9528090b0030740e00301c0d0348100c180c81330700e45c04d85020583d0001a0460f03826a03152454070400354144d060404050000c020f034000b40c0c04549100503416502c034801201c10101d445002440c030050203007080e40c840c0d00614a000a00f800300c00700001680d006040840701808500401c8000ca811001505c0038021225006030701c0381ea010404c55804d0300956010340000f5001e020702c581103480c1c47d4100b080e030444d018024070320180060700b414881c403200f01300143d2120507076600d81040054203020f0141c0e80c10340c0c1111391514100003015201d24032000c0c692100603040c4c924070f0380c507074581500c560002008261b00d0300030b40003000b0302c00130584641800340200903d824048403404024070222488114050b055500402c140082c4102d0080c6405110030b0929105083d402801c90b000740500038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 721546627 1250 721545377 721545403
    0x30f080a020f030d1d16090c0e09090127121d04090b01080d11120f130f030b0a09030815060f1c0e0102040509010909110d030c030e0307050a050103020705 68
    0x2021035201030320144c503040b4104c405c00410007805085102140b50780c0700c1e08603001b0390000002c179240c00c00241d00e2580051040f90414145068810010b002187c2d110740c00300c840c030186945d1014400d100421405c08020006e00c504410908a5070a81d14809080c3c6400e00040900000c403486920084030720250703003400740c409082401640001c4c82c01d00c82c65170082c0103140d401e0007002880340c0040c0c880c00c7e130400007000c0e4100a0402445048854a40c2d07402540c40c603420420820138000560741c409907030802801d45181110089196007070102111501a001d41c51071801c040d07950000c05c2e48654007d4201541001860030500e0313402c001409445540681c03803c5040c0412075106015aa540780400f410b04094140300329940640118200c1c421401150342c80300d0b030440107101c0c41500b0360243c24242d100d228034985140b40c0100040c016001c00c4c030300f1000a41e50b1642c1d0410140d0003090541e110301d099000b420b0807800d20001681c00401400340074101940441c404041c030108006d0314100e605 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 721547877 1250 721546627 721546633
    0x9010207060f05150909101a03010c0507060c050304020607140109140a0c0b12070818150105130e1207020d1712100806040204020d0b15040f080304030f080a020f 71
    0x14440400a49412280820f410740c0c0f13006003030f246040c5601c01502c15007861003d880c210124594503002801426000c0240780005c40c0a82400c1c1c401f4414689401c02544445440303620328501841501c60f24a0510704001c1e0500038040142c84042c01d0326880b82e84486850004031404134101e0040c02c4421014011101e09120790143d00d01c089645d15405024118141c94192500241d240503c030340e06c601e10b83e1546140016035000e10a4030556000b180504501415034412443c0c00e2a01d05e13200c0c40c50b04120b08040c01001145080c421000303e44903614805d0012a00341c206160b115903560543c4542418002513480c1195a401c00440016900205544000c2e550700c0d150301442d044000d4071003e0414850210700032003034014214048035a640003d0602c1c1d902c1d5400e100180d00701c00003230000750343c40d01a12a203c1c0c1e908160b41c00c0721070429101d07680700d62900403141c08113042ca07800110b030307070300704100a03c081003460b1055491140c200342050380c0e8005041040345080102100001180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 721549127 1250 721547877 721547891
    0x5030c0d1a101a0c0303010303080712110904050603010c021c090f1202040b1903020d0f05010f09020f0114090603060f1f02010516020a0b1b070501150803041d0901020706 75
    0x84414009603040e291111485202000c50f500491084d114203001840c0a5206000420002e40306600e0103a10000c6840c00c110031214480c445000c1d02e40003c116020700d4404a00000c0d181040d100e0542d018508400a2045542801001c0d4450085101c10300e46184219800075445000e08070502c02410400041402a661503e0030306440042640482c419410a41c00d05138500d0503880d003406c0382e11203000e414000c600c0d5900b003050a02d20b0600445d04039030f5860899003c190f0a104940c200003510300c011032084841e01c10420b44600c9030781401c0c184040c611080309541e0000c000d0300c010000941305140d0700d49844000846610000f04620350009000310082a01005980001101d03c4584c0003480641c540701c0071540901c850300441d4005a2003500c240003c00c100c84481d6030041001c401401c0c601c00f4100d0088450362009001f503440f03a441d8407038860301c3d240a268200c000c1548002460a16040c41180008900d41c02c0c0243d07004031204010408a003000e6044454050703118030204018 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 721550377 1250 721549127 721549141
    0x6040902040f141509031207140709020c0304092c0a03090e07211d0f070f0b0318031201180509010c0e1201060f0803190905030c0d1a 59
    0x6503009000b040c18010b0b00480026034600307a0062541c8640c0010a2400700b0f0100f803544404d160416502c1c143d03d8852030445111021004005007039040c050b0a642021440030031420345007504071303881082814410003800102481c0401503070141c606061021072103e22202814000004248200c0d600115240042d03c4403500013403004d60543c82900c031001c43c6a95103504030f58528044031810040707580c0c0d03020800c1c120086e0a22814041310741500181c130740940c040740300d840c4052585448841d440400b0703506e007400b030401c8040014000004c540c2d94150806414880310b000192000201550190b00c124407004240b040d6260590b809001d10319a6941e180036541c11402c61500c0c2071072a05d40300200d180c0344010300074078440740825258081d44003040720a024134104003800d008901d542c0c0e00390220340001072232001d80003044110019615030407200ca424035007100c60b0302003c00703000240e08100b0040d100800d0181c001602110310314011242e80c101a0561011200f40340c0840088400300509 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 721551627 1250 721550377 721550381
    0x1c1e0c02060406230702010f211d1203100b03130516150c020d2405010b090103052202130f09052503150b0402090d0303020705011526030405060409 65
    0x10301c194814100c0c0400265524081c98070845d100640050005038603400058040ca08401a29000c10070004104043e41c01031403c8840011401145401c00707200c0c4041c504d4104203080c0b20302900310000c3c0c03131810811100e09040d5514461904072102c044006511440f06040c83d0007040d80001c2600e002220201e015180d40281d4012840d680c40310fa07403080d59140c8a8203031075842560203030036000c00301c00340e440e01c860f40344e041010701c0f201000d000324080c40c0003024041d4900130501082e15948541c0840c0000d02504c10081142100000381c0c90344008a5185c524039246040d0150746a92885656003100ca02414a20002c04180c80c00d025105003000b0000070800182c04404025100c0d000424825200c607561600c0003805401c800c2c411260800010740c002e09840c840200018907180c2504045102c0c0e14100b04268046a03011034054140032003801402484441d038620343c00040e003040c14000855240e0154200c40782d054481d1030401c0203041084401408004129a440701e41d52408540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 721552877 1250 721551627 721551647
    0x306040b0114031006140403052a060a050403020a080109020618030102040521100507050d020d14010e011503050f04030f1103040f090b0d120f09051f021c1e0c02060406 74
    0xc402002040503040c0c00b1b03041d6420303654414040c00380408040d40341102c01400011640411b5414049080195910390003800f020120761501a2101d1640c010000c003000d85a0102c102c6034100701d1901c00594420040715205619500720880034940071000c2030081c019a0001c9030440b19822884805251600540c0d180210a40844150000020060040c0c800a0b41c001020500c180501c110203041174000c0e00b0320310f03600302000400710103500055441c41e17009e0740300c8113214818100520100d104014000d80354012401c040c0541d007014040100f102c0d1000340040d042085c03810100621510820b54201103a5001c401c0700e88030b944130300e000403603809144184030040d40380020030355030782c2042410340804981003403030040aa004c801307065450a8880e1800820008954400b0074559244c00c0c00710640714010465612590320303140d0281c40c21000c1d405209180300e20103103044400d5032060010082d44030309001c0301008100800181c03500c1110380e01c02588600042804a9610740c0039262803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 721554127 1250 721552877 721552889
    0x806040606150f1d0607150501060f030b030706120b03011a1e0a15110109121101140109150b030f0601020d0f1416020316030c0f0b0306040b01140310 66
    0x1640286118000f924000b01d40044400030460032001c0740400c03890010141031101005d403100d0f1400d0895a1450780607c000c2116441c159519001441042e1340b12581c50461041070808003c4840b4140000e56160403d206140400403005040000c1685680003a03030000c00103002444424090740143c0b250f800750148441c0507481c0d5140c01c8400d1205d283c8000240384002c1c10260006090800d02210030a510b003200c4240881385007503103076452091185a10031405a0030b40040d9a20409000303204946903640815030360b0420340f00b000507145840304036046501046c000161042d0301c01c07180c1106005644107100030b682c0401000019800440c22601ca020240d00b0380f810b02c0185001075540f54550b04c0800d00140c00c82d1050010004200c0c020131076444104840c0403075840b183d00091801111108680105080ba6010801c000c042c01c0d949018210a617140007009092454002e41400000c110310702c00d40d03c4000c22a8141d010707a0411001d1104404215502d14205420303052481c2c1520440b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 721555377 1250 721554127 721554149
    0x904021602120d0c0f0212120715290a0803070b04020906100206040602071b080d0e01050306010c031d0d0f0b071e230d0c120c050415090806040606 65
    0xc2c903110a40890b2000c034a0209440d03240800e042c0d501d07283c0019282d140120f800404003940100506010082c1c220b42034050750800d03644d030303440d071412001d015010900d008107242400ca244074612850300b290b2a03030f484504c1009a100c2548000111143d180c0d5000c05494080050404140130701000c80c2032050b8000d49060906403a0901070100e2801c8506122005030070040120700041c600d03400030000d9a01407100c40c0c0b02054a550103000012003039021032210f50114265204140d0486003c01000000b400c001d0309500e0150700107442100f6044004040004a002209001503200e280503440320780600059050313200c40c9401c1c0c0c058080044c0540d202e0000c9000590528400c4900900030f8445955601c80040900b1040d141040c10041110300d0f241003450034040460321501070300e41d0001c2d13140046851041c485014050b4018503c0500c1400d0034484030900c83c03a0050102c600b110080840b201c1e41c449010b80031a0846c40030f0308800da16000303100c1840244015500300d0010740e1012070342c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 721556627 1250 721555377 721555399
    0x170415170c040b160b0a02030702011a0f0d06110304060c0909090c0506070302010f0504060b10020304120b130f0f0b18061603090204180b0106050424050904021602 72
    0x64940d0040111084041e141003000300707203c00c104042c0605140802c1d003104a12045003551a140b4488040340c1c130701c40041c1d000c030821041560900032102440d100c4001040094403100c0800e08010360740791045c0c080c030314102155017000700c0d41d0f010017000e51040840741c0e260f052501c2d0220151408801c0719000501030607010404804074803a80102607806505a01150315000a00c80d403074111300c270184d00355580d640448101c0400c0c0d001c5c00b44190300c83c000004944248000300407005d01403081e85c40865106000501003000702c601c2c08254030750481d007010300e41d0b900c080045a00c0102d10f200204006c03080d10800c0c041044400c1201442407088800e0b105550314481c001c0c00080040241c45021b60081c008520b010034000c9081741406220300d80850000c129401140549104950060220716504030341007d03c20303105009400341c1040c4c944545410300d820742c00c042105081050210000c110030f280681c0034018400c403201100003500a549403040d60a0740d204403c28120140d0203102c1101c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 721557877 1250 721556627 721556657
    0x106090807060c06060e0f0f130213020315030d020303162c0a091113050913060506130606180b1c050c07020d0803150a06080c07170415 60
    0x4080058418450042440d14a440300032207582ca83d200c002c3d50784d00e40d0350f4030100b102c406411005214800c0503030140b09500300b8030800900000002c01488060b41580302ca1401a87c0e0101d50b40080440c06001503160746800c481843c0c0120760b444115071510a080c2d00c1c178081ca8011002e0f5100b40c1d09008400b91a19a00078103882c03500042854616502010285c1801a4241c803031815171550051f20b203121050b2510109811511079101117607a0700000300d00707082d48810004c615409004d090b6480f444604210020356170f04e03081040000c18203501c85000820f0341d00d400c076807924043c0390b0722418041aa5034280c05480025031054065852074042004110704a0000445481e4040c1304c06203d11403049014040060070064078080312084104004009652188010110140245401c50392801d080c02014540310f2445a0305004135086501086515001121039030300580030fa45450b641c0300e19181049508a10460140b07403d800450040745c5103103814810006904151030f004000030f5012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 721559127 1250 721557877 721557887
    0xe011b08060a0f260303071701050d11130f110d05090a02090a0b0102031e1201300312090b1902030108030f0c071701141303081f0812040302090106 65
    0x805844296000d2080402c07100c1405907108000403032001181c50180c818a601604590060303d1f4600040d25145c200d99114012048060043c84203c60303140c0003500c2c030b640d4643c040510a004601c03030424520005c1d80b0461580110103d02c0000380304006515260215039915044042c100b03060f1450030000403038504001480501080d001418030035580d4602c200c103c050001d00a220b41140030602841c2d140c1e901d101c11180706000340c1d440164480a000001908161050707005090b10140c081c51410b0f40b0481c0c0700000811034004489a55113469402c2c10b41d00128086030300414a443c000d00d4000740300c03040769528011251018961809181c084640e41640401c1c0a007040300c5e042044a0046031021100800d07035501c0003002e5400c041e943e250303000300e00d1a01c0403c10312a65118440000030000300000e0540c84400d110085c031035850992001041c2c49001440e130350342002d80f5013501140080c8041400000c1c01540111048240c440000501c2600a07100403400b07046a00c0020501c0d41c010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 721560377 1250 721559127 721559129
    0x106050711041a1003181a070c0818210a0506060d050c10020703050a03020609240610050f160614070c0f081207110c0405060d0f02040e011b08060a 65
    0x61180103103900c400d00200403a0300c0441d043c040034540d0b40d060303403032582421b120308900301802842c0e201c40001825121041c8500014800420032404065500016008406803511a00032103000d8aaa00c5080041440741c0b442801000341c40381102605005820b0014103c00322034800c2050302e4a64070342c6400d0003240c8604507001801d68204900203110350514021400100000e4412210705645c1da4541504101600000398010b801c41c0d0708200300b0840400c00003e030310038030714045d0002d034908071038240415202801003445070080c0e000e44994248140c0c1629034424014202e03076540e090340c11040414414500e0100c840b14203143c070743c61402043c10a0319104100c59141d90b4a10101c40c0e440b00f8420080140803a16124288003108032420b00500b03052252502e52145100400c446c0c24403032420b880b0411140c40786052504111582c0c451403040444290301c440f41c864510707010f03c00a0040c100c2001420100e40c6090048403003051040540c06201040d030312010195155a000d0024400745 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 721561627 1250 721560377 721560401
    0x90a080a02031c170a02160302030c0c0d0803042a080312010f03050307021215010f06080f01140d03020a06020d05040b010806090a150207050f0c10020c0f060a0207030605010605071104 81
    0x15540c540094210500c00050740701804c242c0c018079000c00030300c991f1403407405001c00360010381c00822059407821003044118601c0408590701d400841c1a80e80e1016035100042000b405140e4241c0184050080540343c0901061802c80c0b200303045840742e941c540e03a030708401c01a4000d0140c080000400c4031410101e84c099a802c0b02c0a1881c0403000d40a00c00020504440e9581c103105050000103030300c8504203120702a018203a00ca403151440c0403030003800d940e009071002840c610810010071465040d0304c84001440019100380618491030709050b03040004954000e00382ca400054103020000f02e6900c0300f0320503403103030201d01d000341d0b22040400d0743c0d1641120718685941c040c070313550b4011440c1d05004121742d1a414002524080c11a9102d07402c088042e8038502d00b551005034500c90b28585104104020100c500c01801f0802640d0001803100103250041c0340100c500090071305883c0e03c00c0c00500d0265805c100144510350f91200e0042c069070000e407055400b8a02c000301c92030135203854061040c01400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 721562877 1250 721561627 721561637
    0x120f0e010c1e1502271027091401050901080d0801060503190e2802090c09040e0d02070f1715150d030309050609120d0e0102090a080a02031c 62
    0x6aa007462510006218900742c402d2220b0121440c0d521070140000c149414409486078200460541d48607508211414918130070701c0040008031140364002c45082c901419205080740c201988070031907620403c150805d104480c06c01c0800e070302c09c902464420b03040728421740d107a80c9560380c1c403103c031a22803140a80c03405c005109940100019440355000e141c024840c141806c02e000b0030382d04203004452019030840402c0e040008061000501114501402c41d4910804420000300c1d0340041c1044400030140709030104082500700340d80e2034540c0401c60204555040b501080344c07144002c0c4d91400c00d4403030a10340c000a000081180408440c0c13001807124442c000702182204840014030700c04c0c00810071002e0340b0082000c04c0b81507442700d404c060b01c58002d403000038001c03c90381050741c2014170040c0020f441d68031240400407010085405c487e40700a000b640002c9024501c103219019118a13900580c0c04248a2001b25a86070042804148140708a085401200c601c0c0c0d154094013000c540c801022034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 721564127 1250 721562877 721562903
    0x120c21090d0504061e0210020c06040203010501090b031018050703051c02120306041a06030a2a0813060902040c0e0102010f051006031e05040f051203091e0a120f0e010c 74
    0x40c1c5107080105e490410b006503210020103166a00487e000b000b58210b1540c03019090106504081c8211405807040741020b1002c000c2080100340e56840417901054850fa4601d051104c00c80e920842c0c0c550541e000782500d000e00c1c2c0c0c9041c0a6980c0d915000115640340894810a04490000804641c950341d0080c009046568440c1000000c060604016000d198503014122a6640b050005d51141083c440005814039190f11400c21551034031340306400c008446840d40708442e130042030040c0d1040740c580b200c00220360035280c0b04002e4000e07100002e400ca030400c5001c0042c150040710303407031040200ba4001c00c10f0840342c4174071005444043d01c80d0540c0400c202014020544a90086442c070020108507030300203100050b0540c200ca100f242e00391140b1122600c050208541400b502c7c861042c4a50f080b411810302d040016203445407440078201d801c8400808902600c400e0184552181d080000d620f4428510180070b05941214030340d00b80000d001025407a850360141d9102803a5603000890030a8403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 721565377 1250 721564127 721564157
    0xa05060a05091f0608180705030c060906040b0a05070209090d0804030f051b2508060a18082208150f1f0b0c061003020105120c21090d050406 62
    0x200c2001c0c0c802d43c12240b000c8a20301241e405180b01c01c2c010501961110b01c40c1c606545401c0c00070280800f481100c1c0c0000104020f65a000160500042c40c100c0740d683da1900c1041c0005c0303881c41140c0c00301060314004a039511140d82c016019100c81402a81e009645980700100c0d203446e40e80d02e447c6880822012000308010070301c58803d09150009506226103021042020030b11410040108070325580d002105220303e0801039101f0227050345421a040c1c6800741080100c0b0f4440c4001042c0092113a030b01d40002d5040c4d01c0c00c0400101464111454503030758020b4007025400d41c485c250703c1074000314010700b00203045100000e4840000c00801102441c0341c40341201101144005007982c1c0c552103100700045030021b00c0412002c02801c1613491143e0b00d4000440d441d0410400410420715007010032810070140c1d030400100c40151103c0040c03d074440d5a4038040d0300f200c4c000c0803601c4400b1941e003a8440c1003440301810305070060b5000d80446046405d41c68003200e051260f03000f4600000c0719402c5800403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 721566627 1250 721565377 721565389
    0x90d0806030c03151e07020304060e030c06030705090a0506040b2205090c0a09060509090601050706091b080105090606101b30090303020c19030611120a05060a05 71
    0x30000d096a01a14600d00000e15007150440302400007a13000d020700001010914a0250004030518a401580341c44280a500c070f014900c0750000b409110081c0b40c1861382e09001c0320260590042c1500d80b40d00740554010701135000f0041c81e0b4016031010001103203070328014080e2011111405809460411007550108803013001070349030407090300171413404616503607400500e61058100007840e586130519000d008004203243c1c0c0c400c0d002c1c007404214240c1c040d1103000c12581d102c0b030203003045980c5920305d20b80340d40100084103028110004408080c0d41100000806404991968000b40040e840d421940d94450304140e400d264011446135240c0f000b140903002e4042031102000d04007800e00003d48503460f0031181e0504502c0c2c0428482d440c0c032104140100580560206480d103028020b05658000c0d5840c5248100144074140c1841d180b049190441a14405154407034070031f1014041c149050025900009047c02c030080f40540010003000b0188501031050340001c111101041c43c00c801e0100b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 721567877 1250 721566627 721566631
    0x90218040c3006032018010806161e230c030d05270a03030c020d09033909060b03040f060f0207051b151201090b190602010b01030b0108090d08 63
    0x4400c41c0c0ba6403000000c17504203400301c0641108007030250405102c841c100301d44040c920754004c2a0134494401844002c90002d03500794003841c01246075440315103009007940c820100d00703072007900202142243d02c038280e4880c0900700e43c410f040501c0c4030780100c02c1701400b43c64081c1c440b40340300c603a03c180034603004107150340c02c034a8109085030005a041d10104e00150088403640381e818400e80d100d0241941010750500c50001849004d1025114030301607428000c00c031814520000d40000020781c4609507110307145000c9180060f1103150001c05141516080411030454892500305a2400800084940d6aa41160b2080790f00c640152005906640c4100041070b030080c0002015500740086000100d040204a000320503556228209500060401107140c03003800341480076400902030300003445011040070741956a0114003040304c07698a004144a0514060303400c005140c601c4000816603011362000c5210542a80d082c081c0041c941c00568694005454403a1650300140c204d140c40c030b1040300955 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 721569127 1250 721567877 721567967
    0x120f0c090810020f2712071a07051009020609100e041515050d0908030c09130605060a03090f08030c040f09180b07020705060414030708060c03130507090218040c 71
    0x40c9590404001c52201820002c815203587e00c1034409001c180e205110800100400d020220300d4450140d48a50f05c901002010941c1070b91600c038207004654948040d03818141c0043c10300e1403d001d2004c0e00800800301484041d010b9898902052103880e24118400c0507507210601c0510403a11100088550364030030b005000c5065a10031422001409103c0203500600e500c021840d1074140c0542040f200502c0c6c190b20a03159490150100129205c0c5420b0f161031440c107050000b0021038a003040049105280d00007040101c000040007070402414014100703844801203031128582d103401400085602031120210617401b240240000114542e09075544480c0a10544440955403008950b454001e50030040b6421444000e104171410200020b80050082e54020a52820810100c01441c400580b03c0d003030713145501e200c4c80c0a20408006401c010f0104020840d590316a154a2000c0e0803441083c0702d100700e00389010445850300c40d10310300d42200e81c00a17407104403a009020307080480008910303403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 721570377 1250 721569127 721569187
    0xc0905150d15050d08130f0b281413080a050a12140708070318260304050a090203071709031b1f02160c0806040b060a15120f0c090810020f 61
    0xb0a1f44a1030300340113030040c54041d03169911811103190814800100c591003040741c0304101403178071b146940321200005460003510016035503d0704e1040c1044044140d0006400c5104900600b02000400206282c1c400c0c060034055a180c118070300115403001110a02a518481c18030100c004a10264002d1070303464480e091203074681c540c0c05400d83c080d54599002842c0840c09080c54030340244503400068590814101441c03400781030100007070158001c3d010307102d01180d0120019100a021744044100144020303c90011842c0c45030a0076900e903c40c00040d283c154440c07030a503103418000180c4002c4920700d0650742c00d91002620b0048002d4001803e0005404203404801010441d10100e16002e40124000f030401860075042880c61003d000d0149401142e00800801074100c5041c03040d0300c0c00065142100d030444021050b0000b43c81d1202c24200a2850105502c401d07a0700b1000243c00c4031280342c01da0303082c003001d13200210407030180142c0d180c1c4205081104400c0c464201401a081d40c0c041411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 721571627 1250 721570377 721570379
    0x6091305041401060b13090908130906031104020315130605061b01060f03030f03020c15010b1b12040311030f030a08010618180c0905150d15050d0813 66
    0x506020344009580503202e8110240122081c010280104006032800c40130280c90214000301e0450886068400c0c8141103030b0780d002080c00c0140c444112208603000b16540c51a07107480d102d0310001000f55210845401c0c4403d0000a92400e2900a0b64414011101c204a040003650305200c4007200f80070041800540d00d26003c101c55075540054412500e508560458154500ea070b041d00712241500149941c08142c2d208200003035102c405100f0060580c6400340c0c0b5101c000328200d1800d40414130354203401501900100390360b00c0707040c0a4000210740154441d4109030410423682c442080c1145203181c0c2c4820001400414500303107102d1510341f030141c200e070605032000301c0f01400c6811080c42607000a501d400104242c9078404004041c1388103014006403c20303e03042ca4000d4481c1c030000b8500a031600c8107543c1c60aa030140781c00f1320003001c0146c8407800c03c0c0b8a08283c000c00f03a0150303607020082464004810202500c400b10720041d248054400d400701581398443c4c1c403185c0c125a0101c1041d00c00298 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 721572877 1250 721571627 721571659
    0x40906060b28080604090609061a0f040e07030201050703020c0a090e010c091a0f09060a0810080f060a0b04020d06060305060127060c0f0624150207050105130e040b010e0c0403050703020609 83
    0x4111042c240141117200b071201d41400400bc45014034000042c420341c2021710802c1103643c00304c0d400f011a80d0900309282e5441140c58260f0601c000010502e52064241c440050781c0c0000b1341001344241c0504000300880410903d007980d04200301e000b580d000807298103c0301b031200380a00c001d0484400b01040b4501b4071603600300007002640b000306400e00180c101310a10580200c00a003a10190400030050311500540e1404255a41001001c0112441d11803400706103584450b4125200600341600a200403510360030302a010304000d44645000a404000f01e030921000d400040c0c42140e020891401c000c0e01e080e0080742e000070380c10000c1d221040380340326100011b0507034411400340d1600708020fa039001180070700e4114011080d0b40203034400e00340351400c1c2484950201e022802e03207400342400b0b5160b4892a5040b1900c40e400e401040b41c030843c1c4005c0c003062100f0754000904032805104030794030716603416411100c0c602540c44001c01507840043c0c14001440c042e809409544c001070250451707604551 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 721574127 1250 721572877 721572881
    0x5090729031302032e09060905061608090340030501050405060c090f0d0312060308120a0b1e06190e01020c0613050609040906060b2808060409060906 66
    0x74918004a4540c00394402c210704080c441c1c10120340d000b101c46400c9454034071411440c0c8031400001d00c4070302d565110440030009030b5400340c03882d01d070403030215902880e040315074601c44604020503102003800f503c005541c688000045620442800200010000040c1451420554003591000c1d135840903410590956070000710420046009100104160402d8105142030500203004500c0c1c2c4002003001161540701c01d4800b0313075042000e0303442040c01d948500301101d0003042d044100c4a460704000d400424001a03c01501c81c5032846441c0500030340380c5610500894495143c626000003d400f54020700c0f1400050707001d00000080d02c2e803442c0c0803140c055048900203501c50b0101244d055001c0e03010a50f410020305005410a4412a191040c018052800c0245621a951043c40c0000c2d0780c03415510341c4d40180e11140ea11000620016071070784c20312a503a4201d12007506550304e48104450900b9240b0701041c4a1012545880e11203842c3d000c10311020f050b5298060300d09075298500381c0e00041a40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 721575377 1250 721574127 721574131
    0x9030d050403050d0f020a090b0702010e1224010501140a1404060903030e090c0409021b010204080606010f020a0b0c0d02071a01090e0105061318061b0306090509072903 74
    0x3036035030f19030b1880e10a144000301c130140400800318a1050150075200ca400c0800d01c42500c54031196551141000c0c0300403034040a680031515088200a08250404240028103054405020040b0f50701c810b15104e0b1856043d10901c41c0c0790008a009109a042114200c001c1481d5040f41c0740c6241c1d61928440310188a42c41a03006d440041e1815808000345540051010480070301110080f140c4c1c20042c03000c2240b4000d238000c00400c6030b40001c0d10b4001488140750020024002e4000f95241c0d65100041034590f01c0454086000c29100440d685a0714400700b01d40282c030768401e80c01200d540b01c060400300e80390800d8202d00c2050f9420480741e400b24008203804c0b011a5080044058690704100030300c0150b421010000d54a0380c1088117122007503451400041080c288603000041d14070311707481404403000d80308001074901e41c90200c40321404010070314469641c0085803020300c40c250382c5a2035801151022981440c07550494501442000d031030f650944251129030030310800300c00ba40560b0060b15801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 721576627 1250 721575377 721575383
    0x6031d0615040509120c0703032d030e0c120f01060515340c1404060b03040219030f0c0302041104031110050c011409160602061f1a0d05060901060f0809030d0504 71
    0x30480c02041095408401020503004022b0301c031348014141450013400d840070005c2c6100f856220141d00d00d04a104000e5400340820003030050681d4071100a0307140c1c4405030001e10544550800c98080390317a040c51900d0000c2c41c0340241e602442d003440040d6074000d10700314140d20410a661484410502e010705100380c43c120b0300500c51400010b1903c0843d82c0119060b5500fa80070f0ba09001c2c0800a0702031110660307134016011365681e100b400100101d440010f01d03e800090030020056015024003185141140a9030b03c06e4400b08410a5081c5a031000c46c06988001814070003c02d90001c260b08110340e00282c4038010b418101d0502403100c1c0403c2c2554a9107800c40315a0301d0300c1c020401000c1c000c10204c10b9201000c40c2486416042100007074617a10000d00c5030b40101000c40c0c454400464120000e801040d42c0e0611900d20010903480144a603c4001c1c1070317007454204004545545041024541203d2494031084440c8201e00c1090741d40c40e10090110714640404e000280e5076100c40d01901c1d100700d01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 721577877 1250 721576627 721576633
    0x60e0702010c0915020d080a180b070201050703020906090d1401061707090507090e0c0708040e04021806010e010c0c2309090c06180402090a06031d0615040509120c 72
    0xd00b1100905140b000d40c40501d101d07108032541e00c0c0310354010807982c550034642c1c034201c4d0b01d940c0c41d00044400341c0500c4080c24014692a52500d0034002c42c07060b06401030710a9402070001c0e482e0800114168020720311251351209080000300b80905d401e0306031220b15442802d11140000014008500315241c5901207404100c2ca004e040c1081601480141b02410b100301b010040c50420350b00083c02030000340070700c040030528403020610f001d00c40b0b41a0740c1c2c10b5500509099956841c0e490100144500f690700308d004400c1d800300516420000c0a0440c03003290180d4911000c2d201e604011108854868401d9810603039224001c00c1008248459180d02c1d01c0241c6501486400e18080c0444c03a20f005200340304581200c000d0405984d1000d044510302e1034070014441c110403000001038002c2c415000c0c81039000700000c10015259806412404000010220011007000004c8410362104011560203015510b6045c52040fa441c15074003c0350400344800854901801554880c0300d50383c004440d500c0785034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 721579127 1250 721577877 721577891
    0x5031915050a0f0b011d010309080705070f050103050901020901020a0809010e13020a0806180f0703060b0a090501231b070e04080c1e030a0309060e070b0904050601020a0b0c0706060e070201 83
    0x10407a40100b541c0130b0003c2c81c0c01c40c1034408042e9040315500d102280340b4100350700c81c80303910709100100069030000e07900842a0b60080d540c8207070340071b069402031003203901090800001178241881807003500c21303000301a00a41000580f540d144031440d482045a54140b0841c207603903c80d10b4a413641e000f1744084000d02d0059807120511806070070200700604080c803881c0d0480c0301c0080c802650800c160408825010513409444500c4140d000d0403198012070f260131004161500c4403a8001c2c15041150b0080c0c0300c3d0956583c0c0c0420b22104492504120341d55503c0410004100f462801c04690280004a05841985445500585d180c0301c00359000d50710b0b00b10108045582100a1100c00403144007407070390110319407440c0b01a0781c490148508034800d2607a141a40800d00000c0c0d0805a1701180080a49011a0700c500c2c0280c156004100c20034000e5150200084240d400081c0074034020350048030803002c558401c004514903a0021070200e6403242c851000081c0ca140c000e107090700803030582e00085190 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 721580377 1250 721579127 721579151
    0x1801140d0e07120f03120207021807080c03013c03080318160501050a020c0301050910050a0204061b05010207170c06060d12050903070305030d0501170705031915050a 73
    0x6a80c0041e03000c0f20900129100040019514150040c0d1504001c1102540c03180c10700c000b805142006504440a524040300c8200a000d55612410080c2c44035251a01d80300c7d000d00c200d001c24015188403d0100f80b4407817042d440314066901101c0d46000c03002d01600c070380047d1011200581e000303c43d100302c08000d22145c103054094038041d500035170009141d203048002c00200402c04e44d116003414000001102d43c0e64030300c01d000325a600d5a000d802804103080c40d0495541e10810a03a403075a034503280c0004110404c030f15000b12004c44140340c1d54a104461300c3d81680346025440c4404540c3c0359420042c84000030080b04132011488444000180c07601c1072006075a081c00760017440140718070168240900003a442041100d0f815601c0d141c01502c513124071010074a8061182c0010b0304c24440890701c142a004581c020318141d6001c420441030408003880b14560380d2102d03003d45941038110317000921449000d02230140b10b060080040751026100c1080407001c40c1c40030b03100040c4403a2103000d83d001c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 721581627 1250 721580377 721580383
    0x140a0602010207020f0607020105070b010b0d11190e01020a05010f060f0801020903070e18011a031608100c030b0909070f0501050a0806090c12100f0e0603031801140d0e 74
    0x1084140025441d00a00e54000365028045883d414880d11020400c1300659110b2402c0da041183d1144058400b940c5610112545410504220702034600340580081380148540c03d031140b00c0811444c04610501415040d030349004103207066030452040860980100f8824014012103a10201c000a41107003002c5881140b4941a0008141c0340e00421601d1220340b07002540341c048641044e41c0c0080d07a194041840040c5144036160281342d030808000e4605202d0101e1503505c0210100c0c100c8400131003039106d0001c9400244281d0041e03420040c411016601d042c0c0151028149500d000100b91182c5030001c1c403030034010f840d8102d02d43d114000900c000d215410034203001c0c0c40c090a1150070400c00200007440240300421107409000c6040115026000d16005d4610758a0112688121444d2035003040d603680c052445854100042d8040015101d4641e00c0c0040c01640c018010314645070482c1404200014501c0c0998104190b140304000000e0400d0054401d510a030710012604490900c00589 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 721582733 1106 721581627 721581629
    0x133030b12030324010906050c01230601090b13030f020f060a0c0516060e270108010c09170c1c06052d15011d0406140a 53
    0x340201d8044042e6100342d070b508144103516884002d030481c40d061003a200502003910780100f4424184600000c01741d01054034000708242d0300d104260010810b2860196108090203400d001aa40e0f11170413032001400c02e2280207083c030f041c41406000d890803030301c401040b0040c0560390b4411500ca02c01c0e00030b41d846005140d0380d00c605454101038208111003130304a845010724800c0e00d144403041a10901540c50a41e01c0c000300541c03000510060300a85100d035109403850015600f80c160000f0803c41c0680b80d840000708000e5940132010b0050010b40e0410155417003182110000990300150750381c0c03940401c450321a02c0f488010010107080c980c03200d01400c0c42e414201004800208007401c0910103c1c1110451800014240000e450036070580e4207400c500050708403003400c1d6100740601c140c2200c04d0580c0c901d040300a2030014041f54583d178010b020b01600c400b4400e00300c1c5041a4524 = true := by decide +kernel

theorem cover : BRFrame.Cov 721402877 721582733 := by
  have h0 := BRFrame.cov_init 721402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 721402877 ≤ n) (h2 : n < 721582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
