-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0632
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:50:02.649046+00:00
-- url     : https://prove2.me/submissions/f708f1b0-6ab2-4ff4-b9f8-fd9a6d47c38b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 113489208 ≤ n < 113669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 113490458 1250 113489208 113489213
    0xe01030e060115120e01060302031203060f130212010902090a0905040203060f18060412170601020a120e030a060c0219080409050a0623010e0121050c130b0306090f04 73
    0x1d80310103002e20f10398620881c0866119900503984440c1c00e00c0080010080d40c0c811200d1a0b0081207640001c921901960141c0002084607600780c0b8012440188040056440f2004009409904621a00d120f540038410409502c0460b55064001c000a04015984040050812114001c1604903041ea0344c0f5003828400543c400090341940040ca1040c004802c0d1103c150442030a40d07540c07500c034068411141040104052910380300b141c44403541702c416008503504525260550f0403103111b03005a11401c5142c000c01e00300513901c12114000d0a010303000c150054042170406d054000309859080d00e07083e4504265a04101b254500f00982041012100d055540c0034038070b1040740300364480b054130350011940c4024541d201200528158204401c0030000c04001119074400102c224042007405140041a5000b405c00740003400c0018084504d41c400500070782c0007008040c1c0062500d5105006110030105903c030800081d0a6045c0460780b240b4080c410040400390051043c042c10380f0a9003403000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 113491708 1250 113490458 113490463
    0x2060907081b0105131805010e0601020a020103090212070806040c080c01090b0702040b0d11130203070e0603100e070c331a041104050f03010e0d0f022b0e01030e 71
    0x394000b141c240100c1a030038410048645020300e01185400389040000090050f46c004008a00e580940e001880940e90317488850186c10300848800d80540c104446100040d0310a03401442c0c1e07580300800318894081d04071501480d1040c26007019407164400d0b01407000744850309080300000c1c00d208004001e541040340c00200480014881d4842ca10404106035086544075044040c0000d4003820140e00c40e0601c0c04d00c0d00311040c038400e015000308200802001e5060483c02101d115818540350207821640309400d10840f036100418442e100300050388041141c10030007080b03902a41c101e0b5120b11200703501d41480c00181102524100d445100303e013040104d58a034803c4100608500f440004075442200c040500140780d0400b2580d01a00e0040d4480d401310412010303000b0b442e42541d07646c0c4c00c40d0442d801d050885039850005140c60740041c0d901e103981ca20460088215040030304c140c842c04d0001280e0900e81194a0710740c0514503c003c0d94005d01d2550100c01e400c0c0407a0240b03414071040205204094 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 113492958 1250 113491708 113491723
    0x6030506090a0311010c20030c030f03010302010f020a0b06061605100203070f020f0705090c0d0516020c04090812040f060c02030d230103030f030213090f0b010507050312060d06050a0501060206090708 88
    0x102c40140755204540c543c5c80c144149c0c0e21341010301041d00d594014004060041d47d0007404201d0200707080302c0740a0101480090032800031035000b5030360b41098171342030f041004a401a0200c5403800400c0866040000d506000400c4900208540507031241402840030340504641a41d8004540c007015441c42c0b00000000c8540031100c0c152180c2030103440342003460a0300c1c410103100701440390a01051240c40d91017a103a032101031485a003503c400a0009007000192240c481029003590020710600d8007000201c405d10b41c21511500c0461070a103202d42e00ea0054401070072203500035070000720720007505402901801c4001031018405a481d41180f40411040e0b130343c10700001e81001301680011781c0580c002d0b81100d50b00c5280035548041555600000005400719030f2582e2891800d00410036519401a001d0384d0310340e0b45c000c0141d0300f800400b040604c40143c008003e03c1c0d00222010141e40455083c2c841c10707028860068022070690304251003e4038000d03020b410b1814944c406901000119400f00380360 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 113494208 1250 113492958 113492987
    0x50f060a0f0e01110607020a0507091503020f06070519060c0504030b07121d16060207080d050d061205010e0c01020c2b06050c0c07050102070b030c0d06030506090a0311010c 76
    0x28410b03030700103001240c82c02020040b001c400d204440900120070f40001b1800d11041c8a407044800b416100c000190507a095003c04080c94141c2020500061624a0f042c0c40c1c1c031000074003e241004400c0e00c0310f519085c036060000e08a40b1103a10800d0503c00b80e1302500800d80103038144503203428a99031341c01410b0b0500500e10b800300401280e00c03d4503211a5001000b92031040d009494603100904d03003e0f91120724002c41e00e00c038081c043c80d0000c2d0304c2c3d0001c100f05084542000c003810000090890035920b640c4120059039a559841d0001700319204010030390308146010300b00000789444880c030250b00d030018040d1349030305550147d001d80055907a15081d54104000410003d1000b12580b1500380040c28440801040c1509110070000c43c00101c030060005401d81d00d0803259001d981d0300041ea11042d0500611603500c07020000291010280c0006221100305044005a129903988800f800d2280540f803600d0350350010400d41c0145a801400c01484400401c002c20180d60840700140603149028081d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 113495458 1250 113494208 113494217
    0x60306060c0b0f18060114040b091e0a061a0a0810050f1c05030307020a1a0402060d0c0e0a0e06040c030203010f09052203081806090d05030c070804080601050f060a0f 73
    0x24a02202035400c0910300513110303007142c101e0b5071a0024000c0a0417000283c5004905c1c00315440c0103850101d80403130140116428030350950055040444503008000c05110030b2036112800010200c510480030200f0300402501c0c5916194001320040000e0750181c00c090f94811030364424802c0b561200c41c0d444084000301d40354403080e00d452480144043c80b008002d04940004420800300b25008210391800c9813180c0c42004040c1c240001f41900158181d401a40040041c020b2445aa15580c0024502c0781e07913090124107854484001290034083e50007510302d140c501170a0213130780e00302030064283d00300d500c4c20194110f42c1040b40b403c0605103a88503116100e07031124042846034058032060303814828028850040c1a0780d5040242c200f46090b5409250020800c01641c0300220210311980142c4510300070b0320b5001414071303085903d90406090121708001c100441d100103503d010051004040c0382002d0140c642c50402000422640040040e001d0b030020410180499070040c181c0300c2407101800e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 113496708 1250 113495458 113495461
    0x8010e1e010908040b070209010e040809010305040f0203030309011a040b010e0f0105072a0e07020a030806120d080a06080703150222030f1b0807030b04060908040f060306060c0b0f 79
    0x1401e014100c401000380801c4400500803800240c0e4000600740c41c1d00039286901c80da6070740c2141030000310317046401521101c400e2210700711030341c030a4100507040ba000d6200103c214140c2d0300068199401a100011079a549500882809036140c40160320b90400f22410011015890000b1b4140217240e42028410043c1e2850400b00740c0c020b5080d5001c0d19080070010381c041c003101a5259104000f14140b6502d041d210000144299446150b00d214a50a50242c00900400c3e81c0940f0102005881164003100000301c20a0b0103030b08118850380e40610303030740e04942400d000c0c0f000740440f1927613004514030b5081108107002144800700e1045550400e0400103a88541c4010300c60740c100300d800092150000007510000c20b00802c691002d46c450701aa9007540b21246a511010b906c102070300c01c90300c480e0052002000410501d140169025000e800041082442a81c4000d040d078080d400c20150445030340e00074406c03194140f0415018020f83c1c04c01080c00071003038a515180010081030a03409104520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 113497958 1250 113496708 113496763
    0x60111070b0d060b0f040303180501140c0a050609010209330c0a0f06020c0d03060e06010c05010b0301061509060801080303060904050a0f150f0203010b0304120c050f03030105040608010e 82
    0x900c41ca00408511040c6902c5d52000d0f0025046a07100744070507000950b0342c40d40c6400f2071012011110031504161204007441c0040404882d0907000000c8241050003240c2e038640125400b48120b074800c00c4081c00060b503c0210301c082000342c07042603041102d642c202c01581318581c2903140c002d21200b1480ba02498503843c00c00700c0384d0300d4110001d0004080041c201e010b4800c104054002d044449403c5060b00c80644d005c000841c03c0700d0f8144101022010780d8000b042455000310301c01e03481e6238084c8002050100000000c40c0c2074480661150404524100c0c442c0c907081d5001148070080c1c02c80c1e103040d40b01c95240c99030503592400040c004e640300d28540000700341001401c00004200560048400801c540d260500812013002040401c8503a401c2101c1800c005896100303e030306031003000b2030043c210780300c6031100c2a400703d4085841050094108101001c20010400340c0d0705801c0340d0004541e03a42c189020720095601d01c0d4003400c0c0503070410382e0a510920b0f0201340d90020400382d0941c41c0c5030b24400d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 113499208 1250 113497958 113497961
    0x10021213020a03080c010504031d01140f070605010f0302031504050705150c01090501060f0506210c09030303010b04060315050d110321030105030f0604030206130203030913020d05060111070b0d 85
    0x43d4402411000009621400000c06400c201d1246000b51280301d03500c40040304000c210b2601c817007511300090100500304400d0050101400d0500c110501c0d203424802c0341d5440c02e086541c00c0e0000792403008106010030840c035040080007000c1d0042d0725404001d080a90381e0564071105030040c280b09407051040301d08440000c100380c444417000640240310200c0e06e81001e40c000d180c02d00030840034000841d408030720b40c140302d4116202c054a0000400004400450790552020040c003502031407a13040020000c5590308002443c042c115181446980d5407500d6009011600c0a200300070001f001d6000c204000c0e074602080220305604036120350f54030081d58000904012510b454944062491448070324101c00d000702650580324107070111806000c06414256030350404480060042e4081000140c00410f21401501840e00c0074040b242030104100c002090712846610800d00c040e03012480703c203150942e0150b1500075100382008060040c040c0001038896580f0700a409402000142c0411802040d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 113500458 1250 113499208 113499229
    0x31207080d0b1f050307030b010806100302030a0b040c110d09031a040f1b2d060f0e13140a0501240c050a08030403110f060103020d030c0b0a0209031002121302 70
    0x44103d0007030101c001002902d5600156910b01c00640380010b0f03001c00d540030342c00e5140510801008120b03140c4095500f1400396100404000540e070702c3e41080700c8551250701a1810300c04103070321151070b0008001314052a00d459283e0010422600920410200c1c4500e0445100118440303141c3c2115611402e0031f2020800c0c500c00200282d80103807454102d44002c10402c0250756030a499551050544000c550100e4820142e00800792018001081b81c03034000c610110b600030440c1407601803980e0900000c0c0000381103000035513419441d0010440d007000074001551784184d0500080046506205000c0c0d40030000844107070192640585401e0000d014440c04103103280d000003280c0c02a0164a402c408a03041a641100030036240c07980c001d030f509008100101507400c0d2788001c00860b0303e15020001d00b9040044241d041c4650120082d0116816681251051084101c05a510b001502c02c6c0362610401e103404903000c030300c10b00c03154540a8600c1d2440da08204c5c1044503048250180c00000d00c01c40300e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 113501708 1250 113500458 113500489
    0x20304080d051f03080405010e06070507140a030f11130903080106030b06070501050c22080a171c06081207020102030403020904050c0d06050627070807140c010b031207080d0b 77
    0x3d40c1c00700108100704100140140c500a030388541507542001c007072140c030340203501c4014065008030206100b107216454034000484001400c4252295594075070124050400300145c900000c1a8900c55681c1020a240c10742d685c6a60010810b00f11540c6004007200b4060151008140d03e855405605580d42d00980f0f00f030a030040001c00c41030420064440307459200c00310700d41001d244aa400c480305c489210300c170303001c481042c4043c0c041c8070303241d40d40c10341140408012484024024440c22103140114076510612101036500040e04504046000746010507020089595550400c8600010f0340e000c0240c8040326030555503440030341c40e40d1038507e0400301c89a40080d04007004010b00028041c1c0d98001d1030041a0641c3e40841e50b5120602d400c0501c589030400c0f02d0b11078081c030080f0721040d1040c00034030b50140c060f00d03007031981d00c0e19501c500881e540503500900d59a034440031407060906d000e0040d0020b00420b801400e24002d1140d4031000309001c0c0611611b01c2c5030707480340358a4440e00c1d4800390100420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 113502958 1250 113501708 113501761
    0xd03050a0e030a05070203010b040b0303030411010203161a1f05010c02040209030102070f1e080a0509030f061006031a0a1802090a06030609051e13020103060503030f0a0210020304080d05 82
    0x3c000e00010701d1600b001c40c00740e00c40e600b40101f00115043c280310700c4110b00409000b841c41c5982c0e946503440b010b0b03d402c40d11411840104154040e01905006100c2803034401c444e200400d0303006099140403140e01600e20903850791652400811208541541c2003100c0702820003010325920781c00020002c1c014200c440b03070103500000c0c1c900c04101c3d010050503421840f42402039090070724107079100e41c8120380074001818203008010a400c403034043d4014101e003840040840e0240300e8401c10f000d00300070056400c03140d4180c0000050001540601994081440c00c00185412002c1c1c040000c00c0c4681c14841c04400e44c415058540860400e6012158858006040c840c045640c8142c000d009240c5032140001c0d1510709000700d141e000e040420750b41407d1004207140d199440b8240c04802c04140600d04906059030780c24005a940c8042c800b4041d007010301d80407640c607500091000b07410440710800c2c2c40d0410380f04004100000350f18800352a41105e00020000d06039449803640e00f000254588a002c195 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 113504208 1250 113502958 113502967
    0xf020c0d0b061002030a09121b08011a040e0d0807020f011802040c0f0c03030209030705040e0d0e010912080d020909100602010609020a090e04240207050c010e030d03050a0e03 77
    0x84540ca03003140c082e1800390b038641405545014100e8590080034038140008111190810100c4d0740149200c0100d40a0595840c400c001130501e0010591258822507891351502c4421080f1240b80d500100440e40641d014044c4003c004155601c0d144e00c000e001c1c00380702e100008a48011710030010b08801075085002081a08992182541d80c034151480c100d12544c148281088480d20036065481c0c2514642c440000b4460590741c11740194010203d05505489007000009041c1d90302d02030540300540c040060310402541003801454110824003080c10302450410400203071700706015034034109801c921505c3d01c0700700d826071000180c482d900410758440078543c01c0c00103640180b4014130403256160002c2180e295240c440da0b040e40501c1030004003040040e503080000c50a0903901d16030007403048203405000103c080c4241c03450580032801c00b8070030b0fa010580c81d0070850200010301c2141c40909089802030f4000300002c2d074038110404100c2c10182c840002c5080b2000d01e400407c4452240c0342500d8a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 113505458 1250 113504208 113504213
    0x5120a0c0608040c09110a0806010e0307030305030f0603060c04061107030c2402161701091226061c0501090c0605180d1703090c090a06090c02060708070f020c0d 71
    0x303010199801c4d201800c8211000400301c0c42442025041c00301e5a0b4081d01380000d045040c0e48a030710062030181401601c2038981440d42c1c0c14070502000d50f100351503040c1ca90411102c6000291070081c10713140a0392050041c00f03000708210041d10200d50203071a2000ca400c00e0501c0e0302d0305000041c3d00082c05201641c5001c1140e0b02c0c42c24114145820001140740c01c002c4515040385e0b0b900f07032107160358928841d040050002d102480c6440b03115128040000c290004c45995407000460300c00c08040000d00003000d03140c1c207a0560010640129420101d081180c1001c200040c649205a400d0141030003403100104c2c108002074110f0740f440b030b820100d482d071219940d040c00b50143d805100154000759944c140b45445240260340c0304841c90f0000c2e190400c0100d90b84040000da400580283c1d000c2c801c0207001e610a9890148040c8594001d910208a1610301034010003a01d40c00040715040d134010104100da0306510440e1786920900a05c1c002a0a00e00d05805904201145840d45d13089080c00c03400205 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 113506708 1250 113505458 113505467
    0x61201090f05161211130602100501150815120c010e0d05030d0e070b130e0a0b0d020603060103060b0f0702090c1204080d0e03120103020108010b1305120a0c06 70
    0x4a5840c0e480034448407540c001e0304411038004992401d581c480d10549031011522440074000d100124200001d108419001c0340310850308429155030600b200e50206010f042d5041c000300030014400c1ca821700403941801403150103001682c4d943c804010107080040c00b000c0d024107440e808810007800e0341000303411008500340c450025110325804603145205144031410003c641c01c0144e07400602550400d64a098860081c042030a0311500364402d500e000700d0000d04d488000e102a885801d41052090300d0300050a016090042125001514011540e82c064481c1c46c9002c0101d681120304c243d03240e03100300041e80104000e40104109050125400044080850060220500072940704101d6607500b04164614400c001c1c248030419004404140041c0050014140c1200340c02c0000ca0140030011640745950800782c60071891000540040043d075030001e811901400f980c60f034140c503054414080f119950401d119040c0100300a140454042000b4810308142d1907014100701c5c40c0d039643d06c00080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 113507958 1250 113506708 113506711
    0x712020d0c030f06080a0203070519030b010e070305070905032d01020406030f110c030d32040c05030303060114030a09080f0703030501090203061e0109090c18050409020108130c03020612 82
    0x10f64403480c01e08081800c6030000b4428203859401402401e15a0038241440030000384010f0840c0c2913004403101000003a01809842d0281c0024950b010b428030306942c00806891010780749201340000301409100da41c4010a800c413a805074075075032030010200cac41d04408112070046541880c55101060102d002036064010707807203480d415081482001070700d500150461060304c0300e10f44164800c1080200d01c07107070382e000307000c8040c02070380041d08400705402c2c00e031055032011400340194081e4801708010000d031502c03190007519003980194294070748100082c1c12148284001c0000840210005546051540006c817034242d00c075500a464443c2c40d00c5626070340c2c0000340100d01003814074002048285031362085d68072450000300401110001100c201c82070201079003680e410045c15030004038103035589019a20324082e080da51002f5038a1504440b0150000350340150f4400d6042a000402503a4084040e641016205920001c50340c2c4a24001c000081035030700003904080049281e0224041400170f05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 113509208 1250 113507958 113507981
    0xe0f13050c27060702091504090f02040e0607080a0905030d0c020d170705040513021e0301050307141f0207170109020a140907050a02100f09021c08030712020d0c03 72
    0x4942c1081c1c0c0305140d11607074a038202c042c0d800c01c0c414413105000d03141400d01c65400418050410103036414002c041002c0ea40d04640940b05007621a42d54400c60806104292002010b14080c10142c201503030010000031010708140d000780c1e103880184040c080300f4011600305040310b07001004400702000707010751030f01180c011750404600398412549814030b6900d050b902c54641d42c2c0ea50b900d0103081108000c4964040042900307502e50912440e10340c8010b005075040e070102c1507500d440e01c940c5400105407400f00c042d00f01380152050400c400f10755403240424104c010131038140c1b42c100c1700c1c01001d08915080c03c80c0c1c051860201484401196600190f1200044500a0f60ba0700c42d4030b91101050a90031140001e8940c03c82030b1000091515841071000d4406102c80d441075802d449000c03002c50043e110030000380390b0110f0350340040208501d00b004c28880b800c1ca401240c0d200134031441e200d5601e0750100808800912002841c004482030081d4122815440c101004010385410920010000c000051b130340d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 113510458 1250 113509208 113509237
    0x40509010f0608010e1003300315080307020d060209040b100504060f0f0f0e0103060b070b0609010e04020109090c0507022107050301020405100c110406150201140402010e0f13050c 79
    0x1003045d40c0300380c01281c4544a00750a0380d400314a503650300c3c50501c1e100760302c00c081c0c04661002c0b41c41409203c0500d45141c9016030380801e84894402011000c02101da10042d9070703610800c01c0e81c005031900c1c2c0c21420303150703004100161220b020303d0126014201d02042c03558080e051502c1d0401464028000d0b00503101d96664a00d0f0303030101e850083c0c5d04402030382d4803075002c02c00f0b250540342905d20640360042e00e41010300d8080740842d03075141000da0980295a00302e807100c48150401405040c0041d40e60b0061207203100c550700d5420150000303004061180540310015444d403030309443d40d50088084880300d50b8044c01d01d0442088910248140b24108241040e00f80204280010740f8a070500139101910303801865a400071602701b00540d403138003214200300c1d9203403c036558490403560f5922640004040c8640c95020482c0400402400c4500342c142c0349142991250900025036882841510320000a84a0f00d140e0860500051528004040081c407864241350810407410550400361440344140c240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 113511708 1250 113510458 113510461
    0x90304030b070206160e0904120215310b0c070c0e0c070302011a300109030503040c06081b0c030c010516020c03011e0b06130308031503160302060f040509010f0608 72
    0x8121450303210000340707580c0111f004002c1801719002c01c40710504450359004070b030455203d0302180a01c01200319502c2e0389007041885405c1e84071890080d11855601400c001031000040c0d659171462a92000d0009410b8020110780032007000850f101d120041c0c80300310001c1040745000003007901d441d40802801c0700154200034060361700d0400f2088414607644014814658558249919205682282c0020041d0310403102d0440e0030880a10400b19400d00039074840e82d8915140c1841600c01c5515404001000300705401c104088003075504410640040803500b56039501d4405000b4558010700041e614954030b401c00340810b1f14064140b2031038059140d000d071100c81d01048109407c0b030303c0d1001001303141e52140440184842d0164003c0d41201c0005100a00f0720301d091a030262644169007046480c02c10000c2407024042c8001d001c1500800c04074000c000800e10110340c50061480f51000900800303010624450038030010301a503020f4000a4185581c41da59281a217a5071100c5200c0d50380480d42420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 113512958 1250 113511708 113511751
    0x31104030f05210918131101030908040e01060e060f0d1505060c0d02010b040207080d050402030304031205030601030b0a14090417070c030b0a0603050a080a120e010902030c120c0108090304030b070206 88
    0x68451b8410f198041c2c10441c0c1000c40c4e10740720904101189280d0415640703000c2c0e000001c0c010005440034000c00700d140300c6c00e5814540080e1401c0180180c49206038814484001200300301d60840b818010a40c001045490700401c185440e0000c603008154041004101c8441e890400180150101405ea0091141013002c805000c100e1080c82c6000c0c02107a800c10045c002642d60303401050304680301800307d0b8030300780d0340ea2036401518401d80c0c82c50340007450000a111640d0784c940507100f400201101c21a0320b161a0610140b656405410b82c203000e00c6a2030300050901586044908940800d100d40d10f42d00c0b0440d10f030202810442e400200caa001460000c82e01d84c610a1040e241901d91000043c26607829a8950780c80c9900480c290104002c0505c4110000c80003d00030305484844000010900d50001d104150030005007207102c60203103100241104150f40001041c0301c43d05000c5c20103c0c41ca440c0d10b103100782188140c1e007019024007201014411b40a50000781c3d80d00c94000c00c440390603d1003010303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 113514208 1250 113512958 113512999
    0x4031a010915050d021314010608012c07140d0f050f16051b01090f0510150902221401110d0e01051606090c0f06031104030f052109 58
    0x20702520100d0807002e80900c80c0d41004d2000b0f030b0019000030849900c0e00d00700c072680c2d02030310392100c1c00340c81000c040c00040180542040340540501240b038954071246510b8212401d0031111180f81002d035a001902140d82c030381c05075020325408200345a100345d59100080004015110782c120040d2046d207032000094030156450603060241e051079000164440750700703d0449a0b50042082ca551143c0e985001e1405140240305e2111481d11a88803004001b50a00f04542448503010b01140c115041200e0300110700190101d11080d100d040c440181c882180c40e070a03184a440b0020b0420703d0f22040381c004a5440161080c10101d02404d030384001e401024880000e840310f050784002c4000c544100c080055541c01030018007030b4050080034915001207a9140c91040c0c41c2418819191203410300818082c501010090a010709054201840303c400d071aa1010540d1040c0e200240c00003000341051010040103020340c1c03405402c0104c0416401d03a0b6451540481e512004409209001070781e00040c3c1400c06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 113515458 1250 113514208 113514221
    0x302280f092106090c090603200906010206160e0303070803010f0b1809040303090519061b08060f1906050a09050a0302090612010e011112070201060e040615090204031a0109 76
    0x40500c81c481d10b084580e01c560280c9400f0a007100d65181c0035101041d00c140500c40c0c080194001c2c0b81d00c100003400c01680e0300f01c445281b03a0321400388000c64104111640c00180d0160400842021052a03440f0f010301240c140300e482d00c101c1d41c1b5010004460082c03100080185060398166003041244550301d208003181481226040c041080b6036901074020f034689a0750071a4400c2c000c1c2404075907201d0507696503041003242c1d003d4800c0e500a00f5075800500c0403510417524103068005501144802c04a005040e04c00010021481044859031611403511110605145d06021382c121042040e110940502940c000700b949a0018020745400101441c1c4041000101ca40160820f402511090b0500100f10305072101e5040310341d00e030380300d580b04420240705025260307441d81c80164894528600c6e06803012805006031085a04002050004000d48440e00342c21990102001601811000101c94600016070004440d244040360020510548003c0c1040c2501c0658100681380e888030341000c1100d48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 113516708 1250 113515458 113515499
    0xc0d0309140601150f03020417010203040303060e01050d02040203061908070311041b0302070c0f090c11031e071406070e10030e07050103020c03070204020d060302090a1406010302280f09 82
    0x71840103a5441c00d015030b00c00348185c1c140c1e00e40507240c26114021446450050841117000783e6001003000145030341740c0319140c007400c4107034110006945040c0005d454004525006441a503001000c10855540e640f101e0340342c3d00c451164218055591580702c1d84503103840c401540d0703540c4211104501440e00e031046440c200304080482d0200300d08940100c3c020341040404032006c900d115400b042c41e001100510000304900800429114040200103005101c014030403406d0b50710034000ea259000c2c845502103042c0f4600c0310990b488045600b810640a400590f01282c207008070020b2180c030340d50150703400e14400c0f000c1c2e4200aa0f00080f0301c1c118219a5015091000394210b40003d01c0301c1e40c400e400802c001c0782a5421241070014a4000404070307489122220b000c81d03501c00d8104114213201c282103600c42c6205604203d10315401e442140c0035000200001d04256000480701c14600342c0701c030040303140c10300c82003120b40304032510201178000050f4a074400b0220700c1481c2c0004401c00b00d5140b80c1c07203045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 113517958 1250 113516708 113516729
    0x1314010f080405190311100c030c0507050a0f1b120314090121020d18030e0d08070303020f0c19020111010b1804080f0703020a06062312030c0d0309140601 68
    0x44144d00c03401280f0000c408200c00b0088091000280e5210800c8210310910181d04000f8000c444484040c00b1295080b02d040b042c031034203010304004960080f54201c021364216900704580d610501e044d00f00740c3c061502c03154040c161080017003020141c442c0305200c114443d840d142090301c0440003182441c0510702c075450019112500d10200340c0d44607026000c0010900002504000c07111003a9030079100c1500f8501e400a2000f400e640501d540710b10032a080300c00c01c0d9803490a50103140c4420a55200d2a43c000d001e00d03800185101b2094100c80c100c1e00060032240568220440c880c0c40860807011512082e80024109031382284480c006210715429840001c20400395400041074642c0036120081040e00c0c00c440600202001091020042c005248240c2c082d2140d8140340c608a002c071000c90300180e020710900c00ea20442100242105580b5140403503403182000060b501c41407451050300341000f22406915500c001541c1c06820042503d403040c024408600b5140e031140b9502d020922880601c034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 113519208 1250 113517958 113517973
    0x60a0e0a1a03060111010f0e0a020f0a03030210050402060403080f091906120902060d150f06180b0c120f0c010605091b03100503030301030c090b0a030206190201021314010f080405 79
    0x3903000342440c0024a8140e0004031f90030422103003041c00c0b100d0056001907281c0010303d0980071031400420005035004225803030006a81103440003503544180d50701410150740d0740c1b00400c0556039208140c174000c5038040011540e8445c1310a404229401c050060740c018400e55801c151240300d2045032a064404581d9281c14400c0800c6e0203401030305a040080e81c01002c01c204845001c002800395812460401d6101c0305200e103014038058040420703500010410000000c40320b02030b584401c0c0d8104480e5010750040d200c501d0458254140038214080f941160300c005a82016481d22034046c00384401ea0100801c01c15944000340a85051b0458444130031441003078500101204040c082c50700300f2101a01241203a444d84003191442c0e001f07800c2507600c002d00d40f0080003090040d015941c0d410307105a03280d91019265034003140950040380002e0101402c0720002d219401e20075410744200711050032800c11980d564a030011210445622114001440e01d4032100034240034a00340740c062a130040007016039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 113520458 1250 113519208 113519221
    0x15110309060a050d020301090204080f07050312090121050106090b211b040b07020405090a020a0b0a02010e07090e06090610051e100201050a1a03030f0c0309060a0e0a1a03 75
    0x81e030384006000e009001050041000741942c5101031800382036048030041c1d43d9410081d590703140c44181074a03042c890380000420303c02034402145496000301400d0358951200c3e0700c07c0c010b03100d40038607481205ea0740e000c6012269042d0342d15004281200d00a844040016842d0000c60b125407040600c042d001a280b200c00c408100e0440843c1984040b4440d8031290b040720490003402264001d900580407000b0104a0700d09500c0c10f8820643c004203540010602c0601c6a4040ba05027541c80c030076071b1201b000214850401500070741006810f0360200c000c1c0c0d41e0154071121142d0082002000c86c8010384a5175000070345040000440300d0140200d001d000c01124902400c01000001c010403109007c06000c059140580310008c0f20300380c039a4182c0000c102854032141850460700c00c0c0c00d580980114001164000352008401c40340c050102315111a5201d801040c0d4900d14401c601030990801d03000918025180e910140e21003100d8070403518100b40c2540d450000c4d101d114050050510b4003410408035a2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 113521708 1250 113520458 113520469
    0x610030624021e030a3b060c01091a0106030b0112020901050403061103040b0702010c050a03091a0c120609010b040e1302040e1b100801170307020303040f15110309 72
    0x1115210300c1155085400b840d0542004459074401c030301198400728140e48070350b405c0340c240412803144c81b0082443c8450585043c4103098490b041d03000c031800d185111909038482100321401000b00d64024440403045150000e0f0072581c0040c4620581613550012404500c00d0041d400e000070b05958090f10301c00c01c004c180c4001c0d84400c4059051280410000000818074041e401c03c128400040580ba460300d418490b5400e40020408000c691501c0242000c003908041521074014003031600003109151490507a05194482d0305501d030040030801000000002c030f40040803131400e0fa008690a0b07498000c14850005000c2c003e1f03010901082c00180315110101020550021040300c4540040e40c0540100f01114280c0380070340360f250042080031400380000c10f00034840c0f845c1550541708200c81e002c0024240501801160072401c03001c508040e40050820a5a04c4160000c066a981d503503100000704c40e41030f00d440340c0071410b00100c02e100700c20b030700540c22505e1491144000c5e6190510760010400d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 113522958 1250 113521708 113521769
    0x12060901153605010e0a08031c0609020c031908010503060a09050c0a03030302040906120c0306090c03120203030a0509030721180b120c0c070302040f11030403020606100306 76
    0x514041400102c0100c22110721680c40400c03148007581005040c5000141003c03450080396000b051452800c21212074000105d0340a4166250158015015040c00d100030b00740b25400345101c80d00100740f881075100c0100082084260301250034043d455010030680781443d00744502c81c1d00d90484000516011240e03081000214401e00603503a60b41a058001145031321a03820a030000780d4042410303c1020b829201d5031000d040a1601841260019540d480464106000041141c1d0301c44440000701b100070f060100156a110901031544060004002d41d65003003112081c810030b080070086401000007104892078160002480c2444000c003090b000ca186600400140c1080b104010401c5030b8521450030001401825070060b50714015200751040000c1b010740485403240042161410014001581c90304481d0305a03000300e840a00c0c000402c0003081030710310303042c01104000108020580c2c0800c009110700c2c0110340b1003191203848001181264494000c10813408100c0c00d0302c8a1950f009207065 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 113524208 1250 113522958 113522987
    0x90307080d0605121e16031202010905030a0507060506010c020136090e0105070203190c0203030702040f02120906060a05150408030403030906030f11070221121206090115 75
    0xc41ca19035648046440c0e410514132005071500302043c600c103411660300000c60582c401400800d20320452a64158000009110080500003904d1640b405107000b90031401c1040e82100c1a80d460301021034014259501c506011070350f543ca401c0c00142d06600502000c24010b40680d5101102020360034820b0343c403000040100c100034218810000c2852010b1070f0349010b4081e641021503c2c200c0007408500707641000d0110001c1d50418012002c4c0003002c150b1504450076180f5011104000c1c500200f4154441c00101a41103401d100000103002d9071070b0000d002070420581100c03040d80d10300b08a01d407202e600382c0b030f10355010b12010002c20151038120414403628940309400c03850310f56514400792540d03010303500403404514210800c02429400d4414241d840c6810001403141444849401505110b401d4000388140c5030210048540000d0030301f04c5007010b408d1070458803908006c01403814281c0040d5038580d03040141c400058558100b904413503040311030f103010700b1600c06c0c8103031016213009800c207910 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 113525458 1250 113524208 113524211
    0x130b0702041517070509010311010f11010507090302010e030703020f06090402040504150e09060c03010924240512011502030c0a03030b0a05010c05060601030c03060905010801140609090307080d 85
    0x4100c5800350b6000100030318150200e0000380040516250400c3d0181d407240744644410001003011a60002c5510012003003464104c00440c00744109030380984404000007880d40c40c0c1010001032681140b09a016a4000d0700d544800c1c40c000801c0558408250100a400003c42c0345188a60f00301100134083d16030700280013600b0203072036901240458641c0700c42007407118030301242001032080c04241503800c0190705000d001585840c6000248038030043c4642c03558143e0b074100081381c005100e984d4200b0b18106402c0030a10175a146840c2a2101012802c07090b034480740801c1801c018043c80032070f0304480d00074000c150a681b81081c8155400c00c2045001d09501003040302c5029803006002c0d01096034429140080e1003c003080502100340700300e0f00b015060000d0384440c440030400014000c6d9101c2424680820b02102d010b0b0110050a00d40c3c0c03002040030f090400106002c4810741000f4030400c41400c02010310303500d0b4000c01210311800c1e10040507641040120101040b0b40100505190a42100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 113526708 1250 113525458 113525471
    0x90203151207180b040c020601030f1b120c0603061401090b030619031407050d05100c1202040602070509280504110a170d0203040f0b0705070b12040507050105130b070204 75
    0x1c00190340e00001544040d6240035048403485d1510451084d003c0300d04c0101155815550344128140c4004000791502c46030040c185031601c2c80c022014068110320440110341e41003498042d0441b181801048042401d100000c00e04d12051012849042c00503955840c8561414030220055840a440580c00c4041c03404050400352010020360002c61041c5400c00d801c40c010b86c4517609100079500042d00c100703c802a00008500005421030540c840c2d1100007400c0000414107603000040c001801e0b02241c000702d00010f01fa6004aaa04200c0d4410b82e42c1545030f5460b94a81c041100301e046a80031031b00e5404200e100841c0c1c02e6440594040e11a5100218142c52074002804013019a44100d01c4c0080052a04401c0c11040c06010500c1c0c15a00056003460f042c450340700c404481c01d0241d0700d490500032500c41d0520000300491401000428440c43d59029900307c0c1c02d002c10030441d416140c52049900c0000d06512880845001004610500f205c060819803604582c0d48507030416a8059243d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 113527958 1250 113526708 113526719
    0xe1e010c05030f0a1101050603060601090e06010309050f0a0203120a021e010207051f0c0e030304092c0f0d09060206060d0201120e06010501170115080702030d180c090203151207 78
    0x4180042903170301d85900030444801d041d401d484000703002c00c2c013981110040c40221f90300605810207039902040d01e4005a550200120001c2241843c060610b106511194813401030119070440094000d900b582c0007a040102181084c0c070400c002e000050b0700c1002e040709150f81012110511840d00c00000d03240c074a0b50f40703801d4a0400941d0040d40107071303c100d10b40c82c401c0109119426204656051503c403240040d00000c1e200c2c06141316611000b511208035645504401c41c02c0000c0400380071154a40401c0881c00350360301c0f1000007150600d0b209008101c0c020301d000301e08400032a0b406c0e42c01040b403aa0780c0018000b444845c00c00c100d040c0040b86824074800080303070041c00a405503010080181d90300d844001072865598a58200d143c004003001400a03a0518400e5080c266650405c849180c07220f48080b451417003060380e40c40c0440c1c43c04141c1e02030282150700f69500d4a00642025041035102c1505604910003582d100f0032038014203917104102e04040c0c3c54110030741e206400b5a040c1c02d507101d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 113529208 1250 113527958 113527987
    0xa1a040203150403030203100e070e060919090903030c05190309030c0b09150601090302010e0607030e0904060c032a0e060c0d050715050403050307110703020d050606010e1e010c0503 80
    0x40d10204d0100f5004820042a21000c00c000380040080c412302d001c46081144000d00a0781c034020206000d0f540000d03e0000c0382e100c0c1b04155a00c001c20807040c1c100696502070800082207280d40c03c4000900b00300584d8502441481079480031703030700c0c8400f107400c0c450040303016002049003220450500a44600c0c400c0800c2040c201144510030440c06050700341a0500ca04802d40c50003800303035040c072102030700c00c2c00540da10810001c550482641d00c02d41e2038400d03090a458101c1c01c407060682c030140000400080062542161810240301e4a041c0500640180802240381041d2010741e440c1e500b030204c3c002030b584a8000070b80c1c01e0001514541c9810150b0210604014a00d910030340880e80005503401006180051403072440a1220b040003e82401d5900501c82c0c032002d459801000106071001c0f541400070702c02c440003142e00820405a82d1102d08c0c002d80c0b030320000c550160200340380d00c540402600b08201003444006201c0003008507401c0b204015909040c0315581941d00d0310007400542c2c0890180c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 113530458 1250 113529208 113529211
    0x70c1206060510030b240f030c040317071704030807020402181c0b060d0c05060d020c0a060c1b021f091a04081b0604051c0c030311010e0a1a04020315 66
    0xd5aa010500d12884800e0002017004441b90700020351001481d400c070b10401070161041222510307903495070303a00c50b0107900d58240660b403c0544203500380107101940a40c020700405509205841020300ea2441900181d554081c910019110040030014480107283c25801445d03048083c00b0002e144c1c1000b040400c40c03004a030b61481d058248104213410a10600e046000d0b4011402c0380c0b0352007850303001d0395400c1c2c401000c0c1c031415000e107001180c02c682100190301500e87c010400c034101c81c1555820304000002e0600c1012810109802c500641d03a0801d94101d6030008d260090303c40d18029801e250080003004205071001c04003e82c81c400841c10301002c622030442d0580803143e0341e8541e070500030303103074200084a00c0c44a4000300c0050b4006564680c0da00781e5040b41c1003200c0525202d40040790461100d807880100500c3c00180311008030406800c40e520b0f0807880c4100000304103c86400403c10790360903a036000078060a0117118030794014000c4441c250341c018070160581e00903140712400072040690 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 113531708 1250 113530458 113530489
    0x40b031f0606030b15040302090603030c0109150b1008160306050904120201110c06010e040f12030501030c0b090310020c1c0509011e080604050702190602130b070c12060605 76
    0x40381c1d801041000c0e8540202612100c048481107040c164128902405224a200003030003140d034000003c120b0355003403041d6003070702041e13030000c0c42410789900c1d040000955210480d55020318000824046050104100b405140036458415640c0c84403016405180c080c0e108020415455640201383c50f1107098031907025500c60311502c40700c0e44220902070300f0b4980180004100c68410301000002c6c1c40d0000e00d8504556261110359180c0d01c035410400014a08110080c04211180c1200450f2640c10340c05503040313034003509420b075040d9154625003405210741442c0c0b56056008401c111500d02c4a64014480017045404540841d200000032410441c01070070184041440850000e009507080f038017170328034015001000c000310304881c4d4018103141c6000d40035a01461b528000104281e00130040c4000300782c0080e03400c452041461400002030341c41040883c04410419000103600f081010540d800d4135400842916a1800c0c2080307200f331800003410035261242c4400c0300103520740ba095100f071120381 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 113532958 1250 113531708 113531711
    0x5041a0a06030506061603030b04141602060c120a0216050604030e0301050439260c030303060607030201060e0c030411010206071e020f070801150608010f05040b031f 73
    0x242480200891161258454414507050604020355a038442d0205c5440c5c02051110071540080307410210000c01c1c5484216420619240c2000c28030000445654403440b0407010100340b00e104480c040fa120340d810b0b02e4202700f0f4503060000034400058050034540c0210a8440141030048800c203c0c0e610707802800013601c80341c012209000c2450b610408c840035410f02a0004d0009052950300e00c0e42e0440140300800080305c07050050258a071911a42e032405107035002400d5241e5455680c0e01c02034070742d00c03248844c1c0060078540c000d40600000c40c0c51001c42000802550440e602c540900440d54884101202107568401d00881c60941c141080b6000703102d800740854403031916180c04004c44200050741c90566004404021210758004000f0322005000468144510004102640f80407500800500303580209400401d58100550011809004541c1d180d00c0040d965032003600c4400c3c00f80540706d2190b0039075105001e2810039401c452003003000902117820158024040742c07405000e1004100a15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 113534208 1250 113532958 113533001
    0x30106030c0503070801090b0106030b011206030b0115020a0506010509040c0312020607120920180c030405010506241c0507270b030415020f070303091a01030503220504 74
    0x600b401c00284e4081c0050b04002c00c406007140d255444681d00500c030f800b0806849068200c6580d110301001c5004441e45102803003559107a103001ea209500900448200841400d1400c801c140f00064101311150070402502d00ca900f00000d104400d040100203403200c40700c0d0b1800200251003081070040a601c180e01070041401c0070303200101060010500c186040703080419590125000540b40361034101816102c0e04040000c0010810450550b210380559041e00010080c00c401346800951140340b08100820940c0d54200410000d411000403650541d1204805044041e25180c0100b1003101200381c8415144a90590841621801c486c4c11002501c40880100034041c2c240005980008400030f9604060414240510f0340c0001000a04403046200040380d4001c402c0d411102d0382c01011070295900c1141d403c01602810031000116a00c00801d03200b901040344885209058075800005140341c240c260f2401e40c00300c05920140f5840c074146060000d4550785a11031000500c01540100340c06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 113535458 1250 113534208 113534219
    0x1609051b03010605030610120c0c2907030c031b020a0209070305010602030d090c0e10140922050c03030d0c120b0a0506071104060902070209070f020601060c050c030106030c 76
    0x4035001011511a40d8414401031280f41e410000342e81d841001641e40b510340c808031690803511030454022440080e4641544a40c2c41d60b40607940c4001c0d00d020705880001141400b8540403d50008003109411001880110b100356100ba040840d03504030718600403460219141c45102d441c06084500409a0304c2880e43d20110308008009a60004050500704031662418401a44070700c84d4a209071090b43d5941000e0f03003088654170155000d0096014031404a01d010484240b80340118007030711200c1040c80064642514000c5c9070284140203003c5422481d60100703c101404024a8000b251035002e601105055900c0400180100070fa4a03c008503500d800c400d0043c00529100003c2e00c2c0032410001142440e0703c0d44010713641254016220f8076039605407130030302d0107048003111140b95001d420b2000c002404185900030740260742c000c423183c21840d00c503207000742c42c2000740a0755040541c1254004110f805c0c003d00d041c0051a005a0958a082040200090841d41a50400c80d01840410340620a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 113536708 1250 113535458 113535481
    0xa0207110406050a0506130308040e01082a0f030c1f03060504050f040b070504090504110a0504020a0e0907140f030f061c15020405040e0c011803020609040b03160905 73
    0x806001601d04010701c5003044085014802e00b40a454064000040c0d0454801403074001c40d07005541200103140c807a915107600d001101800c0c070485249110fa40d541d12400107004810702c0c600c0224003c0124051028024030a03200d040c4850154180180c10050003280c585058070b00f6010324219400302402402e40340075040301c00f5904554020351600040090700000002020b030003940291799400385680b1a42d003102c9500c141e4201901c1c00707091000b0311080026840014007840d00c100d88564405446105110880c003030b99a450000038044a0030028170f0401401312034200207145000000040d200c48980351552102c0850752000c5800000c100160303080d412555003100003100e4981c403006a046d03421f0001280400d02406040d001e59203036659034095070485000f00000303401848048136428031140c817589407050040c0490305155001d1942c5103808908015a54020490383c10590560b0034000141444040726400d841811942601940071100150081010400110300d034640740701d00b0070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 113537958 1250 113536708 113536733
    0xd0506040e0d080a0209060c1c23070620070c0317120a2a080f070503011505031308030c0a090b071221020a02070f120201020604030c06020904050a0207 67
    0x1c507035080a084205035076071195845412a24040d80582c84140a00005079180b0503907105121502c2040306440d030014110500d41829041e43d140c0300016561510303900381c51130000e4201300e81720008000030b1000032096480303403003402c080c240812000c01c621491140e0543c17250f04280c0b000d100240b41001000b0b02c02003941ca0401120940504020504120140e22200940084509511000100340700c030603030b01c3c0c0c541070240c014a903c0c0519440d440d0140031800291844098140c51000088800340944201c82c121104c809051080d500c03840c000b16115000640801800b1410b410350001080c0518050750007140311010907650b41c11020710183c01d20095521488032a034043c010b00c008168103806014480b291810400e070600b500128804401145460a90704ca51002c0380411441d0360025190041d500c50f1407541c140d450701c82d00010102c072925030000380103074015800034002910465000600703901c80c0d1805418020750f94001800e03610101c400c50b101c15808116001030203041003006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 113539208 1250 113537958 113537981
    0x3240b0301020c0613060e12120a09020901050d05010e1606080708010522020c1002130b12070e01020307201513060e1210090201020705062701050c030d050604 70
    0x310700c2c250342c4084840c1c603004002c0031703140300030a04007948080c00100d07004010a46808800d54980d40d00f041c10b900d0f800d03080902a01c41c01964403001811112180c4901c080407074000380030070307480c0e0310707040401840c1c0000940031507040d500c8014440c0000010030a80d9104200f0282d41c0300c02a007000c5008042c2306004080b0020810307104010489a100c0301e40042c0403e003a007507419998500b0b1203900c8040d124180d01e05a0364070a120700d60301c40c3e0160303038041d00c40c0c001348543c2000d80b90b58a00d9507a00c10b001d00940c0002c0302d0045c0000c00c030028054a184001542c0600549040800f02d40310b402d144500c00c49805401e00078001041030500c0c1c0032118510404040d40520300706150700e0746090002001d0b02580341882035010744c50040380c0e50900a034100300c44202c111041404d07003140207406003910500817400343c403440c00c0224680ca440d2042c2c5140c10f828071303c61841d4210308a580204030280145040c14400108039094070b82800b0b0000700600d241a000108050400c00c0500080300d2110494 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 113540458 1250 113539208 113539211
    0x90a020c120c250b0702010302040e0f0405010c0e030c0d050118050f070905090a020108041b03210305060102151005101e0212040e100807030309060e010806100807020703240b0301 79
    0xf032181455402101c10143d901e071aa006454002c2440140c000344102e81184c500311000700c041152011061509501c29841380c0c000380032040c0014425149401307600d0750694590488000744810f030400c2c10818032500d0050001003600c40018101080340801c0c940c1c04ea919400444181c40007003000c010080041c0403043c000c02052400094203501e40d0862070009041101c10004241401498041c40d04213800712030b008511150349203841e0520905103042001c000c0104002240c02c9400791040920540d810f0300501204509480303041104840200b8102c044c10241101190a4031000a5541c25548944481c8000840d40b00c0d202640e42c100d200c1c880c210f50000c3c110b1035030101d5070410f46007111504c2c41d100102d40c451007205910080d96400140049c89421000014503500c6000c08040700c0d180d0704c500e0021000900111161007080fa07a094220794101c0c4030303038500c51060701096403003012481500c562176140da45035045044440c4d09070341111b11400c0305c612074000c10310800c454941c04400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 113541708 1250 113540458 113540503
    0xf1311030717042f04050c0702030111070309120501090611031f0f1401030617060105010f050403080403030c0206070203070906080d1707080c120108010212060f0f090a020c120c 78
    0x35481c0303004c004024055450059203d40010381d8400c0b01e0f248400d814000c0050001c1e10701403188440c40d420480c1d00340c1c4070798204001048040111f400f280d040e51b0b0941d544c1640307203043c00c0c00b203801c2003038100c4202d130300f03650302c84102d404603000b4400c1e003401c411844000b60b9079003024044107001132006003d4454091049500b04024050040038000700c1e0348078021014021032900c0140c000f0b201c140d02c5405030342c103201c0d078050a10401044081c1a1042602c48103042e80d103003207003141c1c5800b40f8000104201c00412044c00424066050300000600c0140001d10344440c1c0c1c5d000c80d0130f0403240d1740300c181010745812013802100014000001103505518100071011001d0220300b030003102c0600001c3c1488034520205008403041011120788000e40c0500701101d50b5030b0030445000354440895030f0a01402d96001c680a07281450508050190040c00e072a80320b0b100d07200700180700f0005803505032150740c2008440d003d80c1c2e051009000c104010124561030b01240c40410342003415100512000041000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 113542958 1250 113541708 113541713
    0xb1201180b010807030b0406030512030a0c0903030c1e02060c010507030b030c0d0209040c0e0705040f050406120b1005041104030203060a0b010c0f020102070e0f04060b0f01020307020f131103071704 87
    0x43e03401d80e11080741d15022030020490b0000c40c0c01440710303410281c49400f032a413100200c81c2891300218054030020030100500540c48000b141e4044450000030001400342240002240e422041c144040c1e0306004020304c8038120382d000841a80c00340e402180d0694640e020404015018420003503804010b0f000341051f00ca8082c000303000701c030b180c0000a00c10038580001c20140f000d05a684805012110120812424481c2029045811610410485503207000300402c01d4100303802500115480c0390078004144071035075620004500014046903525034824400582ca81e2940030740303c1700190030724100760340381e0950040c903040802c000c0230f550095040000144c3c02c5d90b8000c1440300440d42080800012900c60310040341040556400304880d980000706000803110040d0f03034030340902c0c40b40d60100a8048640c0c00c1c04000d501c1241030710b0140e0024001540542000701540c540703200020701002240382081c6a03a01141d502e803e08603000340c000300c104030a440d0800c50f4025581d8908080416519155 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 113544208 1250 113542958 113542967
    0x60f030b031b040203250503011419360207051506030a080c030d02031501120501030b0c1309180b180a06020901030b030604030e01020709060506220b1201180b01 71
    0x90511038081c3d40d000001400602c0180642d251580b07000f40010481e484007030001705650004e008290a0391094405101c1d07501d8240050030100f04188880e00d0703203502d03000003065900c2071440804171064145a14680c00d0094003040c11400e03002c0c10005896007031700c0c00c0072860449840520412001500d0903c50035560000d000c80ea0940d0100740642d6882c1218441411806044502c42c0c026001005020406042d010305c4003c00f01c003a40d4042c00444004141410b84500307210152440f00c41c03c02081d080700c0c01c42d000b09076aa0803144a1081a590342d80350804407081025410340800400d2454000c0116610400350020300306074807800c0304072001d603803a41c0b105d4680d80d0040ca5180d00181d400a40d034020b42048000c2d141c02002d03601c0b82d18090034058407aa10502e001d600500540300c01007000341040c8180e2040c0c0c0c10242445040c100301d1031450034003000d0303019501e0381c2c400d48443c0013400c101c1d0319000b0600c100f4580316440b034a5141c5150314dd00081082000d412040c101445c207126a60300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 113545458 1250 113544208 113544253
    0x90c030b01110c060f070b010e0a0506010c1a090f0a06020306090601020d0801141804050106030204051f1412030a0c0c0504020a0507030c08041706090f010603170c1204060f030b03 79
    0x2200c800d5545d0310341c1a01c51101c2c0c171070703050010071207203902000084e503001c1c9001040c03180310210741c203200c5559244011500c0e01c10042009241d527a621080c2014000d0b540591603008a4800844142d4030300055030038901041c004044072215000020005541080304e15950081c0007030008020801e104440540404814000c5032070340900028080c44540d40c01400701c0300040c540c0384010303450070305003015806070019000503030246003408041010030654543c6401c81d0707206041c0c240300f01801c0c600345100420b09070070bc06074465001d514203070380900d05100421240303025031280442259603246c1841d5075002544079174842d520520502c107a00790400119080b250b418074041d4168078a41c9004e031043d01460b00141c1800030441662070561390001016030040441c0001c4842950b40d4004890070f0340c2c0070740001001e0b01d5000c0c1d543d003c1d05110300b02600d0b15041c0304055460b050035440a080080c3c00a6008000240042c00080a0250540321700f00c02c0346400e4011b818110a00000107221003507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 113546708 1250 113545458 113545483
    0x1201090e070909050f010605010e0315040f05240a140703180605070201020403030912030e100201020904110406080a050f0c0906040302130e0601080102040e0703050604090c090c030b0111 82
    0x11100c5000d14030a0041c09548003600e420402009400c07924280140c0c0c0703118401c500b101d075610701500441c0660040c090f01c044120028001c1c01d0500300380c458040c02d000007030801c50703440c4803010300c0c000000c03010304c003001e030790500e14018440800420341c25410414003d0114001107180242a400e6046983c0403103030300c1446420007080314040301c100711624034030002000e402c02e4507150a0000031a0b06400420880340265280c1c00301c00d44680c400700b8000180c0700001c0202c0c1c143c550110300c6007000803040030b00d01c83c20f00006007041c030040b002c030382583c0d441000e0015641000600380952070b0840b8107945c00c091110300800441c68864000041018058280191144045110280c5694020456000c0c1d075010304500200005001c081c80506085215aa8140155400414045014403c0e00d044425410181c12251580c90301076004000141a56070401e80302c50780000031810305880c0c1c10050808510001b4403914182009084a0440c50717420b0401c50f00781004840c2803000101c070014883e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 113547958 1250 113546708 113546711
    0x601050d260301091a0d1b0803030a050124020c060c03130801020408010606110303040204020f0903011e0c140405130e061305010c030b01050d0b011112091203120109 73
    0x1140e0a204800800c050078004440d1081101ca00d801501840074504842c4207100078481c0d070405901950a20240f004400e4002d4040001c28002c5203981d900004250701c10300074a0826502c515903a03085070f1080b40c89003a25501c40004202c40030443c05051540700103d441c8200500070b07141c0094550b8072110080d8419040840c0300d41c8458001e200710b0381c500c41030404140015580c0c95200d40030b9041489515150752030408001481401003801109250010010707501d10796542d07003008000d400401d088030002d82c00380150f818540782407041005062103507404480846160001c0016102c000c20a2000c004450441c0000d045165058900f0381d40203e0307684501c000c00e480c411009011101c030b101ea040c0301d40d030180090f040080032000700c068002e400a0095500348001030341621650358466000403020800c460742840154001c00a102e4141f404410f46107110001500c0d20035042101007248000069a80300742c41c00200070510106810302560501c0080c006861402d0030520901580d20b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 113549208 1250 113547958 113547979
    0x9130506010e06070507080606060f2203020d03030b040f0605010c030c050c1903031e0903030c0f020901260c0603160c0206120406050612100218040608010203040b0c0c060105 77
    0x582c05002c07044502d110240c11140c5034026424400c0d91003005100344c0a140c0a170780f002c2000380c1410700881341c0342034088200610b482a03c4415001c80d05d015001500070507086c0a005c0010f9507031112030b5440b54065640800c0c203da04204001c204d40400404090b801e15080d0200110f03600800c0700c81e109605070030f00d01d401c492142402d50510305200d108a51099100c00c403400401080c0554034141d178002c1d41c520b03d0b481e01d0b05d0f95040000c4011000140410000da20410001e8415403e840626200f17084035101030710381d603001c01d0700c0903002c5c0c00c0ba4011040b858039039601d8542c40e6140c0101c10b191800104062445100440c4141c80701401e1006a01405040c1000407401859800c07661130b0302920700ba40e0362042c00c00d90011400140c904603109410500032901c6854202840010004a6006460303000c04900045000358806c141c02e21003011311a14000180ea501d105820040291200159a81c80d1621f4000a441c41c000c0c102c46020f54140000340303100c0000103100e03041d0340003540d017828803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 113550458 1250 113549208 113549221
    0x506060409030e09010f060f08010303080c0304050f15091002040e150a08060903091003051b0a03150b070501060e01060c41010e0a080d05070c12020c031002091305 72
    0xd00c42c500702c3c6250404540400020f40d981c140080004440b00d6540f003401150341c2620880301d00e003081c80060b0010b1480c01c042a00c4007010001190000d1141084415200600103058100010b51418451000c1c40408100240c502803142c01c5034801c400074114602410304e210b40c0b036666406040e13000c440c00c4509c510459034880c08801005090070b10222031041c076100a1040c2e0300e5000186c01409210301003860103000b0b0090042c6030180c00c1c02e20f44480e11242c02c107940d90342c0ba00701c81c420108050725481028900e12442407110050000894900d50711003e50030001e09403555a0f1210b06420743c210010081182e00c50a00300003a54404001c006041070300013600202d14980c1c4210001091812207100d00d250001740c0b10850480140090000d1654480c10135211008e20360050242001003002c0c0180c0c1640c0e500466005000f801d0400c50340e4041d868426010b200f1030103000240e8032180d07408105160070403074401401c0900500b5071401c032541010656407645003500d03040c015200ea021030030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 113551708 1250 113550458 113550467
    0x30302100c020a150b010e060913090c050a08030d0c02070501020607030c050f040902031510050d02031803070b011e030c090f0f05100e0108010e030403020d050a15050a0b030a050606040903 83
    0x8070507130050340c00c00f003900d03207004104002c169585c02039000c1035141c01c401d03070f10741068819200c0140005100003103201c0d4041e24030010788132130300b03044070324102860010400707946415016000c1d10181000399190714a01d0260400c89900c15640c10039980310040400103685c0c00920b80713034000f80074507000c604030060540540351805091826542840041000700d841040c650103507108070b0081c0544d5034030a50070800d000c6590350042c9141d0000f00d0401c804207003100c4540007141c000c070744c406104641e2203041c0c2100c1d0654100003002c07107014180d04010030583e01192500c1007a859000343d40c0414914583d18a0160150ba02c9809141500d0340b8011007440b00d0355020310804402001e061101c0d192885041040e45601c1c092034009000303003400801d039291305201e4018a0111880114500387c1580c080040e24400321108603214030034107038044000f89a8000d24200411643d00100359801c018030f8540584010558541c06a03000000c4640031034800101c451700004180e0b00002e441c20030f07040884 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 113552958 1250 113551708 113551723
    0x6090c01300b011d01020318030c03030d0b1206190f0b0d0305041d060a0b07080c011404030f020625020a020402070b09190f1101120905061f030302100c02 68
    0x38900400484110510701264000c403210b42d10036a60700c10782d00d0026040c1c840044034440f00500590003400310380c0790709824404c1c8590205000301101c41140c1e01e50000781c50355000e030000341c8045860740c0391002c4a040c469104440c810303660000d494dc0b440c0c80d814910700c9000c00705844142d161a0b550068140d80c1d90750044422660241034000c3c1c8503d030781000b80c1194000c1c443ca5103000c1c09044658596a05150310500038030004011404841c0340490464054110081c02e803418101001030690388c134800d22a000e00bc030b0390a81c42403454031301400d001c0c0a00ba001902c141c02d5401c020200810b90070700100f4110021250803101c100303205c03901c000b00d2a01d07142060081d0424400a215000c4c800b200200a02c103c020b402103850980040c41e162403a000e10240c0141245070b18800f000018900c000c0e56403161030b040c9401d40b0301542080020b019203007030308815282d070780040082c4000000c00001c441781c0804051203c0608a1039603500070b41c1d0389003151140ca02c0a98546c80041c490f80b0a00004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 113554208 1250 113552958 113553017
    0x50c0d060e31020d05060609160509060f0405030a06090c0e090c210a0b0103050607052106150403110f030c030705010309080c0f0d110109080a1b0203060907061106090c01 75
    0x20040c0e4540303484c00a584580a5900d50f2096030044002032711340c0da14800080000c859035480f00c1c1402580070600c00107030460401103130341c60410312002c11240c501b0080310105034050070000c2001b20160402141901c440d40001100084080c104080c42c140096102c02c4110151500c85400000c000301e07001c220000722020302075008449c0f0120a01c0100d0314400c1c140c9000700c05450540d00e44e80d0064a80e4869458020a004060800e140f111150805210b5212801034201c040c44c40152580c543c0b96440f54100f2910072001d00c845081e1410083c006165a03c2e0940003885000350340c01c0040d0ba00c03da244241170415480b074824104010f00042900d03c010084400c44d904d203003459625a44900504001d880015100012404c0a00c1d05006401d44140c1012003980340050342101124003030341103121680e5100508540301c005841c2002480e100d08508006051640e0500e08020804007a030803604080750321903030a110f44200e0108940c40005001d0900c018200e2801007802258102d40c0c960 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 113555458 1250 113554208 113554219
    0x3130204060b0406111c090b0c0709110a2709021804020d060303020d05040e161e081009140c030601021903030b0901050105070b07080a09020301050c0d060e3102 71
    0x5075103500306015a072080c04400944058514100d1035118030708515822400107030f4040801c0040303035580c8004201c1c03010780308161402b1a03100c0700141c00340c0300ca035104a18601ea0000e5030702da1040e0f00501001c00c1841038543d071003c016a509450701078454501071004d0595001503101104040b07120090103452010b801503445d4068481202c0041a0510069015004580701000714900c00e50844040d6103400d0201c02080d25200282d50b107000c1200b44032020b0201081149030601105e5541c0c0255604a5513802a82d02e041e40703c1c900c803545540e00284840e410315810401d4045c10080300d56202d82e118003131a0300c03035941c040100e03d404a09a00c1000308008144404107259260b00140700001c000c3d03442110b503981c3c13a401127503940310f60f0b60082c0c8484000c0010504c01031080f0320f03a0b42c20030040b07080403e500300540c0000f400c403101079030351480d103000021f4040c5c1001003e0068000038401c0d81380c46c40e071501d086120080500d40400407065032415488801030000d550143c4456401d402401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 113556708 1250 113555458 113555467
    0x51305010f210f0b0108010e0705130b130305010b010e1c0215030a0501080d0c0b04030804030509220e0a05030f030a0212012c0622090516171203130204060b 69
    0x400350b000b0112140320048103414110508804d500a0b01c4403412100b081701c50b4115036075551400c86968200100b0f040c012400c1442c0002d5210768440503242c04540442800c89081c80c1d49052421254a003d005050004642d1010355540e100340480c4041c060b681248105103000344001490070500d80020f00000c000803061002c0c80480b0f0380800e044c0c508007011513042c503658a40507520104c590741d00424031480c14000a00007445016220b40003032083c00c1c1181003038038a100181210b506103484541390050b003000440880d40600410815802030f4000d0000900240c460a440703214801034014140b0300000455003143c0302c2c0d81111000000c80c4013803489542c607502c01840180c940c580c000c4006c0680c1c144281034003e94800240100d200030401542406d0f05200242031a4403070388003d5000d9950754000740400c8061081003415003140090943c8641060881880e2016a1520700c440794440280f2038121060001140d42160321085641004851440090b01a002030341006d8180040400e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 113557958 1250 113556708 113556767
    0x408060117010c031a1e130c021603030507170705030706020307030b0a0509071103090406060206040c06020a080d0b030f0a12091d010b0903100c120606051305010f 72
    0x1c108108022140d4020722014084a104070182c5982e03c1d4000f00d840c0c8900258146440c1c54042d80410800070350214603c50080c0c3d0024060f05500584200c0d441e0b151a4a031030016814040340c018800071034009103035103045407401801806002c800804034000098008549820305041d200f0141e40001100e030f40d81c03511b161240194100f60f501c400840d061080741c90381d40c40c08024a000740c034405049455295180041180d10441541203240c1e940420004034149803528000c40010740415002000d0f18181460541c10546423548a20112742000c1d0174100082c100b0011031341c2041000c036000c690280244006401e00041c0b243d85840c0e0320580a0b16810890750883c50700151020780c98250f01d060796100290032078203444d03070181c1c507411543d80140300701c0103401c01400700d03a0b001901712035203190301140d4241119071100c8034401040045c1001a4081041d0040b600940b6940c0350036401d0045030010b1110100342c0740201070500c442c81072a1902c191180380c0410a429800011002141190 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 113559208 1250 113557958 113557979
    0x112d16080a0b06010c1401411005150a1b1119080604051005070e030c040f02040b0403030e090a0b03061503030f0a110c09060108130f02040204030b0f0604050903090d060204080601 79
    0x12500791040c10907900041c0108c180c18040400400786500503141900c0360320300b282c4800802400da0b01110340101740490284c42d802c036000140c00c070107402c07a541d5445900000c5c10180b012841303400c400d8442139221002400404031042c0d00c01042d01c6404a1040c6d1014008030403103141c200080c10321680c0c04010500400161102d642c0c1070034201001a45c94894040b2034800924100903019840596004801d00b0303d90b100700440e41000300018286521a41084801e80c0b00c0e510175000a000403c0c1c1042925040301140d03046016803404002540760500030a031a0580204088140605400c10f010346840510440f000f41d660b05008643d14100024090110042d08160040c5072140ba81d0702207543c1000c01c0f2542c0620416111411140e6894110541000d00a402101c50300c80b4002d28000580320780c00504003640c40307458451440e04d0303e0758101c081c0e000c00601480c4154141024000d0f007580c0401181c0c0140d40030380740907121108500740310380a485076602c442c0e5240300d000000510130948 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 113560458 1250 113559208 113559221
    0x60f0706020703020a14011d0c0a0323010e0307030806040603020d020103020a0c060213031a0c04150e06030420030606010e040e0a05070f06170601020c01112d16080a0b06010c1401 79
    0x20702d100b48c2d1142c882158030b03a81e000c060078280c0d04883e0303044041c008160494002c80800008000e607030f400c01e003151003003030a584415042c101154408101c038010540c111154640c0448113403420072074140f4540016103030203484071002c0d0505a000481210144c07140c0c070624181c035000003081d5a00c443c081117030250880d061005a400d1100c0c00380f2241e4007120031f01010300914020303070458201130034202c1154100c000f0300c44800601100c01c051000545800014500c640d00070310020b0900031034032124042001600c1c820038480d40007001004400e80c0c00448000b6949401e4600140c40d80010b8031191500c88409001f5110388501710000072644a0007403c1c1083d9181c981d50081e12520300c0e01040c4c2000c20999505025800c603000d0300ca140d5100f03a4901121403200381c2102c103440c5504044960b51008206103002c06012400d441c0b04010007084250154100842c00d281c225207000c200b1070302c9044003000200b0b85a04a00407403421781c4070750103070982160808201c58021005e0364100f40203288 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 113561708 1250 113560458 113560481
    0x4060f05150a090b030601061b0b0109020301061427012d020f0a0b040807170d1505011809090c0806090d081303020d0c0303021e07060506060f0706020703020a1401 72
    0xc0ca048003280c04916030180c62104c20001c0c00a03c1ca50f401c1000a5450118a0400d00c00d0419032201003404994601040e6008004a190059495040c580018214807841c81a001810810030111003014070b0b05403e00c08101313407a55024042d050102c01280c007480143c42640d010355a60100400e00c0c2d003031002c0881142d1058089030144001c0c10020394813000c880320040d021490300c01c0001c002c00d901c40000c010841c40340380c075000358410349244440e213500034844010340300c5d55034104000340203603076000d070340c0988800d01700490700304a003501c0c901c03040d40d060084100c52900c0c0c1103560100800304807030fa000707898802c050380c5107841c24108480d41e41c1c0c20300c070440c00040c0c5040301080d9005803120b610300780c01e90541d0207000000c06219003a0780c3c44411620880c109942000041c2a024400b00700078950b440686055995004908040c0c060381c2021780000c1c4039000401207080250400c400719411143d0100015803104940c6c18140c0c2801d214403005450050302c0c01a4209030401988810b80210 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 113562958 1250 113561708 113561719
    0x5060307170c180115030f090c03050a1b0b0f130f060f09050d0f02010e180c071401020f031f0b0d060305100e03090103020919120c090c120504060f0515 67
    0x450050030f051002d4820301c200072200b8402c2160010301c0e44607800500c01d6070f58102d40842c9105840d07840c20086182544240d8183d005a83c5181c1042114820000ca90a03034181e003401c0123050500f14860b500c203401d80914450000140e030b10480035100e0ba02c0c0018080c100b5011240baa0b01c44000c2c043d4004a40c0176400950b4116002c1264a411b031440821135801c00d00b00c5060b0065a0300664920600c034101c41d0b8800d040f040d02c0d04440e40c140c00481e00c0341d003d142c0207585820b42c0e483c00c072480202a400c90519640140420241d0103003941c1601d50000628800002d07004080070301c255a01d10f2504644a01c850014403009143d01c0ca401003411a03108000b2200722960300480f031000c03204061003000b0203420420004c002c5611a4001e40704140b001020444203031414040c04045001c80d0f804030f030201401840303040c2444904050324008080b480424040003480704802004020646424441d060f59236010a0510130164800304006000302c0e010000741c28080d100084071040414a644240c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 113564208 1250 113562958 113562979
    0x70e010b091318020f0d0605010602010c030e030301080d140d020a0801030c0e04050c06030606040504020403060e060603060c07061104080a03020a050d050a0801120215071101140a020a0605060307170c 88
    0x1002c01e01c1040a40d503043c1101c40e10403c403da00304509160711a00a0760700007080780d00b12000c281903104680c0204141c1d00009009145503001405a4000e03003050b071040d030005c1c00100710328540407810310100300c503620740030081210091140c4458010301c01184042840410040d141c0341d040325010741038900030714204409a58520305040c8905045030000c203c0c0d08809034502003402e0100245030490001000207080680703440109049810690003901d60039200ca1403240e07918020b0154641182d0280c01501640c50000400c103202c0c81124401000c05580e40341e03130302403825000140e5000d840144c0540f0780d00310840c03c00a540d0241c161040c1c0b80c0b03010fa80c0594603614010300889040525548500000e07038a04a01d0042d40103480c070703040c0d030007036800c1d8000d44404400c50001c04070302c0d08c41c903140201804044001810091140c0601e041d10408004941c0440c0d00081e40304499a8030203800300d116034404010034201030382036002038010701080421b03050702900031609404000c0280c1d519404d9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 113565458 1250 113564208 113564239
    0x60605090a0e0c01120e0a0302010b0a0906030305030114030123070f02030a02120711030706120b0603150d061103090703030311030403050405240301030b04050d02010b10030c02070e010b09 83
    0x1140d8242900c0c84960b80f00c00d0041e80554000c1201c0303146030251240004056000280c0181407a40b00c803070840040c2d6549450042d14034018089002400c20f05008100541c115540900b1610040c021060901c0c0b02105221169400350440d000c003400302e26200804c640c5070318041e0b02d6410150b81340350108401c01c2c00c40708024400025030345000c3d03159004001c500d00c860a04217255106c840140e07504031444507a004591030810011004049540d07403030031185284d0902ca41140c41c0041c0d018070a203030800500c40740751940110310480407012100d580100c0748525001d8010203092801040c10304010007009002440030610b0380440307000340c070240850303030340c00d8210f484902c000c03030380200450000e010602032030502551115041ca04e4180006959030a0707091204690001d078822a000341c8940100020002d0034004220b21190600003400290415000a000441e00c07501e600201640e8404007048a03108020181c01840b04440c03507041035841d0b14040455038000681d01303014401810340b4854 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 113566708 1250 113565458 113565461
    0x313240f0902030c0d05030408010c020c030d0f0c0303051905190b0406050d1b09060305160806190b060d0504080d0e030a020307110d060e011509020408070b0a1407060605090a 77
    0x100554010b001c2c00c40000840100030701030a0700e0a045d21144003e11000c60189d500b441020700300281c5800604440407802c041500d08074500d112034042205031000901c809400c0191070307070600c0c1c3c5030078041a1640d80050b04410b001c04c50080c083c2c4e060500742403019050b025030001c5040b101d002c0044c04000c09003801e1200342c80040c8140c94206007690294404224141040b003064412024140a0296281c540906840741a00103a031681c000c01c4092081440c0d1560050045c0040009400c052038034100100c41030351498101240c40b03844040c1d0010560381c903812140c2d0050800d07020001803d084c1003034070540d0820400b01d510b05107001954800b040c0000181c91400309564000c600c1c0046070359031040f031010342c0700500b500000107152a06c006a4203008841501c1003800000568440130400c02c89240c0f5140d008040c52441040f0034031180e1008034200f42694016402d080d034900c0f40c603604030f40e40408801160040400480c0c1c0f4010070060340c00440482314212071403542d585804a8050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 113567958 1250 113566708 113566721
    0x71208010b07050606060a0e0909070e01060306050f13060503030406030914060108030313050c0d0b070807050f0a0810090504140f010507050412050715110105150603040201050313240f 81
    0x400f2540240c0000d01da41c68040024445c0f6200c500e40207541c05161000700300d000f0400e480c0301c0002c0d040312109000e16950002d60500400c85031409000c098503000224805940c0780c841d0502525013050b0f6034080340030507000030b402404050300f01d80ea29540c4050040007001583c41c00c454005801c25151001500061024141e80c1240091031940e01c4401451020900c03115023110343d400754041400d070540c0c90070f9a040ba800c9c001d0640b41c13032070324060100514210000f4400d00501505108040d21618040305448415255081c0400c003a01e44a00d8031000320000e9110b86d4540d4113020400c000c0118005c003940c88108175004030741c48210400c424500b81c4c3c0d002c4660b90001141840b08215030440901141c00950190044e03411842d11540e09500384a007507400a404603c054140d009480d409101e9158003001e5481b40c00c0065903501d00140262001400c0a4100400840410807151420101c03020580d4442510310003003543c0d8502c4c14020350000327441c400c154a4030705c50444040c020300030f04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 113569208 1250 113567958 113567963
    0x70c0612151415040509010b0c12030403031a010201060b0306040e01020903010e0a0203071a0702090604140709050a0e0f0412020f0d180e040507181d0a0c060f020c06160206071208010b07 82
    0x42d00581c00c0031951003ea41000c5074511041c800c545c0413010000901c0b002f14000d070b0199501180c42c400500e507038603003281d018084904580c5001c3c41004080321580559400105c2141c0100b005003868912a01a003c0c2c1050103038954079084010041050001d2aa0f09044c42501501d002c541d60f0030103020106240071041d410090200715000051600251640d07110718001d00001d503c000644480000d00d0044407000c002c07908698003400075140100d8400020b11410903400c20324604014000348010024000401001d1880c000401060090140d40c0d0b401c0707010403c6030300d8840d04040060030074022501d190389a80d515000842c21824501c2064031036074000008045841c030707204801d42c40c0c88016148512180d52074119103005481044141061080b840090030748080c40c1c05c001880c1034180d4424800c0c401d011a07004e8401c0d4011441100d032480032281107845401d5000c00c00000000c594000750320080009624003006105461480d80e9000756807040c0301d5a0326280001101d2040d000003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 113570458 1250 113569208 113569219
    0x10061706010506070303060806040308150d050a1103120a12050c030402030c130216060204030501060503011b0e060403150c0305010f1809080705070e07080601020102070c06121514150405 82
    0x148000d080500044c40034034032a15002805c9642c5044603805c205058070120005410407040c40800b44075955000301e102c60031503000c0c12044142c1d540e0f9941d821a410000c00c44070044481c000c0e969010312050200e80141c0840903650248000b00824003900036a00c0801285071601050780c0d001c46c402034a220b2540940146010003002042118444042c001d1501c8030350200880b240d0365101031119100a4440c200142c0c4490461034200c0c01d683c00c0780c11690091b8034250300050901850102c080c100c030803509008241ca94a43d000c9051886590800781c4203900d10740110101c21b54640c0501002c560941d01003001e40d0329051580c207401003c0c0712f00702c04440398100e440c020301002e521500c2c4051040c03641e5880c01440c2c3c0c3d11709060007a15800541c511a20408002038960801c107803680c404070900c021458580c2c02e41d2003d48115245c0203c4041008122100ba080345055105a08001d07265aa001882d5542d0381d40382d05d04080804101d0140c01300c4510034041d042e4070b80a0301c0a45100804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 113571708 1250 113570458 113570461
    0x10e040501062301050c1c0c031403130b0a0209031c0305060102060f07030e0106030212061e061305060d14061905011a0c03070b0106020d030501081906020a0309020a0810061706 78
    0x464041d04040800400f50087c0c11002c0154048100810109200f0341c90b070404508a0f0309001e80800004c036406001d6480420802440f034500c00c1450014030351001091241c0e448546880c4020300034052100e41604c00c850260a2481e2412001400303400256018059542c80f5001244c6400c01074898584070312000000c148a00d000340c018921001c501e0300001417050f601d0b0001140e0060380d50b10000700d40c11503414030002613a100720b0080307a04118070074400a0b080120102d04003144042ea842c16160f95100440d450360394510b000c80c0c03400d40160114100c010f0440c0102d484100640d4056004d4440d149034000071801b500580b4100c8040c60f980100072110b5205110320340d80b148078101d440d030108001210000e00d446031103501030981e56001b4080c0b000d481902030210341041c0c00241507540716036480d41c131800c00610010307403440d8007200268070b4030001142036029000c00703c5c00035481140f00304049040c0900080400c0c0c1414000d40c28055140e49403d48100c000010180f6401500b0a00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 113572958 1250 113571708 113571779
    0x140d0b0c030a0b1c2f2b0b06010806030c0604031202030c0318090105151801050405040204060201020309100c0804080c100606050307031103090309150c0105010e04050106 75
    0x1030360b0300c40003074407003c60800c1ca250001070310304a1401180004841040c026428000b2003403094040302c44000104440540141c4c030040908010140d9a1240e01b070004188040002051480311140303003181d18045941035403030b007002540e50072280c0c680010b00d41000a4003514000132226450540904140e18290554031000180c94906807a00c0661104001c0022142030400c02002c2001880b42d4440c1c1c165165002c2011603041a400644684400000c00706004a42c1341120040400b01004001e640a640c0060f01e0078041d0381e0019a10170301c08900020041d8041d00114403403030b820402c1d14a4210a0500c0000300d07064081b0000000d402040042d00056188004001c04c2c0505c100700e0b030301100d000d010340c0f0035500301c1d4008a00154002c03050128440d018018824200540701c0e056007185003048055689005569180d88242c074140c031075801000002c421103841000b050020b000c0c0750303100c4400d07aa480e807098408540541ca003400005000b0314042c0390406030035070281c80740d0070321000c007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 113574208 1250 113572958 113572981
    0x30f050c0a0914030c0d20060a080106030b0a09180501050606030c0412060e0109030c021206090d05090402070c03080417010c14030a1805060601031410120f050a0c140d0b 75
    0x80c41c540501c00c03181e0045031607a03007030742c06c51b40c1520903440901d084c048212440401301500b0300c054019001840541000341c1c00603a0941541c400389000120070001c000062185e80301a44003280c11031500205c88104801a800030300c815008000074080c0c3d880301d5045c0640b0384012a4510f404202c280300c24444815242c0c5032000c0c40e4096080400c00c1748040145072b086849210b000c40101c0d158002d10404c504008507003910280340d01d0042c06003468002c0307940c1c0d101d014000b404000c11030700040340c0b4070704d64490307054035295030300404c41290041e200d1415020b6039004d8003400308019007000040700410014020a07650011a68460b0101c12003010340950719000907000c00f43c00e60311480d1419403554288003416007a80500c0052090b82041d200240c00c5034480644050b40b840040104010f000b10002100100d800c1c9104115582960b0305000401414510004003a4000e4060000601c00c4521104065400c06031851940f01c4480040105640c2e44a000510f6081c1c4540014210901e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 113575458 1250 113574208 113574239
    0x40506070c0308030a060303030c050a12050915041101021606050a08062101090b130308010510090f06080103290609090705060703050c0708010608060a0c140307030f050c0a09 77
    0x50501410a580b2541c5080d0160000c40762603400d16075a04c0104245981801480001c1549052031171404c441d2242c001c01311580d04900c035402e01d40368008036000c41410481041c50406500c0651050704061821001000c041c1803514010b100d40940c068918040e0b650b548122403203610745a01d0052101415a034561000f0203081d030029241303c6481c14041c0740c00404039080e50480000490003680e00d40f08410000103010310401030410304c0518006500314138075a06550003221110612000f06904565942054001d8080807080745000030704a42c00481880c180ca2213584605040c0c0c0c840100c02140aa01ca8241e10f48605c0c004040b6149007004c2c25040c0d00041d00c001035400403506c40380803a0082e80a42011800560009200108824280415030241080300002c2c0312703580c03030040c2c19980c1d00c0019000540d050707920001533407900d01078a0b4070420210094541c64492414200c01b4005103181c55160351401c0c24030000032680d20651007180c4440103640c031a540b03800c1c00c00c94600780d00c988 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 113576708 1250 113575458 113575463
    0x512100e1006120209070504080a030309060222030c050d0c05060d0e0105071d03070509041b05091e0708012d030203060406020408070605040302010c110d0f230a0804050607 76
    0x15038060503211041c0e6001e000060040c01915102c1080c852050101800c001810b070740400206000900c91502c1c04580141c140e505842c0c003041007015070403c075009115034280d640c1c00e801e02040e81e04d0785401e884441d0742228006c42030075004c0c5070340b10700f480101c4000c0000100701900c2107602384803528089001d404003980c070840004010b039030a1344142c00c68138251070440108003080700c003802c8030421030444013040c0c03c04e80260200c0347c540b0001c10000f41004c4c00c0203203030403500020401509a40354000c00103140003050700c10709003000f00c0100c1105401c3c90048401c421844001140140100180f5040b01c11014460110300116489555108220088000045202c050001c090380e400c0040c140214001c1e0380040e82c0b18030740780089203000101d91040f030034010148030420250303800030b0210104940010030305100e02c0003440020f0032460000401000880510484024001d8004440085481c8000295000c0d442c082e00155104103400c4002c0c0044001c000074170241c100000504106072 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 113577958 1250 113576708 113576713
    0x10909080c0106030c14040209031c0c050601120b0903090d110102070f0b0d0c021c0503060a120b0f061e06071b06030c140a080f090f03070606030c0512100e 69
    0x207840d4100a400e440c080c2d4801e031240b8018180c148403168400242111212044508626048800020940b10b0f040c0350f00490400110104008886004120142015500c0341c00d503416582c55852050381c0918400098030100451000030304504000011200800001080e5904400e00c0e0f589844800449502d003604502a4490000c1d1220310110003c02410308030b101503444c2c0c101c1d6090003040311519211003003107603c001c4c00010001c80c1e801c1d19490441d1180b0f46943e0300c0c0c0e941004a01c03070700a5a80036568189214288000b4452a88801030180c009440c5510907034960004001d0000100040f0081682c0341d000b511440c0d103130000003402a1803041d10034120081a10390703411001c42a5070302540100b9118800d100f0600d9000d00f41000d005a00d034801400c06101d408001c000c441c0040c05c1c12501e040400c082a07080b2001c0006190704029030381101c0da0707044617282c48c0700039118030311045032100382c0c0d090045801d28081c000c00d0030103004000107020b015540d982860240c03c0000c0c03806902d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 113579208 1250 113577958 113577967
    0x8030c0933070203150a2712030248010203060a1e180615020303010e010602120919050a090f050c09011b170a03050103050d081014060424141201090908 67
    0x7e42c02104400302c44a000001503100c138410341484880302907444003174010107104004201907100d120b1000707199200700020301d10140d148940f800d0744101e4090000c04511669001402c05503005400075441110203840c46010150344031a50040011166280342c03205040c82000e01824013058401810388285080c0440c0c0345940307540323040072031040d10340c107500580000006100400307040800c00d0042566200400e501c011070300080e41c1c0c90088411642c811002601d00d111440c0f20502ca84020304030042c00d140303000d43d41e600514000c00a005d40d031041c2c5403d0000044800e03004005541c042c0e101038660070354201c0360b6000841541744105080743e1440300d803221400c145818401400c00e45043e91000100d950545c00c00502c1c0c103803150b40e0041001502c030700b0008d8038413960740194120b85004400e80c85005d034000c0003c40340c0c069a00400c0c0e001c4c41d180c000a54129000e0dd40381c002919644820400b09203852130744115100e01500d07005101482d0004002202c400d5100240160082c0c05040c2070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 113580458 1250 113579208 113579231
    0x70c030c0b03010303020d1e110f06010803090112050415050402030312042301150b0d0e030310140d081801051207120510060c08030c0933070203150a 66
    0x2014500c0e0000356801c01d010005004060301002a86a140c5140c20010112201c90600c036600c80780040c144000c220840120301e203807d000f0080c5e2120221600c0c11342d030035582c64840b42a40e0744c0200e0700e440d000661410070540c161f00d1500c5101d000d583c104210310300c9032414a541c90042c0c0f1019000720381505c020001001020f07285000a070081e40f00d19004094080445070081c2035540310003103900b8691400031445185049405c0ba441214224041c4035110505105000c000b88064029031074607000020402007414002c001010030303600d140d0346030b10000c84074900b07005041103c20002440d1001c20055042c11024803000c0810400052520502d0440000b030034000600e0b05940c18004128200744040d014080c030b0090350b5101d050000d40c0a0f2182c0740c480000e0202c400103401600040000020802c07080301c800031659129000f400c103d40a10701031201c010100001c5884124510b010001c2072840c039112402c403444507070014028079842004035040c5c28207a0300501403810b201e031b0350b443c03c420307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 113581708 1250 113580458 113580473
    0x2010c05120702090c030609070309060b03120912012903070f030b040c052205060406120803091203070c02131409070302120d081b1c02041404060317070c03 69
    0x22041e5840e8240d5880304114410302c103007075401500e100001c0900380208003c80c0c485101059100400c1d14010801018a0034040004d0420113201c5806000360050010b90418040090100c079406880440b0680060780181e402c84428074019240903418918286040c0d4118000103400d00303000381a5424075594008611885183d948101c484c4841c6004100c207018901c0d0580c1e005040589620320944546603035800c0704007032103240d071418950300c5002c10041c2c3c8680d1700410140001c40c003030300f10b0010345040151080d001117600408500ca9004c541a06540f4042600d00480d841e8440d080300d60000ea0070050084001d0400c401e02550300c842c680300d034090351466540124480c1c0007508404d8107600501211400450300e6154550216407255903a50707000c01c0d03c0f50b00080c580ca44a00c03100020b282000d5030300c0b905580300c15400c10541074414028a03a4014421112100c0c1c0309490a2020303418001590381c544006010301c1c00c0d245ca4500ca4510304e20003080681e20031462000c80d00d403240e84d81c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 113582958 1250 113581708 113581723
    0x9180f0f052d15102c030d0c03050a180305070806060307080c090105061c0c050406030c0302040e0a020c03040308120708130f081317010207020f0901080c0f063a0e061302010c05 78
    0x4405c4884030020081c142014800c0080c04103642ca040c00c040661030724003031b015209005916080100c0d41c03085d4035002d44a403500f900034541c810240c512440e0365066180e42c0e40400d4030414841d008601c400155510000380c0c0200809028004520f90780ca040200300b0250003240d003044100317220500701c5c003008200b07200b000d00c0c0403100e4995079126820a03000400b1501d050802d50141841000184800300c031840c90941e1003402014003580c2c84d4215031285040d805680d100801100c2d000c1141e88005a484205502c1002c0d00e991307442240d60340c1003010103081500000581202d8003075000c0030116421700024031000414442d14440d6555445060202d40600008544965400f08941085107003212000400c0d00088a002802e9410304004a89690491209612480150101121b90340715001a50448500c3c460f00600350002020f1f200c060000b20100700d0106040302c1500114a44a441040208200680202044c1e603030340c1d10609070300c03088442c1a414803d030340015500140c000c0164a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 113584208 1250 113582958 113583017
    0x30c0f02030105130c140904060b04060f12050c01050a080601270303020a060b0102070303020318041e0903030b19140d08031e010609180f0f052d1510 66
    0x2803821589508141d40c5e01d2400e908540c203174840881079170040d6035070000001e8100d0382003031001030200e01840c0002c006000c04d03480540f44442610001030828000e81c81c00300b0f00c078000c40a035510f811a2a004444138421000324401180901c8007051440d4840c000d22800b4a0140103c3d4581c0001c1c1002882e00c101c0c9540202c0050340302c0000312042002e68098801e02d03203001c1c0002c100490031668041e4680c011950380744a481d031101142c5040c0ea42d140c000d40e2035402400320b240f403020022107424018100580042c0d011070b04095480181e41000c16003150a0201c0310301d2000d23064244440010100364002c034469200d48100554004100c0c0180110f002e505411300f51221aa1120034460391090140d01181c02c0c1720030504100320350400c82811011000e02c2c1440010114070721a03005005000884000c841546040c040051509011049116008540d407200d81c542c503051041d81070718041107e2010081d006582201c0c07882c10481080900130b81a42480c5241c600c40c100011141d402c4180355 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 113585458 1250 113584208 113584231
    0xc0f010e100f0b030c01080a0f18020111070317070203030d020a0f080106090e04080d1b090501030605090412030e2803080c0a200114010311150304050a030c0f02030105 74
    0x907100e07401d814860392442207a249424403400000d0000261100d40d1010594107006912000032002055544021110581240100000c51009601101040c4c6c0c14100701e0224241d00c001c06406000004d5240840342e01202c984a2040800c0400d14103030032030348040ba010721007485401010381031800078100004440d40d4007812861030200062010006a0004040c04003501c41840056070401419a125401a85007941d0b0b50a07154003030010800c1c005965844400501406040c2e94440706a008031502641c0c1440220f454904210b120306081d10002c02c0c41903080f60441005001e9080506040b01d62030588110703010300c8862040240d61703043c0c0c04c214210001600c804064000d40b80302d4000b5030316201c075410801000e8001e408280107840c07403c8940440c1044402c041000d400100000844102c2400e0301c0d40c5d0382c60701c0f04440550302901071088142022410b071210244040d28812a000340042c03580456588094034040350480b4151490108024040e001d80c50134050705000f00b506140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 113586708 1250 113585458 113585473
    0xb0103080d1401030302060609060a15090e010801231f03060207030206070804020303030f040c0f06020f01060b13061d09040311010b04020a02151305060916080303011203050c0f010e 80
    0x41d03821104400c10038422035190380c005102181d80042c0046c0c0c45001601c0300741040d2100000111408aaa4040b2103241d01411448403a590b0100004040b2000345d5081c01c21a6261089542130352100d80080b00003c1d07802c0389080400c0380c100b85083d00401460740c10701100c241150521404501500709444894001804404042d81000040d0380b1507050f180014140c2032a0380025120301c0041c281d0800d485100c1f000c18140b081c40810071000b405500d40c001030b19070351703070b41d01945488502c5550813940d46400400101d000b4544119862410000320003100b450a00c1000d8a000e81e4180d40c180e4600c0d203100c1d0b0140e55444408205000310b000b91100104484518019800e440d00c5541c65809940184a02c2101d150001040c140440d0ba0104545441e9518103020106807c11540030b4140e100300414000342e541c8c00b08242c0e4000c000d42140c411001d0710303101402d590344030a1041c82841e04801082d580803038441c0c000743c804040c144080e203005510214220b0b084d14024010214250003a00c0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 113587958 1250 113586708 113586727
    0xa150303090e31051e070f050a03080a08100302061305040c03060e1b19080727050108150d03020615041e1805010507020303060a17070b0901020a0b010308 68
    0x1c45181d0140c00a0440300204180d00356400803520b040700f91980e070410759482d00301040402e000b090300c400c503440d03e100d24104001480f02ea90701c80c41d2150170100802e0300000324003403c00b18030190640743c100c140b6514140c00340c98211903c000082098000d084104004401a03981400824240520501620700282032008200c00c651114030520145407030050104180d629804ac030ba40e101c20403c3c40c0c1c840030000c0c0c4151807460300c540302841401006605465075050340040c0c1391401040030781d580030510b0b120003100340b801280d140502985210f15403000c1041d9032003034080542c406102400440311034200400301d86d00fa044400c1c01c8025800050030410030035842240c0610443c41298148040d01e407680500440c2c1c4030040280301b0f51a101d6541d05940650003040002c1c95030701170002c0000c0e2602c0c550003500c1c0e80060b00c05510881484200240c421540803102c0340d40701c002c0d8043c1c40c400c0c2c64100503407135a80c4440c031103030b0540c06200f49810126600000d030500030f5010304030080d510ac4550 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 113589208 1250 113587958 113587979
    0x2701021305010c111207090501080105090d0c032a050105091c0203040e04020906011403070f031d0607120e10150503030f0d0506150f07051011070b0a15030309 70
    0x9410140c10852882e00c044040307010300c440c4100456081d05c042002c43c500d00116401e00095422200c1118105000002c480405501c0395110b0310414082d60302c2d10522100c1180c0d03c10080102500048212610307402041d1700303c06c040e1582c07041045840c0c0328400c0c0c0d6540b40c01d603003003102c005815030412400800003041042c0000221010791024610f07241c01c1159258250f100500041e0164805800154059020b030400700b4603643c50b10566522444c2c40f1000520450611841d14000f038200300d500d0841c40d90101024406200402c064009030f640d0400441c0c640f00030032a007050298a0700d1590b00c012405100301a2410740801001c01c00b45100100903110140c26448503009600130480280003090f2034054581b05180040041f519031112800210102800092031041c035100082c1c4520b00c6c0080d1004041051040303044c0c1e0705410054420714101d820000d035810311440100017640c0000c50b002c10302c41d8000748000340042d0f04590001c105242c1e040e581c100310013042c880c2e4030621600405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 113590458 1250 113589208 113589247
    0x915020a0f0801050d0b1005040603081c1e020a021c030b090f010b0901120b040c05030f06150427090b060a15020717030903060f01170304031a270102 66
    0x4900b4880070b00e5241030040b55646658183c05000c0400c4500481c1e41001015100402043d00800600529450307040c030001d107a004240070315102c0300c203050b281d20b20109405528000764000400e9500024040100c030040d43c002034002046010f40c400c1c2550104a14184040d4044507540001e2941060001c0c00401007020701034900140c0d20400402416200b04101e0724001803e2030a410500310164407803028241c007600d0103920a092070b03903215049034000e0103107115280001e0003003c103466150903c4403040021403007801d89802080280018204e020031504241c085800050000c803c90858108a07440080101d41d49854942800813034900341c08540003401c19289640410410402d003e0340d550301d14401c1404141030141928240902441076a80141c00138098600e24a00383c6594000c0117824081c24444940c20792807072184d804000151815a94402680e80308101d0912200ca00030320700414615204007582131400510420402041e84100311400160720f03030780c0a841d0311003a401d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 113591708 1250 113590458 113590487
    0x51009060b030903041403070e070e011b020109030201030b2707030b030313050f010c080d050405010e071805100312110615061c1107080c0106060203090901030b0601030915020a 78
    0xd00500c5043c0c1400301c1190102e440c22195040154404800700f402c04200e54041c030301050601d000c100303da41e0004002c280b4624241d039000d48540b442500c8096000d40b41e84040d00160f1340020500065001c2d51001c010805e0080c0380309410a0005241c0d800000000b070103420780111003017440525a0540200401501c00f10082c40c1481d038003821012105960303100343d910400312071800007c0ca034020340e402003950f07801400c1156102443c1e4862805000c055a04507465840c0c20304407102d0f01000319031031065500941642c14465541802d040107420042c0a91121041d00c5800100240203c0b00703e0000780a141c8403200d4040044007002e0400300c0040c00c40a51400398500b80d1403560f120f008541180442c001400010706401c03101400415040301008130003040014468144504d910151281a9841f0000c3c0038131a04c44000700d0b1a4041d410615070807050071401032000420b6103030126840348040c500022844d4994940010742c0c010604c8400529034001104401c660340a12812070442 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 113592958 1250 113591708 113591729
    0x2010b0d051c0509031906110301081b120705010e060c0d0815060403080304061d060c0904050a020c0a0215130f030b060108071b02010c020a03050609060906090a11011205100906 78
    0x4650402191b01c1d1110f010407500100012008541000a04e0b400041c01f04260154540c0702c1d0303100c9007042d0313444890344401c41c44907903501d103000501e1602404444090403118050841d02d45030100640c0c10320000031645901440600c180359090b1000c00961200c00c100303555440300307401c003030042001402001c4d90540c0240301c200700a0002c41c07451421243c00950000e030000d40c03020900300e00c1a20031544078000394140204000d01504e00c3c0980003038940da50b030403501000a42c40e541c08070703022481030703100503032007500107c41c10009880c00003201c0d41e018500b240c890346040c0c8510088490404e4130b4004080001f1144003d0052003140160030740e0008080c01c01c101141401280a042145803880c80c0711404401c0001d0301c11a44503084032210580c0c00703400000d406440f45040b585030b410803149403102c3d218036400655581e034000f0300d42d4010043c0300003414009485458031100b0070f00c0c8008143c1400041d00b0300d5003c210141c440c091003001c06528917841207050100c1c030300965103c1d911158149 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 113594208 1250 113592958 113592967
    0x1e1802030f090c06030c0a0c050a0507141801030311030417010203150f0901050906040f06031103010c0206041703041106031602010b041a09070c051c03060501050316030c02010b0d051c05 82
    0x3e0319180c2c05c503a000002040013584800c1101c104651100b42c852005281e13016040040b003c01070300041c00c03820341c4d49240404040c00e03450814040c040141e007000200b40340060004102180c01800004140700c205015280b1f825101c807090203038040b03521201755882e035000003084046e2040c80e10f545540202110801d03105840d5800080d41e0b80d034180580c500c81e0413031401084469840d075000d529042c0e40580144001c90396410709034400013001d95014065401c00d01040091791010480a100c0e82d44880e2004070041314000981d000d402c001c0c411034038554000c02c1c04181c0e41d81c0f6009103214020121001600e42c0d24248000d00750b0345415200703070095080c11080c0d400014401d0014280807000e846445840c1c1e5001e0044900c0c01a1f244041d015009a01100030441100643c9110522030341c0c5060014542e01c0004407518442121109400001d807004000d070300c1e209421001815110748000724040441000249820711160700071525036109040d13051800c0d401d0650301c80000028100b041c00c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 113595458 1250 113594208 113594233
    0x6040b061203030a050603100903200706051e2a07080f07171009080c011404030e010e0a080d050703120e070e09031c06140f0a1e1802030f09 62
    0xa9000c013900380c0700c803562a0400200240c40030007030741122408050007800740600742d040140042c1400c2c1110020740101c00315500c00c14000189440848515545903482d00111000035900031046d0941080030036001c20a58011648406030404454004560400074291000c1d13070515082c00d80c2c0c40100c0c540c00448034035040800204000044488410310b00f1102d1b0300c4002c9490401000c8801110204d2a050502040c0300410010300401540c0b0002001341d5603204047c1c94409004690040004910424030819544102030b00b031901e2601a089071810340d01c07003a2443c1440f40b0031526000181e00802d040d0b051561126154035040a0944100003c1031640d4099880704124094910b00b030184a0110314204c9041041707580c050400da6258004c01911200702c0c0c060500c42c030503410369018082d5038007007a1030000c0c2c1d0844840402410021500c1c40d04a00008401740c0c02c1411000748070f003000c0000c0f0700489400740c042e54546c41c0d000507660720704248140140c2c10701402d44a280c0d4840a5501e02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 113596708 1250 113595458 113595463
    0x91b030b0108061309060203070504061b080306040216020d080d1d06042405070c1a19050c040512010209190f0311040207060e0c131e05070c120206040b0612 69
    0x403c0341d010b03102c0001c80b448026000c0c0c0076006070700c40200011310010820010aa010015105484590b5902c140d041d050350680703106044030040103001c4000420100d038140c075255005180511240b01210483c82c0d15030005a00360309240d0307090b91844070000b20791080c40f5184c45a1884052001d05800080011074002c5640300d0005100920f840e40d620100c540c0c0c00901d21485a00c1d6500d07003018030891a020000424012180108a07900800c000506185003074841c1c13034900c43d51041c9a01294000d0055032003018003005040007210200800c80412a900d800d110404a51b8915001680e1910801e003441980000e41041011088043c0d01c18080300040c152884100c03074108003c1d04a0414280014009104000e40280018a0b108803028080000702e040440400111101070996a440c4111003d40f803c1448031165103840d40d070119400c80260b445240c100304140383c000c1250341640e071107060b200149482500540d0017901040b0130000d803000704582c45881692038084140016000c580d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 113597958 1250 113596708 113596711
    0xc060c020a060b060a0c0f02031e16090c0f030f020c010f02041e05090a0203091203010314010b0123070c030b09060a0f1109120a080a0e0f031504080315060301091b030b0108 76
    0xe24041f1381000e5041076681c100051116801c407048940046030100040540daa2a803184c1c0ba5181c030251540046c82081a00c1003400041113511085808050b0b11400c40c0108102e80045038542e034203201e014090f030000d10440c0d9028962440040e070300ca040440c0f0551102c0d6405505419403561001480203440340071485422080001c40507803a40c5442084904010318140280560100072000205002042c508205203035100c1c0d008000401c4044011505040d01516039001a00068490a1501008001008150702900f1040405c54032690f4650b00840c0540d000c1301550321060a000c01c5036a01d00c82e00d0504492050104210f4841002a5125018019440e48621800e42c44401c10180074441c0c3e030500c580c898621940d031121900060310800207500880e001b9850800d03110380a0a000401c002c180700492a900e0740c0769690340d5684d819610040030600000103c4800503121380710940694041d22400ca800301d103050032446101044418003401c07500300340c240741d6808096600020440d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 113599208 1250 113597958 113597963
    0x20c07080706090315110703120e060f0c070c08030f040e070f0909092108011a0301030c0e1306020c030a17190e0a051504020102060916090209010c060c020a060b060a0c 74
    0x31721142034410300e040010000c4a44c0d50704000d038001880c004042e480b004030031007020850f4040221604013501140d4800c41214030700a100c883c1f0700810302010404e4003030a6107511a82c0d80804186e21450b00c0c034115007102c04805012907002c1014891000c200d01003035032040c81031030a401c3c243c0303500f10b0041c100134103803003250321b45595402c1ca10280302d400842480400000002d108008562400060811009204a60303070450050300c0401150b5441d0101ca0481c1d070080c41c00c618980c20301198580030600030300f007045034001c44031040e000142180042c112061448000d5511005540c0700507001c1e40d1259034012411078510308101590942004443c03041da50044001082160711826500d000d00c0090301514071703c1000c1e103404881c001e1200251042c0e100b80d081e12043c1d25042c10003961040102083c0c851040004000e00c1a52440d6010340340d2070105140044041d030a644032142107544000081005800c000f8581050198900803560f00b603000b80c40c01440d104252000030070120101000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 113600458 1250 113599208 113599223
    0x80901090c0803070317090c100c080a0809010c0507080d0e011b050304060609060303050d09020406050d0c05150a081303020a060203250519030b060c01020a0207140102010203040f0b04020d0510020c070807060903 93
    0x1002c1105d2140080a02b0703507900c00c681c4c2d0744d1100000300c0900041011900144150b0910f01d000c3c590f40d1148007a9021141e0020845051030641081c07080a072201d50b01042d50747d941d4468008035540c2191703c0c82101c1c0c10584a181e980e040904180042c1d0341990041c3c24441d0a0110400000790720004031064000e01e503900049018441c400900034000951000381d0000100c642a024001b02504680031101d0489100d030b0849180740090b200ca00548480c078011803002d030006210100c00628280321544284141c2d0100c2401d603680c181241c0060b951000a000807410154050003103694042e4041c07014200141040d07403001d1543d40c2e13618008400010541c454a8a04003600c40900b1f8841c0011028020b540b600b0342c0c810000d548a503e41b103204803142040301907041950042c421640642c1e0448618840104181c40b21094003002500881c2c20004150740c1d0b1000c15018000d003102450740e00c1000d03a503010748610452400142c5d030000003135038011410030007400f074010090320b0403aa1300404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 113601708 1250 113600458 113600479
    0x904320604150e181006061b0b040b0c070602030a0203060f12060c0a090306090f02090114060a0c020d050607021b0415050906060d06060e0109091407080901090c0803070317090c 78
    0x505440c602c3da0402d0414824188031a0900d06030b0703003206c0d01340d4100c1d50725030241d8030040c00c0e81c6080c0c00504c903010f0070110440000c5004100c0075903041703522243c1e00d003204e071611030715540725012a84102c1d000c003000307070303000c0280b0a13903144c0034006e07007100c030340440781c0240b040202c1802c2500d810010300700100c60b600c00607040d03018901525040e0011a00a802080392a81e81c1c00e000603064030846041744100b03101c80010480e00c00c440c0c840143c2031006040b0307900344012000191049800200140e900950845c2c0f004002074003082054490ba40e150301810380010200610701c0704040c843c005500c154108810300c034400000011080031203200b282d001c86981c840d840411014070135003800c41011402e040d004200c51307420681c94440440e080c1d9072820740543d44d42d00b54080b10320001c08901c0305c03100b41010803100c0d4455054240c201c18150b000140c850519513400d0800340c0e480d80920b0b03c80c2c00118010051681040b81d0b5020084200003500b030138981201103d445414166455101e50000c45 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 113602958 1250 113601708 113601721
    0x3060a05060a030209160306050a1809030504033e0117070e0d110a0501050a230c070e0a05161704051c1d06090a09020904320604150e 59
    0x82510045801502014146c2040b45010010700030244400300482d003480c0c1700040700e00b030841040b0111203078000600400c0400204d14009840e10400c184c081041c01e21001c0042000c0a224060044120880c80046105040c180c60074400c0e046010314200010890710200e41d03000400c05041c07130780d05e40141486a64600c01968000006810242c01c02405401d120070032050f21400c28240e4005c5400d440404d69641c01140c440c80f60b410f03607000007072800303120640c208d03180e01008500700d1034201800e0030031070407641640c600f09140d031140002011003811322070040b0803886610342003001140c4042c03480d081c2c541c000c1d01c0b2140007202c0c5588005560300040a100050041d014160b01d42c0404a03451105060002c10300308101c5240404603410b0616501c6901c1e02034119150790300c0182c1031641441c504203003800250800341d00e11b5081a110400f10710805405054204000072140c1d904414004c03911582d48401030007403095008500c0d100e076040c80c5d503200142010890700818105102c543c0c642 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 113604208 1250 113602958 113602969
    0xc07080d09210809060105010507060b0a03080f041d01211403070b01081006060e0609010309050307060504031704030c02060901030f0e0304080d021c0f0212030c03041205030603060a0506 82
    0x1d500180500c8034040410700d5a149070700c8074009070700c100d82e5000d94503121a58816102c1c0390a1140c5400324001300002400078207030f500052100030004168201250362500c880c60540d101e40860340c45080001018040f103240c0702108600c000c8500400700980d030400410000304c000d0340c459407015042605030300c000c0018031180c40c0701c0303c6910b4050b42e880781520b1414911100007030040d1201c2d8090501080450540c40c0316400841b06030740d903100810b070f04807014814203a2141c03108604150700d400409020450820041c80d444d0701c511800115031500d0b0400812081c4900c1015014800b940c0074080403d0b8810b003100000c90b0100c80030f036500c00002c1c005178001d003040d181c80d014003400e000700c0d10f240700004030103401103070340040a56944c030f121414120303110720259001100d00c2c00c03c0c44510010724803400b03108640c104580100c802e0005802400d007e25002114480c039041800010441000101c001001c80000903040150860802800203511610010b1004440300d541e800001d0711542d50b03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 113605458 1250 113604208 113604221
    0x2010309081b060609072d020708070305100e031c0209040b09070e0f01020118080c030f0d0207021f020307060b060904110d06050108101206021201060f14030c07080d 73
    0xc2080b0648102c08800800303480e208103c0751070b440b403070044000441441c068000500d82842c030b000b4404145e0780d4500850400c454a0003240114402c441c0049100c1c1c0d010403510000c0c50081d130092055a803100241025a600070ae6440090b4005000140107507401c20070398544c40c80251405a19456120301040040c0760404030107030b0103482e050510120302d40000141580724400d8480004403060080164266807501c0c401e4501c089a1224038000710720808042c014a405d0001074038500380f6001a4400b203500701c1015a01113650001c0c044e4110700d004a0202a404010f200516003012640006500da006042c80030b4403c40e211f01024400d40e07110002c454140d88000d0040062644801c840340c40394000b030545c1404145131070004121580035a9085205943c10744880c8012418840202c43d11100e520080b10901d030244a00a5225050342c8194060f201e16543c12401024509000b0102c8100740240c91506074104244011444900100ca007110f4002c00215540c11020103034900030b059 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 113606708 1250 113605458 113605477
    0x3041101022b030b0402130302060c030919140a150807030615090501080c090904030f09050a06050703080a0510050607110d0c030210110d2f07080f0106050d0201030908 74
    0x2410218803800c4140d0442c4124501d150b540800c0091600800e100c01c9210303140c40400000045403082005240060041420104035070550f410042040085071118107003140002c80c1d59100d010a004802c8071000c03544c095001103c580e120245405400680d40301191031440422140700009551203010307412040081210205007044016040341c0148440e05500a1a000603100c3c0d010500e045041010b6420f81080141080003136281e554054030420008a40042408a585800181640c40f162504010000c1783c6030140d9900103841e009215a030002c101104461501c400d00040945240030380003542c40954110f9a503040318145152511995010741c0e0f88a00181003440030488031001c0941117910a44010a0070301c0a03010a6481c11458440b615095201039106071701c3c80e204003107586810145109070040c81306888848161f11040f00141e80c2103a200a004000303400042181701d004440c640000c101d82820b0030005100e90700d2204019041546034403426090092010890318000d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 113607958 1250 113606708 113606743
    0x40902030307020a080c0102010c11060f060d12120f0c1409040e01021603110a0b060402070c050619020c010c02010507060911090109090c060305071e02011b020726030304110102 78
    0x1d42e40e40b10590b64441451400d0300650030311314ac0c08200307400748a02c40d080c40300d108040c0ca52562804400d030040000200701541c0310a01b80900b40204600910700c3d60318031081d0340d03581460b400c071111280607541c030310f0a820501c2d0f1034450640c0c3c00590021181ca07504604440c503030382d142070f1400000c000d8019030301c00c250300e075100250f058900a2542c495500d4503100351199001c1c0031404981e1070302c54250500140043c0d00c2c5500061092800b58001c00d0f01034440c1151a415544540204032240c100098608140300c00d048128000c0360100300700c44000b81c091800042000e10f6a0008040340510380c001001e5680780c5030700c2d80401101d001d82640e0400040c1c254400d642c0d507100c004000d080494010b65981c40d0009003c105a44070380a42e2344a54000e0715442c0b010300644004a6032550140280350031550f8a00c4403910302c480d0303100c1c0050114100e1703000b410b98074101038540503800b42c290b480030324100c4a011704210350000481507036441900020381e041c0e0300c011080182e04000745051090f1501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 113609208 1250 113607958 113607979
    0x3052a0a23060307080a02031306091b051c02010806030309090403051b0303150d020d02040c0903380901060b030c0a0809011116080f1809160c0204090203030702 71
    0x120002030960105440301004001c8070007040c0c02c1c4200d910099505000046000c0e00191152619400942e0015400551602c0b10324854484a08840c1d03281d00071101011100170701004940c401900c0d00c0038000403116907202c6401c0708014001c2c00300b035000003818016044000f941d07039a818070030340781144005007004800d45040d103402007060f8032110150512500c5c0050b00003c01c4000800d071b901c180d514404844111492070200260700305030300c000702d034045071084048006807124083c5013241c40803925541c2503181545400f05482c1c802101c816400700f030345070760080d2a508201c817140d41041294000d25080e00c0301d034681b501400c0c0320740100040d00000014082242c0c2980b000b00003103d016901c01d105521102d9040d0300340c0d0524005059840e6041c801041403400320b004601045204503a064a4500a502c01c0c0090340c01c110b03d16107134228021241100380c145000403591050b1801955001d0382c0300d410002e4403000442501901650f40c072410041151810001c8510940d002000d01110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 113610458 1250 113609208 113609219
    0x40c03060f0807080d0203070b06011b051203100b030907090b0a0807030515090f060109020a030e0613020103061505070803042a031704030206040e0705091207031b03052a0a 76
    0xa502113440b480c4658840c0c0080c80c580c0b0352001c0151001194002601481c1303496040044505a124919001c403640b8404124000103074200700840c000c036019820700342c90303140c044a00b45c14080d0b2a0f02c842e0800c3e0040003005004400416003805581c03881d134000500925540c045442d400681d04002900d11400c8404000c0c0040011480c101400e0b04c000041c2682d1805002a26191800d6150b800b0341d00c034400601800100b1f801800722440c00d40740c006034030014420755525004045e9130841d404003400703078100250350f454020b084c09005d5a8407070400005005000404c00e208040000c5c1030040c01201040405c020300c01c03117440300d81c00d07031000717020901100c82c082d1001002c0f032004584e6400c005c031003284440c04085c10b440c00c494005004908151a14500b81501200188420f08203c400c2203150f5159961030500c000c051003d000520f003440c11482c00c84840d0304940c64100010581d13060400000e40300003000368946246440c6448080d441052100d40d55601c45543e580c08580003002040707 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 113611708 1250 113610458 113610463
    0x521090303031306061a0702211509150105010504061d0a06031b1d060d060e01030807060b0108190903021002190305011208160312060f060e01020c010e040c03060f08 73
    0x1004d005650412915988002140d1a107458205132044140144130410141c501a01c513030007a8810100b50005000c150b000309400d00c4124603800d080c0c10209428080502400c00140e07485e4241d12401091a50502d07001030300313500462155008003e1404813001c41c59a0880010136038010240c007501c1c4607078503484040c0290502b070b0b04910074a136103250749481c011300c100c1c081d1400d001502d000802801041052206a902589103c0f1a2710b441d000d0002e000380000d400c840c002d60007121001d4407001c19241c0101079900100d1003504108180007800881d0f2482c100300002c4040403c000180c0c00018030b010390620025a404540c428400b00d9813130f880300625070341d0201603031860b50700b003040307a0300c500c1008100c03041c02d00042d2080409000800700c0c1055140701e900350074000c3c18143c101810910381e560549000d900305000c1c078504440c0400110b2380060030000000d6090004e40551230544000a050807068002d00788202e84407568020700a000c1c2d8011800340c41580441c1c1d0095856080655 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 113612958 1250 113611708 113611741
    0x30708040516140607020303090901030302030705160311010f030f0e1006050603220f050d0c11010206090a0b061311030105100914010807120e060108070f03052109030303 75
    0x84090041e0b011011100c40070503000d200340d40c0741502001100840b01c06101d0300b50040b0750200e80501c010401d1440b590b40d040c921500a5100380d00650341c555282c641380381003494030f00d1a04c6404031004020700000309080d4401c54402002e2900c00000006c0c507008901902078072914501e064a002070350003100c68042250200030900c0381c0180142d036a00c000380702561204035943c1098411801043d41f40f004101940207546000b0100084204040e4960a09240708013b80c0e101150300c888104042000f961400fa54240b800d0024084c0d514211007050348400c4124001419084020b00268065480010700407010306e00841c200000c554005c40620694030a001d0340d4880e0440d8005940b000781318101243c207540d804000d1b28824a0400c1c0152051000034280c00c0600000d503440f26081c00c228801d00107d412001d0003040554503004071a803c001068000099005c032541050020500025840e0069032402e4124028001e8290303140030513000c0c4032850b5506000000c14040c980a0010040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 113614208 1250 113612958 113612963
    0x180105040c020712061a0603010905010906090501080a02121c021f0209030703060f090b13060f02250c0b120106020601080a0201080105190e07050a02060a20030901020408010203070804 81
    0x422401d26108401d0b6526003d0b0b104112900c400c141c4032100103031a80d04000c81075040c0341811044090120300144064200341c0000c07801a50b5a00100100b504078026140100010001003146504040c1c220342c0704c2c41485d40c0a4004c41034040307220f40070740d000c03c20390070b10400a00107040c845180001c02034480c01c03080010b800891049400c054128814401c892a0b054003c6c0146800c0e840e590314030f03003d05003911000a03550b90b1458000082a1200d041500c5070b4508046050080b502e0701c1d0081c106c905284150500340e01c140650b507101c03103c80b1600c0001e0300700c04404080140041ca803584a1a01c03d401c0765041c40c40c00318801420160b421051410380e00346400b903e505a07280c05642d56940d034284000790000e500b0b000100424280840b8240720a4510502c400d05c003911544402d9003943c0503036000c400141c00003202c0c5412035040c4801c3d41c02180380c4805102d0202104481c448104150048610780b20000008c04c4800f1400d5040300c0040c01c3e890000c0d51a841d00da034002d00450781c1100c00307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 113615458 1250 113614208 113614211
    0x1c110606120a020d080c060a02070614040201081302030f010f05090f0c0a0308090f03151b070b010b0f0d0c0e0a08010c1202160501020408030301320118030218010504 73
    0x428014548403203490048406040240980002c6800b08849682d404200741c505020800c42001c14400c2402030611a00e400100983d4401143c50007601b00c46000c036604403051000003d200041c1e034055441a0040316040e04102c02407801c0c00020700304500101c0704541c0d90b2814207404503000707090b0049071260b1104400d4441100466038881c1d19500b6105440c0d40c0b011000100b40001071184c2d0141040c41005030040c4c0381080b801f00864500040c10a54503803003800c46040041c0540100c900c43c0070a08100400c50070900d285d0b80d010301c00c0308107001e02c20f4969804240e418a41d200703002a9401d15174a0001400b2041440d130005d8003c5030000d04490003038000b42c1c404900341e101400740c8001c0301d0040d910408d400c83c5114180c3c00941040190703070001039400300e5003404141d0174005407000c2c003aaa000f55951b545040303110703e21a1412459800d191030941d0400181d078a58038100240c045081c01d04603007011070621401c40300c1600f40c0000790701000e0a5000c407021202900c00d0360598005950 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 113616708 1250 113615458 113615461
    0xf0f130503011409030901080a1e0f0c0c030c120c0f080301030204050a11120606040801020406090503060a1103070804020a180c02010b04270507151805011407141c1106 74
    0x1094800100111900c5031941c5c01000284040e5100301081d40e80300040c07032400905d0340c0d60000c480481449802010420742c1e1600e14880021426100350403140c152030405880f0703240036a4015001008414000e400c12403800e00701c10865000d40ea80840d01070340b00742c100d400303007400d40b0348041960000e003c00e80c0910300d001d00150074004140f2901009944c81c1005600380f80490294034094200145000e0704400c0c18030000a5040003400030301b0203071846031a01d007030300d9080c141498034080005001e8518142443d0881514540340c4040741d40001803131500501c2c0d0781d213500100b1b824000c10750041c81e8500010741240c0b0003642c0c03607102e038031702a9150b40240310140a41041000b80d400f201044103020260105000080310181c2403100350354450001e80301b901e6501c0c068005c0300c04001c9505004140c020410a54110702c4500c600080d00090904c0071290721008004909401403079001003c04d0080d501c06c1c1030102c0100800c0811003105024402941d540350350040c90700c0d19240540a19104240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 113617958 1250 113616708 113616731
    0x80c070b0306060f0c01110d0b04240315061a030109050a06030816020d05060405281203020904020d0e031815070615030525060f08010603020f0f13050301 68
    0x10459001d00c01c01003000d0f08010114801c4c0065902c41c1800304195982c0c2c1341e03804078178580407000d0b01010310f03104000030745d12800e00c01340000e4605006018607690001000802da50009070039800599412800300410542c1040d0040d0007448150020942d100d02191465402580c440007181a80c8000b0020300440c0c49401c1d240054400d180001020208180a003007118105908200c4460303000400c0b408a221442e101e8905101c01070301d0549064010b55807040114507001c1ea400c1100502507400c0e0000e54003600c4525001a0540c0d4030400c2540001c0c0540290380c1e00d4040d031fa0890209801001302028420096540e50700002c480c003441c141c2c4070350404180c545803e050b8690000e41c49007034605121a503840c401400d04084066a102520304080301003002000b02c0d036070b6109015110300d03004021084880300b03c4450b41c888020400d0700f10030f14034159480b51102d41144c0903428090380b184280c01c1000c0700c50069004448060b1008182e9040584900e48090200c88040e4000c001081c040d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 113619208 1250 113617958 113617979
    0x24070c080327010309060204030f030e15040e13140120090102070306020a03020c0303090609060f040f11040e0d050306120102040302010c0f0206040e01030807021003050712050c090607080c07 84
    0x904101c400001004142c1c0b042c0b0460380d00d101d4600b80c0524001901420302d0740c8603001c90300641c00a0b039240700c00200c07503001c16802080d941400341c0d0840703e2000b41c040000e00042c091140e4055442e0102c456004149d00e078946400c200301040d4403100e80b1000f5900006924001e00541c40d407d44041030414141e880c0e14000012181040c0060740034051076030840d100c01c40a540030b0341d0340d0810141e0070017013490355100c14009180a01800d801400711130600c06000d924184014040f009000704400a00000500501c01940400e46c45410304c0e1103401c8041c001401002c1c280840c4000d40510780c2d01181850f40a0002c1d441441c0c11900440c001c4441741c001c6d4202d010320700000340440c01d403100c008041400300303020b410b03000e20080065141070744610105040ca03000f0303402100e800c00081152710446c6407410385200c140001d0701c1e0070032651909110040000314141c000040032a5103602180c0402a0403040719800e841c00b404056490500e407600c40e07181d40c4508815089801400404550324005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 113620458 1250 113619208 113619217
    0x90b0c091005130b04030f170301230111010f060611071a0c01020906070807140d050f0c011506180801110a05090607061401090c0e150924070c0803 65
    0x50108900c50708540380607506039100c2055498410320100001500e1440d401c0108041d610515403c660701c07200345055450440d00f5145a40c071507000740014070a92000116902403110140f00b01c1903040400030060310007080c00e01e0340f40c0c0d40c1c1d407c3c80f190b45507100058018008031051744c0c1c0c40315a060944c4001c02d03121021800781ca10141d001400c40c0d81c680c5140c05c00ba158a400701d500040c1f4200d62203000410643c049c00e01100c0918001c5944402d0121a00340c2c00c40000100c005403078605d80d503400c0100f19105180509040800229820041400940c0414000010181e91a1186494200291480007503c9440617204201d1a001c00c0e5071006004003909503040d04402418080742c01e40503a0f05030041801036030070500a001481c00306800c0c2c024050490a05843c9a800c2d50600c882102922881000c0c00f05005800c403144589440300b80b040061940300c1c901d00c2d619804114000740c2c0c0388004007448101c440b03103c2c4082001020340001049410311500703111504075501c1c640c0756142d028 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 113621708 1250 113620458 113620477
    0xd0201050402030304060c03050f0c060105130b100f030906020706090b090a0308011511010c0c05010e0705060909040c05090c0a020d0305010503030a0c080c0109060603120503060d1401091203090b0c 87
    0x3440100b01080c00b030340244940901ca0304006050ac0e403005031103006a003124840c07070000e9019100400542c02d0820291072104051507090054044900101d080c3d4045800b1800c2008031038140c0b5a00b187c0f013035100c11641d540c4144250350320b10907800c1c941c018050046040d00c0210050010590220000071a0b06505915850742481030b1301c2c080d03803803207400160340c0700d40c0c20f00072a070404c81c401c25020b110f0319564005649802042c030826041c0701c2c2c21600da920303808181d0343c4009414000341c1e80301c005555005004503425041d55482d0320b041c414454281c0c1c40107800a220307006028100f50340401820b80c0c0301441d401c81e41c8581c0b1307006084041e00c03028841d041c1c064204000d85072020b0300c2461041501c5004600d82d500d0f009118072110f00710303200c090007a1803940d0740e1a414020025600202c1c0b000b07141c18500340b411402c080000910010195074024010038040c1d02c440760300b003429001110000e80012403118060303070140018029000013113007107a408601e072001900b204030150940d07000b0751 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 113622958 1250 113621708 113621713
    0x402040806041103010f050403020d020607050f04051203040e07020304031a041a04020406080d170a05090706051b0109150509070303050a050c0a05062d40050d020d020105040203 78
    0x100c4580f40c00c01490811400f554243d52200c110803c444014042c950090307101e5401020340210042009082180151203c0c04101c002c011000c80a4401d5080d2800c0e500110f401c51040c40d800071615107140300355800084075200e5041085565600030020388100c03405444a064801114801c4260052040350300400c90202c00410900349d41d02071200c0b0303600510107040060306980b948000e88ca40a8446103010006003920b41e0600c0400103c00150f0b0000f059805c00d2100b410076002d040c0c1ca6209600422080180c0450046213101c8031181004406c100100200300041c502e041c0400c00c0b42c00142020030140c2040045100c050700060244122038050751800d04001c1c141c1d6080300d86e0b81c40b105202000d84501d600711004200d092010394001c1700c80362104181140a4211a000c1d007001c2442884207180e02410003441d403003490204003403032920602c1c034504c80f4903106400c240d110410310485000b40e14241c01c0d03410004005070702c6c06044000d0b001c849035051040d004a090719004c030390003900354 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 113624208 1250 113622958 113622961
    0x51201030b0a020c0f0c010f0c1110090e01180c08070e0105030c040f080105150109030302070303200f01270309030209130510140c040e150105041503050108010b0402040806 76
    0x426000000342c200d041d498016141074140c2c844030f841d107207040709540855005001034080e15a0803201000440886c0d080c1104180b4603601d40207200200148900e001d0741c0340c0c0920140d2548a01c1c0301070050f0185124019031035031038240c41001c2c501c0680d8030b8030358186480d10030f01030940070740d100303510400041d5034481e50020600011607040d00b026184100e40312051002007021044242143c014107500380000039030789802c10b400d0f00441803200609040c40303004001800483da0100b156011b403500740c1050466500e100d445d03002a01800100502e01e8000e42452070f8103180190480300361401c04002d1a84941e2100d6101c809507107007090700030003050b0382a200304014280052060303409400c560f00b400c13500c9070640f602303824038011540b0701d8101c0ea510711400305052240354100c1e410a6002c40d405041900b010440c10b01c004002c0c000411580c9044100d00d0507030f1003801103038050522148a0117110078007190250142c00300307006201e03c1d54200741a0700c8885c2054425a411281c400004000e00e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 113625458 1250 113624208 113624213
    0x6031116080408030403050a0606050a0513020f07391503090206040e01290304080a180b0a090905060303090612190213050108060306090c1c0b0709060f05120103 71
    0x303940300c00508540d60001030000054850081c00900000c501940c0681b050b94414648501242c81c19040a48120312043c800e10494503101c040040480b0040c0005a0316062078101610a0050a00017803c1d200c1700c41d901c19665022001c90340201401346030360403140c2c071031841c8240d096069000d01c150201901e446000d5041c869000031303800e41d00103400307203241945600701102225002d800500780d40100704090440100d0001c1d107500300d45199a0210b0840c1410343e6400300b544aa03107012001c00845100140c0f80d800010a000d0050600e0300c2460307601e81200c800502605414802c00207828a044000f0340c19050100444e407000d82c00401d1203140800030007805a0050000e40030107801000d4030f9101d80c40103181e01c014100d00742d10712038110340d0b140b034040010070500c00149408e0103600b10700d05004290320002401d802030601210b810260301c980b04070044003003d012074082d040031040001d108086030005210815a103090740c450200070140c502c00d507814841c49880c58007408082d40108013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 113626708 1250 113625458 113625487
    0xc0c2d0109090510080d0f0503151309060e010b030109050c04050c041a070c152c090c030103020a0533091809061b0306060703030905030d0e0601060311 67
    0x444405040c804039807030700d403002c0c2c6084031000c82d0340e52240e240048042c80203090070080303080b0f0402c00b4130f44035038580f044440040041c000030b494481100308007030860995507100c51003503501d401c0d96001002030b08090305105014103d18500c1c02040e5103080001c3c041c0b418103001e14100712750000010f08a094809050200030800144040349420091002113212a040104460004d8655031a035490f06d415050040120704140c0c013540c42a0300462031120f240f5040f070050710348440002400107030f92a510680c0b002c40b00c03940c4803481c2e00501c03881c1007000c031800940c041c40c10789000341c8151401a0301c07401445000c007944110702c411300e0080b1810031300e0b4000d000d11120f950481d140101d4140010500402c451040702e01200c20710500980402c4001c000400c2075a40c010113010340c0144e40b451038040001c01c1c0c88041d05407400f580000401c10103160080e0486241130794084212035451400754400c20041c0500c0b03000d800e26014500c00001c1c1c0620034002c4000030310b031802900385091940e420108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 113627958 1250 113626708 113626789
    0x109110a080a0f0c0e010f030213060608040f020303090d0606080607030902060d0203070c0b13030e01020d1d04021e0c0708150a05040201121e060801021801050a0c170c0c 75
    0x11104513001d4400310fa0703001c401e9001070003805020702c90700c031407800c1d441004008240950841d060505d04002040900e501c2040150480d411a14402d004081400800d0a501ca111483c40e0001e40d03040000042100c15030010b0103d070b01c01410b4034120340301c0010440079180e042c20042d41c042c005204000ca1050103078011038200c0b04a04143c0b405000c0c994914151441c201ca01c041c413282e0b0325440c502415008501700880d10002d00c041c0820700202c2c000a40303a245080e080b860105003a841003040c640300da5049800d4078034184452030064035031181030b042c0c0768410103941e0214040c2d00c0d0001016080012100d02d10442030007882103554074820824000c190040007641080204580c180c1150124414510f00744e5207a01c000a511102002410035160f01e680080340d6a841007209188070240042441c000c48802d20b0540e643d04aa52001c80e04022140b90190030070281002e84150000100010181c0741011001d031885401090f082140d404501161401d02d010b02071505032180848000c0d40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 113629208 1250 113627958 113627963
    0x13090c090e1e010909020316051507240603050708060c0906030a0f110406030605010507050d03240905070306090506030a0303020a03140a0e070509010308160f0803090109110a080a0f 80
    0x2c02080744905031049102c042a0310040c80e0650302da070b188056017420b10124114408000801703181e640740c9000300721811a5402c502a051070082071580c00c10405140031550340b9445c080c3c0c0b02210110886e09002819540300c05c80d04c0303104400e00012611300214660b440b80c0c0c801300340b0600380b90785603051004a0380020170017450184e0782c003200004225a481819140102d07030302c5483e10345080120260454000743c008506000c000d20651000400001c0c280410100c20714006c2110843c0c81c0b2502109211500c48086088685070040b821908551000d841690582d40520105555411810031500291581038054021301c4101000c28020b400501c031016140ca80092045150b07507842d0f400401c00d40341460352948654400b06507400400801001e00030171100b05200c3c0d45590307540101442202c0c0014103001200d12810240003180300c2824040b0341140800359a4509840c00c18003e1000c00c00848a01130a2201c7d0003680c10032010704020303601440024400060182c5440300d03441d0200340304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 113630458 1250 113629208 113629231
    0xe04060f1803030b090a061202040b030a021f1d061605190602030108010f020a020304090e120c0d08161403040623160804020a05270c13090c090e 64
    0x1101c00c099158a52400c48501980d4001220a2107204100c80f040d0084d012858190400d4414056039500304080c44620768100e81c0000c6018a10f00800d0505108401c065444902c88441d00d0110f01d0041e010b102443d05982c0e01048044074014a0810308c00100b0016004035083c08503c040d1507066510000290080c0e0032155850882a01c8844031100704008aa0305600800100310701a801d00401c100c4c45295207041d400d010007010000e607070f409903119501da00ca88802217602104001c2c401100e444012043e522754602d4848030381c1d90342e0000208042c2c0014000710000340d54481003054400340f09256625404400d20190550304d03640c01c0903200b07030ba00613625000c81c88501080c039081829540c0001081c005840c003a0014508618605003410502009504001c01a9a51070745030095800440341c6104000c0841104250204c0c440749521a4100c00d0b400e03c41d0105840d0050000c6028a00b4003000d643c1d2500300800a44aa28410101103096940c052207410070301e03220385900c2040c0381030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 113631708 1250 113630458 113630471
    0xe091b0307020304030215090d1506090203040c060806010801050901150908160f0b07050c011d0307060305090d031109040e0f0a0b040201090b03060906061c0e1e070e04060f 76
    0x100844254400e68010000d07902c0000c080007141040d00e020300c44a0070180d003080c144240c800100783c0015442c20000d002d47e04c08100004503003c41e07072015002e400c0c4200215240c3c5482d05d40300a4030030090040740040b90a0300001400ea42c401c1203507605131140949607404591a0030510000c0f5189200c901052080303008011844001c02c000308211400300011440e00b4502e03103030034110a02c00c243c0002c0103c40003080f041d4041503001582410540c3c2c2071802d4403c1c404d03200141e1400403002174200703925001e10600040d090354141c1109015070030800039181405c3d080d82d0281d0403191010213515503000d0a01c0103580c0c500e0700b03134080100807100005a410781c1400303499980c20714002c07400032501004004140300541d6805200c10005e84400c0410f00e00c4d5046c02d4001464800009280520514001070085500d9607403052003010b510700782401b808913408004c030082d124200154145c01e0105400c4110b10322001c00a080000c03250b10741403580703050b2a241c071040060041031114442240d20f950 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 113632958 1250 113631708 113631751
    0x201030e0a0b0a020301060810060203042c1e0702030a0c0b06060c0d0801090f0b010e100504081207110405061f020a080d02190f050d09050a0b091e06070e09 69
    0x400c035a202d42443d41c00166030f9030420102403c0318001910007071803162400c0302840041c4e0000100e5082ea0a1003c1c00d81514814502c4900328002c2c58000b5480c20002c4414401125804003100242c015911500201c0c0e50b210300080b42d5034050030100000240310701031101c02081c0c01850880e04400c3c0641034500e0040042002445c1031150701e854000511403400402c5440c0c0103102d2001e400412100c24054a001d00000070618a40403581502c550305c0e2402032001c15018030101d80c000e08010054036008003610310825495040000151100650040c0005607032405200300762140c01e004001e461124004903207060308080110205003544038030304504003c9000d110107844050052080581e450000d0305d809030066030b20407082818040c1404074040d8a64009041d00e40c4624280c00c000341c0301ca00760505501d42962031002900d0700010209101d030708000821004100401d801c00450500e010300d0080ba610b070400c0701d403c0006940044501c0c00b920b8800301558124074440ea841469101a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 113634208 1250 113632958 113632973
    0x909050a0210050a09080624010e04150303020c0a030b04081c090b01031202060910090c0f060305060a0b0708070201110a061d0d031a060702010c051f0b040203130201030e0a 76
    0xc0c0c6502c00811000f05403103d407558890603050140119402520b40c90401d41485d5801254620104941ca40f4a100d601c2e0b8503403107018a200344080092050241c01091034400185500c03901040d00140140c0d100000c01341031030116501140d038001e04001890b40e031919414a140c100c14048200d081051402d0520b40c061401134124a5002ea60311030001e500d503281103540c4050b001050401c0d500700c641040040640402c40d403405031945e160108211b019031600344511303041038004a018606108000c1105603250f80810310400087e2007000e141501d07204420104c1c0184500140301034801c000e01d0300107510a0301d400c982096807000300c81031140c1a0356a213040e60303480040c40317140c02c09210071306029400c10850801201d605090400240d080345880b51200c0c0924540980030f868000b03948070459110700c040e5441c082d00541a1080711000904030035038900035106001c0d4580c20300501140300c5c0303010301c05c4a000e6a0b61401e031b413a01810076070040d00903010805055030b240c06083c00d00c50206161 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 113635458 1250 113634208 113634229
    0x21f020a0c080105010e070206040506040b09120310090e0f03040311040207150f11040509040f02031c1d04020a0c0201080604020f161b05030a0f06060504020d020a030e060601090909050a02 83
    0x8400400e0035030500704a10907002d001822901150311490032b020110301c000c0341a94019400800480380c43e078625841c00e182100803002041103030800020030900c0c0546550039800d5502006040c005803400c4006076540301c544004611035900b0800080000403001a480c8022880c0a0005811302c5044e07180c00390405884d0017440401600c9036005040c0c549540320b16a0070411400505082908000100f03001e2440100001c1400041d81408c00070f44d03408000ba09001425016049061520548000d150b003006559401040d803003c40402d545140600903030313401070381c50303600c140c1124000d4004407008031018041c25000f0741c2c208400c070403220020300188010400650001d00c0b00c002d078681044000304410081d6800006000244480d0743e0128040100d2604802c500341c044900b03080500081a0b2503002036070103440040e2010021007250050103039036002d41c90802440e071102c80820b0b00c034641180c1b6140004c264240620118401d680804c045601440885002c10116070104400c000c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 113636708 1250 113635458 113635469
    0xf0703021303020a1403060a050c09010806060f0406020d0f05040605090118030503030114011421040303020c16080d03050603060c0703050706020406050301051002150601051602030601031518021f020a0c 89
    0x4400c0c40c81d501401e04002141e04180708c0d074030401c49440c0070f0078054140d0094050742410850740c900428825034814081c5c840c034032942c440081c0e41da0340e168070195450b1203007020003000c0b500701524072144038000c0017998204c8000d81c40f094a04008080111840d400803401c00003081558280400402d40800180d4060001d00408814000c001800504510601982541d429100704490000800b120320500e0046180440d10101034481d0314050740a800303101c02c9220140b0a14102041510345001d942e400c483c181000d44400301d001c90703400c07401c3d10421a0701940640c05540400d45410b4028001d050b110f001e46005270400c0360a41d00c6005aa0107507100d1070005002100504c8981b81c205401100c0410600080820911610b41180e00d0721008103540c4c144800480c504007a04140c000d90f26240c1d50007010740d23940d503071203181ca0100da00301c00e1169041c461604003020045842e0206102c50180c00071304440d20702d03960403160b41e050440805d401c1d045001c1d42a0140c0090841c0d07000102401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 113637958 1250 113636708 113636729
    0xb0414010c08100f21080c0f030304020f030c0f13020d0213030501060605070b0604150e250903170c01060e040f1e030518060f0a02060103050f060f0703021303020a 72
    0x1041c94075868009044d8000d900700388044a03040082201c003a1051601084404001020b0401801d0020305030003200c141c82c115000724280820f0403c00030008502c154421640d22601c42c10150506070360301c10104030150010300d003e451404c24980400b802d05850100d01d009031411241207801020782c0c00c030944d42103c00e1100c000c1403003000403e01610000e09018944182403d803191107543c4e14103005418140200c0c1d0311482160204031112004c8003401d00d00c0900d00e480c1c1488807840c110a401505c82c014801ca49140303070120103120394811021207400c43c46021550840310344001e640c0d4450301e1111881e65950200103595640003020070b110318081c4122010802c45400c0c8068003480e241c50b0081d13280c000b040c01c00d00003604201a1502441208802c19880d03a950700810b5152040040e2030a0f00301021407546045940069641d060b603110340181c1d0000724410743e8040e81c0d49400d441c030050710111240050350181c031a6011388038003001c40703205a01c1c043d80e980100740300541a406c10350110303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 113639208 1250 113637958 113637961
    0x6030415110c012307080c07050307020612150a1d060d06090803010815010f090c020709020f0c010b09220501110a0305090105240402070206041d010f080c0a030b0414010c08 76
    0x125251007404440c00500c1307042e60402d242501c4c0041500c100145622503442c070108a51040c442c04000b691f07122a40078000a0755104803d10898504000726100c40f400380d40803800c68002c2c2800c642010440d000300c2c84a421040c070508054010303c4004110680080d8038002e0100440c1e070f240118104503000301c6005a4a504013003400b070400c2a10764521204d025048010003461506403800c1c0c045540051380041da210100d1012401c0902c1030b40840d01a9001080c030340b50b031881f41c0000303005a614010003046824950801d0002c20032044079103100010b0388020355000c0c3c0b2554155141031318803c80000507408107004140c40c039504a40c4400300025610f6040027000300d002d01c9040c0c0c000c81207121010076443c2401506078403081241e241800341c4e8007c1b5102d01191200320aa07409031500301c61802d01a142d0001e00c08480d442407050f4001e15500e128001400100404c900c01c80041c00303001c400714241592989640044041d10454250f00c03c8941e0107034226081c400da2081801c9543c074150035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 113640458 1250 113639208 113639231
    0xe01050d050f1e01050d080a05070b0a1b11060103030c08070b090d09170a080d0f020304140d09030c151209030207050a06020c0307090c0c120e100e06030415110c01 72
    0x194840e640e1a40e0380c203c0341005002640d41c1c024480019136024100543e580b280705000c0b9107034041c6200c024481c16808083c000e041031030307420011010394114034911080a503054220f41011030718507012002c2c1c1101c030060000ca4451142c040659000d404402c2c81d02c0711503038a28002150803900c1c2802e580010b407440d000c19502540b01c000406001070707812100d41803006219210482c1c0076004025507000100d1200d24207070345c1c0010102d01c3c03500030b0840d00e07840c16050007030340d40244006004480c0982c0c00c0e507040c440d004602c420f046d80c1d0040300840000303091884210402c0070004074181071100200c00e811100c4c3c51406400d6001d4130039030103071200c1d52078401031191030744554004009542103240990f003a92800030b2900100c0700c0324000032610b40c682c41c0e07003900c2414010101030a40040c00340c2a07418241c10a020301da141c0c4007609c030f80051012420044900b020150501d981c410070800c0443c010030024241c10204a0540100090840750030000c618244d010120294407a511080710290 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 113641708 1250 113640458 113640481
    0x170114011217030a0f11070206090405040201090f0e0103050715020a0f0201030906020301090b0406080304060e04053606070c0309060c1505090d020c06030c04031709040504030509030118030801060e01050d050f 92
    0x1403641080c400311f0704084a40d40040e0040c0140c01e07903240500c0c0e0341e01c0020700b0b6a01c0b8800a400800300809202112901c0758105540e401c400d000a682031300c40c1c1000000c030f0042503170316507060301e1441e4040c140c14100c0b82c2d51002445505201a030403d81c803072510001080003807000710300030248810009006500344041c001604c54940c00082c1c5500248420000c00e0340184502082c960103c0d40080c0b0380c1e640860054000e8003003103180202032075050813002c2074161484010520500740f821900c25a48040089070001201c060003030004161090401c01c0c80d010780d0b001d25400d0b1041c404800804e02e11075600044500c00c490760111a40410044044150113001e80500d03503000f0b039000b516500c0c2c0220084200d12035444018450002c0d07a40e034800080601d0240c03486e014001b0710602043c00c0505005103140c000c164100d103c0e5192400c5e503a00ca00c4514889600103605440d400e100c1d07841e00d441079885050b0183c001d0305000c4c08001c103100090051041c580719007401e04042c2440c4c1032a240120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 113642958 1250 113641708 113641721
    0x105070e040b010806060d1e0f140a06050102030405210d090f05030a0f0b1b0708030703060602030702031c0221122a07030c120801170114011217030a0f 67
    0x9061004c0d07401400305c2602c840d002c40383e041d072200c0004202c00c110100c1c4404405003200c5080310a41c0b0b00012070036240a0b81d00420003c00307002c1c450040c251240007454003220040c0c840c03940541d204100401841c10251443c2010600030f03108e0743c00007810b060040b806c1035082a0b100c4001045181d003800511954511b90307000d01030590052108405035070314000113001c84034018041d044008001442d0b0541005900b0f0084030100c05592181224580080e0980040d14500c01003030410f580070034228400400d544880f0f40040080100583d1070b1a0040c2070701d07040d010030003107000d507615103100000030b5030024808114200d480b035a40c80d40e59000b46000707030024204001c06c0040046011004848607900e444100300003030340c15900d031100d24003030350161600d5000400c006460550400c019401c05910343c101c6041080e5070f0f01c18482d0001030340c00c03100c42c0150141c13144041c100500c2145842544451100d10030100d415411540250003090f68000b00c0b040071000b902c03818010b840019500441 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 113644208 1250 113642958 113642981
    0x21090501091a3f04050d0f080708060a0b04030305040e010e10150201140c090a0801020306010c0b150306010e0a15030308010506030709051504091103040c060810080105070e04 77
    0x58039502d4003580d80c0400c62189600000188110450681c04a1208400e00081203500e0b02410f00d000751030064408039200403501514180201c02140c40c58a01500c44107684a20300c2c0d40d01b030742d50345c1d9624090340e400001901c095000f00c91f2200201e0804c0ea050700030006903000303407259901e85d0710f0940303411854003050304803000a42e071120500400b808c1241004064502044448100820f952412801002060500c103100700c1040f05120022501c3c0c0d000349400c00c07041da903004005d07454039013490a0f40710644003640042d40d4115240c0100c0c4400c20a1908140b4006808400924941c0082e160180a800605507192844e080c0403081c05244609808807280c400940070003490341e10007904600e014400c580c000c0000200086050344205841400782400074181c221900e07035041e800c603480d001070140c000c40c6490070031032031211000d0800392031060398490390034040c0c14180a800c80e89020040c0042248400c40c00011603846000c0c09072034420301c8550b40d004a901d0b0004104000d44400c690329 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 113645458 1250 113644208 113644229
    0x6181701270302030f0309010e03030a0b030105100302311a030d08060a090209030f0a0c06020c0603060f06090d08040306091104022d09040e030d0510080a0b042109050109 75
    0x440c000a034004c015690740518611205031260756070401d85000d45110603604065010000800900c295240c0c400a8590019070007000310703680760300306190320000e140000382d407103140003a03110341589980c01030a400c00040803140440308000398440d01641c4018010250740080790310131401509041298851291151504040e607040c0f860108040e044280075066807507400140700c451a071820001d101c006800310040b101502da01d030909442d690418040c0d5001130003202900e02c81d91600c503094a0140000074103000d2510302c14410001070b80d20410190b9000400c01a01c100410b510344050002940182c0f0003092641e00c61420803e0b6000d0340001324480c44c4148000e408002810104071402030b9008404411200200340b1182140240c404803503016003040d92880030220040b010300314104506006000c8d5894100b02d03848034145900499101c4e0b8400001030011406948850303410500800341d0a80c54007119002a8548001c05041804560340e028104000e581c042c04800c000c1500052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 113646708 1250 113645458 113645531
    0x16021e03011b080c03041406070807030506040608030f0306042a200c0f010207090213080105070302040308030411010c2306061903030507080c030310030303060b0f030106181701 78
    0x3800f41100101800c42c3e50340907004000541005603080506d43c410f03420000321030003842c18103001881200115100070000c0d0074603010400a04240c042d441c140e0701000d01440c200090745a1000b0749401c02010b050b03000c4d8540300c071800320702d4501d9220030130138450040014661810300009419081c40700c200007403109410b121040c0c00c03003010551844a0100b1100035040c0007000b40100d00c0d21020b5041040400d1000505a00502c4031200300411507800c0402440543e071020426070480c041c40c40003034200300e402c200040029000e810f40280a0605041c229610125a1602442c070040d498a401c0280c40311504810701600c01c01c40c180c1c3c003d80c101c803010384000c5000d1840100c403000e80b000801b030100c0810404c040003218820781c0e2101990004880c1c591412085048038824a07100a0340420310388040031130018001e0741194043c08254021900d56407824004448074541e402c0141351042008070003254503040002c0c044400500351002003036600240c9a0f0103101c01c01a6491082c0056800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 113647958 1250 113646708 113646761
    0xf061e0503040609060603150c0810030f080c010908040905270318010c020402030a2a05190c020301060312030e07080c010e0102070e01030b04061d100216021e0301 72
    0x10304680e44940c1c800d0001c10004160b1a02401a00302604000e00c807095a0480ba070901d031041d40074000d4140f40d40e44800b01c90300c0d501c42e1b40780000283d000c060030130350f61580044080f5030030000820f1500c03c1c4c5000003900c42c0054036000c0301500241c011904a94859041c400d080000c4003540d054210b40c00791500d00a80015115a604d2044000340b441084883c803020250780e000303100c1d4030b09681d006042596646820308401006000c0e21141010f18030341c40070000a1043c20b504242e8080c074041d2111464148a01300000d07561080810510800c0714090744240141c40a000300c01c001e52003040c008060048080e80a420f841880c0303091145588407803004c0240843c0010500c00000080c00d043c1c043c40741d08070040782002c6054002d407003400d108a000004003c861882107100b10302910b410482444072040d480c80c0c10441170380882580e8071032104150004810313401411405032102070700321003c1c0c1340e80c00b0654880141d010b1780144101100406050b003070a014250344c14900c140396540360103010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 113649208 1250 113647958 113647967
    0x3070308011403070911161104060b07030804030813050a0308010f050301090f060b0604080a031e0e0f0f220207140a020a0605030c0906071101200a0609050304050a0f061e 75
    0x40c030174004070380d03258076404003407907800401c80b03015000500c0101a1211141000f0300402c0092911601444c90288001072003400c003010749410325072559843d51252181d450854141101400c119812640040c1820010300200076441c2c01c1d91103511001d031198501040c00303d00d280320786d02003402a4105108800000e0488078802100d940c88600016054000804503005000700d4014095500c00c0065000c01e243d00291403405071040c0c001448000402858106c460200c1c40ca03440381c002074103030314400180c500441d00c0c1c80c0456010746510489242c0c50081d144641450f9895064680e00140711020300044081052181d107425004040008241c0d000c40c002d107404d0301c2020100b00021000c610540894402c0f80c0021900412443c0c40b8501030426880c0414100407003808a42a14a1442082251003c20b20f60100700000f61500700c84a440b0701c0b000d84070481003150180070401c00805d080d83c54400200c0030b000c4008511802a040c0b00000d014990003041d040b10351540c00c0c88041c07016901 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 113650458 1250 113649208 113649223
    0x70605040306051003020303040807150e090f0a090b10030c090219050a0210150501031a0a1e090c050c0f0613030e060706140a0c0504050319140a0503070308011403 72
    0x41400083c3c199221500070200c20780c15040254140400a0b0000340d018000441e0f40a0300c0490a2800701c0148643c0291009104050350f150400d155000054102c490a00e0080e0300028030140850a0f807007917610090700300d5080346c0b82c40c0d2200da480000c1c0244620809110050003440c0d40451a000b4040c08620b4151130036036840c02001000a801080e5500c02d115000842400802c28080c0300304a255000050350503004590000c0c1c5005080f00440742e820a40d45506140038003164003240c00c1c81485100c90414041070102d000480400044506036403060400070841c50b0f0700c3c56240e0020a02030f0341440c01d883e551101551044060019500b240c94a03602f01c15490300700b40d4080710708940498401d02a00d60041c00d424603042000c0900d044040b2598841c40c101c12040243c110000c43c155018010742c021544c15034411501c002c0e002e00b182d001c64800602525070300300800b01c42d80303441d0721b0130100ba5130847c2e064001041000c01c0540140c203241c0034003130f9000c82800b411101c0010070fa59070030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 113651708 1250 113650458 113650463
    0x20105090606210a030314071b031b0f0b0f06060406020d1803062901090e01090203040c030503030103030c0507060e0d03230a0504180b0607080a02010f0c0e010801080706050403 78
    0xc00c0f5034601004104044100d5801030300c00d00741c41c07100201d428041c0c001d01c44404c10110f46c8150000054015100e2000b017a8201080c0344050050304503134a003101e07003c4901c0e00c2090541a001700c4080400c04602c0c2030080b1a1140e940c00740c86140200c5c3c4000710f2880944810301610b030511040c0034050300801c03d848a10103618050701c1c20580140d5420380d19030b407640094141890400c90202080c0c4442040c240b09540170040c9074036001038001112125654070800c0c82e006440d078018444915550000c5812900900812440540301e4660b02c4c2198001c0c3e204501090035040f41c00d01f00181070106000400d6241001070360010070700c000c2a4800300c142c0d002010031807800300000e20105003107038400e91226940061503d4646014000c1c00c2035010340a0b02080c0b001c41e18103030001401c9805403101440001e0245800d0400305d07510350420750050f80c0b0780710039552603209004040e14144510181540d07107981d0002e01403000380015081c080c3c10f80004a032900b12110074001c841e000b03012074003140e6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 113652958 1250 113651708 113651719
    0x10b0304030309080301031a010e0c0d020d0603020a0617134b03030e0606030703080f09060a121d1b0f09010f031e1101050304081b070f06020105090606 67
    0x80d6140303422070040403490401019208044004030601c41d440300315a1004282000351000b590b02e854041e13001100844503c80145802c1120407100c4459401030030440702c40030030100b1001c0d100e50028000d40003640241002569429035181990050050f0030b810456903d5981e0003c44141c40b2080c060030740850084000d6209034102ea406079403101c2c4141000104880074030707212810514260b4412002d1016400282441003443c04181c5c04160b2034010f074802002405110310319a0b41c44415008045c4024113480240f207060700310b0302d0307600c01001119626521042001c1c04030300841c0854841d903420682441c166a004418103000007046541c1c1a403141c80e504103e00001c1c0040c6403e07032444503040d000b00d0a00300005002c010329070804203903807103150156511898400c18050845500201410100c014900c80e50039500480083d0b8009004507035607803404020301c44c141140078410341d10341159804060200800c2505040039400b41240344024005414820041aa00d1001030616071050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 113654208 1250 113652958 113652961
    0x3020c06130213110d1d0712140f1011070c0b0f0c0703080304060b010215040803101707060909020a0c060b03030c0f0a03020d05040b0316090503010f02090315040209010b03 76
    0x190b640000c50202144140401e000481c45103848181d00d81010010f1003901b801c05d40c81803480e00d1081e0b010701d00c4080b80340041c40402d25100718142ca00d80741d4039083d00e061101e0f107030740d010315a4148088020042e546000340140c080d488032080031145800030a2000e04c100703000050020760329030b464108036648150030702e4607600d406081440e240701b81d221103181446070350400401c02c07504070f02071813059008810400030301c2140d80044e030303c800010810f14040c01e502c40006002440d190091904090000d08400c1010780350203203450046401c041d0741c900c3e5800b6080801425501121000250804600540c100600c0380b0002e449941039540040c802500e544914807151400c000369880c0a0449041750741d81400155095102c070fa40c0c100c164018003c0404c0c580c0014011022a400c6401c0c40c0c1da01d624558030003d10700c3d090351544043ca0100440d1102c0011143c0c0d090240d21110300800301c005a2f24903a20041525005080c275914035100001c808000c05a510026814111500010b0311540e9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 113655458 1250 113654208 113654213
    0x41503050c0903031c0b030106030302030f03070e090403020f1b01050a050906090918010b01020312041103070e0a02040806160e060c01091a0405012009041a0409110a0603020c0613 79
    0x82c0034a8907040c0e05840041080b10080c5003030b044090100079595806c1120014031002d046c00c0c0e603d180000740c0564001c011214070041c2d140700940c0d0142035454503c5076411407400058071071030180c0f010b40041c3d00c8080300d0400060706100100c103a100d400740041420302d020340080e006000360500e01c020700001180c2ca400b552950740440e204840014450384062610507940c02d0111100c0616808562070401c0c61a0035500000071986440354041078118595120383d82c000b4500080e00280341c146c0605c15000520410a66903d030148014a20140e140c50610540c40c0c50300b0780040230740004102469645d40c5854100310024508a826508550741e0043c4506d4240500104030000b483c06007501d6100e0300840a54583d140142d1140c0000c1c401088840c1c810141103499101d040f002c2902002400c3e00d9142c1548031400c00c3c10a00301841001d0031503000203003184c0394014280c50840c44000c0c000d00340d00d8000d03442e41c05800306040860810159854507562114002e004848460417007092406 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 113656708 1250 113655458 113655481
    0x4020a051306030803070203250203070306050901020721030c020105010510141303060b090906040c0504020a0c0204050a0f0605090403021f060b07060906052a0f0c06040302070807090204150305 85
    0x1d51303040243d141d52030a201d24002d41d207a0000c081c2803c070200c40503500070660150580c050159070004c0c000c0800a00316180c050041501900480312907508000900015014400440c0800a1304200d40c205101c0b0000140959111584110071645800d00501565945480c0c0800c01112440c000511000040200c0468400ca61612440c406a41400000c1001c10b4000358085082910025800e846031012155219000d42d070042884c403040340180214200313039000c4c180c03001003450b14025149a54001c40c00700c42c401e441d851a5181c5540925906200758000c1e41700520042d15002030516040d10001d441d038078202c501902c201e4501c054000c42c140140c00c82e001800d0a456150b9450f00c09207018030040400030303002c0f01c210341003030002542c9212131420040507800c0243c41030304c001072101210341030364025204410044018031403c8007000c02085a01e11036442a001860428240150350b89401d07440c3e0f00c01101c05004000c00d0000c1c40d5417401c1031004c80e81c0d030b050100d03180e21201003980 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 113657958 1250 113656708 113656721
    0x1509181501030c050a0f05030a1b1809020a060e0d060c03091a04030207060201060609211b06030506060906120403110f0d0e1005071502090301050f09100504020a0513 73
    0x52118103a0001c018442000b10072011030380101c0c0c83e41c2c032040c0d0f601c07000c8680c41104e1158a03456041a031074100816101c2e60402c0507010280d125001340c81d103070350354004c1d0034480300c40b084019030341c0711202000c600b41043c0110281145040000003c58000001120a072041100901143c2c40c1c80510314024002c1c6c0010501ca903108070a038006003503086415008040c200c50550042c45070010004502c0d00603c55141524201d80d10481d01d68109100a41d001c0c10105925803d911f204c40404080341c80d880103110440c0d207100c04014801d00e44a8010141c0e84083d00c06440b0740c030304202e0300500d640e556045a5510b989103055030455076031418151038003500e1000180e041d01414061205005002c2200341030f103045a02ca0402c1d800a034000e01442c00320701030b80800450300411510000c61302135071510840c03058402001d884c1c1110a00400c1c203644056031401c0e00403181d40d05101041c03805021b07042c21300d60344e880d040202d440c10b900052500308241c850103004e00046210b0300c03241f0a81e0340084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 113659208 1250 113657958 113657983
    0xc2106040f140616031808090103022b0209130507120b030f010903020c2b030503062b0201030c0c020d020603090102160c0608070804030f0e130c09030b150918 70
    0x203d106240c400c01d00002208506011800640703042c1c2031503110201d00402c0c00c40207410003045801c01602e9001500203500402d081203407414021460402903201030b00400502c1e40a010240c0c076960194181f01d0340607500a0351001c418140020070501d81d074000d4034903c0a006280c0c010800d00d01081c04607013001c80d540203045042d400c4c010044145074001643c1c86040506a481898100316498101c280e02d2041d00e201c134102074100d40d04000719224002071900100c00a00302141c01d41c00075010000d4401c01190f0b8038840c1029403e0005540c3c051044884403207070790405404510352640001c030f50044044000303100d08808004550004d4096042e00c0d07800c1d18991418040301d005040c0342c22420b4a1340305440c0046c03840700009001c4c510a450050040343d15171214644840d6442d0180d03440440c003200c5540150700d0b90104001c551080c001e10440e6020b949840c909141141040140840c00401707036461440b03804a4401e55407608600307158014581c150200c00e1071040342a40b400e000100c0c1c541e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 113660458 1250 113659208 113659213
    0xe0c0f1c0b06161b0501201e010608280204050901060f090609061517150a09050a0608010c0c0f020a0504020a1709010b10051e0c0c2106040f14 63
    0x10900303140c1103444015079880c01990309580700d000d40e52070315440300308a0198500080d91103d604001c204140f103401e110700201c0d0186c440e02c1d180000c8c1400c0d081c02552007404249c0d15200100702a00b02400012101010500740c4800d0701e6001c105019807241e8410024062a039900014115100c203520400141c0741000154214943c4d403440c1c40d02a02844c056070341818544a00050011403010380301160300800e481c0e14903044a040246c03a5032480003420050488120300708068969150102c0300050703c1218000503d50500f40500c00490365650440d07501070f172500c1184025681c002246500841d41328840354842d2400344085501002c05500003a0454008031301d40c40b6182d040303141d44010750380b40441511159180c00f101800d0740c0700018815084030101c8042512a4450401003440050b40c0e410321400c50025071032110703550312040c02000b050300a034605c07615514046801d16042002c10f40c0241c10441c01005242d101c8070701800043c5000d85840440040001800d10b488030310544005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 113661708 1250 113660458 113660467
    0x2b0909060b070506060402070b0c18060d2301081b0d050a060903140f0d0b0105090a1707050a0b040501180b03010608040b010b03070804020402090307030506010f0e0c0f1c0b06 77
    0x91007082a0000c1d68100c2e9580070386000103c160816109a58a80ba000510591075840d00d810311a4150300c02d07008809141c16035035012030652107007402840342d046004400601409010705a84010000c107800000700058400100100c2400048040100040c0b4046002c0061140300285408402240041807809240c0d404010300c100d03a80f040749203038080d4039507014000300c031080c2c00300a10800710318070407030601801b401409501035440306c2d01d10310301814001d107404411800135403000840c0d800b421050040c03040c4071049440501180008100c1900d0041c0050f003410b461109601590080f5030410421000c80008210904a5240101040b41303585550303503100e0350000c1210f48101d8003036924403061000002c0003a113800449219190641c0c0c1e01000d07842c0d40d42000003944c001e5124642c184030b40a004804101c0c107101a5000300940c0b05141041e40c5041c1d00d01040b0301c0e00800000c0721010070710a29447c42002000c03515051117106c1008031407200e84494070003c00351203031000d0b0042d1010a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 113662958 1250 113661708 113661719
    0x601090c030c0503100b030712140105041b050301050d05030f070b0114010c080702092d09010e151302030102041d070e061e0903030d021207080105032b090906 70
    0x1803005031020960707501030003526039101e019140780c4010390780700c00604482a410428402200042c5800000303601d480d600090074200c15000b030b00ea144011111030100540100005e160034490701810841140511118000d065400b1300103000521a1038028580c10300034a0401105004940c044108200c40c00e48615003030a060010b00001d008001d42e800f0a51070440075507000d10382500046d0340c02080d00386008800e500b80000440083c042c420319201c2e01e0201c003801181000840c00c401c030702d804040390600d0850001400d660310b400c0119220380020b8801c16000140400465000101d40d0f06034910980520101e030080c070507980941480440022100d8090024040413402074610b40d071003451010081d81003001622801d44101102520b00741c04e000c6140f5004080c04413641e004094074140007107103107050140d90188910070b80c0a044a000c1080c8a504000c025000d030100740c005100c64000c8808e49043c400c44c031016454241a0380b80041361080c850400c44015090460041c005580d880 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 113664208 1250 113662958 113662961
    0xd0f08070803150316062d11010f06030b070c03020c06030f07020f07140f040b0301060f0302091807060302180d1103010c0503060f0607080d0603080301030b0c03060f040c0e03060109 80
    0xd807002c90682030000c54030810f92030001050712881d070b100045051498070340142696904580031101c50400c20300f60120380310148850f80521407008a403240301c606120710345024215401c00fa1054182071401c1424004074120300c900d95442100c504041c419540681000e0740b6150351201429030018000080004450700c844846006080d035800720380403041c010031015210700850050800750755203203504001c0c514000244440b0300c00060300000c0d8134100c200c0440c1c05d503801c0750080308441c850004100118180b118500d5440711a44c2d00c1107128030400001c0f00c4c0c0f11001340c4a04030406801040d14681003c4043d01c0c15007100e0024420b070103058692034110789040ca8080c203144294038000d04c01d021680200308076403081100520070480504030004000301c54104580a42e140b14080c4540a05042a0310401e00950300980d40c158503903140d45444500150300401542c0400010b0040c082d090b202c031741000c4d03045801158007242c0c800d054001183c0040105008951600c0b48000001325611039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 113665458 1250 113664208 113664211
    0xc28080f0712020109030c2301050a020315060408030409050c040e0f070219170a201f02090607062f0d0b0411031b120118050907060c020d0f08070803 66
    0x14110100c04034407403001c144c0c02c80d44042070103008100d4449811001609005030004910b1024030006c20429824511500310383c0201ea000341403541c000244071a40301b50080c03d4480300700480300d0a18041c00c10380701a4507402248242c0448545441c04601200c0400303050f80c1c0238004207078001403645000c012010700a0b0042d29404094000c1890765101240124151800c0130740100d01412800300c10541d26085602107411001004462143d030b80e40d42954900c4c0c00b5001d90040010022107030707110380c040c0c615840b414080c450302d4030421000ba06a1a00340640d02c500c1d400480c005056200300d420256000b07000c1b0020b401a051007201030581409401c0a0403d1113540c140c10040812940c05100c00c950356009598030025090000130b200030040d405040f0385060b0441c48a0134140000d240c0d118812003a0021000410b41008403c2281b030a4881d8582c4296440b00a1500514010018010743c0e030200d0007078040c001d0309400c94148280d036021200000d600a9031166610f03014188013146420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 113666708 1250 113665458 113665463
    0x7050d060915050903160215041e060801031110020c0a0815010e15120a020a030c05180106080c1602090403050702120303040827190801060503030c28080f07 69
    0x180442840440030552007014850201e28008510308644210f10000c0c031b402856089a100b0b80b10341b03000f00050343c0724010300000d2480c200c8040030718404040715446c00585d504010100102e4800400200e888a80808103041041d04c81c201c20054070082241031640154009800c82594900000c0900e400551700c2501049102006003d17600c0720010051504180c0b112030701780e60801c004201e680b0701a15101546042e0000b110a0030703405034081003260001d80d005232801040c070700040109040c28404801440040c000e060920342c1018809414620302404211400d10b01081d10190149200049401c40e0b030014840301c8245010b1074001c1103a4020041240174064a0702d0300702c616030000094a0149500541050030f05d01004001c90000d94124001d6801d5105806151001d483c2c48a00d02e03030f042a081d5580400d20f051010044c20b5420325482180203a0040040192105001c41c000100380344520060a090410b0040b070702082840141c0a081520001028107115410900178441c503803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 113667958 1250 113666708 113666723
    0x10080109180506040b0601120603080702090606030f07140c0610080d090b09090604110705010b040c230d0e0d0c05010b060a170405011b08060f030c010f05090307050d0609 75
    0x28801100c101c20180e864038000c10b1540030340702103000100e41540d038503031208062420485606e1b00a9600c03050740d5481c1c1c0140e1300588001a60015800c200b4041503100c607054962034a582000880d0048913400140500200903c03112840240c1101104892004a801c82150043d0820900c1084054100e2240680314402c140f038949545002c5c10f603240460b50640440f50030300b6820000e1000100c0014030301035001e641c60240312032801c20030000c0e01c1401c0c00740000240056800c01404101d4901c241c0207800d02c03000328480d4101100003003a19802c86007049080e030b01c40d8500352498020b020156507265840c050080000e81d525031081c10606283d000c1d5000f0312885001d4010300001e480ba03451514001048002c10650200800e104190060720840001480800c03039106c0304611480c0d00c0120300058a800140035561400000d28940e49001302c014010250300800043c010b240f610340034006118003c07401c0300301070b40c0900c02c2d040208030290940c20080e0309868080001e1885a408940340c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 113669064 1106 113667958 113667971
    0x1a070915110129120712021201090203241e07181a04050a080c22110a1e090305030d090c0b0d05070210110910050910080109 55
    0x3c0000c1030321030f5154071000800c090780d500c070350080c6003980c050001401481000a40461401c1c0d040700d1050000e005200786502400c4443e4020790306006400130103680e0100c102e6800c3d0340480803806070005503a000000c1b1015400041480e040f000958002040b00b401804100200542050560030341307039807511030506007541144001803292010800304028148000c0c040e003d0315001020340381c10300d480e0b808034000f40300e6030300e040b9404042e81038988501c1d102e513480000b01d901140400c0359289094270002c6d011802c80d48004010300b460b001e070005618400c401480039241c6c4000a185040e00e9003200f0806041c0415040c1d40c5a03503031246c00158460400f000785901c544c0070788041503500d0601d0b80030b030901c2011411011200d0800399031545039542c0b03004603044804201c1d401c407945600410100c40b14081c0c51034079a00844140b414089450704880c16038102d80303002c082484403 = true := by decide +kernel

theorem cover : BRFrame.Cov 113489208 113669064 := by
  have h0 := BRFrame.cov_init 113489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 113489208 ≤ n) (h2 : n < 113669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
