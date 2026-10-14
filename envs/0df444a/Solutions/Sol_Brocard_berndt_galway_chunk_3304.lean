-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3304
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:15:59.008472+00:00
-- url     : https://prove2.me/submissions/7078d9b8-0f90-4bf1-87d2-8b05e73c0e2b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 594064748 ≤ n < 594244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 594065998 1250 594064748 594064771
    0x1110312060a17060a02130f080625090536090d18230301020c0d090e060904121b0f020f01030b0906040c0302070209070c031b0308180c15041a03 64
    0x171769521a44e0042c4d03100d460f095500ca0558a00002d2a0072007089100140204078080c00f450319281000200000d81c54454207841c48200e5040d181194105060b801502c0007503440401d04007500724045520721024041000e8050b485019020300d04030318980c1801003035100140c801e0b000c4a0301007214000082c0318601603c81384030b0000c0243d080ca207002c2d24140c07900b0100b041d00d01c0f60002e00003800ca800400070140e440c1c0101004400039507100c8510750141418407403004050520f900400d824010040006007100307000c0d4032710f03c121402401a0f0103c00f81c2e0085804090305940b030480e115503107000b0101e0082d41c003200301180c158000d00a0364680b800c054011b61a5a80d4201042f01800d8034019110601d94200044070160f1a44950507100b50031070345602c40c40c94450318000341013a41800d0020302115003c0c030950000380c3d000074295004042c901c901400400000e00c95402d128400c0495544020180400101031520f10b014000303c544800080f20701407059040e8900600c02243c5d203540c0d15 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 594067248 1250 594065998 594066001
    0x3040504020703171009180c0501030902031903120e0114060f0a0801090b010317040608060d032f0c01092d05060c01020d0b0d030206070e01110312060a1706 69
    0x1400c140d4007500e129802480e0110309462404c0711020324100695401c00c1c010000e100902c00c40445010300b42d9800030b40c0325041011f030351b141c94414029955020340d904254991001000f0b550f0100308440030105040d8803e07040c800075180c081c084002c507012440709541000c0c3e00038030706c006c103211300d01c084007140350b003d440303541e500040000c40ca0814a40c19841f940214002c0b48000092042c091024440c00c20700d03440f9415801d042490440b0603440f040500c0d42007009208480d0300c4494144c1201054400c0b102da00307958642603840150040310610300120103220071844440010541c0000c1191000382c900300c104043c011182d102075401401101d6034020100584143c0308014601c072481c0c41691081400e07100c03400181d141e40a4015248aa034020810700409191803041061329901110400c08070310455070040d4503018003c004074244584c80781441081d901516141c50416800300036682d44544400000c0c18940d4151500380c040c59143c60003150f0340003560012900e0f52035140007132006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 594068498 1250 594067248 594067259
    0xa050403150912080612010204080606040b0301060b0708070c05220f05060a1206060b130e01080c090f0a0f021b0708061017010b130e010c1e050c01020c0a030309021f020304 76
    0x14510081e11064008041e01e102c03001b15042840a48042c0015201070041c80c10b0442c1003100381c94900403d28070a0349410000c2000750242c00c115240103601c109515140c51050500740c4a400c2683d00140d0081c0010fa042282c0309802d28200a041181e183c04100e030700365003081d000480350110760302a0003d16072070040c85000082980107281900c9588086a401d45400030780503142c11a8403001c242c4038601c00140030300e00300c441c1200d0142601c0d00090150803030210010f94281c0d0080e00081040341e1440c007003043d60060350403405031411000703815075442d04554503800c003200d423144040405000e01440450590703c0441c0450040c2c0015507440d92103800c0550070114040d0f540200000380d0b5039000049000e131114100d07070784c00344031b9040d00240303c403007003070180303094607081c22610302041000310b0301d189070601d20072425070f414459251140d1a551110b06003402403280d141c00600d01c0c0310b005003100c10540e0580105244034401e85455030300d2960b0030301c0300200300c1e6542d1030000903810a0205100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 594069748 1250 594068498 594068507
    0xa080a0b030c061b0703300e0d150501030b0108012306010e18100e07030228210e0c01021501090b01090302130b011e020303060913080a050403150912 66
    0x180110000b5020f00344100d800d1502e49003404a40c07048821f0301049840d900ba51301c00300080b26003203824010000c0ca851401078014030f1000000011446020755503803520074805002402c01e808044080c041005503141d00b040740d4072030340911540300150700307225018400564040640c0f020102d61000301005807200e000542d03101503600f001a800c14841d800246a0015034045d00b4000c90ba18081680b106082141280b454603000b4007480c2070500401184000399003058010382003098101417652020b2440d0411510b0300143c0200f403001c240541110304001e441076101c0c0f05c50203a000122182a451a00160b07202e940b5803083c03022801d102d400400405006802030807010030145001401552241d0009410351070440c80c0608442e0398103039100c0a9608201108d10a080c0307207001602c07820b420f55000f0742d42e1000030130442c000e03440f10300400e0b00d4208541c0c2c2615100c1c0d0201003580c07160161a0010a15003252005503055084095a802e20071040d201780783d0095000060800480d03074503070058a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 594070998 1250 594069748 594069757
    0x210c140a030e041802030303040f0201030605100512070201060b0703020c0405060924130207030203120c1e0f07060e060912270f0a0f06080c191103040513020a080a0b030c06 76
    0x105034013080801d03a00107a8060000314840d901c10007030f54050f01c1c2607000040442d1440d400c250300a562203c6c0075074402d9005410b41e401510f20b04120310203955035007001c0340500110b40c0400d841c98400b10b0442c04040c1c0100341111061000d640802c49699428108080e100c0d0a4070707060f54514500491210720b00c81000c05101821020303004058810000c0f2040040342c1c040c040640050f080402d503041050000e140080e040104485890b040144c5040c0c10700000c0201204443d044070000350044d00e1146400a9845880d00640c0401c1140215070b046900d50034100d50719012801407000c0003010009242c00d83d02400d046400c00c5c02a003c01c038584508401045407060717030090348500030142d40e0b62051201c0d0b000e48a9501404a0340d45002c6015020080180c02c800b0700100600484c3d9410807001c100304144607003882c0203045804050b48217030540c425034010941141d075144034801c1c00340850700205240c2510303a9030f000741c1d65a401640c80c00c440051045a605811004e80070020b80b85c41d50240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 594072248 1250 594070998 594071021
    0x5010c030c080406210605060a0c052401170a150905010f0f0608070501020105160c020109180204051c0c030206091c050d17010e0c0304210c140a030e04 67
    0x3031942603510b4440000c1c54000c3d80c0000b0000b00802455050080c40300b22110a24034211024803140c0e0802d000203000d4024645180200800303c0d0380081884010406074121031034104102224401074012840003c00c00d004400c5081c000c10000d20a0b0037000490441c69508507006208004c082e034851005010340c050143c3d240c1d900e0f404006c02007401d912a042c0d14030747c00d08001401c90301d0841c0702801d00ea503e40c000c40c1564508070401c41940c076014403251b0307101d68901e001055a0120710043c3c940392156081801c240707541c181c01403820007459005109175181241e1810603480d501e00c6101e0004461040245a8800488200011f08101001e44031100005080c0352900b8056400041d0b510200d40003607132550321100c0b801440c503405c210041c041d00e02c03402e46081190704000c500c2400c86800382501d6403607038000000400b4080422540c1b044150000004007000004840052600e410460180d6401d01c0d488600c00c98504006180002c00d585030b12012407048500041000514881104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 594073498 1250 594072248 594072257
    0xc0c080a140d05090a03030e030f0405041104030506041109010f0302031c02030c12030a0507030204050a031101020a23070603021806070c080319030b0405060a14040f0e0a0614060a05010c03 83
    0xa0202c0c0c41c055000e000c1c07140e5000402003622680d9401d004007681d00203030340c40070240c0080000004060b0000c08860540b031041c0c2d00400c0c0745d86154100c50540c862603002503c1d0340204d030240003c000500780b900b12501011a88004d00c2e988520309d0100303800b8681300096056011158240c034081c034101e214107003000180103484c281441800014141150040c00d05004400001000582e220900c101508840c2a140c00c604060030f0201285541941d40405040044e8211031841c081c0c4c820044210000c1c3c0c0030000c000000c02880d4a444c40640b0580c5d954254002c0400114000c1c1c0701c0d1080ea11211030101c12460100103910034800d00350710160080e20814503128011504e108108010000004900017001004602e840d008040b00e1883d1401807146041c1414094203603074403091002a00d503407141c200b5003001418001030003030002c81d1003540d480d0705000820821060121b41500c55500170403013409140100c20385481c1182003240c509501048850040c80707a94800e00180c44214401d041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 594074748 1250 594073498 594073507
    0x31918050609280b0d2003040206340b0a0e0c01120e0304080111030907060507050706030b06090306040b0106021506100516061505010306090207260405120d02010c0c080a14 76
    0x12504071603101e017440c04034183d2202d43c3e00b407079100700d000c0c0440c0c0d800c0050481421420203500148203072040c1456440d81c40b84080d01001c4009441140744030780015408046051200361a0004035601c0031a482e8100360324000c80c9040c07841e0701013004014000140e5607440742c0342081d003001c001030080d0342c0c0f1026188814000498111400d00c1480c280002c036404481d201d10f1700e216114a0111181c100c1e80c200312050200d2000600d0010b441029102282000329400303810034041005030103080724040c0e244c815030051209001100b4035403416101180c1c01c0d6040325108801c80800010f094840f03e03000441ca00d1000704c0248910b01070301842d18990f20340030091419446810542c1d6076084100c90740852800c0801c0a5a018864500200f444100c00d50400240f91600454000d143c14010051801c8038895220440b407401210701620380104842e1401102100d034994805940d50701038003642c0703021074048040340070310310a40140b940280c0091400143d9041100c07613600c40d00001002941c10300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 594075998 1250 594074748 594074759
    0xb0103060c121a03071205062418060405070504121211030c01060e0a060303051813060807031704051c05010924050708060a060e0303191805060928 65
    0x8084490145460b00d040c1034501401305418804181e02034143d000d90f20780078100180010512a0b4406041c40c2e4150b108503000c41c441071070880780c0038007039032002034207030782c14901011400905c0c05103038280d908010540d240b0100392480d214501400400316900806030700010034111107401c01d05018a03222a220038906d50381440c5802446a600150351184d409008081d4000d9109501400707220b01441014030b980c601600074450601064651030080c0c00c0c0011644414007416111003131000c0c100103250381e83ca692a01d41096000483e003040c40480b52003000b0441074160741c10340d0030050560005003000c880d048460f002e0110f00315603d5488a07400f1012602d01c0740354062004118401008000d141300140b4100c510042003001446103500601c09a6154440c8030020b542150816920002020001074030354040e1a22081c1c003100303c2c2240b10f005030340c00414001400300e041c1c4104211900d45041040070f01031798884940100c0740050000c0308001d070b4010407a80b076600c1509000500d03103e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 594077248 1250 594075998 594076001
    0x6090e1e190e0d05090925030f050a0218060d060807090207031214070c060603050d030e12120604090204021b0d0908010501050d0f031107060e100c0b0103060c12 71
    0x212a0301c40030000305500a07200904500641c103284042d1000b80a04254070403000e41076003d1031400340c5c040d540c440c00061064400c00c00c8504440507a0301343d1340d030344074040c48024003815040d0000b0407050305090100344040440c1c000c0d2544603400e21201d401c099040c105100003900301c40c201c000440d8880c1d40016070503105110b41d0010740050400565a42250b04018000342c0c03400e42e04a0680e4602328444805460b800c1525801c40c403075150194010b00c0320b00b8450b003d48000d40014107a40240010851180d2300f40d802189010760841c251243e0103c4000000da06000f0355002411111070100000c01c1031401d41d0002c98402e00c028401810314803d07034035585400d440190145050b03408040704203201c9400500304401005540c7c020310866041001058145a82510040801043d004007504160081100014440c841c3c0c089661030380e03076180300620201503c1c1d0003e0007201024010b0100d11310503d59800c40c00d81044c00b00200d17074a0740e6105070041480711528800c0010980389500c80c2c401d90f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 594078498 1250 594077248 594077251
    0x19020a08070f060c170f0c071a010e0c0307021f020409020d06060315030c1401051204080702011e0c14010e0a0602030f01090b13020a091512051006090e1e 68
    0x110101c810100380762510304120303411381c001e1a05001142c00b0211160124a0649038803259100101c80c190f11441c2c1d40d103140c1d0080744001132040506108000b03081203107441c6c0398101c4800e40540f80141d2a00d0b11184070328803040c1c034441c0041e003101c0a940d0301032120740d9a804907280080d00040ca0f25550f991484101c0e0800700347c140090fa2100d4042001e03540c50302880714034030580800c00090030702d9545c03140700311009440341c0c600355181106806010780c000d4056032028200c03400980c00500e081d01d0f010106602219041b808900d80350303400e1602103900c6170704c0d424401d42034460411549541d15000e02502104030301c0e40d2159200c80340703030903480010700c1864040c034400c900168a80c28807501c85200280d050300800030b01751600c10850000d586d0b035100d41154810f10480140e6407031a00804580600d2281c100540c12500f41c00d050100070340c00348143d042408006010410340d16040b821020300b07504c3e0303c075000c001803a00300709116044020506a40101c1140302d02c0324032603032000c1d124a10690 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 594079748 1250 594078498 594078503
    0x31603141f0e010b03090d020d1b1a0c07050d0e18100f0623030702060c160503040e070e030c030303010b0f040e011212170f04020117090105092119020a0807 69
    0x1003c810701545090400811f4945500307070000d020f21301e5803500000c01500e04440c480500e29000c60030b400034014016a11a6201c00410740521240703030140c80311005034010442192103100c2c41d000050b01074800d18501c507584800400d281000d040700c1002100c2d2001c080d100b0420035600c03c4000403c0c01403a40f040009114503210070011480b03018248501201910161400180403c100081c440e804180180e0160060841c162110401c0a41100703000784040c004003144000030740440c02c41071415100348074222039039400081c0381c007010906495110030088182c05900501c0140441d083c000041c083c4103101c50075160401c0d5903011011031000082c0d00108040a10304a90000d2007495607840c001d00d0040d04194808855102c0c402d691108010203143c0d820120201050440e8410040341c40c00300130072a1090780320700b000c2c0c416034000c3c102034800e401ca52003001200300c1c10031800c14100e28041e5001c4400c42c01d009451000075804a940e52070a821801080c0f54a400500b0705170180540c40e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 594080998 1250 594079748 594079769
    0x20c0109060b030c06180603040309090f0504020f03010b22090c031101090b2718101502010b030309040f0e031b070b03091908040506040803031603141f0e01 69
    0x6010030700f4035080603840c01146014100400c59140c8051003151501901c08054078425542d9865040460315443e05802100e02c031420041244031248060b0032940c0914021151207084040d10310405007268064071030706400400341c48490324000039217043c800c24001c0b150310210b0003480e10394840009400c560000c030b4000d8051103422000d540c2c01720801010b04240c045280c030704510060241c0300c00c180f000c0c0c98542f00340c00342e418502c161107600d02c481460f082c82d001c1141600b4a65000001d038001030289080da816440e17030380240c01d80305020b10880004050051460107805d2400d100190940b8101d646c200c6884410303100c000d0008000510001442c001406070004460400e54104441d56104021b0014148140580080d000c030b041620001420031007140500f080c6011741043c0200d03807007141e00c01c02c08140041c8000022000310301c40c40460f00d00b4401c4403485202541103c0342140510303401e40501c0002220040c0c000718205080d081c0301c9020801c0d60b82e0380c2014080394000d801009940 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 594082248 1250 594080998 594081011
    0x306150809011a031b01050d060b071a240d05061914280e03032802031e04060222060305100e0a0f111306022103010506070204020c010906 61
    0x240207100b076042c41c001c3e02c0f1031080310001c041c00007680c807035440310729018a6808802c420341c2603000d0011a442c400c0045400d00006640f0b482e031003c40d802c903000598441c140541e24549041d0980700803413041ca130341c08612455810b90705180d4008691100040c3e000b400d211144408140204525449400b00b180155541f001c5403001d8030903038010003031440320b1440312004c1c1300f96402107440c01600b010320001c00060703c4100351601e802a11030012001c2d0701e80000400e211201402c1c03080401c603842c0d070800210407000000841001c0b440200c031420160084151000300e0340d40c12840480e0490b00890002d030518900708111802c69400610340314003040030101c00c104190f01130155603404520044414000380c5071480c0300c00b03840d000400f4a04110344c1c2c1c1000300020000c640c080504050b030740c212280c85900c1d0901039020500c41e4003d01d405403050104640034000301c24001c011000b16000d03c1415a4a4401880010341011074226449030302808501c2e1051001d00c110b140b45409283e0102c3e52 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 594083498 1250 594082248 594082261
    0xb090903090a1703090603090109060606110114010e0c09010512130c0b070506070809160b030106020c120a1509080d050411010e0604140a0305030c070f140f040b0103061508 76
    0x18521a80d01c03107425103030b00002000c58040003000780d85030045d05a40a40d40e80d034403030045500400c44940c00800c25032074948041450366009142e031040f41d42d030500810084080500542604c08248148013030145103c0010344041481009040f242c84103040082c140680381042c0e410031b1104664100c2c03441d0901ea0804144003e5440c4000200f0091280310300d0099503031507258881c140100080140309107040802c0a580b41040301e02004114081c0124142d81c41301c0003140f00368420302c1030200502c070728900c0000a142007910714007001d040b0402003030000d42c181d80b10800c682040c0300111381c50350344103101c4c004620013100416800a040d20005002c0c5003034a0000d40d02644120310741d0400440160310301740f079202e02c0b0464081d80c1210b40c4031452441080d0008000e040c182e00f0043c40340c0004111905070100020710304040d0355100035803120b150388500c004a80d5104210307050303500100c0d11a5540032400c06510070f82c060b000600d000b0407066258540d0041070741900100200040015040096 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 594084748 1250 594083498 594083509
    0xf01052104020102160b0a200106030602071b081e1e0d08090d12050a06051c14120406030b03010912170f060d15021c0b090708041e060b09090309 64
    0x250034038403083c5085c45424007140a600d801142450024403020801e82c482250b15415450b04e494036800007445029220b18065000c0d40080314200e40c05904000844c14107160850341c2d10030340b08508024412a03215071900520350400f10820185801600d1055407440711891209030620355000042c80e28010030307540182071050082581c0c1441d003004001c1200540d000320308040c604544c000108075500c803003006200900095000a178424610100302c0d0a0741c444090b00403100d0f00900e034030f450880386104166214491203040200740b01c800c003c2809410b0081d844a0480000500001582c2445580300c454240014400c480458945100302c4450002c0c40035050340f250b0748800e040902d06008010510341d1000035030050500300017400f2070007081d95035416188241e240d030b00f000044800000c155402005203003e02c2d2300612000e80090b4134103024400242c05103610440a580000106d01040124800a14116866920b403170b1074031480d0b030394030040e940121081c102035552440003404200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 594085998 1250 594084748 594084763
    0x1060503040b0901050f0a15050409030c0507210221060c19030e030703030c050f0d090201030f18060c050903070306140610050910170403110f03180f01052104020102 73
    0x3100c1c4e810502040342640041c06c519401402c0e502c2e01180185504242d61a07414554002c0d9401501d0131102c1c00c2499800842503c040b401103043c3c0d02401c1d190182408a041c000c076206120241103d903281c01030400b08540c650b401014115903040d65000c03015203003040b000f511000406800071a585000c0e04403680c900c007403072403241020000c40313003089055a240d0060300030240074140c0d07d685c1a10042c4c0200b017280d403040009480c46503260f00d640c0f8101c0c014454450260700181c0f8180b000c0c0303951040362240c040c4a118415241e03c001c250b80c0e8840c4041c08154003070004216041c891024551010410074020310b1042401007102070b081d200304096004018061031050012025010b440c035080700490f03940140a903101c181c1c050a4250540301c1c111800c1506010300c1c040020401855880400210318002000c20758110200403c0240d0340c81c0600142070f000a20508044844c92910070749501800c401030600710300f03006685640080d585620340340312070943d6034503040008640c0e0601414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 594087248 1250 594085998 594086011
    0x911010903050a0f0303150810051024090512030d110f07081315030f060915120609120206100b12060d0201030b0a09060509090304060804030f05040302040501060503040b 75
    0x640312840c644941c0e40d60340d0001005040881851503640606100b0740180c1d0820640090040c0f01580d10040280c0e6030109081d05520246002d001c1078119021100c50f5084a400080441900c403882101844030b5101c0d2680078144041d6010018440e212803c40b400c407440d60101039074503081a019100f00f80d03003221103101c10f071000410a0301c800380158420388040c2604401d020703454081c1000b0f2401746d0421604080101c9140c019200308983d03051704a030a2480281001380011603450a600c4159907115a0a500c800340411040c4800e201064000502500884e400308401403a52194880500545000e10050300072a041060060390318104030010081c0d8a1940d1074031004806000b94100064503c41c461040c0d40c4a8209581c440c0d04900d04441c8010001d419842e41e500c1c8200c018403e030f1089078059001c20f4009230b50598040103842c11500340361696010380d5141e80d001c907100200c40081006001d818000030025032600d1280c90301900594450580ea030404d402c00303800c3c0100c028007c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 594088498 1250 594087248 594087257
    0x10902070204180221012304060e2b020a0f050105040b010b0310210b0f0a0c0905062b0f061a0c07050105090a08011103011409010f05240c01091101 65
    0x150b200503102c08010001c10185080310001724140c105100d809011021100150204240480c1000502c92207910b40500c0c8207400400c0f42c07645030701000b42c407900d0111207844c079040625080c0000481d05250b6592800d861b00c151807080800755200170060240800c01d0302c441e9900c82c200802c00640364040c4d80500a00131806082d403810546c3d03142d0204550003003007080d850800c000e0391014811884100f8103940015200c065182142035080b080300e0484000002900b0004e103007030003e00507000c2d0b20a856010305041e01e0100a14613102c41900001003600390f4466a010040310807006110380e40c6002c4000303101007801c9217400350701c49106031403081c04d0225040030807040682c3d0f440040e020044601c00c0c01c0141d241c0c0e541a0009030540303603540c080c02d0f01e5400c150041d00c1010341c40c0002c1d4142e80e4100070f600b0f507030f14210040c400c468001740200041094040c42c00e028a00c2c0144003400411000090044120644000080107810210700c01c0b00aa450340030a000308051a03250070703c5650300307181 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 594089748 1250 594088498 594088541
    0x7031403012d05041b0206060f09040b060d02150a03050c0418051f1410020d0f03090606030f05060a062c04050a0b041a09070609050103021809010902070204 69
    0x1224a2106200c0740701480b105003a00031688424107205160000c100080080040704591940c12842c461007070fa420005000303004c0041c816140c8007d1844204001520020fa0340e40e5658031034105e681c000c6c01c05940040030450002c01660b545140c204000c0312812400c0d1a104580c50240036160701030849501208184800d005403030340340340d050361015440381e400b286c1ba0720380e08074240c0740e2060140303074900102c0c0c00c120105030351303002c040d00740c001610a03511031000300c03040c120803078945443c4404000040c117120340800d60584280c1182e01c1c400c4c0070781c800240c403d0ba6503070b070040004c1d12020300b124240c0203c002c010103464240302e20001401304000d840c002140b00a0800048141603214008820300304c00450240001004060078440d40402c01c1c0020b4206428081113621114210000040707100700010300c07070b00300400c1020803200d00e038481d02c02490810005401a41240000b104460525120800c090713403100301c554000c003022800140e54240600502040d03650000d001401701c101c01d1b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 594090998 1250 594089748 594089759
    0x80a050a0905090c120703091b05030c09061f170f0105100c11060d0e12072d080d0e07060f0924050c0304090623042a0210020c01020703140301 63
    0x14115841d00980b210703810219601d40100303030000c11944034060000503a09c01c55045402d8012111001d4400c21411103444841d2181000b2150000702c3e4640d1700162081c0d50441240f281c01b078180000e000a0405071083c1d032039018030489588040b0b805084c200344001c0100210b080c05000c00b61240090f1034441c01c11545a107600404203101207010780a5940069102e00b041034582c810b5940d000100d090300d9807458910b001c0c801d42d8109041c242c1c0c00f0700480206031a2562081c9242d0624100300080054840c1c1c10b403910001900903d50311000340d030b00c03000b094035404001d0010201400d61070316500c1650081440c0100301101580200301e4400c40c410384204a503e43d05003c000f030009510f8207680d1880203c1c01e090960085a100e007415078140840412580b10044644a8000d50105041800d546410800050751582031103980d45401080c00d616409080a4842c070403200107004440540340c1d070029180403a4045031080100765800300d5203604041c0d0000350301d050f141e1558001800c650410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 594092248 1250 594090998 594091021
    0x160809070e1f14090c0408070e0a02070204050901050709081506061305100f3902060405030a0b16020706050d02180a03030e030f0f28080a050a090509 66
    0x140103808144224038000362581c0308900d41c5070080b15a0440d8415110394030b0b072040202c20045190395201e911510b000407a01c1c0f0b4528259001c4900070b1006000c121300e840c01e40e0490500142c1040c0d40340360200560f6025890740d010b418002c176a480300000341d519104000501204e5641c01100042d00980388500c00c2c1c0b8403a482054101c401142c0842c0c0c3c41006120104511019a00691308440c00880c1e0311480d079080b240950803481e65442e80508125040041d032070f40e001c0300e00f05921459107105030348a8010725000404880344050809843e00707446d100080e280044455045038124030b41401c012907209a0035141c40d04180c1800100101400c201014007140164020a68411fa000c1411200e150642d01811000003002e0a00c0b48260349a060080000d09200b160310700911400c10400790407000024540301c502841d001a00b11044c03079100610b40041c0a011040801911001090200c0e10707100042208405c07988426540d6203000c1c42c054103207841540901d02c500f480800304500071980 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 594093498 1250 594092248 594092263
    0xd0b01030c0c1e020306010b04090c050703051819090f1506270306140711160b0903030c06010b090306070e0904151404120306140a090e0f0109030305160809 69
    0x403400f00c4800008000003a840050341c8000e03615204020000840300101802001039840442090007440600300003610f045c42666002070025000304081c8110070503d00c6100035170f00c402069200380700c51000d03104146016540008412640d1250b940c0000f41d9981308410f08807913043c041c01e03220351030403a0203008507070120b03c0d2601103200b83c00c00c00c00103452140f001d03015660042d001c0015600059111104040490304540856240e540348001500700080500d158000000b40c40b4440d81001c0c001d4000e030300035079152a0584014000c44122100c1400a5030281031045826501e0315803100070580303010001f0703184102340012103141c0034003502d441030076030f034016006260b400031907000d101404000d1040500d1220701610140c10b00c0100314500d00700721400c108554003800066100c02c8020441520306d02006e50224541a04001001e03050300858000140c90302941c0c110a544031060b030075166007100c01c80000c0c0d5981c040081c4403c002cbc1020042a666140c41c80c882c1c5040d00c001d50b0388904 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 594094748 1250 594093498 594093503
    0x1401030221013611010e040609090b150a030b01050613080109050c01030e010c0207050d030201060e01031b0b030613090c050a2309040519051608030d0b01030c0c 71
    0x90022030900351825107112048102444402001101004000d042d50000350740b0301c40300355514004042000e0003c031020f07805020b07005905641180041801500c0702400f20803180e4020344c039000300051703101e501d1040f603903058003918503000c0e80d02e096060340200d4a003000900744241c1e4010010704c0806c82c0300800c1419103006403101c55440d0927406044900c038216a002c9002c075807c000007070003040004030714541d00401c280c83c01c1c86600c01803090f160981311181c10710300040c1c0c44441c0070000792401b6517031500128000c0c000011200c0d00d6810000034140d0907003080d280a80014408101d0101c0c1582c28001031808141c3c0c1c608500f0004001604841401e50301921991240020340174401480e03203c1d4010400105201030003541c5065241011040800c1c10601004119040b42c213810050342c4680308581c4603019002441c444680300d28041ca00800a60b6188600205900241c4101195034041c141c2c110045803500e03944160300c1d0a079040078103c0c50402d0709180c111808590408020300660790b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 594095998 1250 594094748 594094759
    0x20102130303030f020403020405150414162105240a21060e03040602100e0a020a03120e0607060e01052a0703170a020304031106060a14031f02041814010302 69
    0x11340d94400741e40a4003454002a51007803400d02404100c0045450150f00e428041c1e82c1484401081c00c507401c15201d04440c00032486e456001103260b6280309840222400501071200c815504400000b0811104222148181c603104100b103081c0038050550040245002100c0f8924100e09000c800c2d100390701c0900b440403035114441a410100507450f00300c054104006001c81e6125036a4070f0000b0b40d034003280f0800d1a8814a088034a4039550b002003803c0428075009071500004038039556404000d0880840f05a00300a5011128070389542c1d40001800b034035000c1d03800881c150320790b00329090840300c01405200c503601100c40c4800754601c006404007188806c0c4a01c05803601c1050030305a402c14201c00325080702d4500300c01040301a200a0b405903018600a5548002929802d041d0f203a41d00c40c01d944503a4030060428040010b4401c4001000084101406403036000d0b600e01d540c84000040301c0e20b1800a0760b004103051243c460351011100c550ae00b091024001105d021000048440040c040a03000c0c0c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 594097248 1250 594095998 594096011
    0x20c0603130501050c3c07050a1e03080a0b010f030b060c030318060f0712090c031407090b0a14240d14070e18071b031106060102010213030303 63
    0x94000101c000c59064101c0000d0185142c0188080e18951009031810a080846180e004002070301c5030048400b000c081d0b107007401100c038a40c0d8003401e0303421280080b00e103841f401030880c0016178801e003008000c0b560320400f80800c1c4101c0c600642604401442c61800c6454040d0505c6103a90020761884012000c0c24001194124076010541e14425400f07030041d41d100010a01003c030440c41028809c0c200e44405079007142d21039004809420805440c0e00d40003501000b030150792001990b0199032840c1c4110319200320140d4907902c00c0360714141d00c0031a482c560000c51003006007180038040d401c20b0503011561a0f0b9000d0500100600790310645100d103000799000603000e28100e0400404ca8086a007050143e80c0312404400310fa00030746695031210150011001c003081000b405800c52a4241d0740080c4190401c20540c1880c101d4103500034105010454200280208680800a1820994003968820385100c44441c481454460050486411a88108410b0301100c60b8554a0030540f43d0610700491013 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 594098498 1250 594097248 594097261
    0x308040b040204020f0c0703060b19141f0e10020f0a081b031308150103150915020f0c07080c10050c120a030207050618030301050d0318030b0601140a020c0603 70
    0xa002c1c02c40e90080178000001c0540240a000070250308407486600e003803080c2c400a105001907000b9401202e07a0001e0061030601c01000fa110f10554003000141040100d20b910002c01d070340c45040400080045003003282160582c4c14a00c800700d00b07112030703800204802c4d1020b84042e5aa90318003107000e448150b01103a622104c1103860041c0040d618400c080b00c0d125005840c6000d004403140c41030290b03a04c9402c1c650400d4030034141e0101c0c100c5c2d401480b915158405442020090264a5001c5a00b240e240d80c25548116151014020300d0f090650754584039603140c0821403401c0c15030740200791103611148403801d10395035000d0b402500c4901c3d0319200f80c03640031340150b40d854805030044900418038085400c102980c0d02d5809012820300600c04c0301e10540380c071281c44140814401240019800800c01888141403c002100c1da40d8401d00d0320b03000d00c161003818421000b5040c0c100321400800001070001c290b034030140e0340c00900740c9010940d240414104003e1350715a002c400850007180003000044c40d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 594099748 1250 594098498 594098501
    0x50f1008070311070c171c02030306060d0f2a050c03220e01060c111c020108130c08030403060605090f0a0b06071a0601120c0905040203180d0c050c06070308040b040204 74
    0x124940c3c01190390005a480d00c1315800c8214201b2020b1070240705084250402d1080060a480452000d4000d0351071511344405000859003c951252400c0c0d40303415280c03500580902c10340842c03003054004041005041d196041da2a9101c0d0f140301d080001c24840001e10090100c2115580c08082280c0c0b0042032120550b0550300041c0d50180e40007c200c0000000c201d60070100c004d05591140d11b080038800c8081d01000b81414106401e04170500b00105a03d00650241e100103030000c038080600400d94000303603601c4802c541c10ba04618000e400c0030030308004124a034042c0030702800c01110580d02c0d514001101c08041030700102008104c41d104c90081500c1d4985008880c00c0c2900811802c40d840f507000921104402c080d80d140d4006000c00c00d5110303082c006486518aa08490344d00c1080e02d174640020000650009050880050a20740c0403100311b10f410004003155a0440e120008a001ca50030407a00740700035100640e000710807c1200c0710009602038450750b4860350001c1850300b107483d00e001080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 594100998 1250 594099748 594099757
    0x30c093c060206100905010b0306090709050409050309030609070506030a0207111f2304090f0222090c03060f090515060310030b09070f0608190c09050f1008070311 72
    0x508100c21490115000c0c2d40880c070346120b1540300c8280c09000da40c4116190441c0d40904c214030302910300384081a0035140c0060380320b400c00380c1c61420f04a9161640001021512203403011205075000050240440c10144045544810110040c0c180546000007080c0c042c44010400c00072030351300107401d030100941c0a55503003800101422042880d201d90f100d00c09018540b40c4800c0115015130214040510302c5041604800e140d003607001e080074603107180600030300384860640c04c0c03454003801804c00b68040f11944102000c21200c44440d00e501e00a55802124a40c40740ca60070141002030500a400c81240349000b1220355000c0010320366640700340e034100071104101c0ea55014800005200031068042c0c1860280c81c000d280b600f00507150100855914074491144da8003807a50740380c01b04001800341c2c8900360b101408011400c07210320780703a0b03084e0101c48100c220440811800c410034031050130800c0c05409943c2e000e80300e001c0c8071209240c000d0020359008011000701a00d521804070f2025000e015038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 594102248 1250 594100998 594101099
    0x1150221040f0b0c060f04020f01050702042307090b1314030a0c1e0504050402030703030f1808060f0a0c080f0a09020a0314010e0304060e27090d030c09 67
    0x740120f84502c0c00750040d0b032008400024521524001c504143c601606041c01107600400c5980d40c0b02c2c2d158015101034100d400c0c2070364020354514182c2170314031440002c0c0c004e00001c400750302c3c0d00d89411000035140d0710291f000042003034414814104660300520310b0030144d41401c00c0c1036080b5403807000043c1c40e02002540081c1404502240019a4003c185100c0c40000103c810310b640130b5142c60071300080728802c030b50184d13142d4480750080021038010381c81c0c442001c5941c5050040c03c4004c0440c00f000f807500790b00044d5268019410005154414810b654111120710000e1111001c2d15030018001035000c0d01c02c000f81e206450204c1e446e000d40d540840541a0b000d885004803960703a04060007103441d000e030798159550811076a9500468080100c405407100740e11080468051002400b111044881d901c5070110740c100006168100c0ba096028841c0380408000d01000401010042c20388503141169018011800010b00810341240314030b440302c0e841c40308454408014010000c40400040180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 594103498 1250 594102248 594102269
    0xf080c061c020706061502030a0c081b030a0804020103110a02031c0b0411030f15061c1103090d02070501020607021203091e031810090302011827050115022104 70
    0x883c0410400b42c1140c070071903d41071050320850308500001d0b41c881c483e510003500000c0074507594100003580c01c0f0281008500c40c00e0403002c030302445120207203541d01c80b040701004240310300100300456a16000d101c0c8055103c202c510705049001d42d020355a030181da50916014011800c00c243d030543ca5502402130302100900a001c884064015855564020380f1841d568800300400100220100e11a60001d4503025001074580810020b80c1e1070740103c00c118402a041c0c4600a030702c284002074000d18000c0c94142d0213000c0c440c940460281c90151039074011415900040304002c0c07800d4000c81e0510b540070302011000c2c5c2c1d81c1d5505d107041741024604007403009110076810f502410700800002a01d5220718207540b0800d0b116a81d0200002501c0d02c244220020702c2410043c0019441420030340c1c40c0500b450210702201b915064059030092114800d05042e510040011602e6201401b91a004080c2c0801c540c8401c5180d032402500c802004482c1d031420319134065981f58074411142114001c0841c03011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 594104748 1250 594103498 594103507
    0x402091810020a021606050913090605010311031e0606010f0c08030f10080106050907031d2e05040210110a08040602010c0905010e031b0a170f070f080c061c02 70
    0x50200081d000030404000522400340c3c07805405c0090010b82c000d6503183e4903220f04000051041001c84000c021640c0b200c0c58440091500080c40d42c044e1314080c40c4102c1d81d881141c000c4809161a014500304039091240206030804503c241c00305100350401401e00e80006a40092102038407100f810707940007451040000200035403102c841224a0042154054240034a503444160f54282c5201c3e004840d0300c0110000852143c0e8041e51203003c0300041c0890052800403d6008141441c4844040d020401c1070501007203c2076241000c0007072103410b0721408000302e05260f00496081038001401d2418004044502c8010a030104191008107602440f42d40d0f032251a410000e01030300c400c001030000304404041c04105580603001b0083c20b010090024000294a45014802d17500d00210310b9420a140300000700c0d03003a5103000c480005040c80802016503401e058040341c035010031503214140d50120102c00307000184000c9400c2d40409810ac51540c0c0703640c000800070000401421401711514400103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 594105998 1250 594104748 594104773
    0xf0114030a0f06021918092a0309020f06070c0923130b06150a0f03060906060203032401020d120f0501080c1504060221090324160804020918 62
    0x40017480051a040e1200d0340c020b000c00401d5440b1aa440c400103900070454000784480000c1e6401110380307403402c60040520003c1c1c0e110341c02103040d005426900082d11034020805600700130b481500b05420036540c15141101585910180c0a10f60044c040216140ca0601209444182509180b60b02c615004e90050030031b040f0001013510700721707001c0703072404110400900e4a10300012094a4804d014089614004401c40d007190000050482c81061564814021803000035074480c1502518050700103540e41e0415840c08070b811049048600060940c0000c542400e0341c3c007040790b81c81d554150030124840841c840d5050b001d8401c4280ca245101e03e8400001810743d80054100c0249100340c8890712221003401d200d41c0a07100c2d13405a1700141e4020f032401800c2a21804548035003006801d4110700701180140020f042245802840f00e41518844240144c040c0c0c0c0c219494010701c2c0000d840e05948a0140003601c0d808006101134441ca10031400200340746a10844c10050b100444207540c6004d00d0031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 594107248 1250 594105998 594106001
    0x6120901180b01030303090311010507050a110d0504030b0a09050a06050105040c0f02060c07140618070e070e1201020c151f030510050414030c150c030f0114030a0f06 73
    0x1112a05159801e1881200001c000a070104116a030050303850729503682580ca0070350140c05035400c00c4080151200046c00c0b901d40038841c043c0500c0d81c1d55601561100040070062041042074080c003495005100141c0c8142d400408a808680c3c0c04101100c00e503881f00b034140e000700240780c406401030081c202d065040115503404281650012901040200701d940e9048450003e581780c2c00f0013584c0640081240884548050714005d0f104140c0d04803000c00c03c07081c680c18a80252020340038030240000702c840c1c0240610109016003035104c0d2030400c520300303504000c1807124240e0045000c0c03403018100c000741a00c01e4041300d924404801c101c84441e0303c4035124220000d0210303103248120b00580c04260f0209a2460081c0c00c5a40010080c0202c0040c2c0c0c441800500018000300c410f203d40c15a00184050103001502450320054050403c4403040060f481c13103190018080f5149500410401c00c80000c566603039030541d01d81c48807c004200c54000130a10f0014840340113000f145168a0031002c00109 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 594108498 1250 594107248 594107251
    0x18050c040f080c09070521090a05070801050717280207050f0c01140c0c130b090f0603160506030a0b0411042301030216030e0a03020a090f0b010e0303070201140403020612 75
    0x1950303221310b1a9214a401c8907075000740b1854028100d06048250020341a01011360f0304005144181c8815070895900c05203410007550180f81c042c1d440f802003100e015041502c00d494000c030044a00b0b4989000020031100c07900034111004440e00c102d9107801c1e8000c041e03040d130301c100d603100c1c048881c2426120b0035640d642e0480c8400500161004e25050741c4080720f40300741d0341441410170040c000d211041080103c6002681d001c10800c0340c0d030300400540c41e5110780c81c490181d40c064a050200e400e01d40145414110aa0351400404035410404c03c85074803008120b81d8010301500b00040c16000c042c0024000d040c1e8034100d032640c0000420041003001c8003900d40b000510020070001d8940d4040001542a03004040d0031480d0038000410900109001c2e01f0014094a4010f14400a6980b80e50014040003020340080c09040d80d5032102c1007160300036100d1022001401d0a00ca10145420310000e43c1d04d100d552802410440c4030803101d114280c40400b6a00030b16802450f854031040c0071141800d0700e000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 594109748 1250 594108498 594108523
    0x90318050319020114090312070b06010c0b04080a0c0c080d110f030901080a09061e0c0e060d0f060909120f0801210206071a01050a0f18050c040f08 65
    0x40940000d45240c0010300e46110040c0d10307410549104960015a00060042162198107004201d401119a0248a100c4000c2180e264068030340f042418260b0095a0040c02c09041c130210340b0104003c00e280351425a80140d2180c03001e50b44040800c4c0886060070003440080c0702ca000d18a0104c0d01540100d94500c40b9034450382d8091315050207189240e0784480620a040b0310760030401100500d944250341071030b03000c00e00c40c1d800f00c4d0f0905146d50b55821503240c09e45020001d00c0054080842c22100d0161380307044003880c50011b610030350800008002c1d1180c0b02291005903502d001500c07142009404c03000c020f10800e9030811152480e401d0032a0100c4010101308006121411035a000c0c0f805a0000f034141c80a500154814404251010300c0c110001c4505030b0340b10005200c080005030007a048514542c07205010380c102545040e05214003500650030007007840c40e80d1306090205955600c03074901d0b0a004004d01107103039107660045c400184140d40048004801004010403203000018001e200f400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 594110998 1250 594109748 594109787
    0x10207060623180f060d08030a05100b0c07150306030501090c08150c03040f0201141602030d0e1c06150902040806060d02030a02101407140106140108040b190903 71
    0x110050300f000f0310110f441440740000407a120210700c0540110040d5a032100024001481090703141c1c80714030b62a007044541c0c0d0300c0241c444040100c4035441c0c49074000188030b02100c0a05080d503100d041d5407a01c109001c0c148800e000b0315880c10760349200760042c500941c3c1000080101c04120b00300f503080580c1c0b50050764403a10900d43d901810402050140388a10007001da46d134195101e541c0d50043c1000441c90a0703040111452400388240e0350400106504128603914070100113151060508009403224082c0a1004d038011400700c034bc4071164006a1740890740c90b8000e2442c01460118028105000f03007580340311805402190950940e8028000c2d41d4042080700c0d450f5590104000040c10702c0c1c035009401d5001101c001d4010700744903250740540c000178240820034181e001010506500840c1c01a11035826000301842019030a00c54880a03251f40c0703110b1001034240f2030001e0a10403000c1c00c010f2010298500049000302c006200b8214038015040602101c103c4d406c0042c0700d0407503030390140c0086 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 594112248 1250 594110998 594111059
    0xf18030309170a020604080a05070c0605030907091503020603040219120c0806190504030e13020403060f0c051909080615031605011d010e0310051e06030a140102070606 74
    0x24114803d43c1c2c4406080c2d03006056603901c82d1b40f078160680110700546d040c0a0300788000000074520100d0340000d4440d41d9100c035200d103401101c81c1d29002d6076510295085141050590420306072100602c00d40b43c054804a03500d85591003c190300303000420000c0d1054170f443c040402c030340d8010b00b007941c8040d02500b6410249500c0d00f40352a00c3d0f1400f51440034099100040741c252128164001c943c0c05806814404030100c000d034041444004482e4001c041b82d50b00140c00e0040080a1003441041e03662000c08008580302d82c1c02c0030f045885412140c210405904400302e444612501c1040007400400044da111428800d001d000d282000581d940d203c0d0049161803540031010104003021210305956504640c6068080d4225504030b1064560401c80c40e14001c020640342082907120840c2c0340c0e2000146468a50514084080c0000361002941800001c1c0042540d00140400a1541000400d40d60200480c00e03613009209810000f85251701b007580c001003000c03044006180d0104c0c1d5100d0681139 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 594113498 1250 594112248 594112283
    0xc1002040e0c18010804080702040501030c0f090b061b07080a0c030213020a0f180509090d030509031303021302040e13020112020705100b0307080307060e1605060d0f18030309 77
    0x86001e41c1c0d0030040fa044455960f035032a07610405a040c0c2060107401e00394a85481034020509842090300b00341c0340360140110410003485d64026010045c1601d03034041240e10115000195a4410503164410120507202ca4040a100911200009116a80895441d49001d00d0000d002140e148000c0c1c0c402c2d04140c40407100900350b4000c441c045c07000fa903100714501c84a000c0a42e0103100d02c48030600182603680c0c0205003501c41c00c40c0c0b5402402c140009000c180c110700b0340282940c0c1c1c02009020160800e000928031204901c0c90b501c250781d4102c0b40701008007502c4081c44024081c40c0e001c903580003c0c031024048040c0d0b45103c00340b0000d0003a80c0781c120000000c01d0b20800d0744110300c0700030050762002c5590000510075510070061940010195000355584440c4549076400c41942542d403ea030366080020150b0f41000304941e84041818958602440c0c0000103242d03000301c100d6014143d0300d03000404d203100c0d1280e20000085031506010a041d81c024140140144018042202e980380414550b400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 594114748 1250 594113498 594113521
    0x17060403030b04110901030e0c15120703060506120901020d09030c0204052202060c010f091a0603070e0f090106051e1e09040311100c0305040b0610021b060c1002040e 73
    0x842180025013203180244580c0110010002c440e0384003858041c0d1140d070380060b92020300c80c1a0751040c001ca40c0b5210443c00911036800755002d44003e003410710348041004a600d40c082650600080b04020340e007a5514920300f80e0183c4259002c58108501d420103000415030003040750201540240d60420059454003d88200000307461547d05150303800c81e4802d0700500d01079004203c0201110000f10701d00e82102d80f000c09842c5900400c076440c0a0346140700f0a8901195101a070141084006004840c501140308012420251104681c0314201c0c00041a07104250032480003420050103c5940741c1038101952242c041c075103074041c0300f03908980a032804161583e8600e0250f40f40102840c04c1030300c1c0c560702601c1420b010400e020441c0901d2040010400303040c03140d4046c641c280c2e20003183c5850185400343e900580240710074850190201d04802c040c0d800140052448030103800054494852000a041c034080c03c0301c440d40034410104255140c18440d0058030448011401c10304950719040b02c40070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 594115998 1250 594114748 594114761
    0x6040b19060b0f0a0203070501020301120b0a05010b0904050603210d180507171011130506182107230102070b0901050721021506010207060e090a020417060403030b04 73
    0x700b1060080c82012080d92084005003016845401102d00e08070035940c550f400e9810981c42100c44105014503107003030010f41e810069003e91326580402c47da46c1449020949802000c5801f800344d03a542c400952036490800008415100d405490f017440c44031030040c0c10f10b80d48000110f030f0459040c081182d650406d03203040c4d00615907003e0081c2402504007a07800c41c0c400b00302c0000c40468419500c0308550b55080d031207031180b901554040c0c02d03500c0c000500800036a41c1300c0da00ca540100c1040204903d80c5e04800d9004210200440c1d00d1b040d04c010320703e4206010207264507600c9050044010004150303090040c8050802c2c0059801c408800a00005a868850905c10703000350780301c200803d80581d8400e0000b0162688904141d0742d0000300c494600301035038040340b20107003d81d00100c0d000004020304107446034410b600b48000c00c003250400b2030050408484046060043c071511002ca556212207405440180a45150b6580c0c0c590785001113595a8000345c4099001c01c0c1b0b00b40255030706081c81c2c040e10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 594117248 1250 594115998 594116009
    0x614010909020c0102090a0b0901092c0702010b040c08040c080c06070b0a1506080910020309120f07020d1a060316051e040213170304030b010618030506040b1906 71
    0xc10400e16144181c40694032010011403155820002100e00e1307503907900c1c6030002e4a819213406d40c07190384010015104603100d4000c0704101071a00411380c0559418a001e200d035543c1c2040e070402e1500e034000c060740948a81540c00341d11504202054801c0d503880b400180c8107501401c00f0f031005c07554400120340c445107110a843d400001c2000100042409c05000c16000510001d00040355040072600c110340f06050341015000500c10020300210400420156410242c240021440c500700603a00b250b0703902c020b2070f41c0550300c8400300d081030348020b811055078441030b0007500c0c0401651080c6400d143c00007090b0360842258180700b000c1f9030503080008007411071a10704200c0ca014541400100960480c000d082c0c45255240310032480202c0d00c07180041d00401b4403620541080328101540600028015011165698000d10040020030250010103045078000d08080c01440381068140000c400070342c0001d0032500c502d50500081040007030325603202e2040c41d40d4034200301d42c22000e0341040d15021b10a2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 594118498 1250 594117248 594117257
    0x1b1e0102030f130b030f0f0f060a090906020906040e0115020a03020a0b060f15030108011802090a0c050d0903020705180709150306230a0b03130807141906061401 71
    0x4124603000b4a100404280c1d004000012020b40e44640c42e40b51a8402c88036004268400c2c8140000f800038111240d406c071640c46140e40843c904880841c66540d068030425401507110722000f070610400d80c4c110346510202404082e40c4588422031a000068284503c0d0f1600904c00b0305207208502c00b1813101c880550590103008600003d48411400e40c0f0301031f0840e90b00c8542200d60141a55071420110005125080a80d48943c501001c880c21a443e880d203144c030800b1450117690060b980c0c00130700b643c4018040342c00120400008402c403031500500c603819015503c0c0030140400e15800041c0700c02242c0d400c40b40d8040d03e16088444818419007540c840d4049001d141d000e0152500c900b50078181c4d450710b89000220290359521300854003da25800a4070a42c07022448001420042d00d00740142401003149451420440100003080c000b544c0702811002001c2104420482a5a042e590f031210b140200d6101100036070a1074000151000c08a907142e01d40400040c41c0d041c3c128440d007040c5c505849 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 594119748 1250 594118498 594118507
    0x801081b040b150309071401020f1e0102040308040e04120504080d0e033a0306030c0605220902120f0c04030f1b0b040602010e1606050d06081b1e010203 67
    0x18070018081000752a980403c0c41c01480741d0741080302003c0c5105a55000c0203040c1e17a40b8000c1c59a940d0740004003900e0440d00a05082c10580a000a500440c94442c290f0400c0c0c804000340128020f005a40004000300e2001800044034403084552600941c01490300c000029544002038030f2a11481c401d22159030803100651729a9406545200e010740006020f5450312080312034440016100d03105482014240b8110843c6d10081046e10040d1010042c2010042d917811629802d400da001032042d00100107001400e00c8030601041c10070b40d01c414541000c05945900c0c1c002038000303500b045c50400c54402002001414814048064a01a58226000324602400d580301d544600924800564565083c4114005400c41d01c03040d4600511048207015101c50030b042d070003400c1d03a00d42e411100d00c030361144441320310524000303030100d04442550a185648080000701a8054001d9512408107402104101c6154142404400740c02d03020465007082e41c01e13002d02d024507007605140ca115005038014003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 594120998 1250 594119748 594119803
    0x50604140c1509010c0b0a0906050c07030e150c06041109060a0e070e1f0c02090a0207230109050d03020406030e0a050601030204020c0307050a120305070c0f0303230a020a080108 78
    0x1020000f00c10700d814580c0c1d01d180d8450101c2128260b07890030044e070f0f030781d129402445003501c01c00b90070142400009240c0b07455520010002001d4404040c4951825807404039005c110320200c0c1c1c1d4440d20141074564510307050900c21000c040300250300c0d02a44029000481c02c1ca01400c0c00001d0703030807603140c50920341c540140c103c402c440c144042030340103012002070307081034400055550558102692840c10b001814410b0248000010f000480100d005001c4d502c000b40c44101c02d4011154202240d80b4850028480580074004800024200d40100c005880c0c2040c3e250b0000d109440c6141c800340300001144540d203681d000181d0300544035030040c0300180010700d89600102803c07801141124240346464540604180c03d8003412501b07075030113820400700d030b03500760017210b9201311141894407029040342c40b0880c0c4444101c2d030080030150b480316091030760f00700c3d94183d00c0310b140c004010440900d0412042c9000358000503c40003c50310a8000103002000040c508445842c0318200ca50304c44001c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 594122248 1250 594120998 594121039
    0x507050616050408070803090102012f030c09040912080714030c0a020a080a03090b010b0c0307060c0306091406030f030c19020d20040c140f0706090b0103050604140c 73
    0x84180c030003080b008000004404004114400c09002c1d40806113076960041c200280c00c403195010080812211103031059840942c07003041c9440c801c0180d240300c0c1d0b039542e250340042c542d201e080c0c501039120f440c3c40882c200b401240a6038000228940d11600c42c80e440701441601c0038001c40071000040c44007000001d0036005280f0203003410000d0350048039200d991035903801249400040c3e40d000042c0d44c40b8950002c2c0400854045e00400d0460400c07032402141c041440d44078401c039035000d004c940c0c0701c1079550340345446a4840001021100303801c01200d24010950b820304041a552944244103034010481080008801c4070040340c2001c00420582c0742c0281c0303040b448601d903002031b40e001d510242420041007500000100d00d400604081c4130500010041100305c84c2405c03954820442c0c0a20700030070450700c4004680501d00e20303031009034681c444c500d020005800907030001440d0b4403034840000304001c000115036001d5031281c4051860812a00304007950344420b04290b030b900040030340c10051000f500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 594123498 1250 594122248 594122281
    0x2505010b0301020c07140a0308071412160303200a0201060e0a1517070b030c04031a04080405060c0f07030b070f1b02010c1e080903010b09010b070b07090e0705040f0605070506 77
    0x3d170001c7c155039901e84520301581c0026000380c441c2c0c100d40109080c0941c1c1489400f1406207007025480c14036080c02c950b01c0401d82096002401d05a035400c6c1300d02159407001c440c0c500841d090003407a030b560003034500c000e020308134a01c5501201e19140e8042541d0710003600070607208503003071140710074854a4070b15180001c0040c3c0c003e44005001d44100032540d8201d0200642c030941c00d2143d442d540781e1940c6082012115001c04620006074000140400540344000b00c1e81116400c48850f91034000400c3c00300d0402ca6001101a0760344110980001080203203500c00d40b04032603c4d214260200106041561340e40c0a15000d111240c406551110041d03010340e80070a03d45001e8542c0f1907030002c07400c1c01e10890400c0e50406407030144011a2024181ca030900440c0030a00d42a80c480c509945059030403102405150300080c50880300b000010b10761881012501c0c0107004081744200107041031040907085034002d00660420907544ca6000c00c40314010812502e42c240d000700204003690324102c00041e100301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 594124748 1250 594123498 594123539
    0xb0a05150328050411090415050907090501030f02010305010b0a05092115180d0206190b030303070809120f18010e100504090609061511032505010b0301020c07 70
    0x100900d800304401d20302082c0c1a400580000c0041e1504090924500d0513443c002e66500c41e441d0082041b0001e0104044c1081903e0149008207064565421550030201a41c0000f0412890310380004140801c007001ca1242c03034002e8030204180e98030b40000c0d03540e0344560241440400e20800015800303003880d81442c0440840d6800742e425100b030302d540550400510591106001c4141c009104000400f407402d05094003030600203003045000480003a4960800405010504001c4e0b110078a480205400011034514000d0540303503a4a030008014100d00703c26500c4642520501c5d4000c038030195110b04540c400400c0015250401054068444500d0520307251203041143d41c0011403803a0f21204040420840c858844980391030078841901c04440300c941c0b15441d030a0518100300180441c00900e00448030b1203141c034500c0309a98541080c03451003170303004642c980909404070108401c528200c07821000e200b0381c001d000c0c10f6070344000c040c01c2c1d0082000c00c2181e40c001c0d0340c0401c121458450351114803a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 594125998 1250 594124748 594124771
    0x2130312050d0f0c02160f0b031807060507140604080d020d06080105090d170c0406140c1617060601121e05040f0519080a0e030102090a14040b0a051503 67
    0x28440070000064030180c00c0c0b1a144182c840c1d44c0c00444ca40c061040c150070f1a03004c1c0948450310310b02180e1100e04142c5101e030784035088001020444405101707503403201100840040756806c540d2840010519031103084203858894039111044280d201c007044950159822104035400c00d005401c20350003e40c440360090b810103541c2d0790b00090307000e028005d1501c43c002500181101c074042190241c450144000034a100c104a0b1042040c80000310056505a8800f80b400701c2c0102103804081c80140b00f81d4428120910550348200c1d03d0301c80c01184c00c0182c0f400c0e842142204001054255a61a029100c190200d000401c412000c108140d0042e000020f04010b0005a100c1c0140510101c810a8a05561034441e0244100600000b00110041d0b000b42d0340e490710b82d68820b911100514094001000204804e03400c0200440d5002d4041d80d8203002d00400000e05203175282040421000c44011060066042541e108124035151201c1c0c01103070005045140c01058000c0140c0e01c681c0014820f00468 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 594127248 1250 594125998 594126007
    0x180612010b0307240c03020c040c020307020a030b01050415030807030c0812090a0309060f02060103081e0f07020f0102070602030927100f050d050a02060a020a0f0c0608010b03060d1b05121b040213031205 89
    0x1070340d8001e1463f0080d40100842081075041400740815980086220303101d09074100c00400000740a0790440d545540c00d441c2c200405d16041c601003a0a00c90360325a05541d02c8010148019040c0c00b041860700f562107600c500003010340d150020745100a0b001d00100246c0c020800400226000c0e00040010201c80700c100440c1c130403801000201900547c48100451802007040f00860400c094110b10303400c001d000070840d103483c00788025a00d214100680740550640303041c0d032034520303150855026041043c1d5260805840e006031003080021003440788020b2045044000140c1d402c00160300018150080050442c90440750244481d507840a0141c508510905041c0c50102c1d0240520b0703022030b8400c4070140b401500e0144000c210300030603001102165170402c24400e40d50b0b90540c0c96904140c2c1301c141d25140215a00a4201403040707980945d400215620700c0760510326010800d1082103d00c01083d400c000100c5043c00228068400c0c1d4600010a501c5d050010900c8400c2c0c8510b0101c05d407805030f290 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 594128498 1250 594127248 594127253
    0x240408010c020a02040e0601052112040303172505030c131706070e0607020405090f01021804271401020d06090218180612010b0307240c03020c040c020307 68
    0x3140d07140801d490050304080703e280114070b018024246910004001445c5c10350402c030005224140d10741c007190068024a0070002d03100401c0c40200524190380c0c210320340700c940d2418098103241ca015008585080c0040c009200d140d0010509154101403c1c0510943c000300340003a603465102500c0407004107030510161085a480c0303403000d00038001e11a040c429006026150b10700c2d00001406600908c28a50040c13071054a801c1c095800d490340481d008100e944900e408542040c2c501038507144a9400003610300ca4410000c0390800d4000d07004d4070700b080024092808600d520843c00e103d01d56a1200300c0105020880c1e4090034107850908000051070300c0c4200d411001124501d50150500640108101150aa803800301101e00501541c059161102800c000d41108c0300c000d0010348a41001c100503404541c09500c18615140040d0407680840d1700d801018407140107200081400c80300b80c040c2203016a00c94600c2d040da180c0e05400403c501310408040101403c0d40c40810801c5100901c4880003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 594129748 1250 594128498 594128501
    0x1517010c0f0f0e031209010207080c030a060207080d050c03091509060f1008060f1006260c0d02030c0702040c1d100c0204050708090601050a051c0206040b070c080d0c0224040801 78
    0x420245e01741c54241c2e100111400039050103225484026141c00a80c4101a41e0304c000c101000810343c011801651070390729107001c183c54000c1c6124002c0c0d403461700081141c40d125807002540581101c0003158116207046550001019080b00d0603d065006603003c228003040e082e40d12a04058500014100f16440c4c02200d89002c0c801c517180c5501c08580070a0104480c1d802040034043e000514000e2200001c0d01c40040341542110001101c1c6040312000070313050501030042d6a50110303181810355036800d01c0f131440007082c2c22a21042e4415440e11a0f6800f0390740c007500070741c0802a11000b01d200081c24803010020351809580c10f032428030441c0f0800500681e070f10310400d441040f40340c65101c241e0400f03031b0841d460100140c1140e40a044818030a10180c0d541b26080c8100b00000c0e00e01e20540303035070fa01c04106180203660290384881c030041039600400c81f8905004050300c0d001c004440010201c02001c8032140f54080d4069080b1032003607400c098034070300c8000180d200041c200341c0e540740030f6850800070b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 594130998 1250 594129748 594129763
    0x9130218100c03091508060d0804090606030e010c17040f23030309120a0c1e05030a17071701050402030601030b12010e06010509010f060c0609061517010c0f0f0e03 72
    0x1030001d01c1d403102c240201a003004100f800f800821600c903541060042003e040004007030311580c881d06000f50f8580800600b6007c0358003030441c01e10140400d641c0c4000c064080c003520070190845500b0618407003801407060001c3c140708040e02e9290702c082e460303031307100c691000c0302e554001d4441d801040d110000360040483c42c8220203032220000d50703907480e060710494100001c8120114a0210411000221a9012001e05481500300f80c0009410200301d05919103070f08101e50041850002240005e225904840600c01002c02c4259240455542120884440d50250300103150450410700501550801d036000d1544407206060000f074403081300c4001501c1e80c100c402036011580d192070b8038406088050095070f00524055134003c1c02c40d410700d150b00b0341000305d40c0030350000c2101c881c083c4014009a81c11001d0502d42040f81044801d0b0181040e144040145c01105211089103807403034820841446000e103064440d5458000c018031040d0211040740d0401e240310108210fa82c203d0003d40e80922140c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 594132248 1250 594130998 594131029
    0xc240c010c080a1508120d060302030f0d11070503070306020306030c1f0320070210020304032907021b10050903030f03091603030f0e040f0509010b1509130218 70
    0x1d00b285407081c92401070b1381440c4a20380399500448001c1007060340001d440300c00400c0d0074a03141d44a08103201507a00034040c0b5840039505200b400d2001c15246000314030f2008404040e500c8580c6540c5200501e551180c1c60700c00c0b55050341c8045001c2000c61b4240d409035810860003420382d2440c040c1800000c4034008240c8581c403401503541140c1b140c0315010f114554035000c14022211488032000c4001e84540900303e000380c040d00318407402212091080c81240c0107140c1c00703180e09400c072031060142030491044401c6c88800c0c46d080404039145500000d400c0c0d040001d100540e4101502c40ca0070f014402c040c54000790103109040c004407401d43d80900141100c24403010203c4d0b2685001310100c1e1904d026689040c0c0303080101003040c80400e038025400d040050640c10109a0488101d02003002003030b107406000310712440d1000f0f001c1107107030641111031504411552109803100686191000d441940c3d4002d42c03100c0096100314085150703801800d02d04290509000b000c40c0f901c27010800784816070401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 594133498 1250 594132248 594132257
    0x3031409040f0c08130f11010c05030d090303050f06130b0a1220060c07060302071a040b1006050f090d0203070509090303010609080102091c0212070609170c240c010c 73
    0x4010580c807060136070344405050810712000c0d1140d2208444001070b07981c0901102c1c002c2c044030480da4001d000034220680d020302200d54030441c49440b00010502194210000b03400e0901041000c400b6114180c060b040040c001c03407012002d008450700620f03000e5104c60b00450034035000074a2400882107620505e00500300201031303000803140194050451051035100b400d06001201034498005548005e40e140c509005a55991500301001846039142d00e64019006240401040103e4003580f140180040804241941d8a9040a4036103002e40d28000700746203424050780b02141391880d8004903090028050f202419190350220f841c0990844280c0c8040d44008010400a071b8040404802450102d008506000c41d0b100080d4186040311848160307055100c0455040d9030f61031071400501e141100c00c031812181d80b5038001e0507010341031040340f03419500e42c90508078804005c01c0120204400800e4000e41c100c6038020440c10480342d040c05414030380c0a01140982c50402d2092103000728040e01d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 594134748 1250 594133498 594133511
    0x901020c070806011406130b070804060305071e1407050106080c1003020406020a0602071e060507030c170601050a05040e010e040c080c0102060c0f13030b1f06080103031409040f 78
    0x20218a0058140d120b4106940900c00401c44481510051109028110f421750355401c0c001590300c1140610740c0103010b8241c00040d1407410041c07404010800c9a585803020b100c00d6540707680503a2400c00c881c4e0031140010704554504021842039505000c0346072914002c50501113551134580c01c4803081e40007107160717621519803041a440e009620b550242c4c1c041c07806514007418a0300080d240d6080c0d180003000d07142c0100c0e504082020050701c041050781c200a2104182e101c50403c100508002c0d6003406c041391074900c03010081c91040c024000a8204e68920012503110f8900455503640441d081c1000c10030f0511001c50841400010203000317110380081e00d09142054200244101195400070105520105e405043d81c0d030086100d40c0c0c401c80c401324168840c180d0b0002c1c851584220300740c0d500310b00d04001d00801046014141107015095540c1c0640d092030050311034580c82c2d21a8040c0c10042882c42004000080c8030718550f00b0b0216a0844060500c00310074081340a8034234091090345520b40311007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 594135998 1250 594134748 594134767
    0x1302071b0e1b04090b130e060105090604270215040906030c0e07021c020708151915031b0e07230f0409090515040b0103050d051809040218090102 64
    0x341d454224a800610903500501003101c038010707126920031001c0f596292100008a943c0c1c0c1d0303148540c04004000c040c485010030041c03250700c51000b4050305104d0554403000c00e03a141890f21601003e00f03c401802c4800340351a6007800c09400058104980c03000845642000c000704490143c4014880710030041089421450401c2102e080c40c0c0020890700c50940802c6a2075500007800d81d0b0350244409d807128840002d0030201d0030611160006050707403107041d5a001e00007005103460352003500914035000c80340b00010f410100ba1800301002d024102c01c105010b001007080044c90b03024404160030b146005580c1c810b89144041001c544110104510300007110000002c1c030f40c0c0b03400b04a01d50025518101d44203032144401d008602076005400da88000301c008200c02004005074054209a201c0428a094034010301005400d002c00c48d843d0150452240005028005491458260b00c0034455070200c6070f018070100110041c420703a40700a850f103260700d150082811481c050101c000015035281e5510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 594137248 1250 594135998 594136019
    0x70903200613081506010906080702070b030c0a1b0317150409061a03010b1f0309060203010902040f08030708042304091103070f08030a031d01020c01060303030b061303021302071b 79
    0x1300a1103060300c00038200820350303a100b0701e0001942d00504084615880380c0174201c0c0307400c45c0e035041a141c034100002408003104410000d442d004c05250f0701c2e40001400d0180d000246040a0f00003404a0b041203100c3c28188580d5401d00e60100700d44101c800f0304144000000c05840c20b0150650340160341e0412859100e130a8029000380c90016402032003003008001c08070311001160300194000c54ac0f02840d1184261003a0415400740f90401400e40d217950310f40441034025405031050a9004040071400507001c0310110548403110381250300c0608181c0b400355980c0e5041090044605100f00c1d01c941e10317400e40e9851003040542760140001c160340c031001206241c0b90a51a070041c2d5002d0005400c01c03c21540004102c91510601c0d260105208003850a001250085064212060350000c241031002203415400f29084a001386e0f024040040c0500a00c10a48030310b82c4155070850004005002508050040c94800050040c0c0140b400720192141d5070400b482ca01c00341700042c1400420000c04000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 594138498 1250 594137248 594137263
    0xe2110020a050a031103060310240f0e100b04090203040201030b12060709170c061305030601270b130e030418050114030309280e07020102190807090320061308 70
    0x381c01091b4590b0510342c001a80e90175400300c0e44c41d0300301d4545010421440c00c018070840d0b500c10240c1d800c00c1968885c9040071401450b4082c61545035031800016441590282104084400c2c072107015281c6800c21030228040c0d48014403c0c0d041c940c48000002a40d2600000d2050b0300d281c4001802e0075040914006025518036841460944100040240241e03008607200000071400c584490fa1010743c43c9010740340f04881ea0000c1c1d454003465000140203c10000000045d03040854000d140da001504c800c1d01329681200c01540003c01111014032030075a5520100940a011040728103150b6250f03509240007011909011602c3e4542e401041072079071541d81001e030440110080c6041c104100e0100b01c042581c15890034010180d459401d228002a0503000b02400030f10313070310305450303d800c14029002c0d520a021031540c03926a6100c2c0100c1910507038030769000e810556a0709490500d142c55482030101d030120f03e01c0540020141d213101e659141001004010181c0780b000b50502d14003004d442c00d1804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 594139748 1250 594138498 594138521
    0x4050702010615030b04140705030a050a020304031b0c0332010501050607021c0b0403170f0702100e2b090b0f0f070302010912110c010e2110020a050a03 67
    0x1400400c2c0038000c00040c0c841220440e074500004d0503081e0000140144c80d8a6003000d180119200600023255482070045104440d07000e418081c41c0c0380e544030141284400c50700074000901080c20102e20075000141450f5842c000c83c516458642c403507c1c8c00320312540d0500c03440a01a040e04010000e0707240007125424203508171b40208425850100890214411050005e105010110280c4d0b0480d58404000f0001500a03074482c84a00d05031030094400c0c514011510a10480c04002540d1020403024a610078840381e40608403000722464082c02405a00d40c10380468022400c400c05445140c5499010b01c00e0030754070302a10f4024591000d0942e42c0660002c40d61100100b02c1110000c4c031500c02c1f039588031544403560b035851400e810100e0042c040400000d20a03540d0b550166481c1d90700110304459101e031201501d130620000130040d182101225000c942010501c0c0c460f6442031050554680c0c07007403041c01a55041c04107981707114201c0c0e0203401803c000c59400314100c0619070381846074185465 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 594140998 1250 594139748 594139751
    0x80c0127060e0d060c02010f05012102130b030a1a0c03090604110d05240108010e0c0d02010c05030403060204030c0501050306130c022e180816170d0203060405070201 73
    0x9104030311000c040040c018102440380e456803103a883c2d1903520342040c00c0760b0010310802030005ca141d0028040d00519000b00c03007081c204800441d50b03401c90202c40500d220722955101004001d079082c005004a070501401841d940c1e0308000013030b518103010800303403035200340001540310560364100307090b01030302620b01d4900303907001c3c0100102903c0000700550051340010b0560a811451000214841026030000b80707640a0f600e1242ea08401c014141c014070760350180038002680e212140d0034202c608040e5205a01da0084241c0c094038101078080510960061600d44540d01603071b102c240c0b0b158459442110503903030005040040c0082d101d40003014101c2440c00ca407841c1441070000302c400c003861040042ca1641c1c0c9103e41c10740b03402085181c0e011940001c290b46410010020702d0300715880604400c00582c10008000404407516405c4056164811510340c240b2103046c010646c1070240b098112000c5079a030311849d1180c06800060300014030100d1001d80e4038a810300a101c151503014204a040d607 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 594142248 1250 594140998 594141047
    0x2010f0320210435040602030a0e0f011b050f0706050d0e0c0a0603020a11070b1b03030f0c07081c02030105010f08040210050f04030618290a0c030e07080c01 69
    0x2d9121429020305000044240c25107030071303180e02c03805804800110400305201c0000d000810135004009001c0c1d100341a1200190440104103111369141c0484041d80003424540781e0060088000510503852030040044400d44800d0602803450500b0b180c000001003100811160407e60f01401440138104100c0b0223020240312134000f00705096154040d8109041d004035880341d995100b4604000d200790458211818169030721488440c0d68000402541107000401190340485000001c51740110038814104c0c41075911100c112032a03400514046450020401c500c2d2481100400c085070b90b4240301100503a070f035241c20300141505820f0310040062109410030000981c0d155030b8036801e4603071103040c92503030f480d400c007840006882680c0008285d2403610300010300804420b914038011503ca15080c500d1801d40801741000600f95084009003041a01c000908c0c1803096004a40e54840c2e604000c2100c5109488103400c0c00c4050304880510f504c1400d0502156078080105452846a01094001c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 594143498 1250 594142248 594142253
    0x8070803040b013002091905010b0301090f020c0c040b01051c06140d030804020108060f1309030905090115030b0f1c030e060c0a060b0a03020d05060108120a0203030402010f03202104 80
    0x40c0130340080d020b4880d09901d4002071049803941c01016800000840800842d03848a10311221134200303008000d0360328600b49815854407464070032111100e03803401c0141150200d100401001c0c0240700720043c10072505210841c814410203110311584013f800c40411303003c1c140001090b4a1024810700e0344941c0902c0601d001207900409800c0e04a0340a00e04030000d0354403200420301d1034041800b010b0300a40d4403940f11a02201951150500354840d648411000786d85500304180b901e000c1c0213101c4810b0460b40e81601050095020212420b0301802c404004400003001a0b1032030010821640241518620700c400c0503488100307524114811640c0600b000600e802c1103a8540c0c0b0181c005280c0c0d41c1d141c2c12428161303680c80d9075a00071030b4001c0c03603416643c9051426940781d0000303204400c43c1303100d13621039181c0700c052070010344501c0c00c4690700950541d9140e40046541c40d100c02c99050a00d9528204d1001403c02400b8070f02c41980e144d40e006644502000d0344c2c010810501c0a04030510f040002403100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 594144748 1250 594143498 594143579
    0x804061803050702040b0a080d020a0b01090605030d081e04080c0601050603130b0910020c101524030608030c0c0a0504380612041a0108061308070803040b01 69
    0xc140c4c0560380080c070f24020101040342c0101a03000b181c2ea62017140c0c03007000216800100382c500c081c0b00d02e00700109030f60fa5180b5103060b155140201903154106030f031040002880740720981e038406402d40c82007134001c0068ae042d40c1106c0080e50251910b1100064000c100c850403c44540140030549a0919526021980341c19508207200024414803603440030521a2404000c02c000480c1d0108085559030350400c04261b031607110150248106041c8440c494815580d684500101c5040040120084000d1200396401c1045445910306144d51070303501040303e4408001030710044000c01e008200c0c40840b4800c210f10100940d02a5203c0d5041c20f003c2c07d00c144441000401011401906c5e100c2c1c15140085100d10014002a254206002182522800181d900543e0051740510201001c1c80c4500c20200c9041809000e48040c503480a00444c80401494100100c0c1500454903607040000036a1101d900b03a0051300c0a480002d1003030014441510025941c0e2801d80c000741c40002540caa000c101207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 594145998 1250 594144748 594144757
    0x809060109020a03020d020409020903060f06152206030515090603120a0210050907030204050a090c14010c15020306040501060512060d08070b1e060303090f060c011b080406180305 79
    0x30790090300800c0d034000380c50103501590810055101c081d506c0e6503d5501040003504944401440391103000045822102e594410703600946020f010383c030341501d055038261115880b1121161403244800b40c448882d00c80031902c90040d04044e503012505046c09802940032855103280c042c411134414041c004550380c00a0404480c25550041684400c00301206904103054051300500860030007003002401800070800c0e0041e203200715410012500c403243e50317108603255924014240c004018060000120302901006d00c204140b40280f03504c01e071135859900010844e9045818503401206002d03d914242c007590b07015003624903120b820041d5400103407240341009044039020f04034031401e440074400b40c1011111410f400110840103403d1003200402c14146034810705400324040004503c031442d01200710360040500030407200030200c1c4002080042d500003000482e02e5980c0d1200d2071009105043c0d8614403180c0f81c0c80e0540d0341d14013400c1c400d05540d0b240b508030b080c000b020305c0340d100029044020341d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 594147248 1250 594145998 594146009
    0x1503010e1f0c0e060a0c0510050408031b21010e011a07120c12050a1d061b0c030a050609060604140f070201110c070501110105070504030b090304030218060301050708090601 76
    0x20460b030902e070340180c888400c0c0749041500100001041e01819400004404800d0300c107000b2240c042c46042d061404659054074000c145400c1000806c240d5681e04210a41c0c806c0741130316462402403405240d0404c803290b5082012121481e400410101d180c551003070340180b10080d00181d4419980c1044a50340c801c8580041200c2c4c00044095456442880c1104001e03a00040300f411000140c58041d0140d0401c00032500001c0103000348407104014a80900e00944002d0051801c100403108002c0c0c00800803141c0c00240e01c1540d10500d1681d9040084036000750191001d13180310304210690300d04000000706114003079401c0c03a07455801240070002c81540008010047e5065460b040803c030302600c2000c0f6000147d6a009c0703128108888086102d008480090301e8210314030002c4a0b9041c00c2c1c450071614003020904c24030081003c58030700c000342a40052504240e0f23290036141d6001403001402941d100180030240400c118550400348112504074040382480d410b10f141c20329946565200c140140c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 594148498 1250 594147248 594147251
    0xb06090c0307110111040f0314010e0c13090c030c03021311030f180d0203130906030809040c1707031e0b2803061b0216080703110604030b1503010e1f 66
    0x2161070f110001c1d030090601009440d50300741d03902d0355036040405000041c00186d60a1032601ca0424203a0014444c0601e5040d000000d012644046000c010088150000c2030074240d444101070000079480da41e9181c00395100d01403012030380b801c42c01032209810004401c0c0c00c001f80b51070851180c42200009032a84581c104403940a40d580e2100080c155105104d0303564220310411001c61200d0f5000305c040e2808181000000c0107484e40e0720700ca0310540340a484080d02c140c0c0104400d00ca907040075040b6400305403460401101484058004820031201112030700700103a0b6400d402803540d411104503410080d204401400000c510b00b000030065036140c210703145c0100b4280104002100c050340385600640d00b200d400c00c804410030994000c115840252980180200d0002104503500e0103406401c0e10b207008004c240060842c0d81d1109002100307000c241d0300240521000000414011841e84a50707694403174400c09124000615007555482c0c0d1052141d41c016007107049403003480f000751004642c0403c20 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 594149748 1250 594148498 594148517
    0x10c0f091401091e05010813030815010306230a0b09030c040519090605010e070503040507181e0f0f020f0a0c060b030106030302030a020f06010f030303020c0f070906030b06090c0307 80
    0x6071402d060644c80611002440506643c10b550104042000c0710801e803250900790342c44240e403400c0c4201e5200c1c000c001c40c000501103403051303000c1000305010400c10f050010b005511135040310351500f24980140c001d1300d10610414401d0810703014400041107154410703410700012400103904c41d02030032003184c061a699000503080c490500c0602d0642c0f1035480007081848654209080540310034003591401101410100b45028850340c00c5901c40c42d0050701070301203142040d005202c66041c009494540a88442c0c0c0e039420551140e103404492001e550380000c009d5109940c08090301c101c400d030400d2261040c80094030126040302107561600492030501c8502005145c8080281607421000d6055803070b01e0070100030960008010000c5144035001c81c0c0c03404002c10041c55580ca801d010b8094502843c803010400a030003500a050f00b10103100c2518100c0a54140103864840c0301e07030250403100d444413020018004030043e200d40244040d03451030210300d4a0320308048244400b40010041180140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 594150998 1250 594149748 594149789
    0x40b04060504060834171204170c0102012a2003041802041202010e060c0616030b0103050f062b08251a0c120109020705010c0f09 57
    0x240400d01402000700100001510307801c07100d594907005410305164800040318014110b01c51201310510240c0d08a002002608201c51903010549556003000381780b1405607280c14044410004d04007801c40c45100c18009010001060300d448014110641903901d400040c810381400441d40322141c2c021000109030002120200b11140d0102c82c01100754883d2021f100d25180c1f001000904c201c03107000341a0900b074101100c60004074852441000c528a40ca44201c40040d4082c1c40c40a00c03003000100710b142031041c544419418420102c404030f03104c91120481403031303054141c40780726000242840c0410032031505141102d80365001a00480c480e40125501d00c000003e2008101d061100380040c0c1c00121103545040c2961b508070450024406480042410310310000445080301d003a003000d600707004102e00c041102048140500700b141c04003010810280c03c0301098445038002d00d10f041c0e0050341e0b00301d00d05025084480b620041020004920500011150302c490302d031058580c520544019841d20030f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 594152248 1250 594150998 594151001
    0x90506011809060603050f1e22030c050723090a060f0b0a0e0d11010e0f0d0302030301080d090e071b1218141018050a0806092a040b04 59
    0x1005108101818214042400700320740d0031400c212000e94401b4040c5454090b00301c00343d032408403058601c10400c034005c0d0813506030f40007070250070981c828844c040e45010014070010a43c500c3c1000d801240f0419400b40c00c10500300301940042c2444d17034000307129415034440c1c19814101007034440d01c5090750740041820034903650301400045c1b007422400700d041c1d0303611010481329030040c1d01c0e8100807505610482c03da1b0304007400407030100d9078000700102000e581d0b2801521202c0400044682290001d10340300343c0354440c8d811500748030380a0340065489615010200789000c1e072310710f481410420316010410030f03c02c01c4001103070410703414141800b045002c08030700c0304420300ba0f41015058819078500410141d4011006100743c0041070b0345510941c4d2a204000c42450307440d00e803150069020381800181e03d104080e5404c0d03611050000c698203599500020b07031600083e400c6801c3c540c02c60f40c14001c40850400840e1204d414005208020402544a8a18500c050110140516200c1c0100091039545 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 594153498 1250 594152248 594152267
    0x1103090d1709030a0311120a0c0f0c2c090a030206040803132003010f06050a180b0406090203060907020a0c030602030702010b03120c10202a030d060b0c0709050601 72
    0x790807100c06013124100244190201c09420703095000d0701142c00840020902152481d04550320740c1504031085668450000000341403d44603682c1045c030110f90380c40d80f269407800170400140210f0340c4890301c8440c03ca0039070016003d00f0040d8442d480703020002340c0120b2815030203a00030302c0c0c40da12950f91522240c2d24181030708000b4081f1840b050043c001c2c4003988804140d4134401e42c001c01c543e21001d8013a000300c807500d004250744130062034000c115403420744121208200c000c0c00040340c000d100e0004a01a03074102d0704041503040c0c000c0108000b50070508176007680b02c1d1052004100c01031554a030166030240c6800050040d036000800540039500135081224140070242c00c0350300329086a44c41c85c0b201d8028152148140c002d0038000d91500180740100300c01d070052a64011a0b1745200c80d1980210b51200040300c0c0900c3c402c40345540d03100d41040005104480d9080656a201000c0051008076019500f10001407001403092003800c190000741003003611070700c0c0700024550300e9110068401291 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 594154748 1250 594153498 594153517
    0x14130605030603281103010e10021308030f03060411210a020c0f0c030105090106061d010905190f0e0f070f1119050714060a0f0507080d0c1103090d17 66
    0x8201184c00e90801007480803042e00c0c000c040c40a80c0c410554109401d8410481085d6a2544542900100c080b225401444644407641010441035134a261460440e0001e01315080015404001c0006c00d0520b400354401c40040d00e03200602e803030300820541c5020300c0408207240001d12040006804000968100d1700703580c958508503040540d1200795255a40140d440d110300039420b100110308814030500405003621801d46408103d484400c44240b6110100c0410301e0410102d00750005560301c448041a500b2604c041142d0030380c40c100301800d036176040d05901c0a07142016490070060702d00c54264690b40c0102c1c29282401151112000031140c2120301c0180914074016190305c0391590300d10320344266000e8401d50039100c40941d10b07000c1007400b0891540e444e4011703034100101000144a1098600400018180f950502d04a500d800c1600d41185194601450b40c454120407080e80020101c425081713000003c5160400c080c012400f400e609030307401030400c03190400e07070100d254828055809221 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 594155998 1250 594154748 594154783
    0x6060b070b070f091d1003120903144b0a03080a06030c0302010809030c06040309172d011e0516080c0703111606030c14130605030603 59
    0x9000741001d01c8944810707602540400d55842000c611540501e001008031040b1500401d1000c8082408011580b00200b80b43c04c030b5155004003000281d0061040d4005010681c0c81a0f8403e05601e04041c0451003558a10620f520642d00150154038289442180922607000382c4480d0001c0c44421b80e0580c12913404140320059090064030b88000069180320060280c2c0e220411a2100d040d102c0442d0590700015040b212010018030244d4052040590000585c8080728900700102c03031074034100310040c0c804038001407011104201420005004000010920001d00194824034404c84211400789440c0185008018404000340c0000e43c000c0141c40d40502d1400c1030112034055003001803104503600d40c0c443d4000404512903603c03805603644184000040d8510b84502ca8400390350516504100c00d0f0340380329001c1500000311501320110010110758030b01051661106202402404080700b111204880c1800051840f0708407000510407200c0b141030456a0740c4506001c281004119000c0d8240e10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 594157248 1250 594155998 594156007
    0x1060e0d0204141b04081b0109030606140108160f11030c0a0b090613150203042108040c06050a0c170909091b01050a021e0c030a0302010501050a090b180406060b 71
    0x503411081c3c280b02c1c5240902007100c1c1000030128071110b01660150324060751110703414510b40035989103807070910a014105200215582c1d03540303005032402c43e000441840b080516000d041d50b0003e1009800c10424104000c002114210091004c28841550410044140e1540700112818030417640f280c3d014a05031412000c007820f00010ba040c040e9942c240900c0b1740760000f5103c1e074003130000b030520550001e164180b400b2420382e0302d0080d4102401c1903070b0a201c5003d85141c02c02c40000703c41e040034855200c8000354549800e0840038072031030b41e015030300340030003084044034447d4000030003146264000d400c000300a4054408621034098010066000500700c02402901c0000040300b002a800c205840502146400011615406450010720141e486500c2c4029045259007260700d991501c042160341071106035000900d45101c222040c0c000d40d650b03900600c2141803046144001c0d142d00d21080c0007490101c00421440c60390101c01e204a44c201c030b000300701003180d1904050020135801500a0b2207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 594158498 1250 594157248 594157271
    0x9031c1706040608030c0f240f0603070e180609010b01090b0f0c0a15110414061e0f0901080606040303020a2003100c03050f060307050105071103030c010516020102070b01060e0d0204 80
    0xb41d1fa10755104401601c10300340724448021074106400240641107164a1140c1c0700c8080d038400300c40700030b040251b0500a403080490704628010405118550651121a20100a032445802d040010b0008200c60341851802c001c0d40e6046050301702200c41c42128658fd40350b5140c4860124040e401c04900a0b005070001c02c401c0c4040340200c403258035002002040016900310503244a4400d5105800886603d0343c0003165901d80000900713000080700d640000c0c8207a8a62400ca510350151002100000c3d0100b15846c2079640101c07001d078807034800e99003030b841e2500f035071800380d915090b40c0c1c80140741c5020b40009841010091000d42440030000d8200d80d090300e12990380402510403c070101c0c4c0081d00d071000007401c3c0508a69001d0007000c0c0035020748bd5250418004441903403015005840e01c010818000d40345440800040801d013801c02d0002803681000031440d119010030820f04021680140551800725032a10740040c1140c43c2070800e00c201000ca1804a40352501d610000317540545080f090101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 594159748 1250 594158498 594158503
    0xf13170a0c05150619050922020d140c12030702060a110a030923010e0105090607080310170a0503030a1e020720010f02030906030c1902010209031c1706040608030c 72
    0x11302d400f00ca5a0201c80c0c07035172001d20030b40901d070321519600c00c110001140b42000c68001ca45505100c081143c06188a19004190841e11580e0100e41c20b510002020885100a010701d440c01030040f031307600c04215618040030b0350328040d40c00007900c1076400240050556015403440344c202400f80040c0c491291283c1005890740c103141c0310b0521049008030109075080e010301a40000050141c5030501c0808013440112051313000f8445823500301108010010204428201440c0b142c44440c1e0031617100c0e07007810342031004030002e0b0030485036540c0071030340740d40009a0110550750703c131311354880003d00c0070420314128126030042d03504510458030005600701803003440300c445c10111110480801e091a010001112403001c40e201080050b00103002c00203080c9860310043d034201010000b40d03030501d4400a18509025012030500d40075039400200d4416600f014031001d044649001c81482010b0441c802c00b5224280610680701141c20040005da450355890f4001806400c20400b02d0f5110748045ca81c065 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 594160998 1250 594159748 594159751
    0xe0a0203040c05150d090618110a050603040b0f060a052d03030901020a110409022e0e10111507030b0a08010603052a03060406050f13170a0c0515 64
    0x40320542e81070008603a80c20900d9006000c0904059201d1030421044070000017040c1c201001c4400a4881d441002007034a840d44c0c00707481a0152080e550089511004c102d010340e029441203005442c14010000403583c051320040d404462189038405995802000030100c807825008240d0002800e050f5040344800c8030098284680003501802f08036103800d08050313481c01580c120600681c8441491000a4074107403040403203030b07009407000c036444215500084e5890000a4080c80d1140e65005c083c0100f02c1400000501e14100c0c24a8240040c2e030ba0080384c42010b504007040184030300540443c41d6203c00300000c0306d0a2000520054030b50405940040240c5802c051180c80340c1208000031690319011301c07030442101d45c024010000000d000254403046042c1201c041104039030541c0454664030180a150721441c0b14840010702490b0502170101c00c040040c02c844404803030340f00c8600000c7d550411080302030085d086400d44442031030200304c503503c4106900400e540100007428801c0d0700e2920150f03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 594162248 1250 594160998 594161003
    0x8030310090b0a081239060109050405070e041b09020306010f0212042c010b1309020a09061d04090b15030a0f0f030c061806060911071b0e0a020304 65
    0x1801840b00790300410544601c1c1d40116113068010080390a9504010002404102024000034000e001100c60039188660820361051208199038050301440c0414002d19001d882c1e8207030304011604044c1c490036030b541801e000d40480303c1c040340086414000071041948030179404903240180e01d5100d004038406500141d0b42680803842d501c100b5401c5a0020800c42c00380c68069940d03a08041c5800b110110b10031003100102c01c01c464928140c4605d070403000045010f001514190340e0b0700c041e00d641d9403403540b8550740486807051040c001c50110139030101c1c92008945a40c64000038210342180c607040b10b002c1d4220b00c19407043c40c1141b00801c11a201c070b4014468245101d484510068030001e15490f090440e4004100b803c640812500150803050400641ca02034500030502d46029a0b5010403550500850015007014200700410008980031b00d90142200c6481400b0f01c0c6034540030320034180580f20005108400348a49049145440805480107240300c4446a440e030800c2d100d541d00035441503606 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 594163498 1250 594162248 594162251
    0xa110703021006060527180c04032112050a020d290d080a110a061d0f030408070e09030706110406031112011701140907081b150c070803031009 63
    0x9407180c055010f03564040c07030881d2041e5400c20f0754248a00d902c3d1000c590305078845443d000000307d0007002c0038400d11070b1010f025090750301c50450031b00708420940c4c09101e80300207a12103400d0100c0e5038042038426949031041d83c0801c03140c5985101d030019014803c652082a841c00f1010741c2110742c1e244010900f0910300541e8080003c1807003c3c4415801c503281c01900e104c40410034402c030181300700b1484241c118200c041d507502041c9030303540070700340d5400412248040c0200384404000c0f0200f8031800500003420310003140741a1400c140c00b82c844445118095200c03980c100011080d400a204075100c00713902900c20410241c1207004910160403500404000034030b00040706010b10041e0044600410014102c5092a86000c800706407002001c8541c0c003440d52240001141740c002c96841d01c1c01200340c04054542d181c14005030364038240004c0080c580d0348074540300461311074035480802e1941010b9070034800c0d56840038178411441d088080e400030403288000801c0155680b0715981010603151031110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 594164748 1250 594163498 594163511
    0x2007060506060a0905060c0c04020f03040510140a1a0d120f0203040302130c030f06030c060e0117040b04050a12020109150515011209050304150305060306010303020a08030a1107030210 81
    0x140300850250194210109104c25410f101618140d80500703c0c010b901c80c101c5a880e829100401d00381c0e005452042c0d4540404414041046010b0081c0d1040000061003000080610f5140099420024240b8880180d9030500780803400449514032410f0301014109901040c560b1400121040c070003104480001d520401c0c00101d140b0100440c1c0c100c036001400c00c00c0300c89802400b14020070002d044041850342d41c007400c01c032420301c42c040c8100440c05507020100a6240c0341000d4071146001036882d0410072611000c9490b0b04d40313084507a07041038005104004540d51807038072a2420503090400780c1410041c02401c180d03203905400c441986441560b50400044084075044280c42041d51018245c04080000c7c00595210b0380e80c07480010320200340810a541c160311080c3c11688150400c0344010102001103402e02c0e0140510307a017202041e0014217043d0703d1501c0080d100c100003503000786103d000101081c500d84050300924201e00058080310f42c0c8860344e143c0650340c4d5030000b2192149500702807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 594165998 1250 594164748 594164761
    0x71109011d04082503080a0b010e03060103060903020c06220e090345090105060a05180103060302150a120515060f0705070b040f050303041508090120070605 69
    0x1d1003440050306005010720507100c65a8a98294000740c1d1850800142d41c820350b0300449207051150b450314040d0b11189170906040720b100d410350b1b0a039011203040c01008160039005480006d18681113a4000200003a81d10492400300d05142c034030010b4561010021074452203441e410040003030103000002044001d07075554205c01240f01c0d011601403a0980040c4103c041c820401c1e007170704c040070310001440402c4c200803d100b503081480c8810741c00c40c22240945143c030785081100c489400f50008a980604080e0714120080951040c031540801001100f14444c4240e400f0383c0120000d507a0041880b980f0600100180c0800d412240381c100014004001d45403e0042c5807183d18092078161410341c002000d4002800010341c0b14508127a0b000c602041101c021480500000c00039203580121a941c817440d00014624010380c681202d446a0001c01041000e00001c81d08034041e000681498112952846030340380c01401d03030303010020007886610314060680440000400c1c6a0b8810130f0304010644461 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 594167248 1250 594165998 594166019
    0xe0f06040504020d02091905090c032404021018060c0506060a061b05030c16031401060602060103030e0d050a030f0201151404150f03030c0606080a030c08090d0807110901 75
    0xb80c80c040d4101e060302440b0809030034628403072544040305000540300c2003d0750609408540003101c88558a030464200f000d641e241c140901001c450500082162000c84800c5401da0301002900c000d00c2845203000c480114cc2c002d0b00ea4080010700f44252424545d41c410004d8030481403107204075018005c044c006001881c0c00720900c1d05803801d0b6650701e541c2080715800400824190300701510140700501907020f48075410491192400004290b055009255240c1014002c0084600b407030241d040560a002040e400202c00d41101d80529002c01a2a420700114400b035a04501c0a0a240265040708040c540c00401c000b06541e0340d58001c05c1568510094000b428040b8081c1c05c1e480342012001c01c609151a40060b04450015039901d200c01e90341c0c0f8201d0120070082d40c4118045259507092030180b01c1c451081c40b0060807010043d10803554141c0d001401000d028000801803403000c10302c0300d85511090390141c041b552000721a5542c2c151414200200e0303c8072140340380f003250358100114220245 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 594168498 1250 594167248 594167251
    0x1809050c0103050604180609030912050309040f09060c0305101203050318010b031902090f160f030b1504080106090c0203030a090314070b0a06050108091e010f060e0f060405 76
    0x1400e40c62055000440141c0000b1300800c0d8010340ba2840381d4080c00907034800420305440740400040100c5186400307000b100711684445203404d0280f0701200410400f00444100d030344201c038001917440c00564002c008255410700a050545062000d154564060707100d94040c112022985000c1350341c50088524450302d021006002590920101d903401d2190038070064107023894000420040c66103004079103020710000c010344000e0410500d2100390f00b00308010756040301401103d42114070b0111303581a0360b000c4021684080100708980c155145210ba8851403800b4070061866100c1e40440b00d4024040d00203000305100b5506e003030b10014007104036128103c482525034028605540d21415884000c1c55100c03015001d000d020080d1142d40c110130f0000745080c600c9440b0115031420108216012945a41c012074140404801032000c0d0781d2000604810320304805840d5601c64200100705409005801c4d101002d80d8146403021030764004070030a079407044186040c1120f09581c0c1c02d0410094410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 594169748 1250 594168498 594168503
    0x80a06090e0307060b0a03121d090103030f0e120d0207030611180105070c050d03031e0c0e121203040503091203040303090513092a05010519030c020703050a0c1809 72
    0x10800c40e06001038070940041e034205000508060b11b040d0f80340c8504003032582501a020000700f4420760b2145501c80b40ca58048806c00030703134940e100c541c110b44c0e010b01645c0c2c1c5880c0c20380600882c0d403540340584ea80d00c08100c0546101d40140c0d106541c988901030b54a005d24041198030b5420841400c2103100000d05a80400d60461500c1d81803070400801901d05903c00d0009903818501c00340d01103029125000203599082c480d5074006910300c13000d1120000070a858103299100d42c00d100c0b006c1c45240e400801591451310803200c0c5d40d01c3c0c00000a10910f400c9041501d400101ca010041000f07101001c0003412510b9030642f0481d0f1b554140915050300c034400e83c0001004152045014003141c204468610808a508900080c020340961149501c083d103500d00c21b80b801240a0140c1c14100000124100504080c03c0c070604044c038056030821501020800072041541c0c0b03201100c802442000344000468000c425076030302c0c154030b0034001802d009502840340007480005e1666503802040c07040d01c60341b54 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 594170998 1250 594169748 594169753
    0x1060f0201022505070306090f0309140d08030a0b0904080c070605191b060f0b04110f12071e0c1205040b070f03020c041a1021090507030b0403080a06090e 68
    0xa180b22801510f529500300b0f640038445c40b500400000c2c0c41d442818031a5004a105241404482c900186501ca03240c005100ca001184140ca540b0b0f22074a031403440700c50b40001d10360f8482d52591691802007050090107548020f1031001c1c40140319420b0010100075201c0c1045d503050f642c0f20070080e9098400c3d40d01c254400320110501d0655035205030070501282c049000242040b00c0b6030745541090f6681d1742403d8a21036500d0410302001d02d002e1044a56001c2944251420b1500c0e1800030031070b90040c0e80104903800445000909403520483c1c2c800710103500d24a01c1558000c021400815070140d032482213880c4403129542214060291040d501140c0c1211405460035447d80da403100142694402142035118101100b2825a210b000b014074100400c0c101e010705804090400c0440800c0710300a0050142c000c04009070541080a40001d1442c15140030500224038a400340c41d020b201d1b4800307480c12000d0350a1200305680100014000c00d11407406010081d1146603020032120f003a6050f55066 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 594172248 1250 594170998 594171037
    0x310090218040602130e060a081c080907030506040515100e010302010f021c020f010605090402010c020d080f03040303240b031810020d02041503020f1c021c0501060f020102 76
    0xd500c0c40708a03405407042d0005800e21140441c080e10044040d0008458040360404000540c104440034800410341030380140200fa403007007006419001030003404020400804002250b102003002004002e40d80501160300501e45070501940300c0d504d0081c0342c810421010040b41804a06000318070548044490680107a441c560042d40c400b0140440c04095000f80300b56280c050400590041503150a03070007520394082d50850300ba00b150500e422480c42030106009020260340d201c1090307048240d050750078542060003403c2024081c05a00c1400342d418000208101c100340e410b03000309030306111001c031004c2030401c12017407442e1550b072901980c03c8615041c00002ca06590744180001c5001c1c041090b105000e0644011100341e038004208881441d030001400c0021209004001d200b0a00615046040ca200895100700d03903c41c0403440256400344800c0f8050082c8168101d80d01700e00024008000c2c204008c10040180000748503500114400a000c00320700387c01030007114804180c103244a183c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 594173498 1250 594172248 594172279
    0x20030304030e0f04150305070825030602160f1a01081908090109080709021e0c030f07061e0b0901080a1a130b072712020906060903071403100902 64
    0x10110044103e40d4040e0f1200c81211070221401402009540544050a911405c01c0f60442c541031010981a5001e81c4c000c0c0b1111041d10300006040c00d40303601c03607005a9607030a80d220550001540003401340055124201a0342000848108a002c00004a00300c805682e80c41031351395200c014014012030043c42000c3c00400042c4080000c104a8038141800c4003d2500d1340c008500e020110382003802100d50014610040c509400c03c2e4101c5c00e000503211514080b00680125161b0286040d01c00e0001808100c841c10060241c10003903076400020142440310811109480113044205c0d5118000c0040d200007090800000c1003030000705030816036011344110401070712072038414020b02c04c0c0102514201c0d0880001c0c00050004c0c002c1145544059611030001c0814400d00d0f01e1116914008106d04400c02c503803d0408510001560103c604400c0313035480c01c0100750f03d0700c62807094940c90f00600c2404294410046a04503040030146e04071660400c210341030b03a04503040100041c0d800013034580000710 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 594174748 1250 594173498 594173509
    0x60f0a050703031512030e060c0a0303050405071418100b030c090103050604020a0516080d0507021c05030601170601210c0e040506092e0f0312080403050406180e0720030304030e 78
    0x7c90080030388058544180f900c07080c0e080c21000c070000c90029072148180400d00004003c0c00020300040b61448200074007820000301240080381c2c2a60320009541c0008121540c0000120002c01000c0c02c22641c134030b0200001c1c0e415600c1440c4c141e01003403410010400f54100ba100342c0c0c0c0442c1c0d440e100c080c9400d10300035010558090903a0b0844540f04100100307503002205020301c070300800703090700109407001c489042031040d00160403202c2d080010510801c0850fa90000c1407240070300302d0f07203100c0c00207840391001290030811881d4252020f80c1820102c003690143e951103003240000564038000280742d000200710540e801074524a81c0701c1a405d011a82d00e195055a0716802da5038505c41e00840111160b5140c1428002d5000d050324083d90001001070044185210310f40005600d81501185032554002d4602c3c003503802000d0400404242c9035807801c0766071500c079010345100c4201c0045441c000034020503900140001e2484001083c8041d82e410b840001901d001d10707415200c2d02c04681e40d001c107021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 594175998 1250 594174748 594174767
    0x1a010812070f050a0b090706020105190c031407050a0306080c0d0227091e030705061f0513020c1c02030901030f110d0b0103050603070e15060f0a05070303151203 71
    0x281c1c107882c0c418510340010401c02450420b40c3c4180402107203850400e01c0141040304c990300403015641031004100d120080481ca2519004907407400245200b2444012002481900305030007082c0b103600240080560020040c242d410a903590600103541c60391040ba0311103803c080ba098110f98240b02703c4005151650b0340610100a6401c0b00400c41700c01c42c540060900c041e80e8100c0103070010b200d1212001c0c3c8010749200204e90240085140070780c50359130903595040061010003181c02c8a4452140e070650380c19030800030078008203284808a58100090700943c0031015154040c411441e13500590014402608450348060700a1420f01c050310006501502168440d0340090755070304001d074408290038019080030400540c000580328811800502290b070043e081a12a038440d60040200300c02007500d00f5804041301c040081126041d4002c22041e02800301c02c42403020000c120260184c3e80240130340704050290781c060200c0703400c07074604403002d402a00520140c3d045c80084000800c0c02100b415 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 594177248 1250 594175998 594176003
    0x10614070f0317010b0403030810031104380f03070302061b160e060901050f06070602090d050105011e0510120203090708010e0d030e0d091203030b09010308071a01081207 75
    0xc031600001c43c6a440c03030f2030b0001d070072a00d41c07150040ba0901c140341c0c0c401d441651018036680711070301c1242580c850031401520310080920840d1154990b580f804030103401d01800320113510b4041c900540c1c0c04444110f40103410441402501010449401c41c64001040300c01c89070050243c0d4581071402003403100207103804c1c1000700a8071500f14881c100e6070802d58248014012010382c1c841c03030704148081101c00081030384610300c5118540b400c8640343d030b40c000c1240c00341d6901c00c0d001696202d8034008540031142c594805441946010000260404220b80000d440300d00030b610032006986401c2004031135080507128100251400c0a920b094503c1075000395000510842114039941c0d50f509154207440006508002c1d0350400301c0040c08140d018040e41c00c003c509035020744054040b4200003082281148640300c0d4803074581100704145070095005980c6c044001d094800190384904000c0400c1d07002c002e00300c9036034103500800e1004220740e49150381a10420406426444071071703217141000d900500340a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 594178498 1250 594177248 594177257
    0xd030f140f04031b02031014060103050702030406050915031602280609080c01240f031502210a0603020114030412050c031c06140a030816080418090209010614070f03 73
    0x118015070341c2002010510f440b5554023203203044000d036200c1282c890240090f41818180000d00001c2034020055030140c4583e460403e0b21000700e82c0005030070110310000241d10080000034030003a141c3c044a201c400000c03640032140c07010340602c5030903100c20b29a102800380362500144240001c4150300300c1e5055501030310016082084600c074650840c3e292504034258102180701913a44c505c941103030718004080e01400c0035801c43c61074903090b0082c0c1200c2800503003541d0005083c505003962095150070040a10020304061500034200c800621003400240e021440f2203c2111130043c406040b40e2050798400c03482020700f003107a04191101d401480c88100c103408140820748410840c0c03020a007040d00054008102c691070f0070300741e042504142c09014000d03000100140040f0710302a0490303483c00c501c14543c202001542c100b002c0d00340a107421100038124841800c0e5806809034000845035802100d010307030a07903a0b480082c2d800102426100c107400b80c1c14400b14010402e0403841a40b841d001c2e013403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 594179748 1250 594178498 594178547
    0x906030a0e0d0c0506010632071704030203010609050411090403111914030304030f1d300714060c210c060c0406090302130b030d030f140f0403 63
    0x41c11030070718280c1d00c1d251000480c2c090782d0800340042080745078014066402c1151455003104910406000d0b0110a08842c4111324603004440040300220350a00d6040760794003000030300920860724160f0003403006a10a608202010070b012070140304250113543d00218a40380c2d00007007020701884040c010b1064042c0008180d040401c2001808101c1700c0c0c0b64400082c0500c004c0354a002400041d40d4041150964414020000004e400030810031003940c45080600003805040160b2107064500301c034480d0881000c8602500e0070040410103d800a040c49001034240900308002c1d944014074401e14100400b41c00800b02c0e54103099009020b19840c01c01610030403883c203000c19900e0a110002030303041660006040d414001e0901143d0380003000303151001d150170f140020091802c4668080a842915a4a0250b070010070f0359000b90380c0c4070b00c098241e0303401d244000d0019000b06070244940103003500780f5100307a00000c46102c80c00d10070385101c0d1000b6030a0300c540d20111007114501032100d0040000c1071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 594180998 1250 594179748 594179771
    0x60d0b0406110c0a020114070804123e0409121404030803280e120f19030e160b04030303180f0803040c0509060d0210030b0d08040617010b0906030a 65
    0x30450740192000501d8134603503d1000401680040c0c10b40074002c4c4007448404001071410046074108c4a200040c4070301c1058605122070880741c182001404401440c02e026082c000e04160040b1320200710001c03804070380000b8184800c0d1448220010301c1c000d11012092541c6004070300c07020321000e0036900c6504158032a80e90301d645500940d400121b0501d03d22020422803556841d0001c003418940040c030000752003075181551480d0107107070b11340c0180c5d010490005002c5a001562040d0914840070306c400c40b854030000c1e008215103100c840c0349008043c3d03051107902603003140e4030458071940d000e00c0c034261a5071400c3b80140880d0804152074440b0381c2010700480c0840790203456460103924820303902d0500d482e02031180301c07a07540319070301640d0200c0400c000f503034440b46500501c5405455484e480281c1550440003029801809917100102c1d1144105010481d0043c0c03003070700c03003640b1107520034900500b401c0b00001c800d218103c0700038010030140119051036400f45400140b9890045080c0a01c0c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 594182248 1250 594180998 594181031
    0x512071a041a03010e130f0609110607300207090504020109230a0909031d0616030503010905090c0a17010209090a02030402032a010c17120f0a05060d0b0406 69
    0x140c225162410b000301c01440301c00c010501064101400c05490410300c1c1c2640d40c1d40c9550540b606d0b01400d5290303924007420610001c584030600340c110050440355540c0d80b0f482c2088030800415901c1c00030803000c49030b055a203c0c014090a4030307401d40e50010000c2e0740c5030441c804042c01f4001c3c4103e04011403080300080c40c0d01385039040400b840e01840c0305004050030074144800b40045900c040b070001d0814108a011035002041032a86040f00d40e40b402d030200356040030895902c580300100e00d00b0780380410b000b028154450003560603034115010511203521507138030340c41c1d0703507201412508c0c2c4c80a8016001c021541044d000403052003091000036061512450000e07103011001c644150405400208200842c90b0502c50890712004114071071002300030711840c40c01c500f12036110140c10301c8459045001804100040000145280601c50755940201d42801c20544402c1c4c4000b980d40d101030300454503000c100c0c003500703100c3c10025240910580c001d44840c0400440640180d48036541c9810130710781000d10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 594183498 1250 594182248 594182279
    0x2060a050c010c0201181b27050c04052209080a0f0e04090b0105150c07080f1c0f140d1b09090216080903120a090e010512071a04 57
    0x303454298031034000103021825292401c58203411a40740c1384c980ba800c803800d000c0c01c1c143c864001703040400f856000036800c0c08810307054004d03e03066800310b646071000c24440300008031250344a031801d1040d61a007100784040d078061030041952000103804480d00c1402014403460102083d040c1c00705101c600e13621490096405808a500010209101c184480b5003110020703c0549040c0ca00304030041150300d9402001c103041c0178287c41003004400324000b001c0c200040d03500b440740da601a610301540c0c42000396524090596852800d0052982c0207040f140540103220740e801d9252034228110890003811510b00c40703c1c00c81c405609006020000442e02c1c0c2d88640c4101808044520b5030030f8414080c05041d4544e5584281000341c01009003001daa8254942c1c4604c1c103500c886815290803c2200080c2091070350b200b1356a0400340845d81d5208154071200f20f408032043c0c042083e00c181d0702c0318203104000d1040078181c81c00380c0c410700b42000b843c5a002112079400060520450410381c9070250329808821 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 594184748 1250 594183498 594183517
    0x703051306020d082503020a020c12070f0b07050a03030216061a131e09021c06060905010504060503030909070201060b070c0305070e10060e13050f0f070f0512040f0206 74
    0x4680c00c0d00f444d8000060f0b80d0821510840c004c0540131842e2480d150414240d204010036070040f4440e9020340c003c0010091541008103031260080f604040305a0300c0440f40300307210a03e075030444000395501e40300044400007500840600310700150b5031000d0300a9880541844a079200c480c00c0440458002c0c840c1c00c003900b4032a06812116010f0008000c000c03085006a40c55235440c0002d000c80d900144203030295481e07003103403020070300c3d030594000509003100c0e07014071583c4141c6102c0d02104211080c0c0c0f1103000d841c001c8204014590300d500c28403040301c2c03660041d50f400d0f51041200f9030721458110802a804131061001060356615a042c00000350000031049131340380c040040a10820100748403880251101041d040c0c02ca142c00118660351b19043e110f01380c180140d0f2901c0e08101c0d290040d01116261141c0707018401401c0000d03c048410b00c0445034071101da00e8010100320b205100e4298403101100c507507541ea0418100788000381c0700f00b2001e80304540d003018100150380107032a410003a04105d107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 594185998 1250 594184748 594184753
    0x60c0504090f0c080c160b0912190908030906040e191802030105340912030c030201050f2a04030512040f080601060203040312020c0a0f06030c1e05070305130602 71
    0x880f003410107003840c80060709484d4820000d00031744842021013040d00c00344070781102d2081e4654941000c040e040c00c00d421080e025440f00001c88910031003110700e40a0790b16500c3c5e5034103160603944d2103c040d140d000d02d00202d648490104010000c045000020a401c6018000300f41d100d44802113010342102c1510680c00300c078030320b10b04c1c5003070951500303100e6180c0c414111180c4850204900c2d420126100e800400603a0500e241801c0da0362581c41b8608141c06410350214804840486050283c824080460300310300541c2000c000404005292802a0080010380403545c0c0441443da50048208110312502100344014440000410300c1080440900354518810554a43c180344c900c40c0c01000725080031207190f000c040104161030780002154200c0380c204002c0c540c81c828018089062000c04a801c5512941005012903503c07852400030080b610300f900c0402200c0e02102c005c0d142001e1000c040320b42c8804141c0c5e510100c6000340001c1050510a16080345440300c001840301407503403e6040303c0e0059 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 594187248 1250 594185998 594186011
    0x60e12100b040b0d020d022206240e030a110102010908030a02180a060503060402031003020d0b011e05031515190501020c0103090f0311030c03040e1b070b04060c0504090f 75
    0x2400c0501c2039903e090400d4601d003c40000365000700707826032010f5100900541c103041c0328131818402107003640c030345450048041c030441d5a58081c1d41201a10800405001810b208031031f02c060740900d4200305074210240c0545100c2c40c1c251108282070300540c2030395040d9526280e00343e000840590085200e035140c45001030310f5103110b102c140243e1040fa59414007c41c1c0c0c80c24280b11040e00141500c0d8001011a005603480c0d0700c2c248154000c0d5007580c4001c0d0400c4904080c0c0c0200030804100a042e2850007690030340c404c1c00a0740c580c014000501c04d02e0307090b41154100080c03d421030b2504962150354542c920810f1010100454104150700a840303000d61118041440a5130f418032403181c0002c02460b0500113460141c0b661380788070078081e0004007402005410081150000d0042d208400000c0d070030b032a2a03954640518031b103200202c1d000ca0403072054201c1c9090b817034602c901352180719402018203501e81c0e03202ea03520401400100512402d0080502000418808a0041d60040b0360b0402c00071402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 594188498 1250 594187248 594187271
    0x20102160f14010f0815030109120c0510150515090d080a03140c090607111c060509060f041428050606010c080306010f0507060603030306030b0f090304060e1210 71
    0x820b042c45241004000c048020b407565000000381d03004024224500420421030740024014615100010000030003800c0031200d00790840c00d40e246042c040c0701910150340b4004040001c80794881c911140c07254140f4000c0c0502d0401c003100540e0317000c1e90618507260100382800034525121613031040350000e900141c080d101c01d9240c0640f21050f28010014400d908050300290804e000c0c044070305001e404041142c205222201504694500028103120310ba169058200d02080040070b400f40c0d40541441d000c20045c0c1c00c0040d44a1203250008188611a2140d03078880f42e80140503d81c4015510400c122030030ba00f403611b00c2c1881300c03041145055400405601d021814840d00500741810300c4580030300d440c00f0501c07841c00c4951000091030040600311501509656600031070304040c200310720f031a10200030036802d54050410307a405800c20544580e10141806210002214901e40300d401c140300c1001003901031401c024082d00f00610780601c0043c0c0d2401d0520b0004c54524128000343c5400c1613045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 594189748 1250 594188498 594188519
    0x1d030613140c0109062d03200f0306010c0c0e0a05160e0a05040f062409080f0307030e0114071212020c03040e07050408060708040209062b020102160f 66
    0x80240c011018151400b100380002c4c0840c14680b28010a0103141c0500090314021800540c4501c1c0074a5881803500c0158100103005141b0203848500100300300038240c040e01b00000a0310140102030301030340e00d545d40316401110030300c0c0303602e90840c0c81c424140800b00e10082e800c89190302c600f60800c00000c0c98034062600e4052413414912040038482640d41c0d00340c454981103900410b4030802c8d5404199081012201c800405043d070095030010525140c0001500e9421000807849815560382e9014a80741d14129444441c1c81c9041035160703004202c4e12000030b020f0f112540102c00141018019081c920310701e40314980c00084103c032881240d01141d02d030107810600f11b0003143d2814100718101100701c45100d54034441ca014081c001e03107a000025074032a105508441c00b8022010548070141003141c0040e201c0602650b00301e1040c2000d1f000603a107824081c4842080008010724401c41c4102c000260707092184a42c0d00b641140202c121118480344520304001c0202038403543c2d8041e59103008089103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 594190998 1250 594189748 594189773
    0xb01050c120d15451a04021c0c0e010813030507120f09060e060f090f1807020c0d2d0605090d090b04032319030f030b0a030b071d030613 60
    0xa541018024240800141040c103c4040b0b403074a504c00600d1941c08440c0500404288001a90003400012054076410b40c41550008038040e170341c0d050200090b109000c1c0c0301090400301243c001030b420340000b071156150504c02c1e20f61707a00900349035107041c00645401c00340782503114082c000301c3c501102c0b8400c015072040321a0024a0140351219843c040440060f2240c030420012014101c070202d09405299906d103420414100028600034031182c4641e0744603041041202c050015019410f10c00e41c50303040199559110960040529032912030380c54494000080306604814040b48506081000a10034841c49005001c128000e21303114455000041c400c2600780c0040c20420400e000400004039000d03160724600c07481d10701d030311840130781d0003141d82c036198a02c0750428103044412081c00c103050304010145d404510342e50701841421038450500085000e40c3c4030040120240000144009100d402c071070b43c60300080e41c4821a03a08125002a180220640f26016002070ba82180d41c200310000f403104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 594192248 1250 594190998 594191069
    0x17010501061e1106100e011e0306270b1911030f1f090606262d010b0301090c0215010302151902100b01050c120d15 51
    0x240059030429100038580c404603020040d124488504070184a4082c403201008100302e44110b454a00c1d02c1c0c4008080d884081c03080d00c80c154098400440e11300c500e40f070290380e003099103004020032a2031981d80c0e00c018500e1320421003c05050103001158050610400602d081c011481c40003182040e1107000c040d4286080469826461b00502d0010f410040781903a81c011407413030440c2040e580340610700310b0858201d112003884009100d0b0200e081072081d44002c003591515540c00301105e9282c2480001240c402c0190910494080005400c0c02c10060002014100c81003d0810744100f4040d8964075080a0300015501c400c084018000e15085106500342d180c0b43e88018002a15040b210311403030f44042c0406070003000400c5002000d110440e088486110900c00094115100c07040c0003034840c810b0660003d01c4030300389240707881950711440030f454103141e01c003018123007080c41c29510111503403041d4511601961a0b10b01340601103140000c0701c0061001000b041e560818070750003110f4400500c440b2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 594193498 1250 594192248 594192251
    0x809121006150c060902030102121e0f0403080a0b010908030f03040b0708060d0605040609080c0a0506090f07090e0f01060b1201151d0d02031903120e0c0d1104090303061701 76
    0x2507030751956001c10001070240d00280005800303085030002c070340680b107001d0001c1d030440060f6041c44bc01840350038100c103c2c000180031081076500e4414101580e400240c4000d000a250800402c101e070606500c1a80c01510504200c2c4448e40c0d0707240c910b030454204114012600c24040100300900004c43d821682c0100030345441c42061070721400050039040e4408000d06030703550b20000103041040c5a400301c2c0b005a00051180d488600c02c10720700387d5820329040111014041c00c0c000c100400d10000d071440c01040c040c0087c220361420000a400100415464840306100c1c02d11200c0384a04280300761805446450201640c4016440520226140603030040b031440749416080c3300030b25801500e44941c403000e1401c01510050b0040001c540c4802c9840196042c01403d299109030b01c5d1003413030301c04a14031a445640d480c00100401c6d20449500d016142c00383d400940e2102024030340304000d105070038030849501d44840225008103046404030b1200720003007642d03070805001e66800014038449a40342c4500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 594194748 1250 594193498 594193529
    0x2a0a031107082b050f1503421005031c05070305072916080105030a14070317090a0e070c08180301111308120a0c0809121006 55
    0x202c240682c030524041e401500402034001c20b910034020b4401a10440c034540512403400c10100740c03014490166882091050105d841407880d060100d146142044000300f800c04403802507074000070780010900d00e80c0020480003820784601c401c80e91081d019840310340354040d545042000b0b251500741d411040c0d21140420031000074120342d10404694000713901d40390480d1a8890391030100300c0040e100c40d1014020101c0c04c4141c2c030400015040718450302c034244210903d00410036003541c101e64280251038042d00803e494a01081180460b02e1070b84403c102192003c07940ca031205041c40f095811003643d03101000803107552a140404003403025040003c0032464900b40020040c2c90f554000d90300500280001c03c4030b0701000941c419044000c1c8000d8001e203c0105003440b40d03200c43e800001ca5400c2120f24410110302c4600008600320500c4244101a150030305103841911009144501202e240c8820061121b00761150400342c1c0c80c96280c58014802c5d41c442d5007004082c3e500d260021380b581ca84103030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 594195998 1250 594194748 594194753
    0x13120c0b07051305220510030507050d2a030317150103090503090402121902130b0310030c03140709020f04140613032d03050706052a0a031107 63
    0x14003407500300405080c001d40d02c0038520b10a0030070014540c44194032900080250b1000c07200311045401c0c450014404004035941c440c01c04a50308105c3c0030180044e8803000c000d01a03400c06c0407102444a0145e00d054401000f8502074068080c5580c0b404010340040c11403c108068000c1404c0c641d64200d0030107100f040c078114030a04100c00c24984098101501c8040380800c0c41024000c841107a135020b4010f41d41d030307680078040300c101d550150f480c1b82d0340085010314500c99040c01d209a4280803401e01200504500c3c040101c0720981000c1c25503112110000d00010009401c40c1d40c0c080254858600000501c10b0303002070358141512903014410320381c0100456102030140310101c0d0b040c0c888802d00d40250661083c0840d0035402410708001c02c80382c0b09000801407010300041d40d034003020380b034401c3c0d240c48103c4079440c495038604001c010007040c400e106610008a031744c0c100326481b15001c0401002020649100088403114966011145000040d51941694180034508846180214592602001703a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 594197248 1250 594195998 594196013
    0x60e0102190c14030a090e010911070b0403030e010227120c010c0f1a040c12030c0b04060905060703050907050a0506220e01140103050601021501031101110613120c 72
    0x4005104102d0000c030035504000d4000010007000380000104d0303494245080c0081d100200c50f0058403c040c4800c030000400c48054092581e004185241c140d084c6401e907030701c56030102c0d0b000d002202070585034064810401c41c244054401c869055001e10510b071420040c1107a241c00c40034051f40142040d034410740300114009180080e034442843c002616850301d080c196818501c0440050070300d41c682c5031203a08a2011015180158083d648045c041540d40482d03070083d25038510300801140482da41000400c2d210423403960701c40d0007004086075031140c41d42c445081100854107000865a160284540d85000b000f582c0050324040d54840a03a601745000102d0074001c000502041c0049506103151040803a558940104001d01e00c80c04a035848000040b940303041c08007014000792901c00041d8082d840060030300603e240c010120501a425500e40325485407034114013a06001441c0c50403030000304100040c81c03103043c80e01103d6030f081c0d035149012050105030b049181c0812040035098408510308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 594198498 1250 594197248 594197287
    0xe1207060806042717190f0504083a0203040b1305030a05061b1602010c060605101e0207060807051305060c01020307110318040f020f04080307060e0102 67
    0x381008809640c6001c006000b50440640b441c40b2291500c0020744241031424240844c1ea00c12040092104c0001450b40c005000303030052554a41d60040d0510800e90203050424045080c81c40c140d4a060b85a52113140b0700425903a2031205012051461903400c40411500406038401c10001d541c0c401070300c40025540c0c05607005030402c00700001041c886901312900c62070010900a03042d554000c9035401d01c03070b480d10f00454601c030a04c810254044500f0481808481f0792007824001c40c1030000068004450300d15082070203c403070507501d04001c00c040e980e81c42c42c51450309403a40d42442d058203c40c414560f407a20b0140b400b00f0340d400031f4010f008041d0002c17805980444c95140ca40d44a49032010000c80c0c403041903210f16001800084c007c25840019002035201d100789403554404100b803001c50647c0c0f41304d03050f1440c840c2c1d0703400704180000740786c035800001c0110101c1b0400b40c20715224044032011640a50b00454103644006403441c01c0196602a0a1107481860021400d120003c0e040c01130760b070f84 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 594199748 1250 594198498 594198509
    0x906060405060f0904020c06071707020d0c030f0c0c0b0c070b03070c02090c2709070f0906050c102309070e06060306030319090f08061915030501140105010e1207 71
    0x3c010840340402d88859040e5007101001d40200c504ca41011140a00002c030000c62544080350080d00060000340006455121000240d403400c500c0300080d102210049140702c040382c104846040100c010070003100001000d4900000855600e06220311000d2600d4020f5001054000041c4104039507107400a400c00180da40596410816a9030035140da1494402c1e0040f403103440c81801c004581900c04000482d070020003d85003e41030780c403010b0050f1b80e031040b412280b50014254440c14041c0c14810009005849614422500c1003500c51601e03405440041404400510403141101001403114580035000128000504000740c00c000c1d039030910020040106004000c00008900551000c20840310108960459a68083d018040c020180507092185070703042003c1c884041990394020031014083c080b83da114a40c50080320b03e8120203054404d0010b19610061500000131600a0180c003038014480005201a507051600240c0f4420469002c0c038001c40c00017002100004000400006690b0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 594200998 1250 594199748 594199777
    0xe06010902090a1d011a070b011a07140604060c080f0610050408062509050d02043b100506060703030509281103031c0e07030b07020c090606040506 65
    0x48070700c00400c00344011035200e840e04049262650380702d0f60107a2980c0b4140c6604c16120007401b80c01e0503072440c40c0d0181e0000981022501001000200152410689410240c0e0581030501d0503a80780c25481d041c50a51141058220604020403c80c2a200700c2c2007054940c2040042e0b401c000c046620710190040600c0c0c01805070198041002e8056025140109003120448e11907151100380700c407011200000c01207401c0c015080c0d0b524a50300894400d0282d03079010300750f407032019803e408000c00750101d26603a070441d08100000078002c00f0304c0300c0004500c1c114003440e43e124001030b1030708030324140e0b6207442000942d140c002813201541c1c0d103e01321070045405140c08207080e103821200508014507580400341c174500368a41c0c910140040c1032003030060703805100881c40c600c00f20002e00d031b103038866101c4107901c030394442c01d91840c1d03c4501c2d0301030400300078008115482c40b6281d9443d2285000c040d0340c1d07100541e0080d403250010b49802c105007507003c0d60a03144d41d424245000701150841c042da01c103010005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 594202248 1250 594200998 594201007
    0x3010b0d0c031113110d0c0201050601020a061806020a0809070819081309052d01050d080703051905090f150307030b0312070812010b0c0c0607020d02030109061b030e06010902 77
    0x6981c4c036080342c803400b10401400c2142e030032104c0160190380c2c402c40004400074184288100050300621401f0300c18401070700500b00403100e030780e515001081c0044150720008182c3c2c2540000c1074052025081521160321900107504006811030302d85021a800700c40c03030358091100070030a41c401c2e190508950381d014040755216225500d201010410039000784012614010811041402070500788540e50521064400e10400710114201c000300300740682e5800980800c3e0b07000005951a000b0100c2d940030307103046400c1142000c10308040e08503041e503002c0060408140c80388140f8100303009020300c20088403c0428908903584800c0d00c0d000041c40703901496038408800c5101d44092001a072500060051039581d081d031440c0c003002c035030084451803400b00908030002ca07280d0000012502420540001080b5499500c2c0801c1030a0380300b00d000b00d8014058465100050f00c2c24050030001c144076107000304600d184075040c4005000031030344000c1010b00300242d01711614000303d081415601d807910090ba80303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 594203498 1250 594202248 594202283
    0xb03090106230f3c04110c070303050f0c0d170903070f140a050a23030a0c1101030b09130b0601020c1c140f0c01122a120c03060503010b0d0c03 63
    0x301e42e508035503c4154852840d2101c0901221a103a044c04e510884040182c40e02581c943c1c0100d020b601d00800705580120000d001017401000034150320080106110710707004402c03c085041c46280da80c5140460000000840000b20038072400f07138021040b40c021030800801343c481c0c54424155460142c0003115000d224560050f0600242d041c0c65000003c54074004460700e07101718114840c0c041641d80c18460703e140f201441000c82101e4070800075940361000c50070980c60700303e8a000001c00c000d0503d9504d01510240d611038000c52807149000c01d60ba00c2143c185814110848800100300721704640010011070f0181e92074a103030020170000c070304603004030300b0452070004400301503c81c0c483c080c3e10440b2420760070b903900010b54544ca40000e98480a405007900d9928055507085406c8942003282070f200c0c2009004c510b07480f500c084a841c50800e80317044000f500300c0204c9a00110359000030341c550030b051200d03060900031410406400d0782c0072400c011040d01c56040c005540c2c00020130304210245070110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 594204748 1250 594203498 594203539
    0x10806130b0d032a02010c060f0b1c0c08030a050d0203040c030203061006110303190e1e0d23040303050c120415080906101e0b03090106230f 62
    0x4040c08082c2c202c04001c0300c503003000b03001d070114680054600c01140390b0030b980086a02500d407032015810703110f002c1040303400e41d54a00a0012010428505903882445800a941e041c031072001100c0315040042d138240740b60070300c0c1d05202440e0308111680d40c410017107031a415500c82d0460b4646903c42c03500580b00c0d00d0720300e0800d840e00d10660010b07501d44034000500c03003900103644806040310000d854404400034110080d940380d010883e81b09070f900006824840c041941500600d070500403c06c252004c05041c18041c081d0140742c0300d000d14465200c010440102a008032410004e05010105100311000c1d144545500d03114601005082082c0072505000305d200070007603446035990960f240d03a1100e4070b644050304120020755180e8000346549021600350800840d01a01a1040d0140e02c0c15a5050040e910500c01c60802d0311211700b0407031040005c0540141d000745004007854000030030581d2910812256000315148140840868040b06007641d5468465980444109541c8d401c0c0c4040811032220 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 594205998 1250 594204748 594204761
    0x1060f18060305031206090a09030e0d03020a050d050c010e0a08040311060403061b03050a090c090c35160206040b041109130501150807030b06120319020d050901080613 74
    0x521030701c0042040010090194100d920807101a070b112407c075a1100300035000d407245002e028000c51031402c07918080f420f00d4995010700300e000c0e00449420980c980c0d9803901d0100e41c1c041103000910045180c8d007e444003801448641032940780104400880c45d191094603201d40c0c03000410f25144512100e1041c0c84041c00e841c021070b0402c074100111040000e4580440c01901065000a0b02e4640052130348455442202c46854010b401d00e41040d04100b0504000c00d00101194140001c1d0b260380d242d030403817400d1500050389810030a0201724003c454500c000c4080075085171051000204090396230303580012050b610503005020700403940c1b01e0b810075542e03110842a115420182040400001445100c0182d4205200b080208a02980700c004046410914042d81c1a0f5421050f800c0010a0f14034280c00c0d04020010b15034440b60808071607542c034592109007c1d0080c055002ca41011540e01400405010070751410424038000020000070014040100302607c100904450007000003a241d0040c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 594207248 1250 594205998 594206003
    0x1050d17030403170606071a0702120d0b1e01081504091401090b06060f0f030a0b0307030c2d090e01110f0d15060806090c12100501030e01060f180603 66
    0x1140d41e82024100100b040c4054440a58452120750100d80d06080100880b81115041510250041c0f030000307058800300006011403045128913150060071038103550081c8600264040005070b1341d80d046051140c40c2c042d0301c004009083c208407440f20180d810818607a444411f0380d242c0440d01c40d0440000d0002c3c020050041c0c00911001010024100d05500c44618103002d40c80013400c0d0340e1100c003000498803030390401241041081c0006d41022040c02c001e190000d418103004280f0a283e000444e02e0700109a00980304150000030800c070150180c00d60f56008103652001c110030a034002d91841d1500e84034450000c0742e9076650000400c42c47c003980a401400b4981817030310369a81c4481c014442540111008001c014078260724a4250040c40001c0300c1180c2c50707030f1500c9100f592840c0c100003407820000c0c0a041092003c01c840d207028050142c2d035600c1105102c841c4c120040c2003100040844010708005044e5a24100091180b21004910b0000f02c40c2c055548290240401c880b0001410090303000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 594208498 1250 594207248 594207293
    0x15150f2105090609070501200114091e0c0315190501150f05070203070e07090f0b070b060105090f15040308030f04030e1c020d0606050907080403080603070e01050d 72
    0x105110302034a400450148491108841d12503c504082e1030711a061803281c5804a410443d055900400a104200c0c0c8085660300009018100950020441da421a41c00210760040e00003c041c00d40000022610320840400400e285210540230a94410401c580625900c5000000520700389002c0ca03205502c01070910f0512113540d54440c4400300ac1d202c030b40340c1000728005601c0f01a5603403040b42503070380c2203800500804501e4039096007112000c0d00a0000d43c200140c00c4804100c4002442c900d000400d10000d159551348030328280b04200d07650142c2340f00c1c1044010041302203940e03124420545508002c0761036943c207010210340c0035400d11580e030000700185400320070404610020758103140f09038000d4940c1c04003000804200b12548281c26025481e58a144d064030000d42804900380c0300b003508c244000281640c54000041000030211491000120060b080008040e031000296811002c150300038400542030021482d418181401000e00400004c0c0c001001e102c04259840c13104034082c0d20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 594209748 1250 594208498 594208547
    0x11030a03090602062a0306031c0507021c0b07030c210605090714040608060f061602040608010605060f221d090705090114010909110d15150f 62
    0x100600034000d580308040c09030050b1380001c0c00980088100d0640100b52043c010620303041100544036981020344180d4143c441c040c11806011050405509010000c1d10342d252030342c07428030421888000314140d007101c14a4124071440000c480c900d105030405458240400c2c031518980c000c03070740100038940402807d25814000c070031030400b9500032010b8940a89140e61140e0702e00d50252510070118002c0f10b07510a04100401c9114810510940c100c0401041e111800b86030800107180e41d04107540380755003c050703500c4c1039086162500c01c110050503001e0007840020314110002e0003078069001c0002c100000055584440c2c29152990301d200310b0700070b001140f0b45407502020b0301282c05100819041460410200324081c10014815084039801425800f5580c00c20a04d5002111001c00740307410700000f00004a03080640f03003e6a07010001050740e45459130b152030f60000540341d0440d080303016000141c40c24090b4006550b031544c544225401c119941545a21080700e4490b81242c0822841c5007054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 594210998 1250 594209748 594209753
    0x4060e2817190201020d0809030f0d0f0c1106011505090402040f0824070c050f06090c1503040809010c0c1a0d0b010206060d061d01060f0608010807180911030a 70
    0x1c0d840c039030300001c108461054000302100c101c42150140064003681c4040340001c2c90503c1420099481b92851040c1da003020462035846000713801694044110b9507e624207c011803d440c8540c00405415207000c44982e60162011030f1501010300502501307000070105a14501c0c021001c40b56100e1028000b1940c0702d9546100411000c0389003e43c9010703001d41c200003501610000c8031907104212001030798800361031f090415a02059505c0341150280a40741e6125182a41030003214405c94610300500394282c1140c0811051603000e00b02040800414030601000c283c055003a07a0101c0301c282401042007041c3d00300201110026806a80b00a144030f40b80440000090f015060032441c150090110380e0b101c40069840b103004031051034100488903158008202c2c240c01c11030701403030030003401100d50351500c1050342515082d1300840a0b0409a070f104002682c3d01a0725030b401003403c103000d05096400d14103d45040762210b0001d0680720b49500da05410b200080100400004009045505500452 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 594212248 1250 594210998 594211019
    0x12040803090411071a150d05010c081008120703030b1509130b0616020604080f0703051005060114071b030b04050c0901063e03030f01050604060e28 65
    0x2000040c0280e08125807040f0034882d5400f44d550581c1e01103128072075018038150002d80940700410103916000720066034446511100c0300e401c0580e0042002096030f42d52410040c000007009445242042100e01c0200000000800d001d1804803002a45658030304880c28100c02605801c0d01095000110300c0000e403405448200800141c00251800f502d43c40a03e8180b40882d030007076000c2a00f10004210160710b6440c1c060000e42c030b09200030841403c00380c8949420f450000b0005031030b0040c0e40004824000c0c480100032415102408403414492480c0c0100001e00d888900c0c024001c04a0003c5988420071071000c1c03018140d045c00c405c03802c0b07104c0e6407404c0446081000b074405a0345400b54402020250a110301c106040c1d4485443e1907940c01c400c070b0342c20030030071019440b5016105140d074004035842c1c400c655046084282c2c50010360304ea00f491707100c0483d1500103a1002c1d1003500100010000140c01c01040d00e08400111441081d1021102540d01c0100c900380b05080061054440460301c403602 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 594213498 1250 594212248 594212257
    0xb06130614280206160806060904110c010f1113031b18061d011412030408060108061f05030606040f0b09012702130311030a0b07020114090a02010f1112040803 70
    0x82d422100651030305c0503050040104064030100140c42000081c105041030402460301c2d11300544001035000e070145441e100341d0070008480c55541d4440f4070039403940e1034a010b0000c504461100d81d42c03401d80b01c4a0900340ca81c1c118400240704500c41540b0300c6014108444080c02001a910401101c2207841c480c48002c14040c0240641c03105a4503100c0e224660380c0c000d10703059900340300c9030310782c0a98040e08200c001035030840842600d210401000c180e0720414814603009100d58070090080d814201801d00c03024820000015003840484010081039400080c2180c01400550300080c040c2c25010000c4007600840301483e411410368400015039050980d01407030b515981c0d000c0e441c000c814035481d083c01e03031041127007220b0301068112003400418205004901403900041c00c46131441c009030b40d12010b0700e800302c0e550307000741c6d540304146200458278601a90f8000c113014041d044c0040c0d10b900103080c030b148144402041009581291060030310411058400d000c12189e40c68560390740b00030060390380c0d10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 594214748 1250 594213498 594213577
    0x51306051e01080607020d1101020405040f200c0705010f030e0f0a0c0f0806040212030c06040c031109010605120a15032102010207051207060f0906090201030b06130614 74
    0x1c2850000900074404903056009240c40c4d400f900c1548405542200c0704e1014141c03a81295508100008aaa403584603d04c000400c0315400720351400d510080c00e00b0312001101041040d503080214542d00c1401003081015541c3c00d00782492440084901140102104560741000e80702d8100e540302601400103140c4032180c410444c1c01101500c4509111480d41244900c52860f8805000305005140c20960303151888141c00c11a1b083c960001c58443c81c04070151000c0e6042c0d060302c0380c01c2c82440381c16118407850380c009460710f035080d5241020060403403280b050500c404690400c0401c0003240315030050b0386000c0b00e8440b40c41c070040e100d0501084005040185040350b2034200f4035981001d0042c02079850054101014050715464004408083c0c8c1c081da800300d80070343c1d441100b002e1030401d6100e40e0507498059040061101101d100240480e42205805d41c400e903014010001c500c01c0703840c01202610040d01d420300510030485041d11984c0900465500002c0c0d02c41c0402400000c8155500002407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 594215998 1250 594214748 594214801
    0x90a03032a0b0f07032007060e060112050d050405090a0e010605041a040f11032a0d1407140412020103020706050c07021e060f0f280e0f03030702010305130605 70
    0x304c4007503040d01254122617001c043c4c5000451101030345203006025081c0503004590105919481d28409420086e0076000301a1044510400200b400810080700300d1a94842c20060f1502d4104000244041d8004015602d21916401003100e104000e411140007080054018819080c901c1d007030025920070001914003d610744007201d94049098050319110341603092040f880c64540403100e002403424a4094541d840b149000f480400c0b4213400203144504200500045840c0725003501c140c41c2201810070000c00c03d54030083da00340c003855401c071003c803094000c1070b40101600e403005070081c1c000d03180c024041c68a03200410800b403508800620f4003e1081381c3c401c60b402600c010303645000c2c0c088960540c20900c20b11046c0c0d201c02c920130003020000612041da80c00c1c80700109010314001140881019035203000344030664695048180081007890440c0d9601c020010800030a40e24040c8120280c1015282c90200c0d000d84070402001c0e01c52a040700f800d0040d4500300459100850806001019a9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 594217248 1250 594215998 594216001
    0x160303050a0311180411040f120606141f020a050a06090b060a060512060f031e061b070b04020a12060605010f0503150d081c0e01060605090a03032a0b0f 67
    0x1000c0b91044458041200c050811394106402c2400014a207600c2e9410910004000201c0e00c01c01200402008110220f002040382c60340e071404105840d00383c1e015100b80240c1c06d941c8201c0c1e40d1940131601001c00c251040800d50070400108a103032580941c409041c90260035500707000d0012a07003084008074007515008042d40c40d488240403010701d09128640000b8820310510040342d60300c04800b504004c00400307040d1155061030000741090711000041800c5065089041c1e2a0041481080c1d840100d0703d024841710f2000d0600d440c070910070504001d14490800b0002402c45d42c0340156040603247c00d2030341203124141450840001c002500450380810214031090000b20b00c617104a0780704000040c035030b95061919070f0601000c025006011684040203202c1c0060100860b0448082c4012040000c40d00c3d1700d0040c0003c0c21203686030046400c1003810428003016484801540c070071070341d240c074006000d501c615250800d4907030500394840000c6418042401481400d41c6072502541c003a450f5000d16 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 594218498 1250 594217248 594217271
    0x1b08010306062903040507031703070e09011511030c0304080a11030d1e020106080d02010609110c0a080c030f0a050904050a140c0711060712021e03030a0c02160303050a03 75
    0x81e0b043c0501510f40c0740310100b18895032001e040d005107030050320a00840b801c9644994415204807111017241d0120315000c4200b02d80e1a510103101ea81d040b50503144012294109140d4806000213820b1440504c0f2914041a4170810301f042241d100e0090a01541c0d10713192209070360764403091b000e1015502c0c0440203607046402e00d00810781034090241307511070300b04c2c50303864a4005500c0200202903100b955614140056010070034442401068151303800041e00314140710280c004c603140340440c1002c00c0c1051140d501c11040c0046d0a030201608011801e8903031042244a6245108201c2181c08112003c03c1001800e80c00c00080c00340719808440c00e00c00d981d1140d042c0750803a120401c581c8040b99542020546051211000b45440350054140031003200c02040030803503a1748804022150040c026610b1000c056042c400402c008103848405141810540c88140c0d036400090001c5540b16034444510003607d00800140d610014a0075030745041c01d54038200504160415900c0602190038448020403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 594219748 1250 594218498 594218519
    0x10b0a0906020102120109240605091306030b0601030926030103110415290315090f0907030209060a17010506030f01060602030f030604150b03040501110304020f131b0801030606 78
    0x41c2c03515105c42c100b0180e0300e0041841c0203007036103040162074032800d58140642c1e00c50000341d403c050102615010344c0c0f407403070906010514080309808001e081ca842c50520001e40030080c541c2d0803003424a40441c001c50039007410740071002c50b12001800110000b02945006510790082c5d4100e1380181070001140303000000340320a4800c070602420741e03c854044140080700e891280c1120003400861028820248c0c0c00d80d005c2c440d4030581d40000b40340d50790701d0203c1503817514107485980603084880c4080c05041031a0110b40e18212400000d1084140000003003242e1901c0f55040001c2112100000c080c507041a43d0038020542518028040d01030145e01d03a103400414007519023107441a82c000c5240c000b214040081c00d4002070f0500b5442604c40d880701040d0904003543c10702901000e0b01650307a9040614089086948480882c1e4003200203000300b00c0981d43d150154881c00b807064507110b4007591107840b10001040351307910041b16014100c09404900b40d1080b801410390b44079000420403d512540713840c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 594220998 1250 594219748 594219757
    0xe040506060a060c1505150d08090312070c150203280207210803220b0108070504050408180f10020a0302210306011d0a030b060117061005070503040e010b0a0906020102 74
    0xb845ca00540001c0c180302211a4442c550000080c1c0b2244007600720741c03000440e030030310a500035641040080780f0a03240307140501403005559142a80c55180411030390320303d1a400c13003078440c52220034048007215041c075000340225500e0000c0d40c8400e01130800509050004126400d8203440140300e24a004503805140c040c96698000420840c0305405000b81e60f80d14440d400102055181440c1c00085040a68200891081c05101d000303c080a5030401c4117441c44c040c0240c4c40f142c0f00e40d09110601010408401c1200c4c2c2c600c0320181d45607c3c03031038681b010400401c031803864a604446205801ca0010303901094001c1e10030300c2907007529003940300351003808a005038000382005102c1040000c41c00315805448861400800c11011140562640340080c000203020f5005135590992a170030080a5a0701c000124030024420070303002d03454105440807541461404000c602030001c0080c64034103001040040d81c00504001c4030281d959070710782c24522451b807c064520004100540c1c80410241c0c018025107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 594222248 1250 594220998 594221003
    0x81c020d020706140f1906150903030807020307031704111503150906030c0d1a0c181215100302060c0109020117090a020f01051c2903150c040e040506060a060c 70
    0x100c2e1b251070541071075011000e01a400303030990390301000400070f2420f03c500c89028040e0311494503803490350030060714801c1e0007080701d41190000c00c1003800080d04a190201d40c200c02c00c0341d0034419650f500e40280b41100780f01000e60721280d0109a05000c000080007540301da4406000c2498140700801440006101503a00a030325401c4417a5075181c0742030a44144000c1030040f603054511400d1242001d011601c1034132071801d8003c3c0007854801c02100c0707910045001c2d00c19181ca00c1034075980c003800c84e01c4021010307072000b05211030310105004801d4001c3c1c1e88051500180303115641c41391203810324004c203c07400d0b040380420b82010500028803110340c0c210b0b22410301e02002e4203120f07105508100ca00030216205505124007809160301c90b091207440d10940d025a0140090341e14030684407860185034206a41ca0169441251818543c501282200300008009450403564075106200802409560054040c1c1e8030480c04110900c100000c800d07002d2481600c8030201691103030310884003510b400c0c602 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 594223498 1250 594222248 594222271
    0x703051537050105090d060902090405060109060b0403081b03040b16051b030a0b070302071a040b06100905120106080607090611060708041101032904060803090d081c020d02070614 79
    0x1e40c5c0e594140000c660442a10511000510040aa000a4102c003043d07a090b01c0c1907000100501c06454140705c0d0b05e018101c0141000c2c1814603540d276401c0b0b030348545403c600c16010002e004204800040003543c0103450895562074640d10451007203000c0d101060425669072141e56a0f498895514100080c4030840c00f5020f03058012554450f08010003011300503104041c3c5c208032800c0841c10700622550004600441d900b103a003490b003055660000083c1481e03104105208981c0708060300480c0c0082100e5040c0d504112240012a404d40109902c0d44828014001c004c00c0041481c0d00008010640e10705441d6907050f51050000ba543d548000c03150540481c0340403002ca40400c41d651008079003400c051601003404800f030350329030f03101c51103104103042964908a410035061800740244000b40403088015410a05c41000242c1c4000751084042c0049500050501c0180c001410510f031610070480107560700c450071101440258040c0c40141c662a18045410704190701035043c25010f01448600d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 594224748 1250 594223498 594223507
    0xa12201503040305160609050d0201050606041211060a0504150e150318070803040812070c120302030c01060e0402120307020a0603240e0a06050a0e0703051537050105 73
    0x364006907480940168140441403000b10704900f4046150007440d4451030010550038200e1614a107006030f2920b4032000e5906001c20400c8640b502001d50b01220074400c16040c50411a0901c4101800c0d031011403604407a0006402100a4014000f0400c031a614080129841e4400e04102d401004400050f68009803001d80a000380030340c00041c40d001482c019090315000100d402c51454a545507000c0d84140c0c2000c50b0030481844240b10900c400180310b483c0071310300441c6036a5101803170404d029800c8881da050303e03a842411300c20400c3c0c92048000ca40200851a00c448a0035207483d402c0394124030807150000d10021645010040d40c00617940608211030090400b0710650141841c00d1030b0324a01005c1d8030000c030641081d20410001004070210084103418001404015101d081d00200d00070314921404000d03a0340c100108942c030500701e1900041d41d883d0711060108000d43c407501c1941c840941c0591401c803c40e40424950004a10205030076100038900032484070040c10b11945011820502 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 594225998 1250 594224748 594224779
    0x10203070f0b1b0d1a0406050f06031e01060806030709020403030818030f040902070c0b0301030201051e210a0c0f020c040f0f020708070b070e0f06070f020a1220 71
    0x30701480c0c1000100700c0c0b02c070240c0b0b0011041c0314035420181010214644807101002104410100c45c414000c2c06d80b000d014040c18000031038000e0035144106400396100000040440c10002005030800241072001f044a59481d400103140000580b079071446070060030303000290354400784200d80840768140c41d00035031640c030121501400d2510301d40d81780040c007080150061903400e200003000070382030000c1c0050320b0b9401800c02e404490740039000724141a408000610150ba000403da81d2800e05190864400e543e050391440024068400100800890240f82c40340200c00d20750035903c00d00050404110440210b44200c440300e030101c0c0c808025070010900d05d0b54504050300030301e003420340c800c4020404000610210b070803a03205140996000c10041802030400c0301121440e50425402d2401585216100d0000b402c2d002c91401c08901c0b40d20001511002c100c180c40d07940142c80d80060904103255940d011080b54000c41001c03c0342d818002d20135640ba01e11700c5c8828102d5540000c0c1a9140009805 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 594227248 1250 594225998 594226013
    0x901090308070c14010f1a06040f0e0a1104060c02040b0a03032106261c080609040203010e0a0302010b040c03060b0d05070908010207051f020918060103090816030806010203070f 78
    0xb040305445009079081c41c43e00c408400d0051032181802460001511034034503042e4034400c041f502500d8411103007040108409400c4e1041d11090300d1221a40504a0b2035003400c00c2c000340b0141550010201d0301240001d100e6420680c182c040f2402030302c1c2480f455070f00004110b41e0420714000200441c5207004204441220300588138132120040b030000888507158100c5a0b50300d212401c900b02e0032194691081c0540070705000001f460200480110400001800c0203444c0f4940204014010594440082d0a540d02500800100c001901c02d990a80009003002406481c42a06c07041c080c0d03040007103404a40388070b407085004032640b450b02c0600b0490303560486805440003500100c20070000b02c0c0045100b0500380b0051942070702c02c0c0020659411001c507031082c0c4a41c18465032450324410300801600344c07210383c1c41c6030042d45c011080004940e02c060050f4014900d4000180000c0b001040c070410340c079901140703420001d000741c0795454103070381c0d41e401260303644502100100b42258108110340002c0a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 594228498 1250 594227248 594227267
    0x304021f0219060603050f072304020f07030c020a170c090a0b100c0204050f0106021c05040b040b03040606210618021807120b0d0201111002071208090109030807 71
    0x3610503608409102c804400107100a0700003a9030180c0d4a2400300200842000f500b5019080f41c0c0190860303d180881603040400700c00c100c1e1000003416850b02c09075568aa04660042c6410034046455181c24100100070000001c41203004600c1a80b000c6126104040040c5004580307074009c1416054001c05d0141120029040e00365890b111902d0a10302c0d6030352451440081d526039240065801e95004210a0b140c019264600300c2d100c2c2c00041c095141d0106109005da51019900c1c2020680d00c02c0403103a52051354091840c0400200d00821030f42210320003140180d010f008140400390b1502d20022644000385880000a10840c0c549000508141c2109895a400200721181d05d2100d0300490a1024070302c0c416210f445000003000306960300401e8144403145a120f00300804c04c418004200070403c0010042c0c103014801200e10760040041151025410103002d040d511504980b03000030409160314140d20110300c00f400064524101442400385094159407601c410703031900d8130b059030100d05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 594229748 1250 594228498 594228559
    0xd0e0c1e0a05030613120314010b0913181109010501080601111911011704020108240a1202090901092f0306090303070e0303071505060d060f02090114030402 69
    0x100d018002401d583c240481417181d00c03060712000d0b00f540c580c0f62540080d5000c4400d0401d061416100c00140c089070303000f484c10f41e18581e40150b9216122400100007111020550040302d00300f00b00d0054440d403001e00c080d0300600c20181c20511011405c20400810001d0003001d00099441d00011681c0d8810280f0981c1d504003001600c0120410388204044c4d00c071840c03010f848800000c01000101e50b030107404120380c2400040d5840f854145030303000800750b02c0081c0046190082030348600c01c1c1c141c603000c100914504010090441c80b55142e603012100381030703071005a1183c10140d0000c0c01480040c0900c58150340d02c000d00e045003a4101c50a140c49101251040d146601da040d401d40841c0c07070400c80c15000d245501c0085860389840c10008000d0911001840d000f40c01c00d00c146400a1403c2c072403d40c026514000c080f03900da40310004a074000710410ba016080600b001d04042d40c1c1071190313000f004400d0082ea5000701e0005000b01c0c070491751005840094011108603828281317000355a000743d000a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 594230998 1250 594229748 594229759
    0x1050a0b0f0402190e0d0f03080103020909010903020a12201c021b04180206070c05150c100513170414010f17041506143109170c030d0e0c1e 62
    0x1a07151155104440030387c078210003080059005000354070344089020f070310024400091040d04425a802074490380910030080c03080c04081130000c07507039000c1c0a004138007074460051040074080d0040402c0e0346110f0030b501c01d03840e00030304100c19104900c0450305e400e00301100ca100c649000e0283c1e0a01c0300804218004000003d080030b041e10050b070301d000081140c00d00070760203203040c6800c00c4100440520354042440c4020420014004e01902c04102a440b03c2203454002580e903807a0f60003042c4003a412030703006203c2041080304400b102c010b1000781c0103840f4880c030002111240c3c01d0040d101a0600c41a510104807050340c83c4025807102041168007a00c16500341c500700602c1c10640094078010380094011500e80f222181d80c0341081c0800601200131000c1c0d07103400350803030220355101e00d849045c0142844d0315048050b0602030a807108000c68640240c036070b03940f00c010321041600da40085042100c1c3d5410040360403000080040c01404240c0024407008a2641440b90440320240200307501e034101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 594232248 1250 594230998 594231019
    0x41e0902122a0a0f0e060d20030705120a150b0406080d030b04061809111c02040b18061003020405031506010f081b0a1202071b0b030f060f01050c01050a0b0f0402190e 73
    0x48045503d04030311108c03117107800b099180c11002c141c03d0418940251b40540d041d206280410070000503110400d5800105413240c40f01c004035098060840308a01541090034031301e0025101d00e000070812807509040d42e0410401900d4020003007910400d00c1187c20340f01c5403130402c4e0785c000003135801844014850080151803508035001714111944440b040104552041903000550515005412442c4011901c01e10180c3c110b11540226043c00341100b8004d226154264040c2c0340290b0440d009428001d0464a441144591840090508484e4540045c11800b1030f034040b5802000d001d40106200c20038151007543d550071122441e0844152182001060003222191210358401004140d0080070002850364240d80695243e1025a00c05000c80300c0420800c500c8000d402586030700400300701c461070072848604004070740320b00035442e113640194a44018094103200a40c06840c000c40150781e1020180421030421040380241c45211900a0a98044103d036074403507901d1002c0c16000601d010020f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 594233498 1250 594232248 594232253
    0x303020a110703080904140f0408071e08190f14090f09090604061404082205040510050102190803061c141b041e0902122a0a0f0e060d 59
    0xd0614991080d11342c180001250841824a401100341c10401407011141c00e00b041075070412006c4004002403d40703a800308482007040750078410222603555070724020342419a41c0c00c00b03164035813040a0034284007843c840d138004118090000070036104215140c070f082610140282401a6000c1c0d0290350344100d514010b10407903070b2040c43c202e00403908100140003500d45403800ed4110740340f9080e00200b03000341c0400c200000f20845c0481c0c2c0d10740c6441c582000f00100d500300074a500700766174110747e81c4203041138100103a00c001c0d40e0103442190310913070031681c1491141a6014002e1100c400c040c003054400c200090007401e000101c0e440004407030409a890300b11648400c6000f081c2020002c07041e802c14210b0031495455400503170f054110403941044a0705036121106011401e0528820405403140307448020340d80c9241d980d09040c0c0c04001135070b407101601c1c6180c1c0640100c001c130709004000b41c658402014100002c01c20183c6401a000002c101c2c100444c4460141008200c1a07100b044404001c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 594234748 1250 594233498 594233503
    0x40602090607141908270a180b04062d09151409060904060e120a020d0216080729040608090c0102062205071e051302160303020a11 58
    0xa00b540140b503101c1da003a0101e8100380c1007044040d034803004184a0503188003c150020100d83c09403105a4400a14400b152410705819030f1300b50f0b800d9802440034600080300c4043d00808801d0003031078402042a410b0010410040750341501884140009a0078444644842e60743c603941c3e01c0912510010683d40e98001d05000e4821000300489d290b460140700304070588402c5c01103200014115000442031400b00c000c02c0f0030f001c4c001c0019107c60384411807441c4506c02400607420501101444699070101c000300a0f603a44070401d05040180f181008003400000d00c0076010094681c0e05000c0e100c890b00d002060811021103205845034450440c030100349050002004000500081d1181300c00303441c02001f25030400c1480c0202ca419034001c1010840e40241600a07003007039a84032241038034800b503d800d14a2a1510b9a080a001c02e005280c00756100c0d000c10b42c052080b1070049078001003914101a10805a004030b02204483c01e8001c8090000a402a005001c080705580b401002c95889040f00a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 594235998 1250 594234748 594234757
    0xc0c080406171303080f04030e03060f09070603020f04090b031006080d030c020607080f151e090115053403030b031b0109052e1d09070c0204050406020906 68
    0x10204800c1d5084510074201440b805900c008032101a01c4914510745001e80001d50080101007246d0b110300010b030030580200b00400c805a07001c2c084a405141070fa51103a03802809a900d03200d03c1c403820790300080c0f1034400d008803819186405450b90a1516142224014158141905501d801040310f50b41000c40e0300d01c102c0005105120007000d071408079181c040c089840003e240011900701008004440e034220000319003003010a007500c521035440b4620505040902e1005940c481c0020710111010800c85140e00c016001c02c80d070400499030303a020804524065400f41802144062201e280344001501500800d001040502d05c80b0028010000c1040e50981c40304801003560362150002ca814204090824031410300b01c2424030050050000e07101a00b40d11525100d0703c196030352040d80c0401030000780e007a521b40140c907101d2121220b030081c0032002024444030145429030068036040c0350482580e80109169280c14000e5080b030b07024000584402001916103640812544403551241401430 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 594237248 1250 594235998 594236009
    0x718110a03061a121612090605160806030d0503090a170705010b010e0a120602070506010303020d0e1f03020717030c04050f0303040806060d11030715081e0a0c0c0804 73
    0x5480c1c2c00c2c0001c000400c070002100f03d08030340d4240b20100d40001d8070010305030424048800788003002020b0f481140c0c6a0501c0041c103080504180600e02000041d0708401e014400d4081964920301c00301c0e004a4848604407403042d4554404c047d07201ca4a801100219040500b80e400c0e035201100d180c079020b0450240007000f01e0600000a2440140b00c1e081c402c01e900f04600746892007004440c2000201d403881c032401000000c44045070303030008200c8151304442404d58050700317030b91301da60b907030f04000c5d4075400300904800c04602940b60300032861034200028100259012a00110480701c25000c074029002404112148209003800240e1011982c2c040d41c400c01c440712b01e0b0340d40c2d282080309200c0200c07040c0940c0c1d4040e910511082c401414017042040d4400c0080d512180d90f02014100180d070050995416609070040314004130b120b0700c024002c802d124880e5221140651224455021000003100c42980700d01410b00100e45c894659030000c101005043c0760031044020180c50745071450b4840d6115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 594238498 1250 594237248 594237251
    0x50d230c0a0b094207020d210906060e1e0f0711070b03090706020a0b01030618150b1516030503100b0d060303090503030408060a0203060607050307030309031b0201020718110a03 78
    0x243c0c01c244c6004e1001880000c0440d04141d124141032001079070300c8180c4021181407100401c00c0c04080084002200d1020900b084188511541b40c00c088000300001e000320010b1130710450001744402100300c4944641003008078000800c0d5101c00c113070409018060a0001040f0034032900e4000d102c0104801da019010780c1e0000d0360b036800c120820528203140c6a110b2420341d000852503101080c0e004015030b0440b034000c40c000c1400d01119121f1509107590b400c000740040032450509194100719800492203450075160b1000c1c40000264041d06030013181d1b920076a441c0034541c0d1000091041c4003441c0c100c15174000500109448196005254020344441d030b1050b69211000c0003803560249090b001400154003440c03415042c40392680c2c50380801454400302540000100d4040e4980d0070840302d50396003120651791180c003d8940240a0704540381d080d4005000da4807482c2c0301035003080c40580c3c1f85070f05800902c007441c6031407240c01c80200782101a145855071010107444020300d0b0700080c245082141d80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 594239748 1250 594238498 594238573
    0x501050a06090308040314010b0319030206061f14092701090e060c03040807020405150909030a051804021306020f0105091207031b050d230c0a0b09 65
    0x3800200000307036110000704540070404101040d2030104503010359030414200da04004419004074058240c0011a6400d40304410310265140091400203800620917800d072009925a80208038007041168021280c556414150958850090240e581c3d0341c101041c1c014104030100300000c1d0140d6215000207909134803002d01200d003020007000240580241d0808106070004203401a83c1c584009001e10445040003010805002e8914265004030354010400d1000386003c00c1c00b181c1c14003150340b016010301a580045a41000040151102d00c02255905424490010902d46161a00603003d581040d0308100341070b00d80c44941c5540d000b510103600117141d80c24081100e84d08695004085c1040760b000505078080100c1000115118140c251805111280700320411803d5441400401410303840359081003203900d60031403010305458107907005210b15012043d41c14403103841030794881181a00901e0300503002030442d81c80d19410002c02400c980c14801210745440c10380c1341c8040c070740360381a845a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 594240998 1250 594239748 594239759
    0x13020310030b01090c1b0f15020c061006020309042c0d0216030c030f1514060a080102031504021e0c0a0c060c0c05040507030e0102040b04051207030305031308120a0501 74
    0x603545004000807001001803a40010000f85121203007180c0b11070005000018000b0302c07810f006155047e41c1c10461910600d010714550a00a5003d03c0e00724103103000d04000210707050300803421a01246e4158002e180740c4101801044010140300c0d0700c1120040019808103001345810011401500c034080080c2541c03030030743c84041e00c1c1c68020407000b840310107071007405c1c000034601d00d200d241102e81c400c50039080500c8602e04048500d11070000e42c82c80c546000318a1400e1644601c1c03a601805094690051480d11202c9140c20b07440101e500302c811800da100f4600340750078242d0051403441200d40700c15948030750020021110341c1c00008240016030042e4000020b0001212407000140300350704001e1012002c1e41e840c02c0c0d0081003885410f00c140d5441e0005001b031b5006e90022000b42c01e11384006c40d40ea03038450200351244d422a01410b0300691303d08000e00c0980c8070010301d14003542d416032142c50542d81e610085100059040200701d41503007040c04070b140b651f00d80034111800707440501c80106a035810700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 594242248 1250 594240998 594241013
    0xb06011407050a060903051603020a0c120302060c0703020a1b05010305100e071404150504090c0201051b0f0d05040b06040e0c010e06070c0506030f04140309130b1302031003 76
    0x512030404440340401400c0001103000071540c0e40c090340b085001c1145602800d00b40e07202e014811103000c0340070211a112081650200d8209145441542c070015846d4039581d601c4800b0902c403800a01591000003c02d19a03801603020341780180c3701c0d10459000440541e50750041280e44c41d0500a50303400321405104968050054a034080216079580e060300c0d2401c40b102c0322541d400f5001c00c041c0005180794048030508007040b640580080c090710248603103040d00042c910b9104c0c1c4960380e000c0f407401401c160000d00c1070280f10701a900d800300e80c00301c3c400d03a19032114003940801c181c415100f2080081c28001600c90085038482d038094603240d8801e1424000303000c1070b910007000c126102d4004000e44206680c20490030f40c2d03a10300c192005034a07082e07249080d50b400022500300550058020040001d452102c40c0c2c40340c400c0c1d00c01c0c016036280c070b00b055000356035901503a16801e91041c0003c501044140141e4000621214010070f1007010010130a50501244d00950700201c00b940070150034020b00005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 594243498 1250 594242248 594242267
    0xf0c060702010b130903090e0c04031106032502010e070b071101020706051b0f060405010507170c09090702010216050d0f0503010509010e091203160e06031006050904090501090b0601 80
    0x1e0009110b001556070001d51500107502898005542c0c0c0e6410030180751081400740040c2090b130103d50818148040c032101c99800130300c0221402d0b070390950380d000075081a0303043d203020f0003070b1111016101c4283e401802900008588903002c5640c0d40402c0e800354102048000c00a119403080507560784401d05080400001b00d4039001d0555111031401c00c070040d0b03c4002c94400304c1640800030360900002421900b08001128084100e01c51039062005200c07044d031103580102407076119901d0400285a0718403215500325041d000d41482445031200c5420040e407016480440c030710005261070b81501e000d80b5400d1007040207588a078031441c00405000d8000038903905101c681d050081c159850030002030480c1c1014040c00c288100150007140c0110350801c00ca80d91070001c00041501d07403510481d04200d40314100e00d0340300018480030781f0010609110b0100c038001c0c1140680c0c8004242001c2e41555140e10a25510f80c00565030f00078040854001e11441012078400d00810101d0304025000400e000d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 594244604 1106 594243498 594243511
    0x1020a05070e0f090d170a0603020907081009110306190b04090f06140f301506010212040e07140c0f0d0806030c0d05070b0f0c06 57
    0x101d8204482c0f140c0440104640281d8407140ba5607940c040500c0f80c000821003000e0880c502a0170400f0556100e242c2c580d020441c6541d80e4003013510399a0032940da1000803a0401408028410f001d40b0700c00a1140d03200038488400105032038002da01c00503025030710030032420984604404402c4441707401002158005615035640c1d9107000c0140c0441481c505a01c1e1a00d440460f114041e480c80e540000405801d1400d62500305081c000c20f004181504c10410040303220214103008400215903500100383c003d4440e0391210558000d64450145c4642d066400c900b800c10303403047c000400d807001c543c035040c1c4411b0076848000c02600e9100440d0082c0034101070000f0f411041450004660901204040440d000001901411950000e00b601c20580c150030032003a01540d89080050512458041c2090381c0c051560340d004d15080f03a20280c61442440c0c4045100740240d0800e00074103900c0031 = true := by decide +kernel

theorem cover : BRFrame.Cov 594064748 594244604 := by
  have h0 := BRFrame.cov_init 594064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 594064748 ≤ n) (h2 : n < 594244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
