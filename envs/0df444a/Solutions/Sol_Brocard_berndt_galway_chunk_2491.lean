-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2491
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:52:11.305164+00:00
-- url     : https://prove2.me/submissions/e14ec773-9bce-4441-8bc7-b0400cdad78b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 447841726 ≤ n < 448021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 447842976 1250 447841726 447841733
    0x4050d111908030402040b0402211f0e0a060f0e01060f02010e03030106110601150c0212160b1c09110114120a0e1221071b0308072a 58
    0x181684426608a001c0c407000c500e9640e480e103003146050390003052003c0c0c032414540104003c50388103958040c400c520403c00d01c2000311203460100303403590b2849a440303e00d5452a1000109002c000f410501980c0401e00100d000b50021300454046c8500c41c2c010400c1c941c0b103103590f050345c0310203001d80c08203172a103c40100300542c0704005c0178245186e244004640702800340e0341d0f685980c000380c10000100d2403050008040140800c00d407401040d0f40d18220760001240300000d815070381b0262019000c0d0305050008002018100440342003100c2044c0b1040b10290307181c0e262041904840e10003000c0d00c4281100c2c0440148600076622415081225148109004c0e0015102003c050385030f600c135081c0034890800814030062482d40721308442400403c980202562150911402d8640352699020500607103041107001006000d4010340c49030059000d0302e6440303060b00c26040e0036880c0c0d401129000300100405a0103600a800364103151184515801c1100d01046001200c80100234423000e40120714010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 447844226 1250 447842976 447842987
    0x5040c02071a0403050a1712070306090f02030606030f060607120c0201120905062a0301090b030c0a0b090915031903020f030703140d2702130902180c0c0a0302070e01060804050d 78
    0x442e1019049442c01d641d03a4018140703101c08541e604040bd540c1d003000c002140e9a8000d070302001003030541c21451850014001201404040c02100000c2610710029220341c4074181240e013020741090550220701d0a00d40020009011540b00302d00186810b002c04400c0d03403081c00713808115584240506100c0d60740c2c030502201e0506030220849804c5941c0d102000325000d403002180a040299030100d42c03034800d5410b051400032410081c3e8010141410104001001d060540310800e008903541c02c2c0940310800c1e1141107141d05051590b05010352042c3c81780301d0107039140d2522054825000d0351701c1c4140700000140c9034000c0c203d014000c9141030030b8008150442c440100365100701000700041e40d540840184d9241560300740d03001468440d0700614400e501c1c111006c042e80c3d4108183c2403000c4201c40d800301e1003203c5885005070740009007001207280410b62a06076100586810100d408410790307410000e58070b1600d4416206804421030000c141d440c8503411061242d500507005240503220b1000840380c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 447845476 1250 447844226 447844253
    0x90907030b040606080a06150206150d080d0f1b120f0603210e0409031e0e15040e061f0f05090a151d090a0b0a05040c02071a0403050a 59
    0x105540d41e5081480c40e0340d00d22800010345200d070795081c81440d2001c2c0383e80465205800c14681140c0449040a0450703000940300e9000550707601c0c2c1c0c440c2c1e041e0340b80801d80110088100411040700440c061803a60b100e9802540c060264003414050b0114a090403d05021021110070004000328200002ca601d40d410400c0c03250b5501c140000c4066994442c0302d000e4a140c8040c40e1120b0b03900d1701114000e0760241400b110f42800300c0d4100300000300380d50040c05648403a001c004009141400111305140203800c0315030f84100140c0280d0301e4000414020290354410b020b65035031403e44030f0104035503040c5150091000d801441c4031060b8051506410ba6441c84c50070b00c8041044020407035001d1640740d1461410040808a00d2440c4100c4202400391190441c11082d4612004941c3c04014946c0c0d203418581c1c0200c41c001c00041c0340c020000c0480d01f8820580c201c560014103054412510b1540020002c08076000401102c40c1101a070100004602c154031002d005507016140f1500030074020549000b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 447846726 1250 447845476 447845491
    0x2130e030405030a05030c0d030618110c07090b01020115030f02041e02070b0f01080a0b0411010212040b03010f06080103150b011106040308150a1d04140a2904020102030909 76
    0xe0510342da580c0001d141a4400c0c100b15420f03040890740001c40c074403c001c14000403c2c141002c5c03205d1410700500565000130704004003007854441d003042035410340300011106a01c02038001c1d01ca42d40d454091010242004035142c5005610f0803403040f0b6030703a0007a0110030941e603200000000000d51a000c10001d0201c0c0201c2d441c21007000401ca00704c410451008002c064890030200c0301d24035040109980e814130583c424400c07a0000385021000400c0c00040e15070003503001c411341e1070150b43c2c0c0d40100c0c64101d0b51045601c01c3c0000040100f540b108010145040300d00720f01d404960342c1c1d2180d1041744c441c074080c03000410400270b41101032a031405981010004060601d04007101c900a0700045180600a82d0250f000c2070000080c0000409803c2c0e4020b0820020ba6010000ca460541e24502040c2035013083c0111000f0440440c080280e0004114603400e14035007200c0c020059802c1c099414080c40e03240384510524122904030080800111a100f503070140c001c0c41c1001c07403580502c01d800300018086d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 447847976 1250 447846726 447846733
    0x70f08010b010e041a22050703020c0d200f0313140123090a090b010f0203190309020607060203041407090b060d0902040e030a02010608121201030f0501021306030b01030f060302130e 80
    0x8001541b0b8248008108114100c8500480070441c02883c040f02c2002c0e10750000c25004000502d4584030004500c221145545442003010f0010758080c41e031404405881d00b00c6003c6d0070b442e0401903400001400c4c1d001d44136a001860642d8a000d42c080300d11030440c46c0c5010425076840284410151101809600c4000001d58030309943e5000041c1c161003039400100c1c0c443d9035a4409440b46d43c0c410300c2c540c801055800154500f540002c0e800d10503480603040d180816454040403821501d07100f00303480c1540d074000b106540f281820329003000c00c5440c6866444161082a0001030744425034041e03009030703c80152003189020781100040d400740c16540400c1e60031039110712501070000710400003420b81b034a9030f6000084850030948250b08040c2c03500240e00074610705000c0030402140f08800141140d610004100c144191031030858068000c0b248a01190740c4806400582c980e0550040c0c0700050003641c08101e0b03844180810411074a0300d01010b90070450301e1911840e04009076010000d43d40400e02207 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 447849226 1250 447847976 447848021
    0xc0b041a070f02100501030b27010c020a0210050306011d040b030f010b010906050304050d0323070c02130e060a0203070e0a0807060e060301030f020f060d0509070f08010b010e04 78
    0x184420020280c07103200000b20b4074a107100d400c990500c0008030134107010f4002e03c040d502d5616885006100503080e0013060120000309101a810000d001080382510341c000d000c03c40348030f03002035150300c983d10041c3e001d591342100240e0300364403403c01c0301c1c800c41e0144c480600d169421180c1c000d14820b0900f26a412031b980d960101201e540030402c002d0340414000010920782c8684000400340c90042c3e2000d401c0c418284117000008501152800010b42e4901d40060061802010324410310030549008503001506014845074a501c58258003400317000740d405000554800380700d401102d501081503410b541062000c91914941a001550065054034054841f84480d40005012000380e510880c500d40c4406010440203400031001e11b000d450484486007950f2440d02d9400b800e102c0d085000348500301c4078545038401d91300c030400d40e4404a4520340420003880d0608803a40d0724500e03401124021811400005243e03041401003280d510010b80d13400c04000c11010038440540707009d000402c13004904420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 447850476 1250 447849226 447849263
    0xc060c03040204091a0106020705040603031407030e0a0308070308060904030806280b03090c010504030f080d02071a0403110318120f0609070311010207120305071104020309012405010c0b04 83
    0x205c0c4022558400c900310019458948080d02d40203082d406079014038200380c002c00109410078103d50600403a1040140d9074030403850100c0303140d401c081c40711303501c450b03901000f01c20b01038038202812001e44641c840420a840d0f840070008000000c0780c005000078400e000140841c18080301e488040d001c14140f80b00c01c4c1404080040301060181c115419500380071041003030845007086100c0c42c1c080300307090040c40d20341562924590500b4007800600341040002d0144401d0081c2d82c115511603401c11004c0010811034010040c0009094034194001403511310900807171040881264507040d20403071280701d410100700a00c0b802c1125132404091500501c07542031050f1000340b1581e4441d01e49a00901002400c40c0307001190030220100d01411988070001c140814030f00c40b0300c00d806250b01810310039204c0141d85000c03000c3c02260142e06406c103002105005c03a4840540000902c1d0700c0500d03170070110a611083c46440c409052003006c3c00101c60100e403001140d510340c41c0c19000b80c041e90070040303c84030a19 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 447851726 1250 447850476 447850493
    0x70303090b13030e06040303050a080709030515062701060309030314011202011106070f05070503090d1118061008091c08010315050601120c02010b090c120601050c060c0304020409 79
    0x66041c0009801481c0b41420942d2202280c000700204503803003030510f401c5440c01000d501880790b00c5030030b00c00e4140c041419a40600050340046512404640300750034001110f02c0c2e41c6c1815100c99000350300c03094111110b004181e00c200015501d05e10b1040c202d078a400e400701c020300b000c02429803c0c10394070948500c019800d8241103003c0c2840c03680101e900c505610005080c0e060030490044560421001d11a41c0c41c0c5c0076007400c1412a80d450030320b40340c18890814904512039030039031517440501401001c3c02c000b00070b20001c2060b001101d6640504101c0c00d0390b05010740d811900b01b0303404102c088042c403405004007102504188402c4c1107a100d00d500c2c080c05160010303a0101600072441001c01042041000d04800c16401e840710828000350508100181100c00c000484003400340e1125a5402024800d6200d010710040040c43c585d0f003804c0580c0d01d01090745c0f244c001c0c1c1c2070351000c800003e0805e5000307100300c421041c881001840d19035590799001100da013029000701c1c0e006445e0880e4201181d49071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 447852976 1250 447851726 447851731
    0x140306041805030415170a051801150e01090b09270303240d1e02060f0406031a060705030d091109011707080d020309040914070f090501140f06070303090b 68
    0xb0340045698070b061400c1820255801c3c82c411040080071240004018102d4602135048501804049a0340e1240c3c0c000e5070741d000c41403d41710459882c1821425a040030403407000101c508240200a040e601c88900209583c04404031a4020325031b039010903103c00e003402c2800c941895000440c0c0807503060700c503141d0440d4801d4481c40e0200c4511070066113029904400c0c00c0c2680000c54040104503590b41c3c401c140700c1e000e0f8046400500600400c030045d0b486910031038000300007401e203403a076690f1039100240c010302c001c00c0110001104968004014100340040b505410741290041d410071040d4446200a46030068045a184210300d510307403c4c0c2d07114528094003130400350000540c0d0303001310070105162480680c800342c1281d0100340c1e01e0f0440c98012049494205042c0c078085214160ba0412041151040c9480502c520a0040000f43d030802c00000c9015100705031002c0c007450340d1f074621880000d401066890760008600c1d0140b4924a48a0000d064981c428200400d044074980c41d0241400001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 447854226 1250 447852976 447852983
    0x207030504080706050313080912190b160e15070203070e0402090a2007020109050315010e07020d05090103022b02090312040b072603040515010e04031403060418 71
    0x441c040c4800d100030b025140c007810480c5005401c520b491000d500350988016030203011842d000440001c503803122003003800c8031030208044070140000040e02114901c9030b0b807415103800c00706d080820800000358400e407110640302c0da07684101034414410004000350001c5c0c04407000c1801c002c1302c00161420302508004264603071050b01580b03004e005020001800400d41d5038903034909441c000d541c0a43c0c1d4804520303038102c0e40f00340b83c0391119840140c400c45002e8004a07454400c4031464001d880c1c1c4208468183c4452140440d903607221140c00707990341d00c03c115030080030400a03c44042c3d0b95120394040c103005080b904036403001c0d079581c02600c2c1650303003404006104250001041c1d1413a080070445424070a14021301b02c0e150520b4001d1040c228010400001d0440440031342074184601d2810940001c080c0c454441c5030781341030920f40307103544100e02c01340780c21109800c87c0000b5142c9900c840141c82039801da19044900000c80d4a001c9599000802d49a40030355601e0010b8080c070110b823040c5007010f10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 447855476 1250 447854226 447854237
    0x603030c010608010f051609032a0909140d021906020706020a0c0203014a030313020a0e07020a2a0603060302120a0807080d09080a050d0e0606061804020d020703 71
    0x12011050140c1c2d60081c000e030f18140d65410048007d6038403030609400c8940103007290402c40c0610100c032018000a0050301d408142566001c1b501c06030680c04802c80034400ea20011000e81e2035020350740c0380c0b504461000003503040495032035007001c1841f006029242c81504018a070224940d41c0600b00d1300010300e04030010f0f481c880c010b001c40c00d0074807590700c003002d601e420103a040d0751018800700d55040440c1610b4400c5403100600c0403c1104c44000c1c610310549070141c039228940f50b424881ca540701101d0a0b4480c042034400020001030a00c02c00380a2079095025181104264547c0301c80308481ca8880c414800b0710000c00145d490040c18180064451036a02040c1c2b07030314500401140c5603160390402c515401c13070b000c450005610107003103c14036940141e083e52128200e070741140040c0700810000d030043e480001c22294440d800310040800100f0b40000300184060b412545a407181d0444517903410640802c07028440e80f410410a002e00b000003403001d80381030000480c060990300714070005c401141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 447856726 1250 447855476 447855491
    0x703020606032a0103021303020a0b030a05010b090105030a0e0709050702150a0501050906190e01091d0a08031f030503040b03040c14010512040302190b070e0301140f0603030c01060801 81
    0x107410b00203040101c10203904000901c01c0b43c3e0050080400715040c5034145640054130701c902c0001040d010000f0754004180c0480340b940c4001c100d01990044940300c510398a0100007045000034a4251110640180e40d003904650b15000759000a00010b07160030703180c0c42407102c00a0103203254000c00e07100d42d03610f40c040c0406083d2440040c01e2650702601e0605110708280050109440e0025084e0780300e44100e415054004100c2c50462021006d5007110004c0c0c4001c0001282c2004207400544401046102102136101d1100e00c041d16103014001c020300080f02080411a18001e41031220058480021002c504a0792039488618561041d8000c80315504040208420b008201c030404009111148001000c4140000001e0041c41450103a6240f55280b00110702070501c204582076540f440488003100144950600b0844900201d80020004031a49401001410180103a011b10414080c004007603464580400f0900c040052503581c0511003804181210700e1709004407002020141c00000341c20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 447857976 1250 447856726 447856729
    0x302191101151d072007240c031409030712061b0c020105030a02092d04020a0e1e0d06060806061f0e04110c0c040f090c1710020703020606 61
    0x44251a1880c600c4289244040041c6030039021441d103051032010110420f66104881030b5204400c09480183c003040071552820004000146e06003900c000400410404100303282900c0221607402c21500000c1020001e4000079001d03002c0603904102c0044290704089507a0082850b000a81d81311410a800098903102070141d244a403031621800c03003115030b280c2c048014010b007100c501c050f0000d041010000000e12244419810340d001e040d002841c440521400d4000403100811886c000045103000340c6103038401d490184212180d00340203032502155043c4a008102075881042030105280c080d5060042065950320b03454088076108000000d4914180741456140150007846140540c240d8004554101024055162485101c1c50800c2c141130030100410050302440340c1c01c0f03001005c0895414414040498161070144050b80c08200e141e4615641605440ba11800075004010f10541171181011720250782075411185002c580b00c8032540300d000070072039011074411380040e0004018000075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 447859226 1250 447857976 447857981
    0x130509010f06050304030e06120103080a11160909050a050d05041d010b030f0703060b0a030e0f0c15070503090a15020c042c0703080406030b0108090a080403080a0302191101 76
    0x3500c01d2500103115282440c03000303480e0744000f50010b002d101004007166225540c0404860510701e85d1111200913581d01c1c50101455008000610040348036840c111040c0140060814141c0014000c60b180c09840d2000f440010308400809580302d029010b10304001c82e0040040400c0560b0365135850340e8440c900011503074840d4443c4285040940510010000e000700e94094030b8012005c0c5100c0240d0340c0310140240d00500c03c5510104002e100429401d0301039030235038030424411801ca0182da103e1244400740a480d890110304095102d540d2102541400d04008040e001103482401200d00e40305240000904004495010303035440c0302c4014400c0e06c0243d050101500c0c000e4296802c0c04224848446800048031050624240c100101c50001203c0800c200c1a00215005480c1e66522905e91500501038140300a4007404a118900030600710000042c4001e90380f500441c800b07050504582e01c0c1c2c8581d500000c80c6d0b00070141c090040929110f2213068001001c2d540c0c1c1c4581a8070050800b00e6800d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 447860476 1250 447859226 447859229
    0x1406041a04150e0d0809031524030c0a06051c1a1f080406180f1505010e01030506010b160503190f050909010504110c0f0d172203120213050901 63
    0xc101d41d22043c0b103940d40b610a580030f107190f80107915984600006010071328001b04044003040b000c002d607051041d03145200f8031443e4081040c03120040c07082105410705030fa4148011a036034101d40307604401c112051140c0090030483c0d40380102c070840c2c0d4010415071402d40c1c20402c50000e56240d013205828051070030b0b0090509440b06032121b400d60308046480501007043c02400601013a032142c40184042409076458420558000a0b07400410f0050404409074000e1501d450080b529001c004682004403000301412654000d00801150b8204401818a0341210310000d1035004030340e00e0100040c0c1d00b80301a2100b0800c074191130114403101c05c00200100c04a10040b400d0200400c114102c1d900d036070412a055510955000c13801121030042c1e000c3c0c03803003200c1e00b04009003d620000c41c41c651003c501c112500c0c0043e907a02988648441c001d047d104001c0d10713a07881e0309030208500003038500d090f1208010b05e402030800ca50010f800342400c40a80e4042c2d541c03182191402c1c0800c3c04a840d000006a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 447861726 1250 447860476 447860519
    0xc06020706081b03040327030c1a0309030f130e0f04030f08070905010e030a080f07030201140c09010324061205010807030b010b0f07062c0d091406041a04 68
    0x10360031183c5080c691401e10001c0c10240801c0400072100102c0c203010005e4801140f4000c0e0040401039503070504019034283c0d030140c0d40c200203102e070b64031605044040030f0728024404000907518250f15140c41e040303164400824803055460242000071544020410f0910030301c1400e02080b07071842c061030002d145102c800e83c05400d0120b40300920110907403040c0290241c40b000e007031200c0a001c00e0710001c3c2c40d003200340b4030007000c081c0005442440e03448d0b92000707490840c1c030940083c0300a04096902003010282200d80c0d001d0b203102407080003500e6201c1d40286103038010314032848594040c540401410006141c00c50808680d0045040e0122107881c41340c0c0d801008007002801119085503121361a80a061280303082800300803c820345511403400c2141c0044d6804031013044522240c2e0b009010800304a07640340300b000140300c0d5520b0b500c1c0000c1481421282982e8a6009607400d0460104164800e6425150804001d10010901402c8600c20810300115400066200c03840c00301d42c240c03a0603c101000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 447862976 1250 447861726 447861751
    0x10e0114011206020f031510091202060d20030106140c0318060f0c0105040c05011707080a0f1a121b060702010509030607120e030c031207020304030c0602070608 71
    0x165000c1441010150540c0c4150401c2da0401d820303800d0800190080145005a21000100b8132981c0401d044407416940000c0c0d442c00708120507d1420b455800b103c0c402d81c0d01c90080c0344240c000600d040002824000b80c0480006a0408043c41d01050400e0307190784407582807000030040c4000b0390010490400d02800503511481d02c004560015100e002d50001000002064100c2c0d80c407541d20b41c41a01c20043c400f10f0ba203a00c9603603102110b4044c10094609844e50001018042001e500c111503c405401a002c110000c607111f4100c2181c10010052148049a543d08100640311509000300c0c4030703420b200c45d211080e50388080308008031034241d40a0608980d01091040340e074a010b403100580c0d05001150300a07110002c60005170307128450b02c2c0c0090361502920007000394903074002004200c2481001c408120560701c2d204440d6032481004c0b0001030503403080c001110319a40054005074022030610540341059920b99990f9103a0703031640c01403000340e0040c0c0c1c014040c0c55401030400c0c2d440501503111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 447864226 1250 447862976 447862991
    0x10b030a030c060e070b030a0504030801140618150403140d0c0201021005090a080705061f0609050906180702150901050103020901050112110a020d110d020303190b0303030703090302010e01 83
    0x1900c90340004030003d0196488049042000c00288182401010300741285a41d92429000c01002050103e9088010491540010070340e941d03a0401e00241ca4000340c010f524115100c80490700c8100c1200c506076200c0c016078221068400c06101070b0004500c43d150010701444588207040c00c00040b8481030080080944c082c00150781e000402c004003042e50b840010301c1c0e407102d0b640071741860466440030780700090004d1480f04014002030007078030400c4644c84012200d100c0961202404145115880014481d5007080c0720a203080303018507407c104010001e040e2480c8000b03941074449411100280076030801d02000054425450200381e00000c0b0500802840d030540c1d00064120906005542c10407910f06c48044a401d03860b0701c1184000c9020092984815079040c00079aa40618082c040c0018640f10110045090002e60b001c0a41c3c00d68000d5070030345d0b40700810b603103011960742c00754140c41d611844074000944061009500071105030794007069420040c00c000e801e5401484800c03480741c2c5006007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 447865476 1250 447864226 447864233
    0xc051e120c030a0b090f0103110108160509030c0d11190807030311030c010603140d0504030b0606070f08040810051f050f0103020c2d0d05041a0403051509010b030a 72
    0x15501c102040141038032911410840c0b402410348800ca180c200c09501e042c4104007000360301983c1268852000703c8094911840111010103080d18000104c803170800280d0a82805600034040680025007200c841e0010440002c03440c105074002503404030005803815400d414038a489580d05010403202c0e80365a0b00d4840c43d9a5101c00911020342046950001c01da0100740620803985d08184500c000d0200c03c0d201d0501c0b4042002c094102402c3d44551003094500602803400d0718101e0b500720990600c669240400d1010319486828229900d101c0f00c0400000103201a0240c80508440c800500900c40c907a141201162000381401c56180c40e0200500200c04410002905a4105036542a07c8058010043e40a0f0003810340b070300c0c1c8a0190107225030165619081404a800c3e14101c0c8141202d003080c1281c0c0c441124880500006008000c00e21070421148801c001e010403004415180660f280c030343d5403d0140000c8400c00112820040c050380f14000d0040060200080303001d440440450355 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 447866726 1250 447865476 447865507
    0x8030c030d020706020403240b120312070e030d0f0e010c0803040609030306090908071b06091505040f080f15090a0b190207030f180302090f0405100c051e 68
    0x32645032450b40010b062820058660140e40045074400c40d03e145410140c0910ba03094100001b18084082ca8034000810a10344844600c4a1ba03000d0342c0903503e0300d510811001c520200c0100124181700c580c6181c08810f8500304510784a00340035035a12040c2c0176050300006c00004101c100306041020300070076000030481e081d00b104e0f0810f40c40240003d03800700528003036001e0461580403141c0705240007104414800d0300350040072890311813902d1560090803020010086191800303210002a0454018003c04181510310398244c9201d09002d41003640e50550040300000c40d401021054005004481040108100d0448400031784d400c640d40d545020160780d541d80c00500d002520310044640880c0c0c045640e1000d04640c042004002d41d620921800d024101c09825403003c00061102e846041006040103d00000d582e8028807111254682c0000c3d240548405401541d80b03000d100d04100c601c064512841c194421552038045e01c4401c0c604008901010304840c60010010801070b000d51100da00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 447867976 1250 447866726 447866737
    0x3051b0303190c0c0c080a0203120412030c051f1d0106150e041401030305070b1302010f120e010603140d050306130e0a12030621022101090203030301031a0108030c03 73
    0x5140c00502030043c80d004440340f082094025200480103503004c10901d81c0801d00c451258000d60840381a0807502c8560780c007a10030351044000171401c4000d00c4002030703c1002090701190248003260b1202c150714041c1500014120701465520755075115112002008000b0303075810b000f8040c020044149840320406400da001d10040c030400890b100001c15560321030b4094041c540c9820030301c003081e40e104e207000f902c00e82c01010255038510300b0f00001000c1a01a070f0200c080258180d496030140d085402c410b80c0c000031010343c00c03102a41c49849144142409228081c0298065a0100280c1c0c0c40000320500b8955820309900800c0010002c03c049510344034800c00a000c00140c0c000b030208598440b06007032043d8500f00405400032000464080c99040c1c000405685000211000e0100c005820413000011408000d410500100e003040100d01401c0d60581e035140ca41c000883c0429440d40003a0560388243c20070ad408035244080030600c004251a01805040b00100079071402c0701401a8035134034060f5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 447869226 1250 447867976 447868021
    0x110d030e070803030a0f2412080729070e0a1a04030c060e1021091b0306020c1b010903141006060e120106180e01061203051b0303 57
    0x103486010034405010000e901c010101441a030740c9a0410014030340c00b800c10202d94009844c208035090400c08a5100f0009402002084a08202c0e01e8000080b04000720ba035015241c0c00c00900000d03011980e02c00702030b90b4050310707103402d1102d0540c0001c500ca03101c07102400340d00400852508012094407591114415241040c0c0c081c00207a071500085000d900c583e803c01021312001401c00548190451404444184221401818200100310884034200300300c1e01e01d040c141d100c070b1503a00c00c441c0f9540300700c0515000310401a0b00d00900e8007448210010707940100e4070240e0000e600036094809101d010000044101c031468043c803400c000921301c3c01d20b408050301e40710320260f600c0802c030801c001144808400c088284030792647c40c00080e00400002107850301507202038203841131225061081d00300ba41c2c002c000085c4017880401041008101c003881d10b004940d41c6580104003503403c40300c040038840c401c0c1d0300c2c0c0396655000d44103101c10100d11621162180d20600a201043c40c0250104c03440a82d07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 447870476 1250 447869226 447869231
    0x507080108120306030c0414040c0504050c1204170f0702150c150a06030b101706091c0201021201030b011d0103030509040b04140901061518140a0308030a050412110d03 74
    0x19244c0c00a81010030603002240e101e8900154088503109920031540302d103018483d40044c15a40380b0078402035403401c6030400c0b08080c041200000c81c05040300c50a070818003581d8601c5030f0000103c0c07e802e0541c00b00745440c00001000c45c02404501d4001903031880000100c80fa2410407444510591f510003090320425501100038000400c442140c0c1d110000442e08038000e0074941c240780c0c02004140000f800b8240708800d00090050324a003000074941e025064810090501007400680003a0742d00b0a20590011075400304406c0080c400e040005901940c024804483c00d035152030003524220984009031841d0310703100c1004101094105d0107441c4100c80540b40450444500b0000400814416950b1180b400c910b000f0302c45000e8056214000b030303680501da03c0d5100318022009942c0c0030108030020307411000c14201801031044146104100810140401807207589a540c0c0c0742a0303410884510078999540c20402c414416030000300f980401d81c0313061698a110640c0034064440f01d84081200038542c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 447871726 1250 447870476 447870481
    0x3190e011110020315010203121807090e06070e101d06070b0702010c08060a050a05061e0c010207020906040b06121902070302010203040b010609060539010c0305070801081203 77
    0x34056656a4001401903042c0c03003030760380320391001c40c0290400d4510544500c041d8641c0700c0194000411110300030710040010020ba6192001c200102040c3d500412080c0a0404006144001d070300030001d409c14608017a0100d80342075940200f10325545603840d4030a00c88006180001504a5202e07905414500090030030761142e10013240143c0303d502c800070440d01013642000b8041f0360640c4405203c0849551740700700c0b0744a07442004140740d01c50140344e91209595201308503915041000380740340a00501c01e50b4000e03c4081d4059890b41000d0802c295594001a80c0320441c5060010702d80d10a00440c0c00f007240c40c4220010980038065034015900720480702d0085111605030000f03083c010210450259a240e02500d0024040d4100b038908458400d11400081407240c043c0301e05509403485951007904240d40042007142c45050340a11401c0240d407a50000c1107c0b07441e1200f00c0321001740c03130300101c1d03002c040c0b44005049450050483c0100700c00b040050000400115482402100001c6000d40742d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 447872976 1250 447871726 447871729
    0x5040e09070b030f0a06050406260c0312040e010605190c0f02060d090b0901020703020d1b050a060903200c0f0613080a0201082508180d05030a0e03190e 67
    0x181900201d400d0000401041141d004c00351609116414500051181c6070380d4405000c1511880c1c000c0f610380099170451034454001d40000d035604000c25004940d001c01c141000b003410f19003482c031100d0742c0b140b00003000d212040d02c0d010001e0047c4290b24003a0300e0403a48410180c030880750b40ca480000c11242800034001d00190102c14582d02c3e40080207148e4484020401c00001d0200510032248c10b910780e0002221020184280c8022030303019000b40c06071401850303044a9001aa030315221480800c81c8142c00403400800030b80400f1445240d0009904000d0704001d07040c014440f604014020b0514a50102d0395008140d000000c0350031740d24811502c000d503002454500501c0700380c01d21080c16100000d440c00002400784241d600030303211030070591103c003010035140e00c48205004039046084105076031a481201103a03841904203550120000300141941d00b8400d40b02c6040c0c001800c08400c1c880200c105101c2c050907c0c1c2d1420046144c002c0c04107510b41010006910300b0203000d0790201203100c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 447874226 1250 447872976 447872983
    0x209070f03022208010f02070809010c050a0618140606130c090e10053303041103011503030311120f0a1113090f0605210c060a0c050d090605040e09 65
    0x80481503840942030341d0003c6055010700400d40b10f01440e56013810382c8662800f00d07901c21111075681001e54103180003d4000155010a205441240c803442182e8000001c030b6290f225901142035401c501104801d90b42c10203010a008150001e43c0c5900410240a03030765852282400115809138004510f80380e2088041e1240d80c42540b104900c00070700401c00400113400a4024141d650032614401340c40c80c80d88108001c00e812900361001410542c0345040784100c84c80c0590303801441114020141d4880c000480d09455000c54420f0500c0740341c031810710030503400d0701401c008416801c0c0d0240c1012050b09448039580c802a243c0601c0d1f072481070100c0c5d000b0b031b4030b504076000e8001090482e1390b4a002c0080c04000740c0030306110303200c2214600b02d1400c00b03101140c01040202d0708010500075050300001045410b5625240c405500b5229114081c921900d990014284580081e1146494005c490400d2810100c01480040c01c1050841c014052190000c00392000d65510b01116a407540d16003914170714 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 447875476 1250 447874226 447874237
    0xa05060f030a030e0307091103150d06060306020705060106050a05090418050d020706080a1811031608030d06151707020304030f200d0203030405060d06050604060203070515040209070f0302 83
    0x1054068005082d051582005100141c048141c080792105981c2e41c0303816044a402110091400404101160b500145007001c0c3c07041c06001414041588001d0b80c444003100c65aa2040324825004a070b02810b1080500c40e1354010070b11828014a13007900d0480080c9980b185550786403069945020294080b41303a102e40151060f0301200300d408034400094060355a54441c841c0c680064010740000380078458a000c0c0240d414003454050100b00d10303560707030386098a800460941d0144981c0c0386140c5800d0384030440c44020300320031014682d80d5040400c810169900c1d500003921480300301c51840241070b44100054455504500c40c1459600d5918049096200f2a0700241c1b0b08204000c00005001c1051041c070210307040410000c040b15880818008045030140c0003950641042c442000301d8140701c8001c108080b480100010107075240c4000440f2038100e504001c0040c0d00c0401d5034000c00c002000f801c07100040311221410070349040d42c0007500e102c50080c00181009510018000104e0094041d500c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 447876726 1250 447875476 447875479
    0x2601140c0d0b04110c0d09060c02090403050903060a06050f0906061206031c02030918060102100c020c030f06013002010f11010212070219050c04050c1c14010f06080a05060f 76
    0x2c0b44c0c0c07945011a0b402c58000c100c400e031403406100c0c45000094000d401513402c6415544680480d124603808005100000400035814004104003104444e901400303018032030307082d207140003071160300b400180145d024a20a40a0080d204c42d81404540e070f80701c030185c440341e94184d03006008542c1c5000100c0d0806090002c0d40e10b00c10005083c840301c1c940c001c0090244100251882c4941840020101d0f103207000c00e40720180940c205131038643c001c26240d000041001c0755801114082c451b0503004ca841c011704034245e101c20390800d80050111162410501c10000041c4006800803d10303050914100e5210041c028140086054107940d001c5c0904800181503000d40000c540760358401c1c003205061002120b2840060103070007a51003983c0b8040907034800442c1c1003002454099060000e101c020100034142c0801c54030203100c00c2e6101d00690b5011106020607103004503400e01200000c1041c0740c010381014010341d00c4850240080b03948070402c964030a4500102242c07a4031000c022a89040d0541c0070703203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 447877976 1250 447876726 447876731
    0x1b010204050a0e1609050607060c020c03030703120e070b1909050909011506050309071a07020a0b0c07050102150a0c091a0423010f05222601140c0d0b04 67
    0x18000310416105845141c0d8101082818100c161041702c41e602140951680b1441c1402400d0210781280d20141080380c443c0121030780326503404002880c5401442048000403600c8003e000c2c1c001980c000c800d038131100c0305c2c010884c69042c012404a14003c0c0c00d40f8021844052000882c07040c030030204100208800703085500a410180095030103049000d41000306561400b40000e81c61340b0640499109a100c0006069514202410342c001098030048803808140c051059401590729103141e10010300e401c24182c1c2c0e544640e40143c604000c42c2d0344c403081c1550030403685c212403485202031003a4028495440043d4076003403000d0596903a01d15411020231400070a583d00c42e900c00c40c00003071040c0c984548192140d040150240c0d100228608030b0140000c0c1410100e041250148002d031440e1302c0314a04540d8000d001401d8004d0b5081d60f41c0c814070021081d000f004444500e100c1411342e1104d03d18000744042d00114030f405514100141c40e44041440014140505c000303541e012407200300c0001c10a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 447879226 1250 447877976 447877979
    0xd0b0a1220060712020c0a03020f0d050102070206030a1d150f07050d0f06140409050705040c050c0a03020c0f010c05120c0c09010e0f281806140f011a1b010204050a 72
    0x18000e0340e440c0d004c480240c414035a203011285041c103802030440b640204151800c20302c110521252100140044480c0e6401f8041c000041c2e680401551040005900c0020003144d03000008449038228144001190001c00744018810a01a48a9400790a003080310342680c030703208021281c51040704810000ca514001984261080c80c0d00304800700c0c4c910f0030112807a075031440200000c882d58548024010703440b6200030400c40c10190014102e01505051050038540700340405400c0c0180f102c01140160071180013505246080c1803800b00000c0c1c01e29144006900c19550141d0b61142c072503160000c51130100b41d00f2190740f0100320b40e80c0b00600c0500141a00d5075512810101c50350295450390003d0f1104000030364103502c050403119603c6909003801c0c202c0d112300803541c0017010b0f401050050300d110740783c0600200d90f00740240aa2000c2e4555005001e1411a00c0c0c51205039041c5c00c10101241b250707410561180300d0100f40c50205ca20008030204001503c41034500900c661b5205540101d02c4400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 447880476 1250 447879226 447879233
    0xf1203030f040c08030a021b0d080309030c010614030303043002070e0601030b15070213020711120d020a0318080f0a03030b04090308011202240d0b0a12200607 70
    0xc040c0070314801e0808070000f640310f240840c0c9a014000444006a01c41d80e07820b007043e000030160350780611010708015004425903e4240180e030040340c09003070704e5000040d4000e1441d400d1107441c009100100c1d08210399100500000c1d100c0c0300283c006000c603052107410003180d41c0c170425403840c50402d0492105401c1d002d00e101a4540400c0c1c0b0981d4074400c0740c3c0d40007451a50084c055401d6400c4001c01d12310042c00b44500505254009480030303a04110040d03002140c02940f8401080d03d02c0c01040e00b00201c0c00c48408012204109650494164100c0b0392004021a000610030200c19894200310f103c40d4041240d81c4400246a44034060314851000500790b040c0c408544404054020798052000c415044107000c151081054000d0000d403c58004000e9000c1d004601d0702d80d24401071182d45840203080910004ca41d042442c0c1d00c081c100080d650101c40500d05c0f949035050415110040080e250140c001141007081c0c5020303004001059120a1032800c202d0140c40c0880010440c0346c580d10030b400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 447881726 1250 447880476 447880501
    0x60338100303110607021f0b0d0804090c2a0314071110030c0504140d1a0a061211151b03040317120a0e0f0102120a0605010801140f120303 61
    0x801030b00400d02a095505540301d020034024407070f043e00d400400c0030811891303c0b81c2c0d944203c0f030a2600100e0b51042e4480380340c0e0303502408011700c0c0d000e012a680c0391418070300c0660440d400f41000b6010b00c06812003010a900c0005503100c0211138500441c4c640b04440c3c1400c1c1c80498020fa0501200580010908100a1030007541c1c0c2840c0c80940d05400405226441a011a140d51454401255091008102507c0b4000c05451505006021b1b960f280c00c0301d40d5185c070f080446c2032800300b4615000e0104014040035200c1c400007801480d0408550b5841078654408403520299854001d001c2120450514000d40c01100c4900c8004070703d400c2c10814031503d00e0380326042400121200f441c5100142c00c110885825600000d04403011900240c0301e445184008243d0016529058014040f03c2003c02c8c40a1014180844100750751403150b141c0510400121456500310a0604c41020018000b4030200114040001010b0750088002d4012200162034607101003180c108521000007007152842205 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 447882976 1250 447881726 447881729
    0x1803170c010e030f160213090c1a040302010903290f01051c020f240d0b1305090a06091b091407021207080d0605060408070e0a06033810 60
    0xc030001c10160040b02080d41d1644180b042d4200800010700800241c41c40c540e40a2044a10062841c601500c5002c86002540d020030030640d498072001504125040c5944215000100d15070581403401e03003103174006031040040340406051000c503003041000004505881000460300784941080a2501c0500c0d60004c0f2024020b0034016842500200c91551141c90b0905003150700078445c0c101c880b00d000502c400d400f1450b00110b8410b40a149a104c0103000e01c0007854145c001e507602041c00320011090007403054200b4500390301e45190104200c000c44000c9817403a0110b40c04100231a050f4050f0404c0c601c54810b1100145000700c2c0500005403c100c10350001242d88401d0f50142416030b40c062041e40c4446800c4041d401580040202c54001120f400c01000b030b41522000000342c69440794003060280d007064201c400d095215400034000291041c0d002d6a01690002e001e01c2103d04654400600384104036142d03550482440b100c2c2e0020a2090070358800800180301450185404002ca41341c5460300e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 447884226 1250 447882976 447882997
    0x1a121302030f0f150103080f0d0f0501080c0108161b06060305010c051b0106030206191106040c0f0f0b0a0c0609171305030123040c031406010e0c0a0906180317 70
    0x300303001c00180101c142d280c981200c1d0410080d0782400c0c804600c900d116800710498010240c0d84042c2e41e04ac002c064400d50f4042c006000007011000000d1001404422018201c3c15014056007440d008440d0701407a0b0044c480e2000c000110f504040b072a0034006480240c000070001d50038450307280035456000c4003a0051507407801920100300c1d03d95180e1402c0310071600019410450412581d004444030810604600010f80341100d12440d101e81418142141510300302c030304c0c00c900c078410408650310351280000390540e01c00d8071a4040c500a403c03e1203200d901302c2802441202107800c1d0038000c995102c03003403a40e008141d0303210408245460840b035034440244008d800d220350901182c1400d052050300341400c222510708001a00c4d40e540038642c00402007049411a44410b00840041d0130716041286440d1100010f00c4a0f504101c00d0000441c0e008048030402c06c0c0c1031145021035984021681c00700c0b07501d400c0c86217202c990003601d44d0030300040b82c001410000c0d10800700c0d0060405a0b0081c205d1114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 447885476 1250 447884226 447884233
    0x111203070e150a0305160f14091507050322060806010c030309060f05010323060f060d050304080303070206130b0412021603031e0203030f0a02030c120703020703091a121302030f0f 79
    0x8542909841f0080703440440000501d05140c40001104030b00002d24030303440000c01584c070301c0c4411100f540740356000c50400c07500b540001c1b40206a008100b54901400d460802c24000254200140100345100051a45042041c1c49100106150003503200300001908440c041c000007004072800b101034102848111080301c0e0311542c3c82140e40c9035001040c0c1c00d90020340509400c0d02e8050752003d131400d0180c81a54070660b040c41c494001507040009000400c9100b002e90345034904104013138140720000301100002c1914540f1140002c8200061644c0320341c0c40944102e00d000c00300c03412031406403508040300181d42004004018140c21140a003080060201da507411000320740400c1341c1301d000640310b02000081990104a11295030303006503520503660625030f414542c0307084030035000e00c00944100c0040b0340d0018045045c9a0b05c1031a20380070300200f09550701e03c5603442c980740d110f034800c2000b140f00f0903030002d01140d04e015114082c00c14442d0014105c1300002035903500c07540c407400e10004108181c0b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 447886726 1250 447885476 447885511
    0x10c0807030c090b030a02130e0a0e0c061902010b09010f090516020a140c1801030b060a140607031404080102040806090d0e0111150a0606111203070e150a0305 70
    0x5100380100b800c00ca50907030301c0402d10391800701e104009401c040c0100d501c0300c0e000d11820322407101000c0c166004061a10030341c0034506001114204a60038400a1040781d0003000404106445000c200c52005030710100d621090300c1d001030101d004164101103182c2c00442100002500d0004181c85829100414400c206076283d540140e4034509403810000056003141f189407010440912500008290407002e640310040810002410115080801c3d0805907802c001441408203000e035541d409401a00c5002102c1c1c2007003102d0790801a5449032a11030600019008101486021072400c585001000140c5503612000098040d401c607002d20000c920a18000a140002c006440ca444416a13105d0201c840100c80044508090b418202e40d0310303100b20201803034100007580c14548981d441e0754000501e94185030000301081d00e01030f0450340c00d500031400360f52500c41e4041202c0d00300c0514184420180c0d400d001040032500001c0216000d942e001c65a12641e0340c150f0851031064400c21200042e00703 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 447887976 1250 447886726 447886741
    0xc06100503011805061308121017010203040201020a0206090a0b0301030828120921120605040207030504121a0703020316091211030c0a0308040518010503031920010c08 74
    0x149000d40c014206510400c08246c0034400022510382c11800b8540652501d0035000d65400d585600780d0f5040c00b05c494044082040350498180340c68050071180095240d41030680000b560b82c000c80704040e00c525000101c060442da03401080d54001d1480710b08503922507030b4034100408942c208020041c1c003031056803904034a81403000f00d040d081e005c0300e4852032007511120020400502000404894100004071020000e0358040c00e03189003151641d484000a0b505911507005444c06640500d0195006010720400030380c004059806460400c0c81c01a44205a400d102210a1703100c41c03031031050207030038090204182e8150000c3d03108590703030300c5c48940400000008841c2e00e00141b0500080040700b107030190019001500042083e00b00408235942c244150300002d1504206600c00c07982580f0000d410041400c10720030007040e401181d1b05d14aa2585040042501c901c2814000c003000601c4030444005980600080d00b0b0204c5d9691003c1f08003000d00c450280284803094588010070349420009415 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 447889226 1250 447887976 447888011
    0x2091806030703030507020409062f0414040b03010204150507110a0b030a24091e05040c030803040c0e16030f0b0a27020a02030307110706090b0702060c0610050301 72
    0x24020140081c02ca4900e15101107480340c000810881c0d01544030100c010100d2710502030900824412100844144030189668101d4050b02c400c1003280c8005100401441038881038000703211206540100705494104006802446181c0103440d0b0103200400100c9055841009058641d00c07444200c0e02c1203201b07508110b10103007a0710842194040800000d001c11f02103800c18504860344035200016445404004040385030550800384045907501e504420000121245003c400b00d400020446420951a40c0c9603c80c0140130181c441c0d400000450208180000060000d00c074074480440f041c10b105e284000d944004c1c0b6035900001e0b08000035400c0e0200e8038460325041403401406c0b180d00b20300d0b200710b080d0040342c2e033491403001c0811000300e20701408071400200045030356076000d155207103003004014208440c0440710180d1a0b07c041010710550b600b281c0e080040e01c80079980d16488440070310020705944248603c07001e8a019070428403540307a4900c80c48006a4204070003d008005001c2c801414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 447890476 1250 447889226 447889231
    0x901020405190509070c060209030f0105060a1410030c120903050a0905011b12020f01020313060e03031b030c0d0e01090b060411040317210702060c030f1803040f060201020918 77
    0x10b01a4034407005c900c42c140556000b5009501c1480c000d0b082101040000e400d080d001c00c0009250f9440d071007000388610b442c2d044203014003000c61030f0281c1d460350f60011910951100c2c0201c800e256803510308100b42c83c002c440d01405040c8510701400a041249401040ca400c0b605085022070099172021610b58040c0d03042051070300c180c060310b0003014059292042e051810a00f250154010491841c04418003800110310070441007401c1c00d00b946451800c3c00844800c080380d0306150f08244144002203c9804940c184000c14283d0242c036600c03003200c120750740d2140f81c004000652a0107244a41510103411070300702d55004025407142d941d9441b0901080d240c0200c03038903100010400c03041c8005050f20640340c11050301a01d45030300385684100b008018100c0c00303685c0700344280703154100802d0990400040da441645002e2480c00d5003041b10180721103c82c054081d0b0903118485d1901c104012040090740e000b030100c0201441e440d640e51401030b000b503101000041c0104280f441401c00340c64003082260 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 447891726 1250 447890476 447890479
    0xd0605090112170903060a09030e0a24021f0f0b18070e011d1e1c140307030c030e311d07030b0a1808191701060f0302070b09010204051905 61
    0x3d03495a070a00c607d0000c1001040440920004c82c1d100300c00d548403150040c0140162243c0444035422003581500000c0d0000d0075030045510261296052820384080d800c1c03c070b02d24030b00c0804d115100c541c020000d0180c6804068001510f014407401c58892050b8450240c98aa1550010b92801e42c00440c3c0b0101c8000301c450b22440050040c100e18203108a00d078110b201503c109901c0001e42c2c1001941c0b4410564891100c800707140c440c2410b000c00c400101c02000700d084011490851540c0d030241041c3e440c1748014050200c2514045000d807502031030846408032508d07000c1740c50701e680c0344111040c4804822104500c1d2800071405030b0394607041400d01101401e14000d20620745980e41c2c20520340401040000c4803030f2280341d00541c843d00002c1c40300400d8494000c60740c0700c100300d0300c09031803104d0782100700d104000504040540e084601c1e18030034151100c2d4a0208045c40000001f98007074452154024b2810724a14100040e400381980584291041120340740d521101040b110030408455000c0c25 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 447892976 1250 447891726 447891733
    0x171803090d03020f0105310c0311040216031211210c04080a06050712090213051e01080609060c18240d14090a05070b0d0605090112170903 61
    0x12016250002204981a00c07a00c11130751804401c0507001d00b0f403203055504040c0c080c500c01c90b0800700ca10100485c2c6512006100d00c2c0a030010036181e846203c4a03500c0050483e03d0b420200b18110340319070f01100e187c040c880c0152001064a0310b8000d0111282103040d440b150320305901028000198030840700e80600011115944a030f00b0b4101c801c00180c081c4c8140c031a44810000042c2c400401e11040d410b241c01003100040510704081c1c09401040c440311180100c0b80350040000041c0d58017110f0105a40c080c010010300c0e56902881070b844020b900c14501c01c2c010b07050b000050f070310318000788043c494002d0b0016a503458503502502c3e500b5001d407040c00c7e12003089202780c1d00070b28100071f00300940d900760703446031031540031184999110345074010301c0e00c0060240c41e61b180001080360000c040380c0000444004042024640d1200d986070701d1107001e04407181100084102da60407040e0080d00c068400101035108959507100d007400803507460401151007180103019a4004d032002000e807500c0c840050042c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 447894226 1250 447892976 447892987
    0x9060603021c150b06090402130e070909060504110711040b0d2003030a050a0e0a09020d1d0d090504020d0e01020a0f140306010c080a2703020111010605010c0f0c08010c171803 77
    0x802010790810120700c52001c89d0b03a180043c000c5039001199018080b5900c4200c0241d0804550340160340544d00154003640c00c08160301203d140d00c0084400c019040f100c034440041e04c050000b40548802180e00307030300c0500d250000091040c2c69245203c40e2040501e140054503569051680764050301c14500081281031020159888c090003243e610b0000051400700ca2a0300c038184003040383c0101c40b0180c40c15994400c4611103507c048101c2c100c0303142c208000c251040f14400003e00c0707952240130b181d0140da00429070881542068200c103004014100c000d5440f030900810083c000100c0d61101c40008542c030122800708030302001202c0c010541a0340c2c9071003a06041e1103006955004d81e84520402016074a484540401d0702072180c030012803100c3d8110043c0c50f6000060960314144108842649010020042a038000010b5410694805120a0090001c1c20102d19014050340021525401d18042c031a003640d0044a03080c00d0011212118156204c680c405602002e00140e0002c541e88104030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 447895476 1250 447894226 447894229
    0x190801080c061c0e1203090c0d08031f0506041202100306080c060c0a0b040302070f051503060d020d0501020712090b070f080c070f2c0c040909060603021c150b0609 72
    0x40289545140b000040350104c20302c0d007824640592041000c10f83c80700030003071106111040c0300658886000704e416841e031800c1911103000c01d21020340031a5007071a82e0041e542491700315117500c1d0000c1c58000c05040d21145d4a002505001160913012481225641941c2c03800502920414058426140041252039000024850350b2351045a10240a2054104050008031031429440c402c0d40f0035805404018075000203250015500e400c8144a002c0d880101e07140481c0340343c192507200004855160060711140045002c4403240d110144c4603500001d17080052010038540f451070200d2070781c0c0d8064015500c4003050b8942c020248006e141c0901c2c0701801000c01e0321030010b00070000d80c0d6400d50b1000d5588401042080400d540004100100b1510503112944080030710b00480000c045080c0d181d14206604030391522540c01600d0500760740c1c00c80300043c8103c0350310490140d91f0162440344c840001c04904204400003003022140200c842d0355201c2458064019250780c048064807580c100300c500ca0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 447896726 1250 447895476 447895507
    0x5070b04030509041a03010e0a05060a050402060403050d110c04020703020a06050c0d09030201060905090706020703030f0918050603071a0406050306180403170f0c0726190801080c06 80
    0x10300903001c010b002d000310502c41e80c1d680b00d03000140040b64034074185c02c00303250241401d5510307081061b469500402e0184002c540c000c0b0700c080e8411141000001c6603940ca2000a04074010741e00b02404c03a22030424820901500140407441e114800811602074004800030842030303205141004006800220980d000a03900390000d60700544102c4600c1d051030341848440040356015041503006030f44400c41041034100a1040c560000212000b03085880c2c10325801a5036400740b4440101000400101e04651511800031078000d0322804045101c403000c0036800d40c0203840203981703403032207805a000001100d20410b00021100302000c1c030300b01d00b080e2a0110640c0c0c030303410003401d040d00074540321103162152100340e003120300c42c5101c0d86800c41e403510045036404610b07800400c600781c040301c0c100901c40c01148100a43e1481580b080f00354501d64a01e0442d160400c3e00e5a250f1140c00324042444200c00340e15490300504291599180c2405a81e15544e0340c1d5910000340210f50800400c02c402c207114910722 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 447897976 1250 447896726 447896731
    0x801150f0e0102010b03030f121302030a080c0a020604060c0b1015050a020109140109031115040f03030f11092e0e0a0b03190501050607050d0503060d05060103052103040305070b 78
    0x5000005d007031011100800c1c10340e40403d03058110b2440c00038084d0100c519820700035801141c07109d681901d1860a5011940d01c4c20f4560380075000110124641084030001c0111b103006650160196445980d904400781c401d080030f901c2119443c2c00840042c04040140d060b210803600358920240513800710300425121940030500102c00c40d5211034903000803d00c3d4910300710309852404000101080c9a04005090a80c4a0304460081e0016150051030741c8140d01819049900014080c41100c1540b405130014480300f07011501041c2414401c2030804403190180518100035981a0304000c1f00c00e1200740c410107025064030345601c0816a40c61a94030a2140307001018010f006045041d1325981100c1c80f45c0c0045a12a4a65000403488119420903020b074074014a41a1010b9081a9403030b901e580c0c444a95003d00000c2040110000710b25a444003455001c2e940c00c4402d9801c41d503180e0400540301c030254100741402020b48917144d00c4905040007124481c81d01070f0b544a040c200c00750350320307030200030007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 447899226 1250 447897976 447897979
    0xa030b060607172203050303040201120b21160f030b07051b0307020a09060b030a090c120503030405060105091608101a12090118080c070b030c07030801150f0e 70
    0x2840b2681c0000c0030041440c03d5020342c2070303089881e40c2d010f0f40e032420150190302c1610102a01d03018200001100002540e030030581c2400d1641809080c400d4000091103244800380d0311400c0362180c0300d4080b00086e01c0d218000300310400d4400040c1c071088481d04110703041c4103180002e43c4440080000c41d140101d0b0a4100f800d40c074000d447c0c80b156026181580c030440c805440700c2d03040044c0340e00842ca07066400000500c16044140000c9c0d2070300e1203018003808014480094692191480002c200140912030003900186000203003407500d504007a6a00e0f0000c643c00c881030f00c160800401c261038407a4100380324001c40c43d42081d680c0349240c030840d8580805442c3d200c000022103c0850203031125100c1c8546031410f1082ea40d12038802d610802544480900000d1040cad242c41e060906010200ca60b4420701904071212958514180b60f190749401c680e580002d07402e90020091104010764440201783c440d020390307180c86050f40c0320310b4440c51042240b8045408500041010085a802801004e840100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 447900476 1250 447899226 447899239
    0x100f0f0c1d01031a0303041d090607051210050301060807050112110a110c0a0b120a0e280602030103141605130f090c090204170c0f190f120606050402090a030b06 71
    0x40013000c00e1460300030b034200d20f5070350604040c01c0191a03a412440f642c01174403c0010a03c1d400d00c01c0c4058094420701070f030744407590510070008080106280e0a0402000b0290081026039622072840d0f4071200b50f40101d90000b03850020350480101c0034007417401036100000020f40781c003030752090940f05262810032142c3c46004040b00c80070103642c0d101034000100b982d0090196291085405501d40803001416a10800d00d040100d216510740065103414600e0012078040160b454284500c1034007070340303001c000c200340c3c00000003104100ca940d049108046052040b9228400c0403011035040407954091950000c003181e4200076200400c4d0001440c99001ca02d000554a40a8031003003c0d9801036002180c3c0150001000c00044030b10309640e0700d90242032005010b000520390300003403d402d003508070a841a10701c0c09406810010305508000101a400e207484451952001803402c00381b5511010f45403549030800c00510342c02c0900807591107150040031403010a040d96541c80c0ca002c2c003d0b01d40c503042003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 447901726 1250 447900476 447900521
    0x503040b090a090e010912081e09030d1b020c0105030408030609060406030210030c0e15030c030702010605030607090306060e0708040209040507120c03060513050a08090102100f0f0c1d0103 83
    0xf0058421082c2c00f424000012038501d10b5410b002e460050000d800e101009524010009803000182d080f00810401ea240b00000ba200c400400345107014030080e5000280c03030104c0700c1d010300d00103400c070801000c01502901e441c148000010b507246c4c001102c2c05040352504000240c007600c3c103c84101e80c403d6004000052450321380e00443d6498440718170802c08207580e8180801e441d900600c0d0007805110803250600a01d181c2503d1030010f000c09000c821807030a020011940d030500079000400985006011580755190405000700b00003094070050301c04a1400e1004905510303413038040c500c41c08107030721014001e854550030300c09072450041041e521806000c0c004603880409204800744940200004920310b070550a040045410207045400c4008001030040000b400202c1c400750301d180c110b0101038882500c1c0f80180d050540c0305000300c1d100c500c1c0c42c0020003180c82c0c40c2e110b4843c2c5a00080d00300030004001905580da001100c8000d82d80c2e84021042c035602d98442d800514004140000500d1081d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 447902976 1250 447901726 447901739
    0x10903020706050d1407230309150a0e0d021e0c0a0b180319020a0b03010e040f1106131401030902010e060a020106120b04030210020a08071407050609060613090503040b090a 76
    0x7050700ba40c5640010700042601401c1880103280c005070740c203031807030b03d52300c0c508102060a0780e906400281e0b49001c00c000380040c003418503603408283c00a80100c240d40c1620b00c0900000e4442c4c4184600e0a003101c50102c0380414008001781c0c000000102500001419080214803c8960444001006582c144c400360f01400c0d14244015902104204840c0c000c540441c81040780ba4201c6405c444c042c40d10500042140f420b070584001d0b001a000800002500541d08141c0101c220410186401442c00070301c510351400182d001c0e10031070320300c02d4003080701d81c0e04100114261107050341c0c045d000a509070300100b01d5180030341c020a0f80101c24000040c0956850b01c1c00e9004540359441644d950200d030b4108810306070140945e01405a01000440c03428100b2172014040c824041c0a5500304a0b0f040d44244e800540d00049880c0140c222080f82d01e181b07040c4041726034071a8200c0722140901c40400f40c030621120203018504005510002941c20142040070704c065603000159065844150868000b914 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 447904226 1250 447902976 447903011
    0xc080c01110903070803030405070b210103110406050306040c090c0e03011109040e072409081605040b010c030203180f0d0807050105070c0803070f050c0312010e09010903020706050d 80
    0x507040060080341e16414000205030904a0982c403a11094004004020020300042140c8096030260703148151100303100c001d405581c031402803200d1a100c0180001005020300f640210072604401c64040c0007039a00c1c6c42c03d0644800041c1c5004185003050070003440402c25603000b8501d620b4107460141035640c0503d0001e42520450805c0c0021010000383d00c0380103041c40c2c00340780c1001607240c000f040f01c0c03460440d81c48400500301810808100d245220222031a101318825402405036a084075651001e502061200c5003040c03203101d2146240c0380009813107502445541d02d0a039055001741d0b050041358911044034502e40c180281d4080c507903400c40000c0d5502c81801c107211500504140380c581e1198039105007114405002003040c800350515603000689c90b041200c0e802030151420307420105195100742d950740100c824004640c0404100215084c0e070450103141212554840142641c0b5903001e034071308075568004050010380080c0e20622000380288010082c945000784000707030044400c0d201102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 447905476 1250 447904226 447904241
    0x5180a0f0206220f080f07090e01060308030c19030b010c02041503050d020304080712110105091824060c0316030504050612010501120b0a090c0c06050403050301080d050403020a060c080c01 83
    0x300c0c1c01c06041c0600c08914013501610150545d0303401000120130319858182e8401c1203120b0040c455031902e08010904600790403010055502001c06c540b0307410481c03408074543d04020041620110b030085076414040c880e000381b0b084200181c6800c03034603140d01d40034480940111003c101c0489440b0100000060040040c0014000141e01642d2180e043c0f99055040c4103030703588001001991050720102240640049400c41031090a005680301d400303401003166940450361040c1601008010422482c484040c3c03183c47d40d55010b01900c05e000300030204009800740545500c19503006000c520324069030040d010343d01c2c83c042e0070201e0a150b41e400010340c9560003003080d5103440414100411295811007201002002404404d102542082020440258151094404442d111500002130b640519000010107402020030302451509040142c02580280b08400541c461402c8055040d8881e80554040d02da0040210712010310782041210340c10500c0d02c003624680c0040288443c7c1403802d01c81e410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 447906726 1250 447905476 447905527
    0xc1a1201060201050f010905060303040b0703031b0509041401141002070b030903040509180604080a1b1a0c03010b03010b07060b03031303020f030a0503040b0d0b0604030c030605180a0f0206 83
    0x81c14a0a51719001d01c2c00d106030b0107030200c01e081a05201d07140e5404400e8030107079000c5941c51511460613050450151060040510309120180030042501d50b1200040481081c26103041c423060500108034115884240b242d55135910041d5101b40052506020110f82498503104403a0700a071904120718082c0e1003514003212661002508004909001600031b92211100384084000a854184d081e19140010401881c80c0c2001404c507448902030a4604000c403180c4501c0d882d001858901202441d01d1030000080b1441c0e01d00014120400c403104032410389081c0001141542d00e419154079142c1c00240702112a6911a041c103485510b080002d840007040380070000804a02c0c60060000f010680d5010b540a030b00b14041c3c0720080740000084030111009001d4081c0e580341d034070301c2c1b40006001c1d8041c05a4448030001e0b001040c40700029200c0260780c0280c0041045803a8100094071760045c011008000790421003541010854900c039000c082d50018018a21349482d0074000000e20301200d0088 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 447907976 1250 447906726 447906731
    0x60301090f050f041e03031b090801180528080c010b0f0312040e0402030a060606050c010b03011a0f0109090507031a06070f0b0c04090510090b0d0c1a1201060201 71
    0x1012076030950042c1030b003110075044503080c103082ca42c4038860515a800501c034125a200601401014465444181c9000640000c60344005040708010210f58081c840c010142d0b09041e105c001074000c1104240b21a5803080c02030120410500700107000149041c0d82c41c940215450015021502c02c1c0d0090914518000000859040709030811003010070100140d030184c2c0c88060340c4c440c81c00413a0308840a44041076801003080e0b0700e61001900c2c125905200404290074801f00040a41d00704001e041c166001500900040c1e0f030200502d4200e0b43d0540c071944182d5418600c405581c01c2c2080c41c00c4104a0600d01040036039201d03c440b50a40d0800c0e43c242c000650790302d81503a001d01a0104070b4040c1c500450300180740800c130740c0742c0e0100b400310040c01621440a8034041408100d030300080f00c0003030200d00000d000300d09e0500300508402a052080308480750501c21407000900e4802da5001045511542243d83d45082064411400e080d0403000b843c080402c0200200d29003c403690f4500030305160303001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 447909226 1250 447907976 447907991
    0x90c040c0c03111203240d08041a0307020a03030c02010f0c05041404020c03040504050601120f0b1206091e100906020a091502030304030503150d140f0f0303040f020f06030109 77
    0x1c0620680341c283c00d0756500004941c82c542c1ca5584116030700050307840440480300040310b000c0d0b894007400c5110b5a60291400e0300d54801c124264005e00308139655010045514241d0100003103040c4011100170b4010781002d1503400c0040d0007548074080030590740c8000103460b08800e6a5804482c0043c1c1040040b8402140c2040743d0308840254500000060b80c0c1541042c800542e881c0c0c1d00c0c0643c3c0680e6100d562500006842c691285001c00c000702e017550b000303020b12105424050010400311b6815070250500c22000000d01000142c0140110440802000c40010700010180c0da03101d040c000d04201e01400c004404210f8180c01000b413a1030180030b0060b0381e0060400301030b0983c990355010401d40d043c0000002c892940100c00e0380c0d4031a416041c0361782e0300c1d41c80000803100c105050045c0795120381c4100402c0d00b80b003907800c900850041b1131070880b9401100c2d009125030307503042d03010301c05402da00810018002581d01c07182c044007648051700241ca6813661000041040d00242c10031090140e64148 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 447910476 1250 447909226 447909233
    0x100e0405161e05040f020f0d0905190201020c01030c052205040b0a0b030114010507020402070501140a0612032019050c010906080609100306020a020a11090f0f090c040c0c 75
    0x2018000b4910b412100c14003440c410b0202d18900c1ca940f00d03d41c412a694246086120100e80464201c15140d0061aa84604058090b030041881d00410b5400b44038194098109500001c521292281c052700201104403924004401800c600031031031041245c103000d4000c2d4440170302084940410342c1c1101110781800c02c02480300b21038400c09124030560510104120704490740049030f041d6510308030340403004085e4400503143c03841030400081d002480020340c42c00740312065115141487c0115159542500d03a240c007601901c403240280300220307031010801c0d800640103250314525200300d00101001080b6410100b401c2c9886445c1d100c000d0642c8072005010414180041105901d007424140c000600b002c07001044840000e000c00d000342c01c04e03800304101c0404069001d00441d17000e2419942c8010041000351500121401150650482d07291080c4a207898940184102c1205007280d0070750391000d032404450744024107421094000e1244c0303415507480318000c030040d002e010340301c18800c0200c514 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 447911726 1250 447910476 447910513
    0x30a0c0212030601320415030b040605130e0f07081c0512011203050d1b0908060105060d1503050a122d031109040f09140706020307030305100e0405 65
    0x66030409040020000c2280f141c1c2c0044a008401441c89425801d003510f00300c03001400100d031034a01080d000702060001e082481a90f14160f503661540c2e040c0000c00b8001c0600050320183c0c06226804003070031082010078000d41e4401210840500c045401014641d040e0504001160704480610f400c1140301402c401254040c3c1c4910543c1450903d01c1c041100c00c400301100b0045c01040850100364080c04207142c072a0301920425508044100f002c0502c0c1c0c0102d01d000175460000002083c8921030006083c0c13000300d0200c0c12510701130040c80c40d1502400c424001441e444111450000f110a40440070540400c801c3c25180e00c52122100d82c0e0b00344a00281803110120a81c00041100082503118a146119070001c3c0b58018100031850f00501c05600d2054003031044100d80003441c0081c10182c0b156141c1112298500078941980111006101d1033744400f07942c040c40002d41d000300035200000f407282d4081544455002e4146504d242c031031030f00301c58022003654141c0d07003940a49018250036020741c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 447912976 1250 447911726 447911743
    0x603050c011727011518020405060313080f040906140418020d080d0f062301020601060c020f060d09060509161217070302070f05030303220c050303030a0c02 69
    0x9080c109a00314014240102d8540c000301000e070300d2020700a2103450300e04402224251041918001e01c18007000290540c1c03840111b2041000d80c06464142000c144014400c440c1540c901808840c51070f50b40c0c0109007422085110102c464031405c02c030100b07525060201400140c000598045802071170820000300412660039818419880e281c180803000065002e0440708960549600b500351401d0701303100149005802107030b1a07040c20480740402c5100b15500c1002170740ca10264808603103090300000d10544516154403405640b1103001404024082c5201514207031000340400b6807000451b02040590b000704809120807030319001604200007080c00f0300e6600c4400c1200403d2110b405ca80b14040c114000d02c100310302c0348003805032001413145003008c0c0368180c00d03002200d0ba604c0b280c525009664620740d00c02d590f0074003e05032001c103003403802000301e0b809603034000c5207048480040c3c41d44180003500c110040b40c0e06118481c2c0083c00380c0702400170314414a94050000b0741c2c03040c0c0810280c00c0c40081e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 447914226 1250 447912976 447912979
    0xf100c0e0f0405190204120c081605060f04120606030209130c090c0203070c0e06150405030c040c050c010504150608030c0a140a0b0103150b1207030b1e0a0603050c 72
    0x3580c5103003180c540e03105039114280100c80114490301d810748050f150540040040c0d80017400020b001c205078074482080100140f007019a05400c0355511000ba440c0c0040c05444030844145030b400304940d00d403243c00303811080d5070340001518090340c03030302e008042441c819030850703480d40c50302004c00a5280c5241c1c62540000710207080010b14015035144054200740b40030f80c0410507582c03254400194403c100780c49146902a001001c01d64032404500070700082102d52602c15110360141c41c1c0100d0f1321800392401c40710040c0c020500c0c000d048003000701420890400104008061001c0e00c440842405414003440c002c810842c103070080d600c03c820654034a41c0241902c0d5000f00045200a2400a0300c15107858104442c0c401d00300c0307410709460602840e804064040540040044103221064003069088000300c1310400c80c0d01c20b400140015286c8a1007840f5a98118010400214081621a961024104008640c0c42920790015000b04000b55481d4014941c3d801040c01041002c0024030a070390b00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 447915476 1250 447914226 447914237
    0xf032701020a120203130c08010902030c010c030c112d1509130b040605030607021501050109080a060c120207030c15060315110702060a0e090708010b1e0403050f100c 73
    0x1d036420301912802071078a6200b0f4403503000000a0a4001c100b400309055588902c41c4071800d980c0703d004501a0840d01c0e810792280c007800d2110441503003c0c8040d1001aa81511522100301140c0c803006141c0c50b02d803440d142c000e2103149400003800d4209504d001c0c0c224208519640500c5600c1c18054103415441072840d5170b00382004504165a601003220310710280c10320005c02e14415003800b04001d46070720ba0040d50148180c1c0c0c24080340035008100802c10056150524103280e985900458940c1b00b00c0c421002d450b008041c040d000326a407a04056000380d1035040c110008201d106003a4100c0c0d000d0301041d4001400c0c0c41c022420820601e40c11044005d000b00207100c0c03103003551914011248013a1801e40460380c4d404090114400c240b054800341d0b41c000309210b071500520300d8046c1c10b40c0420320601c5d00c985919400103034613a0160415906079245164907a0900c400040a040103c242404030440c010b000d010010025100304280100d035003800015018107628440ca02068a2841c0c6242c001d000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 447916726 1250 447915476 447915487
    0xf03110105090c130b041401061101050f0a0c020c150c010f0203060603180c030a0c1403010606050d0e0f0d020f0706080402132d020405010f17010e0c0f03270102 71
    0xb00004125400701802c50b075064003c0c00324440740c1d005103080403800390002c1c00c0981c0c64445204908280303048451644401e501200300010709400c0341c1c41104c207100010780410200341940744035440f40c0341c40d541d41d0040390a02c10850002507045030070803402200c95200014221007406082c000d00d900000111000e50031810140d001910034000141400d190301c400c40b4030361450070000c0120420310340f00038050325541245400c0c546582112030103246d5440702e00d080c0c0001c071400c051040c0e0782100c0850343c1e603a00b080a080b03100406850180145406032140c41c580d00c0e408101881100c00c0e52482e41c0040441ca02c413204070904060791544000140b024040030080581c031100040b0703000c81c209000000d101c0801d00240c40c1c0008400609031003030000c580038070b003003105640d005006881c42600e418020038080340c4119144040d40220040c40030f10207004100403941840143c0e00701903000020380c01d210074038203940030b15002182c240521554000d031113a620202103c90812241c4c07a03000951410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 447917976 1250 447916726 447916741
    0x82103090c010809160602011a03030a0c06020919090504060513050d030f0f02450d0204020c151e0105030312101703091503010812070314070f03110105 67
    0xa21100341c82a0501400a00140031a0018446115014110761041144c5505d41d840280241a400c16001c5140a81403590245141c0003003034039980412560740f507003040600da850030b02035000b414940390030030144416810303d40d0310540107001401a0420004107484e00c0d060000503120060101c4040801020406012a90200b006840420281800320340210581d0842005040450401110038804118135014545a00d9040d241c00380741e0301200541c510588400d50384030b04c03003042c0035482090001041090305041503c01c410f14002440182007040e00c41585041120030009803d0485840c02000030050346545007600800340c101e40c0d8203656051002103035403849003072851904401c8110006540000140c088406050b0103070412610340404603802e46d9940000900e10302c03404006450003401340c450001d5034125490070f40205400700ca0550880410742c003040c41a800c0000ca2031140c41e4406901d001809014810340c42011292001d044c010002400c2c0c03040800103074140303c181b10a8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 447919226 1250 447917976 447917983
    0x3010e0d0327170919120c0602030a020318120610030b07020c06030435180402030702071503060e010f0602010506030f0607270902030f01080712110607020a08210309 73
    0x12554a02c0d11103560744409000200c03404070b1850188000176403060040340b40d288043c0a50996413155007000c1046031203d00907a2203004204410f00140d00070710240c4511203200000700525000501010306050808840c1c0303082c40001c440c1404c004c04100010410002d40403d441e038000034a2014014003650640020514032025001030429040f01d802c0850300401541c550b2280c0601c00d04050300c00b005000c8021803500590100d02c0721481c1000c6200302801c0c140200ca1041407554040d2030200c2c01c04400c0c9001031051208032041650711400450589800d84245000c0e040b00d58a10304090701c0c2c100001d007540d4000701813034003a03040321080c904000c200042e810f8208119082c90813140b00d030b101c900d640e02c004208403440e0098801c040040d4450041e0b00550140912042300181d6030388680e43e40756100100d00c41e00c15415540ca1301500416800702c8500f00f02c1c04010711113843e1174102d80000d0744000054000060507001409410100004180c520104403030303ca606601354501243c05544 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 447920476 1250 447919226 447919253
    0x604050c060315031e07090b0603040f1a040606051c020f100509091602010612151a030f060109150b07060b010311040e070806010306080c01030b03010e0d0327 70
    0x340350101c00705004003040005541103d101404580e13421806201031803040e4580041039138640181040071075a030a213406000104200a000740740b03581c0700da40d10a0005005500103a6480c0304910800f410210740b0048137006500800e400f00f070f107070b04020412282d80f00010140e10510b0381e1894040042c0c44901e1800c00c101c8040b11020001c2c124540d00756210710038204c0c1640e110038500200140410043c00249000c0600c0d4000c001550b12a00300c26000c1c0340300c59014086c0b1502180c1c03c18819419004201d6650b8202c07500415203541c07401191600038030340341e825402d400641c01481030800c80d21071410110b50603a400e400c801d03d40340309640140b01c0d054000d449141ca03218041e04176402904204074008100003403e40e102d5981d141003ca0315030540f003400014600d0400f09016600c2801000f0a60394240d0241614090200054000300700003c4000e40554860214078005001444040ca8180450f100496180243e42032001440c003900000c0080d034440404010128954201050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 447921726 1250 447920476 447920479
    0xb070e03070f12061d010c081b030403020a080c0a021003020a030b0102060c0d09060209150424080106031e05070203090f150a2d170f01051f03020403080a02011b020604050c 76
    0x84008205040040405d1030055001c491360810400e00b05082d0300c22503091103a00c031900c6260360300222020f00c8443d44070549000d00160f22820201010401c0e1000900c00b01c490705040710a401c1943d400b04890461400c402c80110343e02141c0c0e440001d816005106603480b00748007800351442c142115400234010090544441c40d40d4007101c4040000b554100c0d001040d00500c0445854030a40007818581c0c040c4c05084c0501440c1d16015030100551a24500c000100780c907a083c5a1f824490120010041c800d0041001c0c02101d40c0d140c03031000d6030b21070940500710079406559100d070620144801c1218440110b40103030540d512075252043c0c0b5134181ca8a4210744d00d041034034141002004200008890b030500601212580000f0b000d0b40c0014000141480443c1c6440b569941c41d80d40c4d4006620074825290090002402060407040100c114103039225607081c0103007006d46a4a032142c240d045440080d0141c4e5441680d110004015820800750314103070310003003078a464282d4600b0b4680695a290701d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 447922976 1250 447921726 447921731
    0x20712030603081c0e060c040512030f03180c042915121b120415050f0601140c0304151707020d030209040216030903021906020604080c0a0b070e03070f1206 69
    0x40405004d50003400c88078103410100c1c1c0041c2018480816030394058428640300747c0107409520409040401915040700c012034589080d0366802440c00074030b03024886c11401d80d02805103084c489070344034400d01c000c03180e000b10604c1000080a0240c2c0c1c2003c4001445845489884c0e048801c03040d032281101c402810039125070034a91110510342c0524a5684040d00365180041444000780d10018402846180a8443c00211003010010082245d4040e5100002404400005944c950055012011152041075558030300300c1400d04450440d0881c0d005003d1102c001aa0382130b4680c1c1c05501c40c5103d035400c060070342c02824031880195840441c2020907042c182c010803d800591f845505490026480c0410207103150114a070007400318070310b804124880c9141035400f20400e03603000c0005060700c0d0580c0007028581c50355101c000d0310750003651885c0d00030710580c0004000926608400d5010b00c041d41c40f0008291200010181018071907040303400d0141d2400e0042100020000b0b46403401070308060700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 447924226 1250 447922976 447923017
    0xf01090302280e010b03100e0103081605071809060c0e03071a070206030a0203060406060f020c0405040c03020d0507030506160f0c062d060803090609060c0106030c0902071203060308 80
    0x200c5000b801c41e80e200c160806140d900000380f42d40e80e1401548210201100e85540d242c0321342d01d0382950407081c040941300311b006201d0345149003020755440c000ba60080045512080d41d6101c55100850344141100c4869150080e280030481e2500a15a01a0260070824400c1c0c4007a004203a07140b05910079001e400d0b0407140f0f40005008440115070109402a00c0c1c00d559141c4284140701952080c0c5480340aa4034000e03000408a22600c8000b40024040c4d0217410441c100c14104006018003070301c2910b18138900d81c0c0000050b07481111803126030784203c026180c45031031410241d0070513800503d281c82c042c19010001c060180d01c50005142d0380080d08015008900a0420704002e060516080c1860b211910340c440e45610b43c84100100328038000001d110003030301e4406c0251a802440d62242d080101405032000314500140900300c140303191000090315990341c1d16032070701450896010b035281d1540018080180160351550350b82c68681400c0610000703156a0302c1c8005841000030041c07451b40e00014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 447925476 1250 447924226 447924289
    0xe031e070305091008012408070e01020705061815040b03060d0320070513060b03281103010905092d012a0801060f0c06020f04120f020f01090302 64
    0x1525150f020190030300701e5880c824003025080500a00900914086007400380c100c035612444040070440c041d58900071280c0710070106403207801248415a0650054003004108c40d1030340800350030207242400003012140c504006200007042041000034004070200b01c280001101242140d400080690310701c0d81c000142e0030203c0c0c8441054900c0d004806a6014074640c0d44c0b400079006054070022a1070350102c56400d100503080b1042e51084030a003400c1880040c403c0c3c0c0084160f400c012001c0c12030030101d8100f002c0000100c4030754621921024001100601107147d0510602e40c1c400c0d1494000c0001208003800403500d5040300340c281c80703444c90520003203821000a400c0000e400102e400340a2508900115645e0707420048401c0c48002000c0e107000003403181c0b040c0e000b80d50255043c0c076400f59036004c0da200c24010b98440725000c01546070401000600c0b00c540881c0c800c007580922040350385d480c0c90b48100021034041900380e03410042111814009a61402050b00c82184141040003a810103000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 447926726 1250 447925476 447925487
    0x30f030c082106040e0601090c0e090f010f050103090803040b070e030f0a120f1b030c1208180f0c060c070f0b03041e0c05220606020a060e031e0703 65
    0x40c001010080301042204404401280a50214404501111141d902d01060104992400c0c22200c00380d80103400402688032150b02041c9124014075001902d0341440001c0384c22940c040c0c0d803d8000d00c49001c0100840f441100c419006418240f03800d00102d1003a890b1100d0500014001901d8a09020040b40e50305000ea900100001000b8003920103d00e9984581c0391581054031040d55032020402c0a444c41e18800c5035003c0c510081c80d100c83d84a2440203060344100309581208900384410009000c0220b200c2c40e2650071780f00b0b22a500c04000d460204110748420454000d484001c0c2e00c440c4110502c4040030421590500702915070302c0e01c90010540079450800c555014100118165038042000c41e00030340194440c6005908990844404c00409070b0088848500a00014404c0b10309002ea8038088009146006811280013000c1e104003807a581104c004d90b0018016030b00401c1480d04006090145102001c5d0b190069810800c1c2d180030f0580c2000c12000322103244c0000102c0301c0c109030068 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 447927976 1250 447926726 447926747
    0xf0b1c1a03070e0408040e0703231f060509010516081908010f03111018080f07090203010e06060a09080a0c050a0504051501031503050f0d030605090709030f03 70
    0x1401882030341081010003504005000840d8081d004a03840031400f21105070455001d151320a030360360718042c170b0824440078501c0c016041804064640344a81000005d40c80c140d420440001a00c400501301101d40880c405810904840e0462006c5400c002d0700e07400000365500b10750203003802d540e90b0300d814880f0001c00d4007845008000c2031021901060b001c40260400c200c0c2580e94603500070690b2a4020b861900b030241c403000700200d41507100c021090070010326810f0020305c81c0c02c200303c4840d14200783c402c03140180d40081c40d0030381c00f01c0101c090441080114500400f04060b08514550400c40c160544042c010211400386c0c2002962010491080e2240c1004114100507960300e03000300d1514020142d1345104e141d2044070802c40106840c90030780301e114003803024070f4184000011000015006000d5200115241c0d940d40340b000004074005115005242c20340310040c00c00d4600c003100c00f030f0866510360400c5008550740002c02012503040244a000d8a400001403803500c1c01501c0c0c100c40b5103030700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 447929226 1250 447927976 447928027
    0xc03210207050303060a05011d04020a0309121d060702010c0219031403071a0f0f060f031005090f1609050c0405040f0905070915270905030310050a0f0b 67
    0x55a07018090701101940c0249421500890095a80d200440d0340300221010f40805190034040405580b030aa4000e01d240406820003180d020b0311070315251003a00e03240301d1802c01304104052078a07421280d50501400c240341201c5160901e40c898000a05e40582c1c1d0724004d00880031801421260318454521800035036116090102c56415500c0a54076600904022500050f12800000750000415069442107142c1c0100310425a6120a0b04440000c040c14482c1c03c03507101e1018005c0d544050014047c0610507400200d0039080c01d46265242010140000f09242c2242544001d100c8504c2c80610827110380000c00f14640e222600116030600c102d81c8850703802440d2114640d817011b1250404d840707040c014419924403070354543c01c4400b5070700c000000d4428039415400610003016409918034444125009031135400c0020080401201e0392050252030982c000b00402c00010354450645014140540e2181c244034a0322481c00f001c0c1865000346c05100320003250400511911462240b912402d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 447930476 1250 447929226 447929231
    0x406110c0d170c030c09040608011b0e0d0822210210230a030f050c0c0d050406021c020f061006030c0309020a0306090813031b12030c0321 61
    0x40c4038115a603a520301515080400d1040d0074285403450004211407064003c046114030310303a1520f01c6a1815484828030917403060352184082104402407040708828415941140f103900071003e400b800180601a00038400d40c694081e65000961794400c0e039002080201100c2c4804115400401011803107401c65445409512444c00c9040e000040074501d40d8000e80714007610f5904e40e24219411000009410710b58815008000b0412080340020842c00e0745070b20f00020720804070305020040e00d0043d034400d20300711008100806200d20500990055031078074202a4985441c220300031b5207079860304c0e01e03102008400444625202c0c1c003e00c11100321025010603140140340500d0381480c518203074094200001e14040c00554514003d02c06d0b9810035800400c8800b0305171440d5100c00141140c0b203c2161101414040304000040c101c08120255201d0b0680c1d0034100801e4104803074040003a40982116940000c542010a401c84c0252007a0384c0c0500e044208071088203003001000d00c80c0740b103140c0e4661 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 447931726 1250 447930476 447930487
    0x5070504030503071109090a03020601030308060d06060b040f05010c0506010915091e23161e0302070201021528020c0a03052703030a12200304020108060423040611 72
    0x1040300e17441281350380c04448a0b90141c5680b10350917991b6503028002005644480d0043c80864011068154052401065010501e100ba49c40e1010b45d5104e82c0f0074940000d012900703120b441030b2003090802404080c43c002034620b0550311031950341c12041c418070100c0365a950b096849150300040c640e0140a032818140103808a00380e46018000ea20f18400c03600c0c500d4202d100030401b100c0c04601900500340001644036032504120314128681c1d41da444028800401c1110f09408050044240003403401c0d00d0058564200d03000290410b01c041000e40041c44083d0100124030103202008240280300841e00d00b000005c08075504000c0c4075055598915100311800e850805030f0200003019480602e0100401400220b421a4085810441c0b010b034150402c2c0045c0000354400c0411044c00b800030400455450110310250f41c41c0b01842c10b82600c2c02c2c9000080105558200740040d81018041d10100b080e810346c051203500e02d586080070100600d40c04800315081c06000c0e000300088a21302d40c0c101d943ca0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 447932976 1250 447931726 447931733
    0x9040b04020a050d270303051008070e010806070203090109092d0609060504020405150307020703021f0f091a070201050702120a14010b03101e0509010f0609020c100507050403050307 80
    0xd400c52030b84000e402d41810380140018141d00002203410718504a0821724140c5a0707001d078080d002c018075960f0000c120707440000c4c2d082d10400c141001400400714800c580c0d414000b920741090f10040811003554000c1202c84400d1760705c11101011a070280000281c01800701c80540442e0400e0010b18040b0600301071500c610701105c3e4000b02c1110008601041066903820074001030340076600c90954001d91240514030a10709907002907501107008d10665050903101e600183d4462485200e0b00b8200c04030b04241e8280d203030400079041450000381030940105180400c40010b81c4120b8074045069035000c40c1010031a4066020b039140154014500d19044c266015281d83c1c40f0140401a690750940780214840741c0010720036a403113050040e0140ca4030014030009203025211300c03000e501d100002102c00070b40000e5148201c1d0301036081080045001c0c2d051450b0402903460580084013070701d10400000342000300006040000841c00031011946a80381030064545000340c2d4405481400300140c4402003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 447934226 1250 447932976 447932987
    0xc10060b0405030106090e0d05070f0803010e040303050106080f0106050a020f010e011a0603010b301302031e060f07020a080a0c0611091e0613030308010810020c030d0209040b04020a 80
    0x2c0d82c20507802005130315601c1d034101040d01d4030b00f080440103400609082c60154454001401564000e8180045900e5a51340b84001c56000345d02070380c6480c0b40d010a0208150303041c00303100d004190500d800c0f11b06040040d40d0460000307061040c4414080c00050310b003692402400110110160400204250280075000c01d02912480780c2d500f070400c011008003019494400250b030706807500c82a140b800c09116841c01a140340d1012201c001508540000c42c1c40d030060000c400344103038400c094408800b180c0380305052802c440642e42070201040b901500300c3e0b04400295841d841b1001c5090850240c0b1210b00680c241050000003421280c400100301440542001c90550000e200d0030040008201c04020b01102e0b0050201c0168000f8000008001c0c01509000c405c0000e000100b03140d203800c50032000c6220b55585a4021800305d40140c0041029074414000b524135441e000b1010340c503140c44180303015201c2c03042d405c0c412a004d42c04150800c0c0c0d0780359580102e090303040c0a00300315036850a00401400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 447935476 1250 447934226 447934229
    0x41806060602121c02040e07111c140d0603050304030b09060f010f09050910062c0c031303020f060408190309020306190b150a120b03120c10060b04 65
    0x8085052400000d40c040c80060214040100984903074101030034000d0800700c4c1e4503540203203001c02d5000c0c8030204114120510b024011a05a1200342c0f2806000361f4160929100149000f9640c0321240d102e044550411035a1010202c2c0e0440a80d41d8450f04801800034800740d00090704034030010401008000b982c019150182072a8801c40301665142c5008540b401d03000d01440341b1004490342c081100f000140c03c02303600103019405481d84441030b4403c1900f260b444da40401c01060781205036003058502c0c824a002d100307000d0885140a031410f11001141c0b0310000d0b00c0518001103240a08080c1482070281e186a00704082c290340441c100703400c00e000076420000040c501c1c071080e1803110300064000d03c240c812050380a000341c101ca42d6822a06207442082814160480c1d89a0300c140406079246640388502000320302c00c01d901ea11907001c0040241012159025140380743c00301a41e21560b000036400448a02800400d0f55003019024450403c03100c0950041214100136000c00c40c1d81c1403101400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 447936726 1250 447935476 447935483
    0x1a0c15071b030c0b0a0b031b0109050105041a0304021804060f0501270c0e04020d060603050c0304240b030a050f060703021809070903201801080309011107050418 71
    0x7820451029040c0640c141198010049210154030000007078121903503560120304000000340303085d002d501090a12601c03a01c9100d1900c44c0f4240101e2968000d280500900000e00e0001e00340790501c46100c841440307040301420300d59000700003c0c08655488105d41028030703400c80c1802403030a180c606400030b8002d40004400803410a400810f004000c1503a40d0303d9000300200364100114000150340081440d26802d404206020700045203580311030005008990316040000f03102072a200c1c0040403100007070129160100100244070208140c00181d040c1174128041c042c0a03040303003070008001000100d0b90503030140107011042c030912102103001d13628800c402040d11b4195403194000c900702d1003108002e904031007000c5041c019a0415050280c4d1002040c03d12070003094503521600f403000840882c2801401790000b80b0266810500900c0a030b8102038001149079505020a0316168060424228100000c4014003074009200300320f640010840030700704215a00c8030f804440b041414030070080d0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 447937976 1250 447936726 447936737
    0x2803081206040f0507020c190503121201050607050307030302130e091b0102010b01020d030b03070f0b0c0d0216030b0601090314010603021206010e0708040c0b1603021509071a0c1507 80
    0x100f02c000303034050248241c00c150b0181026614080030081401c0000400c500700782ca1141c00410ba41d02c0c100700c04106000d41103000c0340c843d40310542e03400a002058218900441c814811240014000401d503030103542c0c142000b43c0c44000600c08501c0c0d444295000350b41200314001808440040410340c201e91081c81d4100404000f0b600c401a03080e511700d900c0203801613110880c418681c501c05d5120341501c2c0402801c0c0c03080300356075210080001c191138010300e600d20400141303900700031420442c0300100b04440c0042c10b1071503440c4c3c03401d80100800b80f1019251100050010300d65a20920500d4051503010b2a002c60305034000c04518024009404101c0c042e80c011038002e0600350f8001281da04071091084804c43c0ea5552040440300300320040d10484407940100408500000080082d0808100c0000f0700101c96580f410028503084130f480440c0340203000c0100740310a4400100b00042a5207090f20711000820720840100c0302485400d02028140c000d10346403002c407140110030300c0e02a242c240d1341d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 447939226 1250 447937976 447937991
    0x203100903120926090915060d050c07062d0513020d050f0a0b060a0909030906081f0f09060803190c0c05040c020a06051005280308120604 61
    0x400215428400040c000c20140c420700b1000702c04507048103c2180c41016025600c2501140074040503618403010300c858a0003091018160400d610039540c803860741081c4045030511480030808512902c221080c82e56180c2c40010301780e045110859910a0388184100050442c80030440b941101c07400c4d400c000b2098240c64811008217501826010720840d40c01142480ba05a08202c0d10000f805807c48042c0603580c51644a20320510249032180e01551030f03d5002d251503010803800d0040703600600380c0e01c2e1030310425201086d8000000025600c8905042e2840d4544081e0603146842142e03004a03020902c10303000c00c51511b100c074081e0071110188003c2c03003a1621382030700300e4a0340076684031501c1c07925214172140c030131a1041802c0c0f10b80ea4001c07a4814415034881c030100f01610300500300c00015034002000e61003041100c0c440c4550089401140008d86814200010381700203c280820f881505011007000e003181c41d22000c04002c2d81c0c01140142d44075514407408002400441e0000d209615041c00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 447940476 1250 447939226 447939253
    0x9061b0906020c06130e06010201060b070c0303080a0e0d0e03070b040902130b090d0314120108031e0307092912091506010905010518040e031305030a030509090c090301050c070203 79
    0x1d568145e060000c14410301801d0100401c0400c10080006045640302c1000107403101040e802021410300501038941000e045003000f070208034018009808c02450318210b10078200340441d580300b25041610b811040b5500d0640001d02e003042c1c81e0851403100704c000800003288070059008110052100c4503800341c80d45e4403480e1030300e18002c1c1c2c1d0849401220000141c000240f041c4100940112502c6405040c02c2e00758807428048070b0242c005081c55400040c04070032810b800c00d4035440048100d4801461450881c40041100f00d1038480e40003807100318500800d181e4410614200080d0401c8900ca4488940b0740c18042641410f6840282c5400b42c83c2c2880c815079020042d5901c0b8040c181c54001040b40741c00f004490307d5001121226040300b1008000c1d038241e076103026001d84c140e0240000c54481c8a1414a20040f1a039a030200384039606c140c803a0070000360888141c89014000301c03903080d11036031151a03103c0d0030700c104801181d040d441e146c00c2081c068200800b1308504c90007642101c110180021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 447941726 1250 447940476 447940489
    0x12020d0335060a050d2d0b010918050304050103020a050909070f0906080c1204061509020405041a0a03060905070305014104020f03030c0303040803010503060c0304080304020409061b0906020c 84
    0x2905400070160000c400104407000c005500c00960300540c20844074001d061514546c02039801243d00004076401080550700038001c4a00179404550f100d5842e0750156030311a40d030303c2548071b2203040c1900030074010311450088007654611180605450314515200c10000c120010144d1840003184c0c4807000030606601c038640352445100e481100c5450054403420608845400500c01c40e812034030b4007840f50424070140084401007491840250f01c1341d06000c1048140d80000216041303070b1103d42080c1c8020b42c0c4484507402202c1e0030003000a00201c0c0d50500c00c0c03d0149030740000e051507003400ba51344003910701007081c410070a071006080417a03030420081c5804002c219a000c01901e40c1c0c6480828058a00350f0f0040200000040441e0b01c1c0011120794541141c0003254203603840503000c00100030508003441015400040d82c1c036000d1843c600303a40c908149000280000e8091a500c5c1e440380c040042907440380300c1026110086d005809461840100804001c0c0a11300044c01040400ca2550a008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 447942976 1250 447941726 447941729
    0x311060705070f0807120f030c03090c0e04020f220c05042603130b0304150501030209010902070c05090a0b030114150d06060b0415030c050412020d0335060a 69
    0xd0307880c01e01d080e5494545428200d800d10054480c50303002c200c840c1c00901030000c6c420381d034003007902c075a200c0c40c000060143c100c03941c209170740080c1070801b910030f00000d400207400c4040e1000000382005944480c004511070390501c2900c81e8005541151840444195041ca80d160484951082c00502d0301c1c0c501c01c40e614050351046100301c50096002001070580c0d6402d04520171191811603050041710000d041449407117a2050007980000024041840f140f4251b204030509208414011035145601007911540c051103210380307440d0f01113450301c1000403980c3d1034070060200800d80091810f04c82c2c050b400070100c1d602001d1003036103800c00f40b5540c1041c64940f1841a034400d44c111140300d5080c424002a0b8801d050200d41d074560b40c0390081109030200e8050001b03001a84551501c3c020b840001508441910310200c00740181880304020f015001100261119415111300c80100c6092034103403014014491002232881e400101010075000c00580c20900121040e20101e103600c0d04801e101019005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 447944226 1250 447942976 447942991
    0xc031b05090c0a0c05030a11060105030d0206011a04230108060d05070504020d09060c0c02030f060603191b03080c2a0402090111060c030403030e1f0e0709060801020304031106 77
    0x500c0010b40d0b011084806010b4403845428001d0102c0c0340c2c4e075581c0f030955001900a0380800c00310003140e080d44104022003805000290008d00190041d200040d6895105104424068100c886c0c48446840b00c0420b44008007100070411500c03a0108035040303025004481c403180015001030000d900313480e00e01e038201030f450740080190201c1802d041c20300000e90312810142840f43c0c2c441d88100005141e501c504542c1401943e14001941582e00c101400c2c4590b690300a40998019410701c1403507138000c00c6041c42c440005001e4204580c0300e25101c484c401440035400904844810000144646031008004542c490360982d15034034908d04000001d1706600d0759580c154184c0d040d1009403401c1c254000c06281c4c0c0141051000003014501251400c00126990350028001100303000c10103405024900944c43d88001400080c140d0100c0300e808001d100303805031082a15413034801c0481009001803805050401002d014040d15410228080e5005642c101c00285046000c0c454100c400300341680640003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 447945476 1250 447944226 447944239
    0xc12020910050a21050a0e0a1110140a0305101e0b071a0403020c180613150b070807020f030309011b05011b08090106060f0f2a0c031b05 60
    0xc1041c400c40d055000356510200344040c00150440d00895001282c9000d00c189501181600e844900e10040d9805080d414140fa0311004134400001d240d602c800c54880c5003910004101a0300c840d040f1503202200b00c5108043c007000640e441e01d2541508501d10849940c010059215a120020a00e41c40f80c1e00100350020344104c1c050040321100303c000c104090042c0003145c1c0d001860143c0403c8298241c40841c0964802c0c802640c650601ca0300d011111801d2500c040750038600940810b240ca40c41c4c04001100c0c5030760303e91070f1050025200040000c6c00700c1980043d10740741c1516000106070300015081e407090140412581203454000101e408200068ad6a4820b039004081c002c10720200e1301a040750503540319a021104406a1426404601180d503500e200d2401c2c1b03c1810342c21541cad2a001b882c1085200c200722140250800d041c00003c0d0801c1c43c00d091810f07098130f020160140da0079104601601c4080004003071181c0c08100d581a2400740b500c00014604942c1c000b044c881e06071103025000171 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 447946726 1250 447945476 447945499
    0xa0b0114150a051803100606051305090403091203110d12110c030a1b120804021c03081501031104080f0d08091c05070c08060a18150c12020309010c120209 68
    0x24180c401900d04682c01600f02d84800380140300d6034041e07c0d210342040c0d000072008a1030441c40c01500340d8060003820705441d08882d5080c80e4070000d1006605024840c041150000d418042602c942038086240c851502a50140074525100501e80c000944044003024207109144081810704405c0700c0308240d5050065142400803042514070504100981044046070f6280401040d2400e03030104030724000d55911406442d0610412881402d09014003c880900c114624000b0741c2140c1065003107142039029481180708140120040c1c401070000d0443c5090100303000031038640c009008040f41243d0016603801640b00c500489810074100d5506a26500c00b24115071903401c042c289011050712854243e28107215034607220300e10600c543c407990303841d0700c084100080c5420030700c04c070704805842081c6a01e0b42d000c1c1c0d0703d607100c55100022503030308038a543d0000c09603403034020800c0002901d0300c48015501c0340b402542d01c2e4020f252481074000406e00c0400c0b030301c0406e41c03035108036070594030003c2125a500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 447947976 1250 447946726 447946747
    0xf170a0c111605191508040213050f07031802030109060e0f060f0109200c0d091d0f06030309150703020114011d0a020904060320180f090a0b0114150a05 67
    0x8215002130448035a064808a1540f08001286941c0c5400c0c1d100d80702d1500341803041c400924000441d04c22001e280c0b40038814032221288045400101d05c0c80d0210b180c00014903503403401092024000d5041d881d00101000f008055006004501c801d80107880d01e00b0781c12a403440d01c40c01c040b505042c0c51981400188204000d5601a800c0c900e2a105030301c5040306600c2408500303a2015040c005c06620a242c16414264019102405804058100d01c0f10303d41904042c0403541010308441c0b028481200001d030151410419038628100c0240250100840344244182650100c1301c150b0065003401c94690b02071400b81c010b14101c0310045600c1c82da070103444284452010020b068040f0aa0b0200032640803aa2a40030304005540103184103070041d40100300311840b101c160007034030f0b0040d401100c0d84282003000c1e404140d40aa900e00300b084a59480c80295400c01e0b400300070081080f1080c10000c10113200c82c502d804240c40040c1c81a0320b01c07200510505600c1d001d08001c090001d8001c100c0320b00f1303d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 447949226 1250 447947976 447947989
    0x714040602100b150a1214070818070f031113020f0705010c080402090f060d0c060207231809011118010f081909030905060d15090b010c030f170a0c111605 68
    0x6c20107498400581407005103031b015406c920544d40ca500041c00b05043c8802e0650070403420b070301907c1000040c40c080d4036240d5880741741c02040c400a0000b8602604105003034407079541810f50311965800131940c4000303800c0044503940105030241c9a0350301e030149072800c090050200a0041c0d4000f44401040c2d500c9012a200b07045000344041d400078100e051400019900025a401a1407240c002e44011400d140c0402d04803510750145c0d04602e04207110145403078540c0c07000081c44800c284110452541c6104030107014150b60074514915000005240300d5083d80340c00e54500f4608241e82e045d94100e0002400c840516041d2540568004600c10010310508141c1c00a08020b100b800c09005890359000016160f42081d582d910304551114420003c02000b80c40300c50240c10116003c11030103031000002052400c25540c010300b404542143c100a4038080d05042461030303201003202d9014984203102801808a4081c3c48000c902001c4a10340302c0030010801d140c05a01009545803040e18003000c0004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 447950476 1250 447949226 447949247
    0x307030206071b03140f15063109110306251b15050606040b071106070f0f021509300a0f050c1e090714040602100b150a 53
    0x52824003c2d0f000001c08a4440f280001103014201c00041240500310303c6060210030404c0781ca05400144802000240f55601c1d00e410010954005080071408100e01040f01a01a044680806560840307018442c586d04041a043e1140742011440320381441415502c1c00b06407501c0d00611008254081540703401310924560540e9031601025082400d108805200003516081e075030b104251141611810305802980e40020b401d0340c410386091724294624200d80502c46004005525500144801c0c3d52140c3c15613401c1900f042e40c80c101c03104140340c013500051a412040f80602410100c41280c0c200c40019609041c10141c2803011103401101c0c2d90140c403078030103294050185480d000a030242010060945c005124031030388603c1c2c2c055030600314642420603169a20501c490102c8040c02007440c45440c840b00b0094915540a40301c0e14000d4802c0150803080e608030040104000541e103034005003000500c9902c283c20080a205a4203011100705130f070312510300e05642002039581c400d00c55091041c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 447951726 1250 447950476 447950483
    0x82b17100f060843030212010f0b031311130f05010803132121121b1808060702070e090d090302090406090b0a0903030e070f12051501080105011d0105030703020607 72
    0x1400500600d403001c2c1d078039030310050784c0f000079501049a040d2403440102072800b50200101002c4c807513213480003c10b410700c40200010301d0601205071b25020400103070100c1c0b9141c02c1c000c1c0f001c1040384107140c054000741141080f1003505814007000044400c0040115111060010050f1046605106016014010101c4c112281002c0f4443e1035012030034070441c01e510240c4405121081c8144000018180030103013800d01d550038071780b581140c43c0350400c001040e41c0390914240940342a281a01501c03110965901c000414020a01080b10a96000ca840410340f008803000c1308650711299000c4d0f0351500d10101000106074100c000384090b180070300d0039079030103803240d84046400e01d066aa42c0029000940d501c846568542d03c1e14410940c040c081e40040d094aa0000c001c01d524140400003082d8081c0300319142202440400c009008090044065040c11000752207860350351030001c18000c000900c01c1040d46080c10365908001100f803481d490480303000600900160303046408100440d4060081113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 447952976 1250 447951726 447951811
    0x30d080c0a030c1209050f06010e01060e12031225020a05070b1c02040b130b0c1b040b06030f0105180405030d0c0c02040e0a0606082b17100f0608 64
    0x9a452545a000b4160101c6c4a90058402041da200000b483c120303060300000e0b14132580d04014800d4039440000030641c8601114040f1b4881c210703506260452080100341c5008031200340c208038901c00c81c0d010003002007640c5c20303030021320015410080b61150800c103c020501c0d042200100020030360350b8023802d020310902c440b10b07980001200580d02240d2050303000151298000c11080d1400510745400402801c92600d50740c980702e20843c0303103516640800c078a01841a01c1c943c0c160700c10f854650000b9140000030300640c0c0d0b2410704a9400480400910a05200b10100d02050100d46031040810b40034540c46801981402d50040c0c00310080c0400c3d4a20030100452402442c02603640d6004400b90114424003500d0781070352500b803240c1030780d0345074000745c21650042c00c4201918203410300305480c800070b0700322030707211001ca05204540c10303100c3c0800d1501e0041c1400030300c101001280702e400100d5003111084d00043d0340d41c260a42e07042c0c80c1142d105400c51107000c114003505a00440044401e00e265424 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 447954226 1250 447952976 447952997
    0x91302090109050909060717041e080f12040b011d070c031e050c0c01020106060f080c0403050d0809010522020105030a060b030a020c07050a05030618030c100209030d080c0a030c 78
    0x70489040049802105ca5071100c03090102c42601311052290070069801d0550642c5000c0d05c81030b00c44101d00c40c24186d00d01010405d84244404181500c5146520625040e9220190f406014402c1025181600d442c001a0f000141c1030341100021441203400d0f604603c61591030702c4064030400002c9800fa01400300305c0c03c1c1810151001c0712446051a21501c5650300c603d94500b41a203404868400241560324040040c000260420100303541e0320081d10300340078580d40d2025505524015640300030601d205014500180070303040003007240304941d01002007185580321080300b105100341044602410160403900c5000d948200000d50780408903950220706640d40388445121a0b1049410b040e040e50b0110300c880e4643c1007800260b005107421110070748042e08200010b0380b1032401070505050001500c1c2c0b5120b8140302401500d015100510541d5070810714100100e02a5101803c0140710b40143d54005418070700880015005a2500580b282000100c40702a4014121006603000380700c1c503d002d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 447955476 1250 447954226 447954229
    0x2012a05060f070f14041403030712020604050d030525051210080706020703050d051308120a121401090e03090a03050d080f0f071b0b0f010509010b09130209010905 72
    0x41c010701d4000800095450249801481c1300030000d03410040100c1883d01e904c2440c42031054405550b00e550709111407108010010385184a044d40081060320740c14a064922a008102540304038055000c0e5125520700d850200c08a65048030b4060858010a444210f81d101c914000912030300c950412900c1c2c1101001107411480c412603188080c8110703643c0c14401e580f000d2109400501c4280001d010785400d5036112600c171b00360b007100c0e0f82c10404045100c49040c141544408024000c0e28240d41007002a0075948000b81d00200d062800705400d8170140c8402c01951003181030070700988880e200b07141d003800d503644060182c0c0e420740840f5103c10701c2001c801d5614000795000940c403490050804002040f030261030584000c1100c0b03480096501000001e041036900180c5c800460b01e01401d00400d220304961400030b9400c0041c1c4014030090401400b0400300a001e41610401c40d0001e010b030383e8919101110344102c10b6820b800221254021840c046540c01802e5414414108096000c1c3c8420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 447956726 1250 447955476 447955483
    0x509010c0803160f020109030504051513090e06010f030209040314090a0609080f1603030c0c15020c010e0f010504030f0602120708071e2c031609050c03010302012a05 73
    0xa850300c22140c90f40d43ca03520042e0f04114a13002040c0240000d11482c00c09484c05403603030107103202d450b0080700c85c0100d0362030810b84401103c07445030b522900609055195034000c0020104801c15046034810200080381c114050000c1104907907000b0140d8103180d4407a5400c07194003d0000074201061814806140b41d0780c0c40c2e4010300050003540e1794400d10303d860200c1c00c40c41c10091440c980d5003500700e4503060001d6000022340b001074a415051040d9280254681580c2c40312080d80701da02010b140074500001617501281d442141e5009a80704200059107c0401000c22400700f013081c04500c0410042000032103a082c101c41b40c5000d12001800c0807910300403142401d80031904040011f00310001c2040740ca4016880c40a480c0501000200c100c2c05104094541030100c08400083d0b40d480712011041c00156402501022014040d03072175050118075113081c0b140c05401003910303440c182030001d084001400c05480c102c80e0140d40c0c000b141c1e02e02d4890f056207402d0515103d00540014a06071001c10402c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 447957976 1250 447956726 447956731
    0x10060237080a0f090905090c060714010906090203150115031d0709050105011701050a06141e0307020106080f070b0c0a0b07210b030a02271f0501090b0a0509010c0803 73
    0x140c8500f1020114080000d080d4140c54105891441c0b42200384214008005004031100000380c541c0740d902e01c01410301c25660340054006d40c030150300384042e80f02080380035000760700d0052090b4200d95515442c80e40c0440100802d0040c8416200c150301040c2e2101c1c4030390007010740303130341d0b4a40b04050442d40440c03040d061032050b82143c0e0400f500e483c01040103503800000d072000d000c1c40071250211541850001101b1020511030582004448a401c00c82585a8011512a00740b111300104004244800c5180150400c07a13103403000d5440c2c20000200a00085101e04140d04108003130030b01e060418030102d440d40c100c814074800d50300c200c040b20340010300c3d2a080180580007584800c0c1c840140707003032110381c0b440f0b00c2c0e20b038444000d003800c92003c2151000a0260f0220f5411602c01c1c0d44582c3c0c00322a89140c1941075420809803c102c0e081c007060368003c04001c0a07100c40e42035051202a191001591040150703c110203480e4010003200400610890203002003440c14501940218401d440e075a096030000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 447959226 1250 447957976 447957997
    0x1311040807031a06010f170709050603130201080a0902030703020d0602040e090703051b010e091909200102060c03040605100f031b0e101403030c030309061006023708 73
    0x100040d2119450550410f503030301c55001d10f40b00140b141c0840c001400c2c4814004921000c1d0b03200e07404503c0f2180601c5851010f40409007a03661245004d08030385014001600007030380814034180119000c28054040c1100300d40d0050700410409156900b480300595000c6c1d1706461455084c000412141380b058080c50051008100070207140d07080d400e0450805d01c4003070400e126161211000c20321642c0042e4140140c5404039030500b0999a100c0d06004074880300501129008e03c0c0141d11230810400070300c0c11280c240c10000711004041c04030016030762038200f03650103204a04180000b0780010402d400c0303190700040c0700000d40655030781c420076141c0110540e04101c030100449800458071003040440000280b1020950500904020204082d8920540215034200302c4821301d410b51034404200b00d8099451960880b59207141c140450390700d4502c251158100e00e1000c56000412900c00240001d2040302502e400701442100e00c5500003800c00d81c0d0a103248486400413440100302d40402625102c5c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 447960476 1250 447959226 447959243
    0xa200d1b0801140613062001020f04210b1f0f0b0301030501050f07091404320c120c030a0b1f02010c02010504150c05040e24040b131104080703 63
    0x510f00c02d074145600b000c1c502c9024003400e0184030030108481501d80122549030034590000c0c516030038081c40880d081400c1120b990f00000f00c0780d104030b9504009000304e40604020005503009000c00e204a4144110068807100c0b0703510204854680e01300d40346c00000a00d00d046400c0c26031710031018140c030410340c0c4201c1c0504808801041400001e0050684c49040c0d0207089002d441c298034040c20340c403594014914200c8120b40e0b02495a00d03070742e002d00001c1c8640040c4e441c41180c0b03d41520190745895603096801540000802c00f20500703842541c1d90508070400a0740203a503810000b0400c0e400003418490307031039214900029551541c031604031747e03c00100b140726451740740d40c3c00283c2907480002c0c04a0031a0701d003000300008604100b00155800c0880c00002c00c110080c07000480341401150032541500040009000c0c554400c15205004034a41401800000d558502080300311030025405a402038020300d07241001c1a4950300c0744031101e0400d0744143c20a516000718914009a54008550029 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 447961726 1250 447960476 447960479
    0x180708010e0a050402010c110102031215150f070204090204060b031806280504080c1c0909050705030f09121303170f040306021315050706050a200d1b0801 68
    0x741444011540b185074108107000a00705940002c05c0504030b400c000d0966882c0f10400b0700c1c660b00c00d000311800d069400c0300503d400d0808080080c5036844400d01e8034860141d80f40300321600001d281c01c0d1151500640749490600700c080e000e00c00a0440c840c0120b07402076071094081101401c1c407024600440c00c000c20380c1e80b002d00900d0418540740019001c40030b4187c14502c42100e40c42035400641401e800c00102044170744035868151540e004020b0100e407903014480c85035603071035404070612403c0007003035841d00340c2543c0e580c403250300300e41c800d0300c0d000d000500410004d000c030f26160b01c600350864001411074500707089007003642c01c4940020000e40c5007d00c089004100307001e2102d064601d1201d005000516040d60004c8175041427080d440020242d903000b1841a100d400e441d90540c008001000d89148070000c90341008106a11840c1c0440d059480d1001180300254a8441d4007103c000c243c550400c6004400b29a02864104040c0c0b035800c02c1d01c0704040c0d28204002c000940e103244c0390762140449075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 447962976 1250 447961726 447961739
    0x20a1704080d03020d0b0a03031e140712020c090a0605090108010506030c0d0c1511060702011b110109080c030c0d110a030c080d090804090605030111031518070801 72
    0x101244815994540051100707105940021800310b40406036070400503a038400502c81640540312803003109034030083c8041d0020034103400c2030008240d2150100300841c1c81c1e00130704060320101d52441c404e10b45240b00380103107000501c0d2000c00c029001c2c20b03401114003031080000055500301040313880c5004951039500410550405124403409413000c80300a020900d000c20200b80d6520b00701012030701c601491072005050107030502da00c80c0034040240f1882d01e00d04280b04d025000f2040541080d11a1184400003528640706101c1c2c00074540035107000403010404200201c40f8803011481c01401950f80d04400070008044500400d80d00f090b00010f142c58a000606560500c00200003c0c1c0500c040e81000301d000c0d9001280b441d0045a1500303102420045078102241e15010b030b5880f66034520701c0e102c010b42c24811200e000e031040310805d90b02803100540300c6043c142a46c0c0c8041140c2c1081d001400891102002076a1401d80341c980500b003001c4401084241a000d190140c40c80c01c0030030212001800360 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 447964226 1250 447962976 447962993
    0x11806050d0b0d1a060d06060e0f01380c0601030606050f01140708070609050f0f1915020a1103040b040e0a0b09070e041b110d0c0c120c030b0403020a 66
    0x45440c01c65143e001a04181c44042c81a80300c4d0019450310030ba2035000880c3c551b03450b10f0820f042c0342c109004000c0c01c0d40365900599440821b40b881b0400104581c00002c43e0403900e2100c0320007010050084020703000d4582d500e0211190702040a80070001401400c02000d801c1100702d000710b0142c140800d51174134200138418210900301e01181080000100480401c1c949412a00c50507031080c400d030ba0340e00c024244030000f4000c10000922074010004070200600b000074071080003a5080d003d440780c112a0301142400e084580500400041c1e0040e102028503400b90b0123004e59402d181003070107200e82c3c5180d0031800c41d40540c10403908850301113000d000d0903201c041c80c0341d40038100000821108081c840051042c03500104841c0801900900c0002035880e40d8114002802c1079006a42520181c0c820140c000c02407600003410701d208004c03060728054482c0d0910402d02d0f81280d607290070107050410101d42021940307000d132281800140000001012403181d035104034003c1c2d0240c554043c09103400c0c5007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 447965476 1250 447964226 447964241
    0x6040e0d0c1b2402030403150510080619020d090f08070302010e031602060309010b0405100602011103040309030f2117090c0a0909030e04020a0e150a0c02010e011806050d 75
    0x844104042c018003215402118403103803030103d076030011030302c9841c200102d1440c4119000102140b86031040300c40f07a41400e400c124020340408171a004440d440d003555643d0303150111114606089000b5101b00440e10560003040450340702500420030030f000341c856041e03404001d02c0403102d03035400060103018180d082c8680f40008440a01851a003c002802200c4116000b600a84599400004200dc014003540003500c0a030303000e08180054034200c0303584101400305203e0700c0095400c08500000107503894040b240b2413540350304c0e409110b2b801d607161019010840030341284c4142029805111b0002040206003170b08120341e4900402c14501c50008445002c080d108680341e80c01441d103140c0c0c6035144d40510003a1000c0102c0010011200c0c20b04a40031250308070007981084c030001d040e1041da6800440e5580d002d105450b010340200070601c1c21078040c460b000e005000103107101c47c0348006611031003607254030100500d00500354845d00b40c0110421885d40d442a000329100190784c2c83c01a426005101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 447966726 1250 447965476 447965513
    0xb030405030a08011536090614151e07050307080301091d0d0503090a080f04030209010509040506040809180a05010311101e0203070f0503030103020411070f03030506040e0d0c 77
    0x30207805c0c000060426514040940c010503640050040518080611201648500742d80c000c2080c1d40c942d41000101000d010b4a05940b00320751074951242030031014405507440000380540780c5000070b5407414645030060704680e0010010080000419800c101400c01c9034014040b660b03132545810200400c9402c03001140d003031181d525003c41c900d2140070440d41960b00040c1841540c80c1d6516040c1c5040016203400144509070218100d07041c0d496000203001940c1c403d445524003644ca50b020042c0c44e887c201c400500c41d40c0304034001400260120050400d003a0b002d00f030503403540700b240312034115000e0448004038425a00e0f401003046c03054070b240d4034a44100595901d0803941d800c000c003c4c05a481c150600f004030710034907140e007c894420011200100c0c0c000c0c9202c02491500c0c54400c1e182c0d8000c1c0300503403041d420700e8070020403554a54101d4a220761310800c070300c000030101e41d0260b01508000380615401581c0c1e00c0304a5441034148012860410307075031748a40c00303140030346010617100e82801c0310503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 447967976 1250 447966726 447966749
    0x80a15031e0507050a0b0c010506060c030f1606050411040f0209060711190308040e0a1104210b0108010f0f09030e0105070501020c12041d040b010506130b030405030a0801 75
    0x300003060300c4505144030320006a4180c80c81e1030850070b01038034220866004075000341c80810006035004c4010064030390384001c8402030105844442c00c00459019000ca0341605400410181c00d541c0c03907070401410810501c0c112500d00c40750030f46451040300c0080701d0980390940010341d1000b003458984605460040d44a40c11410071540e840440c4c09802450700043c9112603201c054900f650f102809510580b44c41204001030a403246460503164109100c0c1c0140b6401960128038a142c0901410754200c100102c001c0c01c240c0782031140122041105007640b01040b114002c4030100e01c3c140155800f07400c905001040e03480c1c8040d2080d04030749820041c000c10307500d0046c2c601300113644130803801c0818100f440c05c00e0f110207a50520a009104441c00c41c00b0b80d2040708195a512904100504111105044449801b102106c1d0401081710101c80080c4401e40c04801070107a844c00c200603000301c01c00440307608000c5889031103450465009480175a0395030300c0800c1c1c8100350382c1d110050502614065001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 447969226 1250 447967976 447967979
    0x19030c021516030b090702030705070e190506121510170d080916060801030c09020c2d070b0d06080703030e010c020f040c1709070e0a0902030a050a03080a15 69
    0x31003440c0241c50001520002c0c541000001e129410000200e0310007400d1070000d040a21004e56280d00000040b6082c0c001c455001650170046801c0074459008000c102000d0300c541c01c00780300200700007440d2650107001181300f5070700880e0030003141e010441d004c0c0c00405a820711a2846100c0301c0341d540403080d410a140c00c9203445c0040840c920010860030305146015031075040645042c0740b10a001120000e50140000a8841d809501d16040f24044d0030450b1002d1340b240b0717166050344100c900d02407071b560100c810900015005201c8920720000060882000c1c24880c031030303a051003d281d0011400394804180b48010181c50703c10540284040344c000c143e1249181d078042c00d404122800c1078184425103540700c040d519143c4030f41e0012800204100000240000054802d5940c1e40210652000000c001150814001010002c0d101038170301c0070203d5a41c00d25904050722109500302e0f01f5004464400d000558100704018440f031091302c8041c26440c0c0703c2112021504c20071401010807005100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 447970476 1250 447969226 447969253
    0x180803090603070c0215070605130b0f1510050c0f3d0903020d020d03290307270e060403120b0a0503030301080a060506040501080d0c11040219030c02 66
    0x8032592450160768031030702c1c0d41d50148161060405018082d401201c0c000041c0c01e5182480300070020300340b048104000d43d0300c8100f03c0c1c100400c0f064100502c04240540461803460100a0090b84040407240824500002801041c00110030788030321000704601051b01c0c41610700070b10400745055020002440150301442440c00d8100c6001888011001c10706800b8180d22410680c3c82c01080da40300061102c01010f19000390b07070348840c02400005005030b0910454030340c407e01400341014584407540384001100319001540031243d002e091360511400400144691042e0554050640e51000c11400d08010149410940f2011541e01d103041c0c2009040000003a0003001220010244150000b4002040000300e514244075420051385848048000a1070580002d03200e06100c1c85404d0910150b184d05040c0400e4500a00030001d85400558020507118450002c00b540240030341b03246190304240301c0106049a120541d200d2440c0314100060380740d0f135050300030070001d15800d10040454002602 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 447971726 1250 447970476 447970483
    0xf0b130b120a030f1202130e040201020d0809030315010509040e0c030f0102040608010b0304020f090103050105072a0b0606041e0314160b090a030203031b0d051602010f140d05071808 80
    0x144c007038144052a000c0a0303d60200c0e40c10740d5039628102148180464680582d48032442c0219003ca006208400481d10780c1441248034074028401d00307004500390b482d02c0310450b0384612030381411810030506003c40001a501c501034800800c6408005d00100520703c41450b050584115144003160300402c000c004c3c1e0355000c10943d044852003801c0d02d031280c0342d0344001034009800440096100400b10008414010b06502550247c4000e03114540f03800710f00c0840c89411003000104908104a41e10004007095210442039441071009200c141380035207070404000c2800b01001109207482c4c50f28028001c0000c00514070b141940d400004190a4101070002d089148541c080c6131086030300840c0d05021758039219506405940d0040503213840c2c3c800e00300c0c0214114103a8403044100d128070b0340c400c48624051030884075440e055040c540c50407089500151549951403900b0001c210918054480400142016080320301e614800880c080c04c110600601c20070744e40000407001da404441c204030302d08000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 447972976 1250 447971726 447971747
    0x109020d0b151215030604050606040507090311131103180d030216110613141e03060103031b060212060306060f0307030b04080405040e0f15040201080105040f0b130b120a03 76
    0x11600800503134a540c0d907031000100000900341c03d4442c04c0300380420020b001c640c103441840c01350341c00c02a41c4c0e905c69045540da820b03488041c0011070b0a4500c0b82c401d0400d00119003c5c205114004101c4141d00c03d08101a40d200302d540320141d0503040b00012040e1310034030211080380058a03080d03003000c54038000d0031400107000c40024403000c81d049916032151a841c0690705040040d90b0180c0741c0e0f5a8442c1c00a41803541c41c0b0fa518800c940d080d000b840e40c0c640050844607009000380080c2140e0b8215501660740b00902c055014a101400300c4050009400c0c0c00141010301c0c903015141c000d802c4c410305051070008007500c100e128649055407003003070b920005900011a80c00c011440d1085d2a01c2c03d0030390701071040d41c1000e9006400c0c141500310103480081c841c5422114481100d0322000031a0030509110002d40e4002c1c009041c8000401003031400390010016039411030030006400301c0d058001540fa84060352a2015681c6600002d612840c04c40018548803004101810480b400d5540040108448 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 447974226 1250 447972976 447972997
    0x30a06050a0e0609040f05030a020d08010f0b0f13050d062a1d0a0906060206010f09150b18300703020f09070215040602070b06010f0c06020c030906030109020d0b15 72
    0x200b900060a204c60141b0401d400c50304401078070355621842030001d40311607000400d2400b041e80000000340c81c5810003181c400300c4d11107159140c00e146000021941c50f030f02104804003411a1040d000c10b05039519200800214441c07a0005800f200140105116158102803003000078600b60b0b403005c2d0243c0150b002d440706512184520040c1c080c450000d001181c094200f05074080c035054001c1525500007400a0507500074044031645956180d03500c40548925160101c1100d01544041124100c000c0282c00024042004900b20b04d004101080d001c80312010300314807540c03540c0103d0110007480c40d0901c000041c00d81c094104d050858010811410311849a5400360310710f08001900a8030901c50044030080066006030349080a0800f0000384d045800c0c00d44da9000131001180c025801040440003003240e64075004c1c00c2181c907407200c0d030094001444403607443c0002c014001d815500c140045000c0c0240120042c0c0b62120b00e541c0d081152909020940030342800c15041d2070040202041e070b840c1070788 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 447975476 1250 447974226 447974239
    0x9090703020d0e030309030c010506030a11010804030c05100c0f03090b15120703050f060717060d051e0304090c091d0702030d02030903091e220608030708030a06050a0e06 75
    0x15002d801c60b00038010810701d401d40f03000202c1406034504004c4002c04a024440c002803006407247c070704164276540018401807200064048404081d40507140721544503010f030401c040845426114103080c84025032282064990310900c0d402415045404810843d865103001c01020703000755207a03141c4203805480017000d011003d200e040603a89a200420150a0030790989504695a1810983c1c403565090501030078019800016031241c4241a0742868039412124501281c840d00284a203a5240308020381d090302500003907409124039800c40c17030a404036400c010340d03940f07140c200c0500880381103042820400c2548281000703004404900d03a022000e00b855280300a0715580c0040e444c612a00d2035001880c0c1c004020003114400c04400b0705502d0b01c041e11505140f90081009e10540400744801e5940031100795181c4021003420640710852142c06e400c00911301d5250b1006600d10340110f1030440b40394000200300f00c024405400750100070b00080e101c0a00b51803c0890019078480000d280501509 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 447976726 1250 447975476 447975487
    0x1208010b04050d2d06110a1b020f1005090310140115050705060109020d0b0406051f0e0a0906030c140d20180115080c07170d060605041a0909070302 65
    0x413400e124100380b100d500b0101c1440c00e20700d40c01c01903003c60801c01950898035200c51003104400c0c01d01210100c044640e01d4802a04541800000702008d28030141c0e04102d0104500400351103030106030301761002c652100350701c42c0b400780e0406142000400e00600e02d81d0410241c0c0741d0713006031810707450305441e20b01c200d02d10882e044040499444c0500d40000d4010b10455000060003c141e600801810343c2184e0203105c000074070070500c425100140b207590340200c00c42140981003410b4421890003015a4a030003240d41c040e00c800500b4259860b0043e2300c42c036a5404041040040708207400c0005c0c210880030802d03084003000001c0c00c1c0d007008040904241030803405410107465660310701e009030b4030041c25000020075441000b00c2080c1c0901400c046041203405207207656000300e800c0351107040102051441d18100303965482d0340700320318140360320041b90034030880c0c00e4640c8900601c0302a02154bd5040d85443c503100d0505000307209101c65450130481000f4020240d29003240740b40d0300c00c00608000d40c0c0c54 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 447977976 1250 447976726 447976733
    0x705101a040b030d21050709210f110d0b010b0d05090f030901120f0e1f02040b0d0213120b0a110705101a030f03031603050c030f091207050a1208010b04050d 69
    0x140040c0b140ca90030b5510741400c01207c3c40d000032100c01074030105088000b00c0d901c982c004900c8100a02e2010b06800510031055000441100e031080c0d1540c009040c00920500c10b5850780180341080c0c00c0850a0342001c038442450460fa481202d80c4641601c004180352500203c0c8a9224861180c985040014800050403103c03030030f030005441401c1e010000c1000492100d4229201c0d40078902c0980c0c4460440204801d0301c3e854020354064801c0403091f5440c010301d55090388020b501201c21a1410150807500017181c1000040c0d0b002d1140c00b440c07007040f00e840c003503000108440d07440082c042c45980c1401240041031000884008a40029100242c1c030700c50700f04000c4840180f0b00d00c06915110b480c200c1c0c0c5031000040007030340c011001800945180d4a008074240c0c15110100c0d4454242001400010316800d0b40040150700031030301c00c0c1603500500255080d1905680311050559880d8480c041134401c204112102400c0c04007289410320013035040c882030020301d10907071213443d10410034074210000740b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 447979226 1250 447977976 447978017
    0x1b0602040f0617091f02091324080a0b07110a05120414040e0a0215220e250c0812010e101a09040f020705101a040b030d 53
    0x240040c0000c190441d0ba503458003c01502c0e003240d080009900f0000030038003e8400081c0d0356100403802d0416070403c50f24175246802508001512644111440b10342107005c00c4c40e10848038003101a070001c2d00c041c20900050124101d040d4070035111507014001c00e00108010740c8030b0381d401074a02e203002c5032902c9115440501e88030603400302401c42d005800404480252080c000c2c01100e401c6820f41c1590036a1800300320444103103c0100030513401c0740042c1c0006180c85055004c80c0d0b0508141541440d17005a0798a03241a880b10b00309104031310481091201d8845c1251040e48800c0031705103c59031801002c9030024010080303841c0d000380031240413000104030700b0b001540c83c040c2c04022078010035a9030b03030248490740d042501c0003014642422808548058402c0d40c2c13051100304001818600350b0014107010080034203100c4650015070901911002132401c1c400000d0310300821f1804204041380110403000706c0719208810b44198036212110115031000300c1c00200302403543c2808003401001011a0f220f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 447980476 1250 447979226 447979229
    0x200303040807060b4911060a210c0e0316140307050409061a030604170a0908010207050a0b0612060c030c0f191e1b1b0306050f0a0b011b060204 63
    0x113100003103404020107184501780c100f0510402d0345807108510940090100203c0715810203003424041740851101414182d0040010030414039200100786440c0700001100b4907840da001c00d190782c441c01d0080029034000303007a5030782c040110054642c00103484141c41c802440307440345c0074803c1d00302011000181d1703040c03002c600245000780c0b06001800c05407900500a0501c0c0140418603140349809a5090600040541c8980d03840b00054042c0c51348403400400c941c02c900701e8001003001e41c00300864011002e001410003948104000c001d510510700c2c1135002c0500003041741d401010300000c540001c02c000680b85030000422034025607244c80e4520301d04401d1003609000041e0603000a920848480001d4881304603215990f00c5c002881c01002100b04c1000c0021400b03030004216040360440a1014034120a0340744c4524103201c541020100007880010307e640c01500c003140e50700100100d4584444140c0ea1002c14200108240340e81c540010b44101d07402150103064070399050b034610410070668100c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 447981726 1250 447980476 447980509
    0x110a02210102120402090a061208090301180638120309060c070f06020c06040303080601120507111c050f0d1e050103020f1806010c05031207200303040807060b 70
    0x642da00f25094050b001e440060b141207014031404000664890b2480c80340b2000e4804282c10000a08070740e44038101d030364204000c1c1c594195a1343c00f800c09040c40b2904503c540e030348182400302e5012141841420303000160f1100d04052400100340001c003107041c3c41c6041100c075084400050412440025500e035001d081c882c19043300001609000e406d000044407002c440c1840904100c05490740012615010b2014059802c0308040c0418000640120070140c2d10150615010009103242000042541c4080d02c121012441e00e0201002424042c08082c1011100344458840c1c800f002c1e80050003881001c0608101001c08104e45400c85595040600380719526920543c105620150341c9001b4442803000b00d00c0f4080c20750102031503081401a4000044070031040907986e645040040d00c02c0341c040a411a803e0001b040a03281400b00c200005006010310350300c803128020080c09002850450b1020024030740d00600c03c11000804102c12514415449000800c0844a010200702c81000460051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 447982976 1250 447981726 447981731
    0x1030b0a122117010609060e09060310050c0a0e0904050607081308040b122a0309160906052119030507060f0f050618040602070203031605060603010507110a022101 72
    0x484403a81c00f08240e400300489901040b0184d030380311801d030707100b844a01c6400d0100307a60f14000303007152400600f1540c1c401070103019620b03107009910300202190400c036440343c000c4601144010344280d00448a0406200075a400c0a103405c1c0354551701e030b980c04010604820810034000203001c21039615030161105600840031529182c07680c040b204c46400108110340c410340b60000044840440040007114212010340703070304401009859030026580000d01d42802481210074803c880494022090003c0ca88094009442c40c01e00042040c1e0302001045210301401e1041d401e0400800401c08105040c030904041c1d070007050b545400e1b07910707001c0e00d038015004901e088460014540e85d030300b01c0c0340c007440080c0d42003200303680321400c22851745519402c1c03000085040d000600000e8180e03005050090008040344e00340300a903040f0003003200d9405011140c0307420580500c1010b007401d00440d50010341904020125610804801e5692251403d010384540404151002d485040048040401a07642c0c001d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 447984226 1250 447982976 447983033
    0x614010b0304110405010b12060109120b181c030e0705040c02030c0c010f0e0d06090b1006110309091f031e03141207120608100f0b01030b0a12 63
    0x108081d00101d6090394021800001c08040386403600c24241601c0800e0003181c00c2c00c4801d60030743c0341e40100904403410b203d10001c003c20040d00381c01c0001314140c8688140781a40c42c01107402e800800400480d024140d10103075a214003100310358034400640d1003d180000300088050b41c001d2620107140c0c0401d03005442c08113000c08090780400209000703a03284e001c40d1014030154004640c110500261b010002d40820318a000500d072094880300c4603401250003103002c507402d4846204c0d403401076a400c07210000c0840c042060b190001e103807a2540312140702450070060340e08041480c1d150000d0943c01031155020080c00001c564813101300140d40c01800103410074000304194188010080f5041d004a40000b8285594620b01c1c8115040c031044900d601030f641d103c0071415114002c0103507000301402e45a01c0c01040d031001c1040380301c0c40c0681061010171001e2201d09848220307404202d010781007500741825001541c4915422200700c680e4120008901c09042c14555496090503010401c5541d02c00b59 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 447985476 1250 447984226 447984239
    0x302090a111801020d02120a03020903011d0102190908030a030504061410080c0a0b0405040b01020a05010c020601240905270c0d0608030301060905041104260d03022104061401 77
    0x125140c10b1842a000c8409011890000b40d0341c3d2500d0b03040340f1070240b40811202ea90075100341c000c0d10f01201d014001264017881407908a0380d8203c111020003031a940800d00d103140310380180e20200701082906051110b00d0400c101c09484e4410320103240b05260321407001c00d04120f00e50b40118040e14107041e081c5a1410b08035203182c3c020703110344180d40d00c501c52142e1303a5146103800c400000460300da984455180515003024080034000c480d80d5241580070b5000c404000c43c600f030103142c188c0e65a0350b02504ca150b0524503c80d03801c9110503402000005404100e1a103a40c01200b40c40544d40201d40014001c1c409049103100311a40045101e02e000450b41400b40c0d44001e00042c002d030030542001480078540b2424140c1d42c03400b0034418100000c120160411032404d0a41c000e001441d15130b00450320b000d80701c02010420400d0280c5c40020303000c03101d0020b05155410700c03060b2010b00c0213140543c60000303042c0c401c280481c8200c5840c2030040705500840e0070000183e00c41890780000c500501c8496a4406 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 447986726 1250 447985476 447985507
    0x120b1e09100608030f090d053f0a02151f0b0304050d081b0c030708040608101421010612030203070303150e010e0403110609011d06100302090a11 64
    0xa403803080c410b04250740459000f07004800d94405d4031924004905041c4e091041154039680100c003900e13207010b10741641d0540303102289090010b0071601c0c6454002c0280d4007103c45010400d4000b589100c5040c0102030513240e020501002052200740c92280710380301c00e145240207200c0c11010f080340701c00549000038801e90301c2e0040d51185001d201510500e5011580c240d0381300c102245c000d49007030803a00c004281107010304060001c0b85a480101c9042440c940c0d201c0410350300507000180030a400c07104200c01e20110002210141c04081e00105e10384220801240001c6800481d0030100818035003018911002540141d0007000750802c014880d40b02c80c1000307034482c1e01082082d0000790070b0003c0d41c901640f00310b065808481806e488451030b40e10307006102540f0a0054011400c2180d00c06002d200e00c0001c0015501645080000043c0481d203211044070005039210b040560307030860380030441000d00101000003281e4040c0c0701d0082c265260386c0360302c00030541c2181540d4030000c08900022006144c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 447987976 1250 447986726 447986743
    0x61f0903020f190b0f090402040608190905120f0706090809120304050105030a021b120a020d020705030304090b011205070e090a0b0d0213060308040314070b0301120b1e09 75
    0x90b03410080c2400e210007400200120000100c44025052400300b24051141c401050b2100341010442d05000711280058140e910507030240c400034040c40244030b031242a00c000780080c038510650030005d0801c50303035441d9240d41015034100c9007110013056000744060500b007265801c2c0d030320903010080d80855203090107842d04603256040c050100d05203040300101d800001c2700c040e00d40584a0608590303030398405030003035448030510583c0c1030316425040004210400450309131314003009071a034030381c640814000d20f4004004043c1c011035001000030405d6403030210813202500c1807a0f50209105650200607101081d041d522001450314200800400c2035004540708005141190455102d4451041100c25a901c05c40c03469030260b002c0000301c00624144580320104002c101c0041005030750790b1203042c6c0300c0e00a507000b502ca0043d100c00400d083c440501c0641c1c050b25010f1850340c215418842080092041900020f0000d1503400101e052004d01102c1d03407504018a2161840c140b5024440b07a84403090f5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 447989226 1250 447987976 447987979
    0x1b040e04060e161a09041b030f0e03042402070806071d01110606040e100614031c020703060e01060f080d110105280b040c11070602060601080f061f090302 68
    0xe40f03002c080240301d0541140200c802c0d507030044004030040c0130000400d0b403200d0751581d40683e85401031505e02240e0b0036100c204458607100020402810782001c0190b4002075030901c81c1c1d80080100780528500d00c0c240c425607036414201010144ca0006040e45030100e41c2d0824503440c0304100c10130801c1c6034042003440d542c0c0700500241003920f41c16001900d2003604034003441507541000f400200716040079803260520f50070300401c40d602e0440822600381201d01d5900300c0d191500d00d5040d401c80b0350500b088800c810440c0010341d01060050208001c1d11201c10f404010031040d15080c255005500c01d41201c400f9101c815090000a96202100c40e5544448038580c0f020583c9006410341c001418490302d44111140b4201034031533905046170303020340c1c1000700b6400107603551042d00004070b03255445940070040e12500c40441c0b0301214201140f408025510503021540541c00f000044e0b603108141c1d580081550100c002c0c503803a00c03400079110008401c03415014651460400c4141c503404600401101d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 447990476 1250 447989226 447989233
    0xd0506011e0915090507020c06131706040c0303050c0a02040c050a1701080c010c15060b03010e0c070f02130e0d0302130b0304121103070615030308070f081b040e04060e 74
    0x351020680c042c0c0340b0040c60b8200310843c8210404c00e00d4034981100380d0084162064404541000300002e0b455040001c800c285130003454400d00080303051403080302c2844400002499540340c2540c4203904080903000c020104140840c0065a50100300b202c0000103070700070030a100814002400601d05e4000588460004441022007000e5100b040038841c1a00c608074040c00f005007901d00155075135021841c1c1200c20110350240d50701c199091344540b40240c242200c0c510b95951400003080e85001024200d080c1c0813204000403000109501c004100c8154141da007130014004803507540004040e10015120103009501d4660243d036456402860980043d110126405840e045d03014440d00048500030318405860100602031400b8245404044500b00d08030703842d1803216a110800da92040088100030703041c805003032007016000004035070310503403034130b420144182101ca004003046809131007180020102c801401c4000f4182c81110702130702ca11074998215040500e031542c002c15034000004003600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 447991726 1250 447990476 447990479
    0xf01090806012405130b030705120112020a0602070627120f03030513080f3717151201110c1e0606090103110a03060c18050109080a060b0d0506011e 65
    0xd02400c15511380220030158002517908060004d029940040c02c40c40921905211104070084104440c40c06030200081c00b030b41800346481803080a00a0340c1041c41950000202484010fa01c0100b4030882d2012118001120042540340200302d0101c3c3c01c240c0c5078002d8074174081c040c04251038954014500c81d0342c00300100e5460468086c001055550020010031040100032920074002c0050030212980c10305002c6100b44061b06400b4000c404c21600015411500c4a03d00031a000310b031003001c116801d507040030640f51219024080d030401e500f009124039406444044000700960106840c40702010001750b42c3d01c412403105541c1c6082110008104440046a10414501091860285c00040c04030400d40c0d085039109150f0010b2520520742100b0801800008204640900301210741203449842004010752403246011a0f1a0029414402c84020400411300d0014100c05800d070003e0000500306a59400241c060b40c80384030141462181c0c0001003407800300702d144502041c0c4040641807099 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 447992976 1250 447991726 447991799
    0x301061b020105091c0c0e0907030305300a0c03110a031e050c0d0f1406061b030f1b0601060e0418080708120f04080d0903020a0c0e061509090103020f0109080601 71
    0x1f0000c50301e00c661900020010000a40280090102c802c55060b8000c0210200c6000140040c801780b042c01c03107407030307268207010b919407062040071040700c1c1900c0d05100440c5190901c1d2000d20410f10f100003015914004006001e40d0303424002000031403170006003c90b0400940001a0350444817404030041e16040e4a904160064802d0003080b0051a0b042d0040d552800c0c20040705810660860f17082c801c0c910f0707500d040c0c0c88091004002c0d080c01059013603200c0e00200a1040e00214100c0519070b01d40c4500b0040c401e541d0000d10180400c07404960203d01c54004000b68612000440b04c010540b00003c5268400c200f981c401615140310181140700f9150f07965042064501800e56000d04174034020060001210110307084102500d000740110703500b254480d0384440c07035003000350302030714400044c40180142031504010361244a1541442103061548a0300011182030040c07100911901030310b00500503c1e4040c0010030000d046000a8a08035079480780f035001c0401002d4110500c0c2c0c0b02c49803080460 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 447994226 1250 447992976 447992999
    0x70e031504150504020607050d0f030f0b01080f071b12081e010e060a0302060a080604050c0918060a05061303020f09192403050109050705060301061b020105091c0c 72
    0x74a411031800300004104400040040001030000ea030400402c000040100307001300440000083c4a03924482c45072201c030300040464200d0710300160400d06003a5a9145030782e20059407600710551014861894503140e00c00c4d10800020408500288902e42c400c4040c440a8203400303080310125100c103c010369814500030907441a03c0d4003a000030310040c0050208a510502c21a8880c0e005403810218039120740002d8047e400c21040000050381c50702c1004490705150080c250010001400390f03091820150001e850700b40c1440811500b40000c0d0700050b40b40e0f540f080786c940140405400550303035400082d240308401d41c40d40401e038051624001c42c28418100048194030410241c40c1159143c1d054401000250240102c001c01580b568000c000800c0c0d1801120001036214000009412580d840c007a4200205a03000c68800c400c144010401d054004403010944490340c20604072000040c030060341c441c0285035005401c4516251032540c91a036190803a40014001c4d0042d1400e030303903602ea42602 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 447995476 1250 447994226 447994231
    0x61205150a02250203120f090a1403191e08030a0b060702010e1c06051503070b0f2b0f0b120a0c2304020a02030a0809030a08131406070e0315 62
    0x150703c103c3c04400251460100001d4003918802010745071500322148080d5036030b030840035403030801c000b00241c6d1182925144080c90010b000d407910003403511000030006500d4030000304102e4007245040701008208400100341d06095455883d03500910b00180c00c10009a4000700e80d001140c910f442644215441c002c01980d0280f0741c140c0d40ca5007248640c40500403045100e080740d200b000381c000f01070000104240985440b07010304004250781c1070b800703034100340c9040710380e9011380607480f07040200c507010190450449078004410400a2500e1080725401c078120803281d1003080c240b908d8103c0e41881007030b440c7c0020654041c00c50380c280d125186d042c00e454441c050b42100428904510f1410420403501c0800b0a48a00c44400c0ca034001081e1080450181e9101881480040c0c20005500c04440e800c0417617983c20583e023400450a20202c40d901401c0003e0207010070100100012602c400c01c01060905000d0392250825039900f801e1444001c2c0c00c25074900f10303440c840d0040034003200c0c0342c1390401036051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 447996726 1250 447995476 447995497
    0xf1b0f1209021c2303090f0121020a1b080301060806090609190b1c020114070f0b060d0f03030b0102060a140112060b0a0f0e0c0711090a061205150a02 66
    0x1512684410f0303e840301c0c0000c0071007140c1300134000290424075840d251603400101301d0701c0055030341c4000072010482040d4008880f203061103505e11010950170f40b0030003a01c41b00544900c1c01a952181050140c5a03046084016451000c0c00c0c0c45400c100680d107405136048840e0390b180d01c070081d1500e00820031010320448115400112a0b000540c8006040c2504100a00ca031000010301030568004207034540d0001085000040c1b9103098081103507071003150084002c2011303e2003030909039282d4070f100c250f0780707190030140c0622528004501159035a5418003050740d4400c0740446d00c500301c2d10300603003d011000451070142c00780000240b40d0b01224010403000005c68050000300d60f0030000704c448071001c0280c0a82e00d0550f00c00c1312241c0c544807030040c07a01401d50500000d400d00c1c07401ca2401805880180b05801c1039100740701c640700007200d60050f1104413030300b114180305d5036848018540003844158400380d4142e0400400ea0140036002c0303148511407544072030518251752408602020b034841c200202 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 447997976 1250 447996726 447996739
    0x10b040305011d0619061205011a04020309030403030f020c06070501090203061f091802060301182304020402030a0e010c0c110a030201020d0507080c03040e011401020d0801090f1b0f120902 83
    0x68003003141c07140000c0101da0161800140709403507d035042d1880211060884070382c0c1d1b5070544468603c002040c000306c1d480f01181c09529506e85200c0c4152240030300c0c48020b00f800b048840c0d41071031078004c0c001e405102001074100c0b40c442c1c51601300b0601821001344164003d02400700840c4036200101c941c03451548030003e5a0040510f058000c8000b48a803c4582d02c03e601d800c0010801030369010011070007068101d0311342042d8110b00e40d40108039000c0361001d08455030b00c11148050b040d94200126440740d011100103880e0361300c9440c188082d0041075402e0340c2039440c1c5000d0014180d00100003d425501a10058181110346018032008250500010313015921139070780f0401141c850740050a0706032007030b4015410a45880c000b180b0716082608050460790081d03005102c1c40610050400488009100030020800c04040251a1a0041c040d000b001e03501c510030601c00078150b401001011801c45100c40d0b110502c094018510209110035000040010039081d0003402e050103580003268004190 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 447999226 1250 447997976 447997981
    0x3111009050d0203010f0e0f0d0c0f240c0809120304020a030b060d1e110d0c1502010b0603010b040e0c04030515131b1716050f06040e010b040305011d06 67
    0x40182503001c20030104d9256407680c01c0c600d401e50141c0152161900c2c0c0d04010301601c0745201d005800c0816080710b190800504082185c00b107050340390101640354110b2518a10302203214222444881e1a2410501c1a0300700313036002003e683e119460511401c40041a03d004d51201034407106244400c1e900a036001031844018070200d403c03c044181c004000800401000b50386550758100d1071144c01c003c42087c84071000c80018003410b5014042800c0c03040750070217188040d55403020990f40d500d0042d14100702000f40b03000c2d0014002d44c080000c08a006029680b6036030f5072460004590300034041c44400342e504001040340c0c01e50300c00941d030649034040080c16600084980c0d1013000f00740106a480d9a44d8070078401404074a072003c1c040c0d64800300b49081400c240c01d00881268880c50002e10f002c2c164006400e05101c1c1c42c003400044180d80044440403625044840002c4150207030743c1003c402c010f4904c00015101481030b0040007107030720601c007c0c410201c00120b00c0d1404504000c0e1400c551b00300100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 448000476 1250 447999226 447999229
    0x1503051b03010b1509090109270510060b0301090b060406020d05160f111806030d0e0a0905071e020a020a030312090501050a0b0109090e030702011d030105100311100905 74
    0x80c61000d00c00600000343c02c040c100e00040340200c2d02c1c400c03040c0134000001c4803201070801c1948607001d0004074a080c08044032031500542c0500c0c2c2c00080310b8081040700301c0c503420081e05003c603c46c128103280062003003640b203011201d2143d00a108992009140c10105c8201c0c0c00d14805030340444070250050543c10302000c20a54503980807801130040f590155210200150090000c0c001540c004d100034014681c0050034040202446441070611038066001c200540d60700041c00c41c050f2006103400761000c40030201040b00005617030807a661080c145400c0001899110080c201c42c41c1d25a40310b2000203540c0745050340c590900f0f400c007a400403042041030ac0420300489aa50141030fa0032000190024161102403c40e0802d40b0b40300f40c0305482d100200010b69000d0500c00160087e03070f004120036080540150341e28031980f4802814030801440c1f080444030388420303020012402500030b10641c41c000d04805400c0c1c600b800200e4402c0384040e041500340c1890302d07820032032000c282c56082d102d504200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 448001726 1250 448000476 448000513
    0x2091c03050a14040513020418060b09040f020906070605070818060106080402010203071202010c1416030c0201020f0604050604120216050f0d080d020309070e160305071e090306150305 81
    0x501541940b40100000180c2e1b4460002103100b901192200680316820951460000a41c0c440900700190800c0342c04c4c082c002d410341c212040c590f0b0031140000c0008400c0440c1000c3d005654445030702000c08107810080c440355801c0640715001c2a551030142d540c03001d0b40e840c0c0b00c14580302508103030340c050b0f00107008a6010300c1d80160080d0050040300d0600c2c1440e940c0d10440c008082c4c003000180d445a144002494114540e000c481c5459450746040202c0800c0280c0510400c1e4006003c00020070015025a4001d0150f032245980100503180c071303803a150820030f965a406440440e6204020a140da0740d00e8408218082c20003444140c002109191000300301130000e118a02a900c00544046180003c07035483c02089003240034200503860b4548002500d04001c40d03075029102d82d68284080250a6410b0420302e50102c50724140058142c8610741d0440b000c01400d9044c900d0060047c3c04482c045030015000c400700d0703214020902c00c0d0361965000c0700c074000c41d40c0301c0100158020000070b0846c1c402d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 448002976 1250 448001726 448001747
    0xa150b0109152708060405010b03071203022109090709150801060e090423011b0905012c1008041101230d0f050c0a02070501020c0f09101802091c03050a 67
    0x203c0140049070f40b540b202c907051190a40c1d044400360354a1110b000c1c60f0800b480400c00808a030b10003019140403a0318082d4071119000d031812804442c01c044400d102d00c84800355140210080c201c0b48003850816806011411140518000d82c140a01d91400c0588100050b60690f103965582c40b1004107001c6c2445144080a801215803216030b040807502e014030900707591b58400085001049124400c1c86c0c03200c620360001c4816040020004003407180d41d800c1083e400c3c0c030501040d01c2e0080b1b03282e88501d402108a0032100e8560000303000d0803060285520911040c000ea004030340300140c0d50f200c4e2005590102c004004800303198081707800d90318480c44100180510800100780841e050080700c04000807954101d9213000000d0001c100d88a0140d0b0421400e8040c06003800140140580f4a001403810200c200b1224418011400011442c04e4110340f01c8000304000300740c2c1550491405188406074019a042a01904040c034846192200c00e0010501264054650f40d1401140c40b400b280c104190 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 448004226 1250 448002976 448003037
    0x6101802092e0801052e120606030203040212010506010e21071509090c020601031e05070e1608010b030703050402220c030506040b0a05120a150b010915 67
    0x342400c10b4100581d00c00110900840005507002103140740041c1c0f1504042c0c0125004508800e55040940e00152105541c048400001501c030500ca41003190404000c49420200074104000010311a4164000d1030050744200c031074036001a0082e1006080319421151140000e42e607000f8100706003009a404007141c4a5034540c10344e181c01100c0e0791032402c0d00300e600400c0502d059100c21400c40b81d000306050081c2c486071000b400a10400c0e54001d6035140c06000c0601003a1009503000c140410200121815923481001e0350142c0d40e40b01034082c2d044004590803001c520450070350359404c0d0302c0784014505a604044c9000c1c1180c81d4500114014480108100d800c80d06400700c502d50209076007a05d10407819402000b01344284d01c040d0040949a0151240d40035600b410b0b01c0c0d8840b070761074100c620165081999444003c282469480d40f9091072810081e01000071150380d180ac03044980c0186035000e2003a03ca00700e600380d88449860f007480c0c600f00b0300b40029900c0742c9001045007954030030007000302a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 448005476 1250 448004226 448004239
    0x40207050a0c03020f0109030b0417120a060801061d0f0c070206030415060603061203030e010617030c060c09150d020403080a110106060509010c061512080c0610180209 74
    0x480e51440d18188601c28140ca412004030403c00c11458060504104e035042071800c801b04624650314039692002c00341005201040d00c42d070b010306c0d03884140c0c01d64060010140038940c0500b040300e1228010542da001700a415403c0100202d04208040c000c0d01c07002d1454101c0ea10b160381d602c1c018211b1040c003c0d001d158040001c102e958050703604e481c061405140500902801000040280001c40f030341035002205241c2804010420b503900c00d00400881c6415040106000f42c10002480c01001c3c543c01c00540c04c0940c92107210344400000c050003c503011002103d440f6280c2621f07010751070003412103455120081c40d03100500c0034107010240850819001f409414a626640d03400c030340790006001c0300c002075100c8000294858007401140000c00e440d0500c03500d05411000000d211050003400900080e40b205e14030240b0034003c800700d0001388503c034820341c1e030034560b884c000c0501e512054601c2c0091090303e002c00c10900940e03045008072503001c04041854030118164101075008101c59590004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 448006726 1250 448005476 448005487
    0x6270a11031e0105030d0c060905011b020304030b0c120402120c09040602120f1506160203030c011e1e090809040609020c07090207120c1e080324030c09060402 70
    0x6140d0000d540a4010025801041000d4501c0c101078040164031082c07199009120381115250800b03c500e100b1500101c0105131000a410224050b20102141c0c114040c0100d21800300350742d001c0090429240304074007500d06170700c4030850303070700c0a01840e02018000711403640820010324100207503043c0710700940141c840708107807040020103c1c401141d045c1d403095000982200e00307000f40468550b102014944800440c240038403d00080c803101c800607030044000080740b4400f00b9900190741441940102266984c800ca11810317030203801c005042224071503074004030045542c0e40780038030100c1c02440d1500c1a280500034144c1d5014050809041d03a10136400c0140c1143c54859003c1d041c090810041c01594034140644003d250030000e0348660581841407249200051550342c40e1700d0824660701d0940c2c548400341c148880c4803181c00d501c3c18410380726060300c00100a0742c40061403068600383d240c2030456100146400001c2c0722162070350b6168010464000c11440d15100c46a00000007034801400d12 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 448007976 1250 448006726 448006751
    0x10020c0d080714031f051e01030b040e010e0109030305010806040f06021c0507030b0306010902040b040302060a1b050106030209072d0909060e0405010c3f020d050f06270a 75
    0xd90050341e02e07440301c4101d42d090b45104030080c0b24481c000d24060f1904000d00c1c00359286000c4100d07e07036400078101615164a03580035900c541100081181300c400801116050801550081c405104201d0120b42007000016249001045a51042d600500461810189541e500c0025400740c0308145c0740c08030312985140c481e1207601c04c0a225501e5910005a0484000201490020164030202c0158010442803014128440640e41141d905803616074035030b41c40e0703070301901c81003900314414000e0140801c0d00d0040c00415040202240d0007540c1504080d00c41103c1210b07074400070055425807170b015010038000c0660707050a40102240e14500a0307640c40e213304403441500c100e036008030184007621007800b0a011302840307424020710140c2416404000102014190031100700040d6070030340d5094208036004001e60b980c40c4410031107004219501d034902480c5030006c042c01e451075200880c04030009070b081e0401644800b05050b4040c02010b200007100741c1c1c0c3d0000071008165501760341e11000028981d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 448009226 1250 448007976 448008017
    0x51806090d1103130e10300c05040513060e010b01080c1e0a090306060e04021f020a06050f0703050a090819021002190f0f1704140709050910020c0d0807 67
    0x10300142c1751114404c2c201028000000615030b001140c901004c820150036090b24103841000c90b24204030900130000b10381c02d0072041c01c8010391109805c10305000800c52002a417104008070702d84a030720104099980106130508880080c0d0000c0c1c0841c1610022070303012448500501740345450b000b8280501007211503064003581004044002242c40e42c2c00a1007004054050040905400b0011007400e00d81a0001004100d8940204004000702e94102c0441842800202881030b000300c1c1c04c0c0301d641802550f8502812040701c4102c0043d00e00400721b05202c20314014440a42e0300040c003276040021038400500b10448449500301548240301d05101002c9690020700007002044403080c0074040000c101a00c005050007003070042041c481c800010454000d00d15811413880c1c4d0021f440981d80e2440c20130880c10342407265031810b2080080003d000300e00e503002244502208070640e00726043e00c2203520309902a82e00000c1c140d0b0886075209811901c501c4110364480c0c0185041040d0803040d0030403200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 448010476 1250 448009226 448009229
    0x70c060305060a090b06030406050702031603050a0e010201050f0604050c04051309060b0d030c03030506010e120607031d07170a02060c061006110c1905040e01051806090d110313 78
    0x8aa240e904000c298a4403c640d00d00038088200244031401100c000210244002480180010368410102d40c40600c20015611440101110025500b40300d040c00781c07240e080f406102c000103038094038281136948180242c5020781d5804130754004903207c0e03000b008040d14004010140c012401d1100080e40d5440f0310864041c6409010001152036941c1402019140b60354485409084140e206100095120b0b1407400c8a80e05440d00080c02d8540b000103c0c3c08200c80c2d48505e9000c916a030170a045142c0110307902d405090f06480c200481002c016843d0604030080c01e0b000100d4210600400050003040700001203503c0d03010035101200f030b10780c1c00910345400c040250322081c0e000c0000c2200c0d009400003108080c101d907081c6843c2302107401c2c54513503503404001005809801d164014600c0b08103210310010107044014414442002c0354208c1500a103412543c003e980600c000c00722490aa010070458020780d02c81000d0110303455a070380700b0744002c007289900d0b415078401040300303d101c41c420058050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 448011726 1250 448010476 448010489
    0x304150b031b0f06070803070f170403030c0807080702030901180b040b1201050f0906100c0b090d030b100905101b060207030e040c091a0705191a010506030105040b06070c 75
    0x35407031180902441035030143e29524078003c100070808070010a000c1c0d81034035849030a0745051351860820741c800300c507032124a2a8485203100c1000c1403200701364064110443c0d1203010b0341e81e500c25640341c002c1200e50380e03020f5032501c0140c4c03c02c1115041c9544500042030710411401e290281c3c0d1541c40c0941c41c2541d00035405401812804951368542e1034101081d2401000c003155558030720407200000a0a200b0040e00d124460f810b4044040384190040381403000441c1c000c414048a80b501d000f419444058403254040020b142514141061400000700800c1188503030743c0c8038209052406100d102d1460515a80c2480605520444090fa9020f061044030348075220140e26480c107890042d18824450225610030390504503280d828550041c1c00e40102e0b0041210144603011503202061248a40407014003680104001d141024004000050075648680111030346040c00048504c8000310078021903a004c2c0c81040100214506900030100852006103c1407505440755201c42076180703280c0c441d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 448012976 1250 448011726 448011763
    0x3030905030f01020a05030f090109050105070e040b010516033204090b011b122f0d020307030801050d1106071b09060321020304080717100e030304150b03 68
    0x103000904062040c99010141c4000039800d2914440005c0d0060100500f8002010301520010700711810075000400c1941d00134000b0411340c200200002c010300e6604075150302440c205820250603501c900102c1300c1c8101310003240b25180a00d5036080b1208010311304080c4050001090303c80842c0750403881240c8520015032240e541d0703450000c4981c25140c541c00c4050503c0040030800701200c501c0c840b040c1c081d03580000107020032201c0a000781e800e0715035804c1c500000d007032078000369004010594410340b02d4030b0160201c1d9820310040000320713520320070984020300082802c40100703c5401e0807205c40b10b80d28442c82e60762651641c12000302d0001c5c1c02200f402d45400040788411a041c85a40d0b00344409443c841c1c10a0044a007551030341c4a182d50010304070a940210040304041d0700f44203100345da001d01191001e0b44c0c00302c3d5458800000303d440c450001051802014001e5911001c180304d10401c3c2d40c1c26201541c0bc669450b1a11209180c0c0c3da08025446600c500b00844665004d0001d583c4d40c1c0910f4004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 448014226 1250 448012976 448012979
    0x90603050105070c02060a0c150e030c0c040b18060102030403080f13060212090d0606050a030302030c010b0409030e01050d0617011e060605070206030a0603051c0e030c010509150f04030309 83
    0x80360a5403400303442c3d04180301981480d40c0150300c1d00c00444501240606000303480c04001c1c07800380c2811224180b90002a0303c0d190601c0e2070101301000803c054a281c03000c4030340d420300f1102003004548264007403d50040ca499462240207d642c05403550108050040e41e05081e41d03502c0d01f09180d404844804d644050011320000004503e806e890050201c900c014150f6508070f80e0700f4a203521410f000e045c4900c4100401344100701403a00100083e10000d885107288580e44d19020f0758036000140b013403804c0c2d42009500310b044e08080c81900300c0c85405540741c00a082000c0010b6070240e0021f04441e54040d12200f010407000103e410418840103a0000007840d02640c200d01d0341c12002581602d0f80050070035000b009901d0340b00c005d442e8800c0d011a02c0b15604c1d00c0b002200390023003207150f01c01400c80c0694085d400401c10001080010107896450b004902c86010040649802e00c04280d42d01050301400107100d581002854101e0001c0c084036518500703d4160b1001702d261b0003543c800c0300081c8a0610 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 448015476 1250 448014226 448014233
    0x6090501050702070b030a0f061d10061d01030c050d0501030308090c03010204180b010512070e1507022b061d010e03040e07031109042f071713050307090603 69
    0x60300e0b40600c071480503141c9a42030206aa50911000d02110549a100e01490300c103018690f005c7c03070091000724845603104440661a82c6040303012034024000282864002856500480c014582d85c1c00c0407601100c03a080d0b12005500508d03245580701308204007404130000c940300318420306021394040d4580390710070301d02a488145440014103609010b40d005100400945041800700980700100d082c0202c0c0084005004070341c1805188650440d24043d030f82449043d58000140c84080d01c4240da800c80400480804100310748a0b10310029008003a841c450b03270000c0b030b080203d000640f607140031079694440c240c3c45150903a184c5003001c4405111b01141c14a41c244244038010010086501a50800d032401d80502a9948000d084500f81505c6031308540701c44140e181107a80036031000b0000c00201c1051094000c00300301140107909142c07100d000107224018440103440d09030391f2043c0c443e652215102d441841e1600b0a001c41541c00240b0040412035a030140f2182c8040c0c2080e80002414a00d0b504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 448016726 1250 448015476 448015481
    0x91902120a06120c09090215070b060f04060b12041e051c0201050f070c03120614131b140f040803070c0504050105101d2d0301140f0406020705060406090501 69
    0x1030044900b10507107400f107000910102d07486000c8481c4413800003408034107030010800c01451003040b07003052000010420100300c10459214014101a5002400c00315005d0a000481d00d01380204510040c051002e40e031343c0e84082c1020b6510038455100d200b1800c2c001d0711174031410068140f0464140e0041c8584a041b080403022400b490364443c4000d10540c01c0c034100d000c89c040c00141c482c00800592401b12414035000d04c00350340c2000d0145508000380755958403008001c0c00790001c254400c0c12075001e2010440300c540100c0c03010410031410210020b03200c4030141c0343c49115101610382510140501200504000040c0000345804400307195101210720707240006071081c0d0403032031140e49040010b024940702c00002001411490038092a4407030300c0a04c2800e00d00204034a95885001344607410902e0311103e080102050900801000032010041098260b90000000040321a01d07500050080c401f100070268125006203001458421070341c44460070100b04072030944540f500c40c100c0da0100842407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 448017976 1250 448016726 448016729
    0x80106060e0405040f030c051504032706050306010e04110301030f15060602071404021909060f0306050f01140d0c081e13030302030a0e1005090723091902120a06 71
    0x72102000a0300e0b2540d036845c1c40d0134818101408000c074017036030f4400f003150402140040900d4011039014928103460000c006c0d00c12030390240700c11140400119450b0781c54201c88010348200d511003604550703c980044810001e5100746560098a07802c035940000c0c1104020350103180245480c3ca100c024604040720300c0c00403180d240d08083c2c5407480802c0600d6000c00ca9005565920f80718107120912400001d01030700455030355400caa030994120b125202d4014100f03a003103a1454984451844141a058081310500c0c0300d03480d0032403820522402c1540c030451210b280d030400c140c02c440c10041e0900840d400c6031410703c040740c0480c5180d01403107840b040c008021200d83c04a080f28502c01d00e80074811144000315a1740041c01e140c2c0100115507100c5907500700680c1f9081a070308540c07000c908064030001802040e04c0c942e07a03500641c0ba010511041c03100c000040c1c2c915040000502c0c030f00000911803002002044080307602c07040401d0340e00400356400242401c0c0c074944140303c01420111006070454106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 448019226 1250 448017976 448017979
    0x1020105010807140402070204020d2a17042a06020a05120a120e12160213060815090102090a18060602030a09050402160209040c0e06090f1618080106060e 68
    0xf0400400040268540d0080700200650740581c071000184040707000b80c043c2848017100c540c10522540c2c540c0c064103000301500103242d8141c0071540baa001003503491030106440419590b0810001402040c0e4041300000b0b2600e03a0008200500f504040e60040342501303030840b000503040b000c00802841000c22a540316581e0328220b2904d41000560054070b007040040900820343d03112214010581010b000e2001d01000c84248075030703203650001d44458051f80d108000c9100740c84039440a0320148103480703194144c640d02e800402803030101800e03440301d8810003800069150b408100711280c0e40c90760b043c07a00051249410040c506040c0f1103c00d400c2c1c1d43c254205c003003158414031203030520a0784007000e00111982a50016070387e10100d202035511041594004e90001a41e20912040052070f001c04821107011a180d4400f03a03d03000200001d0b1401034176000e015109000c08940401b401d04901120f12602d030503c003220070440710705802407481c203502c003c01c140d660340402c01603280c0011304a41d40040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 448020476 1250 448019226 448019233
    0x70b070801083405100e0109090504020a050910080d0f02100b210a1a191a131d061519120c0902040b031b030906010306050702070b07060b010201050108 67
    0x243c142a40a8100322880340b51108002960301008129808002d0050500a4081100072819480c05030a05203000076240c000b0b81c3e00140083d00d940c2503c503a81c01136500a004140031817400f0100140244c003d000418440b225441c00558544100035030103503101280c403002c0c55000d00780c002a00b809295421040302c80d042c0700f01c0a41a603514500c80714070301e20302c0b025039602c1d00410b96418035194006900805020309506a040e034680084203040c070600c446895038a910104040e01c0c825100f918010f440030482c00c01c1b0440b003925280c00982c84406214030b0000d58202c2620f00040594010100c403460f9401040038800074002c051343c006d102400c280d5404401020802c0e041d030b02c3e00110300c500c81e010340c4490340b03140411402008000003440044025500c1c3e5481d01c0e11034005500544014210a00911046826000300340c02d0340e204032480c10107050568a1601c40d440640300c01020302c07085010700038000c2510541200900035142c003c00e000240c031105071001908640040c2c00c031300c005a2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 448021582 1106 448020476 448020493
    0x60e0a0605030703080d020f07050619050601111f060f0602150709030b0f07020f03070308060f121b030709240501050f181302070b07080108 62
    0x1102400400515070340d2002c06035524403600c0300622164080c80148803451065024210b01d544c00864039280ca08959116414840d040700c0080030800400301c0d8510b142294416264410420b007000c82e0034084001c0c1840d40c7e04040002000f9410400b412658204003681094000b040d005e041d00340e44945600001e920f4160701c00003080c481c000b940014240501c60890001101d030001211243c0380c841800000f000d040040c00e40b41548a0008003025484c0c0400007441070a000355151105820030700300b0003841da400142d00c03900c210071032107003400c0d05400402d104810320068108107034802c0c810008242080159845901e48500e4001c50035800c0103040c0010071040c0000c40f1a494284d220401910580240c2100900c902d60511100c80c0000380040000a1401d00074502c0c101c82051421134001d0b03078070903032040310b00d08544011301c64101d4000e55014050b201c90005030040c2d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 447841726 448021582 := by
  have h0 := BRFrame.cov_init 447841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 447841726 ≤ n) (h2 : n < 448021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
