-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:48:35.880976+00:00
-- url     : https://prove2.me/submissions/33bac1bd-2525-4f56-933c-aac6869efef8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 16726625 ≤ n < 16906481 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 16727875 1250 16726625 16726637
    0x3110405060a030e0f03040b030f01080c01050406030e120a03020a0f0201020f09041a030102030c0a0306080601050d06020d09020a0602150604020304050c0907050904020a08040b06030a080d11040905010f17030a020607 95
    0x1104e02903140800c182c0c0680341da4800400d0004d85c102c0c600c0000d61040995101150050342c1c0ca0a00d80d03981c49403140d045020950078001440554821fa011602c4000c1030400c03181d0340c240904240d00c85900c01e04200000940002c3c1d4a40e010b60803801c484d015423000d100031850501e90400c05411401400070741446035841c2c1040c41401c0412800d07008500d64002d0007195281071800340001954040c0301c0c0b4001080c10480006014440450b00604882c4060300e603e49018240d40c0f014025800b03500e0704220b00d90b8503001d050158440940b4040982081d800915101071110302d0b081c21403400807c03a6216074010020080024004140b6852918041d01c0c5a005510360503000e030340c00d01880c3c2030290098800300b501d18419510820580c000c0b4010201680152549801e1542fa041000405009071500b00203c2d69404800d41c810319285000400032403c09448409007000e8860a81c070840c44c40103240020b0101c40c0c0c180d070300030098520260045185c8020710380081d4a942c402001c104c14002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 16729125 1250 16727875 16727891
    0x70614130302090a0608070608010303050703030c0c050a12110c0a050f030709020c03030609010503340503070803031602030a0e15070209100303030e0703030e0d020102010e070902030703110405060a03 88
    0x8058035588024640c010601032280c0b500302e04080013005030384103500700380c0700b080030010310381780102c149a050f6a0950b0b1014a0078030305481c150060001c00700403108105010500c0707400310b4018060720400fa403154040c94070141031440010309008500c00e009116803c0408003280c55943c00f40144201c55007a40c200001c1d01c40500040c3c1005059440400b007640001f904080c510400701c025882070808940d843c4a03030b62034105042c0e4074009403032420301050200c50a0f082000485443c40c0602c080590440140d44c4c4031004242460941c1c1e1141584d0380c408028894048620b00941c11702d44d0561005500b0300038020001829429801c070b5042c0152006000100030544010450b051250040c10142285c10950103030308002c0000d1000b40d00091a103110710210040c0400c8010803240c0540c3e80d980b80c80c0c400303401c0181504110204a040d0f40daa40602c856902080c0401e1008048905c40103860386001e130800350136180c0c00400f02c01d8008082100b44038541d00ea8080c1c610031406807400240d005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 16730375 1250 16729125 16729147
    0x507120318050c03010507050403110904060e0307030c060b060316030e0106050a0303080901060f08030703051c051006020606010c0b0106050309010906050c040618030503030402061606060b0318070614 88
    0x22524007541407200c01030400c08107102e03001036078626141041c0d000300700580c0c894004031840d000350300008002c0f81c3c2c04500000b141c9030035541290028003a03840041c80d0720503c02c05615540c480b28048003c5940c0030551001e0189e140318003192220107031202882c40ca050016140307030014050303008003030640c0c0d003850175420403003540407101600f000390261007460380f241405001600f04503180303000341d802d0480c041000c0d551940c2c004115440f0000440c100400341da8151055003000042d650080c4c400c80fa031400c50505c90240300c1c0500010260a06490b040c494009d080440040205050080074060400000c00001d40315044030820305e0102c0d00c03510b50000a80c050118075101408050a00040c081d040a102004104a46c0951181d698401c24500c048464180620010b08aa0014000107025003010f100428030034210322507100c400c07450355540004441c0035402000b00c0750300110811620012500b40d00424446000c0200407441c44c1510003800e8800c110a030400115021900340010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 16731625 1250 16730375 16730381
    0x141f120b0d060f050912090f130f02070c0602010e03090405040f0b07080105010e0d11010c080c120403060b120d110a0b01141c0804030206030c2709010503010c05071203 74
    0x240c000414844100c509070600030068148159102c05041c0fa11011900c1c094000940b820300c07413041c0c030b03d86042800036000c10a5050340d01a0040d00844c038428080d40503551441004800280c078040143c0f110320341d00340f588010700d082c0c00040c20f5a14020000c84030080000139282c52030b200f10b601007120381d51031410700300841002c0f00c000c00180c100c0080c0041c0340c0d04159924140c480a0b41c0b0f011a80c40d15808000d4500700581c0e02a00280020042c0c5c3d038194412076285010900501f400c2d0b1a040028020914010103d2030165034280b0100301071040002e0390090412004080b1202a0850080241140c5815009103110300348110003d80c4422500d051254805007604140c072054251ba444401084030000d031044640300d03c0418403200744800812140030b5465410000b00f50615055609002996001800440143c07000380000709141062000d0b8051402502240542071802503040c400c1c9040180c01c840c2c8a47d041200101809510005407400d143d00710b00039121201050b4015001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 16732875 1250 16731625 16731641
    0x30b100b030f010320011e02070b04030305040302030c0402030c12060112020703080108160b03010605030702010f060803070303051005131a0a0605070c0b040608010512070b13141f12 80
    0x14004020082081c02c0b45140340140c100c0c1d000700c6000d07061034000c850100c100451550030501065185590400d880300d0003102c0e03070b0058a0f6004403801039444001d445d0031500326510480c0041c000160a100b1400c080c440258200300580c0e0650450402e110905a50f001e29800e47da142200e81c030028226070b03c1030442c45000c0143c0e144c01c641c0c6800c2e9080c002c1c0040d000340507040003032141e403606001c50903c40c0d00503400c0b5031141024038116424400111517590000e441c282c01c5648410750315440741600d01c074180041110900850303840c040c500e4040c0c15500014041e1807a458007040070040b9403605e54403034182d070350159400202d2003101800f0b9170606020b20419504161503101c00300d401c0b03070020010041d203401401584a078981d50b180d003010500c618007583d00060a400300401080c2400d212990516480c5001d842015450302e81922013074100d61801074030051050402c100c0e20340c844112448031081505c428403190340103542e040010b038032603140c6800c0101c502d0081460f45465801a84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 16734125 1250 16732875 16732889
    0xa050c12040b041d04022d0603010902030a230606070204090f0305120a0b010c02060901120c0203030a060503010501081203040c03060c02030904050f0906010b0d0b13020403030306061701030b10 85
    0x1440d9511100c8011881d0050301511070ba02000551907a68130202d20011403085030300401c2d4180340b400034240992a20310a104c440319401c24408400b06035691b10010718040c0c00700e200c1c01620f91400032040b00c1601c904850000c3e003009500080150100c6240020742d001506913084d40d03135428180b000c20021f2001110103080e90440758910010140c2c410700801c002400514541040d4036620400d4017294404401c55010445034030800c40103080200141003420700504025020041007050355085c6d82c5454001c1006030000400c10041c50110f00c115406040b00750300070082581040e0341c45580d043c0202000003196070101c0041c0401c035a41c0c0c06d0342c0c0034592082c03040c08070320240d54010355260403000c0400e2259080c0710028031a0601801103134803880341d110017000d035139182c40c215113150340c03044c012107184607110680200d0607283c0140c412106035050900680d250310f9420000c007141e03a960844000c00c103442e522003503011004910141903d030404000805504c41c5038501440c079140b64803c0d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 16735375 1250 16734125 16734127
    0x702030304080307060506011103030609070e0d0b0105090129160c09050a050a090510050907150203070506010807080607050f070606140306060103020426070b0310090b0102010903050a050c12 84
    0x100e0b006001001502c03002c0c0c4940c0c2c0c00d1000f625440015160f10888031928400c40c3d0050000400794500035121540200c1d00c0d00744007400e9088d040100d1080d003500c181c152600030003100108410704051401034018a0506081540c540341018003101500703200c0c10540c07001c1e82c0460075203160a0645c105441042d40a4510301d007140da228200c1010348002c07200ba04100785040002546000103020302c4030256800000380010780c407030070303810002850050b010440921030b110002c10040c2c4540490108104141c0003103440c0c1704070780f50003403601c0790503001513507540c10029040008110002e10180c0089240c01e05d0742d110314032410100040d002c1c03444003800b4103051001c000f44503a140c2c0c1280080050944c01d41d060741d81c4400056060384203a101d40040041103c0780f0b480101d01c0c08651140d04035424041e200c09580d521400c040c181c0040e210100c0c040c5c40c4881c01c01414410344103000d000003023800280583c411544000c1c22030300905c02c03103100340040045d01000f840c005000c3e02e80d410781c0c07000400f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 16736625 1250 16735375 16735379
    0x3221203110106080102120106180b0c010b031c0c02010c05030706020d0f0b0a030203030307030b0406030507090c0f08100e04060f0603030e10020105010308070206160605090a030306050d120f02030702030304 91
    0x24107040441019000075480c108000c20215418021641c1100500100c140942d1901c1e0f001c4501000344118243c0426041001050280003207004103402450306001044c4045044109030408060480740500c580c607a4a411490580201195900e140c0900303203074051340e24034241541580700e4844000e03d100d20000e140900c1410a43c007400f0480b6050b901006015000307001e0120504003808080d50641c81400001c031003c0c40382e0803214038418054004038403a40e80c3d82d9100c2c6017013102d400c42201261105596070f09558000c4c808088901a854010141c2c20181c0589520307800c10f00504080c035420000040c284620354200f103100035241c0e0307420001c03139603a424000c0c00c0c2804c1c1c4070342510070200c00c99141030043c03050140f0fa060300d8102c2c08951514025a003042041d901c0b200034440300c0c0340401c200340081071540c800e842c13082150001602201d06145801803c48481e070700828070130b0101c0d00ca100e010441c1817a4403100c00804c0d003001c0034001e080340010780c03850254890080d07140c4000500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 16737875 1250 16736625 16736627
    0x90504051905061501050319020c010612060203060118060f050906040e0403020a0209160806120c0a060509031207030f0804060b0607060f05060603010b0a14070f06020306130e03221203 81
    0x20071413007034000d495103069100062004640b14401615840d162110000e09018031007002da000b000211680b100004100da038650501980c1c511603001920000c0e408000c104c82540c0100002144a800c200461080c0e0b081c200b0140480110800b224200200820b618226031101c0c011a8054101840000060b2420780f50080d6035541c11001203014444060200b060603044c5d00014007401c40350b491f040266a10081801901511340d0401840740c4520a1180550744501990101030000d55440c26501e84015050624004000c011580020001c10241003c60340c00490100c01c4401860f20452584942c10302c100a0201402030076449080080d45408211195000428044c107a82d400e100942e03d590422070203020900c528403c0c03807010030404c0646446850780611507203200a41606080890719500e2110040080031280290300106000341031900510320084034106280034031070b108428072000c2c0ca0b03024005103040c0401004201d65840d41c420116a00542009413020610001c9402c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 16739125 1250 16737875 16737883
    0x4030b0c0412060507140c0d05030a020f030f010305010b010806010e01050304020a090509160503060103030c020112060e010605070506061e0f030a050f0706080705030c0f09060d09060204090b0a05030601090504051905 95
    0x7a959003c222440701d10824690750b00250b46091031f2406c060441c8400791202624203a00043c0000d9585030300300400912183c0640246008101004070307181c0319810761520301d003150403801186040c44001401c00c0042c0c0c1c4e00400342003c407002841d0554803a01e80303101081d201c00c556006aa062030034070003008050503001803489020300070014800515556030007416107841080c00040d000840710401400554020452800485080c000c00a012640e414901d05800f40c01e82042001480c000b501100b0f1000400c1201c0c2c0084046503c03030064501c2100c15205145c0002489007c0d000c544001000c540d8203010320351010b40c0000944880b50300b241102900d07046107005078000b007110080400d040d13612030025030f4422101210228a050030f0024a1b55241d0002445250700140030400140d000c01c4030302510f40d0f00b901c2801c2c0035856506000401e0107881d05445054094484601c3c20000c40d42c00040e901e04440c0c0350500020952030700c1c1400760400a00540c00a102120a410394003003001c002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 16740375 1250 16739125 16739131
    0x290a0c030507060f0c0314040b0f131a040606080309090106030b04090f060207020a08060403120911100206010e01050d0c120204110c0708010609050708070f02191b06090302010504030b0c04120605 86
    0x941c0c07c000c7e204800c0c00c454000719041d20081e00203102c8034005882c01c205062540d8102c000045120150b10103a075482c8040b0882d048903004249407a01070004001c254045d00006d4a4450701440c00c00c110000840c03029035051240100b090780303542e8660440d440b0b507031100400f66000080020070252030f0034050081d6200d41c104074052003020b080001d4800c000705046001c1d07039140d5a0748003016240c81203040645445c14080d00c10725114440100d0680e01d007a41c2000d000000c0d0044c00180d8034110200a12080580c085405988454101d40020720000041016900384083d42c8036041c2030f40c008640106514082c005c0e208600144850516000050207030440382c80c10028403003992211a070f0000c0d1502910004045400a400b140c3c01074002c030129050004548100c89141c024010649020603400c034099601107603807aa41c0502c0c807180e407040c10241c852800d041d001a461980003c2017440b95202c041c1400404001280c06181c0400c12a0020f204c2c081032036800300300600340580101070503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 16741625 1250 16740375 16740377
    0x309192f0a0608010503060117030412050a02090106031802090a02160c080705060405010905040902010e13020a030b06070506010b1b030414030105060a0b030604020705030d090c290a0c030507060f0c 87
    0x1c03050020700c00344580700c2a81a104040d02800450b440c1049060803046401c0005401c1d000900c000310704000200703006080710380140005c1692040d5401800b03c50001030300144100b6040078119184082015498403500c0c0c1e050354041c0c903e950740c004240080c0034809a8100e0400a940758030300344480581b0460903103980800340d41046d90b891040080520030313882228003151400d1800c000c107143c135501500700c4500604040d64280003242c001744286202260602c01203501084442041d503061003004010700c400e0352807510f03141e003d031034960392580c051180c801c24001c0010359a4055601c0039040c1140c420210031a510703541c072458500c5540d4121100240650300c0d000c0000c42d540741111131841114807951106281d07440d500c05100180d445005d00f070394544000c0040d1032205130b203882130f100100c4c000c0ca16054018105211400c2120490111031307284c00034021003014465180c011101000c000d0704000d41241503601e8103407181c0c0940f00004c0c0c45030346022410719071220260840d14481c051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 16742875 1250 16741625 16741639
    0x2030307120c0c080a03230114091b1e03010602100507020105040f080a0203070f0f1211030a0c020d0203011409010e0a050304030f02010504031407030203010b060309192f 75
    0x24441c042250454629880014500190140442c0d12000100b280740214603004c1804d0400703800500b003c40d07408101d410741065990040125280c0b043c0c0d0482c107540b04459003841d90500b07018000000c50002d0909943c240300142141504c0b0085201d8220700215003081d580320340c3d46074006910382c1c16411803e030704c40d0b083c9000582114410311610748a6a40510100c550807d182c641801d1504045035200c20742c84104031820105143c210600c0a0310710500150000c07445a251088030070f104110000144056030008100510313000c403d640411403907140c8801d440f0440c1c0000f0f80b900d0094980a9095483c064098066141d0011000c0c030034042c0100a1000c6008108210b5035400e0355007014060750028130003800020f44074003441d400035005140c80b605058032501c2e1200c02c0b9000d0708045840b580720520410840c00c0c01e0003040e0f04660b085400c80c0c00c520b408140c654503a03160030b51820100520025100401c00c0311084180100c64520608032024400303040d8054a14910807000d100341e01d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 16744125 1250 16742875 16742897
    0x1002070c090c08071107050d081903050601080406090507030209090a02010207050616080306060c0106060c15060e01030f03020f0d020c0906040515060f07020603070906030513020a05010f0207030b010602030307 92
    0x11140600310b02221180d40304040b0307590b042000c490303405080880e2009030141600c00182513460f0300580c41c40301e000d41081907450880c107403105c0400400c80318000c14503080600304901030f80c02140083c3d000d0340006000c00ca0648524240e41000056000207602c02603000a10a800b640018060003081c401c0e021036070840e884104011003400b510012041c0300401c880c0070400102014090340d08002c01611042c2012a0f0564407805d455041e00314000240c1e283c803103481030145404040e0000c2c0300e9201d04100c200d0400d00c0641100c401404098440850040361808040c0708102d03051a02c06550f040c0c8140d21610354000352100880007041d4070641c16607010511901e010f20903203000b00c8086409020214114060141c641c00110361400d400800380078120142c0c59600040d40300758480d035640365165040c40800307812280042c00c0d000010000882000040c3c0341c41d81e000085e203009080c10f2800824a0204900d0000340f5000100201c7c4803100000b25036800101031802941d0a0301c0340c8001e18 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 16745375 1250 16744125 16744139
    0x8040513111602040905070801240609230a03060c020c0405061c1b06030203010e090a02030c0103150503100504031e0c080904020c0610050a08010c0806041a031002070c 74
    0xd00d05540e04444800200840003002d48010307400c08600e032001d480800e801c451900c503142030080a034020a1565180c1c02c581e0f00c0c8001140e090a04003002c5010000c1050511b88020811441406028010140d0f0441e845060781c00091040d55110024104c610107a100e240500280038051102ea002d4860040403010b01e14143c020244201c1d0040c002804100300711a148103103d507908800d440815001030305141b041000b008044c082c00d0701c3d40300075030750794034290001070503a40042c1528540c0e00044240030040e500494141c511490910300481d040c00f43d0a02c0c4a40d01615610641d412300c11604511000f00d45a04421311441c000d0315200039042015206424411000f04618000f4072031490690028400e9005002c400c03401500050030306030100d410f2403a019007525039402040701510100b01d0b901d040b50740a0090b041d1107000f40556081010090030402d005800e9512a41d190a881540c2c05339540c80d00c04481c03002011900204069100d500095003c01c47c15580c152500402190070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 16746625 1250 16745375 16745381
    0x7030f0e01091a061503131a0702031206060c07060309170301030203030a0507050a06020a020f0c0619031d01061e08150a020705010905010c020d093005010906020708040513 76
    0x300c1c1d0080120002815007201d111006040103000f10b07880f107015130b0442c140708110005140324880b5100400100c100354101003280f02303081e003015030302050f08100b088603c96011080d141501da188440202c42d844110020755180101100d00f0881c1c07040c1d2400050700743c0d2503017011100302e004842c1210b1a685007501c1c281c09120900019402d64400c0241480709031081c00142503807030142d015a0500601c1c2c0d0780c0e041c143d0303000c00d09000c01603210340d9001c001460140801c00c81c411003240d60602d0006c0c282614002c0d5406088140e0505075103d001c0c06550342540d0300086ca420484000704070f0300380c5034400c01e5031440c1c8448048a0502e40003c01040d20080060349400aa140944d40c0c0c6296031690903c0340a54040101121f00d5500d50000c000014400d0040c68146a001c0c1c026103001c4d07a410800a0940409a012519803090310031030203103d0303c03003206010924203101b8605d21003000c10b04125014003441036004129503c006115014041040090000e41390708503248101d0184916040c802d0f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 16747875 1250 16746625 16746641
    0xb131106070804030305030a09150c0206060d0507060c050709060303020102120901020421020d0b07020c01120b10050307020703120c030f021501141201050c07020301200901030c030b0907030f0e01 86
    0x180d0b001c10003400401d002d08091342d40700b94800c002046042c0640c0d22a400c00b541d0724040341364940c84a41c0003080a07014440300798407134816226040030030419100c60365200158410941481071486882080c403006000c02c501800c460001444010765924009000b50300c00c10200460102c4000414071800e41802228200c1e286460040945801d007805840c05101c0c80f0012a80000c00740c54040c0042c50504c419442600f058000c0d181e556a07a000241040f500f00c0401c40c092031030001900c842c0e9491440608031355642d46855520f07540d0707980d4203918010f4550005040010342c0310b001905241d00400103402c080c0710760745220b40f140ea01c40f000d0341d80b04c0e09803081c02c0c0341c4c400030001440300f110a0400140c026000810303070342c0000040c0d9109402c482060302c0b0302000c0040050f110041d4102400b171042c0140105080540c464003089044c0001e000324102241050713110141140190f2081c3c00422401c4401444c081540c20180e03000340040c043c0410854149050001c03200300071006100c1c02c18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 16749125 1250 16747875 16747883
    0x21c0605030312071407120305060102160509010312110f1b060a02060a090201050f18090105030c0306040b06010306091a01020f0c01090605070501020c03042907020f09040f0b13110607 81
    0x3c00358035440010b03652402da035804000c5888042c4903000102c2c1000da6800c00000c501d840006141c01c144000908200100098503a01c00030030108100c9515203101b0340b81120741080c40071113640800130045030310070403504c1c45041c1403050781802c1401000205584035180141401e0709110750034030b000d2010710b009103c10080560440c00024110500e41e81000d1425441458054944400c21701d4515490304021054001035408c070842060500740095402c0c098002203004054018a400000796070380002040104400820004544940d000c2e03004031002c2c00068009006051924640010355204004020f0042c030030702c420750741c525401040f4030040080c1a0340340342415050000941d5507501004003141c45d594200300b004540c020500150001d86100b03e07882c41ca80c0400401c08034a41d5100c0304c562060042006580d0041c1d079480500400d07150280c400d014140d6640c20401da246110000103422840c40c4803c00014558113402410b6561017603007050b0208540000b03110140c00f6241d4014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 16750375 1250 16749125 16749157
    0x6140105070308090c03010609060801050901181b0f030614060f0f1903050105010605090a06090501120f090210050d0c03140f04080c030c030706060501030209010c060c050c01021c06050303 83
    0x580070030711400845511410344005c41c5c10f44c0c080a07002c2400c466031079222018031640c803802400f0240c400c0c021260840e031400300902c8105880010071584c0b131300c0350b0001808003810703203c41c01805038148a01d0740105028022101c0c15070741e03803c1000241644440a0a0301c03858980000c0452504440900300e102d405040c0740b0b001c8048070184014816004d80c0c010b168030882c40000000f590034000e10b400790495558450721606000280320094825400107014030010340c2003841a40d81c4078a5200d070000754190085203c00030712061000a00404002079085030720302ca1f1400c400c0d50000000d010609031034000300900070250008500b00c400315902e5581003c912008192810001095141c0042c01164a2031501d580c1c0140706285a00c400d012203c0c941002c200d0f90309200151140304000c2000303083c158500f514034400284136800d0800c00401207a40c4299501076503114405543c80b80c05078000840d030302e10031034454400820b414002024068180800400ca606021007520801035008400f8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 16751625 1250 16750375 16750387
    0x501080f040f0201050c03090a08070302030c0904110f01120c03050708010b0f07080a170702070315050108030a030e01060b0d0204050a050a38030106050a080106090f03080304060207060509030d06140105 89
    0x111082e900c020346c01e0320184010712400310f00b641c0b864400001003640b04002d000e09480c503c181400d10f900c03c90050300c01c1c82c2135420000810200d80300d074401018200d640441c1045000e005a81280c8441030845c01c413403504154801090700b5a200500807402e50700c400c5500d07030342d400302010035220754140028450420b02280c40007070024000b80c40c0a80c07286c100284ac0048400c1d01440b50101100d0000040c0c2c400c172020170501c12828000c14400f40c4520b0144002d60400003899540d1156606074420160780700014100b0400070361080e400b5146003060181d0f5400b4411030500a5005402034603c240400c1130b0000d274524005000504441c2018880101400060b41c5600c030300392201d41010404040c01d2810841c8865100118041d000c40d49445450f40b4858130003d100c0e40f016004031341880703500c5c207040c4007041400659104807540b2691955682d543d07440c10f280a4042c2d0040200360301d051100340500b5050200207046a11600d1030100151550340f484171001c0000200d00d280820710402803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 16752875 1250 16751625 16751627
    0x20304140f090907090e01050402011b03020715030911030613021e0d080703030c080c04090f0b030604140d02031206120307020907050a0905150a21020a05040501080f040f0201 77
    0x3125480c280180380c6000c1144100200304040c0c2c0440f120001c580000c04148041d412074455440389440f4180200a140b52036800a444805050300d02c0c50301041f4500ca072020141f0811034500544000c05a45880c07011410001d0007a140041d0200c60000d07400e241801141400100140701e402c1514210000300b58540034891152010449501401c501c28031841042e1a9132005e510014406d114040e918aa282001070458102da03140c1010068140c0520a8148184d0103807029505245c01c001220ba001d040d8400050005909154143c0956004c110a0054094204e03030342c00c030f0078001d03a5005241d09400320b072a40704200102d40b200d00510045061403c01800404080c0441c50440b45070541a4001880b942c0040303580c440081c2c000524151030650040003100104003d8604003940901e698a2a5107406940010f40400c164000d4028058062092204c3c1030360706a00304640e1000b0110000300558454002d1a010402a4020a1840400380841440f03190820100c12141140e980 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 16754125 1250 16752875 16752899
    0x3030905010e0108090c0f030304030b2a0702030c090a0209030604050304080d0206010803030705130302090a0905100614040c1701030f060b01050702031c0e04110d050106030b0102060a050402060706050103061508010b01020304 99
    0x341f141d010300c41400088006004500c10780e00402c0d02c00b41001480090050321107040b120341400100e400c506000900058400003018007100e04200c65081d440e54803803200d14002e010307145030198541700b06c1003800305010000c0010020784485006a40c450400400180d030750f90310a22800d02164010000141c0061055018100801e030030075000b01066503d8001600e080020703100381c00000d039903000003010030104000a410f524070044003803041ca450900c40980011010190302c2c0255140d03021b0b031484920605110380141002142a0b4480d42c403420050440c2e140400d084407424584407213680f503980200d003550b00b03040e4001d00411004024040640c460502081070300180640c08415820a507a00e0180892a000c2c0085080d11361504401110540e40180e006070107062070414042e82c0c59901042459001d4640900820562281d00c0030a016100e45000035141070300d014008420402c081d0001c0b0144640c1d060348188040d00c40c5280307405c03a21010f02e45030250380f0400042240b4410b440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 16755375 1250 16754125 16754149
    0x106051c0302160b090a08060717040501090b01080a06050109060e010603021305060a0e01021006060804080c03071a0106080f090d2a0602031014030706030203180703030905010e0108090c 82
    0x220559400c07440f032000905003004980c200642e0242c003c98109264144403807040018520100180501c0c00d0102016081e500d01862080e80c0711004000541445825004005555409841300c245980d5400c6000d445502c000401c0b03800e6800c1000010301c003540c5008410981343c0c04103204809034a446400d40c001c0d4041c400350b01d14900b032802c0010349655050060055100540c8542c800034403040002818402e00da40752501c6035207440000c0c0403056000c1303000d6900540c04800703a5500c3c5010700b141c0d0300d903015003030340103200c02440d401e00f6460511680445041b034449459204a6031240360301390a010208440c820669409210a000100d01c142103140c040507001465820084600340745480f9800292419201590000240f080080c0d14480001c000c10390074900c00c9550b42183c1c002600d0303068074414482090780100c0480d600c084810100758841d040d2208884905540c1d1030090000e00070f40c440d01d808a0020100c4421550051034803d1107002c1c810040c0010501c100100a2440d07488 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 16756625 1250 16755375 16755377
    0x31303030b040504050304180509030301060302090a0f09091a16030b0406080a0b04110607050304060c020a090515010807020c0d0b04050a020904030908060604020c0307021e0a091d0106051c03 84
    0x10708040140780c0b100c0c8181070007140964059aa1a41400249010081086001e120951420042104410010098a040d5074681c900565141c1d02040010081183d03500101d401c001640710000310203059600150038203100d550603030004805800107131078046045030701c840074104c48004c071846940309500011060000400c0050041e882c1c861040c5000c900400032909480c81009110500c0052061043c003103204640052420311184e59113501c0380154843c2405000e81c400c020340c11550390f440320740041d01c17031020308100d02e2400340f000450b0300c1c1408801901194511f800729041c648081003160284030f01800b0b07424010f1070703940c507203c0c031080c000d10940d01402518140c000682d1911499070055020b940d0300701c922810f00002c50b08090000c0d107500d1082d4030402c00c0e0754519201009403038440380c04640c4009200742c0b042000c240b0340000b65203030b54044000031001c5081110340c0e00c14005075640d50081068001c1d500009400c94105025495101042e010040364107072250310700004c01c3d846 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 16757875 1250 16756625 16756631
    0x90a0f0e010603030c020f03070807031203110307180605090f06070501061502030a02150708010b1c020408160504050f040b130203010c09050f030d081b04080303040f020109080102070803130303 85
    0x3a8508450866009410440008009541220652401032a81414590b045014000c1d091420035155941c103a00d10004100213442da80c4520010702a03800046280040d844466a078a4480c1009007060034414115043e034154441c0030032820f1040302600c2c1107100141580b0400c44507441000541e0300705071070071241c643d2108408a100c041c0001085000150b40c0c00540d120140204080e080460880d0301000c010058000c0001880d4000e000504559514012a070740d400c010030802000301846104012244c00000d00180814002480c130100e800000c25148002d52203e0402c029110152202485da28514022901182884001300c4d003000800009254a0001d50301281c2075800c121103082c00b00b011000c1c100b05904000300783e90300c0080114040e00040c0aa91006051150301810407148404030044c1c000c041d01003901180c1c040c03c034641c00c49803039152500e00200a50000d9400303c0c0050803c12000031940014000e86541c540d02120345030540c0d892055003241040b458800781d08241d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 16759125 1250 16757875 16757891
    0x90501020c03040b030603060f13020d030215090303090d09031203050c0d11130509070804120c0203030721020304060c060b06121e130201020c0603040204090803070201020423090a0f 80
    0x1c000c000600007042d0510f0b99139100d05d0000109401c00c04014503d000300f46541e010018464040d9244502495040313559061021880c20100d290004031000c0c91a042070580c1400f0030060700001a600c43c03070b110b00444110300360290040341c0306800d40c03000a105049000761640810b0294108507071101e014003600341001c1850000c04241d50080e0600c81c0100c0c400108400203400c0d0701410f0000d898191205a054141024024200c0d00004e0029128400700448810480d01c591907000880b0340007822070340c0f0b514180c1044511040c0325608140308095403602d04c21624004020707101200c019480d801501c120035101d9801400802401d664007035410001070743c200710058a41405105000d103d0410048200c46000b408040075108050008201803448010307070b40002d98154640c4151000c2d9120b44071440410050030002500519003d0044100082243c0c1503000d030086a20b1030f030008003c400b0000c1400e071001c015484454002c1c0c410000515030381502c0d0081c1289200c49900061f80c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 16760375 1250 16759125 16759147
    0xb01050d03050c07060c020108011406190509040f06090608070f0b0f0702040c080901060506030c0a1110230c0403080d0207020f130b010801050906010203160305070b010e0a0c020607090909050102 86
    0x2035440c0c00076400b18944040040c10b55174400c0d03c0a004d0050820600000381894001332424011085644202e008a07425440b40d076102d2416512030480103002808030203512042c4002415090050601503840d0800c001990100001c0b00d90880350104d01e003e80241c10211240010b511034400080c81120801105c0c3c01611240b05041034107185580e503013540e0501c00c1d035035400e460329a4041c80c4210014402c2c05001c8000e1300444070920081e081909220b01c40c5280c0d81d0400d024042c00c2488a0b00d040b8606198226080510740104028950650181e23180b0315200c9240c000d03400003a00540c1d06020644100c2e03007035401481c1443c0001d2074003c1d008032030030015500718a8001c0d55440c5e5a10b804a82c4025600040e0060150104458012103840d180f03000039943e02604461442d000f020482c01424940694202c40d4243d4004651401c0c56031210042ca0a00000b600d42d00c01480c609100c445c0c441e440491883d0083e020340c2d540048051802003101c02900502000b524155030030014501d00c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 16761625 1250 16760375 16760383
    0xf0436020910080c10120f0f02070f0506070201050702061b0705010f1505010903020d0303050714030a140c0c1209030f0303010e060a080a0b06041e0911040b01020a0b01050d03050c 79
    0x281408a4801d614075007454960740c00c20702c4d012800e50243c035040041c968072980000b0441d442446041c00020010503004112001d088020b108440c2640300045680502c1080b031a9100414010030846003192200f00c4100d0880d0070448030720700143c00c001c000c2441028440c691041c0d00c0c0c8480b00c4141013180780e84584c2d0031129040e0004050640c1c0d0403842c01800c04d4821080d00909007406d003240c3c2e203850343c0c012a0f4802040c281c02010159981d0000d40340500604a40349812a135441c0103031249409002e030310090a00701c40c24008102d001c40060f041159240468800f842090b0144c0507451000c80b1842c80750300485003966150086480351004a581000554009d188440028549081030b10521544c4200c036003121045e9000702942c00c0c0812922803441d034000ca000e0301d00040018064100b640c0340c80c0981c9a204200381030010303540a00c0303000c08510200301d41c02c650422034070190400580e650101110010411600ba800403c11450000340300503d603402030500601d81001060840c0c20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 16762875 1250 16761625 16761631
    0x50108070b16030c15060302100c021302030a090c0b03060102010f090503070f02040e030c0a12091a030606070c0e04060b03010b012001061511010c020610030212070807060306050f04360209 83
    0x117119074400e020000e51510240c411a80c01c000d043c05045a0056000b04030142c0c1288000c0d03121540020205061090f40d900891a4a0300417282000c40c41e20344201e10304542c02521038070300540c00c2c542140d808902d184640452a54050b004510340032040c2c9d180d450000d034503034007664010f5481118610201d01400240071300b0055030007801c45064586800d150343c40388400214100001490140180082410140c0c059012840a01d0710381e60748500007100b9104000009001401e88000040c00c2074016800c10302840c82110240b00b034000000c00c0c14202c42601c29464001b0350450100e620003441009203105031290100085008c644842d02591101c0309182c42000156142d0000c4065800a00c91111440882e1000c1c3c0858180304800c801900f04500010740b1030703d0300c0340700030201e603070304101070001400043d05803101c00750b90301005801040103102e134030b0146040009804c0e00c0d1034a807184080300901c60550408080442024800d8508284001d0440e105e400c2040400b507130343e20540c944 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 16764125 1250 16762875 16762913
    0xb0913030212070201020606010c08041212030e01090b0601030908070203030c03090907080103050703080f0c010e0d020c01030605060406030506060c0a060c1b05060c0c0106050904060b010201050108070b16030c 92
    0x1155421031500a15210204802411840040c045040181c0c5d01180c00c54014209290654000c0c002d414002182c2c0310742e034400c4044903031003507a0300e0400816045660b4101203d4804000d0203149020160030b843c081d1000030031110001001a0496000360b00000c00240a81c49880c01c100c0343d50302091071030b4000e4450aa441d480460061160f24142c0c01090f4000d54600c2c1c070301d075a54995500c055490742180401800d1090104400640d41c280e003040d01d0025180000906c044402220300300d4a0754400440800113015001303e183c0294064040d090448001416080c60186090003c8008190141034039620104c100b10103606a901005035220f41802140c0004a401010b4005840c080001410000c031403000c2070424081007022a04076840784070b10300c0c0c1581d909180420680140f580b13030403841c1c3c030030511000d000c1840380380c0d4410314003440c080c0c000304001d9888184060340d5525501ca2a086400c003004a03241028440c2030b00c004480c86030520001240f620341d115182d040c21354800310 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 16765375 1250 16764125 16764151
    0x7091107060b01180306050a02160c060905040204080c09070311030403050918010b07060b0303090a0b030a050a1401060c020a1208090a09050c12100509010605130605090a05040b01030b09 82
    0x20301071144140966080c090920803544180344c040354014456511000e4809580c0320005012190103030100d54005042c0484100c107940c1c2c40c50541e8014005004890004000c04800700380c5042c07510841c0c2c1542c250310003c2c411803481c001004080c0034010510000c2580701c101c51000170001e04003850189200c1e4440d10780700d03a40781d41807101190700c0180d00345100301050f00410501074201d00301c400c41d580042c1d0100c0d44294600201c0c3c514030030345034125003000f1010b400188044086019600441e081c0c0d07818425600d03a20002015160340150041031811080c00400105015a910025051000e009511103d540c0c00e8481c5080c204010144c44210340042d800b2a689400d040f101c009c0d002c981010030850038020b43c0d04486000708a101c2c204a403940001ca041c81d1719918070080281170042180c043c0c0d40e11080020800e4121110703d9042c03001081c40480c0f424050800e56100500250100d00003624082c01c2002030030841100d43e061543c0d440400989840f0850034034412424000301d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 16766625 1250 16765375 16765387
    0x90f13020309030a0e0312030408090d0209010f0512060402101110050a060302030114150103090602090a0603290d030503040303200a020c0604050a0b0702121902090708040320070911 80
    0xa003176000026052440394015006070444c02494001362508203030441d100301e807550034000101cbc40f4035440c501c0184d400301e02e6000004040100307141100c00e456007502c4000e50300a40413922030303403810b007510000e40c42804180400300d143d03c40e2003c04d0302191200c0c100c4440703080e082d0480c8201c03001a120000400d444d0034080c01903060034001c82c8000c002c101c0c600031a03890001c41141155808051181c100f545540e55103040c013000380c06071a0922801403141000ca81e407000060010300c42051510503a0402c2000d01050343c840380f40f40b101902e07010b030003030844132072980d800c444680c401001282071640c0e80d4001c0c1c3c08040c1c003074840310100030301c01481d540c3c42200c20b41c060b02c1c2100310302d079142c07040d00204402e20890b140e50440320100c03540002c10f00d0303d031400c600c0040e088c201314000b0b440252140a480303400b44000e41c125280300c1402580d030a061034450748002c951016045a02a012540e401180542558132a07001d0303204410307010035a6031494940c1e144030142d030311100140c035070041c3c08592 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 16767875 1250 16766625 16766627
    0x1909030201200703210605060409050711030c06011a220906080d02030711010302250611030f040210110d031509090f0b040201121d010608060903090f13020309030a 72
    0x6100601c0e2042c5402d906142440d81d0080c03507502000c00b2500103030f1041c001c1010300c0303e45411500141800038010b684950304e8180c07980003000115400800a99280c0d4555a03064010045860703044150000e40b0140c0e09000885022800b48400310540d401d040044480461076100a0a0f03078015441000a110f0300c0c0c200e401e0180c0b04907030018542a044581c04c007046980010848204a41c048010803c05070100d005070000c0c0114401c44110000841d005030102204c21521507646201d404104007400d01d2142c0c02c5041d000454600f0302c0181d40f03902040c05440c222444200740c00040ca4011402c420b501c203440d00b01404941240046a25000c40300304100a014030300025002c914410003200040703494a0b0720110b44140c0207003403943c110003c9001d41e4494681242c0d040c1c01c0c0c0c0c43c240f04648140c450841600c024207003082039946444408a12200c01080a03805683e40e40c00031402e1071b4510003000301ca400c00741c214641c8070f06207441c0311904010f47e0004d9481415601d02954480580c03400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 16769125 1250 16767875 16767911
    0x110a03140303151f0c05030d0501062102030c0406080402030a02040f1e0908030402060a02150c0a02100b01080105060a09030204090f0210050702010206070302030a0902030a0b09250605031909030201 87
    0x4a82446a1840c08403001009240c03803840244445900c5e222442c2503450800c14218400c20007501c40c0c040c10000041881b035000a90541012102c2101c0c44a000e20560280b04900003901c0d1016070f10380402042045500c00c6960b96007140c001400c0d0bc5d0300e0859503000508503005032241400c91515140420082102c1260b1000440760303a000a2041001c541d4581c030551200500c028801c04c0007094040c40c4a200b00082c01c12203046400c0946181001ca0b40e8101c141c102c40582c00c01031103281101d003031030501402600407042e01030b1a191503903404c010422070240c010645020422076408000009039889000d0004170500503204030152a03c1401401806501c0240400070b2050420145005036030028440d9030040451800507100d44900e50118068101000c02a50510403000381a0070700980c1d100e040e000310403401c1110809814140a0016640e8070148110500c020840402c11140550b0095a004c40b0304500c10140e1501d4924a8044070100a0180c2c0140e43d1000000d0050070280d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 16770375 1250 16769125 16769161
    0x90c04060506130501030e03071b090f14010312020c060301090603060e030a020604030503040201090b0a120b0f030c04050402031f050f070c02090601140d020a11070902040e04110a03140303 83
    0x3a070702070710f03228011003001030448051103034504059940075801c000441c1030082c4c4182d82e9009c152081c4040d80b000c2c60340d1340034603140038503410b092504d104840d107a40944100b40d014455480300c182141c1c40c40e00c1d151008007d04d440ca509500490740601804c0d96030340000c43c041c101100300043d03003a00f5404c200c003c55066295800c0207500c20055004155000966140d11aa243c81c0c21740d80d079906c9100403036034000d41e940a40904000807502d403012540000449590340540c2c1010032010700444100b1140e180c50130707040e5030107420102107402c090904c2d0f0401a07000340050102c501020f5100b40c803a1007510079030341801d4495912400e01181c001090011a0031031002e140242e0070ba2581e40005a4a2101600f0035050014503440852001d550b841610f40c40d2012042c115101c1c4001200680300b1648540c4807001c84c01190300219180035644261025a0300d5441a490b9958030f070360300c560301480340004047e40a01c0c01c1c5400800902c072402c96070420341c0600c000d55102d06026142401c565003403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 16771625 1250 16770375 16770379
    0x8090d02010209400b01020f010519050a0e07030c03060e0c09010509040309050913020102060903030405030f03100503030d0c03050f0408090609040908030702070303080c0a020601060804140105090c040605 90
    0x10001c800036035841040060440c2c0011004103e0458900b1400c443c100c042d03005130950440c00f40b80c211803610f0b03c2c2c1c818203040400381c094825030303a01f00d0512400c9840403a90401101800017081444030300551007540e010016660026500000b2209140741000702d50088405102c2d4190a1040102c1d60184185001c028070050410107001400542520713014001e290003009580c000905240c03140d00c06500a290250800c3c00a0920342d0101c0d03100003070b11005034054031075040030030b14810b8000110f0780725a40140185080903182c1c1c00c0755407158030180001000c402d4070840802c850350300344014251041000400074411041c1140501501c0006089050400081c0c0400000c241c030a403c5a02c1424101c98150755070b00f55500080041c07010a202038074051010040003d41500001c0390700c25640251501306807540c0700f07903010890303119405064006801c5040100400d0b0700465000d0b8002d44030304000301d000b0101c11822421201c0c00c80d140600ad61004490004030700341803003040040e05007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 16772875 1250 16771625 16771627
    0x51c020f0706120b010507020409060f0b03030304050a021020060a050a090302071418010f0608090307080a080c0d05040c15030c0e06030408040806070503040b1e0601080604150608090d020102 84
    0x2030b00c5805840455080300b910101a02d035031060302d0a038030a004135a5541d81c000c00402c00c0000c00e040a00041000180014909140c034a040340946400010b41c1c0c800c036802001041c12640f140c0c04d0040d03894000c0d0045050120303ca030300100c64203004255882c00300032400205010b107000c0302c40300140c030b4028190917285803511400300007180d40410400103440b003078045000710400d604081516001c41e20440032041c4039101c004201c00325003040700c40483d0300542d50301a19032510030311181c903031054000c01841d142c030030004403030954002e040c89a404014002c0c2142130110180031501035410445040395412002d800604c80003000c4450f141c920300081c40c0c00c01c0b200c0203080025142d521526006482803201000180c1085400b1003260068a582404c2d0707030850401d030340d0140864200f43e604550040400c00000d00480810b42c14408c01004428000c0c402e07110480151418200074045a800c262070715007481c07500d104030310031400620240d50b40505030701c0c01c03118260415820800800071640 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 16774125 1250 16772875 16772879
    0xc0c181e01140405070207090e01021902061003060903020309060f07020103060b090310020306030a050a051b0409080301030303020903010f1b0207050603010b1e0405040c030609140910020903010207051c020f07 92
    0x11002d1a941d00b010300607100020282c440b940140d00d8201283e114500290030a0406501d1032019005400d4a81d591078001c4d50034008400140d031903083c1150005018040d070041000841c8168002801179800b0f401500d15000c10840802c8103a03103d012020031f0034800150217811541d151107048020500d445507507082410040009072210305120001d8445600803010540541c0e0900242c00c690b42e12030b0031103c0800c2c1e1460560740b40c090840d20307120b03085d4918080d00f050b400d1a00440d0080d41e4008080b518607070a55600341c00035000201c0494140d90303a4407106031074044030710804e00510030305641038051450003040207203081c0780354004601800c01030004100c514241d409561114190200c004520868000100340d140a141d205503402824810940c02c1c5036019406401503851080c000d01c400198034100c0c0f005001e081d24420907650000201d514440742640c040e180003000200050f180c641580c079030500d4006040845510360000c0d80c00703c0003050b01003010300c076007108080281200d54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 16775375 1250 16774125 16774139
    0x709060e010309060b09070801060801090209010c020108130c080610121505060105120a060906080a020102101505040504053702010f0309150501180e07030204020c0c181e01 76
    0x19480c00c404905264446220400b04003d5410642e8100c6003c1c0581c0c4040c07405100003009144203200e00000304007084000300d2417404500840f054000e044e1900c0e4014801a03004440013007005160f0080c0b0b91003d50010001800100366400500300b010081029040c030012080317280c40180e200f4100175a44a2100c000905a00402c80502c103083c400054266585401640c1d140b08043d410034100ea02c0504002d038443d0258083d41c1034500d098810000f480d121849241e460450a174040d0169124003031a40d540c01c1c40d504000f94085804803d81441340e40e40001c281580c2066608540d2078000c0340e8101c5000d00c02d00540031403888403003100100790300ba503100e0411041105030080e0411594051400b000d42c01307900b0409a4981c0108001c0c0ca82e090a580b180040c07c0a00994080301c0191380c044c0078901042c055082c283c1050700c0038145840c51a402c1000070b601444141605009409101d6850390711420040b2a04510000c64040740c940881c2149020b000401402c8120300c080006000107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 16776625 1250 16775375 16775387
    0x1050a0e0402060706110d0f05060919050604020c030a020c24030a020702011b06050402010f1d0d020a0f03030216051801060e040912090602070f06020604150b060301030309050306070906 82
    0x12a406403031055940c1c83c05d0420704c01408105545c44003190001800c404041c50b2603001300d82c80c243c1c8850400450b1644810868186801c2d240040400e4041902070a00e202540c0419045000140018500070030700d44c030309086401c0411380728056008130b50b0000150a091030b94080f0150011100c07001701408090701c00b45404042d14241c400c035408180482164000c0d032a6072420440707030001c0d040c1055180b4041000d084226002c0f0f00103100b000d421781405010303400034401c03c8040a1000503140411091100000c0f0741e003400c0e640b00100c4800040e003e94500001030246003e0742c003405400c6c2400c12103010324000c03603000c1e902401007281d841088c803a48a0070141586d0303251505614210404000401410380001d000c0e020341c43c0040441c0400d90000c14400446085800f030b240c03041d544202104104c0094443c8801603000b0000181c006101b0703e00d4201880f0b80f28100103003941c0148040740503a0130907003044000c260100010f118514041044035232203690b900e024020f5609060004102d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 16777875 1250 16776625 16776631
    0x90207030915021908040306020d020d0b030105060901050d02030709020a03140c040f0b030a1416020114010f1707080f060106030b190b13080102030a02030609010f060903081b1006030b01050a0e 85
    0x26039440e0700c13040200702c03400e02107500443d0099070543d100c143c9010301400950200002510091030050000301030b080c10f0054510a00006050390090fa00e070405004651081c1d00b000c0340e143c0540c2c2c40c04101c900c01c61000d000e481c0741950780040c04d91100c0d001c0d1001c1540151180a078840107201c204856040c5501000aa07565056101d4498036000d40e0540501204503209465000d0441001211906074450b0826801c0300c1c0d000b406142a80d00400404510a0003064450032416005004201c0b0583c01e10301006050011607006540d541440740c28115a580b9070242600008010490300760725000f220080351080319030b08080312a1580903860044c06114000c0d580002155988000d558100320400034000c204c001d666174034200c45000020361040300c04c079224100d100c0c00411160340b8400760340700381c80c2c13140c80d441c00090071503c516006401081100718030959201d6504141b040521210034422982c500118080c0d055151141e000d1038143c01284c024024404100009000c1c045480e030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 16779125 1250 16777875 16777903
    0x60103050631060e0606040b0609060307050903030a0801050a09230603160303020a15060303080c160204060806090d18091e021b0d050403110603180709020703091502 73
    0x40b10768102c0c01501600b01140606524a02c40d8416400901c0015041450328100071010b80d220707503861104220881d110001020340000c01480b40807101d0421000860304410036050003410030704100300003032642c0c0c0212050400100703100010883c0e03051003000100500310540303050007001c00c1c0241c007001094a0046140c0c620604102290321510706005407901a8511448825070989034100655903a0051400700c0f600070508022200c81410351140100b920f6140e81c42c1005074072644810045078105510800c0003040c20200900142d407603101e007100410311180900a9450114046418081e50444050501c114200d0745400c4e140300502013415910390441c006104140350070307010800c06558401c4100c041c400583c2c00020000501030f81c1c1142004000c64008401c03080e002c0310b0b14081c034800101502c41900c0711030b81900d4440041c1d68082209008902c08004050b41985004d12540c0301300003040e800940c081c02d050b800403020010340501c050201103c005214029500d02030880a12 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 16780375 1250 16779125 16779151
    0xc03030f09040506121608070b04080601060c032106030b0a0c0801050d050304080106090203040c0807030c0605030405030705060703020a1814040905070906090605040c020d080a0c030207050f0304050906030601030506 95
    0x101c1c180c0d264180c1c05d000c4441c803021200c0078002c18030300c000740c06100e00034003602d4860300c44000b60800c0648110303400e03124030314007824560746028019203c481031003004409003c036010600425858182c80d860031100070300d0001c9111403079400d00c801640809044051050b04110000d50800e400040321811550245c6582c05140820f042403810740c000c1e0b400041242d401c1c4480005c0200d0b142d0083e5019602402c400188503035039071011513680240b81710003445440810010070103070f405040a142e000d402101540e00d0420a90368040c188082242d510002c280e0100e1005d000c5e65000e640d191107c3c0c6c105031304a5640781000605401000d8007134000e4426a2180d21000c204201808030038010b1842603002c0c410161a0b0300c040011300041d004540c099407406c084d0382c1541d4800a0003c2040000d51102907164607030307038110380c05014811485030505408110702070015030704000c510701d48040103010f5500c0ba402d201c1000b1840402400051190340802e00500c00700d1340204000f9001890072b40302d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 16781625 1250 16780375 16780381
    0x30601020109050f0606011b0312020f07060507020d0e030307050a12020307120207061202090d12030204081605040e030c0303070806011e02150609090c0103020d020d02070f03020c03030f090405 85
    0x101c0c090480c056008066000c0c3c80c18000c100400054018000c0e40240ca07902010b00c1042c08410000105580140010741d85c014074101d2400a40d008192010800300c2d40c038580001a110f003426a0829103c507401070344101141d1040551050721142d00200440240d443d21880340c50b4240d41d00700092014140351400080054103e000300110b40388668003201a0061200103440030b0344400f030b544103600100e0011103003010f00210f1031003110600700005225091800080d264042c0c613007414003208c024140e0030040480c140c04100710007054a11400c00301d060041c144428402940c41d00c90301030f4074079482031200c511030250100a0300d9020225140c2155580d1b9002c004071a03084008100c010011440340751030b00e1042e030208000820001842050a4a44500b400e0001c41c540803a00c03a405904526200b410170b6210303400030300d03200340303603800250400300c40c1c0d5100d0049070f0103400101c0e800307800c1350001000c00d5011302c8a180038550480140d0b0414030406034500140c407410780098400e907079034400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 16782875 1250 16781625 16781627
    0xa14041407020706080f04031709011e0b03010b040c090b070602040f03060516020c030705010522060f0809070e0a0c03020d050903030702070b04030c0e0c0705010216030e0402030f0c030601 83
    0x10140c2800e404440c801081e060105010b92204007601034400020f19404c0006c1610041d10343c0036002e16070654072101100c60180900c0881600a0000007040d52505140a00c1c84070469a2014103024a04002400d00100e02010b0844080040c03040c0514109015140e015030807102c1082200d8021a01c581c1c0c0749411314014009224581100740c515007101404002e000b01e5a2080d0311854411290741f959400d421001daa80323000d00251581d041c0e00c003560902070755110700c020b00081841003110006a9904081424000a0903040003000a40543e640b0094941c04146141c1142d041e1000c1c00205090112400c00f25034001c110b0b43d0000d0f142c40702035990f14440e034121002c05400100401c01428220040e0f0344a50055542c000180310f459004518204040c0071182101d500c000b01c3c041003071601c0044462510300070242004084240310010120f803080c0010319070412003030902001d0288d07900e00500381400c13009010340114814010451f510030304456068000f240a550070342c0307940e60540 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 16784125 1250 16782875 16782881
    0x140a021e030c07030801090e0709020c0c04050903030f070912060c1101020706050405120909060d060e0f0d0201050c0a020a03032408011a0f010507030c0507030c03080a090f050a1404 80
    0x14004803200000820030400d440c1c607001900c815882a6a18090383c0d90b1000070009846540940032020f0b0450207003000304665603801418100207600558000700d180c80700050849004445240c0c41d17400002c1044400d0800070341d426801415400c000d000a410070350704100e1000c2d01c0710002c15503640d034200c814140e801400440c0c0d25030307030107402075581e01d10501d0400050401541d04550920650b2000400080c4c0d900580c0c042c008045c01800183c0d4440301049404500d408040e9801070b80c41c02090400314083c4400034034480d600d8002c04181c03e264400030f0840348024888810300c42c084c030542d0344195021420301c00c615010b250100303540c4a23645000e0395007804000c041e980100310300c0c4c0006001e0b030f0642003e2903039042d42450075000c400b5041800032040c4c0700c87c19240028800c2041c440013074025940004038034001d500300c5428544030ba44000c40d010450b00b05559600f0082144400c8580c018030301c40160030103110000b0018600b4010a150115070b014000c041c211041c043c80b41921664 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 16785375 1250 16784125 16784167
    0x1703040317070e01020705040606020307060506040b03070308180301060f091d1f06051903170403050a060902030f210c030d020403060b0a0902030c03040609031e09060210140a02 78
    0x1080c0405402c2210000e00385080c1c1c00010382c098060404c1c00204c61619101d00001c42e036954004d50302d851519540d840060a0081213154019903a0740c0d10b45843e101040104041c600c10543d42c2e0f0b68035040203811001081c005072403442a030410380280603000d2519803c2003118140340b000705889010f09000c07070180c500240f007c541481030f0005200000010345200010014154003002855101c10500500b01c000a8260080c0481c1a1081002501e0050020f400ca0361a840003410580c90740e680d0741c02c09403e000140c454a0711041040151f06e01030203a044100c0c08035004281e40d03c1d030788040000c00c0001c94600d80c4d6220000c00d03400a401400c4c0308540617040329030740031556545c40346004802040000112409040102c03c04a207581d65442180c2c09651242201070850b07917295035080c003600c1644001c608009040b50075000c103c0d14510301c002040c47c551521300029082120081c5801c00d40b42d024000d40e41400d080030580c000d50703010940c100a00e0354000d65110412599584d92481030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 16786625 1250 16785375 16785407
    0x5060f060306031c020c01030606021c0f1701090b10020604051b030109080d050a0b0607050a06110906030f0108060c090904020f030f0a0303020a02010b04021206040504060605030a0605061c17030403 87
    0x484c0d068000c0984c04250301203810001d0320100201c80e140c15040380c0d5001405412981d164590300300319005801403801c0d02c261210362034110b09180320903d440d40c082e1800c0c2d0120726819102d49075582c89240045207429440c406200070300c51440d10b901d40560f600d03400c0003114902c60346584c0705031013a1000c1d0000c140e100c0e0008140d56551040b082c00d4802041c04807078620700e151800180c070441c0c0c9001400c07250382540240040c50050880e0315464000c2510b1240042009010032095800c2d88820b00598810310465000d1201c56240070306650608070002d06812000300d04003c10522580c40c00c4843d90850740555081d600f0407503d601092614002025100310b9114201070b10003050340c15001002442801d500034040c82d4807032000e003c10380c01001c81e4846a180090002840380c00c0951010740e019000b02d00100c2c0c0796030750700b02003400c08000d548103031980d0761100c00b041a1410510a2040e840c50342d4418a459006030351203114680c2d2a10880403002c400002c0450249882598000100c0c411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 16787875 1250 16786625 16786663
    0x40203012d05070e060712020102090a06030b0a060f050f090a0503010e0723011e02011e0204050906090c0901050c03091915021204090b060c060703021c05060f06030603 74
    0x81c901031409402990558071505424100065811442240d0200c5408409010103013441265038400320010014003613079007199400e00030304515980740c80010340240340c140ca002910303c1e401c4040c0024041250828000c0c030a2402040760034030307801002c81e90401c252040750340e1580c0710000000c4461880d85e10242d407540c200030044032000408210003003252a148a00f14981405101c0441040b08011045010a0440d071300205000241d41071420014030a100002d104d030320011420300b02204580f83d198469502140500550810010b8242c2040c0d04072407800042c58070210807882885014100e6040140c0401d0411280d4420030075502d40d420001c10b903440d0002c0c0c0c040100407180781e41c401e8141e51000c8c61003c69410b400401d01d40540c503d90603595240c54148644400501b0100c519a84c02c400204400c003079400c1c5c244400c1c0d005245a60700503079203010454004c00100342c80c501803c00c3c20b15150611801b41d0341d8025000c000c04094400c246c0300e0b80c500300000e00b0200b000c2d04124030700c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 16789125 1250 16787875 16787921
    0x615030c06090a080d080907060f080c07030201090c0f0906050a150e150c0a0204050a090b0106030e0c04020f0d050702030c03040315090203030a0206040501050a060509060603090a0c0b04091b1704020301 89
    0xa001b070500b600c1000c0480031220b40d1540d950701120f14001d4001e00d04046a10440420030700d00400d00203041c414068000410004003541d5809582180c2d07509c01400800543c3e0b05000302d00b40e034004d620041404807003141c40c1c00c0c20a955484102481d408a905008845034003842c00d8448008034980d2500c081d40c000d845440c50710381c890300c40040c000b00b2441146088001844600584141402c458012011a4050b82001c03819002800305110078483c42c130134901d01409594a900082006001505445885006504001c0261400501010103542084c4414118940008141d0301101d412040c158848503071100000010140032101a415000005115020300c2d0002501130141d44698000c0201c1c0e82c1c0c81301650116603c07402690b6100c080d0b07601143d224504240132715007114a080030340c2c0d42c0b01203640d00c1c08c074071086a0b4041c1488507000f003810040c012042c402d0031107620301408148510402003200504ad1282c0a0019000410010124082d502c00754040120b20030b5804604007958 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 16790375 1250 16789125 16789127
    0x905030a0804080c06070807020f130c031410030302030a050a050d0606020f07060801080d050306030c030303070c0c0501080717040302070b0a0203040e2a030403031407050c0615030c06090a080d 85
    0x5030103030180801071300c034141c42d04503181400f038103e0b00125000580c1904004081c0e00304407150342008039080d070010390f41184107030414040c4900c51100880340c500082d5001a103400c00c4407444c00070700400580d80c04070790410100b5008000c460310a041c5250580d540c01020000342c400e4002c64400400d84c6180041c042102d07500012013036000c0c42c09508a440c4150b1384d007822101c1d140240540c18064010043e21807500b4015009103801c201c0c000c0540300903001c81d202183c0b031a01700b00c1d480000507140080c42c01c10b00030820902005001c0038030b072200c41454040f402038808020400c81007109c40008001030b09051080c440240a08190b01440340d0324603c2d180000d50303a8000e40600001110504003040000d40504291000c810120011a0340c100f4844c0c10806240c0000300150181500e0781c21207140b044940080d903220352210349034035403140b0b00440c0c100d280c490000e20345080740490030300b1440260303000100c400c20250102e6a06a4408036070000c103c0904036540185154440c03113580441e12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 16791625 1250 16790375 16790377
    0x206030c03070215010b070b100605040605090a050d0507030c080a03050304030c021309030305070906030207050c010302030408040e090106090e0c030604080a020f10050601020c0901060503040b0c040513090b01060207080303160905030a08 104
    0x61401103040d107007180c54118127848405035920403400401c000708800c00101b03014401611200c940103008524456803000813030f40000d6280822225034200c042d003403041106104c0c040010300307100001002802d810342d030041c0c90b0780320152003c2c05102d030b18113081007151ba8201c46000c585168006c28040d510003441d0103400b80005a502002086203001c000c20365174464400d489421f0b403c0f05c010221503000400650081d400580240c030004070810000c1840d004905138a4024102c000c0000f804500c1c00e18103200300e0b0728000000881e6088406207051580e800604540c01641081c1c42076903800b13011105a00c1d040520791442d40a00030210220003242850b03000521462f401e8003501d1080c094031080000c144824020000445c0090000c17131b010130020a04d85900414100036a45007a460780c0014141c481c641d64101c000680b82d000c03035001c210604550a005044600041c411075080c00d00343c1d5241d010040144015850f80800002a0340c8184220740c010140034043c1c030706001640c1005081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 16792875 1250 16791625 16791637
    0x307030c0212030f0d021605030c0604030210050103050c211b030c060a02120703030212010305060a060e0903070f020406030605010803030901051b040501030c0309060f0207020f0301090206030c03070215010b 91
    0x420b2400d44100e106003280402111441c00401001500d42511510100003d42205182d2085401c03512a607000051040004004011845004008618141c40c0082c5407402001e1158105030070300c130040001420004240c0480241111880580040480e40510001310844031610b00c0c4074401260217a06c82e1900c0051528109805888805000509011251243d602c3e01d000607406000d50303201d0a480e1074090024184640390140c5000e006100819100c102a002511603400a000b403000000c05882030b000100279041c1d080302c2078135000074560b44038024800701501414586d2540011075031594024406594410401c00495841d40c4005949400440741d00d1075075840d0001040e21481715921a800728250f07040c81c00e160504090044015080c40e40703036082812f403901201e00005825000784e1801020301800161640504e004000028024016443c000c0e49410040000742c1c17500e004a96001400e1080d40f0341d00d40798000704a180c6032401c28410003600f0844000301d610380d250401000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 16794125 1250 16792875 16792879
    0x90206131406030c0301050d030203040504091202010c0906020c010311040306090305040501021626100516090f03050a021c0f0809090f10031511040b0405090112030c11040605030307030c02 83
    0x1030701e150030078001244425035201070141d105200411941c40c2c2100d0000403540300b4411380e82413907030740e2020500b80e50321860304036550149040c4148001794240b050b6401c28081e45010904070b07141030390203500e0fa510340c14094100b640311151052440c00e681c0032a0000c580c071210410107400113040090017500580243c50040c003c128144c00c0116120f00c08a080e128100104048042008140f4050000090305920207000e1036840810768041031003168425240f000040305101d40000005044c121706400c980c040f08000305052020a40c001078000038942c0c141c804c000101d150301500d00e01104c1c600d40007004120f900b5004810481e090020b404c400f882680c0f9980e840e00d403412803e01a034011501d100c1800800401040414030211401e80011800000040d05e42031300c074003843c01d9a104d9004000c406500060400007810300c2c040340d43c01400b403c0d080309062020395500030300c2880c55242c003511500e228514030013180e039564040070007018024126a0740340303450724025041e8981083c0c00d074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 16795375 1250 16794125 16794149
    0x1020408150405070603051510020a030e010207060206010e0403030207020a06090f090203090309010e1f09030b0702010b130b010224040606080d020a0f050f0a03090f050307140103020c0109020613 86
    0x1c803072500d211400901a5900c040503111140c1881ca046005000c014090b0301c6068050740f10707030001e40781c1200c0320702108c1d5250f000d4281c80c06a81006006411a50300381c3c0d0456020300c80400580f5070103e00c07641034840c0c11800c000c2c240c40f217003803c4010340524000a54000d080100005110350031420b200b0072a056095002d982642d40c0101c6812400211001c42c4240c2040240707052035841600240301840008000307051160405040c41080c80020f00c1c10f00c0482c0044000f070040c401044080740c0d2041c501c0c4024403020140401040e121807290720340c40149610349208180b968001d214010510300c00048003000360341151100c00007642c0548080c0c40c1c051418a010071b480314089000036403250150000c054003801543d83d8003c04e5003d050540b000d000741c603024440f0a2062011440c124042d6666030007240c20100c0c4d102d034011032a4070103803107640107800070032040071410003032980040c0c00d0a0041e115405a0007060241044a000a41c03100c000613103c040695a480d00c1020303149461900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 16796625 1250 16795375 16795393
    0xb0c0a020f07050603072d020d02010b03030703020a0b0a020c010203070c02040f0608061f05030102040b03040b0915060402031905270102030606030115050d0213150203090d03030f090f0501020408 86
    0x2540341d030720038080c084d00180b04100041711175000c1c2100c200300010300d07200d4803124901c03e4482c110055501605100503001a081d0f0081590709008258809004901451915145030382c06965245500e00080006005400248051803203605907a12007400034003d5682e89443e090050826821010880c840c42c81c014640c3c542c1c0ca081d00c07601e010f4400c03100c01000c064691a08403480741050403400f142c120400c0c003010602c1d803400e0000d0700080074070003103542c0c407030411b454200700c8484003d00b040d5440e407114501d810074541c4400340a8010009641c0141d0765291825040d40c0c3c0d20314448002d00b180c0c200414403501556131801114012891400d00820010400d01c040c280d1105860841d0b01c0071041c0018001142c0c040402c10b66076215080151500302c80312000002ea0304940980d0710420182e680400160f04011814005066180301862800680a0000e88001d801403000b80415689415100b505d00040d03101c01d031040c1c2c0000c075082e0400c41614000f4080e6005020304d909901440c411 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 16797875 1250 16796625 16796653
    0x30f03070302240403080105061308100203060406270213050405160201050a0b06041a070f0305030105040501050a032004110f18030105040302070e0403020c06030112020301060b0306010203071e0b0c0a02 89
    0xc0c403400b07540e2540d1b926006034600b0040100e55042100000c034400c2e2135000000342c0000800050031402c40a01d40540c403854141c0030041121107962100103080c0130042004e01d003155240f04002c40c42e242d007a005846102e0250721007050f40070b940080d90064034240610011085050808400041d103500038882c6642e10129030703082d6100307070702c4d01d80c0c10502c244000d1010f44c00b8064031100d40c4e00d201007a64100800b944030381408400b403400690100301d00100500141c2024040c3d180034050075148121400c3c82e6503a03164010b61503e140c2030007a9088104a180d5564a4000c40e401042c070305142038440922822501242d88041c0c949024498249801351580c00e06001c1c00d032080342c158014110051030300d055030900c0d035401002101103000c0c7c00d812419aa84e503c01541c0a802690301d01c42c2d40302058410b240c21503145030840d264280041c000c024403030b80c4c00800ca41c043c40e03101a900003107400c04c1c081c0f044468071145004000300101c0080001115501c03002d04450040c40e400c6503141d0048142c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 16799125 1250 16797875 16797943
    0x21204060e011518200c01060b030c030606090a0f080c0108010e160807030b10030902030c010815060a0e0312032203020319020309040c0207080d0503100e06030f03070302 75
    0x540343e8103424000750400c4800c0b4111069008101003104c0440c03c40c6010000402d40c201c840400483e228010031490810f060911407031014140c1444001d280d0f04004854120a00000f0001031050600207a00340003074480b050884018403400001030900c6807109041f94817900610031150019814900002d1001081c002440c050b10007000110a5494602c40c101c41102006006405054071404030b100162100c00d0347c034a614020703a03000500444507204041c00d010024054038100468603092021500c031051405020880403600c49503540003081054400d100361800c0c02d030b4503000d0442c02c01c01e40c050080086100702003035021040e401c45000c000804001a590001d00141c2c0305110001002c14504080c2176080080e004403814001d4400c0042c0c1528125070709000141c02404041104000c100b000c44480a02ca040081c03d51070b0107042071104c11350034451424a00c11000118015450030f11080d01290b080d00181e0390b4650386420080d41d12020555034440b05241d41c900760052014800d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 16800375 1250 16799125 16799141
    0x3013003120b06070c0302040b0612011814070207060f0c0c030f110102030c0c0907030608100e0111040614030411091302090705070b060405060604090207050106050f150d0f0f021204060e01 83
    0x40003417100d6040d5003d00c00241000040190460410000c50b451400998800341c02000140a02d500c0c4081b000d942405858244054038a0003803000140700d04e0341c0e00895400c050324203628000031007010a41d821038141d04900c1e0058829820340001005000103c81c24002c00c6010701001003111764000300490b0707648901801036809401008040c9100c0c03800744040c94104410f8680403400d075440364011420f00301c990000d04030030340d0381d15140c1c103c2d04020b01914841c500043c031000c2c181490804007a092401816502d149410000001030811240d040400c6800308040c0940005103401030480d565980381c2d030f1090384a08001d030700090340940305500f1241680e40c03005444820b45c44000912010701005003030250710040900c00400d203c4054400b03001043d002b0400440e13500d1a02061090080002c085a0b0003101503a5648070402c1d0b044e400c94026110290700050588090401000205140042d80200721b0000603002540300012141038050342c0141010000c542800e207125080328214 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 16801625 1250 16800375 16800383
    0x100e0108060f130206030c071b0506040504020304050f03040303020a03110a030504030803070915050a1e08010b030a0605040c08011401030b0a060509031c020105040b090a03020303013003120b0607 86
    0xc0300103034420308400c040a07007008402d81c02e100101c40584c00604140c0045907d41c200385004030f114070a00003c1c0034039110f4030340e010221290850400000c10500c0c441d40c0207150013640c001003c1000c0203020482d05105603e038401781e94a80761685402900c5846140c4141c0014084030219045010b004c62807110003580341c3c9075549400e18550311001c040e08001c01d00404c0c03000d405030000c0e6242a40c440d102031009035503104c1c3e65800304006c01402651064800da43c8582803101084209900001e4590550390301c050442c0e100e503203903a14034000e001d1a8120344e8220b800e2251800c103183c1c1081c0c216040c0c43d0390480c40c480d9507048000440c1220100d0010940c803000b01441008014060340003424071001c00f03001c0d0b07480407600c115005001190300c0d0b850070040c0c0d03440c8104428040420086504002d6003800303403014540c41c3d00d000303549001c180664aa889643c5502009000b4030b01c220181c1c0300012038405580484605005d00304004021301c5040c162300b003804480c1c01b0f1402e807040300d4400d0781c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 16802875 1250 16801625 16801633
    0x2909030304020f03010f0c09181a0111070b0703030212060102010e0c1203070804080f010b150406180509070206070305060d0b0a05100810021e07020f0d0201030f060806100e0108 78
    0x41c2d8003040311403d0540015030b00340d540c40440741040d4606006e100c0c00303000c0319103920051500c0c211500c110008040320b03803501c0603e00190408d070f0110104992982101c05d103450442e80b1486c0c81081e0034400158402c2c0c50300da000050f20b404154254020740f05080200c54406100d503540b4005a0170307102c020300c06912a8020b000c1141c16172400c1000320701681038203004c582c00c2c0022035643d005542d00c19042910203034000000070720701d10824040c0000c4121f00340e410406011101d54155040d01580c0190020320400c141a0061552214031183c01054003c141c0e2000382003c582c081c1d03c0f05410340d00c03840005d06002c0010910f08010301110100390380410701040c01d030f803403148100080401034000700c03c0103540a40040e0440302006007032110031000e800140c0d00c01c54030101c010504080c0c2d40400c145d00d028003045005d41e9a2590740d0010b03100a440c00641c807001840100d009107840018036104038075107000401c1200300010514440c0ca40705210031051500c800304940c89000074411540c56908c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 16804125 1250 16802875 16802881
    0x150405150406020f0c0304080c010e0105040e040201031b030e0601151d0d38010b0304110d080309011a030102040308030711010b0306070e1f0806011103041229090303 73
    0x3049602580d0150103280700605020b072801d80601103030700c4981d0b0030856501c0800d050002e040c01380110640d41c0002d0921094180500c000a0400c0c091407180d01035140c032500009003564000e030042e4140e01599011442d08010070f0002600900c3d401500e018503100d0310002089940c044a0300c0c15080826854000103046440d995105081c92070000c1c0b60410f0788900070317800148294020404011440020340d8202e2a548441d080010280c2111300300701000e9001040322009c1481140e4009801c40002d44c0402c96040204000da40d01003401440713110000700300301300c0e43c0041d800402036060181ca0001c07150300d0b0a04041c02d030b000c0c1d4000030745880420800f0a20003400f60130844500c490800000c95500540d6000030300302803088800c02c000c11001180c10455140145840c540d482541225841d06800e05900810301c040081405051000f440140301401000704140c8004106021001280f601c003841e00e00c115591310800c6c91690149864412050310038240341074420324110f8020350a5036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 16805375 1250 16804125 16804153
    0x10501120e070806010e0106080f01050d08181e030f0604020a050f01020f07060305010501030c11100203061908010608060609010614070206041701090507060f02071412060a05040302150405 83
    0x14180303000280b84208100095a08018003e1600a2013402d10800b40f13507142c1003020b44900310081411101e1340d600e80c0140000e50700e031000e0101498000f02c00d1034441c4007030945003020ba000715100a60007400f00c4c403100c004028910b026100c004d015800d840401071001c41d002d59600007600e0083d400000005c0131b100d10b00703002c021442c0e407010500c122111010990f54190505555400030300010342c440c0014011541c15002c2d44e22247c00e1854401d80e2000003558940e2902d2811001100ea40e4002021a1982c1d03610701e1411002c50080340d01c50155551286628001c00013446034030700c070f4058800011000d1820a507482e0480e2840e03286d00940e4501e028600705279600c40304049070b100c2e20521000c103c00c00d4098401080001c00c01c00011601050305120385010900c0e0b0004007004107010401c40e0a80d03010450108591070f0340540c2000403030004c009001c0041c041000e10a5211710750070854002e000e03400444c000d6000341c084c0c8003400100c0c861740a00b2a822180a080c0b81d1000d042c0180c5c0c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 16806625 1250 16805375 16805381
    0xc0d0f1407020402131809020f0109060c140f070b070b0601050304020307030b06040933020c0c060d06080a0f060605090105060f130e090d030f1512050c0904210801050112 75
    0x5001c0d01c01c0200c42c0c1c9031820301b8004051081c695036480d40e9209510214106500d90503030041003400e05060f450324100e8000e140c228501c1004114140b1040c00c1504964100181d40d000e400c2c1c44150303280c0a03203c100b00d210f550030803801600c0540302603020442135401941260301640c0c01078040d0180714110f4a0300d05d15604050031044d00190b50f00e11a10100d140e0741c40c0f40c51a170525501044005860240303e80501c114000f1541030035104002d62a4107020025075900508400e840b00c41c0c481c0d240401c130000610322948100b40318044c0240b482e0401590500001c88140700f644104083c0c0c0c6c0382c03028015078450074040d9980140e003c21000d002083c44201800822514410000c041500d503060480700a0313050b50026061750082c40503002c2c43c0d8241c020541c010341d00c0300080000c200103890030801c1c11428440d4000301c03541040d0400034460103005200b40342390302500314001800d00745065142081e90400f0741a0316480344144515075407141e91181c0c100d420596400c00d0120302070f0301110007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 16807875 1250 16806625 16806637
    0x1090b0c03130b0309060a0b0a0519080609010204080d050a0c020906040b0a08030405100c0b01030201111204080c0f0108040f02060d0e0a05010203040204140c04120303020409020c0d0f1407020402 86
    0x110710082c081000c0d110b40c0090a540605200c4a0300b540300d05002c0412880c1880103000c603420b16081c00c04816103511142c03072800403210100d6041424a070340700c52400040707029400c00d0340c950082d042040058803054000300101d801100468000c2e141c05c01085400e8050b00d0072030000614840b0710700c13003d40790100c1003a412071002480000d08809034000100892900d82c4060307400d400105040141d4a8000c43e880140056428910717010900ca5070340940441c01408001d06028092a8100041c0c00030441004190300d1084181d0ba00c0340c85d00110307580d6400780421203200e03808a500c24000c0d54070800100380213950040007210641c03101e908100d6290004004440340560310010605121400c202c121046030040000681c3c906190043c4001e403044c2d039000c00c0783c2c0e103140414001146001d000312401c0b80c044540d170f440034860a2400303c001e0310956000807102800803038a501145800304140e80c0320302176921a18080e20640f603050b1440030185107000980da4041c0b00c42d1015051a070000c000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 16809125 1250 16807875 16807897
    0xc0d03022d0102120106020606010309050703080d14180601050607050d110f0102120109060e0708040f020301021303030806130e0304090b0f18041506181a06030115140901090b 77
    0x1070908000392406089801803a407042041c400100100081501440542c1d0005400c0c80d05114042683d22007594602680c071006250420000705101e400701031380c0c08800704002d40136070145c50342042000031195624a80814401d406000000151403518a044035050b951240140c80000742920341500e40d11200c041c050902c0c01941207890814100f88001d225400c500d02800e41994104640d00b0100d89407508420084c94100e0188813806421101459000d6403003002d00e44038124500c0424064000c0c54028481026207523404410103400c0264075120307180960304e41ca03169040f4203100c0251124000d072040950000c00040c44603a86c02d400440b01068040c082034070304c01a000124001042103102c40c0030001442c0140000c000c982011340701a241d983e02c043c06102d00b041c4c100760300b010312032404907207060b41c40202556900c5544650101c1510050a20b6101d40e9640542491840b00003150700004032a03400041440071001c0a451303080350182e542000850514861000552100b13003914 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 16810375 1250 16809125 16809193
    0x13120c03080307050c010b040209180a0207060603060c080a0603020a06050901030e060906070908060105010203030a0b0f1e010207050301060803031602070806100504050105010f080a02090d08030405070303020c0d0302 95
    0x100c040707081e4100840c042c0016545007036580d0f044500300c50841d902e00d844c0c1803041d80100032000542e9507201107600d80c00c5501c0c420b00840e4035000c074590000d108030340009103118100300002044c8082ca0b0710404002016840708030717480e503503a05524219540303808007d500c903a0381c10341400340c00e200e2000f4251258060500140c038121455004d4a048000c5441e1842d039400282049071442d40000081d00402601c23004ac01c440d410440041c0d22804000c04441590b076890354680d0007a07449281c0080e1041000d4081000b0000c10340200c8101450b01650b24090700c43c0000005d050306051182c00110b40350400a141180c41e0342d04003101c1c50812080719001c52090a0f400300c2d690000b409800c0c014440c45602018030b070b2404040c0001c3e1541680440d0600c040050500c881c03941001e40103500140f016070060766082d902c000a85546404140070307240d140048200801c04c1700028250054032302030340840d00309203510750801c0740c40f03524101e0040050b00a09500c0311401d000c0409030704a98560340c005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 16811625 1250 16810375 16810379
    0x50f0106081f03060b03070b0f090402090d061503020918060a0f0e060f040b01150804020d03020f1e010f06080d110a08030703020a09140105070b040804050603010e0109060b13120c 79
    0x110110140c1a00240d8901c0e43d1078407010840c3c0740c07c21094005240c4102110b050260203803482c4014001c1d91544d600030b9400042000c0c5c10790b203403289410b0466200350200952050300c01584888100c50000302d00881d2120f0105100c0000c030b140a50900d21b442004006035510346a400d00609078210811102c0ca403035a07091810342c01c09008075442440903402d1040303a031a050420100f03004044c3d001c042072540c040e41c40da110907440401660b01c65016100c5c0c02101e0100e00e0300304d10742041080200414000c12210010070901c00422003100d44904000303202d0070420014900032603845105407046580420308007141e90f8050811310740718a90380d005650307004546440746202c6600c1182d070307900041e500081620031260030100305405490341007039240114400a001271310910446030060000e240c0c42c070002d4104140c84040710b0240030041d00907900c95035201a440c180d044d0038051030000505014004c20709401d28015104003450440041d002d19290925500310810340c004243e54016a842c0c3c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 16812875 1250 16811625 16811671
    0x20f04030816120503101401140313020103060b1303021e060304030c030215041203020d0209040204030501091a06061b0a051605010e0111030a0305060102030403060903050d0f050f010608 82
    0x5001464941ca501810b80000c500e8041c840040221070b42c802c0c02028004e00035240300c103925060580d106403001d007445200300701c010b803015800012003494440c0c0000c00c001140080b02e003060b070710318400c0e01c003030014039110954074000d8001c5c0c43d0b448145025508080001d403818868003094204607484103881c0d4860030020a02960084800350003040c0c40d442078004040d8100b00303000d6151480c01007042542010b0b41e441c0e01540198460300300b050740208841c18003500716412600300060007401190307156500c0c40d165020300b50101090300ca820361420b415042c2e400302c071220780c031030100208070600c3c0050754044098468150480800704e403040d404a6000540100513468184003191560143c00c0d1904000410724405442c070300741045400c0d0041d49192500005841e030030502401e0124250391201c0040303185014580c0302604007828815403601741500f00c0000d0140c0f00102d0414090031150f40400c900790399060341c00144098801004101642c46140e00d5500100b401c000c07d5079405003512 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 16814125 1250 16812875 16812877
    0x50601090603021c0308010504020c010e07031208010803030f07050703030b1305010302040c032705010b060d09051b0d030309020a12111305060d060e0304030204020f0903060105010302090a0603020f040308 90
    0x1000801c0c0e0300d40e0300707100f50b107803403500e1114080200702c0d01094404c1070355000b000311006104860107981c010606000030f040030740050440306408000c403490903580f4100424860864000c4002040c1d5071400440c0c4407001104503841101c030031464071040d4891002c112140c0c2d0103c541078007090b0703503607040c18240d9a452905c1c0c1110302102c00c2c040380950460041208035072885050340d0505280920092943c05c618400740b28140082d0480d140050550421a002d05240191a40d2010f00041d40c0311400307280740d000003c16401742d022500600358812001c1c0e044209921401c1c2d211a1003102704d40000d100f40c00890a03584040c0642c208a83d43d011041038801f126a011a1100100850340d40541003c202d20940d0030300e2840144040e00340140807502c5401241000b406040c0ca40401001500c0d0030401c80300250740c0a04210740e2200314401c03082a682103020fa00f4400d000e0f0b6000004c0542c4a07000ba1290340b0b000904003c9581e140c290142c009502030181e80032824000d02000021481881c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 16815375 1250 16814125 16814129
    0x1060305060c13090e030901030b0102030c0a060906181209050f090f100e07020307021318081b240f0103030206070e0d06020a0201020909010609030503040b07060902130b03070501020105010b09090c07050601 91
    0x4402107441f02040030024098822880c1800d04550061003494180000090340300700e0309811080000d0006002d0034046c2c041c20902240a0b011301ea038030b4005003003140340c5500e04c04818140d0394001100e0344a0b41000010750700328040c4d542c4503041101044550002d2045c154121064034413640005a44442421808008803030900160b00701180410a40c10881c0c028000090202c0b4104604c500600ca5a03c0c0d00c042c0e100054030317403207001c604020030340f502c3d400d01401030b01800211345000100161000b101c03040083c098045408000c0880e036616283c0d1903443c16030750f06030040c1c24196500c480840c0c840030403981d001c1d4008000e06144001c10b08500c018130021a19a00269480718220f003404104101030b40100c04006010200304080380002c01620152541400040d039504154108503015290406001e9481140c07586400d212030003640c401030310800241c007a5485c0c00e64407401a1b0072210240315003a1303448400c1013490450300d003039007900c0e0b07101d042044041e04181c50b940302c0d5450403d0903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 16816625 1250 16815375 16815401
    0xa0c0b040f08010615050a09081603110108040f060c0e09040c0602070e04030c02040207080904050a09020102010506010c0308060f0612180c0a030f0b040809060d14070201060305060c1309 82
    0x1401d11240141c20104000750070000e000303221091405d110f0482601440e1070000403c007000c80c640654912031104400109080011114402010400944444003512088a1013400004612003e50042040510984e000102d440140540e17880d40c1014181b02c40819080102d0301c10045626603900c2611390003540221095441c039400c001c03010f46481500c3d0003910b0343d01d880d40d0030070001a5110510102c4554140e0300580c44038140d01e4801018064003400d6036100381040104128900190322510019000b41d00034845920f40702c0064030045810b0801800007400100050b8080c00c00401c0100182030152031249003c0d621320800b200342c1c4040c2c421451207242c5034100c440400c01004004040041220f841c0b542d00e281d07580e165603240300c00d980204050b05041c001014081c01d20203844900e50040c000c16543c0004000c0a8000c20080700090903006404001ca01c241d841482501c0581c0c0c0c2c4003004107036a03110f0540036105904201000c1410085910010516400c0f80c05442200d03119 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 16817875 1250 16816625 16816627
    0xb0711011506080405010b010e0901090c090905240103021309050907030b0f010305061e040b060111070f030201031103060f0d050102090402040609060f02011406040b0307030b0c070b0903040305030a03020901020a0c0b 95
    0x2034035017a400c1d80c2e100450300f410005854202c501642d01c0b00400c0341168450100001d81c8034400006132026005036001c1d05101e40361500300100250310054440040346980000e040600b1190700543c2207000e0800b154200300704900060122030243c6c0c0c4000c0d04495440c04940d1207590342d5071040314041044581c05070002c406001002085000c009040c0c009114032100d140c46c0c480c0340c0002c110b82c64000d01c09450418500080784807640144200c0c110000342c0c4059a41071a215000e03103041103400c1c441240002d1410000d04034850480c402d80b40101e074000c00d180600e100703c0d401c0240c1d00f0303100356099503655400c01c050040c5540754030051009140c1034440c00c100c0d51810070b0107400c43d20800d004400f50f9040251b6a21710b09080d12220b980990111000141440800301003440c106860f0001400020344074140220340d01254054403020b031040c50000309a58640d410280c4074080d0740b10040c001c0d4011711a02d40d003903000c0d030040c08845006104449141c080b0341c582c810100041e900007004560 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 16819125 1250 16817875 16817881
    0x3030c010204140a06050a0503130f0b070503070e1210020c030409060905070f03090506041e0f080310050109030803040b0402010c02030d11010506060703090b0c030c06090c1009030b071101150608 86
    0x1070000c40c0c00300506081c10000c7c204012098050024800100440c00045900003144204035403016074905958100194051900d07017080081c00710307407060700e0020100e1500b040c0268070b441c0607200b441214004c900900301401c5c07400c0344074003e50401042038030280000e00010800420300d00c241801030018242c085001c0c10714900103800d10115250b0380080509011680011aa0003d030940d040b950107481004071510381c0f08080039110b1181d80042c10307045610310303003014401d0404c050b40c0214900b0346c81c0380c0c0d00c0365114015a1b09001a100c000c10200007031000901141e5450b212540c491700604102c0c3d00584a580002c0c14040591440004a1142d000580c00c20109100300380d4840f10507260309182c0301e250748001d80301c2c401c54481c5440400d000600030000c2d070300c24000c2d104a000f10303000321011800c106003902e88a084003034105014400354025018000d104c0c00c004405c49400c56501d9030151240007045440091240342500c3d99900c94044450f90b400004c1c01800074040341c1d548400e141 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 16820375 1250 16819125 16819129
    0x3140309010f0c0302030408070209040c081603020301060b090a09050903040b0c010507030f02090a090906092909010c0e0d03090b04080705090108061b0d0b03071202040e0106060e01030b03030c01020414 89
    0x5a00f40010800c01d44184100400903604a0032200c00c150111416016035840e89401003401b60740d600142018004c40d8080701c80520b100b00304400f5a0301c220300030300034141c0301e0b02c00c0d4245002d02c00c42a0fa1090140408114510803588080d80091224054a207850f4440b07a15020310340c00180c1d00b6101d0f07913603417040101c41e076454418129031108421055241c071012000041d800c000a0007a80c02c0c2c25542c0d00b0402c20801c0691050b103030130354030100090700e0140c0e41e40404100103c010300b04030000e1840001400900e010b00c2a2201d40d52245c4a6100c1d16428ad428000f40c1080c140d4101c05000c2010310108450203101c0c0a00010801c420040460b642404280004c0100607031010840d5072040d010700c400322200600041110a02000607921440c0916440c03000e40a040001d03074250107201c8000c141c2010075039041c8a8107000b510184046455005402d089403024440c503000506c1b151001c4d1055882600a0100154000d0890341041e04000000d400ca91180c2d105032280508880558098 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 16821625 1250 16820375 16820381
    0x30601030308190606021b13050406020c0d03090503040905061915020706030207110913061a010305071d1002010f0204090906060e090706050f0c01021603090801060b070f03140309010f 81
    0x3000c00500c03282d80f502e100651f9a200440c40703100200c0b07090700744a8030758844500310040d0b003055800600890030181000030095001e6400c1c447d8038002c0c0003203200301600070f0049503141d651101c0207510342482c140d0607400a007000f400d041d511403194403203402d44000340503586c00074256802c0e041200c00020030020b85098030076400340d814140184403035008140c10300b26a0110243c155031034641c503503458400410000341800014100d41c40e001c5803440003500b05442100340c500a03201000f040d210818183c40400429000d8030a0b8850200c50680c142072003c601c200c030f011a400003058440314038040b0340603604542c001c103540380c1c0d81e400c0010510040380500c100401d05100c00c1010b60410251007a2508101e01881c005d101000402c0708912094100f02c848080f0f03800021074961440d115008407280e10440305600040381140081500070040c8158812680042002440c0c60503a035104146076045040503018000c51006841c2c2491085004500c1140d01600004907139402140080072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 16822875 1250 16821625 16821661
    0x1a15100e1e0603041b150201050618040b0601030903051306030506090c130b16080403030c0b1006050405011b050106061e1701030f0c030503040603060f17060414010605030601030308 80
    0xc29440300c1030700340d80c2d1074000407640c102d0f40110111020886541040907602e00e690f11003681c0039082c6c400042c1d01903040d80214003801040720000c80d0b07140850000b4503100400d48020f45028100c2d0042500b540c026800881503911906102c0e0500306030110203101c0081942c0203401007529803007045043d182103901c041d40100e8000200d1309101c01080e8800640425014203a00e10b40001500b042c056039600044800c580d0041c01c0302e54807038980c40d0081c0309100c81641214440181c00204083c030380c8000800f0203480a03680c1d8181040d1605004450b00d00121114525100d8242e10306400f00d202800f449028142c15100c1d052018400c004902d010740381c6a645404104804660030311000d941c507511811241c00c8089440c9031180750074401d941e8400c17580010114400040c00003809505900030302e040390350040f601e81000703541d0310007080a01149800000f180e04190001400200820340c1907001403000000010410380350750100345000800e8000740d01092a0408000003000c5495042d08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 16824125 1250 16822875 16822909
    0x604090608060f0c070b04050703020306041101020f0a050309010f0309020d050a050f06070f0e120709060503120f03010303180801050c070b1f0e090c060414010f05071a15100e 77
    0x110304d1503c00c081071868018048010003a41c00c04c0045401d120081221201a640050a40e01c840c02d1034900417561100001d14180513000300308020380c9a080204c0c2941c0840d40000145103031100f100011291603c0c039400c4003003416950480c242c00b580f2030140c040d0345d251050005146a9400c1e0a0443c84d1401035141500c0d558450000c0000803603100300441c4c21507900c2d05054028030383c904002140164881480447ca00c524480082c00320020380107802100d10540550f03038403840c140415009445038803142d9500c1107003040104000fa00c2965582440d10800f01940354058642049500b502d0701a10710400c90b00022507a542403055120000350002d4036029400c1d5440030b4840000c00003006480b800c0410321480c00082d0b0300b05000e0100c0b450403000288565541c9442d00c0811480c50324003100c5c0381c000754848100300c2e00c803070080d812100c0343d58110100c40c540c040c400030184240a0002d211100c0031103450848841910b2343c440e542c540c2c0c84c080d19220f285000c040305000c0290031048820b6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 16825375 1250 16824125 16824151
    0x10f1104031101030506060d020309210f03010e040204060503030403030503070e0d050a0f080d110c0106080f061803040909080c12030112030302090f0a08030a080702010203060109090c030605060409060806 90
    0x1007000c442c4032040314003030070081082c1d0b90386000194540100042d03030808034000010042c0020001c0345401c015408030001058070060041030400d1402a14038076405007100304010f2081d15a480343c602e07840380c8000c001044164a8101081c1190000d81c0201d010840201c1030007000c40c0c0001c0d4014a514081d100b55445400030b032030b125035924a0a0000d032041220007030f01d0301804403001c02c480c9041545038040c8040c610380c40003004180c1c01089000a95480c012000c502d249005c5070100d440c0078902c0c0248016192980701c1c1c030b04040c031034114110600c400c00000420380c0090060342c002d5801020b0351900c1d0600e4140c414148003400c825032054040400c0144284240011303100c034441c0d0903240c016221040d0a022600c80500350840d15800180e032400081c40180020040c580c0300304070f80d02c0020945503189c040c1d00340d001c2a11500e0215031042d50a028a5421341c3c0701c842c2c284214a40030807540d660f1800324070a035001f50041c040c110b031184000e000b040d904010303a94001c0020341c20b42c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 16826625 1250 16825375 16825379
    0x10b0d030c030302090d060617060603030a08040b09030706060f08300f040e040f02030d020d0203040504020d02130602010f15050a0521030a02010c09290306010c14010f1104 76
    0x81000a84141c01030501d0fa0200c1c8481860715024034556880f54046c0f0104081621021212441c0401e911314a00c03078402c506c00203034103080c00b10030344c0c400c42d00076100d801094a480e552845c054000404035a601e200503c00140030980c0c0b4046da00c01002081d0000016904100000e414000074207a0072000060403400c0407075540721640b20084d0b1041603201303580c480601e07494901c3c1c80d00c92944a4243c20000e070080c071081c46489542c034040140300b1011140390780700f200816038480d0f201c0501c42000d60070500c0108103a0516800034021451000c2006241061042d2070500841c0359400880c0140c4d566501d28503542250b100d8030b02400d801c1e12040d05124608000181a0030131400b80c81c4c00b27605007010b10f520407590603e10351038501010741038903100c40000300c4c000e0007084072149810014102c1c03540016407180261448904444c007894958074140d019048000711f07440a80121304101c0045850301c08201d05080011003074074004008500006007030001402c2d103025410f1190f43c082c0401003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 16827875 1250 16826625 16826627
    0x10306050f061f0e0103020912150f0106050306010309020a03060c0801081b0d08070204020702060406110607030b100e1c03020a0c0803090315041106031f06020f030a11070f17010b0d03 81
    0x3c82440903540b9085450103201e40c0100d01034042c401407660010b80d144514a00d62001040112101510031503c1c844c590341c01084020440080c0304620110f2001c202140b0203510a80081e01203d001905500304d0380e6a95844404039182d00c8400f40004501c00010300400c0800e0041810100413584070030040007031030000480341c6480c404c005120a40c0000c0b54411134941e81c0681f0403590300200225143c50303035150080e0058102c429254035a025100000b45014002e1042c40300281b0094800e0041d0742110070181c442c0c51620466a511000398400c0c4520500c4085040d50f90038401c1d0702628422505152104c10395245401c5410030350402c2c800d00f0110b480000f82d0303081807401c4040c17240058035541020f1a444404100b8190130500000030045081d007505010b4114040074010f030f0420540d2102d040342c8030841c00080b58880d03042045928006c0c1e201d2a0003a4003503074035509032550303140e8500c14a0b52010391036000c407c6807240c403000b100e8001401e100d00e06c01d50a00390307a50390726910790340d40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 16829125 1250 16827875 16827919
    0x206070e042706061d01090c0504060c110f04110c1905060c0a090905070507030806031b040221040f02010f08060901060302030c0c0a080405030111040b0a051b06010306050f06 77
    0x10322081062524842034103200164220500031702c011941c18800840c108602401e0080074024075407494149803681c0e03210791003002244e00b05da10556881c600c8445696a20340041c101c0c600103544101d0348031b489081a0385500c80c4891698a980d40d4680e03c2d01802001ca0509003204840300d805024641c1a402203600402d613164416008800c80b542c95800e0b00055800c06425003120350707024607010802901982200050411600944406946640d9a070425039900c0008a2020f8410f5922070b0604007030a054010b03002c0b61075a000c0d0111002c00d150035030321448004803000d83c0c1402218000d54150b58004030f06601240307851600c00b039240b91090105500d18818402d06003099400400101400d00c0c3d482074620444c14441603c2c038255070f5042c11400b41c0c101e402a1446940382034941d007000441181150304945403100302c1c9040421100040d07c0940003140034400188440c241c007401c254042c05281d01031445181c0010717071401c101408041200c40101b16600604000000ca2002c500700a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 16830375 1250 16829125 16829171
    0x121d0307080703020609130c08010306110307020a060b060904050f0a05060a06050a120908070b01030302070f060e040902061201082d06060405060a09020f180402040e0a020f190206070e04 82
    0x10703c11036641d94504010071f4880035603080055402d440c005810000f154003000c0039040702c0c05880207010500040c03c48040034403041d10400007603030100054000007002500208844980104410300702101c0002023000d951046840600101074001041b4112449104807a08002d00303a60102e1818104100a491845602140024044e0414450b007405243c1c0d040f109405a112180303d80702c00c900e00c0c0400d49035200b808100d0141c000d200d40801c0300382d0517100b00001c80d0314560300d0188020142040c84000e01d90894182e801c07840400c1101c440c2c0c0300d5240301c14020300c401c00c01080d0300002151203034002002c40e0044408140800b101d07a0754810b000401c1c90f000300044600040c10744904000403504495039006164050000c2407841070502d50340094038101451219a01400c003605040008074456400341070000c0440e000444d804140c541c2c042c003103041101c04064644010030804882081c08a0081c41c0140d200d10304000385540d1210380307085030b040d099509018a5801c8083c00c0d042078016 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 16831625 1250 16830375 16830379
    0x40305030405010207080d05040b060906010c03050f040812040e0c070201080609190f02120105030c0603070f02010618020901031a1c020607020901060801051f050f16121d030708070302 81
    0xc008202880029411119615448100d02d07070794114485842d0040c00049409540c281e0400300000c0c12810300710940c520480050790742c2e142ca60102e0303030140c41981203c074418008260500021a090100f004160368100740504a2601c4d01d107050810350410340f005001da40d01400600c02400142d800200c240d4000d0b5003200c098100395075503002503000500713152100200c1400c01c41b02010300b03080c5078000c2c1701c500c0c3c03003030350600e410b84e01c40c400d048d9196504049503810a02c01c2000542641c820402104150341700c0c8000705e8040e5507205030b07000000110207580540ca500282441c0d513503801d4890150070540c42140307280f155040900003442c8a808107010004129511403400440d071b07d000484040980c003d2000e805540c44840c000c040050174010703140134241d04030007680c8226142c040724804481c6540d4052410f039800403d0640e0307402050408610303462039804100010034070a400c0d501d4a01c90b0391a100307a01e801d550141c0748a00c4c1008858002c0d0001c1034244403071080402c1450a0343d0301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 16832875 1250 16831625 16831627
    0x10206040201050901110d050315040b0d030507030c08070c0f120c090b03030f0417071d060d02010903080a020105070206011401080c070318030f0201120e0d081812031f0b03040305 79
    0x2640b00685079000054081c140600580711044500d0b0b420101450280c146a648030314ac0d8080c41051004030b4050440c096070241c0c240d00d1050010f44220000c054043c0300b40b070100c804010554400405030001101201c140400000500103981c04620010040c112150303d2488414207448182c2c6000071401501e03140c6407145090022030310108120303030f65050503504007550b0720742d22091615514000e4103421014043c0030380004071080604c01c802c004800300e4808110686404080015032000c09101728180104002c0c00030211382100050702021200e50000702d020714100c100242007a6050b08900d0010016800c00719032a640000c1d5254001f2504a410360741d0401410117441200951140075035030080030790040100502e102001d80c0d450b1007038850368000c00d8480c1e55501694801e0700e00d01c0081d80440c400820b014810704c4155040520200808040064980200d0402c650021075046490001050055817004034680444200c000a50100102d081c03062680691001420180030050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 16834125 1250 16832875 16832887
    0x50909070e060706140606070206040b0901030b04020a0f0905010206160815030d0504030314030606030c2b090b010e0903030c0a09090612020f04140105130209040603081207090501020604020105 85
    0x202840380d001e8091070007481940c0b525650724090307001c1c182c1d10562085c03008240f0007150081c1807a0040d102c40b164020889400c1c0340c00c210380c800c09078101c05003460425466104c050780f143c85510051800055a072394814444d18109030180079045590720960440d0302010400402c0b03404150f21b0303000d140e40c51600c0704a0391100340d2880d00340007819010650502840c51f010b11f0b0a6006801842240e01c01c0e200ca0240f600c1001060600740401c032131054001c48100001200c010401004040300c2841c9402c075112403c0340700017a001801500081d184550340c41420350305021410700b0141c01005180803901c1140703003410015440b0701002e044100ba819000c120030f1101c90144002001828419008110340ca658212000034680c012400364054031005011501d01d041a02030020070080321540c444440c0d103068244280b8428031403007060540e80c00d1009404943e604e000304030043d07024140254a0b108041c104611030a00a880c0005000c1050380800c600e07600410065403068090900e00d498030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 16835375 1250 16834125 16834127
    0x31f260111040f030507090207050a0209070201090b040503030109061a0901140c030c031b03070c060e0103020702040509060402040c02070e0705070f06150305010c030e03040e040204180302280305090907 89
    0x12900552201d034010102d004210305007038100000403070b0301502c1200c0b6403036034803c4100100d210303129026105402103000c07400541801e0413000d4001c3c0883c40005800c0d0001d071a16600003000f51411640f41d0000401008031a41d80e02400029049040701101a214441c0444800788118103410307050243d03030002e2980302240c000981c0c81000503c4150b036a9161086a5142c1300e6100c04c41d01ca02c0c0301c0030500c0d03490b10440004241e03214240d0060f0b031111100c1c20700d41d05950003c000b52000b0304042e000c119100040c0c44d203008060048106000400c01400e0500c104000d8442c951207280031940a44c5040229030759203551140c1144160801507640e00d0141840e126003800e080000d4000c0307060800f40014144000221011640100001c02058a00079022415141440c0310012030342e106010601052029194140e08144000c000040510654450800c0100407031400c1d80988c002d0004503280a590300d407211a4001110307941c0107800d0582d81e01501a025213000c1c90301075000100010101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 16836625 1250 16835375 16835381
    0x6071407050907050301091508031c06080a0305030411040b09070c0305130305060906011e05270408031902070201051801030b030f0307020307080607050403080a0e0402030c031f2601 80
    0x50700000d010042d591070500405041c07a4020302c80c40c0000361406021100000f4038402c3d070000c1c0d801c000b01440c90810741c12080900400a101c030961aa41d07030b000001003046007004030b4081c59100e6105d064681c07a050400207a410a5940b800d8040d506101540f0000e66516107280e0340070140d800d00000e40d9040d8142101d641c0180009090110100d20003c010700c400003801600c03a084580c112281d41e0b0f00c030780088a02d19107044100d024241d12007002d110301d181c40c0150f80c5400248299022560504d4003a040400d0b00c00e84080d5007104001044c00703000c1e1480c3c59202c05505031003106500e08011540000c0c020310422004002080248803206900ea103e504102e4600000071704a56942401c4004c09403240e200380d00807807080c460341800107961540455601c2c450101ca4540c1800c1500d5502c94444550080009000300706030a034002040b03546910296000340301c10b2840c540c40345040c810303448003803851007070007000d03244028810020140c0701d401c161100030725803503034560a00c0d12058003405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 16837875 1250 16836625 16836629
    0xc0501090209180f0a0506070e0102030705030406030c180605090d1401110901030b090405061305030706020a0206060103140f0a0b060702060706050a0b0d0302060f040c12030e040c03060506071407 86
    0x22041842080c0034118055840303c040b040109030039130300d00d40c4805642c1a650035220710010400d40102000400c01c40c0900c200416205042c0141c82c0361240c1d9607610303400e581c4560440000710340c0d40d141d4075501c0f603807201c6401251201003007241040c5041c400c01504a001d400c52051041d58501503600c2040190f0180c901c0380c501490007481846442c111070052508103480590002e40b50080348581850b0000700e6901039038201011f400c02c1d40351412124242030310030034141c40d288000c03c00d2100181161000348800182a4050142414801d0006080d01c105118100c08a54580140200d20020205264020517510300010b4030003c840c000c20503a006041c0e019500543c0400c0d44001d01c20307280c004510170328a580e010050388a180041043c8030741c001c14054010b030301500c00a21810036400182c0d070058090320408880305d60301c0c005d524000c01c28060813000a5a4620103944600b068020140320388000d040a000c12402e120216895001e2180e028002c80768000e07510388044d805010441c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 16839125 1250 16837875 16837879
    0x150304120509180a0b06040b0d0518030705060906060a140904030e030304090f0b04090305180604050907050a120c051806040e040b0906060603011a0901020708030a03060303021b010507030c05010902 87
    0x22640c8182c5405a600b5481111540341141c05c0645000107450404100c3d425500020079150038400404462001031500038901c62801310310414801d40002d081010340400342c0b00d04028501494070700c200c1810980003410083c0214050101401054049910324003059000d07100891316543e60305045a2200c5900c0d0280e401d400002000b20301210160803802490213991700a014582c1c035101808201e035400c080240008074148158481281c85100c4680100b00050540d4201610b031000582d940c0800d42d00c0d1340104900159581455412074070069202c00c5c0d00c5000c01405100c40b030082d00600c2007120000e14440c04145110803551034105071070150484500481d542d190074901061680b81c19681442140b184000044161070000e0460f8180c5041803030848050300c5403044401150030600702541507020b00c0c8400718008400300301800421aa5a4002c5505403540c10040d06208103440080c010564000008a89136002011204050307490b26014506c480d05060a500400d06002c00075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 16840375 1250 16839125 16839139
    0x60c1110020706020606190308031e0717090d1d060f120106090801090510020c0c04050916050f090402060a0513080106051002010203070c020906040f020c0d0e150304120509 76
    0xd281207a002495100380d03100c40c2c0032105c0b180c50f4003041020105a0380c4207007041c0030400c0d0042c00021504406990030940d079003482140040154000d1050b08021140c40c1c0010307040b4903080c90400c00c0280030b16004552030000d880d41023400c21008010b0f03201d82c09000740d0302c101002e03008220386a0108031004958004070b11511016403440b9071f002d00500b07106010000d44105004100c1c0b00061180008056019000380101c64940003038901a401030301001c0910702841c502113080746c9860250030701c180501c801a1100c00060f40300c00004000310f401160280c0c070606a854060703104e0401e41070300560125900d68940c095031408440e240b1502403841103a00d03075031a0015001c281504441d080d82c4085442c0b4000c0442003000f00d08030302007140c840c0c0008426a401c2409400c1009050341c00810152002c10380c402404200c90581c0c3c411103407180c455024407411046254080d0382c0003440c40048803240740807110500901c403180800ba02c00f0301003031a000c00e100c91907800f68044400640b400b9240b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 16841625 1250 16840375 16840399
    0x30301090905070602120301090f110a090e15060706020904061a040609060807020307060b01090902070b06030d020303041a1f06050307080108012c0a0807050304140402070c060c11 79
    0xd0064408040212900e2260042c04900c042c00810560401c08440e10b00e5410351f8a05524800a46000c00c81020259610b58480400c020150010483e040490300ca21094910b801180090040c00404440b00502280300300600d50b951481104c005603040f290141c3c542c409140010024412135105851103040c0d81b25100e6240715001c050811a00d01d51160305003daaa9442030369800801c0340c00c500180c100700164400264150b0020207056818036001d81d01e140ca0700581c0049030b00c2a4000e580c84c4840908001043c501000452100d030441c0c40618114105907659850180081140c10640d005000000d046e9960034003251b0001303048050a084400c1d03a56001404a030b10664008000416010020039000030500820b8582d80c2c0060407040381c0b490b02d421a01c84503101c6002e940c6103028030040d20004c14010b44c007610709180201c01031541c3e40e1500041c500419104441140614010301501001c00c0000b0041c1d800c4640900f0070346e00f4078001c0d2400d00e00314240300032915401070f079034460 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 16842875 1250 16841625 16841639
    0x1e0106020a060f060e0c03040320031305040b060901050c1501030311061e0705070804090e1e0a0305040302040b1201050702010501060e010527060714030706060e15010e0102030c030301 81
    0x180c865490156104203c034460b07181e800d00076104640a04652200114089044900520001c50748a406403420102c03056402d40e04c000e034110320305c407100c19945c00800d50044403004120804014002145c040140c6895200441c800c0d005800c5100e044c030002040320079202000707020b12501085222207461466840c3d1401824445d0003009406051040301700240b428881c01d490808803000f40d4009640c01e07524280200d4155001410845100340144030000740c20072980100c0c45682201805090311180d40c5406100070b60003203005204651040c52038a001c25040300071a0f0640c0d405490110301d40c2151004a0703c8a41660149096586440100080985c1c19848281624160780d64a0212650240111402c1c01501c40c00004e1411900c003104400000450b00c14240c58050b0020303090070342e291039085880032101e0079203c3d150000100b4108020491107130a0151203400c0c0c03e49101d040c0351441c100c48001c40c030700540c180601f10502d260340707a00810a4039a413500c6842160740e2580c6801c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 16844125 1250 16842875 16842883
    0x90507050d020d09031103070507030204020306030304080609030903061b0406050d02070b0f040b090c1305130804080304030b0601030905030a03090602041208210402090703090201050702090a050613061d1e010602 93
    0x61300b0b0b00002e041400416040b0404412191900d4101c3d0080840a0858013040300039800640200d5240c8410000000c100c1818000c0e40d11130710745a4040d5480d0a1200c0c01d046c1480001840401c0c0d5416030900465592040c206840c2550800c0ca030440d1143c400d401440000d125122001e007405c44c4844c04c100c0d420100044940c842e610800c40d444450303c541c20100d40e00c441104199912104040a81c00114030942c042544840f1061403000d5451440d00c50084030750080d004800325420000302441441050420650000c2d801c0c0b800f0444850107440d000d807280981d801182c01c05456011600900c60703540c058030007030052a40001080045c42c640250203501020702c0404105c038580034192081c0d200240c581c4503980145c400500341e41c07120400c4004103c03000c8101c3c1032002c14050040940c560351304061240d89903040000e0b450920f2400c00000c40204401e40340d074a402d0140c280018600d41d130090301c0404480410340d5980d120451000000d01040c54100c4500c041d01000041480c0d00003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 16845375 1250 16844125 16844141
    0x9011d0f010b0f030706050c011d0a062f0307030b03030a02010c0311210903040306050a06090b0910090e0708010207030504030b1003050a0f0302010e01050405070f050301050f01090507050d020d 85
    0x100081004080d0b410910aa612801c03400507416000184100400f5010380b00500800c90300000025840c0010281d003558042d50014111595000c80e1217007080040e0780c030401c256496405040d03180f19003c101d1160f4240c6195200840605010000c00d280328040c0d041180707942c000509482e100d6100c070300300900030308030b00c00714000003404c3c032100003102038204044540b060108800303000300110001d06024003130301c042c0c6080b006e41f2040100001083d524820302c8e0099860340d0300400c51500d005064802e0383c1100030700074841c11441e0103000c800c407800a014400c80312000008520300c0e421460301d505115455201c1c016075400012048201607110b4000d0007134038828080144540c0b14221451485541800020441d51240c0e5056021a030521034948130fa501c01d1001180e1801115402802e440f415a000c982541c40340d0b1043c08034a503540b00b0300006c0c0c04164020030180c07814170206030401c5410b05c60254910340c3c0d6008601030f60320a1049a0f00d06450400666440c4000d04684009040b44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 16846625 1250 16845375 16845403
    0xc01110901090905010806130201090e0403081509090c100908030705071a0a0f081003080705060702010b010507020f040e0c060c0607090506040602030304031d040f0f0b0a061709011d 80
    0x8940103d8450710a00c142e9060711414001094540c3d624111142c8030300070044240d0611041c250001703040300445081e0340c880c038482d03a507645050400301c1003030408008540e000c0d8803603810101046610307180000d0b0084410011255840c40e04583c8030705540948a5030001c00190000080420a000000a0481c12a680419071400c004c000b26611455401003210320300c00640c020304181400e038462050150402c6000551600286d076035620000785a00c1400101c0d6150444000c000e45280c080c410702d040c01200307007041403801d80a82c0c000760307a00c80c00c000c1c0f6610482d83d0b20390308094a84204082215904058040c950702c100c00c180c184da913098211401000034184420101c3d0301c1c105070080d9412a1a2900150300b181c5a503582035510102002d16601d080d81c074064444041c1d034483c021800360108508000448070a0503030000d0aa0740c00849290041d03545030b00c00c2100c9a40110b0418004044011122213500e550040714007508490b1220143c034003002203504416000403c981001c1128 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 16847875 1250 16846625 16846637
    0x3050a050601090c0f03020d0b1e0406080313090509030c120304050c061603031802060a090602070f0f0e07050c010203070305061804030e04020c150f041502040f0306110c01110901 79
    0xa0351800209582c42500c0903000036003c000080c0900c3d0080e0040c180b031041221009c04c0b10049003000c200d03400c26200d56403409030030180780e0030114107040c420b980250010f4030245107403184907400401c1860240c07143c04e10701ba81d141c000690802c418019110709546040507540074030703003440a105144d0420395080e2414056041c136650345217400412120f51004030b400494010540382c805a00806c0c80300700b0034000724078900c00040142d48000007002d20311031540343c1a2500b030400740c000380b9042541d048566445080382c001d201886564403a00c045038120100900c0d20f82d02c4c11000c494a000b80c0a03650025800070050008458044c0c04c41ca01c2600240d8013510781403444081c1144140e401e07140a00070944505a901d06030515400511070b07100710b48210351000e4140a210103000f50100c0380d01d00c2c1103c01000340410403040500c85c1c8800c202540c1d0540c2424284040d04165601034400100220380d00c240c0f505c1090105410b84180d800940004c015020501800c3c0300c40b50300c003544090010f01c0e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 16849125 1250 16847875 16847879
    0x60106030209131802030f03030a150f030602130902030a0903110d12050702070803130e09031207050d0e0307030f030c032702040608060907081b240c0703050a050601 73
    0x322030300c26a464840018940c21001c0c1c0704141440c000d2803600305850b00100d0400c0e40402513101007003d1182c00f0100401107030341c1c2c9811307810201210100001440c18440b01c080c20483c200c107039507602080e290088001a40c0c1c400543c40ca00d80e09540b6840b072600c83d4004010820400d1240c1e01c204003240c0070391503980780d928031803000e175885010072811940421a11441010104240d6000740e0348440d150046030f0b1043c0d03d581c07806182d500190000d01c082a4920000c0c8100812002c0344c90708101c2d80001141030480e034844003c00300d40c004210f00104600865075041c82841d6400c0001115000300980e5560400307810020f254504500081c0301180c18a030001c1d2461740300b0b11403029a52017401c003240003850901c41c4601c1c020f401c410f05036403191b100ca5012038044000c1c41030318014180700c00108040d620740a074040c109060085da041000c1d00303400c11508144c94074814210004280740142d11403010310426501d60b1b01480b98050054890351002000300280090007104490103800bc6500507a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 16850375 1250 16849125 16849127
    0x606010302040605071709030307080405030f030403020a03030509130f090219140d0809031911030d050901051c020f0403030e100f0f030603020306040b040213050702030a0c0512030711060106 84
    0x480b81d03100e0360300010802c029200c086500300c050010542024100359161a4034000060300d075400c191816200554001000c004600c1e0401000b0511400500031350b08144c83d5030001342d03122107584406002c0c40000101c001d031301c0e41c0d0610b0f20022080102801c100c0807000001410090980e12012402211051850005030388035560b54011100d80b0010389504801550910400b09540142180c40c144240020003569500b881600303640c00042c40100c80981e414105800908402100940650446001802c80a42c400201c4e0b01e50142030070072070340e10420071426401c4444c0c0d00704502040c620218000940200003030040c0700320b9000703a4410002c40801e4040000d0418940d200101144202d2081c100490107072030140b1046ca050300700021500d83d6500030905042049500b1142010b01100700011071600109801410101c40d104201514207840041c1d503a05c58035203404107100c1131008140410108010184c5100c01c90134145441b4188510040c10801d070300f81e44554180140e5001050705 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 16851625 1250 16850375 16850377
    0x911010c0c060c020102011103090307031205040804050114090a030507090b04020c03031b1306030903140a0c171c090302190507030206130b0a0804050705010e091f21050606010302 79
    0x5140c219548030310451030b2010550780c2e1107200c00200e043d5521040811045400e4074060b5116024010185644031311601c6c008140800d0048400d0b041450300d01400702040202d4269400c0d501c0a08080110800c40c0107060580d01640340d40303a900114080d804010081c011403901c04448580c42e050050303100d5801040183c0c002c3c3c124800c03041c0d102f8000a11005c410004080c1c80c004c0480e41b940c03a00050b94150080c50240d5084078011944400805c800c02d036020000e4000001c480c005581046a0120010918200b601c4040c10016800501464030450a01102e02d44400094030070360440d00c2503400360246c81c6a01c0141c0241c0590744211036446500d030a0b0300350790340c1c1c0040a00425402e5508015054002c0075049000012070203001c95030311101001403038200100d4030303110b9203032400e481c04c6807420101d44c1140e4100505c1c040c080d003454403524527003500b000010109450049040102d0f4454030b43c00c3e840b012110340d010502c05c15128601e0850b0083d5402101628640d586400047d416 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 16852875 1250 16851625 16851647
    0x901120203100f020c070f0f06050403020904030804110d030201061703040803030a0c090905010603020d110901020d03020708160c08010606080f0103030e030a02090a1a0d1703090f070603091101 85
    0x158011011000382d68803594400300750860001e4006080c80d120726604e0346040740c83e0304140100e80022109000c52001e03000100f000b00803d00c2c10510306030555021481e020b201400090a10036a000820100700606440030100500076010b800350310f525040080c040c00380c504c00e85205031206149c08162002c003108850035a0f00b1a0b00441c556211100640000e155400903e010070208120105042ca044d00500340248a260b03005030300c0e50342c60280b1034100e4020710415900280200509480350b60040307000c5240a49c81d00300140c8581c600c0c1032200e010b100c3e96110326608915100301c103040052152041d403e940030240200001034540c4015a48080169404c06486921500410000f8800e1040003007580026007994041803840c2c0c04510a0340d002c3d1000e02c241d41c0c403001c5050319500300340d0030403c0c9040b0440d0072900f02c282d1501c9100e54840c24041c800324480c00000052103191041021003005564403040741c0aa43c5d9918005009100c902404c0f51040c0c2650f08400096100d40b41c0f40c41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 16854125 1250 16852875 16852879
    0x14090106180b0f09070216090506030d0309051f02040504141b07030c151b03021b0105010f0b0313050316021e01020c0919060314060705031315020f130509011202 71
    0x1003c3e8202e02c01c12200c00c0e00200b4003411881384410101c6000320300c2201c040100300c5144007003003030300f0120708043c10550143e0400c0b00300762038951900c2c0420301c0010211138074465030301c030a00c0122410020714080e05c0b403500700f1508a0b0600050b0302c640a600d021951140c0d40d1450b82c2c10021f20041481c0c030b02c0788140c180250010300c0ca98444000305070902c01032003603000321100001d201c000c2c1d0503501d9611000f220708100072a6003c03544068804000019140d65050000204002c1d03050105691020b5141d00503405011400700c0000e103040300a40356290b016400c4000c698272400c0c01580b13404451601c2100b03e01034000c2d0194211081d640c401c0b11044080305030040c001000904040c0100713000010103950245200c624030b51814a00e1348030b02400366008681c01030792000d54905041c43c00d800904840c00f0030a00b00200101e001682c540c41e4080da038403000d00040315000840c0d20b0b01074040d0341c00034144903100084403401c0d288603020300c0f000c4890035110019140c2c0c0c0d680c82520300500c1000080c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 16855375 1250 16854125 16854139
    0x8190f050c0a0201050d0b03060403020c12070e0a090204150e0604060e040f02010305090106050d030c050d050f040317090a0b0c0615061204050106030b0103030906030605060a05120a14090106180b 86
    0x80044d80110007524a600264500244c04000140000d00c0c041c001d40d010b80140c0c05c0400700030820b041c0410714aa250b10010000c012242c60071a014020080080052080917a90410310701103541c2d6070071540300403541c1c054114a00d500c801c2210030410040d12210300c15464103030b001441540d40c03082c4500c5690401c01c107070707035050040c7c0065000c0c02005004100c3c075580c400000c941503075a0401800c0303141c040d13600c2c0c4c050341c101860060310746520307078038000184903040c4041d0701041c41010844050700d034810309402410314001c4142d40540204491140e00080d039901c08207580c40004043c00c0001501021a40c46880da60740c0d541842c00348412241c1c01040410052040c80752128016400520030000000d005581751030302e00c02c07220283c10840c00510740c410100703d03c0da03042c010107015003411140035281c6101803034040c003a80b24034502401900c020300b0000d600b90b0141c3c1d0080d01501100030152129203481d02007540205094064002410000c1d250068000128421020784c614050522 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 16856625 1250 16855375 16855393
    0x50a08090a0201080a05040f140307061d07060c050f0607050703020c040b0105090d020a030206030a0506090a0b030303010510021516180b030f0c04031a04020a06170a050604060308190f050c 83
    0x281700a0000200705942800640c80b580340054601020401c0c124511405075489450500d0801d09850407a40d05131540418202d03210089800401c0c11400c8030030504090001956500c1d000303090103080440046031b030003030b01c0411030344503041002006080c3c03003582640e0b000da62000070041160300c140e58050000708140002901410a0446481e5541c00100b41280786540c0364002519580100d600704c0d8010303140da00780010b070704010840c1600012411002c0c80540f4185c008607643c0d000500c01c40c0c1c410b01e05800389403a0030b0b00034080c0090701b12807421182190301d0004060550503004845140000300c900c1103920404913028601003d643c10070090070b2658481c038466580d14100035281c02c070079250401000000a0328014510400d410702c913076109035441c2900400480e51510b902100030300113826480c1c1031380110554020360000d11100002074940300d000124005103143d401c002e00c0810001803541884e444000d192101030010f5035821f1850000311400c44150280f2803451406610150701c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 16857875 1250 16856625 16856641
    0xc0314031305010e070f08150c03040201030605040c0e03121e0c0c03060a050f0c03070203030402190f0b1201060203090a030803040807081c0c020c0a0e1b030106050a08090a020108 79
    0x450304038210241c200c0129003103803540b90865070031400380c030010341c0b0640c800c01140103c00d01e10070042c000070b0040c0500101440b103031600c1020003031901c225803800000050031a030096100201820002d082080540c02a200103009100d120103010b00c00c4c8909170032102410084c0044030710051006400d0a51031120745051003070b41d0400c0300e608101e40071300340c070104003030f10704100862160315400c001040506201020a0400300c0c040d00e000200e0350100100101a074000049030381003541035825403d860086000ca00503800307150000010100c110000040d004260001350014020003810041e459030390700e109907030740c1c86031020580c0c000d02c4004040010030303240800b66078480c1c02a40100d00c3d281c901c1c0d030752052592100070506c041003a10f2007105040744480c0704d1102204150300050114010b000c00151306030901c1d1285160002c00c050011300c0703407080702c13202d00c00c0c070f0300300c40900e503160358660b030011300160002114500011130810024520590000e0031061454040e15035205580fa650b00e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 16859125 1250 16857875 16857877
    0x7020c0306091b120307170717040302060429030106021005060901030c0501140c01060b0414030604020f100e060c03030f0f0f04080a0c050d08090d0309050c040b030a060e01050402100c0314 83
    0x4c84000a00050001c01c020854291401080d04410420199180c00c585094034400c2c03455250750080520a02007400142c03a030b00300700c2d400e4072081b020900c02d580f03c2030211b4082c2500103d07029608039010000140c410780029603200d11074000002170090366203103028010201824400980003c0c40c4400c104002d5001c0d07490b90b0003039082c121445240c105040132042c01e4a07640d611100780080005000c022211703910110f003c011004801410403401d0903000a94200c058900c254420402c040420301014010031150058240107480603031502c100380c4641d9140d4008441541c811014080025007410b540000039101c1c0c03484e01c8201040d500c458658050b01c1d080f980c0c807441880f144401d0540031840400105110a0043d40c4400d00c40c131700409405c0c100010340c58444e0515061014590014202040000d149201968005840c41815000a00d402ca0b040c0340038181901c2d05d046006210707410340040e4402d070b009444c07200d0b00c140c200e50116200100510081e00050750100702043c0c90600030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 16860375 1250 16859125 16859149
    0x105060a05030f0c15040906030302060417030f0402040c090e0f040210050403050a080702010e090f07020705010e030c040b010203160501020a0206011a070f020f030304060314010b0a080a0203040204020f0307020c0306091b 97
    0x11038034504198039a0503440448812703810139000b5070b00017020081080000e00452038210703020240d40e0700394101011041307001e003000350000f03110729100d10340d9442ca584942d0000004105030361440d440c1342070802d4042600841900d00340c0c002d5034540d070100000d9000c1c0c0c0444040303d5100c4004c0909043d2501c030780100307803c01d4000f2410003084101e04002965403002c051b006106103000100607040c03e94005c2c2c64441150700c114140a684e40b60070500340e41c04104002e0301e0800741d90101d40001c01c03800407400e62041c1040680c4e110318900c0d101c800e01005501030410220170340c00f201d609903240c01c100c40c4a0b118481e00b0f424600d0f020006540019050345c00d00c10700c20300c05090802001d494100181c1550400d030031400c0040ea80d041101c407640190201c079030041c0384501c0034901d8440c2c0e082000b024144004c004002d03290300000030500310749840d41140c19161510000070b807642801c8400a40342c091480e401380c440d208010100b40b969502180691075010080b2134021948020703807e20036a05601 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 16861625 1250 16860375 16860409
    0x6040b04020301030501020d0b01110a0303021e0f071104090c1203020f01050c09090c0a080c03090f0102040f06030c080906061002100204030b06010f0908100902130c020105060a05030f0c 82
    0x9504552554886001541c003940c0300300000358944003020300c544101c0f01c0408a140c10000c407000700b140782c1304001c60310070740f142e40600d40540e4599001800100c0700b000c1c0109400d52840004d1010204070828000d80b10403440f50001c0c0030f00244150800c0250b441003803015001000301d0208112461410074610b082c10700c40d00555039501000480b003030844c2d17000c03a00d001402e00e0004840384149040c0c00000d078090445002c0b1070401d000312100510040000f0200f1086480000104110000421074600c02c400d160000f0b42d41c0380d4940d10005000c1405215000209017040c80347c81c56940283e60042c030850030b88005241030b41c0c0b0301041184010301040d0759000d44c02180b00101119810340014405103005000c01816402c050000408650318003401d2801c00c01e4a940500c81c40e0004610004102072100e000b00303150400d4000641c0801188400792050f507c1c210081c0315071501034010b14456101100c8440c0700700d988205058880d001184941100c2c2c2003066070803900c0c9807440d0003628503000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 16862875 1250 16861625 16861631
    0x109020a020c031005010f121a040302070803030a020a080601030506010e04020f0409020d05010501110307030207050904030e04021b071401090306020a0c0c09051501091401140d1104080c030d02030a03050604 91
    0x1402c007207410311040d00b00e4000440c0d21800140038100000321000000c24503895102c00c0e040103600e50140e0300300480c0c07081d40502c038450081030a15200300144d0b0082d00056050360390304c1c1421030f1164029446802540042603290300014490340c000d00c035403445490706031164041e101d039260800c0000d40c400e1030a460390401c1800003180e40c0d450fa2020b4403504010040001e020350400c1c0c0013400401100c1000030660b8410091040065408100e12085a100751202c10058985140c25a10160131340b21311a0410310201f031140305802c60841108144410340700340c510700f40c6c50382e0540c100007100c440001c1c00b16100e418200001001a8024042c81c103c41c03502d00c908036010b5843c040c80d0300f410303403146280588800902410f0b102c5450f0780e2944120900705400314503c0c020209009505e02240641440350b00680484c441038030300d00715902d8000c1e040041042076105558540c403508140a03521940c030030080c10250300d04001941d410a440c041e00154180110800101c01501004000c241c019071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 16864125 1250 16862875 16862893
    0x708010e040812070912030c050106080a0c17011413020f0f0105180301020403060e1c05041202040e0a0b0a14090a23010603080d02070b0a060312031a10021c020105060303030109020a02 81
    0x103c41b00c104003034910030350f40d000c040f4581d400c0c02d80c00c0d2030194002d1001900701c407148800050703050928070221001c03108200c03102060b000d81d00780140041d11100401c2601e03401008104c1c80001c0800c1c250a100304c640b912070003507101c107103c4038100f80c2001601103a4104080340d182c5402c5441d00d440e8500c0207002510301512680d4840c180c030100051900319510044802100002c1c0301d508005d0003509103050343c140351504100f010580c503901c001070301503940c910b041c00c0340e200103001303114100b600003004e0020740c200000780800a24005014454000c00c1c0300201703498441c0481c09601841c1c1101e400f42d0400a030880d4411501050441400d0940d80c901000000805101c00f0780402c1280c00030060700c2c2c0545080001081000814180d0254034281084c00007032040805444004d9451900107045641e08100d200c030324444890056000c91140840365201d640090005e950381071070500502c00829507003080c0e0076544240e40966040c0c1042c40103024544e41c96014101041c014030446084075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 16865375 1250 16864125 16864139
    0x60203011e0b16050a02030f0312280504080d15050f0f0306040210021903050901110d080a050618040c08010b0109080604030f0c080c101109010206011206150801050708010e0408120709 81
    0x400c1e020f142808c95000424500010380700001034a50010314038040c0d0700e00001e0411f08000c251207604d03070102c40350742e240f020a0522101e4030540310150a03854042005014420710010081d90b14400c05120307001107a24440541800140d0100480001e0000c183e0342e141d55007004100300324003401500b10300c6a40c18098901740351008003c4414001d4540c0c030742e9400c0c03207800102140b11145551251750b000700d000500c0c1e070b90301c42046503009214110004040c0c0300c0c5030004807240d10f10440c141c0121120818402400600484901110942c400070007140103650015900c0c22054803501500342c001100040c003080c0100d0380109142c041e860502121411075036442e02d00e80000308034a12a40c81071500c420b45020360300c603a02c05040a4031200f030a000c92080002d507100c105005443c209003000d0888020070502d0f170403901c60104180f40240116480b046070a000740000c990a40005e082d6000006d84404d503a00790602490704440d07030b140f50460025504440c1c280280116040041c169400036000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 16866625 1250 16865375 16865383
    0x60509011e0605010201050708070f0320040e0f010e0c1c0902040204031103060108030c030f090a0e0906041109010e0601081312090305010515090103030c050f010603060203011e0b16050a0203 84
    0x749001240c0021080d051000090071135800a10080c00c0c4120001400142d42c0c110750b208884465610300410301544483c071040b81c540c5420141d05145101150100383c43d1503040e025449070703c0c0414500000c0e0780c0e039000c91243c09015219940300c400100702d0104c0610b82e815900051403d01c05000c03e00035400d034046003c981c00f6a00582d81c8078004a00140307145800d01c031250041c410030000b9820001801c0c0c0d85ca8503481460300e4141c5190380050882c0031911008411001041e0003144010b0f80c0c03926084080c0c5502049504880c00c001080040b05145044010345041c0e5120305200c10b07442d685c64005441004000c0c0c015600c0e000301400c01030000e0380380960800c01151a95480000515510307201e070a440f4041c0001050380c04290601240c0c1c0c44004a0b03e04490309071401c16400306260030603074284803030110011503950801c500403041c03015640065049540c1d40d2460200580c0d17100e0b0030510014540605105075004002811005044852107101d080c010790949220f5a080d0b40040e2030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 16867875 1250 16866625 16866671
    0x5130603080d020a1b1e0c05030d03020307090602150105100e030706051b01020c060f13060204080706090504090312110f0c100c08011202090c09030d0903020406080c060706050901 79
    0x42c041c2c00080f400f2400d40e1000c0280c10015071140700c000400905d90740e003e18041d5900325014211a0b4214172028400c25110040c010034024054584491070948000d0180d07204441480200c0c0e108500040e0740d6100041603034031a4031003440ba0000340d092070200400c04400598490030050900c840300c503d958107004180050406450b43d40e0b4400020013054811000640103004503441403000780c10140c40420081d40c401d110044440240e82c0d010b01d00122900d80d07203c0a01214400304002c030781104005030f208150b44080c1c4551481c40d80d500208002d513046214020000307940012808071000b130b540c1118540400c4c1c1044181003454088426401d07801045036202c265029604040d811030b9070744140c1240074921314004041d50b040c00c010344146114014002d000703100100c0000c83c8503d4210a40d020480d000f4255900d5035540100285a802140426880381e40b4141c000a00d1400c00074a05003000400741003641020100e8440c8001018010006c0d4031079529000040d00741c1e044c220002d20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 16869125 1250 16867875 16867897
    0xe060d020c0a0204050105060c03160203030c1b010e04050108100905071d0103020a08070605030103140a0611030405060f010521010e01050705031005090402060f031005030304060917160513060308 86
    0x1808050b00400c01542c1703040e84198000c2004002c54400c3e440b01000712007402c0c60110108502c070020380b01082c6180305811001581d40500c1c000c60f002948104c2120184005c2681d5440d8004201c40400040b22000c2c480c3d1402540400403504440e203450700080d45407400341d41581e405d90b40d102c500c4005080100002c0141076003400c0103008510300081e00c940540303101d500504225040034406410351206010180c80074000e003502d0f41d10640108800b00c071190b071058044c000e40b0140b40311400c039504107407822501e0b0700481c0c00107815021040c5900d0304852005114001400e0149a40c05c202d03002013500500c17554070746100c00c20406003405010b010341403960f41c155517803501e005440d000080701d8015034070030702c4030b1424880540c1d10a0140c81d6100c6e142d601d259980e8880c1007842d042000a5440140c041c00040303800a400f54000272404200c40f011402e01c01c0015208015540f130b0f15540081000f9a074410509200d03a0030040c80003460000600e000040080d141d40b90001e4907003003591004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 16870375 1250 16869125 16869133
    0x60e070302041509060b07050723040906020c0c01020f120a02070e01150210020a09060e030c0a18060501020601050a03030c0309080604080703090510080f0a140411030c0a12030e060d020c 82
    0x40d04c2102e03c07501c401481c0b040b01e168200f400c0c6030344054a40b20144519150b5000c40c1c07059442d482801400320600390780041c0204450780301490070a019401a1502d948180110b40040405500204c0d4600310319170584050041c101841d0501485500811004000c51240d1440800e030030740c020b04d006028010380d141e01c1d8641508210000e1801c1c403040300c024503e90040c03047c0c140481d00850b1150540b8000c1c140020007010314804645046201d0305056440604480006441c0400c2d09104c1a000c6001c0300c18800d4035200c00042e81e036101b00f0f20a2a400002020040011a209030556803145200b4a407a660f210ba5800e030061901e035055900740c440c04c0000a60308205900641400028202518201e40c000c41c511750150261900030002014224004005400000c580c2e000c1c0e8145012012820b00a080c58104165112801c9913041e01a1080940303803a21440d03c0c1540c1070441c0d4071004404000e0356643c1d421038140b2007150f00190041e100784812030107078085001602841060000078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 16871625 1250 16870375 16870379
    0x9030c060d15031110090308030105010507030c050a0308040c050307080601030b0402040e0d09090c030608030d0c0201020c010603030509090f040510020a20100b01080c090d0206040308031f05030d0c060e0703020415 94
    0x4c800c2503903045c1c01c4014803a541d04100009204002030324119002424201e03140d03004c03414152908401c081000f070550103200140d008042e04002464001c0d03000b115031600c40c9440f80b0515070b664440340100307882f590040c0010000a4840300945031b2161000e800401c1360700074211818a00055040a1004a41c41c2641444000c080707215010341180b0380e24050000b40d1130030364290344074410640114840d540340c010758211503000350111130f0301d1543d0600801238190f59040c020b14503002054130070722944003031010594407a01040103d01454000d00034080c2145060704006c0254010f00d81c001c10300018042540381001400e500ca444c400024000c0e141c1d2194101085c1c1c2202c0c4200541c5041c07161f003105110344100114180c1d40224400c0d1200502c00000d40002074840c080c60340001e0101c038000041066107018620f902c40c210f4900400301000d02d48600400d078546401e50442d000041040d1100400306420350050f20341524400141c0d024991030b034020500348c13206c40000d41c089442128013 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 16872875 1250 16871625 16871629
    0xf0613030302030c1207020d0b070221090a1203080f090f0118030806030105010b091203040e0901060314010b060d0c050d0f0209010f090308030c03071202040e0f060609030c060d150311 81
    0x7000c17030916205030501d030121540c006085241c6040c0081e182d05003160000e0382d090b0080110f250401c40c12252160b00030b030b000310000e10340d03030007000c05d14024070001c5000102c80440d800100091981500e03030700025980e0b444801d4903000020281e40d40c902c207860507840f4109003071040c5900b412801d01582520306560a02920b1904040c10303007400317685040700400c4225150000d46042110031140015810400e845051540c01241c01004030125180c1c01e000492205520100440740318441521341361034405501422691080031554009104006020340c444056200c10200c9030107040490406418960311710480f0191403c0d140015400038001c0b4156070007100440b100225071502ea107900d81143d5900c07000f030001500d09400581d0100205080314080c0c404013605001e205000c42d01c580d55510255000391007603034a42965100507021031080c5c04c102040382c1d2900d00240051564410710030074003d05900c85a00010300c1c5903907198241e1407034409410400154010011002c2007050001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 16874125 1250 16872875 16872883
    0x20a0b0f011419060806040b041503020102060702030309032a010f0e01050105030c01050d090203070803030403020a060b010807020a020d020103060909080c01060b13060e01090f0803030708060a050a03020f0613030302030c 97
    0xc1d50900c200003000003124000d00b400e040c1001e9030080d21705510340340c940c04081005410a8107190340d00504021f03500e059881c1751500d81045034002d90031200103484074517050380c40e0320099817084901d41081259008400d590b01c0412076080344035040d481c038981e140051900316809008010356140c0c449040076540700090090502600040307010340301c40041d0000203403492140400070507003591510301480035554144000300013044080c017526036078038291400940b03d5042e000200d5105150600796034940d4415004188904015001030019840390780800a1104401004a040580301d10000c2349078241400f490300200d20940c1a5516110443d030a0342c00d48847d5001030200c80301c140440d400c101103c1200d10100c8880342080184040340400480b0307032000720313002444000070080000801d00700c004001d40c0b0820a55895100316100c6400301302501c02e8a02c20031f0b030b10042c2e83e00144094a41514030a02d01e0000400c5145080540c1c1c60809044035154800c0d4096000410180d0180d00c040c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 16875375 1250 16874125 16874159
    0x602060603100b0109030201081e04210c0305070b041b090b0108010504020306060f070f1b0510020705030304090e010f060b03070f08040f060216150b0a06090e01060f020a0b0f01 78
    0x100050250380040fa0000706025214030000c2d04201c01e001c041113128541c10408c034101c1b0244900d0381032615050600d25903600c07103050100c611002d048400081a481194405c496680c10707a90302e03140485a84070110b0664000d0b105440f0146080341c80d13540002c268070740c1c0c4020240e40d440414001035540002d0401501688160700813070040040103601ea8030301e0110f800d0751440400742c86d16110b171402c01d025060780102d0000c114140c4045082940d54015510b842150350866092458045c4400100d07100c5456126003a0036500c14802400002d80300d400200d078034400f400001030400f45090024068442c140d006140011000044c403100c1d030f0b4060003d10304034100c0d04001e6203609040c1d4600000100c2008042c0109601140e03002d10a41201c0c0080c0c8180d13000915030780144103008410004007552a00d4a20402e00f4000009880d4041c00080d001ca801d40d071a01903040c0e203402810b9403090061640740085025400b03960000070905041c50380a0351300c10f000c80b03510f07605140d0101600c054207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 16876625 1250 16875375 16875403
    0x109150e0f100c0c05060f061f080403050c0c0d060203100e040f02040c0c1b06030c02010e0312040c0b040305030301090b1203030a15080d0e03061e01060c0807060203010602060603 79
    0x1500c01000e001d5000414039416104480c00042c0c035560300301c08881c04056403000601c2c50044109000140d0854154140204409c80749410040d0a10b00c00740146d01e44034082c01d01003840c400c000741c00b0034000c0d4040c10078040b541d41996a00c1c0d041d0303000140400d0140b02c01b29290f680c00300c1030001d00c45e1042006000340c400d0741400601c60400d80c030703000d005140c1031703d0081c0f140d61640192041e40d0720030700903414800c0d40f1024080a2542000c24001225a280a61400a0700e0009e400c3c0764a4414000e810303050829102031840c200030700a0103422448010f000340d4000d030101c0d10004088000000a000460154003d503403294148030782d0304103803200800c065100b18400798450184203804001c40b40c1185460348000340602e0f000207800100582688015080e00034411004c40c0940c000c003003142075541c200e090341d00d0f075521070011405040d141d0b1894111092140014044680180e00b5103013910f025909007410000242e032406d041c5e910980100005800c0042403107c7c6040030420741b0041094 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 16877875 1250 16876625 16876633
    0xc020601050306040609050705040e010f271506080607021608120406050307020709021b0705150301030308092d0c0114030c09010302090a0605091306030c0603020901030b030109150e 80
    0x1d8800042c1d915407000d003010b0700746640c90220b0010000b04000800007031101a10500c403050840003240d0081540c401072a03891170412480c0d204e42002403d80388000f0b07488164907041441c0544400a0380c80380d00d01c4841780d00f0740c1c480c3e021030100410002540306400a6000b4000000c821854280388211940615245c2d4030900b1030481c100c007010152802e031940303442c3c82d589039505d41030100c1ca401d920f9070081008604c0080d000622158481080c2c0d41c041d00101102d040f140d4480501c440c0b502c008074140c4400f0010300c01440000c0c4500f0900d03801136042400c40e4010344010300706a80001d880c07401400504080d01046072410300500802d080080b0034280040039008000e807448031444000c100710456080018013401c02d0b802503050355007500e4003038035445240b600da204c0a0a103601034516544074901002044c038401049003d00000e60b83d00c007000c14400751038440190041e421400715a4141616100c10b04042d444c02d1081041d0507000340c21400b2440d40c2c0e440210102c0c1c4540590007185d0704 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 16879125 1250 16877875 16877879
    0x304060e07171522031206061d0103090813140a0602030306030601141201020d0c0e0a03030c06020304030e060705010f0e0a0507051207081603020a14010f03150f0909060c020601 78
    0x2030301003040201118050000d00c030903510011413415030402211026842130803c40402c06050384006201800b5031004030400c00c41d40c8542080d5400b00c2450035503104040d41328200c04003540320360048848603200d050302900701072801344d46407452041303500a0321100710800c80d6004140350a403a41002851240042c40c51400d002c00402e0f00c1798414020031000f071003040b025400030345610170034080068a21000f103448640c0b0700c40c1c00300688980c1482200042444030003106501e07004001000f201e6140d1503c10a20b882956854003940000b84298140880700c04081003540715000146240e0740301c0e900000706081c000c0c40c45000c55684a035000d00c0f6602810400002400000b194001d8401c100c440440720074580142c1c5180075000c0c0c114803018080c00b090001c14000c0031f44e1500079070b0f2088070804040354030341d03240a003803071b4411a803140080d0080d0320044840707001c0e50040c21707100c00089180c0b0160340c94201c0145000c0381c9a209400c1c030755031000c14600384030907441500075401f8070344043c0a040d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 16880375 1250 16879125 16879169
    0x3091e03050d09050304080f0a0b091501030605060d060c03050f0a06050f01030f090602120f0106140405010e0f1c020f0303040311060f07060504030c200102060a0f020409020304060e07 81
    0x101402042c8500c0d1680c0c0c8695000307002d010810341300208450411502004800b508079910342006440480c0c10000c008041401c00e20045881c003900302101040b022540c2c40c5880d143d014003400340080b0f0f0061500403544010031102d02030048080c9864034046145d0074a01c201100c032202c01002c0b2000c0a10300381c0140010b9540d0f82280c0c400307500908c1d0210707040c0e03400b8090b40010140c01200411a070704c001030000b852207081000368826482c002445c481c80e0303602d001c103a5808034010b0f490700400f901008107104560050414600c6208040c008484420020000c1a420301c8024014031080d150b101c800c07801c44c41c10940c06000c0b44820350155050a1845d5144018a00f426031510f210303103c0490a4000c0840a10940d14285d40140c418451820941000740c1401c01054040e112003103910707141040707110341c007580802010040e80148095611150840c0003080e00e40c0071501c0b001d0b001c00000900c07401900241d40034900030704c0001010701030014030350700d00003a40c0c0c025002035000500c100194 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 16881625 1250 16880375 16880377
    0x90303021c03060e0906190b010504150c1205030a0605040204080c01030b240a08070c050604110607050f01020405030c120a0b0406020708030403031a0114160302150703091e0305 78
    0x40026001c0341c1810362668142640030b48411341000524070505810824800400071702180540803041900380301f95070300c2c1d007160282e40b104c49849003c00c00c10441006070204042407600d0320a0f1a143c041c0206210b07545d0303049110303514000100054804428003440013160703c2080010302007210210b1a09203442c0302c0c40d441d1210300005605066640c600791006480707400303160750524184003152000c07480340c400000c03840d0010403154002461080026002c0d40c0150207c400d010b8001008040369602c550b11b85d0b151121b2402c00343c0e00021305010b00400a602013081c114006d0f859000540c89034141020b141c031f070001503240b281c0300e020901f400005e002d10100e1500c41c1281c01103600310040c0c0c0c880c00d15034003a1160841c002c04072140042000140740c0e00d076002c6c0b0034014510151100100000004580d0540c0800030705083c90802c209004d8940210710103406c40c1c1303101e40155060110070144102c2c3c1404101d88800209455040000070024418038107001183d000c04c80c100c10201c551402012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 16882875 1250 16881625 16881643
    0x408060109020a11031201030b0114061215060406020105221a04020102070b0d02030604110a17060d06090506040501050702010501060e10030605090106030e0c0603010e0601180e010b03040b0709030302 88
    0x140030b030b0000d1600b00032031140041d4070740200400f08681e92682030ba207558100740001d100560f140280a800468000c0000032292488074000340b0150034014034003684004460040c24204d01604108071000d07260301d5a4026000401841e0000103042c03900d8a0700c0300d0444403600311401e010340c02901c50343c00100e40c0718000d541104014464a1241ea484c401031349020701c1c54200e034140000106040224103a43c0d002075218174019942070100c00c088080b80324140c011000c03140c0210744500001d42c1d401c54a884003070380c09440140790601e8a03000e500d035401284c0c5944d9042c1c070170340c02c01c1d010030090090074080c940d048802840204225850810020f0404403404403881c0f1980c410355035812064408c0e0840d00151600812040030f41d691050040c0c014000d00208066a00900007030211500d80542136a0494116081e101051ba4512004444d05005100700346e000065122010810080c2071201c24064601500c03c0c6590703003828200a08040c8004014204111842c0c0092000075404907030350fa1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 16884125 1250 16882875 16882889
    0x160804030f0c050a06050a0c020a03050412030e0a1d1e060105090102010905071403010b0d08090f03031e03040c0801050412031a030a060902011704030e0927070302010f020304080601 80
    0xc05101880c10482e0761594a40000d8454401da41c52101407051543c0014011480c0f2181006826803808050340c4034207007810098049441032000f00700c4400030718950f0f41964401d240400c2800d10b28800034000b5070b02d6401502c20751090301c0e100e070000b00c0050801608281105501f9462a200500006040e040240140e04222002c51403c1c0140d000350064956181d03c102076403c1240c03150040c40344113035040e050300d201c0d6081c10619040d0782046d070b6465101c1a00481d50b00c5c504869401801110f20500780c0c140e806100400400c0c0400760452081e0020b0003031104920740c2c9040c182080301c603006064010102c035914200c1030000240700c5115003d60032020307041c08101c1554140710100500034041026805002e030345064004c0003100d0b888210ba051003603c0ba582c200a01c01007030400c200b0b04583c020085445542d480c40c01e898102203090380400028903c030004a022172030b4080b880f8085094010301d07842400301f40110f44e044031245c00d010040b4402036040900d00380a09540e07071010311602c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 16885375 1250 16884125 16884137
    0x3040603091502210c1206040203061c0503070b0c040803160203030d0e1005090102041811090d0602070b0906060d030503130c1e080105070c110102011d0c010816080403 74
    0x3010021810031400b0081442502107407070b965502e0304000c0c456908100901440c5500f40001d1050301c110f01521448140c800d8a04e84940c0c030081804005e40c00504805e078000e4000c01c9004210013080b1801800c1c91144000e9034590603589030500790303180040c2c44541d40440520003032024500010a8030fa6650169040c080181214004030382035201c8d000702d07024041c5c00c0503076800c42d28800080361480301190040400c0142c3d10180f44508034010b500070304401120311802455458050f4225070080010103186c41e285c5004a07001800031130741444119105900441d14030188804001c0c0103a0014180024152925004002951401c03110b00c0c02024010044003040301c0e00c241d50307006009680c0c4440d00a0702d2540303a483c40318800d00c0810ba080406e1103c090701181c10340040c052180a0040c5031240010041150780da40d851a114016503811596940490001318801c3c034901d8408820400c0a0300300580030748001000204010481c1c55445040d08c03802d14010340c8100e586a1043c3c00d45410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 16886625 1250 16885375 16885391
    0x302030a0603080309030408060603240c0f040e0103110a0e06131104030f0c0f15050a02030c060a060501020f031e09011b06050f0f07080417041707140105030903040603 74
    0x100007071240e908081e1a1080100400c649114000014004d4071030141c12510144c1c2c2c1e840c01c140ea1049015100c8094801c0300c0c03a14010040e03910400e0350420900c03e08182000194103c4d460160044e6000c10a0400324a0040042c01603147d9600000c0c0302c19641c1000c951705110503000708045c09450140a200c5038568442c569147d07900c1060603207040b4022903a0303a03640341803100402c2c890101c00e031081036448400080300c01601c0819401c542140c28101e110314500401a5010f4000315800029804100a0441c03030400c1442107606c1481d10b01030008005d0300f4107000a141000101e0010790710344c410003454250480058019003a806500345040d80c0790521401207800940110751070002e60b180b6842d95007008101d81049128030604c840100d910396a200c00e2610035007042d6141300229440c480840d020411084908129019a9201074600340c1d9400d209503081e03800080d41111500036403401c2c0300c21301000c005940c10706002d02e0400e0030750801007082ca07180d01c40c6218140a0542ea1802 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 16887875 1250 16886625 16886641
    0x1202030f18031605010510050d050607030b0109050d14070602070b04090207020303090a030c030203060f061008090f030406030f0506041e0c03110c01020d0b03120909041a010602030414030319030203 87
    0xc0f00d40092190386111401c5009190150190206a905c440a82014800450700c2d081868031107104030f401c10010000ca0f101e10f502540180b000721001030420211040204194550780d4180000b24414011594119103603003002e810002c2d0f40c2c10000864000920400c078010800e41502d094409184005a598201e80300080c6940310390880c0f02d13007092417003400100b070100300708114007207a00a400360349080c0d5800181e21042d810450321150301042c0803ca202c0790130300c19000964000602c00840349450b0f580d100319842d50700583e01c0f2030006a1aa6000044510180589500f01c501642d0038041710f0310000208146040b440d502c501b01a5490364102d0b600791203a00100c068600b03030726806503500c49507420f1b64080e600842c070f03a0b02080e04001c0000391608002a410400f040d041009a062082050401c280007901034407e81301e01c000003071000d6507051140b04040c020041a0011540d80d45007004100e19820021a0644650002e110240d1144440c0988140c54603032840d00594941d282d1407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 16889125 1250 16887875 16887877
    0x20906060c01050106020304170105040201140318011b0e0906090f070302040e190c091a070807060e010501080708030c030403120201020d09030f090e04050304140112050403030c1202030f1803 84
    0x441c20756082100000d10765401000400c203403401d44010500104510540303e00781c43c01078600a0001303202c1e400301c0700c05100d10000345030000303030b40c141c8507022000c060080e50a50324502d41c40c0c03003010b503a04900041550807404080d503c19007980e400c0380754035101000a00f032040080203610744841e4030001982c014400d504480160840d070b40c900c062410f0002c150102d00c8801080030182500c0c100000601e03501590540381115005007009001e00141c41c039065080d0401801160012024091917001901901808a6982e498000080c03c1d61400c0f9008c4d10300100c0c0d50021141da001044a005a0340d00481241e090301d400944000c50204600d900b03c7c024450b0a000c280a44e00d0301d0918001c02d684000304490507415a40c0e142212074994100440c6480241e034003c14907801000700704242507007030200c4292001c050402d000c18140c1e103414041907640c11501100080d40d51200c0300c401c9034101d00382910301c01e0510f00031811841c0481840d203e0030009000c8800c0450b1030020300304c1ca50303c200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 16890375 1250 16889125 16889137
    0x2030402060d0c05040303030c0203161502040302040f0b0406050d080703030518060405010e0c01090503070527010801050f0f0408090d0215040602061006140703080615030403050d050f100302090606 87
    0x2003c00c40c0550300340700105950841d001c1180028181092a03500c1480001500d1310081d110304a0b901500a81e035941070404910316185408940034040000540d0761441041c42440302c461012030380b4104901080119a1140c10881c81054a4204680800c0301001034030411036050500240703507116043d000c68850443c0001c6001481681c003084101310040d0003004010101c202100e07140f401c000015141440703580141034041d03100120401c2503207804c210003889030041703074048102038140a041c03a90311034098001880d942c2d120b500348602005001070b21076001e403110100c01c0c02802c0c550788100d4a031284042c5103100f845140203081c1035507500c140003144070f480b0780e042665659880e04040d4480383d0403143c4e00d800594100c0d000030424040c3d12600611300500da481407403c3d005a4007503d0303011000e0a01074000301d00260458441201c240214015802515081c0c0c65141c090550360644800521025951803500c2c2071043c0c910b40590504241c9904031a00c0515907124004a2b000380160 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 16891625 1250 16890375 16890397
    0x5010213060203071505010501121505030609070602070501020d140d0b0301020d09170403030f0f02010e03070f02101d010f0509030a12270b030c0d1401061106010e06040203040206 79
    0x9a000040c401e900000100603203445003000d0382d40d02016001c2501260824454540400d407095408100347c0c0e00340d407045100182c10582c010b1038589030008a490300c241142c0341c0080f684900700c107005080e0100a1030700101401d00c01015242030001c001081121421920106104003056031500244a500809051100540219200c4690700200340141c03405010a6405050385400f1810400c0703035008940503a501505d4401e0f07001312240040701c00407410144c50045561f1035100003000c00040c0010098180213200480300040035004006400c918801c00c0e03024022040212494001494004210789000b428070703041208254038151090b04c500f00e000e035031600440680c542001122602c0a10b0068943d4503009152100303100c1e0b03131103090781d600c01e4a100b00407113038200140c01c0d03c0c40055610083c030020540c01d2400b0042682c094400004204020141d105c00601c01039600c90f00c400c1a4242d0240108065490101c41c0089c841001c2c00b014003540c3c0000003e402d544500d02107070545400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 16892875 1250 16891625 16891657
    0x3041206090f2307080c090601090b0304030c060c0c03140c03090a080601060806090403080a0b0f030105090d03050903070803060d03090807080105011802030f15130e070306110c0712050102 83
    0x10700d4100f803818024030310100907941e18146858400000500e850039128668000c000c1c07010364800300980c0c60030060000381000b00c201400701d0390015000145010b284280c07500107a40a1918200301561002c0305010100601c21414001199011042c88007980031444a259140c001c0010541544108032005402000700000020111400a2524120b80840c0c0c1c1d440c01940301c030020440c9680701a1000b900107243c041c00b180f6540340e580d101c01c01400c4010802e44130361b44000e01203825075408807040101600b000d50905202038240c0512a400046a0060340c503251040c0d860094a010140541340151043e801400415000e006140050405102202d40c4a5581c651090107403c1c240158030603e5a400407649914581b40282ca000b01e5143c441d6403410355481c00409a015a0059540c0c0e01a806154044100c0d01d540f159292000468025201c20707401c6080000649003038a4011102c45000c1040001c0b0f4600450103006641000c0c150040402d40340c01c1141c00790141d07412080d08400303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 16894125 1250 16892875 16892903
    0x90c040606090e010801050c070b100509070305040b07050903150c040504140403020c0f0904021003140901060f0e0906011509050405070c06050f0403020316020103140103030e090109020405030304120609 89
    0x2d00016004101c403aaa03280324900da03201c030901800d075281501c0102d85080300741b14a100040c10100381d183e000311050300200d401580d036000030300d480c2000e507550004240d0340c03070921040c89850100c0e641d11500c10b0074210300e0181c007400803d0380c81024804441e039484070b91000c205c02d4102d40302140c0007408014030030b00103040b070142c1c070078040d80065034214050310500762443c4083c240300501408007a40284400b10319036840d001c0c0009011350210740c008065441444601c40f0002c030a00c2804ae05800000007a00c9043c802150030283c0c00e5000142245d2104013001840c0c00005000f6055403001c0307408155080401105031121252074005942c4503040500300208075620854558020b80111000c0c455916110301100c0700e0481a0740240c01a002000700c4140014001048181188103140005094403442141e482c0b000c402c4e00210000b82c026041503c50b4540096440d0150003c0c020440c5054540f038000789c1d41c2c1c815480b40120720040003141e181809030541c440c44440e5000102921162 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 16895375 1250 16894125 16894127
    0x40b030a0b0705041e03050c06071e06020408010b010503310f030210061403070303031802060304060605010e010203040f18060e09010f230406090f08120a0f14040308090c040606 78
    0x9001401000d2011488180c045400201c5c85075040c101c81d0808054090001030b2400e02450380d0200318160394980d604020f00344c0b82d911b601790060a69001e54001a01c0e181400342103400c0d03c00340350304281041814414440f02440f07001000c841054000004044014100d2042c007400401a602030100c070b070100342c0d14090640214000d001c00c403d00008001c190344540400c1000310b041c1e02c0740c0340c142c0d2000600348000380c0071ba4448072140040174003030295509940c0c0010029402200d00b1506a915890100301c0d958109480184c0030809001840c101170070009190015080c034401d2038404035500203041d41c3e002d07031a401400900720a0101c9451850140d071031070b028094040c01d0b4841c69140140074100b020102019212014050901c560741e5191a2252802390030300080554441c4440d44444d0001000080208546c000e440b03154503191500c114003000311158928900320081c207002084c284240c00e04070841d1720960606202c80c007520b650454518208031503030b07490703001494540302051807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 16896625 1250 16895375 16895377
    0x305031201080105070504080a1119030f05010605120303040f02060d06030605070f0206090d050d0e06100f120201050703051803010e030909010801110f070f020a0b03040605060102010501060509040b030a0b0705 92
    0xb864003280240610388565400b02e500344980d10882003503410072508000090b101484102111030018803403006202d0191001d011103800368811980d00c29000701040421600380a100000c210407901d991171100607801054980c440140000c04ca2002e007102c40742150f850509403440100e01c0f030010800ba0381c0b6480c100e8002c02d01980c020340400c81c030361240c840f091310020715544280300e02d40c0941481d441000d02552241c00c19080d40410301d23221a203140d0514000c0210700c2c4221001e0840d000c2076442c1c0039142c0408003860300020f1f000b00000c1c00900240c0d8010080380c44843c0d142c504076546800c03001055840c1c03100d070408160b065080503040f0a0101000005c0c00c0020422500c040c010b076620700e0754500302ca01202d44802d803a041030003810003511512015204580c011a021408030526600142030b0410304c1e040246001c00c040300340824450039100c1c85a002c0c4083c00204080d504240018140380200402103214030345441c00001681c4040c0034181410380d1010715503e142c00d00140107419 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 16897875 1250 16896625 16896629
    0x190605010e09010903091a1605070e010b1201122301050714030609060108060d0b0c030a0f0b09040803060d05030415080609010605091504050d0c0807090605130207020102070305031201 81
    0x11070390440c000b01d0081c2c1d2062140c6103500c0d0b0315441d003c64151820302c41399000c80c400009486045014000324101c642c0c4c5600301041c00b031140015140c2d160901d030255482d500180c0210140000c24040b41155541000c4140e0550f008429200d000d82164908401c0c548100c0000b030001140140f00e02d00d0140f0150040c6000b036203c0d0710745800b40007205500e03007001c2c0400c8a420b40c0c09803d44011070751b01d502840d012604881e001d0241c048041c942e0b1540510140f0a03180c01011007800820480448040d2041c90310004941405100030b82c42c03200012400c0302c0c09171014000540000100300d1035900d542a088040381d0000541e40c87d00e030303a079018900c1603d0030480c503001300e144c24001811518100030001d050b540540c070b81a040103000020f00100c041c00010348071090790f04000124842d50b032030000e03010f802d11900b8146002802c19828030b06101c178076884400c4280c14a6424099507231440c041d0400307021040401031725003c117400100d142c418251303c01340c068080050150070494010b110181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 16899125 1250 16897875 16897889
    0x20a09060909020c030d0504140303040f0308101d0a02040807090603020414011206050901020405120a02010f0e010c0201050c030d020a090807061e120e070f140f030c01050c19060501 80
    0x551980c2e54031000680c032400d1040221500100180182140c1684c8410b0300a4040c0200c00001c4922141480c07035540280c0c0c003500c100c01403e07907140403d03611210281d845035441c032500044514060b1f0701540c11040c1c919080526849a000401ba1031450303050b24020540c610031207c2c490ba9901070207005020501059000310b00304118248005100d205440c120f0f04c0300400d01400e803074280c5440b80201000b0b08040c15a54080200103a00e541d10586c034600640808040d2405011034030014009608211002007480751134040300105070780024600e0071003502828055606c102180d181070452281454010390280302040022100c0e612070300307041c26244040101d8071801d45a11003606c0c01c0041002c111620303840c20140c0c00c80d05200307030805100c69103406804500489906880343c1001030f650400f02a545420b8410401c110f103004407010b81107015281c0f2450344000101117078440c000b502c2c0e101e050010014544104503401c201009040c00c0700c84500401a0b414548000078000c00e1040344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 16900375 1250 16899125 16899137
    0x40c031a060405010e1509060f04090509061006050a030608010518072304090206070203060405010c031a0a090504030912050307060b0609012a0803040c030308070903051b040f020a0906 81
    0x2054900340307441141d05446050b1103c105460544013044020140100b0103005002c2c2030041d60f540f500c4180160150000c96503041e500d0b2070170000c0e404102c503401031406ca0540c0c00a01400740c1c0c2c0c5001100d16055400614203191b0325024840f06801520b04e0340e1001e100c5629003020000c100c2c202e50380ac85c40860198081c4c0c1c0000750388450b071550342e4a110481d244a4003985215158514060740408007240c070160240e030404000d0f1300041d041c203408807800c5da01079444412030b450f4030350b16104098490465074150040c0c4c540c80800300c0c14440d01c900982e036125584001040905000300c07600002404990985002c800032450040e840741c110300d20450b20f081c1003000403216403404c0000c2c0c0e0f0160006a4400144c010310003062210758529001032144010841c03030b0440420165002180b0503805000304e2003106185207002010b200009005d001007290311a01070002540c04100440c0f80007014801003e03210324840000c0007002d170200d1803a001c0b40300040490400d0b80003940701080300c100d92140703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 16901625 1250 16900375 16900421
    0x90302060708070f05030a0b040c020705010e040c080109020c010617070305100e06070315080a0c14030102070201050d0209030c060703030e010506010e030718061d091903050304030309050c040c03 86
    0xa8aa40800b500c00d00c002c280302d003801d1802c4c14428400b0310360240749a80702180003000d1401080c202c4141320314840043e046414184415604107801c489602d5050f1000c11841e030074548001e00440f41806071041140c0c0004031665440e03025081107000d042094656501c0b01a03444500d5603c14680c0b1044602c0c0c09251038a519074401c9108042e041d04408000c0e1185035103528040380108000c1901072603181c030200d400301e83e01e001005100702d0b041c40351050880d40e03030406c040c0c0341c0402c11640456200380c5c010041000180d82c020281e0780c01b60301c20358002d44c81d051030300f00080c01c0090404007190028804103800c428154160888454044204001c00c00754480000440302d150301003804503010791185104210321621030003000b084030000d100000300161a101c0e1682100d202d00075031003181c018032007840380210040c00b2203440540d1489080c245030025550142c80742c04000c1c0054141613031550600c05102040c000d44001403030040042044801d600005402446c400082c0c1c00c2da15008000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 16902875 1250 16901625 16901627
    0x60102010501060801031407031e050709020309030403030c05010e03120a0f06031e06020409020406090302130606170612060708091519020a02030d0f091203051603020a020309090108010903020607 86
    0x140e9040e9240360782c0701340603a0700f1074803000319254813101c03038605074170407420300102043c2812210329040e0860b005c100b41440c000e041a619107803a0350440e28420348104140440500004219022664181400312078a4a02d062050040280c00d91940070b901002500e199100c504003c003034428019624104503082107085200115629800014820100b42010000090307400501d010658421000503140503118a104400c2c2d82080d070001c004104510350a100318982101d480078141d0039480304102080c03030b01000425843c18034a44610121010380480c025884004400a600c0034840c200c40c1d66040c020001090f541084600f07104a0003a810102c020384c2d29480024001d4524003d02079860040034505002940500f0440040d803004011101c000c03510760080381004c000c295000540e0315003905049820f60690300310308007050b140804100a25114265000001525240040c0c540500d64001ea2551149003080c0e5402114440001242c80d0305412410000f48a42d098400603250110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 16904125 1250 16902875 16902881
    0x1050402030d05090a23090c030906010603090609050a0c0f090902031c0c0b070c03020106060804021f05090a0f170102030c120c090d031206050109060f0309020402070507081506010201 81
    0x100207525400c5000d10b400c0c140e12440141c04510b00092850290780d40d5170b50407648182c200d0207003c260504041c00c03207109207070080003503070302541134a2030518500d0030014142c0c031003105000b19018156100005418012980d100c0b20085502a003141c04124243c100048010860b10070340d0030070024040003080843c014052521000d5000d00100b03010301c508900c035100d10f006981c2c00710802032640801800306045480450094034541c40d4203000c1c00c8207043c002c1c00d40300030360440e8040c01840f2007401300580740c0800d0710144203581d003009041031400d40701c11122403144280303240e404415454040382e01040030501c541161008103083e90480c6088034600e0a0340002c4030000c0c3e9640d020300c4405503c0d1000c40c00203900441044450707140c40365030070000b5403030742c1020f10540c002007046000c504003131428861030014000c00d08001e40d03418a0004010300407290080c1c9007081644a41d030307040c215111034064804c13141c0e1000070b40720819150341130955101c0722099003462080b02e0388007065413540188 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 16905375 1250 16904125 16904131
    0x1203090a03060f0f020f070c1d04080c0f01020301080d0e03070308220305010f0b0102010506010809060109181a19020903060711030d0501091a04060803030117070e0103060213080105 80
    0x180c804140e441c59511900e0081902c124450701c800d0704c61107a400c0c40c4400e071008110030241d0750403160321140a400c2402c1d420800c0c1d0403102480a48002c8124501000003801d9841341c0d12500c541d81d2034040004090412001e0b80031200c0c1303503001000200320f004000c0b840381c00d540c0c641e0341d60001000e0000c08156481c120740c0b00c0942816801c00032032000401806a1016a801c171200c0014020343c0d0f65203860841d091700b5000404640c0d04c0100381d8940d070707080c040c280d0016400d1038070002c2803c0082d01d5540340d00044c850078600e00c0d91007141451140b040401d102080f0340208107854a060b819440ca04805401c50760f0205103843c003121000c0d0b414880c400d88040b44000740007000680c0e81d200082e954038420904c4040a40700512900c0c00c200e015010300c50281c00840f40206a0010030501ca801004d52115443e110360300b40a014807000344004252411194100c01d4006020f02c20300000d428070500d9000440c3c00115000080240311141e0010482481001217a40a0540da062440d08a940035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 16906481 1106 16905375 16905379
    0x803180405010503010c0206150a05120102120105030a05030403020904080706020c0a0b0109021c0518030c0d0e01031107030f031b03050108060702190b07140f09120309 74
    0x41d02030309005040a5000780128500408040e4941d580140396a00c0980301c2101c0c103015583d110150342c0100303806030040540d0868845801e010398044146560000d107124000116801c0000b10700c40d0042d001005103050506550801030a85d801801c00c2e200d6080170f01c503d0300481d856100070034003440e5201c010702e00c1c050341e45050201020143e00080c4a00c1c41480170542c118412420806c6210598200040c41d50301d000e241080c01c1e50640200146103c0451500e1008000140c3d004043c100d5445071814410420011000e8030b15260088079910814022880041e0059141c005040d03c64100450075a02c541d6a0380803002c0080a0540025101c00c01000310368000d101c159041071607840035064280f41c20800b642c584260540007450844090005a0003500c00c50354603135050010248199211054400006a60440b00c06070380304094603411000024000000c5604840300 = true := by decide +kernel

theorem cover : BRFrame.Cov 16726625 16906481 := by
  have h0 := BRFrame.cov_init 16726625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16726625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 16726625 ≤ n) (h2 : n < 16906481) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
