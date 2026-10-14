-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0538
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:19:40.10679+00:00
-- url     : https://prove2.me/submissions/00804794-924a-480d-b46c-a43e299e7e03

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 96582734 ≤ n < 96762590 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 96583984 1250 96582734 96582737
    0x60f1b04210201020109061805010b030307020604210f1a060102070e01090b0f0a0603020910030c020c151c1e1104050111030c030307050909070206040f03080901020c061005090f0106 80
    0x41c032200d21080091086030105910500c00898403070300c2501c507101035602d21000700c000008288109030400000740708800d88d003030082d0003441c1001c2194000607003500a43c45004004008214280310003c51501d07085856035100c42600100c0526040100c400d0030105428490b050b02d01d004038031903600009d6407001712030a40340c15150a038200404040a0001541e500d5004500c40000407040e94803000c0f100050103540da0016250f1911404010401620b070240400f03141c074040307414407096070214003440504401d941302190040204002d480c80c0c81903040c00409843c0b2103500c2e5005030030342c1e000140140d10140b0002309008017000c01c50100d81c803d205110340f000081004000c0b40d400b4a000c03c510210b44004d80e81065a4055021b041d43d000f1102d0000013100004d82d8452803805c40c1e030322034104400d480100b10b2850160358a0099140c800c40150038011140005521400250100c40506a070304042d01c19906250304000294506402114810b94000b40001c42c060203400d1001d04842c683d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 96585234 1250 96583984 96584009
    0xc0e031c020a0206040b0a020706080f010911092805060c10090507030b040302070612143d0e070206072111030117010c030606020d20060f1b04 63
    0x10385151400000c0000100d006502804500d800540d640c1400f50009020b890340d82661070f201008001d003040020b0300101c3c1441b4401090102100701004400d0554110290010b80c1c0926041074040901030a100305030300c03518607070145c01d00d80e0f422602c0045c144440101e015809840d141000013a0007174020702503465010b2290300b1103101032500f02c140024080c0c010348024a882e61152100c0004c00c40d4141c0c0941d00654007048100d0340034850b900480c031b0000c01004540030300810100141e0014100e000c10100009840d440308412200c401c1e89a200742144050b0f440d00c0312103131314880f0694803601c403c012554002a500c2400460543d215180e02da4503c01c00c0d06003010302c5504d4104000008a5040c2d4a01c5000f0800e8a07000055002c1d145a0701c1004000d00e42d01183d50a44908122040c101810154101300c9a0b800246424403420306081c1a200015001c4a100f10141d2144840c0a24070a8174148032501090001480c00f03543d0300e44030700f60b011030742c4d03504240035100360301c03030300000001c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 96586484 1250 96585234 96585253
    0xc010206072a050307030206010e01140a0608060109180b04050903191107090f0e0d09050105030c0d020f03070507140615040903020c04050c0405011b0f0b060310050c0306040c0e03 79
    0x501c1196140b0981002c090102030042c0c07649459604100b40490140e031001c0014480c0d8004004140e006082c512100907001c203a100200d8011041c5105800030f00c031400d00812016801950480c01515000f90411900c024002c0ea000180c00711123460313401a4070b0000400e8a000022080b80d00d1204946414454641d010204035112410842581c5613405444c00c041001c00042c0200e1080010005002c5130441ea4056482e04009a00518800b8049260740c2001566005400d4a5001301c00504403500c0c0d11000c80310101900c00c42c21341034080c000010400c1f007030a0b005000303400194001d0308411000d08100e07002507500e03403050303504071a4018000505400780c9800d41080f200544a44192145080440003203421f881c41903c0c01400c10901107801d00255900c01d4400582e424a0f2402211181c00c0391a80c0b034003031410940241c0725140400005000c1d4804020781012112802030810082ca44907440d07058542050340d180d48507038180503002c0c00071807044d6400482288010b010f401e5810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 96587734 1250 96586484 96586517
    0x10f081303050c19030305010501092c1801020706090c0503150412030b030a0b0103030f051e0703050c0a03090305010b010305040b0f061f02030408060106210507210902030c01020607 80
    0x802c11090a0118407413441c0c090400300d92152003c500340d100b61808911941400000f400741040b50708010b101d0840c0c0380c0d201c5103408503941a007064031005881c020003a00c0b0400b00b000450a0961380c000e196000007120340401072254803510300070380603001e04c07804203856104064503018002141c001c20b03003000c0007040108110f00580c200c058402d0800140da4031a14000c00c0c10100020070594800c0400c4004005054000e03103183c911500c2c5240080c50311505000310744182034640c102041c001d00100e507000030035000e0740890748080750340412074910007007521b00280280a80d02040320039500702902c0740795075402400384a002e00e82c4080d403a40c02e41da440e03d03105032444001708030b02c0d802085540401c130300401d8011008041071465000d550f403035080299a80c60701d241a4040310070403004420315542454070fa100c180301e244c0c1103130022503079855860b0110703030407041444100742d40c1e407000020b44880b400e240e21610042c0d200b9000d885603e54402e0041ea1a080300f1500b0b8004506496540100720 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 96588984 1250 96587734 96587737
    0x303020a08030606070c03060902100201020c1209060c0712050c030106121401062705060d0803040305030717100303020d0824040908070c0e15010207150e130506010f08130305 77
    0x128003410941c2803d809444030300d03484080742e009984c902e551760300d09c0302941890101020181810b0000b075141099100c0b48507a940d0850b56900e42c0c0210101d600d108558410b0100c41021b4a007038201d50760315423240705913030055900c0c240c04c4420348103d42030b03020182010701601045a0020706100e80700c0e403e540f2000309100c0e0100c4802240c0d5600d00002c02d40c0c2c00340d41c00c1c0c1c3ca110740705000208400200f02c0b607418111100a055944900e030208802d6001840a1040b654400e915203001600d0345c1b40e1300300649012900d41c01942c0810802000c016025440304062070480c1d000358210f44405c10207520a680501064034640c04809242b0071010f007903d80d0f40909203884101820005070b0385c1564032404420b0b003107680d0454000c5900c880411800600a14850b000318240780c0c2d800c1c8500c803101c0080c0d61240070707100706c448100d41d1164801c000c60203000081d00c9094040c01c00f9007200302004146c0010b140c2155114082a40b82c050032400c1031052080a2141d40825110b0241c1992620181d03410b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 96590234 1250 96588984 96588991
    0x9090509100509060106110105040f02061605070803031b0c0703030e01090801020304110a080312070c060b0d03020a05010c050c0a060207080f0c060106030b0d02030312041e030e04060b040303020a0803 88
    0x6114196000381c10780c0e454810184120b51a101800d42541041401468044200203051060f810001480080341c0c1280342c8002159040b0342840c1e80740c1150803031502040d40550090041d0094880001d001c0102200452041c8000c400c0d0000601600907200600c0c0200089001281e12064080c00000c0c020f60300403000003014141841c043c2e9031202c1c11420781e4022241200c104a104003070070814101554800c0103008050080d50800d043e154801241002c000d1816003013103400b609101c14802d44c0e80c0000300980d00540031013800c01e04d90402070366070001c814040b41c60358608070b01d20881d43c1c480c5054640049071070b0003170700c10044640c4030782010b50400101034500300010000c514030b020f00c40c0000c0c0400328800000c0c11040d8503000700030301103480c46201c10b801076400cec414a80061764007008a40704044a500d000e8050f0312242402d1400004441d114100301c203130f070300c140014140c10110340c90320950215002d00c1100c0e150301003007a150069120080c0940e101503460000624284069640f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 96591484 1250 96590234 96590251
    0x80708040c09151401030903020a29090607081005130515030d0f020c091b0307020c030d0c0203190302060f07020327010f03061a07020607080304060510080a03090905 73
    0x42294480c0c1a180440305008010344070004409004c01502c07280c02c0501103010300034241001154200d0320040c0d101c00700c0e0440141021101084401d95011140c81200369443c83d071072030400c03840e1030400f140d9144001c0c0c6066010800c1d520020b00780107204125502529805071603d64111340650a04018040241150b4038914104030002c242e0b0b102041b03040c5062100342c0d40c004503140315000103400c12a000d51028000c08045081004500101c0310314403800c0e0301c3c00f45013a540d688105c0d049041c210040708c907035818015a02c7c0030f001d855006120f03040e07540c0202e0580d000fa01d0440c00400905c1c1003244000c4c00b5802404c005250404e08088003a0700000381d0040da450700010309807100c4031004082d1451421b040d4000204281c0d6444501d400e025456403e08104007800c241150600d01240d1480c41000d90002132800110349802003500e80c11607000352103a85030304140c500000980703001c4a10440c1c0340d860200015241e240002c100c1810340d05030f01c1c0d4124003400d0485075405420300a00550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 96592734 1250 96591484 96591503
    0x3020a0c020301110a18080a1101050d0f05010f06021b01030209011701090f0f020903100509010204050612010504181a060a0e04060c0306060e06030114040b060406020a0308060d0308070804 83
    0x942c50078080c0040f0301803c00889a640c03107040700041d1841d680000031702e21840000c00700380078160000a19803802504100310803a040d0803800121517038895210b003101071500f0056099103007850fa4200780d050701e00a038440750529444100803a55180040e039440c5841c24000100400c5500a5005103a0180103152501d801c076240b10340e031455402d0a81c0b02415807944c13824810350481c582d210b0542e02e0642e0400540c9414246000256100c2485034138007250744e601d4005c55007041c402d40c12070700248005030666866001c044040041d860007489094091402e00d0a144118000c1f00c02c2c3c040c01d140e000f8072440319008001e01c0c2405425005001035009810700101007002e10703600c480c95100e14801c00002c01d03064188040141580c03c0c3e42c0c0314800303003c12700e00407043c07659a1384142c90648020328402d503004c250180005001c0d2002c01c84154000b03030005030104640398085501f840145c065150704010f920340c0700500555080008000d400102c070307074001c03903001c522404406401070302030070040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 96593984 1250 96592734 96592757
    0x102010c0e0a211e1b03051005071107080a050d0306050603010306050709030f300909020c0717070911030606090607050a0203010204090c090b0c070506070606080a060204031a061003020a 82
    0x51401ca9091542035a1a50350344401000b04500e00c0c00203113145e1204102c01400d0340c03456650031707500c02044054000c01a2074100003840c00d40b090452015202d08031044491041e907a6115a44030046048141c601c1c0c0181c0c25840030690203070084500b140e0000d0076940c0b944c1c1ca50740f41d002c0100005880d0000700222042c1c00000719a03981988441140107520a101c509a1075a074241078026000001070720f1001b00301030a9040d030f040b90300e0038200c0c0c56615000d6910f02c2d0081040e41011196005010240c1c0c16450f200104180000d408c0d0a8542084003042445d01480b0a90003500040b24510b40c014820801020302c1c3c14070001810599101d03400b250001400c1d42d0000f401e98009030469140207503a0325031400c2130341c1e0000301e190051008090172850051a14510b585514030303030113858002c8100180c800c0410856070b00030740052500b40c003560080700583c50410065801031009440602402d4000514022143d11042c01050001c2c400204800e041c1d00c10f03000703500041c020030706020790715084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 96595234 1250 96593984 96593993
    0xb0c1e03160f0b0a0b041a09060d050f060c070506090705030c010507081b0c0a14030d0e150406020d030b060a211d0303010503010c020706020a110607051b0102010c0e0a21 75
    0x2107802404441c02c0816a051205d00f88000c40b02d407110340003404c15641c44400410380701c40d6115074101c0310507101d04410f02c4990901901c0d0042c8480c2d620710038030400080050094006001e88501480380e03082e0b460540361461441e959441d203025103941500b1581c1c02c07030281d60143c0c00406000344103003d080d0404e03540c0f40759820740041403241c00311a070b040014a07814a180144112002d022404542d652913075480703000c280e907002c19000340414081e0503222051740d9502c49400b4802401803000d119625a1944002500c83c19424a5200803078102801661079141501c155285184542d980d10448081a90300000c42c004101c2c1740038040340d80d4030300085040340708407180301207040600043d40e076545070000b803600b1102c08651203c1107411641d024001030340c0c04100b004203d6080f00760345040008400c0061071520902100600a11407a1044010700780c021000440201d400d800030804040c0801041e540d07400c201c0c001660203242031809021103000c5102c50724014083d5403e00011561a03540c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 96596484 1250 96595234 96595253
    0x70e0a0b010237110316080f120d0213080a080406030501060e01080a0515031911060f042c0106080702071a09010810120b150d0b0103020105090d0203070b0c1e03160f 73
    0x6c0800010745100c248081c4004020541d810350442d0002d04024180c0d00d101082400f03480c01106800e900051104800003242c0d8508014014040c152010210185011a480e03806031144201084c20b01000050761801029000211401030b1139100d1103a0780d042c0c9000092400614042d0b80d485684401c00460304c0c100714070710309504007250540b100d244074205140380c0c800381c0700c0d120702c152406c0010302c0140e020a0103841c00c85100c07142540d0991015004188a005882c010541c0c0c1b140c4c032800000c50aa2010519000349420740988507002d499240388000c2004c10010214604c2c02001241101d504c500d0b4081c1e448000c06105400e1580c4035501031140c140072400954024491703000b03200d092441030611032191841160801080340ea00c1d5105c01c10098140301c0a81400800701d030686440c0c44a201c0b0400c0340741e0040569a0701e6403641400c20081c3c001d642d5180461160355485010a00c43c104000c455144540081d4200084401c1c0540c0416400504490b12100d803d1b180c2c001079031450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 96597734 1250 96596484 96596503
    0x302090a0e010b0a110102030114060c0a0b130201081303020606010f0504091506020f010b0d2409050f010f0212060f0102160e19020327070e0a0b0102371103 69
    0x81103250386002c4040005c10404a41400c010564070400040022040301e46407030b042d6120a07036a098640d012071610b203041c074101c460007070402c0310070304c0410220780c2c9241000395a03a4400d032141c020a4440000d0203950400300c800044c0560b1021000c98015801889201600303030040c80e1207841c0544130006103040d11040c0800702a05d00345004d092119035018088005000f80d4503008014010200c000070710404d640400c0034090320080400e40d04149580306000b2040c444c100005d0184c1c521381c1c0b414030380e04c514000072403074654038242ca82184140e8500071034402841008040350f1903117074901040380c03c00c080502e2038154494a8107170483c49011b005010003c2c0000546800c00f450001d5614003001a50718076402c0c12881002040b0100746008101e1800401007000460a038541c0c2c803500e8035040c1950402030360504100d08100b8680d442d40c0000e0803001c0c00b0b1b401d03100210600300203003010b42e507803405204008104000f40240143e0429100c80342501404000e41c003441d81401083c00c10150380d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 96598984 1250 96597734 96597749
    0xa021318020703022401260d1d0103090503090f0609090106030c0e150a1404080f031e07050714030109061805061b0d09050304090c0801030b010803070807030302090a0e01 75
    0x301d0b000050503018066240c078950401441c103110383e2540103600d0b207034805010303009400c1040300c01c000e64203090ba01c03445d1214035400b04860800c0701012015240984014020179446403082650400d03501c00e0041181c1190700c407001b141081044c8007046140c08120241070340056041c0513403086603980d00145402080c0a440000e40076201d0172008146d1003018840d2802a0000036a035442c6030012003c4170180101841d01c100fa20804941d070000034070980c0c2c484c00003481241904800000040014081035141400010348410124001115400b0b140341c00307481508800740c20007506c3c4110041040c0a20014000182085c883e600c40301150900c02054205480c0842c0741d2041280c104800e90f0001140302d090340e03030308c441301c10301d00701522030030002d2031034070341c5804000007000310400658025020322001800750142c0d00400410100d003d1109940105c1010f000040203000401101c20243e0080b400300d02e008a1070720140d01035408402c0c3e8030780011000100182070080075480d03d0203001c24 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 96600234 1250 96598984 96598987
    0xf0212040b01080118020f010903060f0204170c0906010503070905040501030b090607020106050f0d0326071214070c020f12010213050103060e01060309080f0708070b09150a02131802 80
    0x307814140c0308048160054403050389014006244542e151419000c601e81c1120303c1d007410085800100c0c0c0c007400fa50300040aa40c18a801a00400060b07005401580d818585e444007810812409607911101076560b5504044100302041d82540f01d0320040d03074061800d0410b03044503aa10401710b02140e0090b0310607a01c1c2d24aa0080c454150703401d01040c0e401c01d11a10091142c1d0b81400d0004018902000c00d162040003d41c095004060060a51801d4546010f01c5c010900140f50b01030240d4101c08c50742900040c0744603c00e85150703e4648550b1080070b41001001e95030b035035400006d4404074000c031001e036030000c000c58040d82c25581d601004800403291100150300c9207002d0000e11152035080d04054103160030010207204071a1401c1c41c0504441c024500420164580d00b090710403441030811640e00604001801b40900144100501c90103204501c4404240c0e16501d4032921050010011581c0c1c88440c004640c0c03000c0701c0e03005012000c15003028190340c80c0e80e4a4060a03240b0206602840b0140c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 96601484 1250 96600234 96600241
    0x819033e0c0f0d0207030c0e04050c0405130f0f050606060a020705040902040b19090510050f040b1206040b09150603030712050405060d20030903030c25150c140403030c060f0212 78
    0x187c4580c0000500140b2020141c5080c50380e5415201c41078000e00c54041c81d40d60300001c40c18003805802c5103009801c101d11040e201518140324910003000310094a50784104004a45070341407a4086512003450f075400fa094460401040001410494400f1380c0c2c01511580d158645a8170080100840d10344600c00035081440c0c14211020780d03c0041a03040e5040c5940e000304016201c40741c6c0700c0302c404400c4034006080100e50f4001491a0b621100001142c85020104407c008030360709032502503081c07101150004450a1207218030100b003203491580582003403026000203140c00840c90300401a504003039040a4a0704003183c1c01e504403c0e4811615600c420003407a0b91542822900e600c40ca6150502c0e00d5880c1c00c507050790f9280300c01380004422010020f018008514194501c08101070009081c4e164200305080854803d085402d84890701880c01d00d00c80c8101c0c1c040c5050304208031140d20010b0a05203551003e5410b541c03a520b06889282d1200140613100e002c901c014441c000d888192040c440c02d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 96602734 1250 96601484 96601493
    0x209090702071503050402061204050d020f01150303081b133003080a06050402040608070f0804020f100e12030c060f0f0f040819033e0c0f0d020703 65
    0x10406010001076402214090015061500300c0c20940c1e40c480c140482c2136111840415014420010342104040200d010b00c805c00a000c103d80c1c0b55540c20345c0c201d480c0740203001c01282c02c80b4018a40c180c03104161010401c0001d006041300b5030f120100628800358441800804035032940419240f8500303068410b410b0020090711840901000e28161814848a409217041d10354010252809428001c0540001c0d4005c5100d030009c0303025244c013503c03e44d10340e070341c54001600307074803007501e1440100d449902d51321403140c170900a551041e90000d008185000c00c501c18850036488106184041105007110429152a09190310481501320401036540701c840001e00c6082501c081c0442038001b2241d0140650142c0745005d00750010034403051501c40b03403224500841c0c0c511402504502d04455a0921464550584c1c08800c0842045009040803001096082c6d4182c1d0080c80902d07020008400740104486c844001d42014000c0c03401301e07007110a02106440c588031a10100b00010f0344010418070400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 96603984 1250 96602734 96602749
    0x20a0b09060115031a06090a120803060103060905070c0605130b011202030706080705030106050f043204060602060a0f1806060f060503062107050604090203011d040803010311060f030a0209 83
    0x994500d4101700200c1c0854541c4d054103101300b1702c03e00c28000401d4401e51991180c080c50020620b4800344903000c04940741c40500e80d0000c40c6d0a90120b271410400061103505401920300c6040541c0d5120b446414680e241801000e014140100c200c0003890702d030340083d07454407009000e4544011401c1c2e5011181c8109440c1c01d107c0c0e01300b8410008807009000210b41c200c025a41980c64a00380651101000030255945000c0c80e400b0ba40d15480c407040f64002080041d440c0c901031064000302000e81004d810611007034498074482e150050380a20009600100f255004150903005040b022406280e0310b90204006c024070481592804da0340c0c04100640384900d503071348004001d41d00305a802e42c60083e0005003208010003060070080b01c0040901004481407024501070200100f0b0280c603a515100ca20000790001d00a0000d80740345c18814102c02d03190400e989102c0d60f402500149140e08542e0380c500a041000109500803009100d00071001408070701561003400390310701c01030700d42c4000420002c81 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 96605234 1250 96603984 96604019
    0x50408160803010e090109020a030f02060f0a03020d1103090a0201050903030d0c1d030138040501090b040509010b090105060d060e070804021008060105040b1303020a030b0105192301020a0b090601 86
    0x1581c90147e1003801601c0300590501126084074501c0100c607440c0c001310fa80c2d84a01c1649034017180d00010340200042d0142d029110302011028200802216200c00c0c0c0481c1c4015640e40e5003d42c8401d40080041d8414402084403003000b5050b2428400280304030741c20f540710343c001400422240c0c9011980c40c200030841811045046000303100303400001c5a2a52079542000c6030305d0503541300c41450318051802c50010800c002004d00104003960392050290300620301d02c044644100d0500022034101107050158041030a4000c0c4181040d9180ca810454940d00600e1481012340d120080010b841c0050004140704400a4131040ca25180c58410041141b00011200c0c0511030350b00300344006a40c1c00b41c142c5003910501481255a218215001102c8070b28942c4001e610500e15100403041040f000407882c1250015202c00071a40708000d5604000051409400701e01030720070b1004004420b152001045609060041d92100302c80380d01e0300119107800715400800d503808440100181f46107000c40001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 96606484 1250 96605234 96605251
    0x4020d020424050307080601031404030806030d020f1e07030b0406060504050a1404080a02010b060403050a060c0c030c03030207060908220b090102031207090806040c0e01060509090a050408160803010e 88
    0x1808100c4802c041d02a010180c803400c100b1241c14001806a402940072900700462015042e6039491305203002003d070102190024082c2c01030070070805200b40005524420400203801900903030405c58140c003916410f40180802030300c2070a800001281170525014000c40c001c40c0e011038010700f00003e00045e20805405901420314002c44844003154940e49542c005d9841001c855684034a560100e0161284101d241e40c000400140003040090010b010300090380700ba0002e01881040172020346002d051400d028000c50304540075840041c0c440d07801032080602c550b07400510320140380c03a42d04864100340310728082e514401c502d18882094050841d80100050000c0d07504d0822480b000035280d0044625109680281a02085106020340007800141400c0401c5881910303190409002020807882005501003806001190f180c0c402d07400c03079214500290280c9480e450314034440005000c020415102c4c0745061090003058019140d1404c9654010707451aa1a035043c08030a4010b048050841e0f403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 96607734 1250 96606484 96606539
    0xe0f0a0b060301060e010c0204151d13080715111c0b060a050d050c09040e030406030e070b120a0b0a1206061d0f0702030c011514030619090302030904020d0204 70
    0x103c415400000603520520a10302051f00c0c207000e2011902929400e00d12404848042801062401b00500300140c00394038598400b030aa11440101a0318080c00100a4542082001480041803c0c43c007101e005c42c81124000030303c141c907042e004440da0023525000180d46c0440c540c4480d008102e0250307500d2620101d42c2140741420a02d0090b10030310460020030000d58807000010f0920720b02c0300c1501c248030000f80081c00351201e09040151603900a00600010a143c10244594040006080e10907030782400a59458088406180c00f02b00e540200410380c030a40341c04041c50127840d0344403400c1c02000c10074200741c07003d00c1c540303050810703101140c1044040c400320640e09a20411403920f100c2d0443c0c0c00e0300b461880d1b40c44101d001ca0031445078800300398030340d070130706070641c0900c0340c01175810084813031180d1000c14500d01e12040540301c070000c0d15041002e540c8441103030981d04c0d1680c443c14003180b081c01240e1400303202c000454180d0f0400000205803580c04203080020103030035460750340d401c0352404651 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 96608984 1250 96607734 96607739
    0x114070906031a0406030623061e120f01020c0708061009020a02071a1902010203041214040909050f120f030f06010c06020721020a020108130305040e0f0a0b060301 72
    0x4203400150720901c8201a150b8a2101d03500040054014003103401801c240700340381d124280b81002c0c10341405003080d0740d180c00c0440d509450103a00502d0180ca8002d1400340301c4803122006603801c11a020b00e8942c4500580210400c516007040241c404041501c00035031208a20380c103050404e84158031800c001c2c0c03c10320030010000d41210b017003001c0c0c4109140050312820005402c0707240a035960480380024440c003c04501320b0890384003400194160080e9070380280c8088000b00d00341d0100b07580003003c1c8030001070404076407401526a002c40c04058409207003004d40d81c2701030794141c4203160800d85894000e180f050154800a010010340b00d103844030b40a2034001444001c044c20312000f01003d114104803c0030443e00da2007500d040403110380001040d034030b596031410801c928140d50b0603a80900300d1000035108555001061404409070144c594a07920754030b110301100804100300d4100e0800c1004c101c085a4030150086860203070300c0b00f03400d0141c01c0c87c00700c141f0350441e465950f540340314039400e1004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 96610234 1250 96608984 96608987
    0x30b0102100e03040b1620060304022e12060b0301050a03140109060608030901023007021507050a0c050114040902090d120507060605040203010501020c09190c0908011407 75
    0x280c5903854a0311074001901c202070500705003940602d400c900190a400076403a100c00c05013022002c02d0500820300c0a404640c0e0511940c8483c2c3d41824a80d0012400e00024000d4500401903003a07080c00650b030120611010342c80440c0c400b4181c0030610229460012525082481e4807490000d00204c8103032b5441c40d4100340005c3c280c0070035131000404010140008802200080d006079945a0340030304e050182a0300c4000c0503847c3d401280c074950043c0308d0411401c035600c1c1020f21131030f0b00c0907498181c401c0510341c0e601002d5543d0320407482a46c0081d462500030160b440c0c004010640c1c0350003480a0a928181072a003030100c1c0c842944010f0400100d1341c1040714030114a400c840c111050983c005035100e4018011400c0000300da1000340c20312a441d04402a0b00b81c000700280301061045004100c21915031082008900080c0141e03801a801200000010306029015541007400344003000710030107003001941c0c103590f40d042c013020004244e001e0800800d0070034004c0319810b10148521120703d1520403070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 96611484 1250 96610234 96610243
    0x6030e190201140c0f060a1b0c02011b1b081f05090303010608070e03120904240306020a0c0b07051c140c220e100501020706020c09060f030a06150501030b0102 70
    0x110160581001444c02007080c420003d28244908410507034504e40f0742940d4047c024500c800200c8071b20400d0009240f44644a078528528040c1e05842e115441f85421442c07074002290712404940c52807211204444548031100341038000c000903001004401800400c1c1076440aa80c0014a1200d0500e014069260004030560303064500c5403401544035134600100f00d802203070380256a034160064180030b2850483c1c603401400441030950341405480b05444e0041000c2007940958109611103000a00c0006d0058004280000701407801c1d4011802d1074a840010b81000d50b01c000114200140002c1002101400b800b501c00d0811020449102c00c214403100802d4010030042c40c1e8080081d044801c404012005046d9110040c203295955440b04a941d07031101c0305a0303003641551100c1070700203660742c400607441c81a5202d03540a06443d03040101401119a000303400240d021441a80c0904507460410040e28082c3c001c1c10003103924107102140e20345100060f00f1107030401d824001d103520640d80024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 96612734 1250 96611484 96611507
    0xc03050d05040312020d0c0219030903080904020c030408010603050c0414060108040213021303020a270507051c02031503070f0501050702060706090302150a0204180b03070e0106030e190201 83
    0x100d0101d455038492600301c494070344000d0400c210b5480490441003030180ca41c008146001150200c41e200b516603120003e58a1070000000c0001d0540e4078188000b07012140588010107004e40b0150600302c1c0c000340300f815a0000c0d00440070381da5440300d040040c0f03d000c01c034105662009a13130811541c1118881c2c00c44000c1d0061802d41484040c03408101151030300c0c1003030b00b086c2604e02421901e414600c4c44001e40c007412880164803c4900781004110000400511034060010100c0301c1e907002c0550000c00c0140000070210000c0c0b08083c030403142c901d90000140c4603200d0142000503643d28029030065400f40c00d90101600a034000b90007031142c030040e026204251002401c0207625032426100151051041803130042041e42006245030815400050b18000e2001d621401031090340d610200388224041c0b440307075510070606200c901200d44240c0c0e122010200d0085c0641c0e1116803500d6031150040800e91240c40080e503201405644401c0a00c1801d0074805680c403110070456598000900d030710703000c030f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 96613984 1250 96612734 96612757
    0x304080f03040f06020313061b050307260f07030f0b01081314010c02010209090a0b0306040206030702160609090b0a080303010e180f06150d030804030f030b060f09030d0c0305 77
    0x420240f06641d6503400c060f5034041070540d92807034441e404225005195904541c29420200c401c0445406014031203c00035840d070b03410703080d5562502c04840e03188681e401c2c40c0c1245000c12610b4020900201c400d0f1080c0590701d49000c040c2000c0c031000b022110054840710400d803414804100b6680d00828442d04030421112900c924420f606003e01c240d02022800b49140d841c0c116140040303070b0103401411490404503540c6446035140ba0340e250580d091101e501e54190481400200140f50940156170440540e20490b0031030407107c1030450200c42c0035080140490141081040039100c02d000341918020165081031000b46007000982d680d00041c00b032041c10f034500000103400380c18104988140a059402280c90768041a010681c8418054400242800d00080d8035a11401e001e103961101580c5555600501c0e525034030308440700c01d000b44030001019100d4011f405150b60b40c0c0040c0041c0d0700010314284c0e68407544000c16150030044004030741405035181c2210042a0803000352510525030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 96615234 1250 96613984 96613987
    0xa170c0604030f050c01020409091a04050303040b070c0807050a050c0d0c0504110c0304140414040803040228030302060610080907150e040204030b060a0504020306030d120603050601030b090c060304080f 89
    0x4110982d813a00a0f81900091580f002c60002031600403a001414124010a1107803035118200c20803d030500801c450180c4180e00400210b030006078503440c003079400402490240c8909845549003c0980d201e0344050700e0b00e512500c12141800b01c00d020300c1003082c90031a80c007101c401460362503500320b5110b803141c40d2049555002540c5000c080e44101c40c80003040750143c0740c7e0b881c1c940a8403481d0102034100f0314042d6181c0301c100c40c0c0420700001c4075401946c020312810304540e91a801c0140f03c8407080e4201e01000740b06201944891001080c40010f5442030f00540120700d418410301002c003400b00000420088582c0a1110801c0c0210740a01640c42c21308501c4004440014196203070f81d0294580d0780c01c144000780020510070181c04160040408031103000c04190355008000c103030700054a40b41d0f4150808102d8913405400b8030300d2071a040744c180d100071540c01d070341c0d44429091030026030003030b14126005800c109001909005019406000f15851070840c1801e0b21200c0c5140211114191035000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 96616484 1250 96615234 96615257
    0x6060405090c010c0f02060d050f010608090307030516060b04020f09120a0201080106050d0e192f0f030109050f0a05070909030c0303020703050903060a0e0f03120604200c0a170c060403 81
    0x42e24011558400d00d150421300040c2020803010ac8086001d21a40002130f100c0004a4425400801110700080d0141e680c1c600345808039031580b604207002401115015030304d250004803516240040e0220890308004141c840032500305024010814000d00350f00c6404c00e900801c0180e80028901d81540c03440e1030940d8440030303011400c000412040c0543d0050388a10200c01010304c10390440321038071500c180f44964000000407142010349001004014500305032903035103000750809100d1544100c10040020810301c50513201c15040034140003030480f1540200602200f40802004400e0050040c20740400c9409141c2d1402012034400c500c00908050300060781006051041007900c814480040c00d613801410184440300080c0001c142c00ca0644c00350050400c5143c40c04400c1e42d00c0a070b034135084110556103581c2008001d1012000c0714100781c10144040318000c00c0040a000d08a80800081c1900205400c100c04084101c2100b03c002000820407400d0b00c600218905400c5541030421640020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 96617734 1250 96616484 96616489
    0x6041e0c0f0509060301120311030414010f030509251a03010302010306050603040c0312050408010518010f27020a0810020904050a050103050a060b122529030702030403020d0506060405090c010c0f02 87
    0xc0344540d275142ea41c0b0000c2800318080080e41800d4100040036240c80d41102c207038880c02d0301683c40031205088a60440102d000c044140400c0f2180c044084603007140d000d82e150700309075103905401c2c01271702c507000d9004c0014411541c1611860f0082e0034219902400c42c5405c3c1e07a4501c40020385e000091a81d004d6030380300a5810300400c1564050002e4100a10040c034248034059480220440b0302ca90325030030518203200600040c03040101c4803900c141440c120030314580a2190350300115034101c0c0c002c01c1c560000245208284911810690074403005aa180604403c11050700c5000c0e007500c001925000041001400008a01074107aa0010b00400c00f111564006a04402500306110030f071b009464160120b054540600c0054942d444010100d20f0f888141001c401c03800300c00880d0b4881150001d01940c581c41c0405154081010300c11a40350a03143e5022071030f5008002021100c80d400841440b031a80f0300344c003507143d21081c0c0324000d241c0700c5c4560300000c0c0301424010024044c44814800c00d000d54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 96618984 1250 96617734 96617747
    0x40f08070f060c18080a02010813050d05040303020706030b09060d050c060d14130308060d05010b06040b04080d02060408041502010b0402030723070b0c0306041e0c0f05090603011203 80
    0x9030704a20040c120072038070304109001d00a05040c0c030000800e07141044964881000e102c00641355000003c1c0145042640156012400900b51616018944042c0400a40200032109260030b00341d4a0310b45492039071501070314050303698001c5010325040c03150f00d01c0c5549032911050760003942111620300c0c1101905156042000c40c0e0046500254001501c0c1813000941d003080c0503c0806405940e660f648090980b1200c015448008002404060105169160150b40c1d51b0613207008034000a40b03602a200042c1155000360b2250446610128003004130304000d1190742503415079030010b0b260614003992051542c5c411809010070004903140100e184030308c00d511400d003003040a0f00c11903072801e0403c405403070038500e40e4050110340b46802c035088540c20804290341a156105c1c6401000751141401c02085400007080c1c0d0b5006a5200210501894041d40e100b40039200150000b8440d40801c0004103000381c200c5040080c800708100d508a0b5407034100449046544151081c4c1411045281c1100c40b07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 96620234 1250 96618984 96618997
    0x5180903120a1404060b0a0e04020f09040305161a0703021e0a02030909010e06040b0d030816140d1a0402090d140102091306091808190e030f03030105090903070506040f08 75
    0x202810f250800080103150750101920700001c84100003186d40e40d0158044425084400940080319441c20303003843e0a180c007405401c40c0c46810002c0c00d000440108607d00c825413802a9403407038000c050882001000d0303407400c1e0024041d1900350724240709100c01303091442002c0240c45240800044460907a03109005031035a901c801401d16003039581d900c00c14540008180e0b8503e01c40c03450401d94170300c1481c03d491030108582d415290700c44a60b55075070142046981e03140001007840720398000184a051008010140d072840c0c84000240b1036144009150060480c00300f49003d1403040061146540d15890304a0405600c000083c0045014801c0c0c00e000e4040c400455401c03612003d120046043c01c2e40020041d101c0800d002c0203a280c030b400001034441000c8801a00c48082005481a54250704041d01034050341800d190110801c6000401e1410072070851440e003c1c4c00110042c802c601d01004059004610b0a00031414141c0d60740380d5540350344001d40010070080c940030800c81001040c1c410740701c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 96621484 1250 96620234 96620261
    0x10c11040e120403020301061710090606030c060206040302010b0306220501060801060b1b0604020906060a0e0303160309080d0801150e1809060609090714030c060c0705180903120a 79
    0x1203108809200d042c940090204034420350030603a010460300003032a44520500c0407000144445041c0c101c03207000400b200641900c0381922900e01101107141c0050700381c01001d1f10390081c4021300c0c1c6424000d003111b011b1860244242c02a0b014048403900480c95500d00705040c00090300d10304554600140140340c6a40069000d508201000580185c0c510107081d085100c00811001c10000b088999250314046800a600c100c040c0089480c40c101923014081e6000c3c45d0600ba880340360716500292450300701101104126841e005075800f010ba02c80d01180c010607291006091650301c0c20300107020400c0500030800c2408c440081282254840c281b6510400c4001d000491a02c0c405002096040c40c211091220792180e8400b02c0c0440c1804c82456201c0c800c0350019004250801c201d69010896610f00d05505200d00b01c40302c1c40c5070342c50700020290600d50000034201640b504040c8003084184265180d80200c8040030005207440c088100c07103400b40481c90103100343e9200080c11004100c611440107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 96622734 1250 96621484 96621493
    0x1090b0307050a0e07120c080403030b190306050115090305060601052107020105180a030c0201030b011215030605070c1119030803090d1d0a050f010c02100f120605010c11040e 77
    0x201a2203113075445002d0442d41e5603103403098842c240000140d40d040000800000e42070000600400c2c03095000c13000341c06000741030052032195540030b14810105508141d892541c1c507401004600010302140301c94a00b00d04120302348501d1501e1b1387e61100c000402113410f105000802c2d81d40c41250f40300c0c080440700c43c0c1c0c0e00d81c4454148510020b000300001c4801d072260040014607010a0000052079040a40e0305544607903c80c1d01a50045028128090702c41c0e050100001705240780000c9405106840048038021600143c034504006058a00c007601820503c5035005500021407010007070400220010b503030710200d0780300c0c0394580004003d1990000d0302c1c2c80004014000543c030080b41549918041e0358484100c1c101c10420000c594842e0700034168011040601040f240c01c0c001c5007040c0103441410030741b09a003000c3c1c0214001540f000241800210746141c2c0200b0981c00c11080065140300ea02c0030041c071810000042d207a1400e1400c00b03403118100381e8039442c0a40c0c4541160b07655400350400d0311b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 96623984 1250 96622734 96622739
    0xf120a020901021b10030f0b0a030f0501050604020708030c0711040c081501020c0105040e0612010603050a051203061021151406031e090c150706140103050601090b0307050a 76
    0x500070740120180c640180901c0061984901500d106a14032036001420071200d039405c41d00076401044091103d0300b000751030ba030b17518480355140710652000714080c006005a10b0301ca880e18601b1210001d1107544207034410701020000c94000d20581c0c0d80541d550803074075540d000c01d0900c0489514400b014a5015084c80900c40340c041d40440300c6400381b13401d08500c00440c40e41c02c005984482194841c64001402444104040d00f011036209410102c05080141d040d841c061700e00e4250b501c0e5402c01e99065215140d450304000080082c3c9600600c0c1101450541c00c08400103100401162000010000da0036038202e11584035404410302003982100400c640705000c0c91601c0908458412419030140c1c6011020036070601c001140c1c41a000c00d401d80030810016941620740ca040500b10101c540314034480c200283e102c58545801d19000d0110164980b0038a00c0c0640036140e882401010003440c0170010400500005030441c1582e01c48040466000d443c40701091820000350720290b44401343d401c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 96625234 1250 96623984 96624001
    0x706110f0705160303050f0a0c0c0305030a1202031005040207031205040b15010201050402090a0507021915051509010302150d06170c060c060103030804030c06050a050603010c09050d0204020f12 85
    0x207124091040d419148003052420884200f1040c030710000d804190208100314580b142000204440c046e241041c3e0710003205516040f501d81080e400031101603000040b4611202d810141d582543ca00d11b9401b0340ca146031040542c2c05010b0386110701e0340103076000f0548808050140c1e06070a118602c0c2c00d02040107281c00d00308541040c1054480d020317881d9a100b40c950741544180290b0b0300c00d50f0003400b1070015480d000c20840052030300070310500440c01034950102c0d05000010121034083d001c1e050610400088031645400c0324006410000310345180160076005880f0404010704582d0100e4410310101c40d890b0035507003a1700c0ba400d00f12a580c1e182c2400800c61446102c44248803030740c09800c8500c0c030018007051100c81e20410440300201d0f4040d500400c0001d10410342c256000c0c0c0b188c6000120b003c5160f6540c030a85009035a4114126140c00400216003000d100c2ca2011f00b09925010742820300e010081201c00d40c4c03117240030b0301031500000d802035030720b0f802c0c000c581a22401c002c082080f032810880 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 96626484 1250 96625234 96625237
    0x50d15050109060302070c050d0302070806040501050103020f09040f0312020d060303030501030b0a022b0f1b11060c0f030405030c06040c1a0906040e090c15040602150115050706110f 80
    0x10507021801c4030501094552103403007074a00e03070742c0d10144504005080400300000254400d50460452048150100304441c050180d6401580b0030000803d4a504500c1048082c850050f18075004010001c10000422100c0d40c00200c0d003074041c209401112611101d510282c031592440f030b5862400c0a000108143d8145d104a0480e806a5030790740c10764540c008003800340d1051081c1081c043c150050100c85068400810300880074266100040c031003e15a5440290b404140110001500b1014410f5031560480c0c0480740c51f86c0340c40c02810280c50000e0725410b6602914104440d9443d0220000d03040007410412142000d9a035800c842c05840c051a000c8907a00c0c4500920910741e0704800c1e04c140b201407101c10740301031490007400766041900f00364041107400001800c809107807041e40030070001c03a10307a40840c580081c1e440181030b94483c14008044c1c90b040d20800403a1110f1802c1c801044401a201c03200d02c0908001e107030403603845800f402d08a014081003095800e20003000612001d000c5080360 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 96627734 1250 96626484 96626489
    0x1e0f0f031905010b0402090f0111101508060f0c1e070c0305160b091c150504031d010c0c0b03042405040c12020306010302120f030c030d2d0507050d15 66
    0x4002d108503440103003032001b43d020b007540c01504400782c160300411640c090301d012849440084100c500c0c9412610700e15040e5840721040701c001c145c80709802d1000c4002801480d41c041e1050b8800d0142d800c060034103460604c03801540700d4016088191040107001c66038119010326400201b004100c0740c0b40d0400c02d03180d1008854004e01c205500d8400560f000ca02d500703885e58004020040500c0340011540e0154035440154115505c0c0515041c1007062500340c0720b241d0259010b07580300c401403521100705620128002c0c0e8102e040c4a8036140040008940e01d00d040c054a001007105038481d110340c03401140c42080c10802440c180c191001400c680a8140c0c0543e100724010200d0003800c03a582c1440c58042010408040c2d0035800c880c0042c4054104210001060901c4908881d0551024040740c2d003940c21152681003241c00c00110301d12441000c4c02940c0000f0b80a00920501905650001e1303510754103904008096900c0b00c000a007600d00403010340704007549035441400b480c440000d1500700c0e01c80a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 96628984 1250 96627734 96627743
    0x2032e0501020d0206090703080904090812061302040305030d02090f120105060109050a0e0a091b0b0d0b06031311041d0a03080a15030204020705030f0f070605061e0f0f0319 76
    0x1032243d21051403000400d540100181c802030642c0e603082d134030b80d40c1e0154071440c1903903000b5482e5900c240001e00403000130422190266021442c6052140820120442c20081c01c1000c90062006201041c40481221104408203c0050b030f83c542040104560542d060005030340140c0d40e50106800210640140344215800d9803040d4115450b4001c003c003641240c003403d0011403502c0005070151003d40d01c4050740600449601501103002c4e0507254410203950400b120700000424400311129007030080842c400c07411120a030451924041c4021401091140a401d9202d045074482e11a1516804000350020070441c0e06074280fa2072a11b542e8940305490101c0c0014040000600c00c61000d03c40e03a8820f2150f0802080903030715507001c000c065000103c0550f5a400100000300102071802b004010034002e8400c029202c81d084c2c1000012a040200b0841c007070740c40303004080b85002458205c1010124101d0b40c0e06106401103011600d02210300b82d285401d88200707101c29013084104065002c10a109 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 96630234 1250 96628984 96628993
    0x50c040305010b030303270703060614010e1c02010503041103010f0204080c0a05030607050705150f07020708010b0102070302041820030c0a05030d05070516230607030e0402032e050102 81
    0x1040b0034550349110485003404111f08006110050140c0f21030b0008000c1c0c008012210782549070303200c0008aa54552002943c0810f000e002559540c1000d4100da820000700c905110300b000d0100c03069103502000e08024100704e070000000f81044001e0700c24220f0800040c000700414510202d480d002580300c0d0041d10407030710400c03c40385a00d10308000c00a0a40f4070242c090304941d101d02c0c4050f07a4540210508a074180182c80e041008103001c00030052142c0d0780e00b025500c0d00d08082c8406420080d00d80c00c58241641041414a25a6000075010041b6603041d180001c0705c4668020702c3c080824a8000104640f0713030820300e07040e6100c0d07034851003020000842c1950180700300c0704108000c00310b0390311850390950880e8002d0914607004a000c0c00324180141c0c280c840414100c900c401c01840300d5004032586c02c584079103059500f40c42506401c0c2103036080c1e6130285031030710381d0310080d10b840d60002c1c0440c4580d80001c0020f15400188031641040d01c030602809100c455007400205451782107004642c018440c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 96631484 1250 96630234 96630251
    0x1060801060f0b1804050c0f030a06030b010806040b070c0201050705010911010818060a021308060403020d0306061704020d02030c1e100c2004060e090d02010506030f07180f050c04030501 82
    0x1025007198000c441d4131a214071440000c40c00d02015107401404111940c005000e50540690307184000c620071480540300290705d60a526010340214011381040210390300401c100030000380304008140e000211424058000010b51004072054405c400000f0610f50030001100c041000368400951200f0007600c64805c00d580702628100d503525664020801c2d035010002080340d143c0f8940c020084410712840800c1c08a4076a0318681c6003040c15a8101c0043e8002d24080103601d40c076206440190100389400203c004812264001c00407024102901c00e0001002103404c5650800c1807060842000e001080107070392036030032500c283d00384443c0315002c1c5460b0200d04201b40d210711035415a142e0310070413031a0500020345c81d60003510b958105168015903240380220711401800c035842e104480d110000c007091782d00c81030000d003504d001502450099002c14840784061001040350010364412041c0300c407080003041890740c00350203a07070b004072207041c03620707081c0f00203d85280c3c0180b09803030003540244a80c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 96632734 1250 96631484 96631499
    0x130e06030601060f12050c040510020322030c150216060302090a1725050904211805190509010807030201090602150a0911130b10050f03041101020304030501060801060f 74
    0x21350480e00500010318480c0080004080c039804603820084400d5a2410247c030b58020500008006030840c0150340b0100702d2680d0703560b8500001d0229413458100400c4240395684001900400b40210040340c42d001e10303800005403003041070f046030120740040021669a5440302a0003540300d03e01c0e0303502482817410081400403450710410030310313418030000f814110b1103440c11118008540c0c2c4d89110762641c1c0340300061640d07101d09000b802140a0b049540d010142000c001e03040f210502d6081d02840440f01c551500d00b500050004212030080da55885d040908030847d9248001681000c1e9114812030004a025000040c504065074400e8039185101d0392503000a0f81c0d00c021852041c00920400c800141d100803403900440310807403041c40d0406c40d44c0f203044001181200350712285c200c61a541c5682400f185009025060404103505042e4642080c08450100d288001040680004d6450410703d8040c0d01c00c20450b402140c20078000c00520382c03141c4d10310703001e481079105206100c0034900010485a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 96633984 1250 96632734 96632747
    0xd05070e19031502031b370c030f02030d09050304060f0206160e0d0f0b04050c01050405060702040e15281e0b03011d0c12010902010221130e0603060106 67
    0x2d9402501a842681c1150610780203548000c1001c030088100040d6401544107036000b400e00401c0321000c08586950000b21013030000301c03090344c070054603103d08010140710b50403942103450b468041c9001e8492161400082c2e00d0340c464550075018403454800100c00f0320a020003d001a0781d8156941e0742c0000782041b04036036a09050350421036001034041b003007000714091540c602c2c240401401100c05400e80c3d4881441d058010300d0b06a414001040800c41041780c20322a614060300709080080c02d1a007400040703000c60143c03030b01c001d000c4d83c0c0d92000c21415510402165141c4c0780f06181c2c0d180b1034540b0f031540020081612100304411041000c2918083d000781c06100080d041407884141140009888500038250100780c2c150036550f0749074443e0507500c01c03000c03211048409030b0040c114450b035401031003c0720100414070405c5914001003040142c1c1e0114100c400104000c046000c105800c06a5001e5407240c520b80760146448070030005148102035030706900c603940403010796141742c2e66020243d444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 96635234 1250 96633984 96633989
    0x3030f0403020f1f0e03100501060302070606080d0c021207050603090a03030b04060308030402060310050306090a020108101a030705091306080c090f0106050c12040b09030d05040f060509060d05070e19 88
    0x10100c80700d0801c482d03188130307212a005d032040c001c1c2100d1510b0150b41ca0013003140c0b42030304600d0001e41c000036800248840d038000c0d24010320a80004292094011000610442d54014024894800b00802c56844041005214058034004222a07a24109142500d1b0746131092003040b00400d0922030312022500d0079224500880fa040400c05142d65540d0342006031036440100802c002c419020300104460302c08002440c070a4010100412209107540000340c40220020896451102006010b01500e26001228175551207415103060b20390b00c3e094402e4682c0c0c040c650480341c018041c00940c0103004110f400c980e003180c401100750390322076030040d050000d1024201e0f2001c0302190100300400500d031155009104034108201a1009404c404208d55078070350113a404070205c020041054856882c003031082140700851410a685081c0ca40b0584d86004042481000140300c40452403c3c03454a07200101c805e000e201e410100aa864040c4024086540210b00140a01e0070504000420001401490103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 96636484 1250 96635234 96635269
    0x3051e04050601180f0e06010f210602070201090b07210e01021b04060f030503030708240d02060702040f05070909150509090f07060801080c060901050702040906060503030f0403020f 80
    0x583d0b030815444c48071a034010744585100e20fa0b0b41e0300d4600c5021451042e00ea9100b00c0c0d00c05031407a549802c4a500c0100b410b07130009074440c80300700d508a04a4102c1f11460200e95031002026031941c41d10700060b20003005645c1301001b0950b0005031030040040311103c3c030078078900341d1004000e208060503040b5907014185507902d001d64410f40c1d681d1803803c0ae486000310200002030011443c182c448101244420b40c40d03000f255503600100502124680181080303522410080003040c203020380b00c11050b01c2d2161000390360b002c0c0130350f480c8100075500e0b0304003112000c80d005442400084916020800200801c40d8104009440c1d80e101190391000f5000d062819444e01c02502003240c24801000304e40748002d0100d90480c41041c011020a890601c4648010400782c1c48032440c0d0b41c5000080b600303140e91a58154800c0d001000514226a0044144c1e0390480d0150780001f003111682c607121000345a41e422160341840045803268051b246030300100300f46c0b80b0944102d440e14560b601405042e0490a01d24803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 96637734 1250 96636484 96636493
    0x215130f0507090c181809020a0503070303080411030c030a200907020309130507170a0e01140702060115051909030501150602120306211009060603030e01020d080106050a0c0803010603051e0405 85
    0x40900841e049901d00ba400200030304009d9a85800092901c2c03d00e901c100d01184112040006001c00e4000b240c1150500360081c0802c0e2503441c0001c0d0319401c00f0390000300351010417040b0003c80903400b8200340510b40c002c1d002030403604080c50080c0d40c0780c01031030045200c1c41e20340c0f40e90b15140c01d1601403503000341c071240c580d102000d804204050304413100810343c0308255540c40d010703100d10109005845046080c0c000d002c4182c1440c2800904184050700800b4410000e1a080c1d1109680710b000c548400c0d10070751191040c0b2208180403106503c1ca544041d02035800c1015104180f0304000084003124665002c40d60703062081c009440c0240002c48407141d0020313003144c0c071807007044400c0811030a240b51242a1055088006c0e0500101c80380803609849640c3d0f1070509204240d002351072101404801d000030004412003100040081005000702002c00c0804030391520041e0044504c0503116502c904459221740c0c41d43e07002802840d0403a18240a4051008804485071081d86214026504034000e80b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 96638984 1250 96637734 96637769
    0xa1505070e06090d05031e042105030306040903110f030a02010e07120f021c05010504170c0703031107030c09020c070501050f040608060a080312010806070215130f0507090c18 77
    0x4100c01300e030700054405000030081d40740c080c0b03102c0c10740e03401b0031001c0003c0b070781c840b8142001a40d40170303040b4881c682e40810103242000414000010b5a44c4200103d80102d000d90b110310b002c441c44841400507003a5442800a4000403442c04030140c900c0000c1c0758020000c04080442e0244d454206109000951540840b000080f41c1640c0c0c86040320781c006000388440c084020503a0068080030103041d14640d41d54028441040140c8845002600d002d01485007003402500d00c8a840303805030f120040902a51042c9200100c0c01408454021174200300300854241d558544c45029602890b8071010f03901803c1c038042565130181040e200c014503075184d028203150800c08142c40780c8a010f01050b40c031401507400014416000c1004040c2100000d10581d10b65140000d01490990003a041c003003075403c02e044080010000c2111503600032541c41c6a40b1490600d414140c450315000708002d05180100700003c18001e509030409200c0c09003e50f01d03481c80c50710510f44803400c41c0303403802241c07684503148001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 96640234 1250 96638984 96638989
    0x19020a090c1404151d010e09040203010b0d06090506070f080703050c1306030c081b0f0715230714030f10080d0e0a0b04030804060807020109050a1505070e0609 70
    0x2840c2248505000500e8030b000d03a00c03940142c109a1180005010701c8140b10030140d84a51030312070118556135134107200c603041400609040c9070a260300d4044d0340e1031f400050542d5000d40000d4040e0300c0c0074140600300000e41c245900904205241904d1a100f80d0000c1354000d845610311420078034071507a03a9001e82e2900141100500000342c0001c2e00d5050034840742c0c44070211609000014611500d00080ca80b900030406000720100403c1441c8404064030903102d00d4102004035500b041003191420764940541c41c180086440702d402601d409450710000501c005203c0c09000f522011790f280402403984c42500840300b07000e40c1c3c0c0060498500c02d1010441c0c40e9617100742c03243c0200c00c0400041441d40c4848100f480c1a940104480002d0201c028400705810101c1001010b080079420f40c038500750135600c440381a40b01c0c911a031000c01c201a00080c2c80302c0e10030350040503855030101c1600c400c09018100345090807507405500f82401c3c603103c080752501d80141c50741c2d500440c002c0c0c201030524000700d04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 96641484 1250 96640234 96640241
    0x31e0a080304050c03060c0409140c0406120204090203130b1501021e0309150409060504091a040219030b0103061d060c0f0408191e08090d020f1206060319020a09 71
    0xb122a886100c10b41001e03a17805124541c440c40c86c1d98003454a8a2410010000f07807048103002a000c108103038240100c0d400d200c170880c0d068511600f0030b400103207620540380300240b18560010348102d101200340900ba0500070b404841c0d941c024148812291200041e00e1007036020800000e002d0ba004038442e2040e421140b00c81c3c0150003d1130b040c0c9091408440100759000301101c000407001c00c000070b05014021840c41048013820050300c04210b26000c55994452800c070701d400450315003503c00f000504550f550302ca403648c07255180c844020010313a00e05e022150745600f80000c132101030034400c1d01159504e00018404160b1011402000503444d140f15000c1c1711340c0480c80d11240a04100030109a60034200501200e2038511100b9118001880c1014150308046c0c5a0300c1e5070460044fc0940042000c00c2d05071010440200d840c84a291403620000366034140350b092607a04000301071900304076094042440e6105178000c2c1e040d51080585040400440c050740b150095006803a12000d2001d60040c1d0b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 96642734 1250 96641484 96641491
    0x50c040b27132102011a090a0e010603140c151602240417070603110406030509010609090b0601080901020301150c080d0510170303251e030605031e0a0803 68
    0xe1000c00d0781a00381e143c600b6084416084201d03000020400a41620390902c92043d004407050b10014a088174080061009540038202502d8540c85010b100e070800303020b40c45200203640c092001024100040d8065803110b000c0000b05100b0140701a04d01e000602e000111000c80100203000040c174400ca81c01c2100d04250308409030000790100004101c06982d04c80200090001e8115548041c541150034610b002d4558203c80f04147c2811007441e0720b80101001d88041da8020b007404102075440c07000c07050041c4800d620200b81d00e810414001c09108200120034010b203021b80c0d5128040c1d4031700e0319844c00d0784020320a929200e42010880c9030202e22a52200300303400d01c101c000a25001c1c641e1440c000342c40d01940e02c01da1028090400300105608050788401080421001d942149407001000340c5142019404d038006001d00544c0007203491080c84541b901810960400784000200f11000b4005d0456000d11030003482070710010511140c241c03e41b00340d200841e0000705041070721a51101490342015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 96643984 1250 96642734 96642751
    0x30308160905010c150f0b03010b040207050606100c12050c0f0705060301120c030602030a1e050708070503060d0c080106150201020909180a0b04030302090a090c0c170f07050c040b27 80
    0x6140d0045c1c102c0d018049243c5c50b5000c02140106503001094212007414012501c07481c410007110000036004a1140c1c1c3c8200c0846d401c0d60500b00e5000b090350f83c1840302d007000301000c3d40c8c18541918640c1040181c00007130000002c1300c071464101d0740c040c2c1d5107140e40d01465510100c2400100462054244c14070082e51046405100990782e03541d42d002647c0040d40d184400945945507044a150300d0354074003200e2a1010030a002070304110784040e0066034050000810001c1c000000784440c0c968800b4a07980c9580400c41c02c080300d503104030a0340281064010140c08200b002148040d86105000740c400d00c580091003609140c4529411102d00d4425444840e01802450410030204000f080e055220394041d840250741d52042100b00b00c0070507025000102110320300032450603c2588075210b03150841c1d2190fa224900d00078040c108145001d0503c011002c520001035000401c1004141d080d0180000d40381440b40da992001000f000c00350060031465510480304c8882c40c1c40001c205082c0c2c1203882c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 96645234 1250 96643984 96644003
    0x20c01020c030c070503010c080f0c030429010608060409030912020f031501240807111c0c0204060b0306060307030c0905060403030809060106021908030619060801030308160905010c 80
    0x950054a00b10740000c800d4004035045a481002542803e00942c020503156190021300780c80c000c55040100c04000d806441405804000071301000342c500071040074910682c404401280024030389641c402d009004003800500c4003c08280181014000c00c0c2005038940c44803190f0b0b9080c00d11984032400003c0c416603028000c004210442d480520811041200c0d6001802a942c1007032149008807030a4140604841882c58030f41300783c0b40c0c0c030104071030b0403840e14503000d06018010507050b45004c000c40c04001005410140c0c3c040c85c0c039044103030a0711081c8203a17800d1149a030354428a16190008030f9840380c200004000040340e0611a0303110a82010340780c10070781c1ea01c544030800701d14076410540080340032a4405062141a2031f00b0083d80380184054801000b0100f024154241041c100740d00061807001c0110201d41c1e15982da42c16806010711300b40407585115580c0c20010300b403550a10055000c00e4062000c41c40d580640c8041a001c503409484000d1950320704001107555042d14001511000507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 96646484 1250 96645234 96645247
    0xc0d0b15040602060907060f08072105010602030702040f09020d0210141603110f03040504020d020409051f060206070e0d261809060a090b0310050702010606090e1009020c0102 77
    0x100350301030300207032146030700030682c5151140f1010300d4460300380c11820903ca034000e848080c15900902c3c055100b800d502d000c4840c458200510184018401011100b0a08000011035510740c00405800a035000702e405101100c1e02b96090802c4a2403000065000325500f0500005403c00a10f038000112141c0b420915555a900c4400459000440c803810740300820340d001000c0c07581c04500400104246000703000c1d280310101282d9983e220754800c141c002e41e00498103940014003641610f0041080003002d01540c541021401601c0b800340c10103c038198500c0801064203840000e586210302055100c011034032041c0000c00c1214900c940d01120200d14940102011107807100c04201181800003840e602c0711201110000d410075400e400d9402041c61700300700300700759032440e103542c04640304030800144250704140400e003003516884c000b2010760300340014840042d90550010381115603d0307840d903a540da190000c4010180c2c083d1440458500a00014010500715600a154148088000510701031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 96647734 1250 96646484 96646519
    0x150b01030606170f0c1902010b0114030708070e0301060506030406060302120a0503120c07050115080d02010c050403020d020402070f08180108040b241005030a0501080c1c0203070e01080d0e0103050c0d0b 89
    0x6c080e69407000607512008410034a503001500c0c2c00d81e00503902a441d00310f10b003502c001440000c00401c0041000340c51050404030f03480070761219000c1d00d400341c01203a07207142c80e0400f60090b18052008a0241c101d0752030300002d100c0d0110b840c07400340d07610102940c07805401c075190041000001e81040340030705c1c04002180000f8030034864003031101442444054030340d00d00b161035418010860138140541e41483d0303640d24a00d5026045500752a412148401c0c880c00e036001040003409640c400a10054006010005100e00c41028190b28250613110f218501144001120203c600b59401803900141c0c2d80800e860b054580c1c1d18031100b10036502d0403840e01d1103040014542603202c1d00c1040201d103001003030090b0040a801400e0140885800070700890715008003082a00740e2072014a0001c4100e280c03500304541c2e00303128810003498084003c0e0b0403940c454103002d8940101d0990503003c5580f0380d41c02c40d1594007074040c40c1d00c2042a0405181030100070304a80000d001c00051003a40030744404002089407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 96648984 1250 96647734 96647767
    0x30204090c2106060c0f0515130c05010c0b010306091502160308100503030412060b03030d020a03050601020d1d0111060c04031b030f031b150b01030606170f0c 70
    0x281001d981d40c5151440d107480304203455844494508802d424214140409500036030004d560710b03408145030b42c0e40c81c40e6050490500c0903070207404103903998010501001c28480c0d180c00002d9401100c05204280c0c1e00c90040d031f02d85140d404010042c07030312170004102080c0c840e800340301000c1c003500403c1510060794941034100d82c8040310104180d030300c40785064145035210303007415400048440b000c0d1140b402c0200203942c80c00707a40b003100156a08035882c1410000240c0110f4111807000e402ca82d124800110050044e41210b0301d80f000103460240003401940c80011200c9a84009132241ca025043c90940810071305400202c4d58180500c0c0b46e1480403040041118034883c0110960703080e00e03641540b91111401110a0b107020344001d4005062011030400c4045625040d418100000394103030400c81402d2201c040800989458440d0a003107414000e6034000125000091ba402c0000a84070300007524101d0403c9005092896000006203000760b030310200d96081601c3d80029818001384c40314a0805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 96650234 1250 96648984 96649001
    0x60a020a060c231305060a050c2b020607121109030a0813050a0605091903050a050a110a06090b07020103110c070602070902030412030518030a0815010311180103020409 74
    0x20b07020315a80e141d20885101a0500b54820420a484d040700908855401804c0b80100c2e48074010008918003205c0c000c50450b0341c03101d80740044d030b210030034042c407950350889040d0301d010410f0314541d01c410301c654400f04103207128100c19150340d60942880c1490000030107840c0c400301000241000652074039a0100a11040711f03103d0007002d9a0b5140300002404640150b17440a80070302140d801c240131207500f0009903030340b10741e05850303128419240b140000310654040d40051f04501508405000b4007a0110f04014140c2c02042c0040d08088110140038205085210302d4ac005425040b042c000c41c04803000424045005240215850304403030203824082d4030007580e40003140d111035001c20400d40c05110700c9000340070343e240460461500c2e454444103006541642c008056581c0c0029140e40300c00350030075480c4610712003100e0300c94042c0c0b07002500210043d00c0c000f0200c416000044102d6102e40a4054002180e41200342000554001c03014440c04250065060503024040070444c0f0500c2c2c03180850 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 96651484 1250 96650234 96650237
    0x5030f0c010b030705030307150b0d0b090f011508070302011103091002070f050a05220912020a05071a0f0a09031e0209070c0210050c01091a160f020c060a020a060c 72
    0x102c1c14010401c2500d04511503024500070b8009000c4c010100e208050800d0314400325000206210440c600003c081c805130020081003881c240003030240720f010014030500900b00c5400208481406003d52190341c07282481402030301c2d4461042400154494581d03152000b001d001102d040801110018154a841802000040c8e02444003000303000398034400d500c000c1209441580c1d80d142848042100301b0b5024400100c0744190140f2140400a654400984130360081c02c90710700701d05000002520791080140c140c82a1007500408683d201d60820b02d00f03050207000c4180752a0090585116003160046030300f54080c003904980000200c2c003000c1c1d00080368910042210000101e51040105c100310103443c1d001042102400000107866200c9460743e801a607080040c0c0380d55070800c000b409031480e541c00030128207180d1403441c0c42914005009006401c00700c002603c50300031a0b0225105a00301c07034104010790090689840506092004000d0031070342d481034403c1c1802e11b0316004141d40b4400740300720 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 96652734 1250 96651484 96651491
    0x6031506040b1206070e0901060512010b0703050702040908040f17061602070b0c0610090b0d0323040b04080d02030c10110405041407140903060613090218041505040b0f0405030f0c01 80
    0x5070601e4107c98943c00343c010340c2082c85c105070160150b07281c440414004c07085441c80010b404030501d40144169110b4030307030041c0300713010440f00d6240a0103a038020b071083c4007001004000120340032136000c1e0040102e241b244001e000c56503030503141c1803c40e80312480c00307401d5000d1804045105140c3c400200902c030340d1480101024140021400c641c00d03001d5000c11002c0c0c2c41c20f040f05003142c1d25400d581420a0f0036140040005503040d030f00c10320ac0385410504040010300010b0000e007055902000d84100c031500c209482d03800b074040c0000e03610381c4116000c01d20309810010b000303051a6030039400748400c0204c19650609290311140490b01b03c6c1c02c0c2c0c20403c0d546400080411981680c4180b2070381c82d401034540450700b0002618082955400003804540c0308400f2903035025013205456101c0c44110740c001703104510794103c6400100000c40182c40998a4010031011902c50f02280e0040310300a5074400c0300d100d1a55030b801321629802c4805402214580000c0000003007000000c4081d00c40d03004100c0001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 96653984 1250 96652734 96652757
    0xf06030103060e1515210a0f060e0c0d0602030a021b010209030d05130b1608070b09010606030b1f11070f05010801090504050717030918070806031506040b120607 71
    0x61404032504e044514210800041000c0349030302020300d04410609440202c50030700350160b80300802800f109802103d215824000050000300b0340d02486081c01a1001c0100361480c40d189912895540700c3c0c550841c003060484000902140d00031544000340040040c2401c010751004004100c0c2602c01903003903900401c0100c2c035803406029a01c51650306042c914a801d0301d0498801100d0014410010109004644184900706003000c01c0b0407141d01945261744c485030f6140c0622020000d5640c2c0217150320b000b5020810364000d2042040c0480010f04010070140b41012599058115038401e0701001610150a55080820049440a0414046a001600e0501c4001040790505910921226042006001c0411404a03060081e40d1540074a00c003103c0010721140c0c95032003100d2a407508400410f0401d81c000401c139600c0e50103649666285107050302e03107404040d50391588902c0c60390681c84c0200807403c185425480144031000280191640380d040259460074102d0464a1601107003648181 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 96655234 1250 96653984 96654011
    0x80402221a120d0e040b030a0c03030305070801080f031e16060c0e030105040b010302040509031e12071106060108131415070f1704030306080d020a050d0302071109060f0603010306 79
    0x40c1d10440c000c1d000303081a4002403c0200100d4501c50240c2c000d42d9110a00c40840d18144640c8041c0c1c0e402c43c012800e141d1741e03860020010702080f210b402c0002c00060012a03c42d4003c01c0c14030420240030300031810418004500751000e00080d0b04e054900e00100461045400c8184d4114003080c00342500044600804801421600021005d00d2080e4941401c000014002c0851241581d4043e200003c40b603503040781c02455480741c0c000a1003403010300301c100d6899642c408010001042c84900c070074090345440c0302c00c4c0c80101c01201c140c0c203250803031400902c6952050380c0450340256000b0217241b0450b52526100d242008072020076400d0303046500030b02d55010300c580702c5641000070362601c08610100000010090092101e8801024080c0380105050602c41d8101c0805002c594040c0c4103464041100070b55034040c0f2000031152401042c1c0008030131070103803080e030f204142c10034520042e004c855410800c03464401841654841a00c000905450702e80c1400303107001c0c520810000500c0002e5240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 96656484 1250 96655234 96655249
    0x201061403030a08011701061a0406090e04080304060b06090a0602100606080f040809030109021816030c02030f03130605010303080a05010509060d060f141f15080402221a 75
    0x4009000b58820400340000c0c3d948001e046046611402c1c11410b0440c202c0c4400e805001030303a200702618081c02c09103400a5803020000c1003180c10070b80341c3e012010381c0c5605640b8480c0c01203c0150004005200260206107160800f0100798402007010745059071600016101c03060710341000006a0203045031401d01d040134403845002d400242040d23800c601c1c00c014020340c9018001c0004022450200d00300c0050303282504094400c2d58001c100000307140070032740c0c5ca18a012040321202c4054800740e0a0060040c021702c180008030540b9805189466404950310290794809404091010b04110f6044046034a40c81018040c62090b554a070450410164541c203554068000911403000002840801e0742c8401c049174606034030001c0401c04200c000c206100401c108494600a201480c00b08104214400901880742d0b0960400704441d50b00c1e8096900000026010603001c29109030201e0054500b850600c009660090009104040d0950040303094408a1030411201801d046003110603280010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 96657734 1250 96656484 96656519
    0xc030203030c070306061a0a110c06180117060a1e0b0304050d1202090f040504022d01020f07030203190507090e060a1802010c1e06090f0209010501110607031119020106 74
    0x40007c0c0081504400d50600d078801d480741d403c140000501c2070180c0354000e01450342e1000005250342e840d0004e100c0c601c4004401c07840c07281c0c0040e04500c2a074015150341030321180641400361100190a051403004505c08d650240310f010003400c000d00001e138105882c0c00440c4100c1c4964064084580c400390058500c05203066900c030120b00500648181d0f031951100a121190100c03400300b226140c900109100b8040d032041078850300c0b08502c2462150454441e024101c1c64280d0848880c1a90368230503603111503c60100941c1754026608c60418501200b802850041c040c105842c400e96031028450110f80550345007030700d540c101104210182420748207200038031203a460b815214408650000380354041c1d01c00010a0300f50146508055454805a0016400d500c45400c008003030003810044030b46805031f04102d104480100001c20f443d48111003240304012000003c29070381c0c48180b0142c0241c011940404050201400701c440101d101503644107040e00f031900002078060421246085090406 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 96658984 1250 96657734 96657749
    0x10f0203030103030f050307030209060d060501080114090a1a031005190606020d08040302190305030105040b06040602030a080c07020d08030a060b0406020a060b0d081b060703060e0408070c030203030c07030606 92
    0x1d00c010004250080821046103640b807a0040ea41d5075210019002400340040301c542000020804c0703411074815a000c4000d0f40c8091b2140070702680c0c0d591744180342a12051841e6040320b0b4002c041040c081031504210f54860400c000c4083d2103045101003803910118040c0c9009480d04c420034040ea1504503d4041040b8600b04001d000700d81c14031001070f44d1603040150010810640c840090141882441250305114034110000300300c0c032607414000c0240d0401e01030948543c0c58440050254a41101202c0889410350050341c140302200400b581c00710300040204001c01000c0000c0c1d8010707542e0107880f44946100d00c85054882c00d05100c0001103a06540080403030b0380080006005058000034240c80596000790081585980a40030551008584000800084d40440c0c09021402d050201017851030580b0100c60060760342140441c00c0e209548212502c149205020030041443c0390010b04c242070003448141401c50b41c1740c9c007003465a4021040072820342c1001c0414001c02c0240e001d040024140c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 96660234 1250 96658984 96658987
    0x71d01090c020109030e10110d09080f03070c03021c05010212010608060a140d020103020705010c030209120c01050412020d0b0403021c030e03030708181f0501090510170c0d050a02010f0203 83
    0x169078001d40072040680341340e88a45587c00030b130821b0510030107411a480e10860107646105c40c901801400d210024080c40500307025000705611002000001d40c2c00290300050000410362840d002d008803a65400459507003c440290001e0101d1000d000030440f4920b4010448a03c2d032500000819040024007010311a20404100304614150b5000d0000d0891080b03c800d4843c68040c80164000e10440e5002041542055007100c2c0c01c0b0f81550240c0f00c2c214051324041510382c0c802c07a000ba06c514170a0b0209001c22028842841401200030a40810920240c41d0107800981d903110f01e01820701c01c8031300300c0041e40010a20f0f02e00340b021032030446040b9414101400310f041c0e034a0b01d6580740c3c04020704002c100040e0b4070001e0b11500c641b0390800c41c2e204d491400e9450300707507030401409200b41020031800385c10341c01e11000044c010f99910950f03102d5205000707140030280c00e14260700c0000e10b40d010007100030310869120302c00503540d24102a03c024480d000411061041c2d100141051556440c80310a5410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 96661484 1250 96660234 96660251
    0xa080a1e030b1e030a060518190b01061214100911040806060d0204150305160e01050f0d03050f0f040302040b030f0312100308070f0b0123040b03071d01090c0201 71
    0xf0b81802c1d0750303c45100e41e01460b10310204500464507001111002902950600080c02250042c070240e02250310034000035140340c120300c1d144540700b40c1c544a40040c5408041700041180c0d6100c3c0ca020b0540400340000415400054a07551515500036140c881240c810701c43d040106008610980c4284c80c82500b980d030401d8507161501d51142c2d00180901d00407000f800710402159515401500e40d040003811002000f512420440d55a0000380b0040d40700d541d04030808110680300901c041e0494074000c0c10b01d030008441d03d00f40418040d03416003c80c01c1c406d0600082c600e4520f25005080c8260351022196121865401081706960000820b030740681c1061441007144400801120504031141c040c0b018035886040c11203c0103401381c3d04c003070b1030718401040d00f400b08854404c0034044240602840200c1703989600d84090a00e002d42c1e080a2503100c070740a440c42500b45500000c07140d440013425a03004554661100c030a51f02c01e01149c00f00c03500c42c90010300443da02c41c4a400700c851004d10003000b5008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 96662734 1250 96661484 96661489
    0x60306220303051008061003050c0102070e06060703031407020d021006031a04050309030304060c0605090d050d0c021606021f090201050306090a0b040c030606020c0f030304090b030a080a1e030b 85
    0x420608007a04154860380000c02c0c3d200d507081d46500a10100f01100d0340e51900c0d01e6441e2400816010881e240c3c00707000c00342e07080c43d0b20002c0d6050694210045522558403250b0400c0521b5005107012000d06071103c00800c804541004014454103160b00a03288807151460000e08040500b80c8104095140c81002e1011a81d188010146408100c500108580b624240680395015040304e555241c40000b42c0421020f40c8040703090b254a104407024406034544a107060340320111105181c0c0007072018007030005520641d80122140740881d0054131a1515000820500c01105400003805130b4071402d550b1040d0f00750010042e5604a1503003040204081c160b00080003880041c203010311402c0c0711408112540032035403200340c61480003441040003800381200a0040e03d003a110b02000750042140b000e00f1820020307151504420020042c41c505410304503010002e010000d02c01d81c140c0705d105004400660400010400c4001d50b450b4824191803c038411203161074102050002c150902400d005c00d034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 96663984 1250 96662734 96662791
    0x30905060703020327011505040b1e010c170c07061b060908040905100503060c0f0d0515120307061104120b041b0e0f1b041203180e060306 61
    0x7589809030f60303601e0310f516150009000c0c101030580c5620202140c00b07120030551001038180b407411007048070f0a50755070420044581405a16801804130021300000010703035007003260947c0050520102c001c0044d100d0090800a03042d4511005c080083d00420110301000390000402480c03505c491440f0070a282900d46c414402c41c0140750a40720b8901004000c4500150340207008410020000c034071b0040d008801884903031181138028010000810244841c500407031b010410390311021031a10009c0121a00100401003e558848504400501e0b0b00c1c0c0d906401c0e11150300c4945c004546609a60620308100c404900729903004584c208020080d0030900492141403581229140c4402da980781460100940040c0c0c0c0060a198040e001165900310311045602459048591040540d220900c070301c240b079074010108048820520041040c07421242c9280d0480c1c0c840d00d03041080301c0f540d048043c803000381030b0030489002c00604204402c0e820108022079100c683c1054214180341c0440508110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 96665234 1250 96663984 96663991
    0x3030c110604090c020303060f030111040b030a0b06040602030d05011e0504020a030e0102030a020d0f140115110a0b0403030b1815060c0304150207090e0c0103020d0905060906011503090506 83
    0x5040c02200040c469074800c400d030307002440c610340207100e0241c3c2c140d0000e48940c0202d070b165210312000d520b40004c60405200f0a840302a81036031140c80c040c1001848201c1c2c0d0002403075554516140e0001d8120b6441c0d10303010780024a11a001191256901c60042040c0c0d40c0582007002507407502d40c0200602902241104c0480d074003a100166034180001c0102e000d0051400902c0d0b4940c000018401c036106d25a00410ba00740d14400300700181019100c80109551551103143c20041c450300040c0310714042011101c0e070862217400c004001c105803401c3c96040c200c902006a540c45030760f0040005154060040d000b1110040b45c10400c19066103c850f940300c2d00c09060002426108003440c8207903101c407800c64414038480821203407969074814200281e40344106c02c00006000e500070006070348003580a8003948142c000702411621111100460003500042d40040e50742d501d03200b6042c0403a0b01840140d01600d65117020306080c1d810070343d20303074000c00440700c0490801d8030340102c01d000f2030800b0640c40c2c0c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 96666484 1250 96665234 96665243
    0x20a08011803030504020d20010908030313020f0613030813060206090a060506030a0f05210301060905090604020d0905011d2a010504050306010b0306010e01030b06092407060f1503030c 81
    0x1340d0f0386403030000c50382407965040020300c1d400d20300030311001013845842880c0104000740c1e04d0741c401a4590108944038002641d1400480d1009205540146031080720385020400190059040902a8500850b050070360750003503030580380c00905040710300c0c2030124800140041d40014042130500f0580aa90340b202e8010180c1003507034031300c007050840d07409001c40c7d8901038008111075904442802d240d0b8907551000509800d10340b82c8020b81c840310718a18280c0b4100d13401a1030382c4007401c0c50041444403041780140b0741c580c0309900300640b100d0000f4521800f1406805075000060308103518210f80822150415101c1c115403010590020580352040c150380d100d00364000d502412414400141e17024041d5070030656050160303000100b50780e045130000d14410407003680e4100e101180c0c800107400f02c445280826800640030003c202080c20542520b030380c80c100c4440100441041c03001040e249400c101e204480c1552501000c0c071000749a4000c1d400030034005a440b500040c59650054040c20081c0401407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 96667734 1250 96666484 96666491
    0x909030f120b04061d1605030f0405010204050909300403080c01110c0a0614010302010824060d060905010509060303070b04031b060603141f090204020403120c020a0801180303 77
    0x8078a4205400004082c0c2c1c01a0060010070b80382e2255a40004c1034110340240039088000042c1c13191710483c0c3c1c40190141c10345442e8a540c9035403148090741d41005009a0b501d41d002c000015203030700d0b102d0880d0700c1400040060806402100c51300c140c4005c01d60728400182251308405403a1014810454007107a9015000a6940100307030022405030003401100c8100d07030404140c0e12258800070694200080c854281081403544104060200010a0001030700140c0030f41c000640d400f030b5005a5801c94140700c5440c070040d91a880c0010584c5d48400c00d80740100d40c64410804c8180c1550051501522080f1044002c62810348082903480c001c0d8a07020f4441106240403400345030085c8052450b00d5a0b4401c0110102c845003402e8000d40100e01c8101c03503c40c0205c08035003001c400814149006003200070207106070410704100b0806404014010b030390044e400c000c00400a425514009001071094032880105001c070300410000e0b00d080d501078022a410568040c0900c0044e05070300d8062030380750074000b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 96668984 1250 96667734 96667757
    0x60f120c0506070c0807061706062104061e0501080a0f030512130b010e04020a052209050f070b0a09150306090509010902030d030e120f0f030a0c02070909030f 70
    0x345940340e000e150042c400241100910114401e81015945103108481041d66282011030301ca5640641c50821003803001d002c18400c0c0390408c0100610301c500d05d0030007a84180703500c078070580042c20380d803c481c3d03182d944000c407010358240043c0140141c01860101b04940c07501200a488500d048001805640825034003400c0501890690f2250014040504040d213012110403003090701c0617409032200b1924100000e0401c0301c1024a82c4580e5002e400141d50625160a200083c4070902d80c081e80c0e0b04201c0740c041142c40d418031418018602400c010041c81d5070705078515060031010f4228919030389080141000e001d40080342c80703003201c0c40800c040080c00c1d0100c0d8210300a0105400441503d418076003484142e8505401186650f40220181d840e5481310344015800c48464034030340001a008200040c030120b80c2c81c009031401c0c20405507110314020040040c8001d80c0d0040710f1042404da42c7d40b032071854040e410416071010b005940010008044c00d601c01814040b503144100c0100a48604030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 96670234 1250 96668984 96668993
    0xe01030e1e1207060905060609130b280605040b0d050304060e03010605040e031e13050f03030d06120312050c03010b070309090e01020915120106050c070f140103050a060f12 76
    0x44103079001120401d540f10038051800354050328803200d081e50a032103901c1c04103601d46003007034a090050861030700308010801182d070f60004480c0020501400c0061660a01070314001022868518441d00d400001d1380e10f041c041004215000d01200354050480c0401410004200104540648540d400e14103621003c080000c0d02402e215080315070041e08100642d10786a0f00000640380040e4225100828038401c001540014000c8031409400d4000c04002082142051804003120000181c152890502070855410513902141d011842001c4110301c0e80c1c041c10303480040410360f41d1034501c0900c000e00303007005154803c2c041805452a40d1400164540815020f0780401c4000d00300d40c0c805020900742203400c58001d4010704811402040000c1c62108400984411580e10015510230a071007079080c400212a15080301405545510940300007040c0b40601c4495080101a00180d056154081c08001020b5542c06064219102d0420350180318010b01801c60341c00b070b160103849217100c42015040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 96671484 1250 96670234 96670243
    0x160302010e0d0c05031614030c06090111031204050f120c100e0a0f0b1611060c0a0c1a0411010e0d02010e030709021c1805060601050d0b09070c030e01030e1e 69
    0x102d10390621480004040c8440f0146c82101240e84142c07005001d0f4000c2d10901d500c919442c0011076200a0070042d400e82c940c00365064141403a00c0e41e0031281051b04034aa0b440105105450a8401e54000e050480b400c8404014240700d04101d00461401c209900c400340e6503640140d031000e59402e407a0011a507080c0001c02102a41d40d0b00308003500590096810401c02550b02940c0782490080241c01c0c011901e4001c100005080007030000070102940d901250100503086034011000308056000350b01d000c5032801000e4565450781d0850903459081516050072005a807010742c905005501c170054010342e8034800c0e410741240d02820841d1909414800207810100e9030380003580c2062000c16060101c1120085002040c86007034803c000091280c0805150340f80c00d80c60080442c1d00040001c2d00c5075109101804a1880d80d00000c00e56440017400a0b0b4144400c0b6000c10009011070b41c2c030070a069101c940903191360707020300f401c0140710903120715244c45400445e440e0802001a0b03004c030025400800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 96672734 1250 96671484 96671489
    0x801090b120d03090b150307090209030a1403030114120d110f030703260c0301140a2d0f080304170c0315090d0201020a05090f0d0c1205160302010e0d0c 67
    0x101a9203601061040143c01003140c8042036554040c00070000b4504014180640208103005004080051030b12503c031001c0e500415039141c150103911404000101c0b207045001d00e440b0340402175500da46c144071096642c100e11181251050840d140c1e400c0e0560404501c010b0410414681600e010301200e06d854038282d00c01042050354880003a609041c1a4070812000030a00755240c450444d01c400c501c50100c242c425140407900c141c0070401004000500b00700c0d040c8081e809020704c407002d59200c9405402a01d4462118000c0205120140d100740c10004450050200038681c0c003c442d091003034a540d203001f0b90040c00120400e810507541c01a4041007100340480380101200e2408200d13000031424140192058441c0384100820301c80c8403070041c029203000e03a41c00d903200c0d401d107900c0b0000c205400700c244103010f03001480541001c000c0740080076260054012854402640107e5152542c40c081d003909024400010706201440141c0e07011403c05c940d828100d5100800383d0751410400c440c5039542c5d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 96673984 1250 96672734 96672769
    0x603020604080703060b040b1c0c030c060f02010e0d05030c0a05070503030a0902120f0a030f030e01050f01050118030b010311130204030b0612010515060a090503012f0a0801090b 78
    0x7040020301104001800320580303208020a10846510030144401e5582d42200d8641c003402c81c1c203c4007007003000c42101840d0140130341002481159070b911512400019508250300140803e40900718440c1c0902485000c10f40080080540607034101c0020710900001c0c0900016100000d10503074540d02c00c0058409540c3c000b01a01e569041c002c4100c0000c0003101c1d8200e004415985481104001c04500038462aa5a42c05840b1071891650200c5403030041810f508281556000c101050314400d101e00c40c03003a0001d24983c1080e5040600141c90300c0090700e8000e0980e040b4800074400100b0051151b411030354844d83c0202511501000219008031103900886c01c03d10100c1c001081c40040b80c1a28003e16098440c0e0780f480d0700800c81c171421384501700c420111100504044507070070b082c640020f1182501340d00d801000192950002800e40e80c000550b0000c080c0c1c07421861030f03118602d1040040d03114010740768a00e0041d02c01e2020381014414030500190325550f07442c120741030300e03801030080524228 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 96675234 1250 96673984 96673987
    0x90a0906120b06011803022709060103021c11040c0311130513050f0403080601180b03040c060305070c080c0a12110708010203010b120a061d1b16020108060406030206 73
    0x7958a0001c01e4002400181d0316040000081101540140704201c1d0b2400c20a00e401c0c01c06056400344011480c854900314203a070308036080301192241400c40b9600904810015203c0e42d4074500400c0008034000c0c064101d842c1c0064860800210301d051b00c402c50f9030702a03074046414040518240c004112540082d003424000240920102d82542c1c6a00d05640013224040d0035024a07480c03e6007114811102180d6100a401c003107400b11f4007401406600c2041413414004400345403507902c4207000d69510141803030344080306000411035031680c0100640f5072440c0030031551810580c001e081c1041d4203c090401200000c50540356002806205440c0e0307000110f541150440b45002094803200702d10010840c000c82c800465103041c10b00880703040f20940c52000e420820801202c0181daa009803039405403a42c1c660700043c94101c0040e41012070400f650400c4500d203048080e08400743c444034290003216004102e4201c4c46041c51843c0164160286400ea4081e82d901000c1002000b2941020754007120 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 96676484 1250 96675234 96675239
    0x30304050a0e01090608030712052a030711040207050d050d200406030f0b0603150a030f050312010602010606090905150411091e0904020d0312020d050601090803030603060c090a0906 80
    0x10350b040301c20b0403076024040410411341e1315042c642d01c13400307440e40c0140707800c1e104213070340319200d104201810384131248101017158240025075840c90042e00c0083c2c8001900082145000e00641c1d07001401c1041060b50290325040311565015180c1a02408510910a012414040c00310055201c0825243d4140759050340010005100000d50050302c80d0400090421240c03542c184132500912001000251845085849070f13820f090b1312001e03110400d83c01440c00e01c8004003203010b0000c41c046160142c80591b0351039901c5503920700c8060303058103c0e00643e070400400304500f90b4030100c01000c5031060000013076541c0b00d10000c0f200204100301807980c003a050100c001040b001100040c4a601801c40327006489601c000c4038104040c510782c114550100c3c8000004000d81400075030500090310900d0184080389079184120205d03000350000841d501d42c0c0d1801c00102d541c119a1450144c0f942000a41c250302d4084002541c52400070943d00042c80003280a5807151103044041000d0f18415605020054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 96677734 1250 96676484 96676499
    0x70c05030309070e01050d0c05040c030207080f0406030b1002060103150b180603010c0e01210e030406052a0c04091b1805010b040f0306020703020a060501030807020102070b03060d03080402030304050a 88
    0x81d07004d14a41d13007000c44000107651400345034440910303501403d201034548c508001c0100500d01151020145502041484005200003004041071070000c1c0c0042e032142c0c1003880060480d084a03810a00403510302d80516040c5400052180c1101d03808039859030017031181034010014051060380c058100c2107005440101ca41c00440851107007000382e00810000002400c101c50070859101c1a5012070603142e5a4030200b8044030111012200c652030115103181d0060346c151a550150b88103000090000c54102d02d80c0813109c1c41d9442c52a40500d414403100464048503466828400766148120755401d040002c02c40030015000f07100c0016407688001655514200108900169042d01d04d00c4c54800003103210001c900654080c0c950001c60080c4580c11a0f07600d000075400781c5420b13000e62081a13032490000e1501e0107024082c6104084550b251541c030310000e032605405801403441c1c02c605000b00322007174a800d009014410b4240c90302900c10b0b1614001f080c20351140b03400094000340103000114000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 96678984 1250 96677734 96677743
    0x5130f060f14040501020d0c090f17012703030c02071a130806010602100b090103050607140405040c092c0c0f0d02070f140303010f0627060306081011070605070c05030309 75
    0x15400c82c0c0090007403600508c4101d51079a564003072088120b80550041c08041e12100f211401c4281040000401009261500b141441c1421000481b404e94045500c105541130103048442007643c0000c02c242810480f60540400da0b80078030400340c64022844080b564684015030005045000a071081540c40d41d5000352039488544500c0b1881e401c212408546091001c040790407688c211002d08016100c0d50800c546121400c3c005a08009082c80302092654551080121246498139148000d40c5044016111980e513501c0541d00519980c0b6441001d1a40818407540070070b426400382d50700c0130341d88a200d01d1801482260b42e88248013165031000c11241c80c0e0040038090080405101c0c0712215030314180e491109001e0240001c81a1404000c40740c090b00000502c1042041c0302a1400f80050100d0180102903020740002500d80000b0080440c0521201d56000307030400003030141e6442d1101c0d401240c0b01d00107006243e181e0f200009a00c143c45083c0040301141c5c484141e0766241400e1449a685 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 96680234 1250 96678984 96678997
    0x15040c050114090607230f03070605160804060b130609021b070b090910030b090a060c092904030804031b050d02100c020307050402070501020c0105130f060f1404050102 74
    0x1c5402c050344040c07522107540680b01d1040e80149a140303007400640d40c9124840202d01205003241045002c042030381018001d188540050700c1c01161200c0c4c19051080603a2800f9040200100040004580181e442110310b80d2054000b103000c01d518052001140c0c10894650711000d1080c54424041144281500140000030407284803500d002d4204404546450851081142c6008100040345447c00e006130300c00e07031103a010606240c15a03a2074a03000035801048480400d25040b1800200401c6418810200c1c102e00629026030032070308182c0301d44104004451000401c52013190075052482d0300744100c81c05140d11107107c90f202d0f40c1e0703840c0c05619a0180c599920b0484582d0340042464203014200d903099940090429241c520b80c01420345100404d24004c0e6014040c40c600810a51164001800300c00e00c50400181d0b668040d0903520308454000e004240c0d500c0b0810149804289800e8035003503220742207200050a10001020003000300406c030203c2c140d00c2220400c1000340a810b5018220 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 96681484 1250 96680234 96680237
    0x20a0302130801020306030a0b04050c12030702010207090b060702060304140f03040303080601020c01080c0d0626070e090d140405031005040201030f0917090f090901090318060e010507030215040c0501 88
    0x41c103510b41c90094242d0004444264150703010b807840c100031a00a401c03103900706004000f541e05041c0908046580d00b200000c003403520b075000192203000c40d40d04001074402002d03043c5042024040120000e0381c42c1c070a1140103881154040041401d106999180c1d0f900c200352802261100c2124400e03082d00c0e604a0f01c402c0d80454140030010303c8a50001c40c0780c001c5400160364050303142d0780d1424403011640000b51080840b5030354040c00305051800c40a51200c2c6a040c080300042080c01c820040d140000e00d401c001103c0c0380280038030092000001c0c0ca0004584141403c125071281c207a1030b1140b41c00b0b10f0f405203505204640701c0c510f194100d40d000500560003031740d062182410b010380700c1d010748018400003044001a0a00d13080000c4020b4050075002c180107040c3c40c280c3c54140c0c006007005006840e8008542d42d95a000704c101a0410031401392411148040714945140000c05410040c031070354410b052142c00582141007501c2400b00903440c51444885420b05d00700f038245000c00c41646d000c1d060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 96682734 1250 96681484 96681517
    0x6050907170c040f0603090f02100305010f09090203030a0f0c0b01030f0605070f0c02100c0b01081617030a03110405041b12110915120c030f0c0307020c0121020a0302 73
    0x2c000c0c19480c02200c00341e039080341c01070440a1403d0001c90081c0080c040541c1c450641c0c8482000581d5070b80e081c81e45c0204241e9002c5425418180041d040c1c640e281e2010107002d00c3d2a8004e00140c4002c001e9520400c02d41c1402800744452880075100290a808000d141002c0c46001100b0000c626007802c04250050342e00b000f15070394009041d20780245420a60b408244003902e04401407815000c0000c5126a82c0740045e134007000d603620784401c04000e03002550603811036800d191018034003031070000060202c0c040d2201c0709207100c132040341c0360b01c94145034001700360b1982c000d0000b280c1200122001480f01400804c0510303010703125200390030070007840c0344001501103c01a10702540da01035402c81c0200d22854034039008204082284000c4440c0b100d070b5480170300b031040c101c6142003050500c0c03081140d44e084a41e80e141042e41c0c061401002043c220303140200b4814007159680c0000d171030038402d9080c01c1c004081030194000041900e0390450014a09000062120203990300d60042d00020701d02c10501d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 96683984 1250 96682734 96682741
    0x1030512250602040e16030c09181a04110d0506030120070204090213090215030106050a1116080303090d050301030c09240f05010e060f0a0f0309120305070e0301051b07060605090717 80
    0x111030a0300544507000284e040c0c8ae106806c5031020740e0052070303d0b01d28a04040600411400400c0540d0b107070320080480400301040341722040b169400b407958000300850080007030614400c20b1a8a401160071f5100021101244500454442ea400403120a4004000801c46403080d901a00605020396040b030181d400400109540c0c860305050b40c0c182c2d9001c7d2262420014080300864503140d101010010521600064054002032505a500502031001c0556980d01d005503080c0d03d044c03034000c92607007045020001000815032443c2010207070780725444e010a40c454010302e61001e100d0101c0500c02d1480c20b044000608003040b0410380103d82082e01c070308142505020400803103001d25680c3e60728080c010000d540b0681c1c820f2029011134085410000760844a60301c031711200b204400e00c8000866a15820b20039007540202032074914500440003440305140141144090b0540714910100041000c9100740802029070081805008003516540031032909103030041c6110100326031030707100c9030010011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 96685234 1250 96683984 96683987
    0x30c09041401030503032208040e04030807080402010504051e1806040b01020c0a06080603030f040906090b040c020a0305090a0e0411150703020a12170f01030512250602040e16030c 79
    0x960b0480e60084095800d6546001500c000080f03000b00403c81c541098000c500002c1c40b0030080c001410351042030f1815440d01d440d000c0c0c00010083d04003400d102d541410800140c0c3c0c05011101501c50a640000d855400701c03200c8078440d0845c0401c2540000740420014844003502c440c00d2040b403048506212000d809401a42c68030410b154003500503035501414006507020b0680c01c3e41041014084a10b4044007040c110f1103500190404a102503e640080100414500621580c210110b40800140525a8000c0d41c0d40d0f000103001802c1c0140854640d12940d00c61a4101c000c1200107001105450145000f8001d0740c1c40c882c007103102d0741960100d030450b5224001540d1034203070b00d40c004048540c03c6803501c4041407100342c03200f002c1044541d171850b0100104110305014600b0807102c2e5140d94114548103041c0005107080e80001c1806101101094002c440c031035900e0840030072010301070041401c16a02034401c54001c4030842202c1c00c10300140d80e0f0524540e01c0e4406441e034040140d050030080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 96686484 1250 96685234 96685271
    0x17090c030607030903140708090909061501050a0816050c120c010609090503040311130e0d020c0103020c071e0314060106030e03070210080717010602070609171c090902030c0904 78
    0x14060001146c21200800600c043c0f001011010b001d25081d50a1240580020391000001c81c0c950800b40c00c03e8007401519403c40b44e481c0a50f903405d00f00a814083c0340c14009001140040c0810711507034603c441c18090303501a50440d042c1103403a0060380c515502d040544441603000b40b00c0b115240d0310b0070b03000090b11240c0c0d100b00c141c982d41c0480034618040c90b58030b4990003a0441402907a0240101d5240f8403410168424442c0070030f640c4001e054078403034140d4080d06101c05500b519043c07500420084048090104075003007540c40200704020021b80d4250201018a0306030801005448186900e5100b0280020010304032482581c1c28004181d0380c60030035841c1d00407900c0003508480301e1414a10882e00400c4a00c4d880102840c0414840c18444440ca02000d070a034000400750f00561000e10600c0c0d800b640c0803010f0656000d4074807a10745446552651000207200c20311048011811001c041d0707200308405e50013131160010640d181d00f45481c29880c1c81d4002200d85104a1070000d1100702081c0030031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 96687734 1250 96686484 96686501
    0xf03050609010614010c030e1c060506010807080106030e100c0503090f03040f0303051b01110a0f0207080703020f030a060c02030306040b0405040c0b0d060f0801020702030705010207030c1517090c03060703 90
    0x3410b44c0c15842c00100568110180141c210107200c0c2c030105143d00c83d10707201c140b01034240e00840144102c2e411414040229080648600e0401030a2000c00c84803642020702141105c0f200e20340000c2e4103040000c1c0a040203031f5140301c4201d01d410410560300c0c0c80e40c0200658020341071207050300c0f60300040e030ac401a502c3c4100c1c400d490241c3d40030302041000c6401b80c0044e10981e41c84882e1001da24400318001030842d2601429001c1e0003c0106034074004640c84803886c8800d43c941d000910200b4140303000709546044503c0700a104a403903100c810440c4d281406102445c81c1d11a4051161700d40000c0013030b460350412540c05003d94a091800c03110b501d02401500d0003135130062111900326051044100c2340741c0c03050310000c003090b888180005281400810000041c07030301c40001a100c83c0c00c1c0c4105820580c0035031015045520108003440440c00c28081c9204442004691101042d41c0035030656854034405280c1961b03000010400501c0700000c1044220a0000c4003560700c1070341d800b80c040d400c450244 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 96688984 1250 96687734 96687749
    0x1060c05060f0c0705010915051f09020f0702030601060305041a07050a0e0303041701050a06050a0e15011b030507030206010618090b04090b040c170118060207110a0f030506090106 79
    0x3040880d024009000d0a50741020042003520304d0500c0b0764940d2401d4075000c0c60100c41c40e06031200a8900352003903104841c1c0001c440d40000034500001030389203075020f030503000d8800026030008010a100280c43c0c100c8440039409000d95102e90fa4580010b0010001180c0c161160a100c1080f001c0555181c2d0001c0d201e1809901c038242428109001100e2028003042501e425100c00c200c04501030000d261011248429030001180d50b05e0161101c40c00d58113150b00140c0102d60081d014050760060a16150740044008480b102010403800104d408a0690510700e00c0c00488007811014183d1200050000c50300a40032a503c070b1b41c1c1e403542280d8030387d242c0c6d074100b28a015100062220b44040d8100d92030f280030041c000b0070209030305d485140036100181c80c00c80e100e8450480c104044501d244585411200740c270000c205004404080052460100e030008020550000e5100104911031000b065100d2024002007240e507160785200750701c81414001929140315440010741085014040c901c00d94410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 96690234 1250 96688984 96688993
    0x7030b060a05030115020a05030d062303030f0f07020604030c030b061e06070516090c110a030807080402030f0706030506041a131d030f0d0609020307080c0a05040e090a05010501060c05 81
    0x2405000c03803117000d0141081045015079007040010400400c0940030450038003100181c0c2a1404940c02200c91001000100101090b1f80e480d269980c084246d44000000c484c1003a03035251007007214601481901002940080e0108000c000c0c840f142d5000000d583c428410819244c461804100c2003a95820034610306144611420341030742043c0c0040c0c1001c40c42941200c3c01d450114600031a02c1426400481c48545d442502e610308591207604070003280c0150000c0d003203121060300d0003845044010400360500050700089000c54404100c80034520203610207131740304c203510b50000801402043d40c0c0f2621590034082059850300050086041142c1c00504618464005000720005441084940000721945445036411504244004c0502030f008203110b641d03800540340c1d020129240d0390000c0d01c010f88103000300091250845030b0300790880081e5402d1a06c455405004445130f1085410111150001c0301c1030081510001400400031031194009201a80c0c0307914003191482c00314007010f442d82c0d01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 96691484 1250 96690234 96690239
    0xe072105161e0e03030906030f090601060507050d0804080408030c10050603070e0406180506010617010b090d031202040b070c08060c12040305070507051c030206090d1d03031b0607030b060a050301 86
    0x34403940240d65101030117072420480050000354041e0400c40d5074034110000b40c410806110800d200340c0e40034140c03500308a0b0030001552582682d840e030b180c1341101803115050105051001c2c1d80b098070010070840040b290350b00322400e145500d50031941240001c881c00c200101c0e003545800318124080c2c2c2d10300310307183c003840d03407503440707060282261010340c040c0704d54482e51990100d0014014207010344403644400d005000d084a542c000244140c3c0000c000c680144002011650380f10b05284000da01850720100b03030422251644000c1c4103035400304c0345141d400109039040103405900072003260341c10019190031340d50f00d2815610300e108168444040d95421400540028012030281420f40e01a4080780c10941e240e2010447c2c0440c0d03071080006d10901144400209a0704100c0e0b10f51010814003e4000d4404c03601c1c01408026030707019098105003800342c80b503100340c500708213503444500749444c1c1c2180d250a010801d0b48a000035507200b00040e081c041c01c81480d003062402c9983d8018075580c2c0502d540e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 96692734 1250 96691484 96691487
    0x1302040602250501020c210601030c030b07050a0804080715050907260303060d11060a030509010f0c0f120b0d060b120303060f0f040902030a080c160e010e072105161e 73
    0x404103506980e0148500b1405841f8003400c2060300c0c042d40c840c2088043e914210308160360310500047c45207003001410840100c60640c41300c40c00350415404100c450300c50000e803030f11002c0b415961a18204980c5488108400000e00268001c119010f200c2c180c54030369600080309001c628004104149640100042041401d060318400c4010780550380e01c0c140b0720030100c0021440c0c0d021401030030001c0d0f1214141b105440003885032500302202d489007000548103034100901400c0d450582034042c4051160b071100c00c0f5249420050881c0c41c024076140d080c01891074000000e00710710941c0760042d04820000e071280d282c00400c4074000c240080000e165102c003102040340c800a0740744003d4000e5220070400c0300580f030030448424054412144103032103c021141c00f51410902c8205580c0b010340c2c101c070820610800c0d015560649607044400c40ca1680d814005603152019003040080d000e500d182074501c07032150369124501890b03c602040c5031002c8a1a03085a070f40582e810b508010041f0200c1d00070006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 96693984 1250 96692734 96692749
    0x601170610170712260c0a080306010203040806100f081204030f08071505092109090402030a080307030609060f0b16061508150105010203120112021302040602250501020c 75
    0x81014040302c00303da481d0499034403c2000f6101c01c581040c1ea078045150048282c0b00d403e0041195903d0841c10900550300c9a40d030307110328580240c0205400000310798640d1091003100d0203440b2030390481e01c06082c40c40d004018180d2a124502084062003404107503201c011511041b64801a0350090410303041d1307244c516111140309811110b51804110010004a070108101c0e4061690400028a8901090f125007406016548000d0100c940d214841d5941ca018080c4c840c00d40b803e40d110003082e550b62000c64a08920180040c09101d0041b042200c855450781125003600e500002c103100c001d030740380603c404044040c040d4415809041c001c0301c003510340300b050300b408443c0a00e8000c01c1e4442c089140c2d8a42c0e8429402c003250300d40291018008030031214000300e00410b401e1008518040f581014500c0c40780c0d040c0501c40c4e8824140c4d00600655481001c080c81030340d5007e5085648590328800a940d030425071408012050100070200b010300d400803100302c1118010380284c00c481c00300c0000c20055 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 96695234 1250 96693984 96694019
    0x20306070e010c1e121d0415060c08090a0b030a0b010f0e0103090303060e0c04030605090c0f060a02030708030c0a0206060307260304030c0e072c0108070c0b0403020601170610 77
    0x11100000c2e0503402003585d13200360903484c5000341c40c0c0c401503100d49242085000c0d07251402da406a03080c4200821007040700400181223600d0344c40d1000c0301c1d2000d8a403445043c82400c00711540300c000302c41e0118071000e8400003140282c0c0c800000300400030b980c500541d0b41d41c00d440c0b07e160209074005820402d40d4001d404c00003100340b10780342c0024015114041901041400d4408042c0ca80c4040381c24020014140300c1d490308202c000c0010a40070351000001f9407215412811907006000100d004000f5500070000d644199503c00d40c804d44078a07200280460301d400200c4100c005204602c0810040d08000c10380d4000e5500f400c01c0c4e4260000c6c3c1000c400281c80004101e03005510042100102040f040650708000d02030140d2111510305280c1070082c080c402c100c0d003075680744402c1c052074071002c030301ca2120341350196007824035450503503c0100560703441c4203038400641080301c1c1c1030030802010f070301041246c1a50203800802000e1900e900380c4503034920381154805131011f080c40b420f200354002914012003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 96696484 1250 96695234 96695273
    0x30a0b01110106030c0f0801050610050a050c01050708040b06060306011e20010c030606090609140604030803090105040b090f1b030304171006060302190309060e0106080307020306070e010c 83
    0x2400710500c0001802c45500741d00c10750381d0a0f01c40c8405c0c44481044803149009000140c0281b0050074980009a01d1200040300e520510000040c07040c41d490085d8140c07a0242c0060300200a140741101e0054080402120100d900c06448000690f06207465000d40740903401c103a51b101034064110840c40120090130084005000da041c00d07185068012144414107600c0b510000b04079455001b402809a6004e60844000c3c032559020610450342d0003e00e840448105201504070402031a000c61680c0c8034a0b04040c00800d4000100118110b05400c014003480c400d22203c43d895888848007510f85644c9a5002d00c540c000114041c4031300f000ca020113140d504010103a0b0703d01a41d034202800100316501410000b40c02c00508600e8054443c42000e00800d002d040075850b00e000001180704007111020303000f051654904d046020321545910500c034010301d640080050703607140c110b11503aa4010b8282207200c2d220320b00c001a14544284001400300e101a1540304030300020b5500d44010ba910041c02d100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 96697734 1250 96696484 96696497
    0x30c0206090a0602010e010e0c01170c0d1a030c0102031602090a060801020c0d17010b030f270309030123040b0711160501120e19050a0507260601030305030a0b01 71
    0x1080359840a860b4002031a040d00002580b41072444002d0a544219100b9480d640110580ca40c5d03d0760483d0981204500042c1607003441c0d901c3c1104200180a01401c500e811494415810108c1010a0303940301c1080d0210101c50030a50a400120780d01c0c4a00304ca008100401c2165480050414154203074100c62103420101c0d649031103003070b0350742240c08c5004142d40e00d9001c122112141c2e0b401c040d03a00e0503a1020041e1840c0c079814404402c80c0f601c000360202a0704c505180c0000c0c0b010410380c2041c110300558403003c4540c0c1c0501804569a900800030382c40c802e5213408416061504e190140c01080e060760102010f0703640d103944a01401800c01003640041c00010018484103203428008c15401c030b60740a00780c103801420100010002d501c02c501790b40c1c0d500e1a20580040c5e441c000600703103071168148001d8144141d400c0c900300c0d0070449466002040c61056180108512214001002c0c1030710b00c0c2d0040740048101100956a1410203100c0a00490000c00200313000c5510b503004402040c7c81814600d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 96698984 1250 96697734 96697747
    0x100e0d140909151302040e13060b030703122d1110060b0403150911091b040306051803120f0402040902060d0b040b032a041e0504021507050307030c0206 67
    0x81d0020021500c01003541051103d0100e107240410f204845940d401408505081c00d220300550006800780500c2d0003240015000700030030915820050102401074140d1b91078590b0791070104800305201100130049502c2000204400080b4241c22160012004078a4800c56090209036446400400311404500a01110b160742c4031031350050070010809034007400e030354500c0c5041521a00014241d54408142400622004980500207440d6544c10880c2c105009841c1c580c1c0e090512000b46a18500c004000310700001440701642c092441101c02a921180c1c03699900001900d0b48240040e51500407120000300e181d48040d8541c1944c02480034000049080d4541c0000c3d0355500002c1d12484041d88803241c0500a041c1340c00350f6202d08509400a024030400100804001c01410200c44183c0801d030b84440569651604240d008000120104040032611107000c0080c0c10200c0b001d90081c1008204802a44500c20440d41c0c40b07074110024600707101c069681250400c0002070282d90000701071118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 96700234 1250 96698984 96698989
    0x20303010302190e13051915050a02090316091a09070f180b09011d03031204020409020a080d0e01050a0503061002070305060a020406090b070305030103021908160503100e0d1409 78
    0x82e000d00000d61409020300200c6c9865850705403001d00c00780c480b400844a038400070f40e000d154010201070b80398010680c1d90ba00000103009001ba4144203038940700c1c4116070710085180b811560103a6480040920004224028002800e40002c09598120103031200082c451481580381c0400d408003450b207400c45000f0340880848a20031034200542007000061508101d41e00844204083e52034914a201e041c4280d800080e128002d003041d8030340c5000140001002c541d80c55025905407a401010150255207541c5450760340c4003020b14910101e070b012181440300c1d602030000e44254603915901e451031555042d00b0700808960148042003903200d40c401c00300000b201440141d00c180265a001a251032602030000c05d0603205610018003a07100700103c202107a4020b00322070550b9010398110310082c5e622070a00400c40c1543d031040906002c0c1c021700c07111070010100a102290012422202c03108112503080d021540b00c0b0414610b141d1001c00260f1a8502880340100f41e50b03800e44083e8245002c0801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 96701484 1250 96700234 96700259
    0x60909050f071e021c120c080c090d050a0f050304030317060d0f02061201030302030307031104030209160504030602040815070215060f0324060a06110a110f061902060a0c02030301030219 82
    0x9217000c5003845882d11000022442440700e42001407a000807107080881076051288107558002c3c1c042d03030282c4020001c1c0031081015601035a403001180540c5234043c1082a12608980130440010f6404401c805d403172205130300360600031030b8005c3c40305200302d01e29074a603c600034240804980104091000c549a1000744800710300031030194001e10b03940c1c03421240050072a4508501c00810200a10050000d6210404800c0e40601c0751030545449024000c82522a0301540e440148414000980410a07900c0400c0c201e140e124185c08520b9603455500c03040c1e0302c80c05a4481d00c205007007500e002800a10b044400110301c51350107003d4032002c4012011200300320301410303001c4100040345014040142003404040006048a1600d00807050903a88001d0f00c60240b2280941100210084504d25544074090700b00300e50002404295211008400a40220020030000016010304000038903095514007410180040070f6000c0c62440c0e0039a800c210f02d4045e80e81000180d00049640031400418561 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 96702734 1250 96701484 96701533
    0x9030903051504020405060303040e0a02030c13060507050c0a080604030c0303020f0d0e120708040e07020c10081005090c0f0c0304080601080604170405090103020424060909050f071e02 81
    0x380040c1543c5081e00600064401c042d114501070f5004010400140c0b5078909056001341c81c01d0000341c0d80e525110710b141120300071f500016046003151351000800c16017242c01444260f07c00c2c003d0b01d040500400800850001900c18042150401d200040000e48100c4030480110300c203080040c106078015102040c2500403420542029988082100802c03108200503c0020f01c500b4030685002556580c05405004900c18280303c01204d4010401e1035000380040c0a608202401030a44100012030041001d00d0a071000c1141c00d11100c004600c60034844042c40c8220402040b00d842c2400c0c0320740481855001c8107154a0500061001140e450002d2009500074001c6000038600350400341442e2a20344403108000c18001e4017000100181d449440300759044035011030780000e40070382c040e059020b44480c001d810355103d4014000440c005030822181030548810b0030003000b082e40c2d408144035090005030f403040702040c2c1c0d40d0380071141c1d0400412154420342241c4155200964044117166101e103481 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 96703984 1250 96702734 96702763
    0x1005220f020904060b07030905120f0109060b0906040c020309060d0204051c0317040210050a03020d050f090d021209040b03100509010209040b031606110c0a0807090e0a0b0a0903090305 81
    0xc401c0054030b058040c2c000901805c5a00310314100007035a028015000c1446420b000d614802025249003006100300403414011100a001403081c924010000300000c0448a00c200d0450740800c4140c02c05210340541c10a1a4008514042c000001c100c000d8221120403076001c1e80800011070281c4801c030b410424161050f8000714407030748514001c1c00c00710b09954102540315009003000007594462031131130060709450070322907580c2c14100380407030180c0308000610424504000500940c1c51030340405c148100503140c00e030b40e14100007000490322060b0a01c100c0001c4101032009035042e19060b8030010f521074000b4220303451945903110076816240121501c4000340d5010814000d2810207004020000508501034010100711001d88800d0840078001d480070095681c07000207000908103e801b069900040c0040c0b031490340e07820400e941f102680034413031000707060208645c0d03240700000d003105d001ca030f014132298090795801c507480c4020402d64505804224a1a0b00000424402e004103040460303038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 96705234 1250 96703984 96703987
    0x109050a020f09040f03080612030a0f0e0301020a2c0a030809130203060d11030c15070c080c03070911130603090b060a0503030703230a0203120601081005220f02 71
    0x40c0c01086002e46894040354020700c510010400001e4407420440443ca030302d070a1001040c0c8880000c2898118005a2009a272200040d40c01d0301580120545803906290b07074490201946d1001892700340c2c01098003d5012a4400e4420303c0340f9140d0400700380d224031020085818072840800001c0d0843e069034001d5031715110008101c440780c10300c211103807101a4144020347c07441c100040403c01081442c00e000c0c0903200d9904c06c060031542d06001c15001010b0051402c3c070074001c0344909901f244d02030b1008a0b124410010001507018001c40c03d003044000c000c1c081c1c06210300e0101160007800c141d804034039601e40c08220340c011540303182030101d002d40820365001031203484500d0202d00700c22014089070302c5004d14000401443d600041140c034080e80c54540000085500d0380c007128107080d1603503405502d2001003103e1f103c403035000028044004100e5800c00203611136030010740350001d0583c0c0f01c60344020340d52410b000505011001c0040d070441000300c03545000c42000880704a400c010950061a0f40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 96706484 1250 96705234 96705253
    0xa02041401080c0a140d0314030c1c0501030b0c0304080d050109020d0c0305100b090301020f040909150504030f11190309080f0304181d030307090501030e03030712051503010905 78
    0x1040040750103000050b100e80104c0c50501d000e20001c410f020016500c1081c04811040826101e03407a0400d241c01d84003103654a03410501103c1d029a0040200101c540388504000510b4900e14000d46040366040398540400c0d8850904980703641c0c0c1700500944040c10304000800104801c2d01c100350080c034140c0300043e26211540800c10a640c5080251010176042070140310000d44180141c1e8220741d4071307200c0da43d0385004003004280a070048540c03400c100c110104001031242410b40100381c440d84030704903060958004480000441d0025100500052404c2c1030140b42140142040a60100540c0855241c8107404c1003807038201c01d21a104070b0005035140c408108100d41005285551070526002d1420325083c00700c0c1e00c1040c450030b4003200a10780c039190800481c044030008815500d5154055907620f1034003010280c40a07006200c0c0900217071800e18800405000071080c1da00964695440d4140c1409414214025282c0a07000302c0c01d1a2800030071003080d07a024442c4940c44c900c500040c152842 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 96707734 1250 96706484 96706499
    0x6070f0c1410020c0402091224090a0b010b0a1704050a0c08010605030a060b0a05060a0507050706030c053405070306150605120a150308030a06050105190c02030a02041401 75
    0x62400c101e500551402000219180d008a10030782010803d0700e00680b20100b40c00004c103400300d51b00c0d5002c02030142e1401440c0b01e001100501603030104c0440f92804503150080110342ea0b4101038405040b0740484801401465440b00080440c40011700d421186070342d034042201e01604060314205c0381540080058810800d60000d004010030760100208480c510744400320b6150300b281c400043c01540d8640c5201c529507200072a4001400000d01599200d0440a0003c0e01d16480300ca0103640718415200e0000d640d41c80303070040c0480c000e140d60b54903040056000e042c5941c984008450003102820111101d480c0e88c56485658415010300020700b1800e1860600c0c4080714041820f13003540240c6200d003405895002400c4410210030703031615890740d0b0346916841c0000d04034410351800c11441c0780b900005004040c1e024501500340e240003001074640e520011f40d042d01c038002040a5030740a480f040c448880c024122802c0c8507001405841071240c850b0b000070101c460301041c007090b0340d40e036100501020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 96708984 1250 96707734 96707759
    0x6023a0b090105030705060702030f0d05031b04061202130b0a0c02040501050a0608160908010504030309060b101d130905010903091202010203030114061b0102040617012306070f0c 79
    0x1a409560080701541000003103a154030b95402007600a0200240d500c0854030204a000260780b503e070103036a80c0350100d400080c090342c000d403564080403582100c02c2c020a0186801c9400716515900ca0300c06d99916409448043c1d00194007003034a0180c98880010391580540c010500c043d00d56469424403c1a841000111103043e0045030003450340300c0060190503040400c3c1d54018030304400001c104000800704984440c450740103c021075003800c3c144020181c03d07412414074144900806d1044083c3d0303200740200c40f00c1400d000e0001401068900300c000420040c2c848032480d0290401446009160002d4207441c0a01402c56207030390740e00c02210901d83e0100200024258081d0884150401038000039501d02041c042e40b0203590f40100301e14807a503030754422944020144940f0000c031082480743e040c000c0d00140700c0c0310013081052031503103801d960700800c01d4180c0d810341c031445440101071100c180d81d1103c101070558001008001790b401003800c0403106141644903503464512141441c0021880 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 96710234 1250 96708984 96709001
    0x61305090a020d020a03050d020304030c0b0c210408061806060307030803040201050306041409070312090f090507050f04030b010311060306030a0b1b0726040b040306023a 75
    0x106854141402880140860300e1554203030110b5407141d42c0d00f000d00004200030503507480180548a25102044601d4000c0040c0003128050902905215074072090700a0b60f02c180120101b0541002280c0448604403540008149800f1650281825228040d03070786011800d0382e00c21301210a240c0d0325100d11000708402c41e4465810303005401402e2550740d810032140405000281401070220002c6e03440d841e10f07400f00b03040c3d803420548198141030011000b0780700e500d42d02056812404441088203070901401c8071104845640307100312202441c2240610003090040c1c40d20080160420070040640c24207000740021750f008038855080d5515500d0400e240103160501680a40d41c180100a000d5501041407041c041e007208a9643c165035803080e00321300800200e810b0101d02000f06902d81481054601d400c076013301142100c80c0340c201000006c246024502c0b41800b0164104403e01c0051015000b80c643c071401354440021501d9213a080c0ca02030504209903101c120a03042c0180030251003030192410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 96711484 1250 96710234 96710269
    0x6060c05160515090301020d020a03050915091e01020d02030c0a080a14040f060902040f0c03140609041203090c0b03090c19061b080408060601080109110313050c0d0b06 74
    0x2070080c600b00100d50092400065842c280303201140c00d0f81a0344080d011110b031842c00d210210740c0c503000a40007400400c000d5601182a10420320b04181007040c0c1203245010300d40800c01040a40181c105c1c40c2401c01c4a801200300b155001d000c1041140000e002850058840301d0f451911a24100b00c0208a00801000740b6415802d00080d4000705422908440e0083d41000b030000b0009502c0c02e0090250080c2030f0000d410918081413142c0320340e1075134010300d040411540c00b03100f0092601950103884200b61303070302e03640b1020300400b1a0004424025012003142c4c10300300440e4140090315001d003140d5103640b11790360031480003041041285080c8025038000804403034119007200740c60f80200580c14a40103100034009129002c00c82019030102041526500c40302c2c1550720b0303031a0003006803208400d60b90036000c510401c0012490400c20701914001c1034070300c0402c030f0450795800c2c100c1002d135010100aa902e4054544406070a480d05644046c00702d001e00342e20203450030a9000c1c858081502c220960 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 96712734 1250 96711484 96711523
    0x305030105012d0c03050909270303040b2d0103050703031416110301020d06031a070f08042315010509090c03100902060919080c010f17071206060c05 66
    0xb8241e03e842d5403100124100e41c50046030508003403400b41d4039442204e841690040d0002e0401c207415550300f81d01802c1c849402d2510b07107100072121400741d8900054500400c7e038000900011b091030f4503045c03801d6100382c840754090b40200300c0f0141458030b03035800e8005507a15000301e5801d20525401000d000c20284880e44031a14044401c07440307110820151038014586512101c080000360340075015a10321490201080140c40c0c1d991070002d01040c501c030b80c082071040c52180000d00c080c0c00f80e20f85282102c4541c840c00216a00c1e90b5403413180c400c021160706401d0660090807500c20307074101308015600344207a0549d80c00d941800200302c80c20000030702d0301045510101070740030170b5140807600a50012800f400440d0202081c8009a003a00454482580110030010441240612f902c0c0710300c2103e030580c00341c8881c1780c10140119154080b5409007800b00e000b0340a02c0d00894410540a07a001d019407606900b08038000c03583d101510001c1d841840028401d81c140d2042c008240000319020032402d0307010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 96713984 1250 96712734 96712787
    0x70c080327010e1e0415031106030403050d0c090306020c03030a050934050301020a020318040203060a050603040302100e0c03160e0106050c030c030a0906030f0b01090b0f090d030503010501 83
    0x20300400003e40210f014068044000b0800c1081880355482148010004e0050809158071405032408500c000c0d58040f4007a85c41401d141880d004990081e42c01d5981c8901d080f10304600c00c0c0188c10003040c05010480c03040400004a80c0c42e1019200010940c0041c554a0510f0003154068070310192400f1051f0300718445401d0102204004014841c0300c010741d450440072125601444001d4981c0300307075015400054200802680800101070b0507100c1c1040e4404182c180c8103010032404100c604170341214008405211a240460103194450301c644102d03030781c030250500e411003520b0110001c401140d000c0a002d000d80d10302800b4a84030720a8032240101960b2900102c40001d070300610980c001e01800013105500c010342401241d9264005034202c80c0d8561400c040100301c18280d10031800064941034224104000b14000c1c8041300c00b05035502074807070b41894060040ca900c40030303890820040c00c100c20340b00d54880305428003049009072a540e03265072500f8005042c0000030b520000321104171207500c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 96715234 1250 96713984 96713987
    0x908180a06021b030a14030408060a0e030406030b03190803010518040807170403050307050705010908150f07030603061b18030528080d050612010e07051302070c08032701 75
    0x2d00c0b920215403c00c1e4104010003c20300381a8014805001d0034800b2805c0101c41e000000100111503c80302180c1d240d5030741d003150408650558034040f009400410041100c6403283c0c0107041d86080007030940b45147c0580803000d4400e42d52044c1201d2890011004001e0703031038076000c802e4118000074008a040d1420b556140b07050700c69948018040d8540740480c40324040c0e06815580615400b108032a07442425040140e6141d00074850f03140000c0b2942800b0880e40d20110750810b07007078003644001c400c58a4803a00c075068510000c008a0400d55a8030000010854900030300070400fa84500c608016005020f0040c000c010482650340036200401c1e0420000c0ca000400c0100aa020602c10075680a000c0200c10880e60002d000782c840f40d80811401e06410855000f54064201280c00b5a541490905001c5c265490102415142d070004d1004215031704108400082c40001d41c000149040c0d6250780d90400a102130b0058543c9500104449004014100b150a444005074955203005a00c0000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 96716484 1250 96715234 96715243
    0x30a0e0a030e03010f0b0112090f0206030a050f060609010c120201020906070f050c010c0b010605091804142a060c0106030204020708040e1b040b0c0724032f13090908180a0602 77
    0x90101a5909c80c400c038140216031004440f0f4039030081c416a56402e00c0720b140d10107170205503545081c0d000404045003080c40c0001c211104040182c455216020003603d5014440e04080520002d40d5000c0040264696825000704519403107180000c2c18141903080852070303e890b803981306040c424408400404034902c5075805044504600e0440d55842020020546843c0510207940c606207141c03040c4403c110040e04910b5114482c00e0440300d2103122045102d580d4010205030114200154801c0c5c28070341030080041c440c3c5501c040000c2051a035a6020600b01d034000401034816600102c0c080c800001429a01d81e00845030800d101c18007128861000100d10941c45046030301500040d81342076070802071105000804480c4007406001e01304065082d40c40d500e1191440c0040d04d000d1081d01c0110030313404407611140300002c90b002c000c8072500001c0c40300e9101411104441e07264520001d07542d442400364059940c840c50700241c50b5405525090000e026401120b03105080449060100380c0d40000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 96717734 1250 96716484 96716507
    0x10e010f0b0a0b25080403060b03060403080615160c1502030f0f0702010309050d2a05070e1b030c130902030f0c1303050709020c0c090106090b030a0e0a030e03010f0b01 74
    0x1c0b0381c1d96a542c00164440c3c00c0054204c1034400034113508004000d10100700301410440e4000c1600b484481c4000e01095210041103c0003008a841c1801007a814288100d040c0302100d51100b200b45002808100700c00540c0c00c80c002100c01101d540d009000410703c5070380c201d25240d0203000039410f00703a00c14107025860082c80e400c61010100800c00c1801e580c4603812200001c2d821400340c880100400e2030040038101c04600704401214400d0b0101131400420b5003c4500540102c0903011150501242070f03c1002d0140100d5812a20b4a10301d440440043e0000e5004401402c92955a0568080d44401041d415802444d010344180304004c00c040842c1403c1d135201c03601080980d5140e41014003014940e00c0e136000a8007503c280940407545411f203500801444d504a0708441414030401c00f0070190300741c24085d5100084061204100d820030780d03000703140c1082904d0808200c1a180c01c07409464484140b40030380006000e00a0b02640b42004c0c41440504201c09806110948804002904954014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 96718984 1250 96717734 96717749
    0x190203071a130210030605190b0912030c0d090e060a2103050f040f05090609061807051209030909090d020309130b0303072d02010c0204021e0a02010e010f0b0a 70
    0x1400c0c105240b100e01e54250b4010301202202d042c1510082c02080e042c040c1c180210100c0241800001203203a500080b280c8440420b40740000800900400e0881e51003001010f1005101c0114000e4052040c00301600b825650580c0a0345440c0604481280142507a401380d5207906080c0030034508108003103007071000d010381c23401654407601e0101e60390711030003164910240c00441c2c00f20780392040d01c5040701180e0086400c0c0c44a501c600301000520030069071103070780c061074222a10040001009100b540300c003c07400e0a43c1400200300000c12000c01c200d900d190315400c0014500428a0307d09501034100300d4402c000c05580182080281d503c2c821007100500c9614428103c0100142c140c001c5804020054140c0f170b10f60700d80b803030401d020103054225511071952009040c10000c0e0092514014039805964420240c0144d400b448001d5000b20013100c260f0341400c3c4083c04005140b802481c2c5140715900000701703120f1958110b403c41d0106e00f58141c0c2c45083c0341102090b9904c00003d4403e64000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 96720234 1250 96718984 96719033
    0x904142107060e0715030c08090102130302010c0c0905070509040c020105090c0f04020c12040302120312010605071103070e0a060e060904080327070e0604090f080c03041a19020307 79
    0x450240e02e141c001142d005c202e295030340d000c0380410968180c110701d035032084544a44d0305503151041194240d0041900303501407815806c20030030141d1700c59082e00842d6401280311081a0b602e03410880c00b510011250b010110b04001880c045900341482040c290840703c1c8000c01c154286241581d0710350050071707945441006512181030480d03581d58102d4410420403c11a10104102013504850350010720041e8030404030352020700c82d00c00d800310468400400b000c0ea40001c5030f090074402d4034035801c01502034414200c012002c5001da10100100f6000c1c00b8101c981c88110700d46500d180082c1c0b80c1540201d02e40d00d0f0201c007440425283c01d051b050700035900000f60390702c0750394002200c0d010780f81043c001145840070b807000400c045d6001c983d06056842070201d1f040940c1e5000188410781e070558400401c03080b80d15807101c02059040d07014002d89000030040c4c915007a13607485680402041f07061207812202c40000c00240d0b403000c01020030025100d60000c0d5003480343c02d4660345100411000340060f40c008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 96721484 1250 96720234 96720251
    0x80d0e09040f26040e04020f15030a02031509072708060f0705121003170a02031801051903050a050609010509040f050703020d03030f0509060c070303020c070302090414210706 77
    0x910f90032001c003100030002443c1c0325980c4400c01c441000040e10164001d51001002c45224102111031b401034030030b1460b0030703803650710ba14802a000b90b10040c200705950110921450003a0342e02105030b4007510540c1e49003160909008216400d98038448051804181422020081e0110100798958042c070718402d00121035035088401d039007501c64429104110003000c010414103000348516201943e000e00448550415050003e201c5032080040550140e032043c06085411500000013447c1d20340185442801e00804c4c4c00303010b03020090342400c00003107138481007003010003510341c0b107144d0b444441110b0601095240070302081810781c000c0e00190034010506140d40502404000e20310055501800c50b031508221400d00800400600004805103414840410303654000007884500801c51000154504599a9425030003075003ca245903056014890300040982c2d500039805118034011440c803005c03020403440c07583c102082e4400c442115201910070603101c0d650202a110110b41c003200c0082c1d9401d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 96722734 1250 96721484 96721523
    0xe010503041a090709050c13140301111b0c1c03080907030f0b041e05061303030e070807150503040305091203090d03020c030d0504030f03050a0c0804080d0e09040f 72
    0xc1e400002c4035100c0c00c810003072011203580084c40c3d00071151041420031082c2ca0303502c580e4440d0310849449040c1d0900c1c080702071210001800076912807500050002a83c207241032500810b582111032402142c040d2030450040d03480061019400d002e41c00c444c0e070151895101c2c000410100781d81c0740a41009408000150210410001c542c00745070003000780d6100000307a107003150031030b00102c80469180389108100400451500000c15a041d80080503005681c1d035414003505032601c0ca00103804054891009010a842c180003e4016140d0003014210143c00c1504c2e0313014050503c5441002c01c4420000c02004c654008240d0781c07840d0302242d5a44170f040c0a001e0003441e6010704071400c0e60050319076070134100301900095146c0340381109130244c1d601c0d00d00e0301c8000d4640340500d01c0701400740c40b041d144940c00244103a001303284e40203950815a44262042c2c41e4640590000d4110142d2a0300521011440c6504010417503807034801110350b0101c80c079040e5135000c0b211490040c02000701111144500e11310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 96723984 1250 96722734 96722753
    0x206040306090f0204142e051206040201030c021b010311120703050906161403070207080304080102040608010e011401030b0303091e0f03010203071b030e0a062d0e01050304 76
    0x195000041400511050f0a0140301c810b01d20390120710540c40d107102040038188215003180700d62588454800e001c0514415002c02450301c00c034078803940d00e00c1c3c6001724581d0b0f505800300e042c0203003108c010301840c5000e10000d030490390aa00d5042c10f40d0712407640310b000c0d44950104143c5480003841d01140e803111492265100b030249024819007100480c5c01c001160380d15500142c420030510044820702d0f15051440f20620265400c440c0005091424800d081e0100d84d0095030402100d2040310400c03655580c1d2607081d500981c10044d1140d40004080059941c8584100e0142200020400d181d5150081c07040180180310030482c141522030b025000140d80c18000d40f00c076410701030308201c002100954130780340e01901104000d20942200c1004a05414144243c0b0f01c40e0225440f1007444004640d070600d281034100c0c404408114103c086005c0e10b44400a4100c01003000703480e071008402d00325024200e41e803800b5078070050100e034003400820295800f5a01e80500d071428204243d880c3c6440c10300d141c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 96725234 1250 96723984 96723989
    0x30e0103090b0903180f01090e0606040305070303050307030b1012090c080f0708070f140904050a060f1b140a03020a1202040b030712020708090f01110a050105010524040e04020604 79
    0x2428602400c0000c503034000310045c2444d5400300700d4020f1080f086401c121407036030854400b0780040e0a808060011414000e8140d07041000144404d041550320740e10b2a28011040e08124001a004428004400d415000c7c50300f092408458003004030a030040d00420220200c50409036082d2030f40e4a01003840318009901000d0044441039030a982050080169110164801c551481c441d2080000d482804568038030103a40c2040740960b03400300c11b01c040284011300038106491030f0180304034080c000b40461041d00401c25840b00d02044020411171107000c14038810b403a01040c0031000d8100d01540c0000421141c252203a8100142c5400c1900802c40303902403030b2082d05012034400140801d000b482c00020310311840e42603551a8088054001401c2a8001c0007002080043d040c094004245003101d1000341055061500580d200b42800a15180c40054102610355954500040c045420425940381c009644100800040c5107042c0400c110b511540c400e0010780720441001c41d04658904044400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 96726484 1250 96725234 96725243
    0x140903070807110f18060102101a060a091e050f010314040326010b03042a0b03070507060504060501170c0303090411070506010839090604060909030915050c0604030e010309 76
    0x91203485c01c900c03410000140c072954098481e0300d102d4078021009004e40d82e056052610411000d1000406001c9150441b0b01148203012500c0d10110704148404440041484c1c00152004403034545014040b8a50000c101c00d41010f0904207400c0302c612100c059203402c80c0c0d052501c0310f84450b907201c0c0c4400d8032a002c0c140c0140305121200005800ca00d1102440c06280a40c03484501c0c420f95400001800c024019407518040c0c0e40a010410000102c02656016410341071042c90411f450b61441d084410031601241c0d065692390060101103840707200c00a00031030581c02403081402000010b9a0ba004200c60988200d8540044007900000c102c16165a030f90f1081c02c4541d20758403140555218072103540040e0352012414403090480040524802da203290b09a000c64030010300005108280c000201040e0300203440b4980020340c80102e2040c1031481d40241c0c1c401c0400b90405824200f44a420105501000428840f82d90f00d4040400e2076034115038941008803988503050016809070482110140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 96727734 1250 96726484 96726499
    0x19140c01020c030c06060d12030c05040f080a0c0906060518060412030c03140306090c03180d05040911090f0d030315090605090708010e2e060201140903070807110f 72
    0x30076001c004050b1015900004c2581c05030f0784c5010a004000a00080c040c1c46121a84c41c0c2072a0b0900980c420a0307c07468070714080386002d40302d94090310000f0096004401640c080c0c4100d200788803542c0c406002400f4642c406115031443c0c61402011070207403c0010301c0b5400510008080750f0b856100700c0e002400c0001c1990980322407420042c0a4903080c1c101a00885c5107841000384003039046040302e110b40310080101640e900c541c14424810b40005003c01c50302450842441c102c0c01702005550780c8246e09030345aa80d00c9080418007015205001400d14040c142440101c03140d60700d0034010104d0480507a07034514010b0300c03414100d0180c0420300d40e8a81240c541c0d4030108402d0910b400000556100750390f4500c02e5240c820342120318150900c10200300c00d9203074010400014403c01132085140305030030150202c0c0e0085d0385840400c506a407240002d41c0d900c2d481c0d040031320131000307405a024250304e01540c01d24242d80c841c003841d0f1007504401004c40070070805072041951203607981140a0701c0a00490b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 96728984 1250 96727734 96727747
    0x9030b0103080c10020c0a0b070309021f020106050901080703080304081303060f1a0109060f020703200f0d050604060c03020423120c030714040207080a03050103030906030219140c0102 81
    0x5442c50ba215a5002940740501581c01d0354004c024001c40d04c00c0210880240707040c0d43c890b00e03008000c43e400303040c40b420075840310550800350b030b2480141d21501d003a111050443c460198006421100c90383d02850055180c3e5004011060012a20780c2c1100d42040429949035241c0c90100803d1188840d1031646080980380031040c080350740d0042e150804040c508210b00c0582c40600c91904c0915020940050700c0107006200291007114200840e030900d00444203001c0e1203130346507007600c041c55211a078000c1d500c07000c1e6640c500e8840c1d20501501e10507528a84601c8080e11426200c010007440a40174541b540e044d4501907102e541250024020900203942025000049100b5008041459445940c030b500c4c081500100100d00115521f10040060540320b103005200b020103252010890350090b8203024175000b1900e00c20040092a441d40e800141a60440c90040d108850300d8200d07908140c410b22500900f151078045680e2070762107500f02420000e00080c64150700e8462040944d4880d4000b0801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 96730234 1250 96728984 96728993
    0x6170c07110d1103010b040513140c0303070b09120403150e0c1e03060609010f14030c06070515010602070608010b03130c151214010b03042a08100501051302090109030b0103 76
    0x400c90b06880c100c0082c03100f45c1b850300130030003038820a031107514241840301e440c4c2d0001010818111101c94410094500d601040800281540c01900082d01c0340450f60042101030001130101070034030f904081132a8282800c5032140c1100080307681d400f5107926561200c110703c1d12070400000402d820028601881c0d14460700341c0c2240300c14045181806441500d006c42c10380c0c501905a51b0603a200c1003500064149840b0b560082c0c0c680000d840b40d018040c100d1100990340b9020018401e071401040240f11408117540703880d621400581c000c004640000c80103005032544003000e10304413402c00304403d441e600c501e440442c2d03d03840d2030300042c07001c81428400142800440014084010303191246841d00c1d1000c0754102c2611020b1000004c01c89841e0010300510170510080c64200303001d0f910a164020150049884070b0200f541c03100c0c01d81c100d03102c1c1089266010005265140c900d608144500d500d420042032403680c1840c240e600c500c2d0041146803040e4800d080e00401550402981c03e4035507520b090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 96731484 1250 96730234 96730253
    0x30905030d0c0308060406060e0f0a0512060f070302031e1e0106201504030311190201060312020c0306010e09030708040b090a050901031104020f04051e0a06170c07110d 74
    0xb002c07004100c4440000783c03d441e080c410201182d0b40c030b407541902c2014040800c2103842c0d0700203c090b444014088040341c0b5803960648980c881d10144001c3c0924100441815019130b0300800c03203000c1500402c10010a04060004d0074211100e5142041c1c690710740c403801a4401c00e09004805844d034034036000003000b07a4440c06940c00c440c0100114941703480040e946d10380f00d0f008802254980f48a00c0081800a4807951084a100c011951204d00f0401400c0d10382c000400042c41c0200181e4403401d051051001e035001071007403141240000c20710a032400340440e0b00d69005200d070160b0048018002135041ea0144111404c3c00c0c1e012460660300c64464045042e1f0760802001540603541101010441c0c0c100292154180e0b60410f4420903d0180007007004065807080c0340060300c01e40c0600c40060591a00300c0c2d401c0303031300d0003022a0314500304002050100030713440f640c008800c010304442003d501c1e0340b407004a9500440f41e06d450310b6440401d82003000c82d01040540040c0c00101a007004014400c0408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 96732734 1250 96731484 96731507
    0x90b07060f0c050c0714040902030d0302090109060305010e0f090c120610090603031b11120d12020f04060c140a0302030705060106020c060a050703020a1e0204050a0903020613030905030d 82
    0x40041100c072100b8070302141d081c09091000c071042d42c4400403c1c0700000c81410000c080c034030000d102180c208a50741c040b90034403c0e804048400700340c000c99244000c0d0b0f00051b800e4054541803070b04100d55894900c10412510028091032082038199000c00d17040b00c42071041450000c4050301610140290764070f241e07a502c0003140c0c0350008001580c0003065000c414001c0d0003c903030300350355102e51510007032a22000c81c3c0b1098004603401c60580311401901e41300d920145040d50848009040780c0c102215001e44540c02d40403030401d14620402510b8910200380003a2810307101d00e80f030148624162840c10201010b500c810208403817217000d0700c243c101a03000000b8a05544203000340d541c40c0c1d99405090342e80304040f4200582c000c800f480001d00d058400c0c0007400d01d6074020300c12100c2d000b945494111402007021144000503000c6a0700000b54141401599080300f0840c100704505007003600c000303403160340140030402601005e030910002e05104d41030250140070010142c400c1a2400c880c082c204a00c00b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 96733984 1250 96732734 96732761
    0x7050a0f090e0c0f09181e0c03120301060309032001020c1606020c0d0f0b01080322510f172a03090307020117100e0403090b0706 57
    0x24250b0303101c00c00b18031810a010040d1441281ca101c8504003d4a4000101168000304807031894001c0e60000304a5410b40201c42e0294640d4a065089818288049629600c1c085d500c41100c0042c0c403c0c0b60070481c1c2c11030301186000140203246243c215901d010500341c20510030b846400c04010302ea010b60080048203543c0084541c59004140d0010501c0058401c420140c2c00c15034410b4040d04125810f104070a02c11741c002c200700c1c8400d80da82800b5030360a811145a43e41f012a00032140c000c40b41840c820580403d40c078450503442e0540401d200a00c400310000070003002d0226010120b500c2104404200f00071000e03040c000b0202d0700c100c2e6044100100c00700040e403080310184200e4042d071034040070b1885040540906503601400e6000404c9040f80700380d41400002200d0510980c0940a14010060140510350750300940c00018500c00400701e01003035004411040c0140038008010010445412425452007641c540c1070a5032042d607a03a001254a100008686041110644c000d25295100c1e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 96735234 1250 96733984 96733991
    0x3050a0b030124060908030403031d04151403150115031e20070f17190207050306010e01210c05220c02060705090409020a030206120403080601020109031403070207050a0f09 76
    0xb149405c650745d215034400c54209400170402400440e10070451003071300c85e07a10204400c0c2c9007071f02c41c046421901c1c1c8600c080615405000180102c1014112407009400c00b00c009007030038140000c4c220b00b00c51041c801e05000c0500303c9800003020340240c0042d419100084031000c001071908080380040c18283c20310000f20207214000f1035500450f1015505090b0300150401d0070144540c0c0c1d41031180d0a0f1090348081540f00b0305c40c55248a13890704580005038130542c0079003512031820b0103052500c1c2d0107800000d1010090001844003200300b50000c00e402001140800400d580c41c00c054030104420317000030350886600c84403c0f21103602a181e40041e0440d059040000d070141c40c02c00c0342c0710030b13058648a001490030410011035241035040649003034002007040101d80c1d42c2c3d03400a580380d072041d00c2901c0040001802c0005050304801d6043c1e00520030300081c083c0c0296564010031180c850003440b03000e2a804804034103154820007201c000380001808401e4074035200e030344032000000c95110740c0011904 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 96736484 1250 96735234 96735239
    0x105010e07020f150109051008011505030c06120c0d0213090615030504170717030103050109030219030507150e06011e1d0115020a0b1906141003050a0b030124 70
    0x10f000a503514a0380700c09000340c50507424208000e000e414050b115040c00092103501080040003841481000c049040c201910603140c001410b0500c0c810b000401c0c400d48050000e03005010710240f00580c4071000380400380e51020503a58400007400ba601030000e00c01090000400c0f40c4442d0703030202c403d644420b9020344181d804170008400340e500454004102041d000107400c0526401c0d009030100904c03c03400c402c103040018480042a8100341c1c002d9400e603450340d03910f0f024180c0600c200c00d81d4542e4450603188e00e800301e880281040c4640c500091451070161901c0c89245199880314480c1e40030325040d140740d965105010050841c8a0901d081d00182140c40041ca4484003d407402d11040060300e00522a80f070107080c00c50f050101e07141d2000794052040c2002c0010a500c0942e4441c4030790035807401c0c0341c194402c41d030002c558013900400d580e038030048034022040e0745030554091a10300b6807501042d19039a04103043d01901110301c0243e003640c00c00c03040c16050803881c80000c40108569030103c0724541d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 96737734 1250 96736484 96736513
    0xb07090509091b0907021207050d090b07050c010f0c14070305070801180615050d06050a0c08131209080d09031506061205040f17030609092a120105010e0702 69
    0x1c1c90065000008030f5003103801494104190382580c001c2c0700c4c2c01514008021131401400d40e60045030200c031142c000c600405107280d00100140042e115034022507085c1140d940e1507565407102d4043c102d0512081c01d018901451280da0b48051103680407020303020520041134025620102400100d40d1402021004240d1480c1407164046140c0440058020b03c01c4a4840b24020320700780751103807240f010491010400c0d44a203e20110030900c00c0d4800240b51034544c89017401c0b0340c048000d00040165110031700010355013040305042e8846d003080d168003c032224404165001c81c01507109810600132002d90114060b005620f000489019106685111050707482030400c60380e41d40070b00380100e09401e47c21014049654029a841403160340c1d02990708950342c03074115054002d4203c0d8199640c00004205041c1450301c0341a0f000620701000b4908544409003010b1182c00301411214402c21101076001295a01041e001c07202030100002c1100c0e5031540d0003070301003904c219400300251041707000c00070481 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 96738984 1250 96737734 96737743
    0x60c05071101050a0c030e1503010807140405040201270503060a020d1a0a0e0901021c0207060c030b060906090a09050a0902150c030421051506040b06030402210a0b0709050909 77
    0x50203039200b00e001da101ea031b01940d14500440e002078100045141481c4a10341c0354000b1b602a102a6008028541c5840380c1c8c13002c00d00c9032400c61070040741064207000c0180d80015951740403000708a400f09481d0000400911074100650060354140b14030024030015001503070080040c12070755203041c04401c4c9500324103007400e1001c65049070402c10640341080443da41e103582c960445a100c3c0098500109000c0d82c0c2200b048180d004185254001465001c01080d446502c102104038201441131604200000f080c3e40100f43c0c916009030800569a4035603503400300003d02400c0841000c201134100000607078018404001c00302e000d40924020010050807402c10b8030160a0320300c0c020351130242401000742c0b0031001c20310b0021038402c041640340c002072024082c00c2825600e003c0d9582d441e241010400080da9039a803030743ca004000030024003003d626880e810500482c0c00c030783d000170080304040440d0310382a80e0703000c050444800101445000ca5000d4250700c2107810440700c89003161920040d00c0e84a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 96740234 1250 96738984 96738997
    0x140705100504150e122b050f0f0f0603070b0f040f090504020a060809030f160f0515010f0803090f010c0f0605040b0601030c0507121b080306130905210403060c0507110105 75
    0x7603142070101c610101005506a92010f07903040000150101b030318050030a0f1042541c007054585451020051014180300321281e00005050320440781c1d044c1000400d031181c00c81e000340c00c050100010030b01707071410402d412180101003c50104081c940d50309183c100804042c2d60880c4294011440011a2849020521b01031a00c1030091854000b0780344002c1d00c140e0140a0070f0211aa80030070620118000a080c44003003801040030f040c030038414051001c41a041600403c1812032030140a02904c1c00010551758202000d9840c0c550348070002c030041c0c56450003140010900d0b030015400c5400c00407260001e6000c0e0f8403c00041031310351500001501542c075244074000c00104140804004124200ba05c000400d0345e505040c1410041000c003001400050702045c0c0f580300c0c0000074010203040c0418101c8100700400000c001c07055155130307429180d10700302d440c0765030741c10b40b0340c100070b030724048601c121001951f04c207008010084000e180a045c94200030310907204422003801d400b140e94050003c542c02c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 96741484 1250 96740234 96740263
    0xb03040203060106110a020406030f050106080f0d051b1207030912030c08030414010c09030b010e0403050f130807031a071106061c0204050708041e03140705100504150e 74
    0x4040c0c0c00c00324105c510300344d43e480c003942d98070440403a8009a1030b68418800034502540f0400c03d03080c26030402509581c4180d006540980c44000440145030020400b1035541c0c0355803400c1540c03800142520403a9050354211817846000e809586580c06946c50000d256207446521299802559584402011001c1e10b00140100d000d182c00344d030014040c0c00c02135a002e4400c0c42451021080f016440c5c1c2180c50340c2120701c0108115400900910000c40129401004900b220f100185413a0381d00030481d0090700e03c40c0745a41c1012a092411036120643c5201a081003411182580d68030f092000c11310b1440710b10750b04044140000304045038492240810418032078802804940c49210502c40480c102903480c035811008882c44100580e104c1c09081d016550703585e10b100342400c1034108101d98810300d80300e0a240c5115503240c000002d820000d103050200764400344a8850706242804c90404162602d00c40700686007004000c07c00203040f480072801120144100a241e503451003d541c0c83e134040705100d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 96742734 1250 96741484 96741493
    0xc1e1207030c0b040e070f0c050a111c1208060a17070906060309050a03050a05130b031e040308060108060f03010c02100c0504030f06020a14130915121101110717070b03040203 77
    0x4049901501c7e202000c0002464450500d02284d00c4039401c00c40b4503202116000030094400c0014a0141000d4081d4403030802000b524492a0340c602031115601c070016410f0146003000502c140d42d134107480800500700e0700c24512501860400e02900c445441c05009080c03440c00401041c2daa10034031440142070751240c020b1100708065201900c40341c020070301e5501000340820207120035040b10280c8000600c0303003d08058490500380d015890881e07029004040c0c6d43c03000003c001c0485e40c00030016800c0b010038282b070310154a5180104510b501c441d030bd8141c1560070400c3c2c198407241c1c0014040744e445d8a0748810086094488000c8405100d01c1c400a40f05880114042020484980c02003818800381c0c10305840400900d01c4c0c070205074004441d8030800d00f05130b11081040481d035014100b0304031221090440c1711810714041044400d5180070140111762140090225640252029512140300c00c00b100c0f0115501d510900c50380380c69944030030890056400c005102003001041c0da004960040261 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 96743984 1250 96742734 96742741
    0x13050c071b0b07030c0210030209130f23040c14060409050c070609050609010c030203011520010614130501031a090a0b0a0f0b030a050c1e1207030c0b040e 68
    0x148122400c04041c0300e0300030420000011010040802055803d2107912007503410065401008a42c0c0407019440040c580100800d000640d103140d540c3c0140f10040000190a0340760341c207500b0017014910111016203092482c6000003010301d00803d07104511584142c1c1450745c49803240304602034500324041d044001400188090a4503822260f88a14081d0030141000b02584486007a130b100400252000e40041e030a102c640032080c018140d002455007010740c51945800f00c242c00021203080420308102203035020b109041c03400080900ba40982d800240800c603100c1d6541402e046091000d98400c44144100320407010882c000c4e14100c0350401030816071502d1691203000c0019008214048900a011b92000003901c1680f070b181c010f0010b00d0300001d4521000f11013000b02c5140807a8144240c4c00000381360005400050300012030f005c1a82c000003510024401c10f82c0340c41c103d07051140e00ca69480c006480c2601d00080d00c0044a000b01840c48841c0e60300e40c40341e040c41c4950701440700d8294909000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 96745234 1250 96743984 96743993
    0x100f1b0e030318031c170109050c09010f0512010e06040f090510051008010e0105220209060105090103020702031507080606070b0112170d05010311030d02030409091a010303030203040213050c07 85
    0x502000d428007800745c03000340504950f19825900d0000e44c25000c2a05070700541c10044000130440c2c09429140800c100b41d052031800c8141c540114840340d41048050005251003512610503038860070f001c4c01009005503120001071740c0100c0121001800b1324500314184490ba1000e000c0c2d90b507625004005400d0580e041c00b4603034040c110091600c5504142e120300000c0040d07003403103400420351244c03000040e03e04088118015490303414141003c2621000c1c1d003000503a0760048041c0c0c0210003402d0a42d55807071441c0041e80a4054020040d515004100898101c070180b151018400c026550390708070b0542ea541c00700141406082406421585d00c580140604469207071180c3c142402811800041d8001501c0641e0a6111800d442c1a290f10303500100b0401540180758a440780d8200c001e05001622404020350700c0c010b52013078400f41515107880c0010b00480001c00d06020b5910300400b07101d90b0312420094065801614100d00510101c140210032003090b110355030240b5641d103003091038480c0a498 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 96746484 1250 96745234 96745267
    0xc0b0a031a03211810020706091d0f1b070302070e010902160f0602070b0405011e020408030d020f120115140403030e0111070e100801110f0417100f1b0e0303 69
    0x1201c2001a039214100303045da41c0d0140024a4011580103140d03103802d1660042090589502c02e559900e10b800084080034450521203074042e98240c048160390b665008125489010301c02d16048a40f0b00045030f20602d5408100306083c0c407103140307a484490740e0f80c0007410200c2c030810b00301c01d252000c8040404009020459150701050050310058280344e0683c582c0e180000b000e0380c08807030b140e64859000c00ea941a640c2c0f400c0f003822500b60114203003071400048a0f100d126500c070250115a00240c00f1082c8503020042d603c003510000148059582c40710700c20044190307081c0c84038000c90070f400c0d03409421074410300c101c809507607040d521400100e000710010354840407a181c5840703282c01101070120301c41c1507060b266441214500100501a0f18101107142180c610080c1904409801c021900b40790f01000121000c4642c4a6106152104180d103228140a4440742c04c503041d43c1841c4035032904420035000041a000c007249014200c00b40d50000303844928520422070b405410600c10321002188000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 96747734 1250 96746484 96746497
    0x3011208070804030606090b12010e07120206070b1618050a03030f0507050d030204260703020105090d050303070207050a09020a021506040902090a0c0807080705030c03040c0b0a031a0321 82
    0x2d0b0342c2d040c40d480f950350780150b48041d0060282c482d95011040d1503407034861850607403041c001000f04a081403104c1c800740c480e07031107004d1960840204103c0c1c0d001c544407002101c080607000007104046041c01d0f001c40d14041c444a0800340042e2521480148403203512041c001103071002044890200e103507a40541c0c0b9601e9110442007403000a1044001040f41880741c0c1460070119540143d50300c0c1043d07005d0b00304445050558080000151000140d01030005989050b680c09080c51a21105518002010200214401400b500010040c03160898001654000741d0380304641404c266602d91000d8000c80c081d8541c440f0040c0d100307110310b421210ba40a6600d4008802400200e0000081d40104403485800ea62490032903645140440d50325602c80049504030195103080350039401c00300401064ad001c05000f025140b140080400d0400022001c0900241a020042030712001c4464000d401020014844402d15190910785a070900d0049001003d04007540c1c89001007110340c4c40c603c5025000103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 96748984 1250 96747734 96747743
    0x901240504090c0207050907090b0d050406090c080705150a02100c0201060b070309030b10080a080310120f020328030507050c030a080c070803030c03070305071e11070b0301120807 79
    0x800001c19060b5180c0a50501030718140c00400e001071404c402e0080388500149808204460103c09100d032901c90802c54899a00c00d6a0102c1c580c0c8030703400e02e40000c1003138a030010110100c00000180d551000314a03001119004c880346883c9a06800100e240ea01c5521015001a080701c0142c49680d0741c1540161400c410a10000030b00607283d030405801a441aa816000b0404980303040041003130a52410360f1126042c4182130b1554034001c0155501c0e500703800003d02984010000941501d2044107c038001e1840750680c120001183c200600d142405c20b200303a01078007960500111034520011703545410112038801d042100900d403811180340e00900300c102c0d03045c0220320500d0200c0d030703040000242c82070180b080b0329035401141284924003021584152200d400500421110308100d0080d80e500600e90f040106140c1e545c4001250401d010710a500249080c0240d241c0680d0340c4100f02000d50304d10f81088400c016220303d10840301d40424410001c0d801c2a541c0d100002130f079a030003d0441c0e940720f07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 96750234 1250 96748984 96748987
    0xe090403090302060d0209040b060703050412030c060204030b06040b191802070503040e0115030504020303070206070f050106030b100503060903030106180b030112150c080406150e100f0509012405 86
    0x380c1d07002580c035500c80085e4140035900801c02c0d41d02d03842c2c00d124218070610304848552034030402c0d81d0041d00340c1c013807032040c6d01d8810074491509003490300501c141c100d000c7c7d202500715070f9552240340100410009079a258015440c001d111803403410652000210140342040c0a155203241003039030400c0c008407000f0f14150759000d200c0c50000170030410144c4050401848422440d40c10a0759501c03082c1990702034002007505010a00025803000320858110580548060395034601078105140c043e01d01e040f00501940c60010008240020709601e00e0041c0c5d1811400f4202e6540c5104159640c0c800796150b001c144c10030801004414010901c01840e8654070032141e41407552503452079400d40090b442049003003000c0306d9041c200302d040c2e05180e100c945080800c000441d00440f006048540051004010720750780c8075030f0003521030200c14203002030007400714501291900e82001c09040d80184650f4101d4144035030b001c138607032070405e41142c10b8035000c140c03002041c1945100c02046404012140c800e2110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 96751484 1250 96750234 96750239
    0x90f090c0c0a0605160206041a04020a0e090a0b0c04050105030a18020a0303020d180602031803030c010207060b0907020601081005070c0206041d0c0f070209060414160318030e09040309 81
    0x2440030080a5003d4000041d69103062031035050504400000d50085402600c20040000c150400011342e2a40c075512102c0345c0e46e01c43c030114199000c2c0e034010a80c0380700d0380010443c0700c07900012a81c1c0400d208560010f0716403103400e001e01c0c1501503405003501007941480001e1401144c0d5205100001013010000903105164000c1031010440b0782041c0c0050b00004020190241c10107112590310343c0c0b424842026601d0000c0c000e480f0300807030342c0b010030340c4041500f2038541d030703408000740c840c0c01c2c1c1550021507644143d0b180030305c01800c00d9141c40f4016000b20000034a564000b161180c100c9600c41c01502c1d800302c0c8101010003c0600804040034400d40380241c80140c2c4803200588040c20340d01d8100a00c3e203088428141a02c0001400b241601c10100440030910524005540f0481d1703040c1d401d43e01c241c50380780000c3c0141030400c10300c0c619610700c00704202c144030b00300e040d04200c1d0703810b900d040104800282c901900300e4041c14020f030102c1d00c5420b0328596400c6c1200e10b10352040c00307858076404594 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 96752734 1250 96751484 96751507
    0x3090303041e050d05030a0e010c0b0402010e01120f0c03060803030615030c0f0703030506040e0109150e0102090d0f020114090a030206070212010903020d0906210c02030f2b02090f090c 81
    0xc02c2150940d800e03071011603001c4010b40c02c44408c1e80c80d9402400c00c7d0a22039690741e510640c1c810002d000134100162041d0191403a4094448007031a403501507030502403800c6894030040104144021031000030704000300000d0504011049a0080501074041c803201480555010416807015041c2004c0c128100300051005106802911305a8800c0c0e4001c28039003000c0c8100000c0d50b06c0d0b00c4c01440d0780d07498195084002104482c042c00c1440b806800881c2c0395540d00360080c020b018030744c1003641201440e0343d8641000034421090046d18800d88611a2040d131103441d0b03d02030f004511009400c0200d142c0c00344003508c0c4c0711010700b19152000b42079050390028030460500352030b016601203015034405c415000c415a0404621006000b003403508031420408101d02a140c014960825100e282d0740d0500820f41a1090085408038248044000d540303844a1030906003a407000107810000d550303611a00340b0712000394022284542e200400085054070381104011101001806a01c05600704010000c0000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 96753984 1250 96752734 96752749
    0x5162913060807210203102408090a0605090a02030d080709050402070609080d1505010509010e090709030b09061906151805040e01020306040605061315020a0606080303160203090303041e05 83
    0xc4c1001d1805602e0303041c11158900591071942061246049424809159800c1d2100c180828000741c07a245140341c907103120040c284214143c01502d9103040008202300300c50005629601540300350b044800601000e83c00b12071020098608000091101c02c0400c114070b06031700030b0b00c0241d0080344000780012040d0343d082c909600c035401010040d0740780d14030030440d040250341e81c0b80146420700705585000d81c01c80008009581030360f103040c4580346443c0810001441707101c03c10069507000420981604200c03e0440da0f0348412142e14900303c82c90340810800d0700150069504580181c0c0e41000400c82003803081c0e40c05103003800c03140300d21000985c00044680d12402003816142c04003000503504d003030000611003550140d822290080b18104503441c4500c15400004007190b0803802d104e4016a00d0190490501b14001406400303142800008644010040015801a41c10491000c00c0c5e0411402c02c0c2d0712401504440e5074141c00c207100410268140620591821f00702c0c08110303503201c0d00d50f030000d40c12 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 96755234 1250 96753984 96754037
    0x1403060102030d06060e01110d090e090a08070318050a0f0302010c03121b080c04050f120102091503150d081903020403080408010b010206070c0b0a0905162913060807 73
    0x54600c6c42c2c407001540c106043d440c0b440d102401800b01038094102c040e040a4003440b408040c025544c0004944900a001d00f5044030341c0001541e03921a51410300804011014090050100c401840020680b520000040440f103000002030790962030740d001076884e004c0010065051040d60485032240c246144195031806d4480c80421001d900c0a83d0020900100101b034a0794400007000240324560710882d030042a920304a03013041e0a014450b101e10701902829840725041508100c1b01c100c03504d0030343c01a502c034141c1040b1100d4501c0d0242c080060580540e6000740503c002005441100300d0b802d240200c0c14180e5003009480c16a40c0e907079050155000b503000f6052070f5562510340d0001d42c4e05000c40e640140c024501149504400d403141495942c0203041080140d036030704060000c015040c0070308200702d03c14400340150750303076114844800300c1c000d4a14007580041e0000030291040590054804080c0f800c540b4000c06803c0000a858161000d044d6106004490a04850524100380070285 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 96756484 1250 96755234 96755237
    0x3151a031606030c050c0303013303050a0b030a020907110f03030a060906050102030307021002071a1003050d031109040903180915050a03030e0f040f09030c050c0102030702011403060102030d0606 86
    0xd070381c07600d800181103904081400042020400061080440003c00e40b81510700b5a04e00415908814003101174030440710303100d10031809103d03100300241c98141c0c0c45a84100e18528080c41040c1c0540c2c10191281a0300324020b5210000e0301c08582c3e028811230070701e02454600811603440000f0001c0362890f41c1c104484020420341c40b00418481c9484074090100100003c1c0021802d40c1003ca1000c1d44580782c400c1080f18590b40450320000f8003114019080d800050174125032003a081010010040480c58001070303800380b04074500c150500b440381c410442d000ca494201e550415a01004000160a8030301d400d8081016100c081441c0020004145009061000000500c031203a41c0201002003259403040f48101c0303041d441000440d4000c0300040600703174100c42d80d03201001c40c0800207006142c0d881358210580c0c0f4241c412420903400c00400120180603204445c00900c241004913038901c40c2d0300340280042e2905ea181404654988061a0082c105005407801c11201c035555004983c0207500000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 96757734 1250 96756484 96756523
    0x9090501050619060504030f030e04020406110105070e010e130609021c0b09061f11030a0201020702031002030103020a210501150312080903030606070201090b0705010606090e0103151a03 82
    0x40700c3d103410303000200c045150304005000030740b070000080c2903401144000380c000341c46044410200342c072a6401141c440c40c000c01c00c40d12941c5601c4018000c042481610040790b1800f0003040030203006803410b050840050b5180c00e0510b8140d000d0002030000c4641a076103587e03e603940400c3c001e2450010780050201f03281100070310b042d805e042c038058a482c460041c0c080c098081c1030001c0394641c10394580050070070745440401c04540d03000440f007005c03e0820280840c000806d19880301a4190020b1850b00c1c000c904030b96280c4220f94003002284401e21000754040c3c60380004200504807407080505198485c1181c038501c0320562a11400d582101c1802048000d024000f1b0082045071450101080a1441c1c0b0030003903c0c000e41c18550343d00c8054032262040201048031811603105100c4500940460559a030f01c54a452510601130003403400390b01c2c0070904203000480c1d440280b58215040342e421202c0c2004041595003d00028401c1144220310304941003004180c0e510200800d1014015000350789 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 96758984 1250 96757734 96757741
    0xd030509090106080402010e01030e0c03060c0d0f15050405100b07060902130905060f1504060e01080d1b0f110409030f0806060703020a11010201140a0203040c09060503031c060909050105 82
    0x100c0c211605803c888140b01c0c4ea8418080540d034040c1e86c03040603000a080000f214004a0030441c605110411510392500c80c10301000074001d01d150180859842d0781805000080504005505541254010362980811800708102034a42900802d070401c20601120201e151100001e00c05580082d0301912000d4031286208114200715a80c2000c48a01000c01c00c0390f0411030362096201c61001d0000c5525014000c04103d07a85400d4820f03990649004004204441d902c06201000500034490074a81d070041c110b0055005000305000c8580c82985000c5a8003030790f20359500c01c17202051000640d42c0c0740c18140c910000d6195480303560200d0307010b0b890786060411b5181d401444158010080b40c065241885107000194001030842440b07075003e00d1101014000c140100c0c0104070304480d90417040070103001d008050003298000d40c0a14091815103540c00d44034a0102c00b966194403e9541540c001c0290201c0e030030540c801640120b82c01403020901a640314925826155545e00585041c0d640d1400d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 96760234 1250 96758984 96758989
    0x2070b01050906090604090c270b060307020624120105040b010b0c030906030606090301061214030f0d02090316150806091b0706060e070801081e10090c050d030509 72
    0x819004240071281d5040c540740030000300e071480d00090001402583c40b48a43d100300603a81d5500c03400341460b5100c20201151402030600320383c4003e0103503880c0500d81020011981050802c580c41400141c00804154899400c0c03012401451068450310540c4014004070650740c00c6122400c1342d402c00d00101e1a414103040c03168400b00c060303102640e02c500801c1402c16040e0048180c500c02c280490384a43ca035643c3c400030403102e100d6002c0550b455445c0c240081246020048500c000381d000b100880d06070400d041d4a150b480c4a5800c0100d08000184103460007612250010300e0305400140a582e01c0c001d8406903045035040c030780c1124146d041601d05801105a0001c001d03540618111500001410144610114120a881151806a0001401018018260042e500070074072a142420b00e0300d0b010100a1482100380212070740c40c00b9503c0400e5640d500c075000e049180d01d080c00909910030074800001c0c0100001e0b401140c3d0103500c5500054141c2d696200e100c00d080c007a88031903070b491030ba1404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 96761484 1250 96760234 96760253
    0x30711060a0524030d180b0301092a020705101b05060106020d09030b072f030a030f02120105190801060905070f050418050c07021c0506070f05070f11060c010207 71
    0x2011105074070b00780f0381c29525030760000d655100d41e652401c207401d01c0e1030905c22400a0208a801c10000038100100024400c04260300801da00803801d600c01e03d034901240300c00c00c10b102d042d84c0c0c2080140d01418044c4000d00d00031107000302011140c28044d10001030b460029000400b5040103584617000f00004001054042c000038412038600d19150405c0e50556035012a181c102403c81e100f08201c4e004035100400e9154007a005022105c5c90400b001d880703056045650b07030f11052407080000d04044040d09100540d0007590090b1070440001d0959a003800103020900711420f6801413041350315400090140000c2c495040640030132540030400e880c11220182244210382c090000b040b004010820109038010400f00b81004000c4c400705a44e01c501d0154081809280c501a50004219404205402e40030b402d0101080c03048c4181c4001e95240b030800e035100f103c219807034408290304110504c005882203510f00d22140c400d0018003280354414010a049800c4190f10741200ea60004035403061141c0d418 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 96762590 1106 96761484 96761521
    0x11110020f0906070606050102010b12060601081f080c1c080d0b01030b100201050a0b030102160807140f1f02041203030209031c1d0d0206030c030711060a05 69
    0x5c1c040003d00043c41018095840c0034406080b80c101030452130005480c140103052540c2e41c010041d0313400c0c2d0000b040740c2003440c0800c24040c0303841e22440c611405058070800405600200e0024490111500541d20184003201d514820002e0303444002c98442c0010032002184030401c500c0140c001d000030351406540405103512042c0c4503035056008a100c1c16a0201c00c3c003040c8845000d040c00c034424040d840411001c64094000440c02c078034010a1380c41d1103640c1845260b401e151800d4140b4030700801002c010b81200324602413420004481102c003404d0141c0c2145402c0c58066401c50f400c00902c8000c0c240340c2c002c64101319039542401041c5407107407007441c41400d820680400809420400246920724034501d440900d04e400d003056588049076015084c50b166440c2d0444090254000406103000c02042d00381903e1001d070140306090140680300008246810039250701d100141902 = true := by decide +kernel

theorem cover : BRFrame.Cov 96582734 96762590 := by
  have h0 := BRFrame.cov_init 96582734
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96582734 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 96582734 ≤ n) (h2 : n < 96762590) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
