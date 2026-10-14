-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3273
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:10:41.491721+00:00
-- url     : https://prove2.me/submissions/28348e3b-0c2f-4a85-b144-3f6284387c48

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 588489208 ≤ n < 588669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 588490458 1250 588489208 588489211
    0xb12032701050c1b0a15050d38150903070308030a02120106020c03060703090b070e060d1103010519120809030102190c0b07050f22030b19050709050d0209 68
    0x1490403515101120400c00d244c21130210a01200403030001c0c182d2804d203803040340600104100703000705013060032105000c0c0c40d40c0074504043c070203a0780340c95480c08040a00024400020481c0407140301d0780c1000002c1100a4040c103903003030700400d0203005094403400c003403007a1030110000800a182c800d08541c0d45000c29000076050040380c0b9020703c1070096080e41c8a85aa001c0c02c0154002c0110007408410940740c0301d406403214060514086036440460841c0e401140c1c40078450401d810a0a203200c01306190f80704120074880301a14010f0006116a90040118103e400c00c5a0408190301090441c0404c0300462203207254019103100a98000317913086000e0924148001c0c0014100319524060741e0070b03400c1c411414000182100c00980070050001a1b403a0040c08901d48075051074903010801850b8818205480c4038504912151307406a052030408402a40d404001c04c90036040c038070f0420b4010b081c032070036480041e0300313210000c0e100900c43c2500e1000c44400030300002e614a01d076003e02a04800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 588491708 1250 588490458 588490537
    0x6060303090d020f091f0b03150108040f0c060e010212090916030b0316030b07020a0201080720100219020d0507020f040b090708060a06170105012604060b1203 70
    0x403030740e500414035600c0c9042c40d4443c11b8010001c18030156000d00103014210b00d90841d02c2420380900920500c2c4d010100b82e034141c1e00007820541055103441c01d0040c602e40720802c000b48a01e82702080401d0b501e80c88084030b2540390080e0200e491088a406446400380102c401180d0842850760005490010944c0d030f00c1a88206410700003180b0710803c0102c1e0500018180c0c221880a0a0b041001000501907000b94400076a2010b44007840c800c0d80000d1000380e000e02000304110760216a11027030a00c140301c031b8507262a40d000301c4600c450300b14140b801035004600464040e0042d43d424020741400417131290400c0301c0550300c451401400c1c1d420080c906042c403031001e401c580d4641080f2480d8880352051030040c0e0240e16501e29078500901044183c6140380c00c142c2c04c00020003000400421010780c04c0741914800d00b07250501541340c1c00b074101d070b911a41e407210801e41075040c14030060082552101c041400d060310b0301026094100c5445a9910500543c80078034452842600c02007003002c2041c00c01c850 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 588492958 1250 588491708 588491719
    0x18090f04060b01180305071503020309060c180d0f0b0601050c0601090203130f0b0a06050d2d0c0609050102061e06012a1a09010c050307110c210f06060303090d02 71
    0x1e59860459800c40c0140c0080714158420b00e0280444c0754030008e41c805100881c54290328502d080c54086e91110000b5140c0442240046045191142131116140001d0809040407107115100c0c100720720f03038044405041d15018400e002080703055209400311040400d9000c0142401e17403134140c22000130361000300488284d0318050840d10001c0c6150703464001190103091035504504140a5482c01c84040f0ba2103584500300303c80f5600f000400401001c2c5126040805038140c0710061910f0302d544858100c2c00800c400994030011a000f80c00100c040305946e070aa08482e6150340301205900f00d990b5079000e0849885440f03002900640c0302e500c8850001e04200c5402c480040082c8800407120040d050445000ea48030300000c90b4109050896648641540001c0c001c0790115000602144005807030a010400c0400e0b51a161070000c10814035030700c0010b04022002c448819500b10b0900c42e2031041e600902802410030350303641c07000a555015600090113180351204490800c290080380140480e04030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 588494208 1250 588492958 588492977
    0x50726062e090218030313030308060a080d091e240918021c050f0403120902060f03090f070303120f06121101020f060705090d0f0204090818090f04060b01 68
    0xa2003a95861002004030b0b9101507241e100c0300b1520f03001c880400d15110302076401404a130100d0078200301c05400300c903094140361541b0313143d200c00b01742c59460f160450807861180714402c07400964010901d1040301d8400e072030601040742c62482421040b10070311036081e00220f0702c240c0b00c02e020141c4801d03061440060070000030060f038840c1c90600100855009295145e4003160715031015800c09804a000000f0140c1000103150459003202c0485014001038208859900360a440054640c40745012a800501182c0c40f02c224070440c860540c812a81d14011f405800c6018030000c100040b107000b902da040d00c2b44000540c1d0030803840c00178080071010500c00c1761075002c00250040a610b440368030600400c0c601c0b4140c407083e0000382c0f03000c4510786604503c0e0300440c104546680d129082c4d07080143c0440e915540307441282040b00c413210b4140d2002c0d6201c1e10306110030302009408801003100055265900025130714450030045100011621041200447d10001d000a07503247d0008401c00414100010700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 588495458 1250 588494208 588494281
    0xb06010f0c0b090f121216090e0405010f06080f0c0f0406031709040c0f09091802030316050c060c03070b0405070b0d09110604031a041e05072606 64
    0x40c0507040e2070f0042d00c3c0e04290080c000765070080c4200403801d505d203040d00d454500e040321429806000101380c1d2403881c001510302c90115104800500061801e60035048140c2002d0034204c1c002e040000541c80080d1403c20001040e820104503200046104c0c400342452078004810320041684000c6d00942c0103a071200040001140e00d500c054143d01400e00707403074550f24410180012110380100c12405e20102c09104e54049a210107070400b519000e6201007400841c1404d550092812418000d505000c040b403055a501c000305503292039103000d01c00310751010f2000c905018051080c800c0140403038004201e2040850080b09540d40c0080c420301c1101c80c420340d034442001c041e8100d00c01d00a251a2180c82c0f04060115142456003c0602160182d01d4140b46584907080907001c8034492100d003500c100081e080c0312605601050340326248a09814460181c5040340e01c600e000d020749610b0004a458550031107115445002d441c14107140201171030344604616141200307828622520841c0f103428003a49 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 588496708 1250 588495458 588495473
    0x18030309170d0b09060a0515091801080c010207440d08090601140a150905060409020a090e1e1009090f1a09030a0f0201020d022805070b06010f0c 64
    0x103a0019882000a03400d0f468030800200c80c00180c10035100d0b0f900c200c0d0511295460701c40e00c890105004980300d590b200540041030f5088400e9558607070340c46006e40001131440e80480c4950308444241e0039078480545800c002c2c0030404d40a81e107401d841900450300325403940f0402e94880d00d9080c104007100c41907095512285891203054804000503c0349050056440741000380038003500c0751502d030000d0400d505021074a403410500c16094100d01c103500c08104280a045007034041d00014140d541d55070744501013000a54054001c0b000014401440040c80c91202c44c140780c000c192404613070408200d0b40101c0e0a003400d010f00398629404030b5140000700c2d000980300300d6070080d10511010304c4e502c4040c18a29901c0d0210310214558100c3c5104000380c1600110440350080c10904103c0004215402d00320300a00580b80070b0440705100050f015544940403141580169007a013182c000c0400e4070074116103600914034000c10480310800890390707540c06007411031440303501403810140440f200e440380139 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 588497958 1250 588496708 588496717
    0x12081b150f04122706080910022701020708160e010902030411011107031407150504060f0320070b0901050112050714060720131803030917 61
    0x50203034000c0d03034510100509109025400705940c61041114074040c0c6500e55807400300c0c1c01c19802c001c4009003007040000110010110b445100906105460721550041e09022003a601020300e40f02d03100380b0b4100100c41d4005c4032a030024004241c1c1c03825001c1880051040303071a80c1c40c00d05502411801151890041107055800000711031400c50030351401802020049068002c1c0030058010030400021844603514082507500030b00c0e101040700c4030301d4800d50030034a042d04000c1c90130061078a4203401260020740765058400000f0074a212070000401580c040c4594440d20001c69004801103c015020368440400000108001001110a160480e616030302c00d03101101c0d01106102888418402441014050405a280310800000a845a664030f056a104654014012244240c0c240e11410700761921745900080015824045d115170171343c0c203010b16a03028025100e010402900390310301d0181e128040c1700d01079032901800081e1000c1f4080c00d43e428099031340440034600c00070340168040080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 588499208 1250 588497958 588498007
    0x30a050f0109060b040605011b15140901050a15150203040528060219060203060a0b070515060f0105190e030f010906050a020f0301060f02010b1306031208010b041208 73
    0x5211440f454200101c410355554a4022894501d050069903004140e189403a00d240781300c01400d82c82d5251010100301985080d00307060341891031040721002c0358100c0c5401411a00c000303200c0756884808210403501700e240320000c40c1458210420000d0480a20300c0e900f44480d105980c906900e403404100c0540007003030b103d2030743c0e4002481d04d40501184d0401c6005403030244003505110394903079101503c00309645000317030400b0b0380000454426654204454014204007183e40d894040340d060150302c4c3c480c030001240d808009000001c1103031a1900c0342440c0c842058490a041802d0b80810003940c1e0b07000c20710803042c44620000c2583d656810403030420315803411400452640098070302130041e104003900038102c060040c040c6149180f18602a00e05548040c0ba0003e103100c0c04c00340172405000c11000041d00044030301c003229041c202982002041c3c1c0d00510489000c42d1090104880040c424400c910301500244024820070071402c021150503805051447d04003d040300d0543e02c040400c0b4410b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 588500458 1250 588499208 588499211
    0x106210b090105010509061e041409060c0306100509040b03100c0909090f0b0402011403010305100b0612010911090604080303100503150a020a090b030405060103200d020d02030a050f01 81
    0x5001001805035103940d100000344000d10070707540340c04003003085000b0280006101c2c000786400d062801c00a50f0356440350b0080140b00b8030100c612504100300f010700545401c101c90159200007440900d500003120702948024200070801801c0f041d04440540281c2520307a071054480003000c0385998204442908050b0a2800081c44440c2a2014142c2c01650303201010282c2040310580209420020301a60700e900b005101c02e542da03807031004803013491041d002012000f0001c00080b0070320000145c003903d4680001001c0001d040803608001c4940120210003901034980701c0148042600760b00700b14031070020043c0c011304041803100003500a03040b5800000d80c0394000300030007003882c21040112000300005c2e0040d0015505199541c15054002405010003580000794000c41c1489103000c03500074003520303101580b43c4c00e05180841d00c1d14000e200a40d00c10016030b00000050306142c085200402c0300500d0507041300501c1d030900c044601003031016645405a8000440456801d000022480650500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 588501708 1250 588500458 588500519
    0x30e06033d050102010908040e040614040c08010507080402240918060306060a0501051b0a06020c01020309060612030d05150907020706113405061801080c07080304140106 75
    0x6425101a602d611a0741168188840880440d10400407142510840309075901ca0703a80b50304001c00944411854282401c055000b000184030000316800c09079031111000f840140c5814904513076004045c1d401030340c03090301c00050010304d5880907010110240b02011a5044c20030000000301c44030402102120508015410480b05140070b01645a000b14100c4d0074000709414a030000b02103000e2191990240c105480380da14920f0002c100c0f0140f82c5070b22000a541d2014010340c000d010703420584254142d4464040840c0d042d03e041c8034488170080450008605040c0000c10b454054040603250b4016038110a0780f6050a4964500252091003a03400408019141801c0201985c15814600d0350a4020240d503100200743c40072001d00c0400c44107014149509540c0a021071042580d0180f03601c400c00092a403080c100403a10020101400d80b55410395503110755641e1114412103000600c5000104001000a02c80c80e48008098206000014074592204404800001501c0d4040c000754901c0b00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 588502958 1250 588501708 588501811
    0xc02030607051309051501200604320c04021809090a03090603020703050306041a0409060501141206041e0503070818040e0a082115011b030e0603 64
    0x1030f8820020041c001c4100308520303003000c1030780c3d8a4070307440ea6990410114082d49071450f005801e03c5800d41e1507040980d03040e810a4540150311005c00132414903c0920805040c540081407400400d5000b10100035014041e030032003c00c4001d511500d11003021070078448000710f494962031203642c4158404c5004100500a504014182c00c48642c40307102010f00400ca0140000e9010050765002a400d03180410404040820071400401c8500e415030060300d403200090503c006c81d0046030403030b03618070340b4000210500c44c14070400350791041c8510300d6503001a01290010b048659988039040f0030410442440300c0f1566410b04540c403980302502d91960108007246241030503a1505503524040707034100b00022601c0341040e00c480d4081e101510f80c1d880410125025001e0311035102d81d411030702020805515043e2064040700c0c58200e0140e00140000c205408241e50a184c4405103a4251300d44841d46d1500300200041540000c00410078154480b18801c42e00301c400030f403805404040841417880c41800c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 588504208 1250 588502958 588502987
    0x180804060809190602030c0d020d06061b0b010e07020705060a1107090b030619020c010e071701020309030301140a03060501080a0308160c0f060207050a0b100f15030c0c0203060705 79
    0x41c0441c503464126840c480c3c8101412200041810b510160140e100d82c2d500032824000d01400707003032005003400025a00c0030014a03600c030400b0394810f6110f000c4c0d071240064031070800e01b81d40440200314510060051040440c040c03c01c070382c800098412104216200e6005c1003035900080000f070b01080da850304008440728280211000b0b048040002c110903121000020ba8415000e0492000000a60296600180190104c03120124a0002031160102a91550ba035807443d510600d50a01e01030122040131350018000c40e801118404000d500310713402c0401d03402108047c0c14142c1c0d40001000c1c00000014030340d0003018001d00c00c903400340c111208141006098994001c14119030214000103151748260803014070100340e034001a11380c00640c003a191040081c071034000c016000c1d10070003510208100d0404003080c814510500101036403555041c80e030340c40d0041070246601c8040032030702c4901d100c1d101ea4002c0820301c8403403500b000503a01c45d8001c0385c00c2100555811300020000a80070342c460001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 588505458 1250 588504208 588504211
    0x7030230010207020a05100c0209011706060904020102070e07090515030f071e03020d020c010e1f0c090302010f030f0c020c040b06040b070b0c040f0b0306041a011709011808040608 79
    0x39000a600c0c0401aa00103036609810303005007032107aa200340d40544641e10940001640c1c40e400b42082aa65131201942106522503030055140d61240c08000340d1181004526507015507410b80041040900300740e4019000e00c4002c1c00d1408010407000700140c180c3c0c4540102c80e03810000042240d490822004403203101c0802009001440803c0d04403141c4c48501c68005428483d4520340180c0300c080b42440040a0710030b4441d20444c81d0700f0400031408800e170100d0010700420103c1c1482e401866111004030544481980c940c012502c0e0020800255010b150212500405440c0015440c900d452160045903400b918440c01a84000100d410905040c81480e40c0b40800f101c105040034940300410b19188601e0000070308404880000c00d0b04101c0c00340a507006004e40d000e004200c02e8071446009200d0300200c50807442241800300b030326020005580e941804950694130440e507660802d43c180060360010341125a5590f0794085d4200a6001b039003030302d110900c1000c0f0541d90700c1ca4454010000c410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 588506708 1250 588505458 588505549
    0x50c0a080901170622061707050a0f180c12051e0c0f091005120f150a0302060711030f0d0c15050105060a0c080403201203030720070302 60
    0xe098051140d140d56174101d41440c181590006003558420b0303068100500110b5010754603222030010f440e105044080b500781c06940c0252007010820750b6500d038500c0d540c0c40e50304c9146045074016005c032109010541180030346503038a0034080c4a248101000710201c1e035045400340642d0721060811141d03034940c0b000b555003214452200358140f920760034035020188141c08440d4881c481084104090754014019517a088480a02c04040752402480c14510064202c483c203208002101090a240c0b80100b47c6406490700900381030304080701076503590ba0910301c0120640e4107214a0141e0303400d0050400c043c0d0785001d003d0703903a190440440c0c80e00e0301181034510010042c0d1030a200050007543c6a04050703403030070b59082c90550783d10381b51801d1410880c481c07078001070b1a01ea00c2e80e401188040440e444002d11060a0305c2c89031403c4440350070b40791240010360b9480c0000da030002290f101e1189401c0c1006042c490a8117aa14856880e400a402103070014580b000612201c00d80501c001d0484024681c0b03440b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 588507958 1250 588506708 588506747
    0x6020a1e020d211d07050d2a0e13030e03061b0a032003160c05060a0e01020c1c09080d050910030b1201021c0204031e03050c0a080901 59
    0x410014041d484180e071030420410802c40ca92156003c1c2a03960820b0425903002000304a0b5203209807520000b0549003424203110710910000180c40e0600a8810281c030b0b4109240084008401d0225038516940d00400b04010b05807a40201e211006515900e000b03224025040b081103c103481d0240501d0185000d80c4d01ca50030a0301041000040e43da82c6074008520000a10f507155030005c0150020300100d607002084e480ca0000245400301d000b00118060483ca03034044246d0a02645d084030b44440e010001005074000c5008a10dc5c094035420400000310240e001604281a10403e0751401a60b09100b41c40b10048004011400c0c1d0030404042c003410021020b0210700100010140203449280a0f050003204400340e400c400ca0b03ca5400010200c50081140503031011680d4071038080c0d0041da2809003031324a80090900403400c0361007220102c1368070000c0000e080c96642440c1510312607144c13003a418441e0800c0005299181889504c402c0c0744a851000c0c3c5030040c2000051282000074242c00c42d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 588509208 1250 588507958 588508007
    0x31b07081510140114030109060e0c180405190207290106020703030810231504061b0611070803091002030c030f0403090f0305100506100c030302032206020a 69
    0x10450402c1150590307554412648200200000494802c04040e01d041e890b500e002c0000304d032140241d0031480464081010328141074035000d41003011889242d51090342c6900e250002201c034103064005c40d500612040148103031070782c02c4031980281e0317102d0f41040300c01d0042c0d06504010340501e00f242158091211004021640c103240010355640c00500010302440420350008040004110403040038000d041c03a0000c002c00c0c120746102c000e50349108c3c0d40744100032034250701080210351400d43d8215211960344500c284a80b8220404006810505440d001d40b104402c1e40000c041c0c9004280d0903105a64040d034078500b418980d824690704888141c050f50041003406003404040056a4102192045036240381c3c680d13182c1947d80707020315800740302c2c800c0d9041000018881c001c1101c1042c460110014041c0d40e4401e003c01001c92510452440400c1c60741c0580004280320341c0c0950b5000d888440748010141003041c80400c21002a2811502c143e00051483d0840e5407100f1002a4504840381d0110070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 588510458 1250 588509208 588509221
    0x40207110411090109090f111204020f01020102090f011115010f180204030b06090a0b1e04060e060d0f30020c01030c09050f0d120306051014040611031b070815 70
    0x401e207146c481c940c0f1068070350b07420611b8540c40e40d2080b030300145d0300075005684040218061780e5804080f01d09038410407002810400d90350041c0212401010300500c028240b070030f0074005440781944a01c440c103031841001030b00c52004051916180c003031320038080c120340824540021200005000d0851500d004e005020400010701047d580540160b4103c800c0d0740195584042c0000414030610f00a51000350a01040e0800c0504254035052181c15101400040c1e1a5020440e2012056401030313040003683c103880c8040b4040c0d806100c4460b114803c0c402160b07404401c0100c200e540f03014501038803040d60085103c1a81c04204800c07440c2c8080c00c0501040e00d400178040c19900c80c902c505400f40c48101000c01403a542e0304100300089074040006a001400c00d01c0050040202d809018000c402c0c0710700c07100e05240240c04400380181c1c0a03c0c1103180a00380642182e140c0042c0b0411901444240080a07959080301d540510f0140500e00504480745881503062600c4d40910032001e0103101603040c03041c23 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 588511708 1250 588510458 588510467
    0x403050706030b010e09160e0405130618060507090e011410050901031104030804030c0f14010513080a0506040c1a190e15040812030f04020d110402071104110901 71
    0x21107000c0d00780000c5410340580103071003541d40c0f4600f840e072000c0220100880420401100d01000000359510b002203c00310051008880050340c4006450501c02c22400009000d50030814050aa0540842a028069480da810b40380280d90340008550400c000303108026003551011300400c2c070220042c00d0f0045402c01300700d400709441d05c000d082290016026800fa400394000c004101c0f040d0141d559035640ea414440e01d6a0805d0000321000300c503044001505500d00c1045500340c4600f043c0000850384010010744143c0d0040140d81c0c000b000c0071100246001062010850850080014040c140b4144c80d00000c0c0c880076070010f07020a041d410143c0c0f001d60a03841a103500d40020407100028201c0c1c400203840c1107800740d01d641c2e44500744c0184122100c54500c09131044920701c40848480c280d490141791240d020413500d1040c2c6414000004002d40b51000d500c06010780100c000390081014140443d050707078032202083d2744045907050b95498905003032040510001c9121202d40c10566504002403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 588512958 1250 588511708 588511723
    0x403031e091101081e0c0f0a051801050405130504240b010201141902070510050c041e03030e040b0406081b0f030c030a0b150d0c03030e0a260c060703020106030b0c040305 75
    0x250360340d052030004034401702c06c004554650306030110942e229003540c10020504e500c00c0340017558506520600c81c05550140c0f0036101580d5009004a4419001652420040100610540303500c0703e15000e00c0e003c10350310380020200c040c00000c0400c0300b00e445800642903646940140d0102d16a01c4102700503515101e140320703a0300000038405130703595895041c150700e003001480700c505c402d030324200500160b12010402401159004003813025001c2c440124100b600d01c0c2d500c4058081082504c0e40400b500d0294840c1c0700240004000007112034540c013140e49400f144001c3c4034820001c6030301c01b042d9868540201140c00300100c00030f00c510550200840d89501501e80000c000030202e40215400000810140d66101c801905010b0b503e8030600380020705468a02c030a50201d0840c00d0b00402e281840070b803900c00d4403000319001c1035940009aa0b2000545404c080910310301500d20030b207915954a83c01451350b0f40c00f84d030000c1182c1e400d41c1021803080c070000d0312414007081c1c101700c108001003020030f08a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 588514208 1250 588512958 588513001
    0xc08190e120714120c0907050913060b0d0b0111070905010f05040911010c030215130309121a07021609153206040305011407031a06030402090403031e09110108 70
    0x2551038130030400c64505094440096071084001e010440d50a602001a01011000b290781f44d00307260a024940c02140c003140540d42c03002d0780800200e0405104c0e5004501c004030185485000f210602d010300c4c1c1014440d410101465858600401c04001d01001c03500c0904411901000400c0a540d6000e02c5000340f0321006060020440c1c0f8881070500170b21001d21140410340342e400c81444c1041500c0411248480c0803008260301c11b0011445c00301c0c01404040c40d5501103440c405c040031700619814611001010201180f042d04040e03444c410102000000800c20383c10b0101d050620305402c1088060250003600134800044078480b10104507015503421380354112085172190301d40c0d07404101e140c4281c1e00f000d09036609025020b112110007080d041e01c60b5285540800c61981001860806007103001e1980750700150601c0881c02514081c0403040d00244242030020fa06c521074010620141782c960390400903956a41003e0040c007085d08e0841000c2c3c0d8091030015202e1400b00c2c1c100e8580c09088499 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 588515458 1250 588514208 588514219
    0x2a16051005032e061e1103031b091201020903062805090c041a01090b04060c230106120c050406030b1302040905030c0109150c0f0c08190e120714 64
    0x140246400465002c0012003d44006090310b50701d40740040d10200300300b18044543e8031001c85181c0e4032445000000a03040308240503510395140e5821100c1c80101d03410850208110402442c1c0311542c2c1c1c2c02099442e0356208001580340c011034410141001e200034401c2202c11412207121070585540300555a10101000c80001e02d51101d1a2180c07074a540701c0101c6410a2030030f0540c500b41031007001c80700b810072026030740ea00c07080742c98225916150096100d01c0d0301040c507100c1600e00081c00e1141c41081801c012100a1181403404541801d541c42da40c00f48601d450349002c200244010407010101400f41614240001ca2550b9964a0a048000c121150350095450403204665464000030380054002c41181c0d183d4401300c040500030071030580c00300e80e003ca21020090850501e0b015a20388034901d6102d00d1740c80244000305444190a40f041100d51050801c4903034130503000400900047e401035035a403079107a01e6040c1840000461044811400c0d444401c0810030b100c0d0701e1103401c03d9200103844 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 588516708 1250 588515458 588515491
    0x30f1c06080607030516031a01030b0409051c090f1805060d023006040c090b01050d1406040b011107090c0509040603050a0303140f0402062a1605100503 67
    0x520000300460781114400b80200424030654942c0350f0800c1d40203000ca1090366680806040064044075603d02203180b0b0002504042e000c41e6009501880d170307214010340f002c42c03031000302d55902e818080e07040e8a40560403016810315441540c007450071405080d90206076855281424080e10042c2c0003040c032041d6054030f500c001016a11105800c2e500700350301820701ea500e1040503050759400c206000c1003507914691103003002c89600c03001030001e01843d0800c200e10504c40c00e0600c0c540c0500855a400d5046c0f1030100310032890545d59108810403007403104c2d0384c090642407080400043e268444503060400c007810340c1d031a5a5040c0070560600315141c1c11000500c40d001c1c0368003a20f0900851080315400f515000c1c0010a0050114100900a22a0340e04000c0503403426a2080c10035020307a2420355001d86000050018100349000741940c0c034064061071040c030301c10400c540c90400498080d40e8590000c0d00025034500c07550422001070a82102c1d1407501c1c00304003100406c00e000040c40650124903075032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 588517958 1250 588516708 588516757
    0x20402130503030d1e0c05090907021c05031b032413090c09060608100b030c09060406170c0a0e040902060705010207051b030303040201080c091908100e030f 69
    0xc0c0a00014503015050f41d483e5608100070000615070840d8600e80010941401c100408492060085c00000303500c0383c0341411106070a0100c06140100741c0030a40c030440b520042d508000b8540203c0400c51991025a20f00e40b00a0b026441011802c13020800c4905105004000c00b6503810386001800c81a920313907040f807440e40001d812104007683c0d5411949448040c81c24000042420019521440c00611815a480104440d0400d0848003144e036021a68804e00030313601513000450308184441c94280c144601403000491691041c0e00210100707464040d142ea5648074801800e5102c065140c66900300440c001000c0d00a0407400358481c411541d43d100c10301195101c170292108242c100c8021034a0f81001e1520a5030352030301d03640b2030302c41a0114a55415603e00001140e104a5041e074490400d5140c0040c0101190001c4403181da00520f4001e01d030309110480e85210009200800c0280805081200b001c0107d404001e002407c07900b080000c403038020303224401c03070b00003810001f0008540100710 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 588519208 1250 588517958 588517987
    0x1f0e150406090320070e01050d170a0e04061203111218010c060603081e0a020c04090204021605010f0f0204050a211a1501030b01080c030a0908070f0c0f030c03020402 73
    0x100da800c0203855124001409104000458106880c0c00a1640c0d046d03988400402800c0450014010040c0741c8104640c0e8100c2180d40181240007500c1c100b0b40007004031440002c040d03401a402000d52020107110708800c4c142d000e4242100410a00c000c1c01c0c80d0707514408480034038842c4098045110340304100418669106102890100b40c1204080200503200c0c5402c01095000380c0c420740c58111800d4048000c40f03039035401c40740300300066001458104038000600c00904040300080e03a0065081c00004482c1c002d07050900c007142d1140e00009008a00d8041d0301003180d40301081714804501c18001800303035481e084003643c1a5160410090360303198a040c00000c8450708a44001c1c0340440802982c043e10361015030345402810803d060060740c1400400440807074681e02c002c94001405200800c0c8099500d200841c1c105200f00030100e0040101d0311001d015034045401201c00031110205034041c00025500d00c000361251610441d510780c61178a400080c882c0c1800060301c103da000a4407039044980 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 588520458 1250 588519208 588519227
    0x120c1a07060e100b0102030c072304021201080d050702130b120d0c0209331c030e040e060903030a0f02090a060509100503190f0605031f0e1504060903 66
    0x901c0500003407600b864802c2c0c4540c051115014080d0624035074003659030011060300d4030004400d0045c10b4051418528466509442a0f152401c405010201d8240d84581c001070410303290482c89008517501d008081458920384043e8102084001d1100c000180d440e10a02141c007000840d0218594001400041240c40303608002074485c0b0640e0402c0c1c02240e00003024000d218002c48403d03005a60301d00c0302c0111001c41010000100100c41d01d003412440a04982c99a42500901442c040350031078800219140e4400005401190096426580925040c01802e00c503454074406072aa500304100610307074134000074003114829034450041c90201c0300c0c80da060b10907224004200144490b40c07110007501e554405c40d0306a00030342d08580a2a54940a90202c03801606605074960f4022902c2455100802110403114803542c1c44020001c2d16035410045031002c24a80da01003513404034040004400ca9035810a0aa0b1642151400748841c0c9004085c840d805500300002143d100c006181c112400084d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 588521708 1250 588520458 588520463
    0xd090620070519030501230f090c0603070302040e1003050a12030f0203150111072102150a0306080d0e0906040e030c011a0a06020c0f0402071e1209120c1a07 69
    0x43d60085110091452107880341140d001e41e008100d00008840250a40d2000a40310b011003403840007c920310000c02c20b8010b921008450540364122031a000152403a0700c15215900040d8001c5401d02416000445054028000c102840c0f1014610354845031240101200541070f18005c0001001941c001d4004803196000b01600b1580c1c0c0c40c241c42803d280211250003180022041c128030050940006580310545241d000445008040f03e003a000454410f804106c0c0c0200f0160349540e03d6510388806402e4801040c0c0b0007190b018100f04589140000760000e0701e04010085010200c00d854014a1642242040e200421441901d00609107144a10350546013198030344215a0358200d140300e2000c14203d02110342914030365403000c00300d94905140d0146a80001001c2603000c0c0c62500c1e038018801030380300711680d0105d0603412444007503080c864070054401301046c50b0400d43c0315900c90b0380d14001d00211100d96102280d6030720740001240d154010701074142404070040aa01c0840c0054841c13150703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 588522958 1250 588521708 588521719
    0x1092312042904150206040c0b16140c0d06050f060603150108040f12020a02010e3f1b190b16050102091905040501050f060f1315110d0906200705 64
    0xc00800000b9903a000c00c487c2921140d000c48030204015862104450b600c2101c501c00f010045501d403108021141500034001c0d591298091f01052030700e940c080300302040d014140002e03240c6403100c161410400001c0c2510300c0303040c0400812045070110f840481d0414802e00c0d10071020340d560300d04140385500350f0101070000c9030b1454840d91074a9000441d018040e100380da50641550004051002e20f500d40b000440703510b840381d90300c10144544070a480c00c0d101c0890300340402e124111040c0b5070030000e1068480201804401c13189240381066414100c60907041c801c5c00718501d00d8480400441d0040604560080780c410000105010b82501130b1108100c2c0100860402500c07012060600900c62107600c3c0104e05100000909140a440d080600da202503c40c030b20b0f20124132600d0301550b116a103400300254000c00c0224121181445044201c000341c1c698096182080056030300e010342c1640c92008200c0000d5042c004a80c0c8041401440644000d035058406582c4140f1428200c1540000c0d4020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 588524208 1250 588522958 588522989
    0xb070e12011b0908191502030c04030b0601050909161e020309030c03010504020901170106090603141b030d0f0504080f0703020a0b0a08010509070201092312042904 72
    0x4903019480301882c1000110b002454480c106400d0715030761104e105031400c035000115051252140740c0301003980688503811168004140581d40700807030308141c459003917603c40420188108240a8100d5801510074200350f030400c005400069804180103210a00c541070122030790008034050b011302d40c2c08450b03580220011000d4024025174a8202c003204521074440c00f22901014201880f030640a5a0080d0803100d03640c0c00c02c45040c0d0341070407500740d0491966881c400012080202e110b40c40103107104140380c01511503607010b02f078035042c01c0302811912404a04040da2250360000340312603003401d02c2d0030300307801548804400b074445020325072000100b40204940012003100c045030074016640f080ba5204034054840000c1c2c6064012210554040341d9520010700261401c0a12154800e41920022544001581c0e0b80c000c90100d807421180620b81c0c0d07500300712143c1824060040c469119821141c1003501e00702030a001c2d05184082d0700000700c200030500340c824829504407005014043d014500d030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 588525458 1250 588524208 588524239
    0x3060b0301210c0e1006030603170f04090203010626070804020120060c030708090304270906020a0804020f040c120b010905031c0e01050301030221250f0e06010c0b070e 74
    0x400c0007100c030b10b041c1c543c0c45c00380410481e02901c5500c0c15690402c050a080d9500640e0704289503106410502c00d1001c00e100c001030845a40c00210b003c0d00c42d9070b85070585e107905804000d0f5103203158402c0404518030340041005041c0d020340310540c000d8091900742c41c4102d101650700c9152064803034060b100d00840f01004808502c080045000d8001c0ea03a6210003a51003515141d104d01030b9000d03910b00040300c2090b541c1512811480c8442e58034aa80001071400050343c0d908049921014038000031403d81d2040005514101d95038403117200007a9000d001091007035030010041804c4c49410115259245c0c60028103920800854000d014090121104c203032418000e15010b807100079266002545030403240c02c09502c603506480c12258090084450301c5602100c41004501003070784054103204c1d00190401940501512003600e1910381c80d0450308030304044801e035804510f504543c108900400500000781d030300900441e901604000a140291203c40d0221440d4601c085403035400904130945022 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 588526708 1250 588525458 588525479
    0x60409061107060e1b030a0b090102040e01141002061501030f110307020a140703030f201b1503011a0a0509041d010e0c151305040606180603060b0301210c 68
    0x41c14110104444020890151401c00c10428036170140c6c2607080058000009180ca03d03415030480003580c00541010b888062140a03010240d00c100240300801014a040341403109c81d0490a00051014003483c0c900f5144015500c2c8000042e1410107a5810040d00c1704689980b1040310303400c0100300b4ac1c1e40c070300349014001e41c0c60781135100030b4525201c0200241900100024041e01310381c4d250316400c1440828007030907901d4038030798000840e180740c480341c104011410a1200200c8540009480802c42c0311072402d00041a41034428420740810403c010710103040d4040e0230140c02c107040c59009599425030b18086801b405102c0511307070804d060001c0340f10403000841007803103241a00b800070001d83c7c410b14102a50b44500c0f03110356802c8688103149901c800c02810042c00c0c560100c074070141c001a50b40d0045421200c19038004800111059504105440110309040013081c40d490280880d50400541c00000c0c4018800e52081080d070250448014030124000010b881e000f000240350550340b03e103e0075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 588527958 1250 588526708 588526721
    0x902040204030c170102030f0a020c0f07030804061d0a0504090212070b040e060108190c030603020306130507080307110904020f0607240c0206011205031209010c030c051206040906110706 82
    0x400540c90300702e144004030414405d03607100c0d0204048c218015103d40e01204025400600b0505d068003418508a1584100b00136810040d032040c00510385d16032404800a08420038184070f03041c1d0000803c1c118890746e56035405003003900c034120f50000d00c0380e0003072002030050070303030680340c0003070390061400c0010414810000790007103c883d407551000b0b6603501e01c011100100111991605c91000682c903550b1010036500142d0002114140000d80301c0d1290000392411b03070b046803540c2c01480703500d4488080060074002c03070004000000040d0300388400ca90381d0003010007c0c15420340c06881410001019581c60701c085500400c40a0440350341c40c500ca042101c611003106504002ca99a1410f020740030361403c4c89050315075686980981260303420409042c01c07160110100b40c1da68841402502d403203445000e0307000d0180c1c07582d00001809042c0260042e0640c0c201c2d07540c078810310200b40080c0b55900d110030201030b03005004030b50000d11044240b818100a00160300c0030b0345564004202d200c00c10900382c0c40386 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 588529208 1250 588527958 588527969
    0x5041202310c0f030204060507110301020c030706020316090501052b050c09040c08150d02030f06070203120705041512060f08160b030402150f0d29010305010303080105010f030902040204030c 84
    0x8043d6140020b80a4050b40310320310682c800a4010400d280104228182003440060000c0007d1314007151088440d01d075803c495010b44055600009000c80c3c4206a1805803c00204e820941c044914210010b8200d000c1e00c06020030500c02c6440003500909501440803000f41e5120702000681054012500326410001c8410b000b00d291603900800d10b070180400c00d109500400c0044000d1403440b050007003689002c01c0803a0148a01e8640224460041c4105071180030644c2c010f58603402c0070b14101e00d8070000038100c80180002044180b10381d180080d40020341c240c0703905043c030b0b00340d01d6055200010200c035804401c01100002c408034400c80086240c981c800c0180c40072884140d1140c0ca0745540d44025a0001d42c02803000440141c11000701003e0220782d5074a2801505201c0c0303404190055642900811100c110381c480710300036841c42c5003c0e1a120300c00030b103420000c0d03604658029152040600581c0e06100700560603000b40c034800c1d0002d2111903805801551103c1e45d07071800e08540350403030184 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 588530458 1250 588529208 588529217
    0xb0a03120807110d0c05030c0d1806030b03030f0721021c020c0a050f130e07051219020114040b04180b010c050601030b040f06090c1505041202310c 65
    0x1c01c241c18883c01c2c48201040941c0c000e810b01850300042902d00310b01a401c00c90f403d00081c400c000e80d84d081171000ca942007016880320031800300300080d0404922050381155050625002006c0803540340003065424038540c626195503203004905004d0910001c00c440c800c1c01d02100c15003d2802507010030700c4880b00800802c4100c00200030308080e078a48200075000c0e504003094910411a5251041c0b100d115500054002074041c200b200300101968a041c40c0c515456014007401c2285041031856000e000c407101c03010703003140784014500760200070410101078100071505056544428151045600911006a040d651190341c0c103180342c2840e540c01c21003d4079505e00260580c841d4000c86455185a88c824042c0046a086548148a008000c0c4c815205140c20751500c034000344240c42103c4005000701d1640c51201e180080d80340d0195040344040003080400d1100b040416034941a820210350304840030300854000411060840c0b1f4440c0610300b100c0090788d807202600a0360390000c040c50f83d071030341d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 588531708 1250 588530458 588530461
    0x2a010903120c0e060a1803050c0102100b010c1506050409060506181b0a0221030f100f091d0607080415060e010603020a0e03070803090f03010626010b0a031208 70
    0x400d001150725900b10840861007070070025200f4a002402030107058040c0c10302d481528160844801d07042940d4108440c903901c00984e00b019580c040298920107003098074240446120100000d0841c40c000740028031221031104048080000c0c0c0d0800d201404000c2c1040140c41c01c0c5040240107130500740e4485000c0c5070101c180e0051400b18085080c4622415400d5042101074880c8058a42d4030082100c0304600840416001002c042d554503c0035402c120701c4561a810080500009500301402a0000d20f0105804001f1404c06510900490780c10080004039030300006555844502541c180c81e45601612041101064010103074038016401b500b0118525004403a02400312501801802d44a00c010710041000d644a600280214015843c007110f1640445002c83d18103160f81d0091221600049200d0041d42001c440000c140f010031030081c00b01d00d1800c0702000300750307145080c070180c14100100b40400c028006d400180d0800e0001d0503254999540b804c011418a21100b07084000456150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 588532958 1250 588531708 588531737
    0xd05090a05030a050d180f2a09020c07090f150e040302031e070b090601090b011b120c050f06061c0c0b090301060b1b01110f0304082a010903 62
    0x28400303210640c03001c000d6240011028050b0b803030350011844c021140d511100e2140c02051966940b4030024442c2c12400e00d0741c016440d00e480c03240001c1e5103a045004200719004840341d400e080c5042120f00020f0f0050760343d520307146c1407810014160030041d18181041d01e0826181710741c6d800001080205081c806505480c0e414001c0800d5055501400580c010321020400c4200000080f80d04101c038154945800d90954510030449012500205c0e140c11030401000018450300607100303842000d00e8a000800c025480700380c0342c2109214041d00142000c0c22a41c1000d0107096810b0b80b89030820100c9055226445101c1e076281d0b4100c030868008c89515010340b100019501d0500c00059100c4407070704184c0d09090b80c00190740c2041100d550b00d507480f814002043d02262005048480403039010b12103050584910900b9501c403050b0f1b96902200800c03001c10314442c0a400c1e40d0300b01d58004030880c0d0f03580700d0003003c00300310034007062548250b100f1060500903424158884259030344603445000d01d000820 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 588534208 1250 588532958 588532963
    0x60501050f03013c0e06030f06160c0c0b0c0d21050a0b1c0b0709031208041b06081801150308090d050a0c030b250f110d050d0509 57
    0x1220744080c0710824801804442e00e90104080b84400c2c018510703034600038407200384d407010800a02080840d0598039085c40800384e8100000c0e8800c0085d4000c0c121420a06080c56594000805009000340c18940d4200c0d864403810700114050b030498441a41d0342e03118101482258018484481c842c421003207188082402a14407000007100d01d040748620148615840b40940001407102c00103966880022030305039160140a200f04002c1704000e1000340040c9032500416201a002e002800514501000000e40e14401e00704841c0301442c180040c2d40721460401500c0440795880c4411070000f8001017451a44802c600f4816112040e0013a064484114000d08940400f0307411040d20a1000702030021418110080130010070280100c9080001e681b01c041c10996081800c5418013a040d40c04c000341b00007034801d15088052040d02510500c0007500c503802420080c85003c09005071078520b044094010403844002c10043e800f55510f0b85046040180580c1c04800801c0090b45400081500d11000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 588535458 1250 588534208 588534217
    0x15031b0e040213050a0b19260c120307060519231b0408010614150306091503010e16081006050f01030504021309080d0608010e060a050903270406050105 67
    0x50036103040c0700f461211140180c200104920442622400100319548441000000150110005107581820182c5240b40a80b07a000d0303841d581c1b08040c404145d48400810400300c4120101d5204940d000508a99421f5000d04400608054901000c00c4030f0300450806280c2044101c4400700402140d00c3d103800b038080c1c0b030410072145410100e030010b0304041d007100c1850000b96104c2c80d2282000d80d0789260509595140d0000340c00c022500f81070404d6821310b00c0c0303c4198542c00c2c4111a042d032810b000811442d25000b07007005028500e14440c00421f450a41c032180c541c0000a0035034152802010a200c6070700742920448205129540c600760f489215882005c0c02d4440080882c015120b12100440c042c0c48094020b03a4400a6803136002c9140e00144a1908800c0c46601460307110070a032418001112034580c0000318a904241c00000c258101142c460382c032a11004c0009010b440d401100c034a03500640394108040003481c403900350310644008101c8861501140e01303109403600c4100454442c0107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 588536708 1250 588535458 588535463
    0x2f060c0a0311070302041104030204051b120c070b150a0504060b040b030612072c041208070e030d080f0a0b1309080f040e0a0e0609120702030115031b0e04 68
    0x10018000e40001d1107030304099050014542181c9006480b60000381c102d84506c200342050741c0c0001030400850400f400f4040e486080841074085c0780041e40d100041c0c07071141d41010951040c60100081482c1262000d0341c1c43c0581001440d0840d25103030b1200d65a00c9000a04a44544144500080e013450300340a6903040e00c1c0101c5400d403c1a2500020141c01d80015200d142c0c0601107039490284d1503010440c4500900c05e040c15400c0c4198165a801064042c4035030b80c0c20192820f4080201043c98074a40b500c0400d80e034074115103103694001d030440d407401103407200d1540350041072001d51189038040c24083c003a50062103051465120100d030803040311801104141c00254141c4805035aa685030311000b022801100103d262030f46203010409980e0180d0088021014144180310860035144618220000402c008003901c2c100003407500d983e041c1000200c4800003002691000f1502c00390090142425000e41e010301d026280c0c41c03c09501580340e011004048051003000507000f5200003141d000e42d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 588537958 1250 588536708 588536713
    0x8030313170d05070917010b011707140a0c0302010513050a170c030a05030103060e06070e210109030c02091f0b1b07081b06031506162f060c 62
    0x3141d5804803411244a8180301d08003007440300340010303003041c015544603448030f90360354003503900300482480c0200000241070f4080c1e1511242c59482d0340c06c007014540c00c4c224989050f560f03541340c0c03c085030340700e9441e8100c02d5034000c00310b00a071019801400504a291081d0002d200a41d641c880074265039142142c003508035401a01600e001c1440008080310130008012140d1900c040552504d00c1c0d40d00490200001400001c0104144425031013035075803030101a8050122828402c42c010001740f00359144034421251105c1203c0021141c0a00c0306010800f0030023401046807030305000d0b000a41502060303004200c5800041c2386400644041c03203042074030144444060f0300345180c000480e00481c2d010907079041219070038850348804100f641c0081c03440e03c0003030005980080c80200107032140118135010304024410b00c28400012540c0780c0d03080d401500c549840d1450301081038440b20f451003000e801d0b03264410741032200e100007036803412180b03000700410030440c1f51803810305c2068418075484201a4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 588539208 1250 588537958 588537991
    0x219050f0a08060d0c151116090f020418091106030415090309031a0105031605010c02060d091b090b0612040201030902041e0515090c19030908030901020310080303 72
    0x5070300601465400c44400382c030003040114185e5400380d240d00d4942281c040031552060a0002c0c6a0080071041d0101002c1c0140c40342040100414505035094091102000d4840e0703200b0071403203055415a00240340300780014001c840c1e0381181c880188020041521941401c0218a0b101d041042c200c07070043d41d000307007641076907034103107001c140100000031044040000801e40007000c909a0004d1040394a1a02560441540342c04100752415064020880141e20040c3c01000380ea030f00811030300714160f015039074903907240c028891140081c04441c00003403030040c55101003101040a09051410b94400b000704100964030035007042124000c5c81c80d41700709110103200080040d4802c0d044020000c5c07004c0d0000c1141d000540e070401c60b0000c003007124118684c0e5032003000b0b081a4909064450f22000380c5003105941403c10a8580a200f07102c2e069240115900c0d901010600c25404600c185410224468581c01d280081c0c03400b035441560341468400001101184010010003200d0040318881030010301c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 588540458 1250 588539208 588539227
    0x604050115080c030a20030a0506100e0d0804031a07030b0f0f12070b1c1d03032e0906080c030d051e19030509071203050406270303030219050f 63
    0x43d0307100410298034075440b4001303190030340d1132841d00e0f289046c004903403a51203140c20301c82d901c101d9070010040391144502d604000883c03500620201004034040d01c401d09081405c0c181030400388115400180a0650b808030340141400562510703001d43c00c180d50510020070104100052000c1304000503501414000000d41c180c90002d04e030101d55080041600d00c0c0d140d85400040310f60b0002c95a81e1555810380c80040194065441522600b50048a0121000c00b94100c0300355a800000c0040c040806555040180b02480d010881082950070800170301c03180d00c2c0d44114018040a119081c254031440a1742000307882c0100b404440000650f40700b07810301c0b46070050b1031210041030310020207100080142c01c071044060400304024100d1034038007050764184220150f14059203a4058101840300d1024540025405030488081f50303924a000c1400340a41e8650407100c0016242e400c5506660f92000000c240e015000340c40501e02c40c1010f0304041e010100d0a41d22885901500c03400c0f01f5042064211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 588541708 1250 588540458 588540481
    0x4050613020d0b16120e0a030c0201020f06190507031b14042c0c0c0a062003070f0908070302010c020d06020f0f0306100f1b020126060405011508 64
    0x40480c001801c014801142e81c82d8050110b409946210b01444d4040c07850700c20759080540400c041410304000c00580c603c000f103c0f030315503d50f0b050003010009007001401c2960f20070010a42480042c00039603146081903054081d5050825490603100c43c2404009120709009205000c0741c03440c036070800c02d040d60540da42100c10700f0f84140d2880781c008080c40003060000d125514501c941c2291013a010101d0b0b03501d8101200d01c84001c1400042600400aa4031480800b01d1407982442d031002000c618580307007172840a00168a00c0410f02a4070300030040000c1107520461501c0c0b200c80caa103d06200d40e03115090706880c0c504500019021440354180100141010074004e121103000300360050500c005048140200d500100e00c3d511400b1000c4203102c3e035031030700c48003401207110542045101143d0001011f00794551707020340843e81c003110807001d00c15a4095000c842c5131018402941003050044400050b000f0400e4a07014042c2b0320b0000040f40c201c940d01000403000740182c542e0100c5030354240354040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 588542958 1250 588541708 588541741
    0x604020a17090f010f02091c08120402150d1a01030506061c020906040b0d060b041d0a0902100f030b030307051c03020f040b070201080a090c06030b010e030f0f060708040506 76
    0x1416101d0071942021082080c4145c0c00c0f043c444110260303440300301400700000400c98a0b031320040c1c2c1c9042d20703c0c1800640c00c2c02c1155880480c9540594407070380c4600005210800c056015a0b40d680005481c080139400340d401289080e036183ca00780c608181c0c0c0c1004504446048a2258000000704054040105c01d90310240b07c03a1b0042070b02510706181c2a0100d12150003d51140b0607c20b40130034200404080ca00510303000d0030704035181c58149858201808084a080e10107107600082d000b0126a4110060f0040101140c02406d04005905c0f030300c0000308072500521800000910f400043c0095180200885200c0ca801074010300400101c50700e9501030100c031001c01402c0c035508101c5c0c06005d85025015100034604e000010340c9a004600015115100040c02c0101d928070300443d081c0000c40301d040c110282d5070a81f0340015480b0031080181c40701300848094942c27501c54220026400130700018008035a8001c0d0098801c00d858090702511200420b490041041c2c001c0400603000240580415 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 588544208 1250 588542958 588542971
    0x60f1d0a12060f0606080609010b12011a07051b0307060801030b04030807180902030f06031c0e15040b07020f06120105090601090e070f02070f060e09060d14010b090604020a17 77
    0xf4058030410711070341180e40340e910000200340c5180c1002070b1351030320100071342c010000d82800f186800c03000b92000c61740d2034050164002c60070440e4100742c0018900d50540e06d00c0d40d84002100c4441c451400c180d420042e010403028441d128045020480911500d038950480f54024103200aa448654096032180701c020a0030b070802c01700700c034512000680d89844100a09298000581c1c0e42010324001c940e4040003044180658405551082491021a18280e540c070b681c0c5013405a1010034400280d2024181801e82c43e41e041c0801d002c40c00e114524000c04030745100710b6482045226407401e000c601d01400c0d98050841c42c0d1351004000d5420014011940404145000c0c0c0d0100c1c1c80e198204003124095a02d00006100d11503a8000f0f681c04200e440041c0000c00c051804d0345140842c010312412000da9004e0155407010007056070360315880c003024003650340500c41280a9207030911140c0245002c24080b442000f4100101c3c116042c2442111048181c030341d50002c40102c0320400d0705445038007410a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 588545458 1250 588544208 588544211
    0x30315060702061b06070e0607030f09120302070e0f0112060b0a0302040903030c02010b0919020d0207050706080a0b01030203060a03080901020a02030105100317031608041b060f1d0a1206 82
    0x4150043c0d07500c5004050050b00d00c02901d248038003403d9294540440200b4410612800c00c070507003e26a140300907036801da5070602d801c25003180300c07100c11659001c5903845410710310480254030342011b0300800d0000581e11403030240d041c66550f500740b94a44050a101d9501e240b44ca08010700041000c40c0c02c80c1d500510064894602d003a42d03a401304e4121410380c0c505900103030b5143d4240031401e81c207010300c101585007150140c45a0900f107200341c1d14414680010a080c0e40e0014021240304055010740d0007052700f1900380d520543d07503120042d1502c4402c60b0170b0384041e4501100d480541d03000c0d200341d031701414000d000341407110b0469940c028250320000c2c2550661142189080040c2c0e000d0040c14032800300200c030209540d2961614208407100300b140a0b050841c01d10401c110700d1242d9000a40c9241140307030880d40c40c0c83e14204000303c42032035056590314081d021808504950052901c0242c040281e0f00c880c9668415803c040004041c041c0007584a18204000c001058840703e901d20418080c000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 588546708 1250 588545458 588545467
    0x170307052a01230d14280902150703090609060207081e01200a0e0f030a020424080304150e03100c09050406080f190b0408130308031f12030203031506 66
    0x1010b21407904030f41301100786184c990040d1921a0454030400390850881080360460300300380070314115080c070444190b40d0b2095403001e62409560f0343e0728031600032001040c1190750300d000038103006040d1145401500045455031000181c40d910000d0090101d485100c00340040c802c00c0c0190900b0a00e49040022856407a4000c0282c148400740070ba81e40b200c2150a0326655080b0700001174881d02e100d40b00c182c81440c1d1009a02c1c3c0d5518041035203c80268102c50025030681c1d0f5006074000b02e002510b030f41b0304082e400040821718400000080082c0c03803448005524020213804102c03103031805017412075010703082103480d640c00051703e4206501c4d018003800c1c0718801c035071110f000c00e00b1140c03150320409140e4409440c981200105120644500a0b5284003103207115054035218010800a00028186480060b111041c0058840710b03a000d582c0c0901c003959030f42025040807540412516102034603a800460000c0c0c010348001d00412043c0e8141c014606540d5210a0004401d01034003500760040320420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 588547958 1250 588546708 588546767
    0x31b0d11041e05061017040f080a02060a11040501120e0c040f0f14090607050a050d0e0a03080a0c0e0402160b28090b060f0109170307052a01 62
    0x101400c2d18120311140c40d1510b080c903024000e4a0b000303081140154882000c400103958070442e030001034410107018103600e48862070000300050401402170007074030000c1506c03042c00d1b40c0070030310b1030085100807418080306280c030b1031407410b074440d510905004c1001d9440d020a800c2c116000702c1c44900010056a03001c0c3c0c001c82c00f003030503580c03080948411195650880b00f244201c510130190700101c01c00010210b4030300704078070380c2e03460001600c48410b0100218030040780d144101c0844110700200c0f0018821030345001da20542e514103289040380800c1c503440010300c10840d184518048100d107a03481a90105000c024030000303602c0020324400000c88800e0010205a0001180c1c0c0680b01440d07000280c0400c005054400c000c18078001d09076242042549404299100070302904075504443d2500c03983c9548005913041034039a40070031050001c00303191000c6150080050601075000f10280c6405d00e1060004140d00c0c5c0384004030709031404001011030b581d54400c0000340c0101c00d940040610380052031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 588549208 1250 588547958 588547961
    0x6010e130f0e030d0603200a060c1b0b040311101d03070b03090706020d0e15090429010e06030f0103080f0720010f020609060c09030123070e031b0d1104 67
    0x10800e07071004c0d480d10001c000308002c005a24004c1c0301c166504d04201e0452a0003c0c8aa41d9148070b90b90404c001c681c0c140d07051054940a8240d20742c1c00d4003215000c03030790301c01070400c4a420611003617500740c0740440340c5016070030420100f250700701140d034440715075840c80384125010100c12000d072038040c440c800000c6071514038100210301418001009084251510304020702d0501c030b58404800300004103c40c19240c2e280c0360005100c0c00060442e05840d040d07001e0100300204030004041031158228000a42c5040d5890304010b031801c402e80e152003070003034600203215031488161031810b6140b841030010008a20080054121960307001d03041880c006207a00da08142c013400070510030840c41500904545076800680724070126100e80003411091412010f030640754903000300074003185a070005100c05596002c3d44960001d40124071400402611001240041a000c0742e070718001c504a28203218075850b00150300e034680d42c0408080d01a51900c3d409010020104013012184040c000c02e640d0a6565103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 588550458 1250 588549208 588549217
    0x70902030a0905060105030f0304060f03180321140f0405010b0603100f060903110d03030e030d0203040b0114150a05040e16031b091a0909010f090506010e130f0e03 72
    0x111001c00c1c1d480b850b0034101e090900c10b03030140703100f43c0c054400030320040c03404000d940403902c4900300010b005000702015030242215051100c045003103a0411002c0540022074107621400b800c0006507084407200e05202210422000703501700051020026002c0040304884952051081c0300105103d00d1100106285070002d85940030b0186080100b0b00c0316850010019008002074940815510329648034500c0ba07100380641940640c581202041c18035001c2e800c4100c40010460032203990b0801004000c000f174000b580c00f290003114910001a2010b0800000a00d030003009000c00800000302c81d20b003540c0c0d800095000305001c800d01001030078280344517070148a004100c0e076128030344a80311001411030303000c4450020f2003400000001d0206030b102c000d650507075685c5d0300b6410381c1c40202d80202c80360703025080000798440103040010030910142040e9000b2035003c48001c0c411521100c005450b50788050030055007100100e4003428030040c0317a80240c2403440e0090000501c0c80507032031030740307003180e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 588551708 1250 588550458 588550471
    0x303041d010303020f0c01052703030a020c03010e0c01021c12050414011401140f04110408030403051621020d1a1503010501120f05120c160b0a08010b0c07090203 71
    0x2100d00100180758050208903161000180070b482400c03d148000782440c001d00300703c55032210709982d60b03808200c800440f038600712100030122910f44000000096603080bd03205c80030301035402c00f4000b01901c40b00160780150203405802030031584035041c510240e07210226004800b080140a048040400c151160704d0081d4090420b1080c00b012841000c1d0965003019003100501e0810030040101c803810142e1042c41340000c94901d5000f0428000003405804602c02040614000080003d0321040000080080320f01c1507003640c404207610103072000b1458440c840d003600403012080300d894003080b1220301d04e0b07030078402060419401020784406010101840340d203d12032a14005012100c138400da100c5000a508400a00c500d40c180301c0490000d00b10b0b10001003d90500b050200d0811005100c800301400c001d174103841c0c50306e04803809190b40f010903929550f130307641211170042540c500c00b600301d03041c00c030980e1110580fa920f040d210000660041118241c1401654404207000d06240000e50140c1c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 588552958 1250 588551708 588551759
    0xa1a0903160803150d0b060f030c0307090606090e07050a0507020103140a050a150302010c170403300e210c130f110a02100b0324041101030c050f0306030304 69
    0x41d1480c0380313540000104001c0342c810302008054030005080c0580165101c14140c80100c01c5456840c08a464007a01c520856418001c200c0b0200e0388841650108049902030703a918000d85542d030280720b0070100c0036903010300010b2041000c640494050b50003411514411315000540400c5e8103424281e50406551040a280d12030050040d206401d0062a1948180d640303d401960b295900103442071001050060400c13800d030000c1d014071139100094030001c50b0002c0980080300c1d410101284243c410307400300240c00682c001d00b00b0000d4481c000803000040c001d404030901e4020310302c8800050141d400d42e00164816100140c04a4076200b5502d5200302101001207140941503010906480d1804222115084103019141060350700086001c007000d401180021404102000f090410740c100c1c0880b0000104424007020180c400500684118010602c046140c9800c0004505a800302040600010020b0041c01c02c210400c000840c0c04c8080102100d18080e601e0070006401d80c04441e08004c00f1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 588554208 1250 588552958 588552961
    0x1083111090606090d0201350f0901150b0705070308041e050915120a08030c1903050403080c2514070b0906390616020a1a0903160803 59
    0x14240550042d41040e001c86000d414840810003240e60120304001c00390400081c4200e48070344200c0a840d103109503070000c456180101c3d0440c4004018081520116000c4096134002000e01c1c0041c400c0b12a55000c0c0b0440d500960f1800000900d1074211040030340310b90046030400400108040c006100500822440100404885281340901a080c1c1e12550050214000b04407900d8100d035805440f0a4045962a401440c044116480c2008117613005040810000900220a0f04d03040903003507142c0c12007640003000319000000c5041d500c0a4500030042102040401c80c03804d0410301416000c002c0940780030501c030389209000000400d4080540c2c0701008086a45486101400a0009410343e000010f1500c030017030010078403503c185d0549030490b480510fa190354165003950faa042c51600c1040014510b07244900d0b01762036070016100d4961081c0300105600380d40c5c2c0041180c001d00c1d504000081a00c805612810040400040c01031fa058002000300c1d6250170000340705454424045d5608070389a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 588555458 1250 588554208 588554243
    0xf0f01060c1118070e03060f131403040b030612010209030d03020a0e040923030a2109020d2d0f0f0606170d12060b0a0309020a05040e1f0902010831 65
    0x717020072600b0380240c00090130001c044010344d0030560014038a04003821030382d2440c24051140c1a00040004250100007000680c07000104050f40c02010b0899aa03016203821304002802c0f8490008100c2c0c264101042d036140d01d5001e5400381101e10044d040c40b4980203a00d41c00a000c0f00d003800422a00201c96480020012261644070424480080029803030070720f0345100035000c209100d002c1d142030318010641802801854015010541c0d01602d016815441403411100190101c410310031924030403101000361500004a045034503030008008001804c1c0342e296110300d40c0f07509200f520529200ca00014110310800064540a200000a082c030a03001020007440c0002006449111b9801c2007414000a0311890494150070b82e582400070b9040381e10320100e105503010707500a0394070900e000303103034690398402003602800010070f1040c1014540c42510800c007201c0c9003043c084d0000b43c000001542e83c541b00e9000c118903120302a071500e9801c59650900400f4070038113004650201c200c070284041c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 588556708 1250 588555458 588555467
    0x1b010608010e0102130e0a06030602030f06040b0a0510080c040b04030b040c060c020a1205010b030d0f0801080303070c120504120609020f030f210d02070c05090f0f01060c111807 78
    0x210b00719004000d520749010f16a100a07100318034000c901d04000e005010801090055120320011640400195128500030704401c0c0460011601c8500460070450001401d281076101032050340c2c401042c110456400c0c90040350398100091020469140401c000300d5010b82001c0540001c52094081075824030341885c01c0e032480044c99225005104c800c070071480060743e07058460410782301c094204038503003401810102d005d0300040b02081d07010300600c510410341661020603140f0218141e11042001c0c3d9a40581964070b110031500080040c0001d044480000c0614a82c2c80884034503150060030551507400003001078524030f81c115806592802e41c031045050080c8840c04c1c86104030090171201540d600c0ca50344031041c03040115024009442c100c005010340f4070036100d03985400d180464947d1028501000039040600403203114420b440c0c0091410684502c4062091850002c402d40c50791030444190f0301e90150010440b0b1140d000350101d8440e89030780307481840703104081041004a0a04801c00350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 588557958 1250 588556708 588556721
    0x50a11070306200f07172802240c0a170c070209061f050a0306030f08070c0512032d070b0712020c0a20030a030206090d051213081b01060801 62
    0x1080f40d4090000000140d03040041d40e94076038114002170100e0b03c4204c000003451140011010030f092601c01001c0703080c1e028140a00004040e82c08844507100004410b2511200c01d0f2080c04035410288002031403411040094001d0034110704149540c4100d40110702a540e004072940001c0e03070008a12031b801d602c0c00c000b2441d04000300b41c6140e500b01002c030000301c83c412520f01d0b21009115002a0361407a051003a07103c03030015500301001d10701c0720501d481e06800950003c4410360b070807030a250340458585004150380c0c01080100b802941742500e1100c6080082c042c0100c2c0c4602e10011a00c0c00c66031072031000007054541d114a400c500c9600d4080c41c0a00036a403481d503a007071140d2043c42191050400002d40040003030f00f001d805090f40514001e00e1030f03490001c403691078160003149000d074200f60300040c03203d000c0d82240094a0094510410031266400ba600a0300c000d20300c82000b09030b06041a281000f000c600072152145008072064460b5258000b410b1120850303955844204840e55082c460710 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 588559208 1250 588557958 588558011
    0x3030a0c180602031803071211030c031507030c0210050a02070201020f12040e15040e2113090f0902030706020307030306050a050f221b0e1906050a11070306 69
    0x100295081c81c82c02941d0b40566005590081c0c04602c02003495034041041e00000c00040c0ca015081030300f40e25180920015400c082c80c040c0c4141c01e0071031010701c1d000c603143c1c00042e601629801c5e5070ba11074500b01d0145c12107004c000258040c4078190040e50304c80d4041c071803180007585800b41e50784440f81b000a180c051400383d9490140c1204a0b1141c1288010040760200d0f07007402c880d8103182d1517407121803801031001000503901500d0000c50f02480d45020030341da1307030703407401c00107030000304c0220800008031441b40c150028042008c100c3d06202c034401903401000490700b141000640b6034500d0b80880d181c40050703003000c00903a102291a200f0150b050140d06c2c0601420b03100304200718074103808a1100d0405486051044460440c17400c40e444a801e910070362100c00d2213042c400016000c11050a4625948140c40054024504031005082c4a008017282c940700858140481e481c0c82e00841c0d0300c2c0c0103104000200b08607030401e280d18103020414800a503014100010307403292180100c002e0703a040030010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 588560458 1250 588559208 588559247
    0xb060306150109180e011a0a060302250f05070305100f06080a110d0606030b0a0b1f0f1211130510050901200604031706060c06040210030e03030a0c 65
    0x284401641d200d5898401c40b19509640c40c407a80040d5103160103818001c182207103943c82d05440c901c0800d07c1c90101030134281c0070340381e6114054480d041102030b881400441413010107a141c1d035054282440c011240214080c0b810340c84008100d42d56141041a51b81c807d5540c0e90002000d032101c01d40d40e200b8003440d807034814801c0200c50b1804d0310003521540300041c0500000c1400e00ca0300c0ca1512403030500f043d004e9002c0c5040000c280c0328a010755114009980e0305490340d20f0b0982c4186241044200301c0d10b891041d5126031460003035880c0807601640b48a0000341006101008156000700d01e008401407611201000340c0c0700c28a100306900e40b212143d000b03a00c80d0050302010420160070408850041c0028a07108400d0620000b001c058108960400c0e40940728050070401810780c06020110031101140c503124080d1228401c001150085801611140c1c001c1000f00c2d0040ca0021400d40061071282008180c25500e91071003406d5400407078201480780c0d107a004680d1001c1d0300c4401d035840f10130901003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 588561708 1250 588560458 588560491
    0x90203030a080906010f140d08130f060f170609060a15122004030602030603190b04030f090b0d18081b060f040b0a0b0f0303040f180506030316110405040b060306 71
    0x650b07401d07e49030381d07189000d02d071403000c22024424042c04a990003881030109180c010b50b111149010034010780b20310000601252030440c1042d110300d011210b9200f500242d525151240c01c100424854090101c60341b0424a91000411403840b074204411047c1984643d0641c1c4441c0000c107003078500300710759041000c0c0282250380c2c04040403001c1d142601d030000750050702d981c2e5032008a0700d003c80455410264150080b144001c1000049007a4440c5110341e685910307550ba044010386040800e80501425060184400403602c00c942e4400180102083c1040c08049415214030046a1061940c034118030b03100001211090703020846681c010203031402d6042d0614141e2200024a10054160700c80c280e11800c9a02855644c080828260400101529581c9584d01000d15410100d44100c0b802490003541061f0b24903142d01c105449480d020b4051454031903284284c100401601c08201d403441d20052200c1c0705501d5600c50244218412003c00502e424400201442c1c00e100600c0b40c0d104144042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 588562958 1250 588561708 588561719
    0x28050c09190515031003300206010f1806030212070e0c0a0f080c07020a0f0602010f0e03090d080c060a020d0b090603070e07031409060411031204060e04090203030a080906010f 77
    0x3031089514103030200c0380c02d484e51100c0d0b1800764004915440900b1404902229511341000c840c542d415a00141401c144140340c11107090361030320824402e403000c000001c40100609a1030004030003000341841d000246494032980040e0404222004039031881d0700510080c0840c0070310b1060141c20810145180d0708001e0741c5000284186400100841080f030b80d01301184074441c1c1e520a07250502c2d4001e180500242c9c48052a901c03c00661090100560030f00600e20035405184c4941603000100d40c024620f05440142440b00004200d002114454020050501420000d0010f40c6c043c2c0403010003d40d60350301c031150040c2034804214003640708040c0c0c0300c140300003540c001030207108031208050f08000c00e5941d4207061700104840c0044040340300702d942c1085180840072907194452445031002641d0341d000c207414195107032120303c0300b50041101000140100d50044802a0b00c03010014030110303c09004d940443c1c1590004441c1c007002c25141024410b0080040c82020302410591a0000c001803525 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 588564208 1250 588562958 588562969
    0x17011706070219150e010c180506120c091504090b0102070902120f0411031e10020a050a03090501180609030809030a0219110a0807030b09011428050c091905 69
    0x440000d10141400c1c0d0140f04079800c58102c1c581c80081c45000300000942d201c03000d03010804030b1000723000c1e14908902c0428180b4280c0296010310000007400d1680d691224075620650b40010a03041d4000c000d10041040e050003070004001409038030002164105111002903d80440794100300410750050181d048000700b42040c3c04c2c0e000740c451400c2003042e01d41d0305002006c41d01c105e407002c1d0035000f03008640044141410b00030003030180d04021075107003003507079500c80c0124001e59841c2c400043c0d04202d0302020718425040400314501030b02c00041da12035286003055a12101c400c040f6400780e2140780c00c0040c99085480c0a5104481602951802444502c02502c0e4190810f01001015020075510141b1800310066021024094174a4440c4c944400a080d80d03895580302c112604100d100000711500c1043c054150740020740c210300d100c2c949401001404005406441402d6260319200174a0703001003600840e4082c4559160581e031390080d41050140000070000c00e01742e1640c0300c203420002e07626607 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 588565458 1250 588564208 588564253
    0xb04020a0f0c020a05041a0f032407020c030615100c022404050405010909052503021018090203010f06090803030a05130602180a050904150c170117060702 68
    0x80303242a4410303010503c0000c80300034031a003090707401a181c0481500c114800d1506500d20300c00849002003404041c1c0e0405a556415110001e08280303410b107017819031044c4056184d0404c4440c01525250140e0201091030324904940401c8034668455500703003141080c9154201c010080d141696000ca0b01c0d80100b40002c1d030040b0a446a542008403007000c1806600a84029200c0280184800e5039100d07451000b6110307402c0203980d2409252289030500c2030300058a6050612250107a2405180d40c007000700074041900c05000780032407035914901c48840b00d05000c01500541e04016100d50400c05101c40704078983d0016020b002200c1001c0c0310761071002042d6075010350110004125a50384604020b0304444000e4002c14a42c00410303001e5011120010440c200c0b9026034000901c04c0c0d279842081b0b0448003d55005d4000c0c0c07007220a4a00c2c070012600302d41803040e0302d03080a8050034030504600440381c509038050a01540c1000c0c0349040c010090042641210403403000b010021a005500b401a051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 588566708 1250 588565458 588565487
    0x10206070906110f0307111503040c0501050706091b1a0c03180103180f020108160e042a090305010c110706030902010201060b0f07110a150302160c0b0a02010b04020a 73
    0xe07104500f0b001c0c40c02041924000105203040e240c9660b0710340390031050007003082c4c54980700707101802c001050b803003004080d40d1251b0b030803100c0403d030f1900e0140152100c3c0d2100c0016684140c4510500c808100081644486d103800240c10502c07103850003e002c0100504400c403142d40c03d10410036400030180002c00c0d00e40c0000b411030694665440c801c0180c0040150070440841c034892070100300d00b402061454114145c0c000e8807200000d5807032901c049902c08414039000c3c040760619051313912a082a510401d500000450030240003007014115900741845030f102000011070307030401401005002e0046450200242c1403410700c003403080f180e86407900d8060080904147e80d036001001568400d4106000514000b01010b030b031420401c54901607540702500946009401e50851811410040040c90848040d06003000ca200a1042e044000c1d42c0254000b604a103040070407070000c1041030f509400140401120f11f691030b0384032080a801c0d0742c900d00d01c01b4030840c41840101d07544c1ea0080c1d6894500381 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 588567958 1250 588566708 588566717
    0x13080303061509010207051203070b0f01090e01020f0f180a2603070506130615090603061a01050324040c020604031805031203191a01030608010618020723060a0506010206070906 78
    0x210007000d089d1543c018100050600c000391011710031000343c941100c50688a41c0c3c5000d0014400d81d8250701d00380d108181d5a6900c1860400500051488441c05803202d0481407040b000d210102c0400900f071a4042e8000c070840c00f05040e03d210034003032811114000780c40394101550a000d040e0702c03482d48404004001c8100700311000420420000a86e00c20040d22a900301108105520b0300b00305001081c441c08203d4420386481014002451102c00407000b0400507500c070352440c1d540c444804c02050442e40c81038031114600582a00c02c3e41c0c1c5000f0310074042d034190b00804080c40d103401d0080c854103410040d00100d642001c414041c0303490100e80c501c0ca0304050f00e0348558a4a46040030b80c002e1003581404480b00b071a000130442501400c01c41039078074038000d90741841101d0f110400c207400c82e00540f04e014801620641da000e01f03000702c5c3c3c000d40301c004d00601c201ca0b01f48030040b00e2407580c04001d07110100280c06c11000c000d81700c4014800c0540101c000e00c002c0c9414500001c002e0000d0125009410900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 588569208 1250 588567958 588567979
    0x307083a0e150d201c020d020d0207290702101e0c09030203010c0f020304031e080a180b04080a03110f0a0f0c090903050f0a02031308030306150901020705 68
    0x35200c8080c422012151100c54982d038090b40720b1010b00400d90088281e44c8514110b903081d9075600d454080e51030040380c008030803610204c400c00d44030007540030115081c0c450b0b0b000c0c400401c80070164409041d4030f9015420840c2c40d0009100055500d0b80184884100c44000d0320600407219800140030058000c0300340c00081d00340804610004100040240408a604000c003c4000581c40307030030070044034401d8009020300c449010060354014480603008005910902c82000450b0310300700007004c03e050400e042c400906a6840f1040c1c20b81c4038070020303804206030740103522010300301002c420002c1049112075418141018031440d259a04c001003e0300f00201521008205481800300607a11428a01128000c8860f4640250111b0120b41c1c00e4070458103241002500341102e0040c400e081d941990b503145041e022503c413207000e4001041b0765007180310501c508400c9640e219004005800c440c00199200d240c03107401c0146140399401c0945641d8418400d15520340d800003608400c1d100e0407140400350 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 588570458 1250 588569208 588569237
    0x15020703081e04060c0b15100c020409080f180306040b18010e030c100e060108060f090c06030106090806161209110d060203040314030c0a05030a0b0307083a 69
    0xc2503148800c00756a0009000136400d5008164098003900c5484e00c02e078a40c3c0c4071210744c0400c1e001303031a034980c021024882e400e03002803151158a0b2814401040054001b0240c0c451000307070380107800c03071142201d40040c0b055145202c400141001340c40880040c245450a584c0d250480341000e400d00c0d00d8055112a0301d44484429044100300d49454400c403a12038030740041c0c0c0359856013a01d0020301501c0c64541c802032148404610705040c0d86090006012944940340710006a800c0280242241e00402107410010340d500d2009600800c070326541c964103e4100306c005400c22034094514540c04140303100b203075071458000110b00564441000001045001c600f050000e00e140060380d142e02c1142c80608c01d01304a000ea01950007980a9a00c519682448004024684c03000b910103000340201030001900c014446d1000f1548500001e6000c104a0194070100385000842e412494944d08200f0140840102d41d06010741c0e00d91014a0a188c0c0030002003103800da0b904082284420028440c00101c035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 588571708 1250 588570458 588570487
    0x1b0f02030702180114240c100504030e09070314150d08070f1406040b0a0203040303091a040302010c05072a0f031a010e1509090705040f05010509011502070308 70
    0x3580240c50300d090f400f2a05140500410309015141110302d500b0754034030017400d26580200c908400060035074200c60f8105240e000c01e402000a28100f03108040828010040d10700526010b60b1098848250542c2d00070100300000500410350010545080400c0d40340074003800d8515000446002d81110000d80207002c100a020034440c058501031001031644100600352451620316401000e8511440345400000c80d110101690003412195566011401a1304540d0082d90014030030308000440403150b0b5110880c08003a089014480707101d5100300010f0580a0046244da8030452801512b8100310343e9840001c800b24120101e414000c0007078616031004040101c10242400c0c0441c6d031501030f40ca1401e513860201c041c400480f204c05517400007500f01c0d0001100d80c019082140c1c070307004010090713040c8980381000412407000e520484000041a131941d22030244101c080c80070104841d0304010a00c003941e03106038449100703101102001c40c2c4050740406e0000c10f0f290301800302d5503180000700c202d00d23 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 588572958 1250 588571708 588571717
    0xb1f121a0f10020f1501230901031103011e0e160605120a1808131a0d0b18070903053c2103090c01032904020d0212040c08011b0f0203 59
    0xc4c10b52241c034104640240500b42c82a0484088940c07170001d40280e840d007010304000303040480341c101c8200401031001550039030076401c01500107000000c001070351141454411490b1048101c00550b00c0306403100c4244c0c1032100c82410032040303200000107486d000c0d00408078480d00b16007048240c445000b058040c041c070740000000e50880c6281011607040d43c1842c0a69602516a1904030f0300080740014424102210400c9802100c0d440b1500b007400d060a80ca01030030302440b429030f000d4074200000084040001c0c845004d42c02d595a510700860851400d240f0b000070044d110440d03003100d012740c0140003a0360b4806034003030700080b00d1540e002141560900d20f42120794070140150310094070341c3c00002907020b01035031240880104440266074075400541c01c9a111940409001c0384445a15151210b10290a004071001420061030170803103106100c00c981005034808105c1a140781480140112108090054101c01c002040070300090400c01d20403107100d80d241c4c0180000040511030725070082c030555 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 588574208 1250 588572958 588572983
    0x2090306090c1009050102030304172a010b0604030803041e1a150d23030d051005090c030f010e0709030503030901050a180309090b1f121a0f1002 64
    0x19000e074200304180c00e8951500005041c02549034040d501e40c00341c4a900007034200ca006030007940c9107443c1c0380c48100b034000c90180c3e007103000402007090b8091a40c06800700d1140306008108000040c1d9950741c010301303640c0301078461485450103210600110b6442c030b0450ba0440d5001410300c1007821920031040610f0408100544100718096110300e254804841180c82418100140464144083c08101001c0ba039450040d190304a080321103000000b541a5406201c4903034400c5a041a100c203010800740e91040703030308001620710207400700b0040c2040500740c1d8000c0145041c45080d844d080c0601c0c1221401403181525806182c40440c0089000d582d12001a5402c01c00340c2e5582c1c0f805400d9280a0002500c820b8502c0340f4118003040c0301d05014601c02103681c0d041d0744802d10a8600039045000d0b00d05181103980c098400e01d40250350325208401c1d25001c0e9076980342c600f1034000c10300368181154420940348516055490340c040d003e03510021404202c10044464808004041204901e84964640d05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 588575458 1250 588574208 588574213
    0x5040b03011401290a08090705040905030706050a0626161809020411030f07020708070807350f010b040605060708030a09121805120c21031309150602100c03020903 72
    0xc032171100d502c0000c0602c80c07400b08007241ca12554034414041140c5880002914640081c040400040d40d66000b00d500491801c0303000c1070481e200e03c40c110503410b503204200c118107094241d02401181c140007901902645103456102c09140442141540c6220b64406943d203a40380ca2000c2190340301d0380320802c0384003e48010382d1a0300d822126a0309140c5c09680007030140c400e4440026902030000b0724002543e1b641c501500f5000d10b00312440104c5a01300384076951b490042d62406c0d1214800d02118001d105c2e40354001d01c40b4402c05c0c4800c0f42182e00e40c20585008606000c2c05001d580c0b929001c07a14150740c0011100d03600d50303a4400303d8000b000900402040061f02c100d164180952102d030300da4400c1d92041c1d601540966942c10041480c034402da03580056040224091201d00e40460b894000c607914410140303100000b859100d0460380030140070480c0200d890414000c0300294440c10060303480e24001e5140660802c28007942d141307440280030102d03549421040188502c070b40c0503140c45001c007404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 588576708 1250 588575458 588575467
    0x512160e09071205071d19050603120901091508010f060801030f150212090c1201091509050307080c01060e060d210e04060914101a0f040e070905040b0301140129 71
    0x400146600040d12041f40801d0f801c0c2c00950a000e803841254080c0200070010711504e507144154000030b41207940e83c0e90500540100006003426600503038510b80c0a1541e03400308030740c100241d801220358550060b40800c42408010710000309000860b0b003400d60401041510301e400d03020500c010703100383e4404001c0d0009507001d1018012001031031f0101c003030007200e5003070f42444503240315422640045d00180c040c1610340706006100301c055118648103406401a24074224454907000300f10b900a002c101c11983d9100010030140021004d11900321204503041d0001c80c1071600d40e000c000003001301d240804107185c2281c0c0000c41c0900c0300c0c0e000303d0704c008e44140201c0782da801c502d0004062800068100307404190006085094200d50041992642e04600e000301540c5822200e868010302e0900004d20010840442e4102260b10303120300c5aa420340d2001e0006083c40c05100580d042206d091740281e05000000c1020b0401c0c1c0d10490649602180d01c41600310000951140143d034810001408500000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 588577958 1250 588576708 588576749
    0xd021308240604092a0305030c03040306050105011407110a051003051017060f0901390201060f06080910230f012d0512160e0907120507 60
    0x1455903084031109400d803540303540c644083c8010741d40b50100c014000c461740c4580d1048000c004400882d88200c442d0f000070080d459564a038074660000c2801c028560010030100100701c4140510f5002d003000780380039108203c486484070b03600d00502c04005c1c40d140640741718158548a071106c07907004060052840c030b03401c11107000c090000d01069440504d01120400c001c02c007130341c9001d0100205820b902c024001135440e448981c074000f20240284d07800d95264086042c511121003070414502001c0b2001081c0303a13003030042c0070f69020000c10750b4034150b9050948c20408914400c0d42c10045500030300b0443c0142d981d04147c64108083c925007148114500700b46901c604085c501c40649001088141c0e03441a22000758104800000b44a40c00c1d04405d000b024007401c00e11500315500300888035901101c40c0c0c0c1c0750b40000d1106a051984503180358041c0c011040b40388803010022000301060750444038517084c110103491707c1d58000e00580311842c085010744005c10004004943c000c1c07640150400c48034034001e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 588579208 1250 588577958 588577993
    0x10c1a18010e0a0c06051e03040606150e100c0c0510031401061713140d030507021e070519030506090a030f020c01020a060f0f050133050d021308 64
    0x20305803894190320b0015020440040018070641054004026002251400d0011203641d400340044c81c12100d00900c1035406086c0150285024500c501c002013001400c100008007550100c080b8403081103c101100540f0b92039030b50300d415141c00d00b880c1000209241e42819040b00c0c00e141d1007031750006159460300300070a0389540001c90804100c40410180e9903107003404c4821803008601400d01e48042804216881d40880e050b04140d0700c108401401000710580090800354050a8040883d440d03c0801c0340c0300303906101c861902d01c490001c1c0c3c0703004011940c00075581c2115000e11805522840c407801107580a030b600314001194064115043c0c0d140040b109a1244003a801c110042410340c03140700030301c5001103040040c056041c4d00030700645c1c4903502d681c40039043c1905403d056a0b43c0b5500207030103448600880d80a0050713021440c5e0f40343c50b2071105842c04a181075210842c00500c07010300c8a0260302c04100c4100b000783c07034000b60b00d410b062500c0102403081030344022002d1003414842d00005602 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 588580458 1250 588579208 588579241
    0x3070b0405070e190c12140405010506011b020f04021917010b122403030409051e040201090b0901020313260106060905041112071205090309060702010c1a 68
    0x390341a540c10540c3d40d01c0c00222a0310a1303d103c5001500e45000d0210340c2030781d910540d01070401d840e003660740410b1200c04400f210b462041548400c4011030801c02401424042c1c0364004d2003c0c64418400303c28140c109001c0500500024030440003c50404910351302c40e015900361040c20071081d1080540500c020303250a00c6020164001c10b41000001200550310044d200f69169028030070925940c1c0700c5440d099205a010803032040c3d03c82c03582801079500d01304060030180900c6200003640d4100900c1000f81c46000d10000c5d82d03a121000308001c010b0340e01600c0c070301c112848081681d031140c2c80240140e00b14080e00404004a000051000503200da800452403000840780c10610310044010801300c2c01d86816000f150042401c100c400c21403800c0c0740e4051038445d00700000c214100080801490054401035501c100082d18005002d004025288030300358106201c40c000307520300740d0ac40010400500800c64040d0521081d00a401c05104100801500d031000c54140440d09140405610328030048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 588581708 1250 588580458 588580463
    0x7020d060e1e06064b0a0902070302030a0c030905060708181e060c031c0903020d080105010c1401140f1f0e010b0a0909050703090303230c031803070b04 67
    0x40300002c8091140000c40c860740100000303010080d005440c04000d110701101a9021800c125140d01801900c20103203c441d41d4141d480b001a11054a0303450130841d041c001e0b5044440081d2040004200007a0000200c420821150801e400381124904050f50b00c076201d5407042e03030003440c00200340b0100070b2220700401c0441d900b00c00c80500022505e0500603221503425100f4400035940416064a01d003000180c0440c3d41040c0440340350002c41c906414039080500740e0145220307214070760442055018040c4403207005540c6800035081d0f260500082c180f0041910241c40b000307484a21030b90100c2d0a4012120700c880840c03000d003540c244900100d001000c00c5907040000100030b1000c04d50102818011001c89048642060303a9900701001070002ea0301001c82c0c8014010040b00005980803180105481041d130358400146041c03541c00c01400340c43c405010701303442040b12680c40203406403658980d40c001121020140e281c1e0b48a018038520f140c1101100301c0e4034070010031020704004844681038070940c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 588582958 1250 588581708 588581743
    0x60c0908010f1b03022d21060108070507030e01080a06090e0606241b010204030b0408040f1d1801021c0605120d0f0804060912030207060605012307020d060e 69
    0x103108000301d0403405603031140030400040c4403161000c0450000500314a00b0940f1b5450f01e480104a510032500c404a500086460340c01002c000b102e68110b5203246d4000c4407418105e2408030b40395001004c1c2600c0c4840c850500c80044046105043d00394403034400f8245805c820090040000002c0740c0c5d0b404102c035414400d00000c0300c013030050108407501010b18403800b5200ca007040419904058842420950f80145650900000011450b200000c6000754000d00070380d6507407400c00c2d40c1c10310701c80c05d581c001c0086000c0c215503c02c600500707000c0e110f900004400d8070740780c5152a603007030134007920a02402740058150019030107207041071a4041c0c002c5610444610301a080503070302d219282c0e4803006612000c150484110001c0e1802680355660091043c44002500c0315280d990758076145400d010280020b5004c00d03441c040003243e204000107401d0908107103402c1000d41042030001c14140e0902420b405011555604540b0741840c0c118141d580400148a40b043c0c1c040c07041da40c0d088c40741c64402c400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 588584208 1250 588582958 588583001
    0x91a040213051b041d010915140409050a03110c03010b0d021c0c06050903150106140315030706030b0f031b0409061b0e0a1401080114010c060f0c2604060c0908010f 72
    0x7c1380c0350301c5070907154821480308910340340c03034000c403480520404103070142c0003510b6101c001c0000707005100c0305400b14403e468451001ca01d00174490320f00b81e8a000c00718082c0c0c3c90140040100c0d40c91040256510f58102c41868850610452040c03a03210299001041b0021901e00071809540101c0030740740c50381095003290301d040c0c0726410300c280d00d6100303106500110f0500c2030302a2030301c000803000307607030004c40022041c0c0704450290121b07140011640c41040040e0b6500722400740c03450070302c1c01403c40d410110001c00b26100d9108a1b400c4503550101030703d00c5960307100501da0030040b035504650342d00e4000710418000d00d100b142e07014186160500c84c1500c150008000495101182d2803460701c940c0041e51582c66980c01d0a000320400c580e908001410710102c1c0e81c998000810600441445000100010941c000d610001401a40da45040301080076166588500030403584c8000725801500408085100c4031074541c103a499050503081a0055428100c0061a01c1c10030740100e840c4800046429401c0e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 588585458 1250 588584208 588584219
    0x5150a0c060504061e020423060c060103030305040c05090603070501111603050a02010f020312130c0305011e0c020307152c1f05060105191b06091a040213051b041d01 73
    0x6c03480b82e4000c02d003603403130b4222440315081c5242507082c0d007030f250141c2010b01c0c0203106414a07140040c00d0340100c00007074540301040100455000803034000c14007075551036038a040040000e51288010702a050402a01c10701001031081d00300304024108041e0006d9081840d16400c15170344960420740f0a9011403a14100515080e100004980e00036103c1000328419807140d105d81002102d0340c1406070354003c180c010200100300203104414184444240380320080c0714070140312082e940c0210a100654000b84200408640d00c010074800d1108490030009a51081c0384a0b000742828101080060036500510105030401c009a811681103000c44c1d00650404c003003d001c0203454080f61220300040c410f0004950000c1c640301111403071455402d1042c0c0010511b41c0c09002c21590039401c0ea81c0640762164481480b038500c001c0c0d01d0b00c1c0d240c8014209103287c2500400c038145400006290f9055880e00040c0c101c144007844842400d141000c141d139103d036078911008c807050840c201c40c1c0044000c60000a10f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 588586708 1250 588585458 588585461
    0x60b030a0c061107030c08060613050c04030308040f140d0206010816060809012405010801150e10020307080f030402030d091a0c0709020a180e0105150a0c060504061e 73
    0x803a0791081c5040701003801c2c55812546440020a000041e1107035410100001d0990354110014010080040c1074502c0c0035400c00860b4100364110141640ca0201800a8854120111025203415007804121074403186005801d062403400301030304152141c401c14128080c0461550104e9455601b25100380c0d803200441c0e82c8407100d641ca000d05225183d07504112550260311429889200c40e0000100390216050280034142c2445568160380300f4250284059a0440c15017070150000b41c1c40440c030404100320141c9541071303071044140704030480003922410383d04c20000c07290426482060355440f00c100160000d0307290403e40d004c80c4240100507141f4030326803040251008803552100d440c81a42c1c488a18041540e00c40d4004020340c1c041d205010405070038500046c540120b080c0c3d41c0170000d145410306012234140035001984800e0980d401005982e607821308420b001c001c0e940c41147c2d244103100707081c2c800710807640004141506203802c10051284a5211101c6c00705050314150780d11302840308290 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 588587958 1250 588586708 588586723
    0x70804050910231f0e010201060816090b191e0b0703141803120a03061e0306020d02090d0c0303090618090b120a0b100b04060e0f0f0d0b04060b03 64
    0x18040d1507440074085210802c00400f450080c00b5008995042c00c1d44000c40340824882030540200d00b2200c402c44c2d403940e09129450062142c20045c2c01107202c1e8408100f0801c54601c58001d40540710812150250384002c0c1120341041700108003d4403954a80c0d1403001d480700c045c401190320103490030004910b00c00d80d04446010342c0c0345e580c80d110810901c90445e02608135031b185d40d20700c0190905406944e2000c1159010943da0b440215032210780700c080060035a0bc4580250f4943c03100c0988840b41180481d030300780c0c25a5840b81c0e0260726103c000d95244000c1c002d00803042d41c80b00d0340080072014400042c41103c10740c0d020b81d031100c01c4a6110181521218104400340d00b070428444010408003d060b0311442e040c0740000d1165150030520390b50a440d2004074542a1074460071b482c00c5c0019146c0da28010401054030580940c18540340400c007605450030020340c28050311200084840c0b555605c3c0c52414610b80003400c1c454400c925080044201a089800f21041443d081444149140005500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 588589208 1250 588587958 588587969
    0x81b03070b0f070219090903020a110a120b041b0303031b021212150d08180f060307030506040e0f0106030204060e040f02010c05010e03030f15090403020705040917070804050910 78
    0x703850f2890039828003400001d40500d01300015600d94000c1641e1120f03010f400710040c081d900500620070241443c09081e4410786e00301d4810120f05504000400144c000d5443c0e00360464007582c140d0b038541c100303a1140100c0c03040c1c2c04d00c8080c041703002000b05501035121452b140c1d601e5000003044450381c04140d81c0d03200019204440c03050144a140c0b908103404902c60b501080c00381c071181c80540c1c00380200d46489451801116850404030300348021100e10f822800084404442140b81007c0c00000324a0503c0060140703400c06485030000f80b5140c0f5507030001c4206d44040302c21944001c600306508c41c000d200500049114a0400e680094003002c00345016020391340000280b03100d00d540d5401507482d034201d0305086038903548450294040e84006e002661081c80d00b1101d045c0076282c1002000e0942070003100310340c803500d000c20a00c00440d81c0010044141c51003aa000202e1004508000c500e01500704403140d61842d0006402080200c110081c0017250803d80d050000d58031840e0401c86a50000d0140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 588590458 1250 588589208 588589237
    0x4030215150d020f041802090a02040e0609070e090f151e01081b13060e010201020c0d03180b010b090316060503041514070201090215250804081b03070b 67
    0x641c0036454a100c000c45090700c010400030500903903002180581d8280701030744c260850300102c080107600b44a004181e0100d0000c03011450303e4184074500c95564000b038105401150311400013012280501012808051700800a000c1444d0512860821034000c80d4a03043e07002031048010198100b4044c400128105800740e0999503030324600450748070000410801400e01c1410340d00c44c07031074908002002e104580300030300c10201b0f080c40d0002e040d07600d00719039090440e80304000c0104071400c00719111a0212140c80d0118802c0d040018241c000a11940050801aa000c000042c01c860365002007216043c160140e8004043c0100b600c880041148282c0000c076104000103000925084c0f500b820112403001d00203031501141460381c03d6608101d030700f50090303951808440c0a600c1c003601c000041103192408185001c0c00355100003900d000400041100c2c04d0103007400400c021140d004e603405010694103e444192a0b00220714101c0354088405000380541000480c194004004641900000441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 588591708 1250 588590458 588590491
    0x1a07021e060a05041a070e0414060619050f0c0f01060602120a230c0a0c1e030602090f18040c06180608060307050a0602030a110a020d12020307050a0b04030215 70
    0x80318001d804010300417108a1298203480343c0022840c1041801000d2654071510464142c00510040380c04e44914a441c9150210411019a0321481103a4903514100409142ca00070350b42d0948441c0500041140c05003000f256000340032200259007030254800400a1007003c0c1e554a00703984030f07603901e558035140d154104640c0c80780b140075000414115612650b141d05000c80e2005046d155000f41e4449081504120700400900550a1826001c1c10410509200f00ca00700742c020400485207120092800340c0200d0f0b104456a04c50000800024010b00100e8107950104c290300c46450040f14102ca80e81424000426814410f0710301c02200e501c404820041c81e804e00005a40c1da10004002550600c107a640100303554480d2604040202040e8008580741d544450002c0d21046502020100c5176100215040150f902c203491070260503003102c1c8260016440182c1242588544240503001d0711601c40d804042008054441d1b101d54025030903200455000c4802140a64040d100c88441520460 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 588592958 1250 588591708 588591721
    0x906090f04030f090315050a05070822051218010906210b0d140606130b031009080c030c0705120a17090a03062909040b01031502071a07021e06 63
    0x700000003028540c04c00008160341e907500c0200300401600412841500c0f001442810301d0386014141d0022003900b0501504d2810303281200c54414001c2d829000a65a12010028404180006600400903521007941c60030800b051403040005045964002581c008000a05d28401d0315084050b03502000c0d140c4c06455000e129a029194842d1101d500c202c81e890100b0003d00000c0c02092904c1c416030280c61140b03005400c0000100403444104c21485c01c1c0610040141c1d0041144070388400c0603003001541102500f0320200780d000b2a83c540300f0310b100c00180c402c050400040c4000403a94111048412503030300e0280c00380c80b0000c805c001003884414501c1d054150520304054207407818060140c0c0e003040d82d680c5414041d5004582c0310706034000c220b03030341400d800e505c0c20006035070103410f4031a05202d061039600d82e0707610b00c0d0500c40944030300407684050030955140c1d0120760125030480094070200d5100d0b400258012020764520300548182c3d000002e190810040d6000d00460807070180c202640c403503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 588594208 1250 588592958 588592967
    0x10e0c09070e0f0f03060a06060815060403150b150306091e0f15040c030b12060103052802060703030507120e030a050f0409110319062304060302040203150906090f0403 74
    0xf11042a44181c40c45201d45098600304809485242c2c0c40c8004903890385006006014002c0140c26100310b030a05802e80480f9407602421a401c490340314091404a42c0e030f1041c1000104803c03202103030300502c82c090142e40035006030003a60007004121000c04051700c40410014400c84070844000601400400192200a200300e0496001a0b8000300020740e1100744000ba00f15401050400042959184941007508041810700d011000c1c1d200206420350464640039a17504c46000350710603040941001c01c4812400020000203a0fa000e000300e82c0701c507007600d0082c002c1c28040b104080026006041070846856600546110001c803102441c03400c00d400f841110941e100c0c2d4440b20074544100000104030000d8802d14050170a105203458480c20300f9800a0301d0001590840041b00b81007842c140850051100304020010102c6031188150b1703203000114000e0521540003a51042c030220410404800c2c2d521210b01c40141260b41ca0510341e10442040050b1301c00b40e6000ca504e00c422800940000e004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 588595458 1250 588594208 588594229
    0x9200903010f060909052a0d080408010c170a09080412060b0d120210150608090a1203050a0e060f060409020a0330020f100515040509010e0c09070e 65
    0x90000b0961080708040c0000755030b2142d000c0140c00b03a9a26515040c001d007070001c02d44903c0c006a804c4403101e2a41010160f18414090b01d034800c0c00404002010018002c040b50010308060009001d00c0c0b101c3c20b405840da498101002ca084014100000c1c070704101c0f84981c01c10b082c0e0144c1414207260512101c081d0007940000201c59840d41c904a03203400d036940d03551126006200d0120701c3c64140180030000c0c00c08449043c006109400e0000c0841201d010310002005c0e501c030b910b4032480c266a0b04803c9450040c00b40e402810100320040080100d0b58150000f070310400303071003906000030604040720b11350b520300468006001e03003840404150316282642141101d2400140144c81150b01c80d295170b131811401100c059402c2060048022141640d4034050744c0000a50001c1c11081c004040c0e0161145c110310200203050780d88000040c00302a041201c03107400710014104000603d040308a982c024007034002c0c822220300c00c00382034110600c1c08220715032052103a9034840c80d07514507940922034085c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 588596708 1250 588595458 588595477
    0x90d0807171603021e070512040e01030b1306090b07080c0c0c060c0f0d020d030b040203070206060f040612030203090414090d030207110d1b050105211f030c0f0920 72
    0x400300400700c2000031210040d444940b44560990f604c400500d0620305e0230311502120707000303030324107000402c00003050304911030440350440807074009650740065042082c41c80a50082c0b2062400603402d09001c0a40742d42c6102e00001d884140180c0c85612805040380914a49000c013907002c034149003418180346e000713070001c81641803c032601100d895406a040420311102200140c0c030004018280aa01d405061040c403c161421440c41c14546802501d5450082c0722601802d2400d000000356140c66214100404940d0044100640c86183c000c2d00ea80c4a00003483c0305a0414070440f000700c2d80542202c0c05851207100401580210701d00c00d030086d40040b90140c0388019190044ca0382d07619203502081c0410710402c0880140460905201c5000d03916400c03460410106112806c6e004445246001d112002c2c0a6450749035900d805140405480d80c2071080744540000300c0010800000080042c2a2021420102551034541401c101200c8991280e007181c8080308104d8140c3c441d4000c0100b01255 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 588597958 1250 588596708 588596711
    0xb09032508030a050316090e0c03060118060207090e010b100f09030606090504122309060403020a083004030b0a24081b1807020a0605090d0807171603 66
    0x554511940d4110f4000700751a8000c0341e40081000700700d80070700c003c0b284075030090f041c402c0055043c400b80101a4900501c4542844000000b050785a8098280d0414584400c1c0202e0009034032444000e480d013072140303d00125581800510b00296030306014840240d10050300c500c1000003a01313002c441100b4121001018030114040200100340c560040c103000e48003842c03002c10181403a25003405038070344203c0c0f000100003244154590f4514440884420006449041c075241d10b00340001950798416640020b41c002c040740c10001d00810f01182c1841c0652820208451544c95115001c50141200b002c082c007000041109000264400001a400845070b150000303001c031a0305541200414030030460380f824491120100400e80c8100000c41500700703a240309424280142003c03070070041b140c4150f8840700158000043c1e4192007082289242500100144001d091a80841d41c54100d82c1140d0070020754000000340c42d03940140c885082074050795484082c1651a204030b410750002501e012030406 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 588599208 1250 588597958 588598033
    0x708070807050d090b131502070b0301080105150303040f060305040c03123203061e0a0915090b090a051b041d0f040305070f020f0a140a0b0903 63
    0x324144041d28285114500601610000c440041c0545101d075010381010038040181c984128420080c410032512164034141032240c200b102030f4200150b43d04070444005021000190031041500118083d0050150036201c8010704010b058580c030aa000d020311411590804001c064420b600466209004901e008095500c950368110b442e803d1121060001324004540b5000b11102d00980c200c45038805010a0074101c44806010240802400c0c684210000d25021400c0d445203413092210340c00003000f11111546504090b4002c10b0f50449c0002520540200030403218054814103e508100409201c119500d00e0700d080060800100b07a03050101000c141801d141c10b68501600213040082c0750b6481b48910300c500e2042d450001401052203910520070310003c43c0c2c20000b202c00c0d2030f806c92407102e0610f4060012801d804482e448080e0400c0550b4000107148070300300ba41018502044912049a556070000311b0110700480c400280d15230000c0c038044400107540c00c60360300d2140b802c0b603450201 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 588600458 1250 588599208 588599213
    0x314070509040618050f10051e06070c0b04090c0507030503010905041b180f0605090133030b0f0d0308010902130302040c0203032a030c0a11010e0714090c0906070807 73
    0x4960040d01a144c0c00e640700e9052250444c01e2111a039484181c2030030000c20203141c00c1c0014894141c900110320880c920802005c0c554881100711201542c201407501035403951024506699809440b60801a519241c03241d4a880d100314210b07084123070035540c0d4505590810303505000500002e8001c640c960200300d21175480c0143c2030301c0b04c002803c00141c012180b003400036a0005a403010350405500d14a800b505114607620040c819056402111000d16010011481071a03025400681c040d012040561850080d982c1508602c80000042c2d0b144442c042c00c032014030044e01219079000b000b00f00f2079401406a00c1065000e442500c3c000707100d0202c0d8995070b4020800300c900c100c49210042e000002000000080c2d8002c41c000d8440700c07580d035943da003000d07020784000780409400d4130100100041c8290b034591144400164038074540008101e940741d0102c0c0700e0340e00e029501c1018810340001040d00b00300c1c0ba02c183c01e10b00c14000c0c4640c15142c0321380740040101e6940f040b90119078604080c40380002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 588601708 1250 588600458 588600479
    0x11150106090f090506060a051c0e07170d0206070e060f2a0604080d0b010905120d030b0301020c0a020409030c0b090d0201050f0705070609021302070803150103140705090406 76
    0x204041c0c1c40704042076007030141c00b000054043d04046049414801031040540741c0c10b00700c0b45071641e58a88242c5404640341c4010044040e000131640302800c00450b645004008501c6e5400c40c0c494540b240e07a4120840f03047d6448800d403c0c1c90f0380150704100c00083c6001d0041e08440b0030b82500400080c41d001c44612480030541050603007442c41508008411851112040307102c100110013002090313a442c0607543e142e0302d40304030740640d4241e5417504603408469026001e030101030503004200d400c00c201400d1009a895103081060000241003041c074801908044c0308643c1c0d9a540d01c8044e1246004075000d21002d00f46040c4100c04014401c40b802012880940b0b0715801004000c015001c00061680c00030b0940b000684000c400c440780106102c03a96400c4012143c0c0380350700c040081030185407800000c508075000541c1d04001800090002c003001900750003140701d460074000100c0340b00702000044045032001e0003004c1400c2b58580c08101503070f004101400080c50000c00c0420629283c421000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 588602958 1250 588601708 588601711
    0x60816050421050c1219060b0a0815010e060a030201140904020a05130f050f0f0301060801050a020c061003050a03120e07060c02040b0906030616031112010e1b030105011115 76
    0x206000d0307001c050030040200500109002e060100c4440100d406614009030306c0b0020710803c501000c98001c6001c0400250750020381007480000c1c40242141c2e5aa4101b5032501454801102400051400881c2d042c40b8014458066140a0551000c003820f681c01500d0040100314241c400c80c60a00c015881c5549a0008000c0a0704a5445986442020030f82882e00c1d00035800204859145a0f0240b04580b61420001070340c040072154012000861400709004004035003141c021542010100310f0b1404032500140b0a0007800c80c21a201d6554003030074070400310b11600000f422a0840d031008404644141d0454000f40c0b09a000092000c00f609901031a110080d03011001051100c0c60220039454240300d0440022002d440811107840e101c0c00190701c540c03000b440c40b0701c2808046080d040280c0b299110070700c2e040c4207842c190703942c1001c2c88001c0d0700310000344074101501d2550000030302d0406c0000100104404854800c40c1543d00303010044d18001441c0c030407500b030381c801c03404101c810323150100016 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 588604208 1250 588602958 588602999
    0x90609190f030c08070b1e0706090c080c010206011d22061a0f101809150f080d08071d0306070e090a0c080a02090d08030f010503160608160504 63
    0x784100e1039071a103c1c82102907903000154a80181d101008446c25080440e46003440b02040036070100120a40142c00d809a114041c02a034a0000f0304401c0007014042401656040382c2100d04021079800126500c0400340582079151182105a003c40c10b00860f016801820038404501c0700046d51641030010f06c004601911f803181c541c20001c07820340c6500d1041c809043d0076503012202c09615004601d0b480044a0f15400b041184030400c40c080f00d032a003000c0080d040c2003d080c001450325030070b00c1000314401d00682d091a081044009a0300c0e50004420b0391204c0c0648441c0d805c2ea458071019034142035504400191500044d411800964090208605c1441140c0320488001c841e1010700503d4400100100b000364274185050368115005441190b0202e140d00b40540d46110840114800580303a420082c6442004024850f28100c00400d10781a40c3c03041c3c040340c050404842c040003c820241c40b0300f401182d8160040790b100ca01048450380701d1041810302c50b142c40d40c3c0ba80c10b080c803450712905c2c1703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 588605458 1250 588604208 588604229
    0x70b04050604150c02030a1202270307050307050a140a150c0b070e0a03080d0b06040308030406180c0b0304020d120c021302040e0105120a0b0a05041104050103050309060919 76
    0xc0108101a03c50541800e101c520b108011042c034600340696244500740c1240280003044981116208603a01201c06007091f542c0300755130f1025034038ad40c0507120207001c0031548280600500800c0328100040c5440c22100000d0803062600d1600c0d890116070800c58041035001440c80801003501182c0301031041e83d5600503a24224611040e0500ea6a80030019042da0f0402c0004001d623200c1782c1d41d05a1030742c152a000901160b0b580019030f1548010200c0f0406030b0340141000c100007080c03010b000080c51081e40685002d201940e101c0c1a031151071021440d00402c102c036808001d0050190720307005180d02c5440a0003050f00b0101c140c6036180c0b101c3c610382c81040010f0380407034400114100440c1c2e484001540000c107600381801c06510b4034035070405008081c0500441c04c8a0042c1440030070002143c0c85e0000e142c5504d0742440e06e07140020340421a02900c8840042d01c1644075402e00d48242c80c101d81d044005141406510410010550304c121041940048840b52280c180e2002c100d5807001445182c1c00f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 588606708 1250 588605458 588605461
    0x106030305071203090b07030c17070801150806030a0b1317090411030f07270803040e1e0403080a02071401091b120b0604020403050d030605131e020f070b040506 71
    0x510342543e9414070440d404050a00c90710300c0014a400180315081050750a010900020fa079008981040c6280503000b500e444040a000505401000140c143d4007003150201c40140c00c4d00040e01c0d01c0c0b8dc103071507240e090b071300580b985c00100e221a55001d0708464260401088071000740c680d4056500c820710b4080134034034001072110380d514040c03103100c106250104049046244c100c1c0e115207240350003814001484215911140707040d195410b0049038181d039450300740351292103007107140d03070794109028000b00c080341c0c00d020071082195850300d9031a0340d01526214034140d84950741140c012801030008ea020940901c1440005403059004c1d0f601180c440d00000b5201205040003200c507094001c640c0040482904107005c0c1604241040045036046114404591a0400810001d100d641d0020f0000e002d1002c00a42007940354008800315074045452000006403d40744e402150922a10402c0300b122090b0b260500080f00c0d00034010751810741e4045030034103400d915042c118040488040759143c00190 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 588607958 1250 588606708 588606713
    0x70912061d07031a04050a1509051204030b0403030c1b080322020a060f0e04020315030c01050a0906080c190203210f0f0a09061d0106080f031c0e010603030507 70
    0x10000d50454031503000404500b072840e21070034a0300084c00c542101510240e000070b070031300c0b80c104503254181c0d80c40880c18403180326890b0401e00621015400712000d00401c0011410480c6a4080c0d60130340750000303119540c42d2030f184d13000c1d0000c0c100c4494a6080c0825110f0346000319200d00900c4a616000e42c3c50306550b031402480b4000c2820001c0808003e40e01c00d03041c0305000d615011301c000140c6809044c05e68110001e40070036a41250b11400c640d60150000040007002c08891045c00d001c01c10660032100c40707604080c0107442900a80c000440002c041d010100b20080c4030307109145d003104410002519201c00c201703034050403919a1000f0300160b4030019500c50701d0441c1e0400c00c000c411100103215141d0802c40070115a42c4406082004041e9880c004a10f00c2c00382036000e0003c0742e500030700822a41d04564415108040d0184000c034181d484c0a10000c2ea0a40105040000d2800c1502840c50b20a0b03c00d0b4208a0202d890560140f032a501d003c40000800e0900c10030003e14001e4498607103901451 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 588609208 1250 588607958 588607991
    0xa150903060b0a06021e03041806180902030c0103090c0e0c0318070f050f04020d0903020c01031508060f19020c011a061c050604020705032107230307091206 69
    0x40b0069000d02c00c0700108001d9154041a03840c07880c90156400580c100b0604021469806280c0160307140d90386000c180078a0b00c2255000e482101d1000a84000908c134000790142281e42e0008040e4158100b0110700000b50301c87d13440003001910a01805500644840080006000850300c0c0e40041000205000e960b000c070705040780d0004d101a005110380c0b820550302c801d00150921415001c0e41c841c04102c0725035a0366406690440d000315000700808038041c10025501e1b4a080411408207180c0489102c91040c001700c1001695012002444e65456070005001e18160040c80200310341ea02000c20010302d84580020612100c90000100302d04035408650043c00740c40c2c508051041c01d0800c075410403210418845074a0600c40400000c03e540c900b40414040d11801000038507a000018000c041c403210058041d20050010703c01c1034043c0e0351b019081e25942c4909110181c40b904241c035100c000c41852000390351061030b03442c100c4101507030703440c1d0003004041204089514545980f1440c4404281c0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 588610458 1250 588609208 588609221
    0x908070506150d0807170904092109030206091002031201290c1c110307150b1903060c020a02180906090c130906060e040804181a010c020a15090306 65
    0x446181c88410f0041d07072001140d100303403a0300074001c128442c10f000080d010002038509481001c0c00502c4681c500c2c0c078100480d2568460900e850341300b0103c41e080d82502c10454581542e0b40074201a280000460410094132410120b00c811840100722609a602e030402c2c40754002d220b940c0340d1420840480703502c28480e2160000c00c0c00249000d004002c10f04d00c0001e4001c62030822180701060000d00b0800c1210035003000c0390400c08901c40020f10904000401011000c502054082004180754284c2000032580b0000249060803c00c4030301072021640710340c41602d075407c0742d00450b0300d000b40ea68003003117203900c1100601150960040422002400a02c991607003c80c0c22405000b02c841108002640306440184061106560f030b010a010045250f01160103046000d14800c41e9280130300d0b120415038000c0c01a0707644074050028030340e5000d46a008500400000c4546140c090303d900c0f00440f140d925540007a6840a01070000040340c804180700300003aa1080d5035450007036800d5060105c180d415 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 588611708 1250 588610458 588610501
    0xd0b0117060c04120309030633080a3801080c33041d0601090807080c01121503050610140a090c020717010b01110c0a0b0307030908070506 61
    0x10400b0054000e203030303800701d60030f0340c0050305032640100d0941011500f02a00c1d80000b44082c1c074184520751204150394182c080000e0540d002015000811589050030300284240926a030240002d40001342d4540b2a20701303000080380385800c1007000c010750b0a00464181060b4103402c512100144102c00c0c00348880101503a0540d43c020540b0f50001726410031002c0080d4507414080307007402c2114030641f0300040b60004d061131881032004210f00030f080c1c2c44503441a15058049074554400042c9802c012401608a41404000d810400b400314019101c24040724480c00d566641c91803040428009030100c58040c5001d400200704510300800d00042c08140d42e0041e1070031446100319050780740c2d50303501d80ba0140c03a038000c0049225034185400380d240400e6078200c01c80c0708040140e01c0e404075805503c00407a003442642e51111805a4540345a11603000c02c032a160846081a0f05209070b4508400070b6400050600d80003540950780e4840c00e410b500101002c0f58680c00580610041107240ea061316990300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 588612958 1250 588611708 588611713
    0xc082b1811190608070309080c0f0f12030703090c0312030510270903030b030a12020d0318030311040f031a060105160b060d0206040e07020f0c01120905010207020d0b0117 75
    0x51200c514110b0030001e44101002c120751440041d41940c802d40146403403a612200b80380e101e0311402109a115003000200c414180304491140401170f200088400c20442000d0382c545c40d40d121302100710301405005500b5520703500040c600000003480040220b00458081da0000b503282888189004a9006548841e90040f000c82c048d0b98070460644009254504030b100000c2e602a4503d0b09a01420211402d2a858054070f4050001c0c010110001440c200c2e03aa0f09860800955001c103034101ca03441e040444440d0001d5a1240029004e540440140040410038505080da221030700d6041c910f00e500304a035004c0c0204881540da141308880310741c1103442400c0044c20720b051003c9541540310700100260100c0d2103840441e1141d201c1c034924880c095005002650713525180d006802480c1001e44002005114170014581d00302c02c08604070150f904140d4072004404d0000603010083d01414000384c3d220f55081204d500180e82c1c18501c030010b2442210a240650314181848402c0f56401d482100e194 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 588614208 1250 588612958 588612979
    0x9030106090b0f010813080301080318030a0c0510030e06010602072102150d020d060e0603061e061009050406030c030b130305030c0d0e0d020303160c082b1811 70
    0x25924544212441c1c0f10030310f85004999201003060104041030326010302800800800802c1100c000700040000004405200d800003182d4410b06070386810f9150054040e1000541c2400249803404003040703000594a004034414803951151401c0110030b920000240e0b008003003c01021000d1101c80d020700d17405c803184046103c019008684035049000e8000d078141c00010710f000c80054254181c0e511694070ba01c040120b00d0f1191080e40082c0300070350b0620711034454407002582043c814207030b25013642c2d41d098441d4a140c46441c1444444030741d2400d01d005119190201040d40d8881c1e20070040114090303040c0d0700e04603180d400c041d640042c4c0039142002041d0310305090340109801c1800c494000c02c0d41130110707035690340d2020110002c041007140700e52a806450b10404e01240d0000c040d501404c241b0310311986440e105007090780c01c0160164004c281e200709022603411800d4100308400e03039001c40503035041c0c9540c0c003001e0441180c0e04484083d03001c0c070701139100c14184180d062032031024a8041d5080c0194 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 588615458 1250 588614208 588614231
    0x3010b1e0409060803181f181d07200304050607020a09021303050105060103061a1b060403050c060a0504082b06030c03050d0806060409200a02030903010609 69
    0x144500002100040c0d000c4114160104000044034010041e0035003c10800da11a00c9040d01d941c030040000e00b5140b002e011408080c9807900d0141d03442da21704e41d05400382c00e8540c0003d5a070500a03901d09485c00454000024483c3e0102e14401c40801c040682220140313003040340031b840002418440b0f0f400c000b41500c01c19002600000f141c1c16504101c0e07100e07032580210701c0000d0b0300300a2030b003003004501d001040d22400304078103c4154060381e00c03901c02031169030b43c1d0b440114200c540c1803041c0070201101030043c02114818500500708141d122070640307815061002c2403480d00c03006440440000314005028210360703c05122603500014081403c1c4401c4c01c054403030b00c035a07000f0b9a6809001983d82d01072000300300c84011201910280d00d41d41801102d95034200480c0d02c4049100a586038003d031240da802c0700d4456000c030340c4100c20040034035040c0b508246080d07000b0003210010311150a0b03211000c0c1c0d00c0c26182c0010b00722102c440d500a42d41c64403100281760940340b05a10002040341060390003e13a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 588616708 1250 588615458 588615479
    0xd030929040b090703061806060806090d08190920010305250225090501050906010503040b0c0403061407110a0201022a130504200a090e0c30030301 65
    0xc01c160400d08114203500c4402815003000703599400186050318040c02e21018514040c4001d141301e000b01c2c010000349035036141584d241c1800325071031611504948060b001090103105401c1c1c0122648150790320000d001c01d524401c94581c104192100511101191782c08002c5c43e0030301d111103600f03103810700c41403c0c15800c41c1f000241300c40c0c05020402c804507008584a200700703c450020307058404a4404200c50040303200c030740ca00070b010b40f91200742403600201c0c040c1005078400d401641c06a43d004c1c0303160f60b282c44462091001504900040303074204400404240c00d03018042ca03403040600070111a040c0355002900c400000f84940b104c9030071030f161940150780c000c918148042403405441203800056010700002c0c401d40207441d07a00080940300c1e0003080e45651300080c4504d1040641c0c0b910348809502c041c00c0804a810341680c02030f01d840c424495240c2940281c40510181421507400180d0b802c0000c0041030720b400509220079103c60981c000c010041280c1c580307140c451002e10f1440d41000d002c1c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 588617958 1250 588616708 588616711
    0x2070501150e0c1c110c1203060a080304080705062b050a14060f040209010c3c05120a1202030f04020a0b1c0510050603010e011a090105031302060c0d030929 69
    0xd1343c0310360340c421600f2081da1329000c54050040890984032078180c1d150004085801c184c4207580202c9401d03602003802e82e8000200d40130386800c0d000402c811490442080101e502c020340090340f01c5035004061800180c3c07800e40f8819481d612401081529050b0140c408035081002007089012001c0b090164a441c2c441c00024802c8040e18090ba441d2102401aa840c0d40000e40050605000d600314001c00240d4a210f4259000040d0300a80c000018400304070148110401c05420303904400201040c5000003001014001da240c1400b00e02c10780346010348422a0030817030300c10281d10040410441146002141c41c4040c14032841c0c4103080c8044940820501100422341514080d07a82000c83c001c4012460034074000d040040c01c0075680d607101c1ca01a00c1d083d05c00e00c2000108000c461800e02ca5480e00e40a50300440700603901c031821941c84518442c1c1801c050601aa00040c080021102c1140c0a0060600e0046a40c03008510106035242100300c1070345401451021084407841032110070305942071079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 588619208 1250 588617958 588618007
    0x6090c0c1a04110d1b080a0308010b0706110711090603030f12040c0302030f24060d0803061f0914190605030c0c060a0608060601030c1e0302070501150e0c 68
    0x1106682d94510705004034902880030f07168403c3c0003450890402c00103600114111181e041c503989080d6403020300f5075650318800801000b113a120b00043c400701a4a4014291150003100702096000d00000810b04036800100306030344040303104140c4401824110700203500420241c00031840c1c21980c81c01248680103d200c60001d02c032690707012600384515045180041d580040a8900c1301d140862056a9411950058018110320310200d030310303416034010307410b20903000a8800000b0901aa5944039640d00c000d20140d40079a090410080c11180f1480c0c040d0180342d180ca40741d01250404030002c100c28000c1862600c100c110319541148084030700f1000e000c0b0703031850a095480c1e0300c90048400450250018103189440b13010100b004a84240d00000121a40a016500303d81c954400460946d985480c0d101d000c641010300704140f05c03505d403001c1200842903250041c18034003a60340340360a461240c80801035085141c8000c0c007682030070300c3e403140c0c20810162103a40380c51380c240c1c071400f14182c40f80c415 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 588620458 1250 588619208 588619253
    0x15110c06180109080114091009030f0e01020a0f150f0207050a0b07090b0f040e010b0901081609030c09050f0c07030807080606091c030e040603111201020f0a020106090c0c 75
    0x1c004459000d0442e00c0c001d402200000c0c0b040500d03104a072010054121503a44440c8600c106500180c542445540c00958140c2c0c0c07850403101c6000026100102c580d004107046204003401c0c0700c041014019444580b030300c96080400015070381c48900b0b0030307503003032200360001144100480c00014000044200c43d03e339000d5008203055a40d800d040d02e401d0385c0c95014207a03000000504030745840302400200b041c0c4001811020407a40c80d552010481e00030204d1042c00f0a47c1e44c1c02091180c26900390382c5066001d14038203107072119160703074641e4041529903008040e065192410701c280010400207203036001d4149c05d54981000f4007610010505140a0701b00300500c0740183c08180503846120445080703540203011b42c2c1c1850b02c0f0003802d0b6020080d07400282e0003e01c1100221040d850103000d41c4c02200e40008006041d00007441c2080310a013810f2036404007541d420000350b000b58904001a02e5417111039000000d42520700060442940c120b04040d42c200007600008000103080c420311015001410401c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 588621708 1250 588620458 588620497
    0x50301060e04021e030607120c0309080319020405060706051608041709030c12030c010c0e130b040e0f0714030d120c030905060c07061a090f0a0b0a15110c06 69
    0x50400918420026503003500902c0100401f580d00b02800a448400b1807501b048070305002c14049003291505440108201002c0020502d00d1030b104001d80c81c403c03880f103001403510384d4440004806611110342102c02d5074840302040a00010114080c2000c2c0950a044009261503524486541c04501c80341c522001c3c00319180d0180e440c00c0000454500018000c1d00c0d0071000e04001136503d070003a640079089136081c080803c00c040e00c1042600d10200000d404254520b40030320f030ba10301403c40d06032002d030010b82d1a146c0c2c034800c030402c00c003000710140e5000150030043e0410401d4001c542170401e406000341e1001ca50a1081c0c2e030f016410400401c405107000800080b0b050085010b4480d0b4038019046120342c805218403032081d50000c19109210b2320042003000041e110f014507881d490400c0c035500c176110800280340703444080060344d44001003080014004042800041d0707100d0310303a00041107900e8032840c2184c0c8242c1040c81c0350f00c4110407400603c0910001000aa1148111175030680b09100721700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 588622958 1250 588621708 588621739
    0xa0308071106040605180c0307150215010311090919140a0c0308040f0501020f0a0209040219030507030b0c09030d2f061b18091b12040c050301060e0402 67
    0x1224402012901c0c41a600349003000c0c04c0c14009803005a03003200c445916070000e05640000002d40400455002c0d02400e005e0f17180151900900c1c03074240c020340a50044200070760071001c469034014080c41c0b04c0d5400c8200c26035504184070362600d0080c5114456489500440500784075a0150403481c0c0d4008620001c003000042c0450400d407441e10001c1000083c800b000c410804040003030000c0d0b0342107210000c030303a55460004a903110492049201e00c1d411401031034015082031400f999004c0d00140c584a43c001500301c0c0080f03924181d42c0240ca441d00002414000c1004034203032560411040c8031a94248842c11000039261100c00307000e001071110300402a02051044986911144080048000064404113005895a01c00c80e0b1048903020070f4040140142030b9030065030000c0341c5401041c10b80d028610706020f03501d040542a20070040d0050140c0b00140044402448210401c41c0900707280d00b0545059510314601303800c8248241d0520754280145003000c21150341c81601114020f4800500d0f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 588624208 1250 588622958 588622967
    0x1a031902040306090507030209061005040911040f0e0709350f011518091a060a050402030a0b041a0d081315020d0206090105060a0306021803031b19050a030807 70
    0x42d4001401d85041100035410300502207203900c1100d0003543c0c0e10700e6943e43c180c01c00c40860001c1c01c002000c608140024400054207906c0424a0210710340390501d8181c030f0320079520108030b066000380d070004c400e14204803186500002d076000801c600e03000310070820b0110041080004120031602d030520340d400d0088043c0c04040104e140300b80c0d6060020485c40d40f500b0451031101c151402900c1007100f155140f4140300c0168804c8000c1c0742d0b040b00c0301042204e86a55002030090000e0003440d4005d01c102d0011a05694130310045004255484000904080c05424030040d070394829490410814800003d144640300c00e101700c3e0040364030048080d0745040ca01180c7ca81c00700c89801088000602c0c41c0848002500041c0c422500821a021a00503a940442c540e00ba9881121410f0308401c4c100020000a09190090a80307880b0252000303043c1c40d58040800d1464024480c0d2900d0580701d0340d5805000c040502c00c1c0404901c0d014100c0c0c92a0b40251611035950581031002001c20052000094001c0d125 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 588625458 1250 588624208 588624217
    0x100614070803070c080d1406030a0507050d0c0e010e01050f010918180c0f180c090b07240c030b120304050d17040602011a030606090703020a020c09100305071a031902 73
    0x114402541b5000b60142950081c10854a0010302825001c0820384034900041c0d8040e12903441801407001504041c28020901e80c401012106c601d80d20001052004000d402680603190b030300790904040d85000104a0100040ca00322818000a8182031180800e00c000b4040d02d18681c0401068841c801f140c840d2140d11216070103010350440480201e03100414841c8030301107410540e4801c25a40d038071034401040b14020421840422035100742004412882c1000e011994011840414214210168500c0485400207585052503903022494000b540511600350a603200b5104513032045080324144e652842180541846071800e01941810808a01c04d0f804c0402c80964125031242da8400303000c0d010308450800f0003e0a07850710300480480c1800a442481060300402c21500b80e15a00000c3d4000c2d800000013100b1030180e00c8111030a512484021409440e07a0f0702252081490360a0080c185142078000c01903d4048009100c034140d840e2094903004a0711009180004600501e590002e114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 588626708 1250 588625458 588625463
    0x906110f0a060e06061903060c030e0609010903090602070e0a090203030c1902090a0507080a0506030325020a0e070c1230050705030610030905070e010b03100614070803070c 76
    0x1454072450401182e9003000c07071208451011552540ca0307203000c01111822a8205101c00160b4050403c041105a000540308061358100045d042161520060800f4021154003d01740e45458158080540c41804600100924805003040e5130801c400342c40502400740110600c55100c0c5044021342d0340500459040568100c1110102500390b002c00511050340c5134182d1198440c10300161880d01d607801103034071440c495030f103800345940c0d881e0b1054000c0101400342ca8051005000e01039906030700b403001a07408005915000068200c40c4100419024203411442380182e0700000d01002642119610812503440b0401d0a620348500608070740200350200482e9010600c0d5410030b40c6c010a421002e4540c41c203000b0280103580d42c10405407000d00c02690030942000c1d03101903202c00140309034010303103601380b14800f9140c480d0b61b900c051880300f40083e04680c60368500001440250100308003220004c00042c1840492189000302008813800741031005000014004005145a40b060003031035109035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 588627958 1250 588626708 588626713
    0x91a100e0609221514030a120f03060506041d06030c0306180a080f0a120e06072f01021b06040206030103080a05220519051320181509010906110f 64
    0x128504507491461300c40b4855090b600401c035669085500f000324440c0c3c802074000c2242c072048000440d084402180c0c00e4110420155030303004c0801c040c1c0d03440300100010200807610b402088039422100c01c8402020700114429400b0b13590000705502d020409540c8581c14451100c000400150b0003401c00b07084070070081507031100141304e082d441d8041003c1c010b0078401e075a8207003550610b0106041103c240610491095005800254900d8405c0c0c0110380e00000d2258140540c1234006506007000f00d520f109401240d40100b00c0b880c9582c007600c02c0a243d4586040140b1f56820a60007081c40380c48180006001c00000284e50408240910226803440c0313112014000c0c840c1000c0401010543c4500030144204001c512650b1051500c66841d8241c9000801c1c00e02c20002c07a00e0b401d001414106500a440c40d18200d1502c000b010b144050401c420f48040640814110801041404c18503085070030390300002400340d40c3c0b803039038000c1d12042541c0d0a4180014004001202c00b880d102000c880c203852407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 588629208 1250 588627958 588627971
    0x2130e1b03090618030a1d010306030c080a0b100f0608180f0609010c090f0b07030e03100b040f11090f040e0a0312060e07140f04091a100e060922 64
    0x2d076000140345200301010149074044510116142d9201c1c070034468000c0000326440c0c0c00550400c1411042202c2050504000816070340da5502c082d1307160160350002e4a2508802102c0040c000a0410a0762102c902c2d00310313100850400794180c18415450141e50108261400043c0b690b10485030348901d400051011128800400090356641d418121082c0c1041e5003403143d80a4001c0c010283d401c03e4400c65000d100302c90b828020841042d4015020a40030411100070f1030800e500e00b402100c0780b440352a90040750b209410800e00041c0ca1500c3d00c21106a4541503010000b0608017003600c0c00c60104881e007500c2d500341c9000090243c400a07502e42100d001c0e90780781c0410076030490045000284c0c988000e204051b80c1c0c00c54151000421613500012907110300b24880c07006d80c44001440e840801304615400e0984031142c05c402c42c1c4003080c04601c100401e580d244201d01c1c1100c0d040000300070b2131a24010402210002c5001401a00b51340c1d070203040c41c8402d030003004032a00403014102d4000d58040048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 588630458 1250 588629208 588629221
    0x70309050a091a01020c01140915042904030f0f0611040b3103080703110607110114010302061c020d02120612151506070c0b0c010b0402130e1b03 64
    0x20f080d040d04004070001c259011820650000c10f4407400700710147c56241a510324072600ca03480740e200030003a9500200002e654005154014040e2000d049101c0300c044501081e0900d180e4019251041c10a031481d09010400003d043c4e00ca001400b980d000500455a1035145028406001c0c60303850150920710124010803000081c40242401c011508441e070001300a0061480c90030490703807000d4101d003c0010080c000700b41e000b0020075441c0e02c2890140e0398808082d0344035081220994003031001034590f0f000e1094801c0c09008081d140101340d184d60810f54910b070300050032485402c06583c00810a004050040c040d141c0c152040750a006005554420240c14031807080002254003a01c2602c0036000345100210000d80c90700c004a0441c1c0303040145d15007070041c1c030080f4200b4001c41d0307200900f0000100090b00380092003000f403201e52a02c2e6122500c4803401400c0d03811015200e4012481400001c48010001c5081c00803628501540d0019441c1c80b00000074030170300c6094110340c074000041400f01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 588631708 1250 588630458 588630461
    0x2071e090c17011503060905041a04150608070501030f18060e160315111206040b150a020a050607020a2f1903020406140f0405070216090f0b03030a14070309050a09 72
    0x4d03410140d60100119912980144200c07003040d2009894a9400ea01540c025840300202300d404c20700880e170b407080c1d500d4600d19040a8441d15080140e16400c928010400c030358260107540c009281900050084660340c0105100003044014003404807078a81e8407400c0b903124288190807c154500301c42c1030f500d07074030390511002d0740c0000c0721302c0700c01c07140f800313064030303030200380c0c04161a2903514000038005039464400400000c0d203165101140d100ca540c41d0380410041c0e031400186a52021900070340590f0070071341404c5041000050200095401404a03a0300088840c104044081e0032500c2200804182d07120300b980009225200c15040ba417403540b140484123041d1815021030344229804c2c04440d0b03d60300343c001c41075800001d1941003200c110b4071103004c0c40c2a403c61035100200d441165007120040c1d440041e403028503440514029642d00d282221600c03039000391303081d00d44142c00440c540301c01024020400b00104c640100343c500007080c0341d000c0622a0301d0210040500409090046071983c20200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 588632958 1250 588631708 588631739
    0x5100f023a0c020f190f0f0512070501050f160203040302010809031b0717010606120c020109020402180f0d0321020f040609051804170a020a02031c02071e090c1701 72
    0x548038017400c3d509950248805607846030341c042020a41050a682c1340081404440b03c100c64601883c406800005014405801158000c400106590500401243c10700c80090024850002c41d41e90000c0200e40002c102e40c126542880d01641070355070b4080c03007400c42c000c0c02040b074a4000d4180b03030901d034130000080d40410f58200c00f045c4858007007803080c03040c22101d003881000f0100d401c120018004c80e0315035100302000c10081c0000701d0b801c1c88650018089a20003241d00440600c03550341900241003031800051890800c1d500700032400b50315100a003420801401c9510350a44031403440c03040300d550342c0503150001c0810300000e0b1200c0d2141c5000c1c15000d16406458001e204480341072000804d61346481d4002e6030002402003061501c010a01035a500441c00c0300158400c0302c240500580702080310200001c0c80c0c1104440c41400c404000742040c01c10352140c08000705a0659002140301503040204440781880c00190540c01d04070259040034010294040c5070700084000110344034000c3c0d111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 588634208 1250 588632958 588632983
    0x702030d02030406020f1c0c02030c0a0306060f09050906060d05160609090c0e0f090c090909030409180330050406060501030e0102070f020d0f020d05100f023a0c02 72
    0x66024259a03280c1c02d03a03c100c20003028000142809081f241d050103100c0176200d15002074141d900c14202003021800d50201030b44102c4050391364500c00c1010440c2ca10000028040b01c2d003043c0590f040002005a0342e110180025114019402c00101042420070018244040506191034071513a40d20029000da030340ca1103014680c03420f0a1134040340c0c1d44145000251464004c00000040d42400c0600201620050415083d100c082194600c00e5480d00051881441c6400c01903580381e0800403203405aa03081d02506500c1c0c032156041000180c1c01c061020030102d52050b1580f00380b182d480203510441301c0f11000c0c9210524001c2800140486900b00e0401e6540a0300c050001e21200910b060803407040510180000c061000007000514003207141e00002806403071900d41642c046d400050b005082c4090031a01750f8002d50001d03040c60301c0e9016645000660010450500c40c030b9150282d4128101200d160446052403071190003540383c4040307010305144c0c203a000c01642034950006507a5206040e402c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 588635458 1250 588634208 588634213
    0x70801170316110a0305070305300f040b07080912030a0c11190e04030801050105070c06030207021f03090c09091109040611160212070e01050d0203030702030d0203040602 75
    0x8160035840c0e080a44000300284015072810740c144181003140315082c01c0448441100340421012aa1400d0361100594001c9003c0c110440c5181b400b14a400d00c207501400349020b0440c0c1000f42005001c034408a40001503081a565500301c80b5420004e00c101d400000980f08c0c0840e0709818000200090078680500b0780e542c01030400c014030210ba0b03d025089844000610a52100d00061200240c6500d40040075190721014100302c000d070691903889030403003074907041507008000130306901c4988140100400e00301945042c0d003035103580c00700f08580e00800f414103400242c030200310346600d00614000d9500d05203042250f24081ea00402821641c2d6040d5800072400c540424007108501c185d40c03030168069080009580072030309002e820a030007041a50f100e90350781c0c2000c0b041c03004400200400906081d0002e001c6038948100b11900502034040d80c440e41c40400d040c02800049030752907054036030840f0748480741d50103172000030700d9441004002509406026015140e054001020700255003680e001d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 588636708 1250 588635458 588635461
    0xf0509030d090e0906012d0e070503091209060703031e0504060204090b0f060301031106070b04030f0f110a020603060f0d111807090506030a060905070e0316050603041b0515030708 79
    0x640c5a50b82c0c428000c41c5010300d03009440c030810700c41d10940305030306031202147c06290726510000c054046404481802c0421800000c04c024100c040c0840c2c0311070900c40e6400d6040002c084d0105804c1c0c0241d00c0000d05041c1d07070304a40207982d144100d441341c3c443c0c0e40c0e00c014003051805182040c0a50040c1c400c002d44103041c460100158039000103202d50140000d842d460540e032a40c0c44801c2820628040103401c4801080780c074001ca01d58085441c440c41c000e4a031001405c1840b1001003100c4800300e8842d0402074017406400c00100e001c034540c5200c6404590343c5031039854100020341c1c2c2c00c5003800e045030300032a0300b2a07040410248045200020740119a1600c4003900309950380b414507030880780031002030448042406130345000c0b0041e41d04020030090001c1d1294440e0b04074011030b80141d888034086019191000c00b103190802000c0c0d808100304100c1c004c21841c0001003050341c08040c000800550b40301d0040c41801d840c62150400034200100400c2c0780110310f11401c4035550003610b060000482c05030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 588637958 1250 588636708 588636721
    0x6051b0c07030318051807110d0e010807170a0b0105190305010905061804120c020a061e0f020309090c130303053c1b0f0d03140114010f0509030d090e 66
    0x20540040b9180030b0203101c011038a00c101222040b86c01017290040c01211620481017940820207200f0100d20b64941c1021a003060001400c42c040c028159801c010341c0030411050b4132041603440c0e4005d00703004400b040d601034603801600e15000c0c0b0b00601d0494bc491040029126034503412140c12154406e1080100e034480d50180083c511440b4418001c0714425030100300090810250844940c00d103290103001400e4581c0000d2401003d41c0c4001c00080752080800c2d0345100d68020b00c3e00d00d82c05414180001d07a00c07050041d4a034010f040607240300d038203a600010014101802102c0c86469002c80201d14591079203000b90403030701304108650004c0c4951042240a40c1d800d1001105042c84410301c0103103400b00da008180301d603c803020b860140c80a02d41600280c0d0002c03c003048250702e08801920120740305840040440b400d00750b01401c3e11858000400030400d425400c41111442840c1054060310f8001c81558541f0404c40b04d47d81600c1280d41410013036074001030b120280c400ca45003440075030325483d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 588639208 1250 588637958 588637997
    0x11091608012405070318141e0102190f020301020706201804021b0a080901021006050f0105030c0c101508010203040209070315080f010e0c100c06051b0c070303 70
    0x40181c0040b04120002e840d40c094405402c900e80f00385800d4107007000d2039200d83c00c0d669070783e4465500044102000299460424110724000440f5100c0c84903400c690720000355190a10300000b41003107100c1d40c84006016044030302902103a00600255035031205403604800501d580d00f03141b040a4040c81150b561003260384200d40d036401e410308a4541c9a545042000001c2d03000006403c15010302100c415080c00082c03001020050041540684408540001a08204080850f0781d00203103082020312565445084c0c2d03041c1c603902880c2560f01c1343d580e40b03036030100c600ca06850b1080034810254a1020b00a95070400c0d10026406181d4400c504e603203031301680c280d010540b4001e60200c208000140564880c0e4444140c0c1e0304030107000214940d0300c3c9541e07401c020480b4a80440c0b80d4440b1000030040400308502c1400403000d81d428950b400517a81c0080c140c54900c44000c0c0300035100c40105000d00300c0c001c0300c503280301d480c6d40200f9a01c00d00c41c00d4081d43c840d01d03440700f100481c0c003003001c1515a0126 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 588640458 1250 588639208 588639239
    0x20708030a080718120309360c0525051608030306040b03072705010807030c090f14070c05070603050603030f0f0f030f0123010c0f1109160801 63
    0x1c0351690301c102e455108081d658425154101c0101d0300c014400000c2c02c3c00e0f060340c280d05c440c0c020784034101c4203410141d1704400e82c08104840c40001c10b88030139521080e05c5410074000c03440d244010016026202450840302407284003101c3c03101c205440b445440c4001a9807603a048a0300c900100d03645000320b03101e4486090050b210704c54441e081400050b44a090541104d80344c880010709552a11b521642e02140c043c40300480948d01c0c4411154001e64028103103c1c00d4054840003004111151a41d0b03076000c0005c005000d9139a80d961192114000f19040390001200031000390001d06031460040c800801003c2000b90584c0c1d036104801000170103c4c020f11640e4010301015002d140703402401c01c000d0f10581d021095840021800300280d08001c1c08983c040c1d80076012122011205503d0491141681c030002e8440c1001c4912019908405e6030308500314282e16a4400e140e200c4a90b0b15090191a6258441c09103170008803010801c10f001805182c040d0b0f580b00d1644031448540d80b034483e00c0301c91010303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 588641708 1250 588640458 588640477
    0xc0d051e0609150c091e090903040f080118030c030306050d060209010f09230d140a020307090b180a020702031b1201090f061d0703030906080903030609150301020c0a110102070803 79
    0xc104601c0c41a400c200306030188640c41b201400b00801c000d00003103a42c405003129032803c96040400c0900c1070249102400e401058028000d119850554901003480c20322024010180800885000c0801d07001e5003096000f84002004100352368200e090901c041d60000040d580040c2140421400e9180194071300c2065601ca01e0200c1c9240c0c40303603a600300c140341e04410015030240d114220b090008500b40100082c002a10000e0100c4001c0e61051624081640d001b01580314200342c4415040d4562044540c000a41c041580300c0c1c0b501c540d99048001c2c420301101035011300400c05603500da90036070421041007820503100c0110500d02c0761b0485080350b808620007040001c0110352a0042041900480e010200001c9000508801003045a203040a82c2d40120301080c0141c8040004980006101d03501118490255165141580000b00b516000400444500c15141c1c10401c040d1025030555070200721050481d0b44501e40350500c601000c21803000140140301d0f425020400c0c0c4d202209403808000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 588642958 1250 588641708 588641731
    0x80a0f0218090705070501061e0f0303051c090b09011514150d022701021204060503070311131d06030708030318150a090c06090501020c0d051e060915 66
    0xe00d6081080180b00034200c4010400c00f40038003408a0000e1251030000c0030480351804c00d0440f412150110405240d0049141c00e101d80400c2000c85c4c2c01c20100c41c0040003003444218681ea9159001c1d000f400c0144002d0310718822141005200401544000d01d1030303901c042c01411059440e91450443d00c0c440340c040f900400001e42c82c001007800c1001030115085058070140c182420300322a440050501c840380350140d005820000c0c0503580602552400e02c0c8a00c410a20382402d0070700c00352107407101500006c105130b035441c0020340582003079007958806500c1c404c0303e0510a80d51500b8803202c6800c5414141030352080c3c0041107840c540011110201d4804002441c00c0d942d0b030b030415009000c10145000005e02170582440c0b12105001c0740d05108214001c000903282000d42004048006d0700e4001405002280c0300070301180e0b80006003d00302c0b800403512080c5010452070068205005601c15107041210900d07004003050000c56601c1c40340d0050004c64681b07200901c26440301100030344023502806c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 588644208 1250 588642958 588642997
    0x30c170c0105070239060d11030109240b0304020102210903010605090115200a0b0403020c010c0308010b0c1203090c1504031502090303120a0204080f06040b01090c1e080a0f02 77
    0xd0340c62000805020400400315414103150718242408e0366003094102e10030000003c014840d402140c030925620721403400c4230b11482c2c08202000780b02075405003e50703e034952002c8001411680f00700080411080415107050143d580c0d16034046941c2c0000038080d22035400c0160116007410004000c13030480e00318840f5080b01030031040701515007114410780401010b843d00c3c1c004540c4402040300e0200588641003108040c90941030003414440042c1d802d5042011081d8840301203984400064152202102d21560b00c14004a005240c29011040040000030100c03c0040290000c20400c12020b41580c48481c0c24014198a0605109600006141054070180e00010207a1070b03014001041000e000c583c6048807420b1540031150007101c80c2d0310780d5a0005801d01411000f88020043d040400c0f000300403030705050740c0301c610404050241592040d034600f1804020b0f842410000c1e01815450f92681c915406010300a00e40c62003100c101d035103c1d040c82c40c1001c13514241d00c01c841c004034144400e800d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 588645458 1250 588644208 588644293
    0xe060a0209061e040603050901090302071401020a051e06010b0c0307060f06032301110903030f030714070506040c0b07030c021909110301050a1e03030c170c01050702 73
    0x94201c40c80e00d94201000340600c003803101c4468061402c50340c4900900d91111720302034008044c2c8400809070344150741440e01004c00070780c0006d140010b03220b1200300580c1959200c00101c0c58171280840c09842031181e901405407035101d6203840e00c070804a51069500d00c0e03072136000044041c482c1c0180c3d26001d620401c6640081115580a090704001610b80480c64503030301c1d11442248080211002c1c07020794250b2414607035200c244143d86000c40000c140a0800300e0b2000065200d0140115062000c2c50000000d80000c0c07103a1400d0960211503d03034075841c0c101d1424020b60340c000446044540752120f580c00700307040a241e410f840980e681030350341e03040d01c0740180d080c4581360601210090340625014400b16140e20280141401440e944038110384a40c544002c000d106000341d441402c1085008000c0104455000310302c505981d0541084158500b075480c0151280218042010304d0103c0420b8500200106400a50181401e40e007281ca8008034075684250010007091035100c202e8012818451 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 588646708 1250 588645458 588645461
    0x40606090e04080d0c0806041a010f03150902070317070306360c0203070b1e0615120c0d1527091b1a0705120c0a060e010b0a090e060a 59
    0x501c0b41c42825098181516509003405540c00c10084c03501061100d01001310900b842d2066254441c1c0000b2960700f120340c07510010300081c000700420002c040d180c0d0320324200540c1070400c00009005a20003159a071445003801000c10700400c58040040109001242030603101c3d004103000d803800429080720310048145003140035145050940c010307182c0500d280c00c0d182d48a110346c440c0640c40745c0203590b80b080c452400083c0d50354003d10580d02d0001c443d0307a5240035400124020780c4658191020903103110346180c440c10034091111495a5900c0900420601602080c050024452080028880381c1001c0c0e2030702c94001c0c114024138110150b00c808540d1510701c1030040e40000c20303080c0000520b00e0325903140e05001003044100d410451140a404108072202c8483c2c0142e15810012081c0c241500343c0e44150325021490905514003d002c0707504a440b95007445043c00385035203d141001405425445140a4004030550600c201184000007590348014014200c0400d2035a015041540e80e1081150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 588647958 1250 588646708 588646711
    0x1909051c02010b0a0f0611060f070c15020406030f110304171e0c1b09070c02010309021804210c020f04051b0a0203090406060509010c0b07210204050f040606090e 71
    0x804543d242c245803210303900d6a000030320142c41804225805541005c601400030240c140c034841e0b86038410320810a10440c0041880c0c0c0000c0c803450110b101c140141020096603441c070010846961001900003846601584030800a41c2618810b01c000030030b50084040900017141e018240b01403194a101d50b81c244080205800a400d40d03e0030304588200041501c01d4000542420309070f40502c1c40540540d8180880050700c40c0304851240407032800010003002038001030300c000e0600d80c0311403610702107586400c0302000d501124031a1031020f00d072504100c00035182003480d86114120420300d002c040c9204000501040750003800c0320401da17201505100c024040141041004084c4402d55140032000d2402050450754650046440d1145402001300705d40700303a80200c0501000b041007400d04d913000154100c9068010707010a4071655000130960751140d060846110007a03400d10074058202065000c1e00c2940c00585451107055121000d001c01c49045014960229600d044200191100000e045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 588649208 1250 588647958 588648013
    0x803032701110319050403020a1728031407051c0e01140a05131505070e060f04060207050a1208030411030a030e090609071b030c1703190905 62
    0xa503480d4034a9004542100d441c5240e41d45924800818080d002007030041445400d01c01800030040c905007680d000c3d55401441c180141340c00200000b01140d4100001a43c03401840041107121403040058882c045582440c000b00110345085510010101c0041d001d61245c4c80c941c841914203107082c140be5080c005030b010084000c50301d03615489404a0b00703001c3c69903286d9240b1080700d018102400340c2c3c025510700800c821411085400c0d81c0011801e0100c4000b580c0d0441c2c02c000030286c8400c0011905210f08004070741c0c1082000a10051030144034006000710780b103581c29103035010386641c00c125005450303106e6010040d402c080124045a08040195041841040e81590080352100400d050201c818402d03404a15148011262410f200d1070469210500301c44c03006003460f04c101c000c1c04807100c1d80030000841c5503103050481050300a0951881c640d800c03400a031101000b15a00424a50007102d8030103024056000c040020512801a041c155500c02e0103880011030701d1698040012140300803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 588650458 1250 588649208 588649261
    0x2a0f03100204030c0e1b120a0e07240903050706030b0316030b160201140121020a170d0207030f0b0402010e041506020c10360e041b080303 61
    0x40c409910424802040154441d40c45440c000345402e000d407100b520020301860b0f089100a100d140020107100407920a04641c0d03540340810344466200b00020850741401444074032600c140030604d14410040c59048800b208611034205c000900d04440c8043c5612000f01168000e810a00c2038038007035005a904034101508030317192940500c85060b500c490b00c0d030066030301c0700300303141840349040fa000e01403a480c1c01c49000a0000c0011066202004001442000c2180d43c100c0781d41040b840c1002801000a500280b0501d02c09445081c0500c601d2607030a0801c0440c894142d00d41d94103400400c614084a070024050144518103445003940c141000f04101e04115202d00c140c002643c035841154460003410710708504007410004060710742500d5414207031064a400f00d03111035965100061010150070040c1d0048202c0c00c0314921100501c0614080242c5038035603202048011081a242e440b03240503140e900380000081139620301c0c1c05018000d82d01150010400070751400004442c40300049126040e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 588651708 1250 588650458 588650473
    0x21c110d060605030613080d0e0c03010f0204050a172a0a030f061118011215030b071b03050405060a0908010509100e030406021f060e070507052a0f03 66
    0x300d1848031a20125512503580744107220f1410100162548044903480e00d6803150465200d1b140c003030003040c10354030b0080c0d101c0280208690040c003600c2c0418001070024440080c10520300740294002e800303901c0c0a0440148002182e10030800015541d20707049001d000880603100e90140c02003510081c0c107001e41c0031030040c0f600d103072109130308200154080c507840c5010031401d10700031007640ca0b4507000d03c807400c0003848018880f5444012405d6456800d091a64007401003c7d0711202034608081d181000894a5000009010140400911030513140d590b41400d8511030b2507142c200c80841c000640020401c4c08248202d09201c0000c0c80614024185592841d940b5030465003500d0b070486440100d40c018143e071a44880e082d001c1d00303c2560b142c1000d5400e15046c0400259203100c2d000d0b07141100110004c1a610001c0d003944000d015061003960070300149003000000d80075074440760f001c54582c41000300329000c52040310700340c1c1c2056030600c1c10005890544001c0120303003134800f11800d600d0b005456 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 588652958 1250 588651708 588651743
    0x10180c20070e130b0a0c05090607030201090c031b08030307090311010e092707211a0c0405100c0f0308060118081e150a051005030d0816020a021c 64
    0x5840c2c40c03091000d41d010328400f9051345454104104042c08412240b42820030a8a0054001040d03648032907050b03035a107450300c000c0e0a089000d0000700f0b00c0540740001968020003401075200d0550207440042310780815440c2d0b1007038100c0d0b80344000c6415400040000c3d00c1480040c031a103004a42085052400c5107081c0d03c0000003404001c02a0b8043d42e60400c052100d4980d40e602c5450300e010942200083e1502624094601d00c14501c0c0340c000041010003040c001d4208020a4018a0003048182c0c000d4000e207041040803155a0180c0501c602c990106180340301420300c140c103034041195100348003480d44161990290b4032900041c01940c10b2141d2210020256540e0006450040c18244018408095503150f00c80c00100c0c2c941d0407803600e82100030b00e03902e4110980b17080d41d04045401c5000600b0758840c08a8150700c04c954009036414080c001e030091090343d121364007074000c880f0300b42541004503400e0000d0fa603030081450000e40000720144420b540100004080c1810f9004840c942e81210342407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 588654208 1250 588652958 588652979
    0x302040f09080c010e0d090509150d050304030501090b0f33100e0a0b120f0405010f02030c0319061208090a030c0305060f090706090b07060605040510180c2007 70
    0x240c0c045107040c1c0d0340b4040192013120030040e065204080e810210313821400c00c004664002c000402c00c0c10443d0310361202b400b0310b854007200e10610503002420b698032280c0b03034a080342c060a103c91041c0e403036000c0c090101e41b04007040d44029000b0300200c40d90300c40381312900c4440d89100002c4070031200e10f4858050202c800e91942012000c03141070301c0d07075400c00b0083d00400f081074596441d08a12050141444440000301c51401015003100c0e4013941043c8941e91454071601515281c002440c6003400841445010000032001e180900c030483d40740003000035a50014801c4810368841e05401d41e090a8000001c202c0801c000d120309840908000480d40d04d80e150120700700c50030381c4111030940c004400c0120040c8600711041d040400c1d1006022030500d05840188010942e0150346001480091510300f004100d60004000b0a0058030034082403810410b010b9068549105918544130110307819070342c4038050710a0006040c0c1e2070f202c00e52241801908104007131022851944c8501c9a40d01c00308101d0b144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 588655458 1250 588654208 588654217
    0x180f08010609140906370506010e030d050405060d0b060307090302120a03020a140a210e0402271219030306050d031e02030d15051504060503010302040f0908 69
    0x50600115115161025110480b00c0000048558819000c203103d410b8401040b52508480503668401306d0703040c0e040311101051108503d8444c1c0b0083c121141d444070075580c0105201d92000d80ba075180d94000f8005040c1c03141100903242002800c1040309100d680380c0800503280c4000d4a0700c00054001079900413626641c41903894601003403444070200214680140a402980242c4014103c09a480d0798003079070791034070a08010068030a030400d01c40b55150802c103411000da0484140c4080c240e841c5001020300c0c880e00301c84000145c10610428113418170707000300d480107050f105c070120350585040254501402500304c05507001d22100c045416040003005420480000d14140d9000e0030075506d8050201d40003980641c0c026102d40320214003098000d50700f080e00140812003141c9020510408034198414011100c9080d46030041c2d140c44905010800030035982c040e10000301e030300f001550480840c06148131341d0000075800c10041c030040c14550048a4003502c00b00020440c4d4040d07680740301ca80d401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 588656708 1250 588655458 588655469
    0xe040f09050c010c080910030e0d0c020111070e0619030203030c06011d010501021e031e03180316140c10080a0f1803080603161707080616180f 63
    0x46039211441407000c24040c00c0c0501900b4245001c102e01c0d99511400307180070b10080d50344280c1c1d01c6c85161100e00c0c007940000387e0b1513014006455041c030001c4c10150a641d241c44081e40004c802d85400c07610b00724001440002c0e29600c408000503507845200b00081c0700c40300400407a00e4210b00c100080140c40c10009004203060080140040e90b050184000154020740c14044603141507200400c110303600840d1440590700d60f01105500b035601c1030358480c55441240940320b03100361031200d510210422170001c0e50141c5101524052203d5100d409140d8074020410141045002c10f20b0b0381d00051040c0f000092141c2d080c1c0c081d00c201c0360032500003a451190b0f140e901e2002c50001010060300707800301c3c81508231001010741d0400c5131a4600400c01107a4184150040c01e00102502268559500300000c2c11100380842c200b05d08103450701c0040104203441020000d0380d00c51000c0104103904041207003817040c6100d0180c082801c03d040000c82d00a8288901c1c4c00401c0503140000c9203910901e0422070203401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 588657958 1250 588656708 588656711
    0x27060c0a0b0c09150d110a12020721020c041d0c01051e0a0c021207060e01110709020a11060106090b12071112040825032405040f0b060f0d060c0e040f 66
    0x45d401440507500100e101080b0140704208043e40b00d60442184101c88a903503c1c010780340e072580d00c1c009441c2465a105030066224128903d00340c654000fa246449c5481038a05020190b900010280e415850b802c2c0100d042c2c0140c2140381943d40704d1006840084807040b250486440f5080c5616160b034056502d0b940003400110071007055040c014065030001c18003100170705482d031420700000c0241142600303c5040103044000c00071421010002030002d4484028215a10450b1030300207070003074505d003279000c200d4081c0200018915000f5440c0d80d04948200c0d5540d80303443d0041e84081407403040180360000b403018204215034011401c01194100400040e0000ea07510f040521003450900035034030000401420440140030801c2e104c1d0004c0c1282d41c08003060004e0700420980c01543c0f45000000120a450803003044148580f001d444200c56000b9450b082c400d84030001484800d11806851640000d9004684e03c00191258042d03015600c0c28644600c041380e2a10001d02130715901444030480c0e6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 588659208 1250 588657958 588657967
    0x9130c1710030b0105270705040e0109090b010806040f0204050c040e2e0f0b0901030b03151e041113110a05040e0604060f1802090627060c0a0b0c0915 66
    0x2040d04a02c5024140498094906d0700d0702800781c0c49540100350111400385a06004a210786008d0800d490260490700814440d540e105c0003180014104a40180d81c3d0000040000490810110341d0b9400382e900601700d0b150001203034003400041c00703010f4040800c1600c10440000c443c98410141409412015040d10b4180306140e1360307d107100304107010141d4008035108204048140726109e40221020402c0080c0c0311010680107800400010000a40500071802e0b01160040790811a0b440303641145171030801003e440440042e41d0034200c800500c0c2004404019155140015090300e0010100b80701007195050003404004680080303640c5000b00350045401d000c90504090420703886441039a04220f050b01d407255000c5008410720030100a01030703102d50304100010a804550f042c003030103080150f40740303c074140f00070783c1d00035010151174110750405a502d103524040302140c11140307181e402400c101040341c83d2560910b0011344211a110740c10030000341251503070700c0d12105038035003015030300d494 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 588660458 1250 588659208 588659213
    0x61b17030901150807050f041116030201110a120f060b041403010518031207090902071518020906040c0c020306070915050306030703061107021302130b09130c171003 73
    0xc3d0740a03962907a03038204480c8400c2c000440c0c005820f01c2215012030300d004030b14060501050003000c1c01070b507448504c800003a404c2c22241000c00d01000d0140b180d13008100c034511520304010307280981420140004e090320301303186541d10f16411034404107544410006081d681d510500825501c654000c01000a8019082c101c0385000e01c0344e6035001c0c030440b804a08415642824980f00d00c6030140c86504c2d220018003280001d48200e0f00d5402800b01000304540e1a1007030309207252048140085070513100d04003590399000398a004003d000803a406401c079201c503241ca4040101610607040000d040001254440f400350790f08100d42da01070302003a2201c0c0c034000e0400c3c0000420940000074101480400c00510100d40c400003060000c60707401540c009408950740d40c0d810f690344504440a9802000550340c18104001c5600500c803540d0704488440030140e41d6400702e00315000388500e06500c840142c4203107199000310782121000302841c1c9090b00b00703100074070103a41d06c0c500d0a8030180440203182c13005204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 588661708 1250 588660458 588660461
    0x901270609091104120f051c020a02100219061e0f05060f0102070b07260706060f171b0307050d0501050105090601051204020d08041a0c16050109061b17030901 70
    0x1500f4005101032850a07080009290b01080f5565000b130240b8626020182440802e0100420144030640100b21103810540700075510f042c8450140e20030300900d5191403a203400016130484040d0854211a0703000e10540b103c2004207081039803c2c40c500d0044010b550100f44502c540e1005035a0080c0024a42c00c0c11000c0c0700020310010b8030a410740d4080d1500303114040702030040c0c0c7ca27001c1d880040c4d60020b00c0c1d0050624448060a4002c0b8485003000c503160342000f8182e04100d050300d41402c6440703222550380c49840082052000010f0340c40d0000542200b0140301c0d154110840d10001e02282d40c3c05645002003140c2c403c04c00d4003a10b00d030355214014040e51500301d828940080c02403038a1400d140c0c2600350110500c5014000900c10000405050100500d29042e5801441c440a018441182800c80e031045036000407208076550007a01c401c660002205490f07081a10411ba50b1200c0d114100030040e140c01061418103800329032142c2c03000001603406104602d440c540c149110341c89003042a1181e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 588662958 1250 588661708 588661721
    0x80f0c2712100f11041d040f02041b080a0b010f030504060e0f1606030b010e0409020d0506131b12080d1e09031d1c1e0317010f0605090127060909 64
    0x54013403800c20041108000c21a0448081402d005800c00a51039514100b0016120305100075005170901840038607038035480c60142c140c41040c3e01d450100d580c42c0b026105c1140d021008440c04515900318800350300b8402d611a0340c0c4a031290b00f0011b0840190400302c0d1414107003400c16616030307004104907076004040245000c01051213080034800700000703200280202102410140c021652449800159a240f402540b401508082900d4844c01c041c642c60600c058403d030700b59011080d0040740401040c02d004460115141117040b0441c1018550340c51200741d021581c00c0d010161a2451501200410820b4007840110f55000040481841c82d01506040450f40318203201112114880b40545a00340281c43c5c185103804000740540c007034600094980c0085140000c030041407145070301050b4101c1030385691204014903a4450b80c2e0303a0b004540f14110280540b00008406201c080260350152098035000900c180c2c407048404403408503000d10500c241d00c070800151080b0000c2280498034230400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 588664208 1250 588662958 588662981
    0x200108010b21250f09170a0b040b06100207050303030a0b0a0305030a08150102011b26010e01060809030c1b01050904021c11120411060415080f0c2712100f 68
    0x440042c18245000d000c0000703d1246a201001d4011b9203001c100040c04207800140d40000512002e06050512030a440030850341d81d4004d481c0715001c403210900007c2c0540807140c0040c0190f1443d0380c3d00c50000c0280c0205503400f6007052524401000050003070010b403840e14100c0e41d490046240c401c1d0f0403800350320a5100c0506591501c15030020b039583d440c180b4030310b260300e500342a11661030581c1c101d004020340042e458807a182160010402d4680e480e4014101c2d41142d0f41c0c11403076242e84012948074800e031911541f05500c204021000b44444c001100031b1650305041150405c039070640420182c0c0d003d8411048101014402160a500c044c89811160104100da84c0d0420041c885240b001c20400303000540145d202c800001d400b95541e208440140150080701c010303d1b04103460280590b007040c1d51021301000303088000b4401d400c5120550f034840c000c1d104034182d4400e03006442d0754000d19030380d40c03203410900c040d40880140d003040040c44103180c02d20700300081215803146031004403480b00404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 588665458 1250 588664208 588664217
    0x140301111909210b0415090303021201060216120c0e040f122316140d02010b0f06180d1b1e08070b0a051201030f200108010b2125 57
    0x3a43c0e41005a040049400c4d40400501016122424180044400d0120010340c0505082404040603819005014612541ca00c11076440e40c071008241c0c1c4903508100142c2d4200c00440040080c050130090764510240110200740700c07161a0410000300d44000c850503104122220000001c01c03804982c200f40b002e52601d8800310000814040060800e00d0802c1b6020300d0a0200d48206a1204940b0102e031456026050403a40440300d242d99403181c440402c44c00c003651034141003065a0401402c100f0710842e00a21140c07401c04071802500004400001e415046403c40740141f0000b80800041481c404c03020340490206450902a04121000c40040d02d58000c0c000000300102d0134005805420f032032246080c2916031084444c12281c0e07009030088054000e04070030002040c00b450f00084042d041c000c4030301c00840f01c0405584000380c840c1804944c00204030400422200c01008060418402c0c0a00e0b00b40b03143c500034080600d041c0f03040d40c90300c40302004803109a81c3c00c03c20200850300055541070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 588666708 1250 588665458 588665489
    0x110418052103070f110f0d02070801050408070b04031209050c030f2406060c06011401110307050705010f12050c041526073018050601140301111909 65
    0xc01d40900000c0c001c60180560340c0104c942c0c607400f51580c0094203c51000f269006070340c030140543e41d024503420b404054050f9600110350120180500b510494020340654030b4820256076003410711500800c29000c1081400c0d1144140780203000d180c44440c043c8004007110388080c02014144550415022520b5000e40240c03005166900c1e0007580703001078000124820f543e64030101c1d0140c442c2402080480c0140e10000c2000034030404010700f610800c0e80c0d0b46290103560340b000366482c0704e5080d015040341d105d0481005558810001c140132010b0301c0c034018890400c080349410590360b0075a071001ca09000460103014420300140c80c0d0808a14620700410345a41c4030b50310349009078046181c0e0180a10080015102030f0142080880d006002c041440003022030040c40305280202d00c4031213a10030300f000988169400a182c1c0580c03090b400001a0115034070386031000f181000c1016034030350103540780e888402c002282da0010b020300d0f0340c000080e0350603081a544c00034100e50032500010407241c50540d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 588667958 1250 588666708 588666763
    0x60c081902150604290411070302010212010b04051e040e0a0f0b0601171311090f060307051002030f072604210b040f030909051513020309060c0711041805 68
    0xb01502c5c0642c59081024441d90320a0f03011078003a10180301100420b07600019030304105641540105400a16200ca4240030307621030b0b0a015a40c40360780714050b4440010084040200082e10101d000500c00078000a0390160034412281807558000003540e414145054400030300122015860303011900b407909201210300e4428641006c2d0000d8103407a054000c00c0890410804c00c5400c40c03412000090007850780d49010b80750800140801c0f19514001e01504000180905207079110074150342854019509260208000d40c8144e0010308017035039281c00c0810b8003450b1800d0958003030000f80141401640d00d50034074081c1e809501c40c000e0000703a1882d0082c119404225511005500698001c811300050840c5040403120f960301c94002d02d010314a0701c8180300401100050050041d1382c141e94040026044100060403404104c45400d0325421500011340040e02840040116070b10460401001003045004036003219251880022400080900312040c08030800100320142c0450409003203c4d220707034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 588669064 1106 588667958 588667991
    0x90402070c240f0e01050d060602010e0d0c030503010603051503101a06091e030304030b09010506040e0102160305030a06080a0b0f0112050304060c081902150604 71
    0x20080d6000722071003802d044003400c2e0b280c5508180ca211a401500e101e001030208604120080100c0c0d1040209446420090000d960000030044040e040b480d2500c25050031350320500144031546000654400c040b2810b54040385800b00c1e035a254071488411060300000703c154140150310807840d0f00c042a83c03085800b80340801d4842581e00c2c1e01002c1c8810703482100c64a941149644401c18280c601000c0e2a14407100050304407803030140d0b03e4503580001c0c41c0544070b07015241d44030028040345103040d008079103014103200000c500e000307022130319020340a48984008060180201c0003c00c20764581d440b0b04000c1c1303407280c140d42a010342e6250071f484c0380714105c0302c0601c289005400400e907990b040780d10300001903002e002540b92a0034001c050b50600f807404822140c00c001084070000100c40995012070000340d40d00100101480c170f14103070358440c10042131180907520740440303281100d611 = true := by decide +kernel

theorem cover : BRFrame.Cov 588489208 588669064 := by
  have h0 := BRFrame.cov_init 588489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 588489208 ≤ n) (h2 : n < 588669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
