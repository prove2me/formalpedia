-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5244
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:13:40.594192+00:00
-- url     : https://prove2.me/submissions/96f1563c-f7eb-453f-9fa2-4739bb010329

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 942985611 ≤ n < 943165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 942986861 1250 942985611 942985619
    0xc0d0e0d0b0901090c0321031a06071b15030c080c03060618040e1b0d03170a0609060b0903011404020f1c021903120f021f0e060702071809020604 64
    0x440d084020b4112541036682d41c600c540011a550805001180200318024641e4a88442034000003031007003402c02010700d00301c14140050303004108001c81803030656a0640701c41c0c0d43d16255005c81586040d101c2c004a290302c0004605070594004e010441c03c6940a001c0f00c00c079154140e805450139214502c070300200380001221400c144018111208002c84001203071110103000c9030444c0c0b032081c05084c81d50450501c2010b81130a48080005810058503142c1920b2410340b0000c00080d101d400c1c03103408070001804038803005004d8000c5000b0f40080581005010b13524a400c44803580f00248a034001c1d402d00216600d261030b00340d0082e20554025000d8405c480b0300c6070030803400001050700e81210244028905d005600c607134619031203640303030060315525060031414441c3c2c0001c8401a01801c01004055005542d9408500f285411000040f400325440b143c0081a001d42015401d00d07046201e01d40030001050350001c1c840d012540c0d0301c1100300b108138100031800107035024054007941090b82080108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 942988111 1250 942986861 942986873
    0x8060906010f0c17131a07110a030812070906050c070510181d060d08040603110706020d14010f0602120a03060e0403020a020306160e151e0c0d0e0d 65
    0x5400032200c0c58141c03c82c4106948600e000c00c080b0f03800300005200400c070383c02e02c40440c12206000e01181459090100180100060325106a803030040c208041800254400e07100c8816040184d64003010494945079090000028241c00f01c6400c40003070400c1c1c00006240e4061000c42d14084134030001303802e8550411007440506411340d01ca5404104079818080128420b0704008000703440302e0b0b480d07052501c819104030012864060070581c45203000c030b003103800002c0000040b10304a550038180031889078100540c0385007034010400007601e401d00008202c103444490742d00281d60039080158405007039898400e55001c9602502070000580d22805851123014030007000707001110398614004c510070b038450b40b01910702c0c1e00c00e9404501507485009851b00318a0107009003a4081c0c5002055035104100410040951180c245241c1c002c16a41304240c03400c815200c121115041c04135503003008a20000c02d402001e52102c4030007941e40c062608500300043c0710300d0720340c43c61000050070948500d000d902d4007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 942989361 1250 942988111 942988127
    0x324070e01081807050a0603091103070e0115050702090c030406060b16150e0a030f030c0e1c050a051c020c3703020907080105040e1218040f1503020a060806090601 72
    0x1990f00e51081810018003607940044043c0078285595022512070503a00d884485049807104951103508900701c140068813144170030700d044909101c20201046043c02055070740703120343c500180d04245103008000c035045170030f401503010301d1041600704691642d6050b010094003400704494154229150003401244013121a62076806802000144030300d604902140381411104048020030700e6981e801c1001601032241a030b5140030343c1090b21400d811400000c440340722003840a02d255002000d00c200380f000c108031805000794080700301c03103006408010704103030000007030f80c02c2c0014810184681600e0503d0303601c6201c00e41e075070300709001400c0010380d50f50814140c001501b03941014108000000d40da032191b980340200c02c81e03142c00401d23504140900043d190b18403258101680501411490000e0700803c441040510031841c00c1d0000c500c3c030005002c3c2400200001010741031484030a5103200030411030b000c8070320858414402d00d6a480c0280d41c220000c07610541c0c40050107000910350b5000d621a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 942990611 1250 942989361 942989401
    0x140c07020a050909011b2a0302011503080c2104030212160308120c0703080604050612010905010f0b090f1306020403080316021614040216020324070e0108 68
    0x1070411a80315070104030400b1003114000d10303683d100c030003090040b0b40c1c1d0104424240e000f450208100700c0040036034100800d1000c02c40c1c0245410413130140c1818400e6124103040025140400001c503520308004500b42c2140040c003503280141407008106c51182c1c524001d000c03441c000c0042c01c0c9813460b001c0280728405050103c3d41070107040003c941c40e0004c0070000f40510b01c290a200c0c1c07141d5140c0c6040d440048000c041c90010799040201c40c01082c0c00c0516150b202a04880124190341d520000c11030003501006021620340c03c048021081020640040c41740007941082001006804010840e110340f0940707468020308107540101350304080c1100080c64107409000094503140e0741e50741d205a158400c68005001c81061030031201c0f07031941448001030544040d840307030480b50704100c03c900c4c400501c1c1d100d0390710556002030300e500b01034032110100340d0898006060705d4079a4100d0341411400050601094480380340c00000480c07460190a207140d49032810381d60f00e6a01d940d80d00c000e2040b204421a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 942991861 1250 942990611 942990619
    0x204020a02010e030a0207061404060c14191a150a0603020f190807181419051504061101020a05090d020a03060c0905030f010627090c0b040806070201140c0702 70
    0x3490710301d4820400042c29000c1980c1e00400409144c900024242704900030040c000c1c42040004100441d8091480303404a5040b40f409901640c110900350319112030a880b2014030074213a8421f505010f80b00c01945c000020400b440d008550b20200d207502c6424280600c9a8030070701e280014400d080c400d60240c1903819580e036405140103003c1041580c808110403440d00054080b0b42084a481c0e07101c124202d400384000303840c07455030b8288002100c008030788414850040c0d80c60f0220000c0c007003200300c0000007000050302d810010321100701e48163f55803140c000e40340031603070250443c10368440500c00c503002d641095603007a007440415000c10281484510f400c0c0d034001405c000102c08220030740b0402079048081e4a810016030b142c4800d140c2081039120348464182d14283e07041001903e68100006206204401c05503850940c0103600002d0000c1c05d0702030b003074125030300022405c040e8076401070050300c100c40110345407980c0d08402203017a5542e00d50700020f42410900800c00302d80002c000b800b4451f00c020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 942993111 1250 942991861 942991871
    0x90106081f024308310f06021b0108070c021807030f0c020a020d0b100e0c070311010b014a01030b0d0c030f080d020310030302011107020109030204020a0201 69
    0x308107141001c00400e400c540c01c500ba00d9800c3c01c0e12038854400ca1042d50001640741c0009419290f1466a000304281d4a03d10354080c0c1e540607030144400310314558070004a2590310b90b01d031100c00c03040c1040b0050140202512079206800e9682403030b0703102c10500f003005a50b405002d90b1912022542c2215808040380c01c048115031034600b10041404007841541030390760000d12403816140400a8443c040c40741030554000c12012001b6032255141204101c0d0000014119038580000c1d4420014803036021500b900c0642c0103114035001e50100400c182406503a030307503000c81507004160f0300b00c844c00c000c0540800e06c108a840100c80c03100300d8240380d0f1a403550454902c1d654140034206042980207140501c0600d011100b080796806205203044040141c0d158107400601d550340401425050001402141ca80c100d41004c00001001b103070004d12109000795101e00b001e0a111403000b80c180400c402550a041802c100c3c0303080001692003680d01690741352140341c034640a00c80250300001c3c2490440d502c0b8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 942994361 1250 942993111 942993127
    0x120301142d0a0f08101802090127060602101a1005120109060503030a0c0606050a12020907020f07050f060d022b14060907020a1712090106081f02 64
    0x400082141c601600d00100622030303a034400c001d25039905820000704450f0302035041c030020300e00280d440082c9910982c0010290500342c40c04000e480c02103c02076100801d100040f50100040c041c40c80e0321100142e04114840c0b0714034840060303d02074080d80005900c8051092608050394224007907a0a80c411762480e503900041c00b08200440311b40c0340301c2c0070960010380e401ca00c1703c1124000c0e00400398460100401c0b8105000291288074819058041240000d440000d000580d840700d00188001002000216a291000001500301d060268412903e40c40011800b500214402107020450809496045d0400081254076078100340301c6d0382c001c0000c0c00008d540381e5042c8014001190209055407a02d08850b60450145c2c1c0d8012600d0710305400c0c101ca0900d030f4281a9801604201e08407009071060365400012846d140e40c00d20040e00058100303d2401320724802d80c00800a801c40c0b52800e1403165603440200e400c0c4c9500d07203c1c141e40b551000241450707000c0800c060500000062601500e80009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 942995611 1250 942994361 942994399
    0xf15130201200304140a08030a0c031d0a0909060b090103020f2418030709140c03040204090204140901200d2c0c01030c170f130f140601050312030114 66
    0x50f04800708a150b0103101551906d0601122401040c0d030380015450000d010b00002c0240d83d105030003c060080d216121910341480e401038582050020380f940088640e00c851400141000aa0690f025407404941170094140583d07958140e940203086120811441d005126450081001079a0035031100c86441c11915010320051154034144400000001145810142032401581c4280305440c5014407942d40c581e8070742e4945030700ca010075400759100d039100c4c000708001d840c1c80b0000035442881e001c0c034018400c980462090050381071000800155980d0060401f80d41c0d120710b1070b51250740080c0451200721000c3e411a421400480e08508501c004140c00101c08002005050546410180d0000d04070350345031041060a00c114540f19500c41030303c1c4921044440090b01404510601c4800146400c0c40390500700c03200c550091100b1900a514200070141c61a031100e0070314640541c00002401f03150008404000c3c0078882201e0340795910303214001a28401d905841d0381c02000c01d44655000c000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 942996861 1250 942995611 942995617
    0x90c0c0f0601030b13110103200c06040b01050604050604050607082a1011030403030b22021e07021e01091502030c120c1203040c170f151302012003 65
    0x26451004105650452520800c40c076001052010701780385000d2424007042e4201c6045024200a01300007400d03500f41000c1000b002040f0310406a080d0b070009e09040c411304002600c074801c81c02070030192083e988803030820505d8400c41c071074541d005006110900c62171401e03400901c40f8911410029240191481400c05000500c0700c94054034920200c49076807c10b400e100d452074694607000d040088030722aa5503410341e800003510203400c00d6500c4102c840c0ca034032040c1d05c0040c14070a002c1c1e00c140484074101c10001940c4044c0140c141d40c421800c41000c090104025660265030041806401e20351880c6000305101c101140c2d5410441d448070005600f80f280710740d14400c0d180700e41c09196640c804c0940145004100781a40b62817000c00c01c007400c1c038150042503d441200d00da19011b560f0b0b45581c2414040d03015690072075040440082d030a0854614000366448038a440724040d070b000742c95402211080d4bc581140c078445011800b0540400549c8103a041e800c64103102400c1d1075107016501072261541d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 942998111 1250 942996861 942996883
    0x200304092f0406030e0102090901060818030301140118080a030809190602030a0c080105030601150504180b011701030f0803070210050906060a050a0807030b06010c080a0503100b090f090c0c 83
    0x1c07002500340811a403500030150419407030802540340402e01d0780841c5c1c0d041014490b502c20007502d900466162861000418002c041c001d041300d4813561641c00b00d040c043c99428060340030804060281030181000301000084840100161405061a8a0584408030700174502c0516000d0040052641981c643d14414020702405004ac0c80e460404201c1d800c617219940010305010f2000c0041016503000919179054495543c070f092200603401034113440c0c90084c1e03000b0002012000404403400d80030f41d40000d090401c260395075151000c500403007141c250428040500b603030310700501c400e0204800700000e64002140c3d1045846a100510841088904c140c40d0307018560011428803909151091150300500000c481c804503c500e8984815560141303440014004405500043e2083c0c4c040c100f0766102c160840080c80e0f40da11410401855030f0b200719100c6040141c01500891410320744008d54034900300207840c0c5001001c0c004200a09400000c065440d050010030410031019405d000f40302c00d00b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 942999361 1250 942998111 942998201
    0x30103030807030b040b030703060e10060e161b080a0909091a150102151b070b24131a040e01090203070e0c0d0c0905040e060720030409 60
    0x7034200404000c0a99425180c5248903a080900c01000c0765004600c201c00c40340c2c13043c0d001a411403050415801d1106082807a4035080c54282d00088410041200500c140b0f0018500144600c0c000f805031160761458a42803425a40410408000307198880200030541320360a08100c2569640c6a003800d940a00000302c4544202150390800329044528050f00703c0c1048003856281b51040e00000e64401d00740c802036803002a01004103051031406a56512101000e8406c90b948401c0c0341400d81c207541c1c1c01e42d0301014a05030708000d00250228001980d2a900d4001e101c0a64550814403420152450031201010001c500d01100c12503652032003007040c241100f00012030071704070340d004050810307105501504000490000704981d521001045601c1040c22900000700030070905800c451044081e044250406d01c0c0280441d038030200020482e204144e107503a0360a4032041c0342c0002e604a02e102000b00f045901c03d2101340000c44482d041242400d44000e4100d942d06509401c0440c04020440b620310342d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 943000611 1250 942999361 942999377
    0x714040f0e010911031c0c0c050907050a02070e0f07050d06050306130317010e0c0c07082407090f140d02130509070b040807050d03050c100b030f120d020c1203010303 73
    0x1048041c54a0794000e40303040700078046d40c280c01b100303841e81118070214003c01c2140082d00c000030400c0403a600c2010317003000b804c0351303a1625007902c1c007401d10340c04840f080303001d4400d204000850311034030390b284d9110741012100d0f85156269917a081d1116080b0345084407201d40c480401107481c1c6c0341040114031030100c076040003c030390a071414040c000d0301d042d01503e490341030309500602480d069404400d42108002c42d401e03544031003400005013801001c1e000000e2601404040c1108030118041d550256101d600b03a01c8042e4449020640f901c400b42c0c07252006007407000c403040080d00c1c40c000e00d14103882d00103172016400461603800940201c41e030103940008540d8a1041c81100c41080000e00301502d21020319174586810002c1e0240d07118100c0c411948602203241d1040101071041c000d50b8104031a99044070301a004808106020b01010300d0703028042d21803004000031802d800101155020f1866010500e0b04c070b41c049104c00a5030095480760f00358070070070041c3c5000006160055000318040c0c8d0754151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 943001861 1250 943000611 943000613
    0x706140109140f1305030f070c0905061e0f04150906211a07030b060d0501030605061516050a02180109060b180919020c011a030d020714040f0e0109 65
    0x104442c0000c000d400e010010b0340070020720107001d02c01580c004800340102040f4005510340507240d881030042c0b00700031034000b080190810270302803044020f8a881c16401e120542d00c0509009400340100302d00d82d03622080b1078400310103003080469410070800107030000c1800003448802800f480459031241c0745290f580c0000700011860003400040e500b502c1c12400c025800305031500300c265100c5409420900c4400b801280d4214080d0b808221107a80c080c003041d0310b44040a40760b400034402480107451140c06d110000e103030751501481090114a03100411410f00c050124590b2004c00400b90840f030341e200e0b0180640269540d14100750010003148411020741d814912078a090b074400d0703130102d1a450300034000365000550003115040c080700180c580059550f2041010a440342e81c041c90301d45454400a02c0c0c009200e819004440d01503440041300c013810b00300300245079480351880d4180006030005030040c4206150318400c000e401c10001d0010a01240450f03030300045502c0e80980014582d95130a0800c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 943003111 1250 943001861 943001879
    0x2a01091a0108060f0109050a1404120906020c0607110a12080a020c06070206040902030709170d08010e15060a0309050d110f0607090501050c03040b0c0c090c1908070507061401 77
    0x40e024041c580041c100c0c0c4d08000c00000348611060151315140391b1030360005542d01145500c038265080c0d28450500c01e600b1303e4203010021b0000e41c80600c0c0020f081c03002c04a0194000600044000c0024000e03902d0b00010f6100e5181e0003945003142a4011000e00c000141c03918400040000140035070422075035410f015001900d01944c00724814040d4000313100c5540540e840c142950200d800d60000580e8960712407400716041c1c8115000310809080c0302600750881400000d14942c00e50703480d16211084d980301c555070f485c148012039400e0030300c58014a46074410b0030710780d010300f89071405400c0106411100c0e07a16541441d1302900032800040001c00420300b035210070008048000c02031809400700c0d0170101c500502240341401030a0510000181a44103000100102c900030948211402d0301c558030002c4a89c2c0355100c40309840d101d48455000304020049150480d60040b0351001d150320910303081c10090f80d01c107100401c0f00051280174400b0302d0119809004900205800100c240d40070340c1080948 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 943004361 1250 943003111 943003163
    0x10e15090f121c18030302030a0b0a03051c170103050303060108010e04030c0212030d020c100501050a0806010510090819060e010e060411060c1c020705040905032a0109 74
    0x1000540c0e000201082410540000701c5a501200d00d2001c440c50070143e20480280210940c0810300c40d000395820310905505030301a5001d807002c224180f18010a803010444a82034500016102d0740000031240404000840c86111120090810140038200c6c02800d51a900c0243d00a44840d04004204802c80da44440b515024018549008065003000c1d10020400b03041403000900651050b03410707244154041080d0b4034131401405042d51b03102c3c0081e100341d031900d0361801180503040c102400030425142000000040e59130f23810041410f40c0c40d1000f005044450090000103010603c103011608810074001c190903000c3e004944080e10110749090b0040341c01c000000040c0341d140000203154044081030542d00700e908404141602c900b49000100e0b00d20034843c51400074460240d5902054502500001070001e42d03409403035420f0340d40d105001c10354120620003001d9800400404000a5144011041fa9a400310b1254480c06203407001900f1612000740035a0f03a8841664003212030a115139034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 943005611 1250 943004361 943004383
    0x7060513050418170c1e010b0a050102060a1107060e0f1e0705010503061309140709060312081b0d0f05180303040803041506151d06040501050c010e1509 67
    0x30401c40580e100c16280f1829038030000041404004699500c03102c00e00d241500c56036807159094520350080340380c48840400e00e1254920881d400e014420f400c5180c61062401100d206801921175580d0764603d00c0c004080b000701000d0007090900640c40428040d1148030310403030340080105501e007100001280b03482c500b5002d8101d20421554405110303080030549504884003800e2080e100e844a07000150f03803020360a003000e2110320380861101489007007445111441c941c2015a0340c819110419141642da1900018200e12080520000158420802c960f40440103580140c107080031038104007400d42c8080c40350740300d4070b0700d4000d080b141926030b1140750f42211840342c0080c4075060080180ba141d010040004d84000001701c002030900820400c1c40200c20788462003003000a40301c0404400240c0e5554103880010340e4445003040c0384d0000c41084c031a030500203114504091918004480d184d1112125241e99500c0307107101014043c04000040c0b060340804488401440c0601603146480c0b24146 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 943006861 1250 943005611 943005619
    0x1b0b032701060b0f09010201021b0a1515140d0f060c1b020f190e040c1a0307140d14090c030f190303050c09090a050a0e010b0f1009080706051305 64
    0x1002103070000c4007181c80082d03244c04601d07165034402c1c006031300a0180c035110550500d80540b11221006004c50300d41c0501d4442c0c2d401c2004e8113200d103a81e40031501c2034410340c00305580f0001305001d11080380e6880c6441c440001d002c2640320095a03605c480a00507178004888072601d07901c080305243e800000989018094071580c10a41e0600d800123145802100c51040c0074044c0520300c4285a01000e601d400a8440c03000c1d8001030b818649408414484244542032501d07100e84c10400380741080303404581c010794191356102c80701210354600070305660082000d608202d40e00c8203126551400e43c41c40511440c03d0034082d04444e082c00b400d2500b851400c030402800c98000c0e0900100b9018180d407508001c94051a000410b544c0b81c500043c0c00d81705910006600000c01000c115101c501130700410320840d040e190a00c01541c0340d10b11942690003850401c1ea01240c414a0101103081c103000681c071402c7c00345807900c0e50940e6007048038100f0302d160308444006800007400d00000e02c0301219403401002c05071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 943008111 1250 943006861 943006871
    0x90c12050106091b080f13080c0303070e040b0d0b07051b1b01030501150309151107030e090106020d08130c030b07111606051b0706030213090b030a1b0b032701 70
    0x12400602e20714005002c201416207100110f08459003080030400d01c107503c05a0103941c0e030f454501160b13803900100c3c1c03340001a84459100c0e4642040c0c01240c26501014007911124080383d40c410940e210000c010700e041010a101290f115594000403e509611501c082c01c1c54a00b8074506103c0c0403c101c1c0d825042c141440010002400c0099500070b1981035460002021041450b00300c40c000d10908151a026050281c8401501d580720018100e2500ca51129400d1181001c144508140c09200d00d06c0941c00142c0c1c1d807506e0340c1c054500c180c0d020410080007407060519a179843d1088000d50000da4030140d1003c00c100c581030300311034400900c20024000300040040c03003e45a00405180c0a44e80401401258502c08514074861808084450001b51400d003a2513010060094115415441180911110000d103409042c4240d044c80000038020b4940194140c603802c000c40c9504010512400c0240c100086000c1c42c8000b441c054200d04190310740252018a458549600c501c0654111340d06d41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 943009361 1250 943008111 943008161
    0x4020f04180b0603060910180b0f030d05090d14060c030f0a061202060903100501080619061505160804080307210801060f03060801020c03040f210204090c1205010609 73
    0x280007540e85c0068202c0d41030055584100106483c50402e501c03400d80d41c00111401c905c1070385560080d090020040e2600016030070100d04048c5e88210000c04100440d000300004407907070402d03059000d10240940c0d02005441c1c174241000b032404d2412504602c074244007109203c80c0c01c443c10102074001036000307401c0c440c1c41d0406000c140750394032244000340308200009809025460a0040320000c1c440450200059070b501d4401585500c021030b030300203581081402d42500042c09200748025220091207901515044400558050b80041480703c0e500840c1c0340320070005200000104081c1410700040d607150351080c038000a0040c0c04001d40c80d55103203088803584c18a640300c00711038119001860900148040400264014240ca4005c0c0b83c4950001491b80d2075090000004d10403140400030601103d82e90b038803c0741e0291042084c19600c0c200c1500300703101500e0f00e6041440480d0044031190390559036003641c0031041780d0100088440b81d465900801c1118443d11600d2081020921699001501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 943010611 1250 943009361 943009369
    0x705070809040f0b03010f321306021b071d01080a03030b0604050a0303091a09031c1e0309061a030a14010605060c150601051e03090c04020f04180b 65
    0x801e4801070046a0f1502110034802c0c0035000044503060140c0204000c0c648845600c01820045114011102c0301c2c00c2003c85549440841c80354028580407119900d031140d40d09200c050a11642c03e485c619000e101000d0b0318104040280a8080040c0c0108403070780c50b041503482008001101500f040f070b24600100300065000c40c40300c41039949450b00150340700a0b5000a0a60301884d0441a0403100c1080301104060304485600c0076a90101c4c4603407400039a0340303010503191140400740d42d050341040da540900348403100328402075101ca6040494950409454040511401c1d41c2400b0000c0e0b01d0313005071000e000b100d108082400300c4280700c86a980f4481c801080d0b80d05c0d201c1c8001409805100f8515410540030741c00300c0064a40204002e0751060007540290741c1c0c1c40940c2c10400080c2514010401c550302841c104c0d080e4103100100340b100071801080030443d6800003007600c03165000340302f41900c0d903903520b200a10b1482180c80c01e0035101d40c1002e1001110140084024520340e1403e010000703150384d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 943011861 1250 943010611 943010617
    0xc01061e030f030c061a03100c0c0f1502030705180901050102120f0909010305060916060210110909090313050906090609060a41010c15060305030f07060507050708 72
    0x50042c0c40d40c1c42035000c0b440d0841e013000034110050310803460030f000100b107008403050040080700114101c03641c000c00084290b0859000124120200b580d59015000040205242400d81d5000d0b803110541012041c4848060341c0c400c40b40b08001601c0020300503a034905568000101c42d48c288c0700c2542540c1000000b079504c0340d80440c1e107039240a01240c034a0460695508689007940c0140c40700e40c140d6540d00d040c2d580c0d00c1c410742d645c9185004451403c91440c115410680461348654000c00b61401c020362498001d05040c00a000d2100c0100401d110680707400200501a400200c015039075080c00c10b41c2c0c9000c11103980c221921942900d0140b02440d50b0701032100780c21030700c00c0700c41d0005503e407030000075550100c5512000484a40c00c1a10020940b848901c50f0b4910030924044452a811210305121140b80c0c28250301140f124806500403500b000c2880721030032459140003410940740e0b141c00b460358020040e4000288000101300e01009481d00540340c2001540c04c186041992a170340e856140c3c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 943013111 1250 943011861 943011863
    0xd05100501090b0c07050f040e0a080304022d010503060a05122b020a082101090e01050601080412230d0501080708012a0c0f30050703030921050c01061e03 68
    0x5a4038001d1880123640b10361240800e0300c0c050086071180c0145280c04400c81c2c104440907441071001d20750400c05055440d050300d0181121855840402050100540d166003010780f40c1074000302c0c45500820151580003d0001c0112982c00420704481230b040c00743d0340203541e2040d01042c02c901c44070254142790000f800d800000d902190103500c030380003030241c0e040081280d0b403038034032040c4014000203507038406038440851450990b0003444150b44000054814031029a0300800301c41c51607403800c524501c5807986441c10510b81410700025030604001800c80d030088991070150783ea0f00d07801000f00a01c1044440000c121180c000c3c0b2151100c25040a10800703010184124800303c990481d0900e44114200d4200d680d101025040103081d41c01d01c1000b2100710944403d00e21501c01200700410b00060344464602c041c1d5407030318540780303481da01107018045c0c03481d0860b50400381580c503070b07a00302200700009500400ca690b5203403190040e8280509444071a8401044105040c00801485004070428400d403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 943014361 1250 943013111 943013119
    0x50114090312040b0301140301020a050301030b06030a05011b08090106030b06150f0a170601021204090207060b090f0601021b1f05071a06190513090201050d05100501090b0c0705 78
    0x15100c200200b424290b007003001c10001000001d012800ca5403080245060303030f000d403400c2c1041842040c1854200d01c01c803626080404d200f4030040001a84c00140c1f16400714029050b15261b964aaa0301425100700c0d000c0160752007442e2005401c0c0f50b0744116a607034081d4011009002251a42d101c01e000700f64045c203103500801060b00000c0d1984820b00407119030403605da4106a54106c0801c0041c80024216012090941e00c0f0001ca14158070000d181c1c8000401c294003149014508516540254420042200c0e4241c46002480107641c5188038648034102180026101d450184002030401246110740f4814010200d0507104a0301d9428190100e4000180a50444001135005403140d02070f22000a180324101410314140032100c40b50313180039010a69241154aa80010080c82a0b91a0007010b80206600181c1c1202c8189900f11544850040c1817803480d280600261109a960071905d4403e03981c00300008110559002a42e48000e00a040b0903071b00302403002ca10543c0341c40700d80c0f0405103d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 943015611 1250 943014361 943014367
    0xe180601050c03071b03061d0d0e12031206150f16140f0a0b07020c030a061512060b150304120c03020f03071a06030a0302060c07060b1324050114 64
    0x42c91004004892a10390031104201710401c940000000f2403903d0301003250240d00380307000b07151585d00440c41828001c0480f8064858002c00500440d4911302c60801194070145440b01e03403d080300c2c248010404c00080c00c80f015568a0074000340300d4508503003190342c21400c0081010500c440300c50760a8601d00c00d0120200107110300300d418000b0910410003a00c90090007049640c12040030002403900105201d542030600c00e0303649000698540d81c08000701600340d0042103403d00007500c4c1c1c0d4080c03248101c00c1d1900205d080c0c0c8038030180a10010030310044804542e84ca0415006e460f10a0120280104080701c06243d03151903500d4061404091317443d18140070350500008201030007030100000750f404130000c40340c651082e410302040061028009028000b483c07400318081e0f080200701c1030800c1d50903400600642c0c4840c01c002d0001e5002590946581e69200f07081e08a607039500030010a8420f65110221307105084200f030b200e4002c100d0b10303801100d4400382000c00542c2d801c40c1070310300d001d41026412a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 943016861 1250 943015611 943015627
    0x19050c300409050f071110051f060504060305060f0a21081c0e0304060f0503150409030801060e041401050d0203100203160917070b03090a0507090506010e18060105 72
    0x90680034040d569800c0400200740440c001c0095440f1901c1403021414002068403201020303600740440c41d102901c0b41d0043c414074040100c480e00314682041606c07082c0c0341218115541c6403400121070b00104001000050304015a55140c0103041e04144122012080c1e90b0350f00c0006450030000e80728060034040401032000340f803441d031001981c2c800e8001811a0355640c4400003560708140260031720042c90b28080c5a85940780d00001900d0907102282c0b2442840b0007003450644154100a00c9400f9502124000c40320a44079030092311a854400d40750301c0700c15414034134040c041c132950078456805140391800b40c084944110600c0c0741112400e03245070341640014000700c0d08000f100c0d900c000038540000203200b46204860340d00301103882940d44800e00c664035240d011001e410180e64443c140d40c4001810300004103824015600203080030103c41842c02a541c80c50b087c00c41c40e0340089103680da07036070406c501544c014078030300c880c218111240c2021402d00681c220180c00d01806803810801c0c003280c009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 943018111 1250 943016861 943016923
    0x602030f0912011e060f140f3a15020a020a0209091203040c050405014103011d0c0102010c0c0807020a1707080d080f0f04030216090219050c 62
    0x91040c2241402900c1141213003801c00d000d010a8820a0140c156003140001c451101070282c40450350010074044a8110034000c02014100000401c030001401d80341002c0d242c840c0c1c0e001403030a5031114405607030111113410a0b00e010320442d11040780190040040503805580416014040c0381c0c12a100c0620f1b44407150300380c0c03500680c02e00042480c0400020300060200144149084030340446040c44107070303280d48410903901d545043c00b01c0c440c4071282c0c46410074451010620b082c1e0610300ca00310581c03040000000d007501d2036510040118250101040b0340d00c03506000c078180382b0b28280024030400011005c002c028541c916409492008040b580e40b0455444110301da00070f00d014584008640700b01c0030600c2c0c8426061040407810320941e180754010500480c85035114190a0400d004103590b42120051903490081048046000f080e41040700c2922118000d400f80044240058903440329a182070184007110402c4000d00c00c0030700c4691080480062410142e403200648120205409800340b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 943019361 1250 943018111 943018121
    0x60a060b1905130f0f1509031101022e0c0509010f0503060d05011d010c08040b010302061c020d20040803040b070303020c0a0b0a0b0904031b05070302040905060708010602030f091201 80
    0x2840720710703440d0781c0f0014107042c1503902e01c4103413020700c1024034400760380e1a85100350f002000c9900012400035202000071605036602c11903406810b00540b001000a98941101200d01501c44c140e022913a0700d24411409162003040c041d8085410828981600100040c261b403410b0403407241005000000540310f07484640c1440c1041d43c6c400000d21a806544652501030300e440c0a00c204151300c0e002401140381c0c41801020b000795001800c071401d41c0d0940e024401d9075170060981c0340842c00800701d01c54441e4064402801d4a042e0010001160034007403200390003c0c01c0035083e176540c170b64080c00144040d00e1b020044504884002081c20383e11002454103070040d02a004000409001d2101c4190170b0010086085204800d5042c041081050b0304040200c0440f058801800103181c0031000e0814a40000101100901540403101100c0d031300d600050544a0403107084680341c0059051085071500006643c1c054a1a40003940c00d208414114017524090305894510585030b00f0740e0001140402e40c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 943020611 1250 943019361 943019377
    0x51c0219030314070801061b02130b010e0d05010b0a08030309060a18060e010b090a1407030b060d1a150a020a021908010e28051b04060e0403030e060a060b1905 70
    0xf00c801289865100508240ba0900c2100003060103518410600c242d4175500e42c0f042d983c000d1410440c122840c0c100d000401030400c4c85410f02040461464603580c880014003012403041001040840300c02003803225445a03644003c55580c01072007400180d007004030b001540140185000115103001501000080f160300001170074407450003021407040141900042484042074542401d00d484907140e00007211013105030442400040d0b0040389009120707030040c20600b00e0051005c0c0c1042c840d4201002241d0454103c00801c840c20800c0c00c1031410110400304110514140050900820394006521224007400080c42070a280c03480001041517400c40301d026101d01c40080001400444050b0742e1840c8462205018400c1010003400010001151900069010f000f8045442e00c1da00950651414038103055809512403601041401c16101464070460003079070b0200c5d800607103100b49810321001a01c165541400d01000b482448044070441d20b074030b4101c400c1c490b40c0c0b81d40140211001d00030300d14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 943021861 1250 943020611 943020641
    0x10b060a2109080c03130f031a1f0f0905010501030506060301090f14010e0f060306071b0c030803040b0f09060c0f0d0f0c09050315060d080a0c0804060c051c02190303 73
    0x6941c0140fa60010180c0540c6040740200f04001f074855942c580e01070494840100120791500b04039500d000c1c0c2050303040d0020100300c0c0c1c2e55854003003640b040701e0000180d04402ca0701050500100f20b428000e000301401000c0a080800c00c0b8101140071403040e1205009001d1041d0315048400d03d0448950b0100f4406480c241d42c9000a58480005542c03650b400e03584515500e042c02c004c11510f16000c22058000d24160b1182c030b50015801d950040107003400c0f81c0a5502c02d80580b4008049062000110320807803141d440350000d481c0c480040040300d100a03000c41c0300c81c0d000d881004001c107017840840380b50800041045445d5007650311020094000c40a070802e1841c240405110342942014008080da0812070550f2401d08000c0080910f40c6011a14680c0c01103178040c4240100f2422801050b42400070315000803d84807507202c0100c00c2d402607101c3c80009001a9111040c0719007800b01340c54400c1d0040000003e0f0030085402590341e013400e203840989020340c0b1102c0082501039031186d43d810b01c00b0a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 943023111 1250 943021861 943021867
    0xd0206180607080315041b180e04080c101103070c060e0f0105090d0c120c0804030b0c3c0c07030f0803040201080f010f09110c0a060e010b060a210908 66
    0x210303014503d6002030316614400c80207140c1c1c081d00351900d4004c4148050703802c108040c880510000459000071941544030184408110108a20590064140c82075000761007032030780c584082e402145064170001c0c1c601b91640c500380a42c004400d5040440350000c956150840b00c100302e90a000c001000c03200700c5080705204861034000c40e0349064101d03922828070207003070b07034844004518183c03600d41c07070360900400f1a0040504118145e004041c0000030714090825107040686a0b03136406d2034114142c0c1d09002660000ca0b00803829008060406a21403c0c0794100081e05110307945081d10b080c4a840b082e032440004140c20302110401c2120400864001c100c001c1d0300c800e281040c0d05158402d540c01d9000600280002c1c4a070041105200d040301e80040306245031a2800c11503000500d41d48000c0080c4203c100f00d0060020b40812448400034011440058501c40301b40d1100d085903212488640100400e2080318036241c0c21001c415005142c001c0c0d400b01a4110004040052400c2000184904008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 943024361 1250 943023111 943023113
    0x423040b1002011b030209030c120f0a0c1a0414040c050f0403030e04050603030307020a0b06031914011410061409150315010503041e0c030506131505060d0206180607 73
    0x1504981045144c000d050a190001003d0450507482405c10f5190154070080a5102504140502c5045034407140140c0344da4003400740f034490a140b001c00c4280c1d44140c0c4080248501f403c00c41091400f154071503002c038541440c08840c014802145a0203a100c0d9a80301c24000703455000e0011034000c659840e540c10341d03441c0c8910b0068507111180783c880d80100c0c60a000100c1c681030002c1201c1c000d4040760000c1c01c0035100c0343e6450001c82c900619054240c09580e244107041031212540b540c0303291080a01d0842150100c080340e007101c0925800c0300180c041d00c0103101c03054100c1031941d41612605d1800a17542b0040042d82031282c42041e001c00d800460500300045140010000b443c01106100c20000146035484011030f1203001c26600501000403411034201d4940810940c840780d076100b980810501940e035122141004411150281003060282d00501005107034681d80c031401214484c10000c0303040400109100d5814400028051440010610341c1a01800c5001020b450300034001c59541d00d031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 943025611 1250 943024361 943024363
    0x372309190b250906020c06090303041206151511150c0703140c160b040b04050607020d060507110c01031a190902030405010902010e04020304240921140423040b1002 72
    0x41e80c418031005011b1035141c0325180c90104122640c640d0003e0085040c01d0900c0745285082e414810300300d4819580d01031500b012800d9002c00c100500c0f040400200d4002207040140901108003004d800b503400075003809071103e81c100134098010b5407445181d91107040382e16060b40e51909004807002e41c0c2001042114050f003000902030455400c40d81c030700c40103a917100150100c42c001d0f03010720441404140300502507801d1040252a40c5400140300304030002c0b084d204d810031180260340d00d034002031500e00806e240d00003c0001c40c807910b10a29041011062121700b0100d103111540078944904d10348021207191700c9480007070070b01030541d01d04210342e641081d1030964001c00d83c14108a01040c030303044c0070110503d824030070b89100e10341141c00039124200426981007091142d0b0403800006607140c1691002c00c142e42d40c0409a041d0000c401e0840285050000d000d00160341204d00f86040100401d1003011004151140070a0b54406079201c0c00d84820300150203440c1c02003495400c000c3e00b0b1609003410ba8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 943026861 1250 943025611 943025627
    0xa0b0c0601063c140a05090d150e0c0f060408060109020c0a0b1f1a0307030b0402040b1209070b0a0f030207050a14160e372309190b25 59
    0xc0d44c440c0e032001c01200d100d0f14002d00030826a400810020f1001404909080c02d80800c003d101d000c0003146505110724a070704541800362281c403181e000841c80382c00350400d00d0483c800798404607102c0e0b0605181c142003d946560502540070713900d402043c07a5440140800a1405c0f80750700645600c0c5510748003012040c4c500b00e18000e1a01c060000000240d68072290141141150700d241d0700720310310b03a01e50f902500603114140b5031a8116500b00400211034a2000280210141d208900919420070340324044c5070a5503070704007000d041000c00c80f885009070441201c05c0e402026003000b586810003820824140301041c04080c2c51701001e108049105040400c0c070705072804260050104a075154160340356010001c50704d000102e0607000c4411054002600b1035101c00348a42c1c03070201e440c10b43e072000c80c0c103950141c281c5801d81101110080b1036100c0c58441e00794040d41d90b00c010807405000048045402c001d00d03402034100128140492074a00c0c901039551080c006c0c50300341a9401c0841c0000a042d14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 943028111 1250 943026861 943026977
    0x230d0f0f0503071d15031614090616260d05070903030219060b04020f07020a0b070f140c0d11010315050a090c20010204050a0b0c060106 60
    0x9100305400e080103a00860650f40255007640d58003524400d105411104a001008680e50042030214030345d09038500d0000442c0300d002c03101c0c20420b2020703441d2805020054041d94120054070140040801615503a06032141c20f103071003e0800d2520618107024524500490303180f18500002000c030110a0f2102d0001c04c800814280c04220fa5038942c0ba040b501c00030b403400700500680081740490019501170032480540742c080c8900050300e401800000c0c003207900c800031a9018600102c0c0300429458900130a0780100880c030351a030320b441400d954000301014007520060101e41d80c010040e04c403000800c06c404200318082c1004481c0035440c20300445040d11568102c0c0060b003400407160b00c0c450070440c84000c0340c0024064844050900349594007800c0026035802c03c02954040051440c0290021920114400400103a5513401c1c0341c14000c000009811007140588104a0403004010000390281144e0407480c2c464817030604548011500303e81c04195061010048191900e401d4001c0321610040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 943029361 1250 943028111 943028117
    0x3010317031b031311031b13060e09070603061d0601050d09020301022a01060518090a020603160f0825120f0f0e060919080702100f0905010318230d0f 66
    0x21111241c1091340e52514480d800201503040c8107d401c10b030405090019040000020201d00ba0f91228060140100d00321480e2010744d21600b010000c00342c0510402d8054180c80d00000c2c00c14642107410a03203241e003d000c0314100140000c1440301c0ca25168440e002c0c955005000759a581254041d16613903003010704000090700c6c4401206c0c1d084102c1485030008076900500b02c240301000441f80c80400c010002d010303000030b0181c0c800580044e610003004511a1045006240300000600300c0108598404a20342060010240500500ee070910250344100c11120240d14050340800c40101d980c441014444c0100700d06200301c01d13035840c1d4190498240014403050801041c6109080c09039514802d0303607040e5454000c0901c4c807160b41c004504014038a03000b03451030b43c6054030640c081110328a5000700c860008007058520a00181d00c0720540004001c03d180a109048520300807600440b07011100420b000c080543d2000b6121510882c400e030719100006951005c0d01c0c1000140840715a15120000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 943030611 1250 943029361 943029383
    0x51806040f080c2e110a02070e041514090c010f0509060d0f0e07031514010b1e03070e0f01080f011502100e061e0f07080702160807170303010317031b0313 68
    0x45e1201101c03e84100b02d100da80140b1146241500040c3c546601a2007542c5103289511a020820001d019003100b40d50420011041d40c64003001c000d0400c04840074003410000794600a201807503018042d0b481c0c0bd40200c510b196180041c244a90043c00303060740782032032036040c040c0c14100c0000105507441228000d20b021010f5040c070301c40c114219003420345940540c0751110010311862a82d0405400307504851054083c03025081c06400c111908126a0880020049018080181003501000c06000801e0801014608203451040742d500c80500508502c1401c0005a0980b54030800042402e0b10380000100180751548030500c1c0c5034201110030300030604840d00c0500c00500c004081521809481c065004503807141c42003102c0340840a404174003144180c03101d001c00380003c54200030043c4401c5006210300d078981524034004440f00446441503030400d10040000c02c80034841d4250040d80c00318030710781c1c0741e030380903e0f214450300e00e102c0402d07a0304030201c10801d0381c40001810b01051801034070200700e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 943031861 1250 943030611 943030631
    0x312040b16030e0a08070201111f0e010e0a0821010f0f051f1d090a0e1207081614030a020c0406230121020d051806040f080c2e 56
    0x341c070310f01c030519015507003c4520040450107400c0902070840c41450001044a8850411881c080300440c01031000740d00d003081400d042c49039108460749400c44000911241c6405402c080d1100b001450107000000002030b000701011092003044101040b03d1445100c0d941c6a0072001d2822595004034001f1409080c40410300303107041010038200310352903d078103074400540c003400701e9010120003082c81d40f080e603241c00a0708139515036020501c40c1101d440000303201d56120381d1491520b21140300c0078507044003c10254005c100c0c010111000c5c03800510a0001c5503502d0718190036480e0815041c240c4074000440e5a14036260701155440815800722400d02c03169440d41d0410341c1c1224841c414841180380d000051200f9405000e10080240e5a119000d51f0340c0d100030001400e0707a12034a00401000d42d6441004030018060441d228868201001444245026a80c410040c1d419a5010300400342c0407801e820303101c4003040201045040100d00344490151421107030038840c0300e0b00c0c1a82100b402e0a404075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 943033111 1250 943031861 943031867
    0x1e050f060901060f0308130b07061506090614130909150b0102060c040e180708070f0f1415070c0e15040c08160201091b030309090b0609120312040b16 66
    0xc0c095511441c0b084c001c041c0303103603508000d960140e2004d15100e51070400000c0d4810104d809091403d0081c02e01040f4030f203101e031200c035041c0380540100c018491100d030240701481d0700020000500d4001d9500581d01d01101d6134446846d03800d540402041410160300400f00300c00040c540d0320602d01e00109000340000800160f84400007210351754445003090204000368086152800e8001e40460080101c0d51030b212a501e0409034240c100e07207856400b0740d804020072a00fa000840040c0807408440c4580d44c181141450525501d5200b50705c940e03a540c036640303c0306001a04440e8560340c0440c690443e10307600c00581204280c22a501e40203000491082e0101c1c1c00e083c02001741116181d1b40d002443d0342c0b00c003902c03080c0c10058082c0d00210b660303404036540001d01019a24032411202c12141060610f9898010801c03001e58120241141c141203003112642c5542050b03681050301140c50007803011041b002c69184d8060f800c00d4a580c1c0d900c1400784001e01c50b40403410b60180212090403a440c2c40101025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 943034361 1250 943033111 943033121
    0x51029162a03111e0a350c010e06040906090603150507170910060801150506041811120a0603110a03021c0309030b0a05061309050a020405041e050f060901 68
    0x540401c00312108211580b9200b14a0300b4201c807140b00a52401400da001705903050320070341140d100080c0715500140c88444500481c4040f20380c3c4c1e001c02c07088800c40c0b008551036224501d880e80c10300ca4090a0901d803566941c05841c05030008000400500343d6400303903100a000b1a01c13040d034800310614078044040d0f845010381ea22650b8a41c440060340b840c400034a2541600040070a80c0c640950007070b40c1402c1a0714080c4070010029600007203114145409180c0030540f06500651050360100000c002230101304c000300b48403001c0c0b1382000a403a00c048512211a00c151001c01c2520180e510401c640104560711030740075a801769600d0061a803070001842000c11103400040d50068801e00318903400710ba2041d8410105d40310385800955a41d9960b038a040301d41007a0b40340c3d0b80b501d8448040114604017003640b84041c4450b09420f001d4110301382c860b280c6401e420749029000d0740c0c03210001010701c698810340d800e5880340200742c1d44080119003020758450090070030b0008075004080c046002520140a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 943035611 1250 943034361 943034363
    0x160309081006090f230405011107061b021c08070e2d09010521010b0307030302060f0702030a0e100c0203030a201c050706060801140406051029162a03 66
    0x80170b8407100140c410b002c09420002d00441c1e1543d01c0d060500600801c0c1c101414080780304410106070b41c041c0324240000c0400fa20260800c55200141300410031018014841e55074010b42007560b0652222241100c98426084040d81c00c2080081d02080040d8200d84603000c06a0368003118000350582010071200d40801c0c850070f5481804402214203182012980308002e01c030f401d0001402561a00110381400c2d43c1358415809a0401c01c00c100e10001100d000135131080f00c61000e5403412442c0d080142c004904aa0301500403000c81c0b041d081c01c2400348944480041e001801c883d11901d40c4400102601038032031003401d400d429803401000000001443e4045c003002b20314060303800c01c50910211446e4106010507681d59444600000d6040c100781b00f02c0484ac108004509140d1030039007841c0c420740f9000340c01014844030101c010000c00d00000b1024005036002110400164080c5440701118044c80c00020700d4015172200311800c1181c61400c43d500c4450301000c102100b03030960072001000b8003d00c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 943036861 1250 943035611 943035641
    0x1080c09010315020a09090e0c011b020603150d0b012d03020303090607080d09060204030221070509090a08130501020d111f0603140a1104060506160309081006090f 72
    0x281d0f1076800429a0041c104d080c02c1440c1074030141ea5600f08107001c1d01c1041f60344c01b44a1700b2076400c0030b005580c02110501441800d000b18104000c40d40d01150301440b00804084a695003180d080c41e5543d10700390b0181c0016002911001d440d40c403200990729940b882030300040d001c04425481a0010a400340c000c00f01c0b50010041c41c203240174081441119030020b80100d84003841000a400d04040c0b501c11100218068580143c5507819131060094803400584042100700c00000c20f08200c000005081098480c195a180030944a841e00246000c2180d50001c01054021038419a2005120188802c440099084a03140b900c00401079031040365030030f2000800d40110250040640450341080c1000d00d40d01c1c0002101c0359280c80728042d00d00f81251080380d50300142c0c0c15000780201c03164840c08000049404001103403800d000158240f0441c40040c541c40b0782c2d0400c0c0d006050103510704200030f0030948103444c58541c1d406000f81c02840c0da802098451880c1c440ad50304916603030f01c58035500d050082 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 943038111 1250 943036861 943036883
    0xf0501080c030a090c03110f0904020f01030b0f06070506061305040528020a080102120a0216150b090916062c030a0c0f0e0a14060105070c0b04060801080c090103 71
    0x4aa15111940010441d084590b00c443c40c85000914441c5e50800444c00b402180d40800c0781c5400704140500c1a020080c414080300007404003683d59000212031921007400c000a410102ca400b041c51950260388441c3c0c00140810710364140400482d90345e1156408a4010118600480340c0b02e0841e207066401426a60110040d00f2256620509416108008014030160224168005a108034054001c0b1001c3c0e5001b18480e09440c9000342903e4001c003828900b941851840e040fa4210804041b401503c4000245511003404060354003840c0740c000c0113071404101b071a2020b020307641c1d0ba516000b03c0309507032406c03400050340c0362142c40d4442480140b284d070280c0a6082440c81c100910601c4082c03541401a10600070010344804001802401d15007000321082c1c0c90914007203154000205803c03038441c14411850740280400c80030b00c0c4e10003000d0030490386070b144900744100031104540000000e41c000140104130769400c414060304990040003110821990b050501c080e6680a220082c004c003554 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 943039361 1250 943038111 943038121
    0x62a14070b072102030c0a0e04140601140903031201081207021507031e090812030903030c16080d0f06080d0207060305090f060c120105100903240c0908070f050108 72
    0x41d92100c0e446115050300c024020070000842404c0313074820f40d04040f01001c001b5010300d8064000400c0341186030101c07810082c845210303000050200000b02072a040205402c41c554000540c0400d8414140010302107a07140c4503074a103810f0007003100780586101c5101d907041c40c0410303003c007000700c490455001d0b24034900c50402140e15807541c0c101074403c4043c40880d43c2041400c084011030040c15510382e0750394030001d0389000300c940d007410880350581041080800800184c2000042100d41000c2102240340d503400000e00041c401107038040740101400c100003244c60187c481e80c0c001c030360240380b41103042000ca95581002079481a04d4050040036802040040140354025400b40342d10131244002d440c01d80500d4018541040c0d4111003002c0505408181f40d05002040007030309014110a644800c40400701403005400382c111031000030702c0c84c1404142040307100e81c1f40e0440c4c000003402d0403090015103601e40018164113202d0150f201c65200e4210000350720030702081c00104507001a12030021948a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 943040611 1250 943039361 943039367
    0x12030c0303020904090506041e08030c1e030108100f0e1b040609090f050111030106120f020f0301060c050c0a210507030c080d020613030f0c062a14070b07 68
    0x1018016030600d642885001c18a45440c0241c00e0854400c4c400f50030035103404c1c074000890310240b55a440101407201c02c0c0000149905084a40005c0b00c4607215072680c06001542d18072041e4244034403a86040440006106240050b039002c000c0d0020005000150710604c0c05012600c2c2e050301d2044552026001d2040c082481018081c40314000d00701042072900d800001040d144440e0080328100300f0800341e41c0c20f0010a1181c00c40710354203031508510f1741d4075020b0010100c040684004030314030760704c584400e0500100d504681c0d003030501080082d02c079030303686002504106643c04227442d0341c02a6030450f500b5152030340c2d04400303990500b40d00c1c1030110108506a150460454002c0319a03104001020010a1f902e04c002001410380340c004056203121100001d0030a1401b5080d510001320403c516400250003000d654030b000301c245403240250b5410f041c59400341a0030700240450802025150402c07010780703038130b804070300d105900d903181e0b8a4a2010710005a209401707001d444003a060001c1020184 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 943041861 1250 943040611 943040627
    0x6110d052106130c170606040302010207061b0c0b0301170a0206040b09040b0a080115060804050309040e03090a0b0405040c17010b07023c0319060c0203040b160b060a1203 75
    0x14007070201901c0310850f00403502143c1c11310301024081605036007680e012155041509900c81000d0b10740c0380c101071031580080c0d511141801400103002d40c03414100380ca0551b00c9503440d0290f41058140c08984da4502e205c201c990301c00c0c0034a10100081d030340e8400b6020380004102807120f50260460703107024a02400400c0799000704c101e0b580c1c02921081d0700001c0d56582d120080103441064000203451079100c1c14501d0000850344010f00344003440c400c210106101005a681952040e100840c0c0601c180d501d043c02d41c8100c102055000d40340c1000420011800f02c040c1c0140d6206880c1008013030317003100c015201076214005040300c000782c15005200c00307246200034200c0288050b1480c0c41c0d5000c2c3d48021070032120a0b4902c10030201d0b0f2140400107244603103481c40f5280f00190042c2c046490680d06030942c840329403034003902103501c0d04518000c0c14401c2084400a10103004000d85400c406449400b09080d401403da40b80d20600b40810702d146400311008003101d07030000b4290a44042582c2c00c0d03410345 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 943043111 1250 943041861 943041871
    0x14182d0121060801022a19060b18070906030209030c1c150911012f07050d0f05070501020d050412020109211208060307140a09020406110d0521 63
    0x2056107080ca80d4490700742e00034180940281030016865890501242214071100d800d4421482c1c41c48800d81001d140c085144003000c8608145080300400364245207003d0004010919013003484c3c01101900d11814405403030041d00c152380c0f00e024041d5104c104405a0103502449a456000415010058901a450b007591240004000d040009860b200e002c11200c06d44544aa400d8841d440300707040007c080303500f03521503900b400c002c01c0c13a0000740341e6103000181d9481d054810682440c1c45094030300c4100810340060500030b0901e01506807a142c40d4034110b200c940100d52610400002048560002ca628000c10215a8480d030138146000e1214520000e02c0806134144803c240d400f16019103207516250303102c2007141118011442610b8940114034075180c16104101c600400e004d1255000b0071030b48101c588005030601c00c50242e1000031441d521541c410445c00788006400206582c2040d00302c003014000406445100c45a450103444900ca200d001c4295103031442000d40d451107100c00c2d0306401c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 943044361 1250 943043111 943043147
    0x405180a09050f070f0819061d0609010f05010f1a0d0f060308091305073e0c0907020d0c0611220906090204030213090314182d01 57
    0x11000750300d8083c00d0403200b0386000d54981008a051103a081c43c0d000010040c940c03d0018410001c00d0140b0150110b03004900600d95612500314410303089400d074000700080949026500381c1c2c1410300c0130340e001f05818070903000703590705140000400500c504001c41c22140d44100c40c04070048005041c0c4482d9110100043c20f181d61600900c100241d42e00c01c8101662141070221b54a00080c1d0070007440400c090380b5440d2040c208401c00512a034400b01c04140d40c00c2c1e444e003800b00d01302c0b98001c5042c410030f4580101810f0306045542071b00070000007045506008269410043c5448a1074100c1c0c03150f2049103076002099041030080000342081e800302d032200c8075580c145400c2800d4480c20b903196010034001019240d00d03101c020702a9a0584c41048020004039804520b028a0350380464115144203080309591580ca40705142494003c01005440b890301105c003e03074036051886c8503540c8400c140242c50140924801ea200c0c800700c01e0041c07101d0540c40a044800c441001030045544100c0e8490001c15 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 943045611 1250 943044361 943044371
    0x1230a14120c030106030515210c03190606080d08240d05010c030b030a110904020d0c0f140108070c020f0604080a0b01051906050a030f0b090108031902030405180a 72
    0x1560120303840d2501402c0b02d0010b45549500d062402000d5a202401d03801501440042d2110540d513580005020310840305492030380103a810101c142000350701022142c043c00b564003145040f400d50025085e2491088070100142d607101d12090342d0b2402d07100000408a41150040341a240f0349509004410f0704603001400c280c030001003c10a0306904c1c0008864070fa44034820040c0517600350040c4002d0f400240e000301241400c1d5142d5800c108040006203000b0b40c241d802083c01c0d916601c43c905034075034004442800d02356481001d6280110184100e99002180d400c040b10a0b600c1441054041c5413507560384c1c80000c18640030000c10541024056920041c1000002a1040300344004c0c407125010b200c4c204040e6240400b4040030702e8105000a01801c2c080740240040394111041d140801094900003179030300c40c0c182441c0700621050301001d600ca04013100026105200000800a550908410001c510180e00d4188c1e030364051405069800341f00d14004445081c2524626503100b0880c840102c1e03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 943046861 1250 943045611 943045627
    0x3031306090804060807390804050301090f03120218100e0405160914010503180a060216030e040603050606061c020a0e0108070809030406080403030b12010b01230a14 73
    0x40741d5101303a11000104110700304001e0681e801654540c1d100344a414151030b000041c0b001c10300115100f2419140d0500e040e134003142800007000645019103006002000080f0260410b003051800c00a030840c005181c0c03681c80300340c80400303000381c80055a441041c59070320310301e610030003100380100342040d07040050307514000b40c16540340e02650b130080110401280c40c031008143c0003022075034190480204504947c00340700b1240d80c44002c996102841c2002c1c0441040160343c10380c2811302400340546441e0003ca01820f410101c0804682030608c03a072144948101c0e04c0b030038041944c1c890f203c0034240340c100000103580d0b4100301c40180009942d4040010768944411149000c070b8120780c49047c0081da2110050b8a9035800001d1550004003c1c20200c00901d808940c851780c07071040e8000d41d002c00800d0404582018001d070054480d0803001481d02961000c0c07040071900134a4080c031081d000481c1049514541204c0005140803800e210b121546041701c034407003d03a52241c40c3e86404040d58800c0001c12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 943048111 1250 943046861 943046873
    0x2070204180c090c11060c0309150405150f190c090f0f09061d150a0b030f0604180807080714030307050a0201290d0303060b16050114090303130609 65
    0x450500c18401c2d040c1090802409204440c83c2c3c01c080da040c04000e022030580510b001910540c004040c0100903640e5845070700c8107003019018010100356541001c1444204000031030719064580302201d911149644170405010141030541e103140101004009400d10300c1c2c100d03004040454100d0420440e0103540d10742000041250b540691001d0301c454100b071044080b14000c8400034040310079152440010142001000440505400c810108800d6954200d4462503d008000c08028541ca034403864036007064064003404480c100c0c4903c0c0f404e0300501240705854216603420360480040b601f030803903139503c9440c554401c803010b9481030703254441c0f06140c840070802184102c40e10703507615480b10940c01002e4255448130120444404243d802c0d012880b040c5000101550740032a00d802c4d19803607031f04080e03008250540041c02a80300019101c040030561008081c0c0380d83c824002000202c000b07030990042140c06481c8000150400c0002c0b554590005d107114400c940501f40009050690395201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 943049361 1250 943048111 943048151
    0x190201060f0816080c061c06050d0b070306051c24060b0c0106051c0602031801051806060402041505030a020903030d050703140910020a11060c190e03030d02070204 72
    0x2c69010b0f800952010900003101102c0c0c0003d2141c500103005500f4a50300245071405a0164150f0312804160380c0c01c1d481c641a00400b0003014041c00508121800d81041d502c203580c21180103004c079040200015041c1482c40c510ac1c40c8111100207511242041d0381c4902c050112500c090400e180100c0c0e507401402c40c01e1141d0b00083ca580d40310a03590310f01610b0070b142503500a0f8822407144000380e00d80022090b000c010b8941c86076102c1c2e801a40d03692070070100e07050900c1041c140b9416610303120821040380e110040340382d01c02d9031400803152b00e03641d0203081000380d10481c010001001d4800c0b0002c1c0030301d40907401071034101351000409820131440d500480c0ca0341e049801ea000303050b03480c0c0c400d1059040d0144180b000842e030000900800d403401c1c1302100d50b208403202031a1502c590000d40607940700e00c42d40320003607403403005001d0f04d80900303000b140802e0682002a488000354640241425030900542801d80302c1e03a0080d016506200c1c071411a9402500522420380e0895218a12004000b16140c08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 943050611 1250 943049361 943049369
    0x2030d0f0b060d1b090b0909190e030901030f02160210122405040b01020a0215360a0807060e01031d100b01051303020d0c08030304080901020c0a0b190201060f 70
    0x25030201104800c5000c0c101004101305016140409100c46101071045500701142035035020150307103030a10300071390340081d035005044000c0c6030050100c0040c2001c0020240400300360f07018081c1503c02c1d00550f01b02d2003400b09042c0094070721081d42c001420104038200d0441c3e010b05021503010000341840040d04c40500500b403c0c3d40d41d4208040356a50300056281c050142600c2c100100243d0400207075440c5952500a0700c00c0c10301029080441c000502114801120014110403641a0706203518000ca0b0060070340080782c1c0502240302450511584440071a4840f100906845107800740035603402150700441c6c5c1c101a202c01d104240140d020300c0221030801e100000705050a424055030017200d003c131500c14100305080000c0629207500f4088030302620340480b03417581c540345985001214455035901c095401d00010080009200e40400a025200c0c802e07000c0d81c04450740c131003c100d501c03489170241000002d0203000d40d0181c40e170b40d10202c00050700035000010704191030300d0359414110061740c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 943051861 1250 943050611 943050637
    0x13181401030b04050f19170a081506090a030c051c050a1203020d06030b04140111180a0306060803071707080403060c0e0406180608033f010608160f02030d0f0b06 71
    0x6d4881c1002088142c000809600803021404c2c03403004900100804005008440102c480b081c3c250034981d01c00d001c80c0c8103c0c0004100c441b519a580c078103107000408500c17401d0300c00c1181109004444140382000302d6101c2c0e000e0060305c480c4039581c0e600d2079190520500807080580c00d00586810441511502000e10300a01c0c268070703c1c3ca0300740b429020503c0b990110344a280d04246140310016164015036140030242018102034081000c08510700038550f130f102501d51428160002071482c80807000700700c07680c003d00c4100d680408044501d12a48a2028024003001b4100720400215190364001030041c549450010741c060700d2640024240c07000c40d04611402c3d02518000c04c40c1200c0c911414004200e00c1024505024080000049003c90182001403c2e01c03030380044c1d900070034488c22000c100c1d4521880c0008030f584032000244070300703011903105010000d07075020f81e51481e00514003c1403038562035000f585401c6502c2c0c034083c00707054550840c003900d50301d52080c00d402d135503468054604000e0042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 943053111 1250 943051861 943051903
    0x403060213090b1801060c170d0b0306011203090302100e1008011e0f12020a0816060e0f0f01030b0f0d0b04110a060c0305070c080313181401030b04050f 67
    0x2d1948122584045014460001000100d01100c211030101e41180d980f414035640d480c2c4182000190724142c07130005226114009203d12038800c60b0341c804a8040c00540c12140e05030380702d105190301004c010304043c01088054008000616005500300c8254000340f618800100140021030240080346401d0341c0451801030042c40107450030000350480320f017100c116501c100c0c5000404418541180145619540042d000c00190340b04c8000107001004000101e0344c0c0f030540c503186440d4451450184900080450b15604810701d01480c100b5603207840104403c4071580401d005400400101c402075070042c4540d50b140c8c003540d84014400c04040c0c01000e000d941031a0900d0b003448040c0304001d141d44a07107050392081c0005036000850302c25866140c105603568101c2410081b002c4501c5030304c020101c0c400041ca04c1c50401c003075840300c81100c4d440307403240340312030541c00094041d6408400b8550074070159000400100e4081007407150464040c1c0291000d07420031075000b40c03c1181c00942c4422429001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 943054361 1250 943053111 943053119
    0x3060c1e040806010e2d07030b0114071203110c010e0705010512190e0106060c150203070c0b07020c0a03300c0318030203030406050324130509010b121e21030c0403060213 75
    0x502801203032704024a440e03109000049050303221030040400c094040000b01281040081c0681d100005d074080c9118460b803184003c90030309000e403142001540083c040c1c100c00048950083c42611801903882001000c0b91341c0d4866049400390f80304070800d80c0180c0b035564a0703940000038400e00000c0c0100c1e179a500d0300748146090402c10b982d90202400d007498410810000c08590203402d030764034580d22819607105510b803010101d00d82511806034903800342c44030200000f04100c50240c503c40d1100108001202480c0c07111590440c4d48042e0104007103907200b40d803100000d11804840300c0104000c8018030003143c407600424030b50f81094100d180461000018080030118003001c82aa104800d400e00a200000300c02040c0e17009104d5014803212034590020860116003034120075083c00000e00180b22074500c0c10b031201e40d50301801c25401c0104a421101c001c40d208041103c02e10400748200310034048030b80010096043d84001c01d0715005040a00002c070019110340014030707003010600440c100305810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 943055611 1250 943054361 943054367
    0x105090913140106090b10090302150d051918230304030605070801060909061a1b06070815030c0306040215250209130b0c0a050903060c1e040806010e2d07 68
    0x1881c40c44900c280340024180c7c8403a507000b042030b030682e50f050304c0762441101c424516810710b024a81036841c070b00e4142000c220181d60620751200403078039075507400d000000076080c0c1003402d00155440075105802608200003070b21411171101c0503a481020071a031a10355203460b0305046504c2aa0080300090306040104100da6211151310040c10450804001040c80c1010918205540b50611441907401007010810320100145c21a1b4040110060318840d107400b0300010004a4120b468180c002003c1172460100c2c1170015950012000c0a40241100e80704e0360200100d40b22600d043d0202c0900820940c2414803401c01080c9480c01504021001741c10644100b02000000600900f4510000000040401c03103000e0513980100000c0c42c243d544944001d0202c0f920f1060062080d0103200e02d005101c0070144500041c82001da135080d098801804100441055110f248a903c1c45940190700520143c02c0c000c81340bd030404846c0c07081e20f2014081c805420801c0c00340421900320002107908221000d60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 943056861 1250 943055611 943055621
    0x60e06070801080705090606071b03200a0e04081303030c0302010507082203020c04110c010c031107120e15030a060b090307060c1b080318060702010509091314010609 73
    0x41800d1140e0300b5814000f48541d0b0754200e20500744120403400c00f040c113503101c100c215150705400c0450700b40d42e03101400f82e81a1603d03207032004540d131030540c1c5000d0040d8903100f40e41c2c4200744801003141411174031780f02d000030301d0003006032003500c0c11a01000803c044500e07aa450000851003900c0362450003010381806030860344000c0c09101440910710400c2514408059601c40301c030301c1440b030b1084500b04c0b400c049162a6403919141d4105d41f801c00d03100099140c15000e00b40200e9004001d10607451560030407810703074006c00c02e403140401e410301032000095000406402005098a4083c0040400600240c60707103905160103840b112000080c44a02003150003000080c1402c07100881c038181d40c1e04046075a03451544210300802c034040d55480100101c681c9015890a134400c441032901d510348181c0350301d80d441080d1142400c0401d00074000c0c1401d2901c01d032241150145c40d42420090540181b16503c2801010203181d8007055824500103003080781000c0d079030f0a186000280c428104051a000c0390 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 943058111 1250 943056861 943056871
    0x120c0f04150809190b180f16090c0806090c0c030d0207210504090903030b030601080c0909060420031e0c011107080d030c0c0c0b071109090a02011b050109060e06 71
    0x207000740781c0f4200c2e5540d0400c002002d06178009a5100c543c1d46100402e255103510b049042d00c82d003d800031081c0e803a08001000c01d181044610038410340381d910a20001280d101c414604040380300500025038914100120a41c08014094024035040700c000001c1d085501401d80f03081255400325010081c0301d2141c00360341c560004e402410f00c2e01420203001420a0043e4828032100913150202e01040600c2a08240010720300a001c540c103d5031200b542d561141c10140e0164069540440000c0607460005103d0740a160031840650ba2503104020b60b0880c003503c17a04c0a40c144c40344002100c610004180134030083c003040000b501c00508108001803111200106812803503008a409101035880400c003080c038a845420001075812213140c0c241d9000388000800391081e00b140d400058005c0000d0010074101d48034810001e00c802c440d008011603418103981300030050740201c2e1004019406016000307002184514840060385103961190700b903031401c0e142112880c2e00d607000e14000c102c1c1001119008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 943059361 1250 943058111 943058113
    0x130312081302151c060b030901140708040809060405030a0f020906102115030f121e0e06042c061807180e07020c0a0911120c0f04150809 60
    0x6a9464000920f600d0b03d5078031110f10b0b60000100c1c0300c03114000320910107400d200904140700e042d90700d41100c4941d1304122198080c5500b400900d40102050301b1225116811075241e102490302e07aa25039001680218040300d400c10001c000102e0346540801c8514220340c03295051401300382c44c52043c0494120040c0181d4040c68818500340c030340b0f54000080e0b00c85803410200c04841107801101e190013610300d00101e014442d0054101005224154122107646c80c0241d012440030f101c170382400c60390390240c04124102c045142c6002c01c01980b15150740e103680400140000c0c10540c07950704242442060650368030002d414500d580c3e0146040300741217503100d80c0403aa00351021340c44850700c0d4406038004001404100f010081200d16000301441c010180c2030900d108180c9152030200a940c0d5961034050502c96004928000362001942c02100041c1c0c00c104002d03403e19500842da200c0955016080c00c81d070a0050119481c101da140e8050402040d81e8164840709694006010382a1100541078100ca = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 943060611 1250 943059361 943059391
    0x20f06060307090510050607030f111501050d0c0b0d060314060c07151b0905180601051c0e010c05090112050606070b070e0a14120a230313031208 64
    0x3190380109841044808158000c1036650f500c09032820103801c039030010b41d488840802c90388180760f4050b10b000500c1980741c0b941c2d0346c0901001d44c100c0c1d40d5501c40e6201c440d040030100050016040001e021464548110602c13488507445220389411078009400b00c8044075030343c40c01042845000d41c0d001c0c1d1040c110368050551400c00d4402c440f80c0340b06058002e071060740700342c119254441c180e90207201201420941210708825070381004024000c1d070700c41c10344100104c12152005000d40b82099001e04030507150513141015a040c1c03045a20300d042415105185d0f100d04020115500f030080480c0d020080d65103a5440c0840c00000d449880c0d03a50104600d540f0f0641002150303240d140071900040d4000b4610504c642da507040454890682040c02030300000c182400080b40500c040d49480d030b5090031103400f4460303100030b03000b40c2e555803030710f10040c04ac100d41c921039a80890795140c80100c4081690b00b035078a000428840310318900700c568011110100061030404e0496800310480d9040701c899502e0100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 943061861 1250 943060611 943060621
    0xb04211106181005070905120c0102060609090f07153504020d02061201080705012f0a021503060306070302040605030403080a020408010609051f050a1503060b0c0a03020f06 76
    0x40e4691008003110040b15144905030310390a0100800610b1046110060019182031800140640700c548100380c001e200e6501d000c010b424000c5041080d010041e80286a50341e45c1808104c41088040c011f2091406004900a0524000d00c0350b40060b04600f0340075040303004808001410400350341e0740031081450800201e03170710300c4c1d0720800c01414805008508a00f41c0351800002d484109802d0700070341c09100040c0b500405c0f80c1140240303040756544d0082e124103550300c500650310b4100541030744450b060307207200584c07800c420b0303006800c3c0311400b820403654000340b203a011641c42c0c01009030058030203002000b00406840c00300102c80d8414410b00d01581428030300700001c1c01d1342c040903000405011861340000d0300d00201380d059030000c007465002440f4490317036550080010030041d90420003044140c01e4890000b10a0461207044400140c1070201c400e1918a41030485480203083d58101529444000b4014018002401c1081c4041c0003500400f041454061b20300f60000c181d101098100c0c9040007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 943063111 1250 943061861 943061863
    0x10210090213181e030f031a10030b090109020f0702040504060b0433060f0e121605040f06050a060503130b0103060b0102060a09080d0f020708030403020307020a090b09011206090b042111 82
    0x341c0c100655060204d502520310001001da2640c010340e140c1c01030a91903127480301c0c5074103810030581045c094585d8015641c840b550b4406038030480c0070030b20040c0d004004100040c24960300c034941c06130146100007405060f580002d4140c4015420790b081e0706681d41c4a081c0b91440e40c4c00d05e0000021505c0380b030a10f030b43c030b00300c0b000e0301003207070703002d5000601ca00307813415844039202c11560401300c008003016160740d000082c204054549050040c1030203145014241c03000c8550744d20441064409c02004202e0756803601408032055840104503000d00c0300c21010600004031500d480c1d03800307140320780c0c008140b1035060400207290036402040030804605101901b0041803104086070040042c0c040c0105004248bc5181c02c080d11400c140102068800030402c42030540c0400a010180c1c800c490ba4020913545070500b03415245520852507105008000420603007d44562090101740f0801f4003142c4207a0399140d0b541ca9400445003500e1840c5d50740c507022508429259580700441c41ca080504c07418401850207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 943064361 1250 943063111 943063127
    0x3100e070c3f0504080d0e031009031b0507140415030201033c1508070b2802010614010f020a0b060409080f27010210090213181e03 58
    0x100300c1a02101c0c00860b184204041101140441c54603051a102d200c01c1c00074040e6010344603880c05c5000d07100701c0869030786c856a01455242c1008000b0b00140d0b41004001c3d0061039008021000d12034810f4524001800f440c3c0d107200030302c0c01100542086880c0040071424451900007040c03285181100c60040d07121004d4a0701c041c0e03038080c40c0000c1c90f17208620f5003405510040c20304802011070140410a4154801c040c4001090400c5043c0000c846c0c00140024682c9035015803000d98200c004240008440c4e80d000d000c1055000e4000c0444e004141c40418407020340411070801070351503280078009450400b041d1240100e00b80303000741c0320000c90035009440c1c480b0740c48002c040d480c184011555a03541c80d00203001c002d070003888190b5500303a100c0d1800d0303040d4081e070401040c4c6102c151000d08620b80a910840620406070090324866010302124401007888640c12680800051030140e81c541e064428101c03282007203201100130500f603081031b4002e14500c0c0040040d00e400440f00b000002d500007c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 943065611 1250 943064361 943064393
    0x90f010302011b1403120406061205060f15041d1509030703120f140403020c0105030103110f010309051209210309060307030b09192003060616050303100e070c 70
    0x2800c0d8203c1001c2c5000c244034902d4111502c1140300c0420010410607806c204c10f80581d00c140c00c00c00c0185d035141900c0c0c0328a490450007801c0d0b6009140011728500808008a44c4450081040c0640e02d2403c0001400c4500b510300200d20811070380e22404440c8004c11689403040300a0480407041d14184014a982c1c1c03160386001010048036802088540360f0b20341114a502440c50303001d100203024501060044641120103070010700c103c070f10210380c0d0750044c01200d05aa8120810407940c040203000d00800481102605040503a140800c40c00300303c040c010300b861001e10204056480440004003d5907041100410003c0c5c40d0401d20f03000f05100000c1141d45403001501c2150b280e42e40e07030f6000d0340100b400340b0340d0350303000308900c0100450f40052400801c4480c41d0a001080105084201d240c03040b00350810005000b170040001c5038a600c0c201001e420381c504100120b801ca106030380e0740c050454000303441b00310100d020684240051a0f1190260303501c509c1302e01d0403810807070440c4c641410b13624850031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 943066861 1250 943065611 943065647
    0x70201090c05010f0e040204080d0f081317070605010f090b03030f18010504080f030a11150c0913141e0408180f0603090a020909120304022701060e090f01030201 71
    0xc189600070700c00c917148140010000c6440710782c1c9807000d03032300c0c1d0000c42080300005460682d17110070940510000307801080e511644a034111070075a2146498110fa0504d904028020710103100040c201e4042d181c080c0c060301c520800e0742840c4c58000400c0d5110450303102e200c1d03041400b0031542424500155500c1c0007815101001d03d00d9140010380382d42c851504110004e000d030b60000d64602500000500355290203940c1c46412810152030a03840785001002d032490742c4101c034003164142480e00060019100c0c02030a4007207121101041d081100c0c401d44440c01410019020481d179908904003000740301098506075112031030242d80d095814407606030043e00c03035442204a91215241d54468021717040002d891541d4030b080552a06564103280e4000300d1091200c0d0b000a084024081030818500c03004175207890450300c5035400c01444d04428a850240045408c003000c0311055409001802011161030320300403603031450300784a2181d100400e40c012980b5913800420041c3d030f000e051401582ca0b026 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 943068111 1250 943066861 943066877
    0x40503121b030c0105070e01080103110103090203030d0213360f020d0c080612010e190f060501032301020f160c151d090435160b070201090c0501 64
    0x100d010500701c0c54040c0082080c4004145030101400560005000714079a44030412041e602d4801128281d5090000a10302d030404030045600b94000e070049a80f580c8000c003640c0c101350b072065030300301240c008d615900508203050780c0800c10481e010040c0409600300038540c050341a440d0119a60880d12100070601c17040c0d44081e81803500000c0d60540d004090041003d00440e1a0b5060041c1003400a6a83c144101d110590352104c0c4101480383e148610307001805030200000c5804411001e81c0010410b030b40300e40d03444e501280026114400c090185110b1121910320b030b12400e0800450300c002424242a42c0e104000d0907071889081c0382075920050a401c141110408140780000d201400d0754000ea2042e1000d42d03107054615000441540070040341d0f06024403403642201000200c001c192806895505050300355074110380c52100440310ba4520440b40554000b8843c480640307a402400701c51280e481841c0790500308000d80e400d01e41c102031248000c2c890b6101035198400c000105210b0789040c41848 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 943069361 1250 943068111 943068127
    0x905070608090703120503071b111e060f0c0607031503021309060509012003010f0501200a1a1e0c030a1808070302071a040902070606080a03020f0f0304050312 70
    0x1089400d01940e03101d07001c2a01729107804c070050b0003a00195450404141d1240440100301d0002a10a0101e900700301410b4018580800303200040154508001001c403400090856903114400204030544102003d15036410354030030b02600340748018001508060070003c1803004081c2c80c081400980e034040b946201c2d031403600032800b80240030f10280240514281030400040002c10750140e4804940d540080d000c0c041c50410b10b82c030900c424012041c20640318403083c00b0fa54456840707623545600c980380140c41c82000c0c2001e24901404480304a070004034250100680c1d000b885c442c103410007000e4a850340e090070180e101d50303d5404010021848464040000354005816400c1560500c2101184004a441d2402c0203001c0d035005900030360140c032038070b240010020301080312a528203410740d02030760400d4100403a8101940c07117000140c42d11a01c0d548041541103003413003481169880b07900104150902c0c08081400d01b03840180c401c000d43c00c04d1004012649012421200388000e18809581e92008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 943070611 1250 943069361 943069363
    0xc0604080d0e1e06010b04061b02040b090f04110a060e04050406150608091b09010311131a0307061d040b190b070605060a050604030b0907210c09090507060809 70
    0x82500700003440751064000003a901607042003440aa01e2044c1d07941c903a00c61504060502c00e611901e400500c240d402408090460752590b00000e20040001c0f40f201e0454000804400303050340c92071007a05a9505000802582403a00110400e040e00e03102c001350718142c4041c100701e40c0c85000d2401603855000040c100001640141f550021019503400303444e0300c4035802020050100c68a4071a0702c00c26038843c02120080c1e5245000b0480101121042da0869649403d210010442c0310740007805421300c00d10f02801030081d0707400e080210202d6038805201d0401c00d40780c64074692068080c481011f90710740e42d9a13070440d844c0d401c1120503540800e800a03000042960075000d1501c1660390046442c01280c101500002408a58080d2405001a407503810070010081c4551103490741c801030070001040010100a04d1551200119041d1400300d0741d0f800e140381c01c0441c10b5482420402d6108a20820042c089a8000150504c14820400014955280c035560141d60103114184051000001c0c3d0442c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 943071861 1250 943070611 943070621
    0x9030306080303070c140712081318050601170709050f0d0213020304031214070c0312380d06020c10110904061d0c030a02160c08120c0604080d 63
    0x14a800460340c3c2c910300008005c142c4a4100c41c100d5003880301048040d011480000c041007035072507031160404903086656400f9074591142c3c80400381080402c5002942c1d001f28901820091500e21000c1918134051000502842c9041c1701c00142c1c42040b03041c841c0c2c01d81c0c8051a0b2003a03035411346040280803500e600003000c0c0c15002100070340c00140d00000104a40241d00a180180e2094803482c0c280b0403900ca1140030740c0c641601004c0400070400000704494403c100040c5214000d090900101645121201c1030314001001080c3c40003c2180307081a0549046001c0040c01c40400c5141a00c2c100400084901010f45806040f284d0003040d00700307010b001806000b01400d040b10080202003494505900c0c41d80245060510451034400000741020301510481d02c018020703a001c101c036590701c100060f0070740c00203041d80151540c00c0c000a9151002d0201d000b08083c00b8606c3d01d901107284c02d01151621502c506040f0292505005006051100007002504554408030740c5480c2c9010411b140c000309 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 943073111 1250 943071861 943071869
    0x1506031b011412010305250b0307080a060806092b090302040c0207050a0f050411030903030406151706090616172208190206061c020f030a240902100309030306 70
    0x443c62000081000400103a60000416008940301c28204282a040083c40d103441540c4c564281040041c0c1841d104120301d90b80024200e00025009882c6d45078203160800455044042c0e40c0005505201071042010440451404883c0c04600e43c5440c64000c3c419005884028019a20f402c0c00d07141e82402402040094030300989405442991100012034194442c842d0f14052450300c3e91503480403055504480c801d204040040d031075a2610b90302c14000701300d000c1c0b0355042400042c0c40032420f401c281c00007000d65400b40340241294184200c905003007100c0601300048a110085070040313056048a0f0030b44404500300000c24455480038441e08043c03007c41a016000e01c000c202d20010041c0b0301c0094045942101400e0320881c0d924901682e99003000c0d20178903441984080c4140320720344040403a47c002803010704071a0309100301d140403c0c980581c4200403901d0325603588680001060b0000b08004502100505202d50170151f0003080304e80e2010a0307103008058684040205060098001380010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 943074361 1250 943073111 943073137
    0x5090a0e060d140f0c1f0507140619061406070f020a0315020a090801090314180301020a0507210801090b030c030609280201090b030901021b06151512071206081506031b0114 76
    0x151911030031528020301701e000c03a0542f0038900a000320344442145140c509400c00644640d150402a03210407120160202040380d0100c5254004070011380c003041b00e506082d5003141c0160300d8191050025090841ca42c0040d010b682c0750245807070110b80e1002500032441c0c0e807106119525900130000d100c042e1804030059030990300002d0a00786655100008000c098002e035180c41d03102004403410030481086a20311000111380400502c4200e0496005022001000701150f030654001001b0a0400c0000c840e810000d8200d03040d00c00c110104400d10400400301c00c0860b0380d42d15050b60001c0c0502c141400368031a1000e001c800901d04203c01d50440341c2440411889000c200d240307001c41a580c1c6001c5841d5007022404100025071400c200060600244502150a0908030b690b541d030100d15200a000f181003040e80803031521821201c2c803610b405401d60601a00d0705040b421b2402a42c481e028103d07074001d41c8a88a42d034011080300c01100c0081d402482c0221403c807148110b14154000c00442c0c01c59 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 943075611 1250 943074361 943074373
    0x3190c0c080c010f020d0806010513050d080403020a05010207061215030b0f100f030507140303040b030a060906050f0108040308070e100203130605090a0e060d140f0c1f050714 77
    0x11400c800160b90700080e009a9624400380f4020314201d0f15824055800404200c059000c1010380d80200c01801d41002c03050b03400405240d5400000c1d5a900e41a40e003592a00310005040c0700b9410300e000352a0160000b0f000500c81c052902000804100315050840d1074a0b6646801d00e10041041c4c001400a40d080b4100d000300e414040c1310039030811825265608103c0c0354140004068100c48046800c0303d8200300900313600e80c40c1800c515502c1d2020b0308500d92600040102003180301d1400c01540c0558540031000450905141040d4110fa83c03e4010b50720a265810342c042c5a45c0e0301002080d8003a42c1803420504607266a07400ba642c0c0c0003a004040e500c071059400d047c0b40d8503400000761410060801c00d84200b943e407924103964034030806c00300c20703000030032580d06114803103804014582083c8041d110104624858031418070030f00d800501c3c8000394011103240d17444c401c400c002d04c0c84407140454050106120561003002003454200402060003070120301c031401d00c0700c6001340305456001d80301600d50b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 943076861 1250 943075611 943075619
    0xb04020f040606030e06060f03030f18040638070210020106180e07140a151206230108010e180c0303030405160609140622060f110f03190c0c 62
    0x20240103050305d01030f40ca2144100044807440c2450302c4110000b4040c0c00f0703624100e2800b092155941c42620400c000507103c41c051b500e070751030b05e100d844000c000841020003001003240b5107290303000c0c03500e00d0160a242c44d40755100180c4c0400045800055040b1a030400301a89a2070507405404e25600440c41c0300c181510f150345c0284160800c03079503000740d401601c07543c039101c2c900707070b104010f28554441d0044200001070001c4421035041840c280701038102034280400d03000700034003950280d410074442c41c20078034070140880c080d0265518040c542404c01d42c21641c145008415008001008600400d06c0b8000071a4504410310900e8502040602178036070b03a00d002c0c02d045039580064040004030400a45000500d980301d295040203881d000410495080d840104002d540d03048003000e0400c01003c83d482240c00d5001765410002000b0607200c5840c6030f001c03428054600512a801d560098020745528900041c000c001c59000c45820601d0f000d01540709001240cae02810110001e01d00c05180d0710101d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 943078111 1250 943076861 943076867
    0x70f0501030b030c0301150807320a0305060106020109060c030c0c0620031302090105090709091a030f0706020c0315040f0317070314310204150e0a0c030c020304030b04020f040606 79
    0x2509039008c0b03004031805166922603074100c51180806070f4042884000c036903414030000500c44c080c4580b004042c05409500c0c1d454150610318280e0054000d80c0d541c5984608000e582d02400e03a01c45814207040182d80215400640307a0303601240028081e55440b1408600c0c10344440e840d1034441c65541469449240c91038003400042c603800801d0344110250000001c0c1841d00c00c0003d0310500c1141d4400d140366240c0540c0c030016001040b038074400c030641d011003c1c0d506c2d20100311310144400060001d21089250800103410640009011030007600807048900c6903000048002e0341041c0d00002c0c80e89284003905080310313010b030f0000c150310f44c07000400d040c400e00d5581500242511000e11402550684415508000d451300020200f40031440407030700b05514400116003441070600182010031a402101000030441e82d858101040c100205000d000d031b510340307a20841d0013012207070904120800d003140000e035a900861000606201c4d8040004007152240b43e100340d80003901402c10f02410b1384611000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 943079361 1250 943078111 943078151
    0x140708040507211b0b0d0902010c02040e0309040e0708030f0c19050708150f0c07030c05010501260102070803060d0507030602030a061e24050c0d02031209070f0501030b030c0301 78
    0x2076038020b4502c111a5a0013801c1c007840e02c100c0c0e05804c1c5a0b85030410285080010340300c0310305c1c16414840501d142c900982c0f550f00500c080385120401840d9203030049000c01c0304684014111440307035440003000f03002183c00003080f5011600615041500d54040224441c9041c1840c1086207c0595404c01c1900b04200000c41030252003014007a40c0f5082c016840c081e0104508451900b6941c00420102e082c02100c41c1c01132218600030f02d0901201d05854580c0c909544080c4e0104500c0100b20390440291a40b440b0f81010541c4504002d40c541442074489107442e00000d0031242c8624900004002040801c02c5450000c41c0d000c48255180e2502c00000d01c0104a14403c0948541d06034905500e02c0030b07180340140640e4102c0350800c442840c1c0c5030344482c855503060503407010300000f000080c032500c408000414440309a90300541c0d0f03e5000349644054680d0140c00f082032644429018480c0322032642018081c1c0c0e90070f2a002031034071216400689040710303890480f600b5505e0610324010070703180c00100d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 943080611 1250 943079361 943079363
    0x11505130e1e010603140f0705011407020414090c03120706050c2701110c0a090203060406030503030a0506011e0f05090607060e07030606140303040314030f04060201020a02070914070804050721 85
    0x10b542041102c1030203680310482c580b840d047c150458034091100398010510a800040d0038980c13181000f10a0f07000c05c040702d540d0421441e09800560801040401c100400c41060b4401d401400c103e04009410101900030300700300034641621100000ca0b0b400101081c1c0321510020103c10413240f02050740c00000700200d03c0c11900040708080c504200541c002251007202c140a44a11212882c108822000b0341015154542c230544620b00040415810406540625004c810002d85c40c1480f0001600c1c12140c5075170080c000c4001e040c4c0c540500e400684150b510796041c1411a520034a580000d14117100390718009291034071300040c050441e800082c0d10380640f80308a4003088a9901d800d001010a10f00960007a032641c81040140009104101c00e288400d540004890800c5c000d003000c0c0f080358005030058030041c2c4d401300c4c0880e0065030400101000b07200488040052981c282131040e90620700600183c00d21031079002080030000c0810050b00248614245510002401500b10345c5034000060 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 943081861 1250 943080611 943080623
    0x3041a01050a03020907030b150403051b0f030a03030e160e04030930060209100518100e01050a200d09170a02130b0301020f0903011505130e1e010603 66
    0x800455035042929104003500d030010308042d1a980d0351407040300a003041c07500d0ba03504a1003406540d516500840c001c1c00103035100d00040c2a0264480d810900c100280d030b1400c0d0702c280c00302c1c180030b41642ca0100f030f007900181d0980b5002c56140014441186850240f0401d4100c2c240031300000100d8181344000036020f103120390f8030011115614645582410000c070120590500091282d00c5010700c18840c0c03c42152040b00c0240c10098a074000900f01c50031040850041100021061094518401d148540f4401111003002e4402002002000c44d00c180c10518184840012814081c82c02147c2c0d4817500403000255540f4980d400c0700c0d0700e8072030745080702c01e00109074038150103c0c100c2650702c103254006c1c1c01d44004141148007502004945050b507190300325100c0d990720f14202152400e0000303001e846007420f50907a0f41d0180700b050508492140c0c8001e105072001500c01e124a0791356071a6501d60b2402e9a5022500030f07002c442407414a422100d12901c101101c1c0d038049502107042d0441400c80303018907 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 943083111 1250 943081861 943081913
    0x3050f13051c230708030406030212070c032a050706030b13060302181b160c050402070201230c010911120616140d05091609020414090a020f0304 64
    0x495a5981d0202c1c0c5034002c004002c81058a1003c040880b460048090204101ca00c800da07650032850a56029402c41b0340082d030005080b00711030f101c0c02146038000741c0700e26220080c1c41198400400401e956810031050b0a42900c2d0840d00b8050785040604107500b000580d40482d5035008040c004000f0707440c0540c020348001d2150000441c1520034041203940280c55000703d0913220900d110b1081d0028600104605100d403604046e05a0700040c210094023110041c1100840e800c11010104603540154401c03401000b40d200141d0340180c0d05000d00c4411100186e100180310b100034100d01035140001442c0d80307044a18400e10200c811030380e02c01001036410301c6007244000c80c0c107a1144404c843c5100001e85560760000b605116940c2d2031028040e0961590510014440500540ea001d80b01034210381e02c6000e20111100045032848014034410408520703091500e00c1001420f560b603e0410311860805000408050458045510f04825656202da891415160213017a00e4031789192141d030080b0340303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 943084361 1250 943083111 943083139
    0x80c01090528060203090a050703241109120c0d0b06041a090f04080d0606020a1205131e2d060813120c080d0221041e03050f1305 57
    0xc440e00284804080c2e8120750105080d21400069807000e020740c0c2ca80c0c801c183c503980224605011000107140b0035000308410180b01b0b40c182400a40c90140150b001d4071b422240c103003011401040b200758480030364075103054003130144100b4100401044c001d5004100300344106c04001c1c44403011071082c5000c0360204851869180d882d140d0100c8a070380a900003807008040340c4074120034524103a0152180710502d141032030f1241c1c0001955481d82c013500c0541c0c0409413210030810614100341c081070840c9402410f1411003540714a201c2801d1240c00c0b80041820600c1540501a8040c18050016000c10b103040a5410b912400c000c2011180e1008070100f1314000310b016403081100c1400f840c968180140c650310141c0f14840101d410907100803e20112254190000704040e000c1c0403e102c40f203400607140c1444048a03240c1c0410030821000c4881c04404200008440782d0014801035000c0203030754240120740c03400b56510712512040c0003020f840468007a000303042c160112400d4034402d42d031002c062108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 943085611 1250 943084361 943084393
    0xc030c0c1d0109060308041a1c0c08091501050d1a330603192309070603090f0f050f060411040606020303040c0b0d0f050a06080c06130311010c080c010905 68
    0x215020044c10140204401c1240023162000341c802c22003d00080c9162440100e06a440020600c01c80d075051900d4000c0061555002000d85500400c0c1c40e006d000c0c5850044001d03004600c05000e521300c5480d600003040e0500c01c81d4400e01050803440d5240c071081d400c1602010272490b84415404200442060100350960640c001081e005800642414207540751011180840315030145a103608603503907230103078040f0004100c1c1070001000c015004800780c141003035900e0074006141c00c50b10078035007042100400600e18184810721207800a5617000c041c481498040c0c00c000d84030310740380c280d480303144280030034407005507100b15010b4011103041104035614641a45c8030300003200c000d424800c0c100c800300140e02081c0c0041c85401354281000414009442c403000031110b05032031f280510b0307a4901e070500800c4c0b0100000c840e058401c0f21182c0c2090110f010400d05030383c10f408010a102020724000c1540c0e4010402d0640c5680c3c00a01e83e0744401d5103844160080c0302c01c400c190b92034845c02030501c60b03200c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 943086861 1250 943085611 943085621
    0x20c120d090c0b18010c02040905060f010f0f03020a0b1305030f0c03060a270c0f03030503060f0103062103140a0225080d030b03101b0305010803030f01060c030c0c1d0109 75
    0x355484074490014070328010341d6506c0741c0807001d036040754484103018000703001070002e184500d0044000d6021941072100f0036803806e2440d0860000b0410004060003d070b074070f40d14090222080000b4960b55044840d00c0000004007030380c00741c1e4251003030101d0340031100b4000c5510503190100f5022626a59580404141503915051100c0c22065500303030000c021403101c1a102541c1e85c0500c03a10201140d48580c0509001c03290303401500000c201106110092038940c801c451880c400746000c1c005d582c10305420240f1807002000100701d1080030b00407601098011255070b0040400d642e0303040d031110310050019403a1100300071a8490b11a08100059032010415002c1c0d0a07a07901c10000d11303956107620405d500400312200301542c548240b0000d0754a081090203103400c01a498444600001c2403410050107032001a0014203941d0810300c1080164112491142d0440f0920301d00404c00c14800c2c20155011301001e00c01a2420040ba40301040701c80803060303025000c00f042401c1c844107a9940310300c0c0089072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 943088111 1250 943086861 943086877
    0x120f02030405100c2604080c060f03180111040303170f040b01050d03091e231804061806061a130905070207090f090b0a051603020c120d090c0b 63
    0x50140c3c40c242d01c250f200b42011050984650310411400007016515503448100c1c05980d80708180006090084960034020140c043c1020782c0d00b10f0800c80b00004800003800300070031450014812b04144458103500350025900b031120f00e65410ba41c0c41c1c4034240140310100c05107605d0100248440402da4185101e0040d92049401500025950342402d04011601d90251b000350104100e011010807500100b0211040520754221000070907442d00b03265083c1d8040c00492040c41c64041c0909041c141c9070800c0001c0d5026610b010005c0e9980c5a207040380040901d45400354410501d1000f100400c140307a807000c810b560010310300304012001c850407802140b055128004002461045c20025961130303400182c3c01a1060050b06d0319641c49007000c0c02100c5020018900107521042d1440500c1141400c044d00300342a00c500303014906d04508950207000d003220701c54041641c00120800442c40030710405450316250300660ba0b440500341b110b00c000d0b20200c40196041c441e510b00010b216003c03041218101c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 943089361 1250 943088111 943088119
    0x44100317070c03020f030f060112030f110a03030c030f020307170c0f071e020d05030d05060901050105120a0b06072003010c080a0905030d050c1206030304050604050f040612120f02030405 82
    0x8038250b5090040140d40717500c90302d07018410141d80d103c89010500406001e4025000c16500c0ca440a050080603042040c0429040c0508991030740c01c020700110300603038111340609010910010b500d4048008152150500f0141c0e0b1000c0240300d500d40d400047d13038500342c0d01d080c4080942d843c0c14811400ca44680442c4108000b01044008001200380d2000b44071104007000c1c43c1001c1c8020780214804204c07200080303680d6000021384d030f050003429204031030304990142c070003c159604000c0042e240d840341180780d130004d821500c0042c030b1202c40b0f0342040c1030100300a40311f02e03140c64540c506607000e07445052030003000e01e200e00500401420144229401354000740c0d81e00303065031100240c100c01018013404c203480f140070403c4505400d11503400307124000c1c01c2d45004180d882d02003482c00d4010502c0500185d00c80d8004000411003a42c826041d030f815a03000301d030309100c1e81a0400c00070f001084160302079000c09450808d02024420742e201661000d08154031244086440140c0480e140c1c8142d00915030302c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 943090611 1250 943089361 943089383
    0xf030c09030d0f05090108100b040803030405010c031517010e101d0d0504030803150d031d0a0605181c0501021e25060209030f06070f4410031707 64
    0x105c0d6114008150f000403030203c0c04103006885054000b42640540c01c45d0140c1c0d480041440b04000f024820343e5103801ca5480d0401c08054440036200480ca400e2040b201e45843d402c6900d104040300b035219804c1a0001c0b0115214842301c0300306403004d804400c208054500c20389101c504419408901c103c03820305540c3d181441d0505541d00c3c408142c0002d041140600c03c180281c03040d0343c0344c60b040107403000d009440d81d400c040c11070000c0c52444180c5150290040680301c404028181d00502580d8000500b44c0000f14a4503102c404107101805503943c04c00d80740103020741002442410b5004080541c1d20304d002001c0401d13103141c40311039407042d4164295001c03007922130580558501c41c0c400d41041c6c440c40003d0702c2c0c002c1c2d0000007841d041da06644540d40c0d4120009001c01260001c519a03c50f50950800307441d5032640003201140220012445003458141c000c00550501100c081d41c03c0702d07180040f8810040c140000a64140681800120341c006d54010b03a03800e024140c03600b91501d49078400a0160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 943091861 1250 943090611 943090627
    0x100e150f0712021c050306041d0616210501080f031c0b04060b071407090908070b0903160602031b093a15110703090b0901050f030c09030d0f05 63
    0x15001202408a00860052514010b041381e190070421040b05141c0d96030b2078407418408204011100254240b1340c8505090b601e41c0c00001c03011507480d40c00f0409040e403201c065083d60040c0c440d548000610f034445802d40c550680b41c582075a01c00d0341030352401d4044440403441d240002c2e81d64400c00f290030105656400f008211012a03800806007104043e00209005540d441045460b070807850045805442d44a094986404100800703801000b00300c0043c0414551622002954442c84001400048002c0d00250512404108503a081242c445410b5250000c13030501000a42068600c0721030310b0b00710342e140f0400b04207200c242e0f1000d0b00b0083c0020200c404c00c201950500b16041005c140780f864040c400d14443c01e0010312858414000c0c0c0150b02c1300e09844c601001102e042504450114006100300c5004c80da208a084058850400800c0d40e1000c4800060315580a04050800c0c9508000200101d4107087c0300031307104254040d03046401c0401e40103001d0301d103034056407401000034005000e503203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 943093111 1250 943091861 943091873
    0x10c021309031701090912232d03010914161805030f0c03010f05010305030a0c0609080a091d0f0723070b061f080a0504060b100e150f07 60
    0x1d48074900c6410800f55200c00c40a00f1400500d090b8810700d031040e5209000340c01c1c040110341610b01e540702d1b4a0007000ea01d2203540c50000003900740240454907000031402541203021008000303880001c5407801020b0000410030100154400d000345032030350b420310031392120990405d4102c0d8025070604410481d40c000520301101c0811703280d541414614507944000a864500340900300001c1400d1000e4824003424005041c00e50b5400c1640c80c80c1180b41c1401003012440200540d43c03018003510f44080503000c1c6040800161040c3c100241104c4000a429002250094a0700d0111240384481c1c41569000000d85800c0702001c4903104482d0f41c515000900040c81004903000f000f40d4009144420751480481401c20340240c030086030b800c004101403004515294007144440c90740408828043c101e019030003000c40e100a005401101d0312040420b08016030780d0403480020b28043d244200310b0340440ea004020100b1404124054030070304028048042500088a10074210715034543c1c038115080c1d81d88 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 943094361 1250 943093111 943093121
    0x8210f03060d17030916050612040203100e0604110d0b01050405090304091d01050903070302072303010c0f080c0a0c02090a0e070801020d060906181e230105010c0213 73
    0x1d01e0303111078401651400243c8002c1c1084905030801040342d168980408100d1400504806048103261151410007480e921041103030503d0880c802d0f1b01403036441d07510200c2c1c0b80804200300c0c15201403d240740322005000006599104902800404012426a2040c04500c0d0741c104c90152051010304010300090034950041900300c460340b8110b902d8a83d90300d03202c40460348070108500d581d940103424291150780900905800501d1100a0b614040103990069581c0115103d0350740c01d0802641210b5620700000c20100802001400902c28031741e5234400203000da84900e0710280401e8492011542d5009047c00340d0b6078a000545850b0782141080e0200304d40f1090091a00502584030b001290310108180701c10002040d001001680303907400c04a60f03e007070b1000ea410a43d2101d142034070820003407a40c10b040101e000401c800c002468482e400c54500c030f4000c10f4503408403060800304c102003440c0482d1045030112030242020380c0f031031740c03250011981c1d0410144080d51129840d1312039500400340b030b880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 943095611 1250 943094361 943094371
    0x9010b0304200109271a03070e090309100f0f1b0f0203030c0a0308071101020a05030a020d0b0a0f17030304080316090305060f0601120c021902030a02130608210f03 72
    0x1425016900e117070003843e4104c84c42c0910400b51a003203000000c1c070700074010080c250341400030b04011000184c0c0420b607105c140344604c5040c09280b1012643c1100107004a6134403800180c04149612040e80010701541e88030a0b199000601d2518812459840313210300f5030038031500f038058240c403007840d0300c804001c5048640b043e68140003c0181001ea60010046125440d100382c803441d4940c038041101034054100301ca182e641d03d9004001c5e49000c25445800c40c0e601c00d620520050f200c0001c85450001001114007090700040788040224003105400003100c11250720404000d55140c07905c080f2034480c0800d441c0107058400500200d00070000d00f4000040c002c41500d020302c4c00e2942c075210b10749400d5040c3c5401943d2420181402400d5a1221200c00070821500050024400820000b959103040f0508200c50537494410b500031540d090042000c05034008110840c001483e0204000402031071040140a1060303e021000880d050080e01191281d052410b604040e85001103512650000381 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 943096861 1250 943095611 943095617
    0x6090c061e030108070e09010b063f06282112171807030201121d0d0906091505090f040f14150a151403011409010b03042001 55
    0x2508641e4aa240025600801003d001000785a1812250704081080604076040c1641401c207042101d80310403086a05030300b6290343d604526071041020b451000c4d40280b11204421203211800601404c40010302d01030f24040b50b18034007030342e040e508094591040304240070816180f11020440c1010016580000c030140319582d00603101240d6524044521600c10100800c140003880040d0090701c4104590089081100d0361550f98003014403503540c1030912000703040009420910652140f142c0241c0380b1074102c0400110b4544511691903251041444000f0002d100e8050021385e0078071480001701200d0a480c0c0184240410000444684e0300240300c10f50814103100146007161114801c00c5061546080002001c180601038001c814501410300c101c01c40912134204080e590310800311040324120200d40303168803000403041d5070440425035650f000300e0012000080c00501d40c00e09000f5141e00310380411640e03032150020316540c0020341d00078010040d0304900e080032280102c2c18616a0300141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 943098111 1250 943096861 943096897
    0x20f0f010c06270f030905011115061306030c03050609060f1b12070206041a100e27060a06060912150b1309140a05060f2d0411010206090c06 62
    0x10460303490340c0f14145001c6800e0312100003e1001e15900881c8030014000034a0324510b503450008030203640c0d00e080c5c001c1e21440098500803524580e80c2c0c44000c600f40000010620007250741341040c0c0c4229065100c1662140504000640112004100c80d0310032400000704a805480d510007030700101c014492045464201041f102c200d003a050b0340c11b5440b613404c0d58020152032400c1d14100701c0d10342f0f200d000b0038880f283c1481401255008403910f1401d59041c500712401c296502880d811005481c0315040d1412420700d41d4007810340c400850002d100d000040004e003c0c0c0396a64000301d4500b18548030f8007692906480d105800a0350b40c10384142501944e030404128a0303215800100b01c03c49038840385000701e54407400a0100510050303030481900c2000085d10140c03100f6240c1540302c07a401826140800d8106000400d245070b08050005508da10000704040b4040c000c140c0c100116080d102540c40750710340c124505196100250322031240642d0390280a459a0410610010750000e8181e500c40c0c000c03003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 943099361 1250 943098111 943098161
    0xc0305040b18040c020c090106030218060406030605030f06010819030215070f09050f0306060d170a030209040e0109020d150f0908040f08030708030c03150d0f020f0f010c06 76
    0x140007502c1e149450700c280d050a80406400c0008503540604501c003590002d01444030541c0d9584040b1381150721f181005a620080b42000c803190710000651070368000b00205000c00c0455242d8400010344000768100c07520030741d200680b5607440703509100300e644982c4584404040621079044010b81e052090048508442c101540280c030300388115041400504200c100c000000d9201140300c1c0100010f0761248180f0b1100400700307403250001400b10b070050108003042020400045402d00c3c5085000c114075448104040c0010081c0d030100b40c00358422400c00a502506010601c500502c2e80da0050903082c3c0050360faa100d030225000da2680c00100341c1d0b00e550f10655031000b40241b410446c407503100c095a4a0a21003c0c078422007003500320b120300e0761052180a0000d02007004503604540301c1d02e4500c1d2603640e02c0f021041c85161011176240c20019400c82a020000f6400c407180340c462003210351203180400c82e41440503144149440324001048642844081050750348104c95801084002070fa2a4144d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 943100611 1250 943099361 943099379
    0x4051507060516020d1d100c08030c03010603060e07021c031d1606020105070801090f091e061103070f1101061e0815332206050613060c030504 63
    0x20031a40d40f07421001034000010b800364184032400904495007400e0040500c124421a4004481d40c0304e40d001e0700c0042c0011002c1c5020f50005a0b1140d8010040c030741c4c034070341054980500d8000b0b1042c08003007810000013183c02c001c0202c00c0c030703c104540d070300800c000c40031010f540c200141940110003d0640d50140d0300c91b1116400e504c03c0024009100400480c40d24401202c0360b41380b036030b00c49411645031009222800d039121080e181111031000c80407035086903040a2400420003110001c00d4044515080c194150805180f11462030140108000000c501441d0050522046411070006038501a0300100503000d079070722000c50304200c1e0000a445845006560390a40140e0101d000507416100070030126604003c10103552202102e40b4400b400c1c5081d034140160800304081e0354101d014000c00c50005540c80c0c5103482420000d10f481e0a00100c0400600700119001e0109003540c1803010201d40c0782082022a1014212400d82d506418a019400c40311800000421800c0040c10403000402e100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 943101861 1250 943100611 943100621
    0x10507021912030e0402070c0501231207030b010c022103040b07050609062214012c010b0103090b0f07140d020a08181f0618050a0b0a03080405150706 66
    0x60b0490842c074001445060140c00c281680b05142c1c03149004009506c000340c1000060f00442e013080c00c0107840c40610554840e160052a4070110f01c0300d8010501e0110352500d641518000e1002c4e4070304000003501c810045031440d01d8650301a4110001c107402d0441c05010baa10108218001010303241029280d031000f804551040000b520039902070700c00e100d00d20509008403038108100c000409030300d0b18800d041881a46500340e024100000c2c007541c2c661708203802c1d008404500d4440100780c807042c107000003e0200841406000c0d8183d842d00c0b10750320b004c1d4000c4c03042034100c540001c8025000d81d42e0310320150584600401140c2008848441d002c0081180d602400700840842409a140d61070b1600c003c0c1805002040c41c41c1b18155482071186003074000c2202e44910032111551035003164212201d001600c070b6a8004072400c0b024416451241803194846405070085070000d102c0c40c891401040840d143c02c0c04050b040400c20071080006280000164450071480741c9510f0404609413a40c030202c034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 943103111 1250 943101861 943101869
    0x10030218091b1912030e0a1809140a0b0a05070e010c060207021504062705182a0301080601060e01200c130b0901050603100303110c10110c0102011a0105070219 70
    0x148070f2802c440c101a000f5682549185041c0e07001c03c125481d018800421002365900041650365603103c8201b8010442582a0795881200444d04424554640141c1c03001c4120740341c1e0b002e10b28200c04134400c54403a5280c14085101651100e5134131010780c9425000f03601030b100481c3d00101040350164800c2e0060702501c0204407c1c0c981c41c0c100302c103031603005104081c102540c0d0881d0703201e4003041c401030b1394150911841c82260311402d10f55a885088155035074811150010b01d40c150030468030f54031300076180110b041e00c030315009940182c0d036a01010340701d004010a030240030505125840811003c0c2d002d00481c4071688400b10392132800404045000024080555080580c80b44404503040c203140030318500400d020f50382140b461070f1101ea2000880980c4c00001d040000c4207004041c15141004140305c1480e006000a12540001c1300c00f4041940080d89580d107801001d201c80e00960041c0b14000d0401c503062100744812070440f0045400350301000080342e00c044008000c041c91350310084918058 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 943104361 1250 943103111 943103129
    0x32f060406180c0b09040f020c010911120705090406060e240f2101240f060f0804060c0c06110c16120b060310020310030218091b19 58
    0x1604003800c000003922411508900100c40d541e120030005003a43c0c0f00082100c0c0001161511103400500003005840040110b240182c00859808642201980718855592040c0c40800c010280d1809102542050443c041c9003074001410800c9103040c0022503e500c40d1180c1ca00040140d152039508010380010740e449211900d940c3d075114103000c100740b08a42401e0023101c02c075407811560300005081c5808175150401080844000c01c40b001401d4000716100c8c2c50908641d40ca68000e0074120700340b0a07491081e19950001c0b80d1000807840e01944060010009940d580000c0c1e030345503146c08020b4011420040d04200b4207403001000b08100d0310548400e6501c0c3c204499440d401440384500d02190010100700382c00c001e0b4010004010f0082c1100300055026240320100d89d40e28000a0400116000b0780d080a80000100401c400b01e901061050324400c036883c030b4441c080090346c440c0800c0200c0300102c1d0741d40211103600c241952885080b400480003020300390a004401c02001890529500520807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 943105611 1250 943104361 943104373
    0xa050f1608060f070f05070203070b09030d09140603130212100e010605130c0c0b13150c020c090612010212010e010902090a03030f0504030231020c0703032f 69
    0x55030031980300c04401050303040c00a00d11424000b414140b034590150030a400c1c4410900030b806000c0c0640c00780c030704464005080c0c9046980d6824544007641c41802401d100f4000da0f50350447c0c043c060140da9040e100300802c00d010400305041030109503400078005e114240120000074006a4462100141161450028000c408007641c1c44c01c0944400c0040861240d040c20014005511041030f034422a40b20084081800018a02c0594002504100203411000e4000c10131858110074520311a642d40310710224068801d030104d800b002c803481d4402c0400144c0240d0b0a000c442e01c1d0080582e41c00120080643c8081c600541c01349089910084010301c210703034120010480c0c40000d50032a401004041c0d025880c0c0080600004d47c0c00049010040074401070307408000c2d43c244688159805107074040e00400b100c0119420b1414030344d1003034841502d4080181c06101c181c0c0706034000d0710b40760315a502c0280000d605517a41520f00d0f114454014609144000300d64010034442c0004040b050003820140c09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 943106861 1250 943105611 943105633
    0x9030e01031406060901120b0411040303140306060318070b19020f03070c0b0c01020c01142e120201050d0204090c0f0f0801090203060d0c0605270603060d03020a050f 73
    0x5840d08500842402d642a40c00c105660b15100c0844103001d41c00d20b88400b5602c5518640300003064410b40c6282c11500d011110850a94441e00500599001b074503204801580150024102c0c403048420542181003031010451000c10001162020150402507490b81502c1d11a0203a003600406003100d0a0b800c0820001d0b40907806006840040c0400c2001d98a410b42c2910386c085401c03a2031290005407080003070010f12100081d4141c0340b440f07070314200034030000a400d01e00700c1441e00240c5a4036000e200183d240c2104150000155505038290018050100e15180707219400c5034001c0401d82c1400350800080c034001c3c0300c61008001904858600042542d03001300020410b10100e170502d000d000500d04c100c4106034024801e18110745043c9005a035954441c0049155070f0101c0400600c944403444010841c680c00c0b1001d0140140074003d01320b16117810000007200c80c105401d20541156041000c60014100116060301c954020f0044540308242c81d65090314105828090321540e07084482496 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 943108111 1250 943106861 943106867
    0xc0f01050f011701050f07051303080d1521020415030c0b0c0c030303040b0f070507050115061d010e0405130b040b011401050304020916140a020a060b032e0f09030e01 73
    0x90580d40d20f070004c00541c07815590061402101070582c2d4144030703010940b510100c1d04c0722141c4c80a50b0b40809210707103400b094907904001d040c11840e48012950350420100c0c9921f020000d030040b441c1018550a290403c2c1d400b44001408040030b109120710302d2401c01300104071241503d01c024644a070155a40301c4990200d2070400240706007682c0300f130700204103010201e105440c0c850f40007200c00c9442c0075107841ea80000c0d0355070320441500500315424500c861441c07120a081c0141191455146c496141c8582400d04080d00702551909003c980401c0e150103080c10142e001ca0317030111f26941c0c007241c0005941c0351083c00b00f01c112021a20041c501c40140400e281003144036103880c0c02820b1032800c5007001d50016034990b200901d001900b524021401d0405481801060642081c0300c050b60764034521040001d4030307891040b00030364807541403807084d4140e4180002c2101000d407001030321044100c10070104c02c6075201d1100030050b402c0d48580a010700b900c0e041c0b143c454128400d465200092080b00009 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 943109361 1250 943108111 943108139
    0x270504050604090c09050c0d0f020d140108100e1615230702060903010902091003021f09051c05060a0614030c01020607110307050d0504030b16050406050c0f01050f01 73
    0x1d800b590800040100240340904003100f550060100400d4656440340003c01c1800742c900d280b551142020b487c00010480c5030300074984075501c01801e1000043c10a00c086611500f81300389803081d803110220400a00c11a0700241c0349070f00d07040035126400c8094000101d0301144c2d4016041c001583c42e12030703840a400034028100000000c403040c0c600305803c03d00c0344450041c524081d0040000140307440032681c1c2075001c24001039000380340c0e1115040c00502c9078000e01e0350740422801441d4010042d107681c400208480303660072882c0c0c1d4001110b803c0c0401c0c02950a8521030b10843d140d03590110a00050061001c20710071003500100050b00c514010040d4900942c440010f40070341c100d445100d0890340d002c241c0561007403c0342820a15076220f10304040c5584940a400380082c040c0441c001d074801d07030042c0140700f180e0048489074015120030003410180c0d05403010740008030304108410003e09001d80050b181810b0280d041c0c500c82460000b0490941d10121202c800082100c0c1c018814904140c0301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 943110611 1250 943109361 943109371
    0x5061f030b1f050a020613050d120216050c010e030307020a0501030e0f0a110108150901140a0302130516050315131e060306110403080414120316030e1008130327050405 74
    0x18520355000d1f607110b01d9122441d0415400400c440c9440240b56400181c044601c1c1400c50402c0808180560510301e49401308111000e00084ca08603240d8260310b000420f544104d500202a410014500750064004040090409429000c0e030550b00440d420305100d8000707080e0140ca10303200032902d00382c0014084040144520034503041c080941245881c0c3e505841c2c156240e24550214000000c400030300f1514440d400250b20054141505c40e5903210385c0c100e24080d01518016a040c020f0100d001c1d00c1c10301044030100d06000000100244524001804515200c566403001034001c40b11500d14025840103841d082e21541c542e6402c2080151a00c80c0c641d0100d03c0d200003905003800d5581d954601e00c60b600c94100040b4480390341d0320290b520041035111941c4064116561851280010000780804003c15000710f04001820314140c24049802c250140b440d03500c620240d52801100021b11906403803d6081120304034034441020208000c0d0244076000c214081d05003441d2808000c255480100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 943111861 1250 943110611 943110631
    0x8010311090f0a0509030408010629030f040b0403030b0a060201050f06030115050609040e160614070209010605160501110426120d0209040203040c030605061f030b1f050a0206 77
    0x4120119070307841100b0350003100d4000080362544507000c200d0724600075500140c989500c0c1c6040043d5621502d51405042106c0e14141d43d06d4006200c86242180401c4503081d400501c1140090300082c1d42901c03250b0301500c60f050002d040c0c0300740e50204032a0003042e000003026131f56030818020746680b0204400d80c00403045000b8401940c034100c104c100204203103c1d0324003540c1c02145496450366030b5040103e00c03111441c2140c101c0403d4001c41003800c0002c2c40b034000400c0000d80356851208040084500d04c5802502c0088980d03e0314104540c02e9000c900d15503009240e000b84580050350a0182c100941000718213152914208640403091500040c0000c000c1201142510080000414081e080c40040340c24107131505024030051000e48260801c05911520000c10401004840c0c101c1e401070b60b010302e90800403135445070107108160030800440c4170401558807041004600ca82c1140403500400380050440b110f4045001c40712191302912172021400c007040008004c2d1381041441e0740038049007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 943113111 1250 943111861 943111879
    0x1080f0411121203070203120907060f0c020607120207080c06031317040306060e010914060a0b030603032505010c0c080702090705044106090f0307120308010311 71
    0x1e903541c12020302201c0c49030700404404201c1c01c1c0c1c4000612110f400e03100c014400503503c1c41c2400f0001d40303d921001c44444105141e034042004420300040c100b0583c0c0c0140c980f0201c1c2680c01d241541e098206590880c0d105004000d01c600186050390340b10035204e52a0020090a82490901420721082d011802e018600900030411022401203481070340c50342000010135605420501103895109039040a0070706400e01200040005030145400c2c12501c42d07050030460a4000c513646080c49a040d100d40b54840007a8505204034080013004541202000342202d140c210a541c40302e41d000d0300414442e0004000040020501c0001e003d1548400711f50b141c58030003492903a40c5d08203a8000e040002c0c0c003582140001a04081c018400c03500030b05050401c3c884410041c4840e10001c0d0030348903609050b20340200301c0a51a21b070000304e112040b00c0060450782001e69030300501c009800c1c403820b82c9505100302400080d03100101565807030454041d9981030001d40c110704141d0050740642007a98020a095 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 943114361 1250 943113111 943113113
    0x20a0b07150f0b0a12110a03150f0b102a0f0807061d1606020c010207090e03072901050603040b16090503030f04030b060a0506120a140109060501080f04 67
    0x407002109501c00c00940081c0d2004807600d10401000c40b0f007000c90700404010008242e07499111031220800f403040081c940300d6400710040c440030f20000d200040600040d9428200d4000d4160002c0d294a00d102000140034910300c0009803500340c812001c00c0105d40e050011807250704d851051601403840710812a80031661650340c56403054960007020380300c450b0226401c0e0030004582c0110f81040c8115141449010008482588803c02e40781d00c9503e003550b0100c009843e034008a8110f514101c140c0141c80058508114000a059030354424080c0303010411115000401500260500000900d01510855140103c0410282041c0c005510802050041100046c642c43c0203a40c0304051003a901c4119400f1030080c0c1e002e41058000360b906010104002c200b0031b201201420840c0d0245088074402e44442090050804140c095190049020807081180c080b210104640000d04004001035458003a03d003079004070000c0c0c0000c4074054a600d001c001540c0e10090144c0c1141041c0d40314500340c202 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 943115611 1250 943114361 943114373
    0x6020606090705090d2109030b061207080d03020405181b07020d0c17071403120a181211040b01171902030f010503060108120a050d091e020a0b07 64
    0x2004011512608088002500b00c5124100b07503814500050075074a04503020b03250520a005071486000b0f4011035080d12618030520a20000c02203a0300040028042e846e00001c3c0141d18a5031207052140d4420300c880002e4400d8108000d5501040f584c0e001a26141010200700c4030038212070514080e000184107214145440b4000c942c0080b1020603c80d546044034800b04192002081d40903001c18900341c8001140700515041c540000002c5098400e00303901c0c2c6c91061424040210901d0b0994450031019813003030004401058400c46504004c045160030780039100d158810b03604104288401c0791301e1042081080f40315205298000c4a081c040e03046032100081103130302418236041c0e07a040c00e1804214641f2131081c84c01044007080a06540d00c0c83d101e07600146d070039000e215160082c481e000c0001410100400e5201d075500c0e8981c42a8500991b450b001c40d4550081884401d07443d0391103a41d0800151170514a191452180d00c40c001d84803540d004004015032942d004080034141006070600143c0d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 943116861 1250 943115611 943115623
    0x314120307052a162409090b03010219350621010f0504051203013c061e020c0609270f0109061e0603240620070602 51
    0x49509008041600350350fa42208004610507a06024000d5048541450301100b501540c90824281003d001c545409403045804d0010507000203c001d201400b10f100150480400301d0b070010009801c00c0c1002502c4549d01c00280c2c400e0020038004118a800d02002c01c0c9401508185040c00c1039041c601c0f41316031085031350001d141c00d03c40c2c0001e0013507500401c1c0b40071800000a811100030442d60b400440c008008041c2590240d406205421100000c10181402c480c181d03074440c0f902c4560901c1808240200c41e02c42d14014122000980308154110000e070245401001141d407003140001e0039904030320111015201300c030115013080d500f500c0c1a031203000171a0100542600d250030001809a01000c2e1880e680682500c0340d826901030001d54060302c19168140d0340d04407000c1014569404051030341540c441c0c0480c002a0162404000e468042d500c4070250f2180d140080354032000c800350800e0003402a030000e00100b10804e210280e141c424135032014210010300010f241d000e0515002a40c1c2e25 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 943118111 1250 943116861 943116877
    0xc08070e0607030e01050903120c01021312030c02060c0106050301050a02180108010807061d060a05040e100f091a030d180b030f040809030a050d0c1e0f03050a18031412030705 77
    0x2c0001f901d801c0c50301d007003002d401d818091818035511890403885142c046d500c5a4542040714024080c081010310039010110500d0303900d031703c1b0303821b441c40b441c0c1c20310032142c02c28401d1003074a55a4510000381500c080c0182441802548001a0303100f48102c940d82d410f02030021388504100c40070005002c2580c0020303001e400c0d05c1d2203040020301107540f0802c01d841352441d000b81c582c201c4000318000d8801d5421501900950b00c4034603040300e56075100b03000c0c0010404544640f05180c980250b08006502c00b40c0c1c858500320140a0400466466050220f4507203101002458001415000b0742c00c5a880441182030150040ca1442440c600300722151582601020b440500302a20016040d41140c0d010050401416407100c265281c000040c038019098203100340055401c5440b0905841c940f008150044541a81c03040c0b220b0402241ca80742207409400050b11407003480780080d4103500c28240c060410f00194400c5100d201e192607003805103801c0041c2910301e080c94500034800c0c00f140d07e8100051b00c06407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 943119361 1250 943118111 943118117
    0xc09140109141b041a03070908060f1f12030e0a0f050d11010e090a020a0206131a04061d030918060603040b15120615100e0d0804090c08070e0607030e01 67
    0x80204403c1c2105030320031a480700e01800c00116074141c90b4820407010f14810042c0d0344a41e0354080c0c1d01c400362515031004a42c449040c3c003251000070710086510b44e0400030a008400035031400354845801c040030440300c20040d400f2440c2c94507440c01038030700800c0d110050030b52601c4030714820385070001040410340c0e100c00c000d0104c15116840002c0d6440f5040381016130000401d200c00604041e400c1170029444080b855006004032000034660001c84000180e02551100c040a100d22021144c110080f00152048600365161440c1040c115001e480b19245241200041e55444841d0720821003000c18000c03036248900705e50000c1086039964041680d5005412085032411a501d07100b40342c0841205544641c2c0c0515000c20074101c0d56000640648160002d4052200c0100844100000e60326610440d42c0018400b0030480840d0030702c11411a44144184401c81c01c040c0c4500122b420307619031001c0c0340d000840c10030070441d4641d44400000c3c8641c0301598080d241040c2500e00070101c4108400c01c03418 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 943120611 1250 943119361 943119391
    0x6030c12020c030f030103030f030b0a0b071412190905180612010b0301110a020f1203280f090c0b070506060108060303070f0c080d050c06130507030c0914010914 71
    0x148507003c1c001c0340d00c2d480c0034580e110340d2580c40b0b1a01502259103024400c00103403401c081a081c60500796450800e640c8000c0505040980554802e000b50201503088030081c003a03040740500c168513100240800030811403030113280c0d00038070600504a1403107030b1005209012200028800c032000c4004160408000c1d2490381c0700b0617103c004030b0b01420540c1089500f540c03a01c0d1404000c1c48050010f080a0701d40342d801e90725408500c81c6216a94822440c110403030302c0f02000480c0b200358074039045030702d48001d2041400010300d040c0743c01e0007180c03101d541c54400c05803940022420018803110400180c008401c10604000d010703110103550b003400400c014144105c142c0410b2a6079420404e51f80e0981e480012140307484518540244002c005104144462081030b03581c81501d070062040d1052052283c006010ba5564400d00150064035510f00f51031074000c0560100105d0940174540d4050220184041031650411190300941d42d4142c0c4000c4030949403647c0d403140d041607003103400d030015041642d03461 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 943121861 1250 943120611 943120627
    0xf0f0c030f0403031205090a1212090209010305060114090912131e09182018090114070314040201030507140c010905120301120b090a0c120c06030c1202 67
    0x86907104004002070060780100d0004201030b44902c125001c049008000d003c5501c0b80d04a80b0359600032002c0c000c003441030140b01010350500c542c030b0207070304403202e040c4c003095031606500414002c1500781c10030341d11394100f40018090541c11440c6040420801e503a40c0411386080d0344040c0e110f003400c54007040c4d42d032400104141e0803100c50800c4406800402c4980d20000704000c5070003200c15861158030122418061201c03040b40c440c015200003a5041440f0001c148000b510b0740d0304c01d00781110308943c00904212201c1040040c200c0140c1300b10043c6000040300031289548030740101004200d10201410075440883c1404107002c0b01c0d8100e0f50a090200e020349881c1c405480740030b5031240f900103450012440c4801c100b815001208a135000e5016105861104180f00b0035a201c00d0040c1004420250020300c00640c0284d4060f174001b80d8a0b091702e450100b103980d014150030050784031104030f003645241c0c5c905201041c4070000050807242020040040b4502028044020842c10501c400782d011401c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 943123111 1250 943121861 943121863
    0x10c0e030d052206030902040608011815020c010c020f060105030a0f03030b0a05030118150e0a0209070c1a01150201061a1c050f1b04140402030c13060207080d03020f0f0c 75
    0xf03441c2c140341c02e28400c82240c039541c000f0002c140b024800d074401c034241031000942c076006205040001f0301c014449000110f0680300d110300080e40c45c0c6210001c0b9070030404080703400c0c001c0c8504a41b8104a9025001541e0110055454070406810440c400d8002180820015041e898026600383d4542800b107070400044002511048070f680c441d0780c243d42055540410503100c00c0301481803a100d40d2241c08002441c614010488070824260041170f400034245c036005d450301c43c500980c014103d00d40820942490b544040c20700c400d81d043c403031544c0040c0005205018011403215a04052440200181031030710032401013030f1880032201f01c01000001103401e210f5100d800030362922640f102043c002c0b03080024052031583e10803030340300000a41102c0500d1a1a09190131901112540c80c24180c08184845c1000300a50002e0140740314500b0411140d152140c0300d11240d070091606802030010246882d00d454185440c480e2908201441040305251110000040d241700d90300950b01f03982c640d03420749912 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 943124361 1250 943123111 943123147
    0x80307030309240e01060e04020a0504091e0b0612030c0706031a09041103010c09030f0618140606030c0a0608130201033c02270319030e03010c0e030d05 67
    0x20300c46039a0f003601c0040d500b014941148603010220340003041159655014045082c0c001c0e140250f00004400040241e40b5040d040007603603030302481801c10a000800d422549010380300104445583d0000e040040c1d51400c807021004450301c1202852501039280720303042c1c0302c180303038002c80c03051580d120650300311401c4841d00140c60040142411055040c5400e20f04602c04c2c216510a03c25800c2c500704810307103031080d0302407000c59034000a0101c0030b80d0903030b482402500415202d48005070000359800041200042c500520651030f00103400c460900b8800c1c103080c410a05407803401140c5c802410400c80b81d01c540016404890320200418118052004801800b041c4241d100c48610300b038503840009041e850b1100902c160300c1c00b440c20b22000091313880305a0080c041d0406400c0301100d8000100010342207020743c50100142528442000c80a0044d81601c481c0003d400080c0c3c0b00705006c0d800c4c2000d1103940000e003d035051052a184608001036646c580b14008a420004080780558808140002c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 943125611 1250 943124361 943124393
    0x30108210a0c240207030801030606050a0e0c0a050708040b0306030d030e0a02150c0124050117060d020109030c1d01050306100501142b14090d0f140406030b031204080307030309 78
    0x401d664810340e50800807d9040280026510300b450541c0002d010310708078200c4001c072040010848003a80d186d0300c085829410143e0440c0030700078100304170b40014607038a0080011380b1703101c1c100301d85034100031080c9460074017406002818103107440100d0342100b60004040c8140d55046410002032040d2181c000c8407400f0703440a40c2c3e12076007011041d00c245110320f1400300d510080320300d605415580d243c00440b070f0341420b07a040380f0010b00458041000b50a0582003c0c51540c0103050801c1920b6603a07607007000d4540154040c0702c007000141c020507641071300b0800301401084110700401041c1003a4901e90804034043c49560b0611100b028400000c000f03500503104000c041d90320904001440e854041400c6218400302d456681c41e0981c0c014000500b0a40a40195a20f100408100c0c52000c1b06a503e41d0503482c0e40c000340100070768176400302c0740c05000600143c001a43c01003041c114480605180240811070204145408d0100748078030240001a1030350150145000f00c2d24031b210342490040300b420402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 943126861 1250 943125611 943125683
    0xb090f04090503090907180e04081c0501090c0e09010509060d05010f06050f011d06030711010609090c120312020d060504020d05091b180912030108210a0c 68
    0x4941c10910a011000d8036911000744d40031241559211412544030032914101400014103030310502591004030307071841d40144165003451601028901e100c140407900896070074015203a4005100a4009024868200e061402d00b6207840007402c0019042120500490b40110594070001d0000ea480d0010072101540280003000038080ba440340c0d402410b04d034040c40c0d002c1d2068004080c1c20394499000c120060303030060b106605220315401044415400541039030f0420054181c0105021003c0c442d000041041d8940028410480d03e0064041055030b8440c0d40c58044185020300481c0e0449003518104d8a0000c005a5542800784524010305a030780106400503c08111043c00c04e00c19481540280c9101c402c8030140035144404440c0c0d4469803a031150408070042414043c1d003410b16005804c00c000c0c900b541e502c151035880d02421034100342e00c00110b0b50f10100002410751001c00920020a1842804902d06001c0000140c00000700c03042c002e14420b0008001018000c1604802541c60350080b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 943128111 1250 943126861 943126871
    0x409050a111303021509060d0c260f130b010b030406020f0703170604050903070f0510090803180303060d08210a0e0f0c011403040507050a0b0a1808070b090f04 70
    0x1904014030110f00049010710004505000c4041c00c084c265007196500400c0c452400c0503516000d409010201c16039020300504650b0110030740c0e0501d047c1510240104842c05407450310803c4c1404c0603802420503886039891044001c04a2400920700e415507003801c1c001640c03625030b440c000d0001d02c21555040c00c020b41c0403c10408040c0d2115054004818260107650f040d20350384100030403a48159000c2d84c0583c030401089000914200403021007034050010740c0c0e00c0721407810a8106403410200c01702e48401000041190024014003030041c5540b201c1c008505519001001c10f0300451115005002800007040e101c907551006607000441c000e85140c1d061301c6040000240020b400141c055141c8e41c041c846a001c1740e003034002090030350100c0507582e02c10809003404203006070b80e0001d042aa0b07640140600440c0340d441361f1922034002d143d0f40050a50781d03015544010110424407121098401c4c080004102100c070015221b400c0e180d107210344071b0703407013000400080016643c1d03071900707030418204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 943129361 1250 943128111 943128127
    0x30b1305100b094002060316020f0a0317191a040c02012c0a05030c0610090911040f060906080d1b03050313021c0b2a0409050a11 57
    0x30b4000c42c58441041c1e800c00c41d03545820107000114280742e05030540c40c064207100031180e159440c0751030700643c40006009000c000c168001c181a45d2044604e2414845442c201c3c1812503810028440b0100c00900900443e0003250b40003004003040c5561684404407072004100c011304c3d65851030101d014a903404221350004500e080507410041203c19110ba03142074000c0100c20300600402201d00c0c1140152280420401604a52600000c070421f0452040e0b00c00000080c40c200014107805e0070740001440c0b1480c00030070601c2ca919258000591203400e2000c0702d400101403801c3e20785030a0f4102c501152820451003000010161607202245c01420000e0001d0304180c085000150810700c5d545100f900003890b0f00100609888090081c00582e08100003804803d14240c155603442c0700403c0900061031801440415030400c40d42038a40b0740c0c490092080c3d0319070b0701c2000d02501050000d04d07400300310988600320032409107114500c0700c0c5072035000182c1d030074009501044000c00a60744083d140d41d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 943130611 1250 943129361 943129393
    0x90f150d0902120718020307050c0a0b040b0c0c100b040f06170106150503011a0f040b030609010501030c050f03041752060b06030c0a1407020109030b1305 68
    0x10000c0183d0003903100c0c8101c2031032580c01281e002c007a610707901480c4040e14110404a0000c0d03000400ca90200300d0300344480d00c03401400b8804403101c280500c2d0409914142800c1000c403c1001415006107110204603107201c080011803802c00604054000041210144000c00d018102003104000c4080c50918007140510f032681d5024885c1d940c2070020406951605005a202c009080420000c183c003800100903002019243e0440034481210703aa0910062200100e09500284c200700c0103108040100901414840c1041c1e004180900e81130102460000c4098098840c4542c91303104014000b00203428807064408000001c504804190350b2508400e000e400b01d036040714a0a800910030842d28503078000310060740c2c98001200310459680034520307544218a080303004000c907500e41e1100701000d05680c85202540c0300766094401c4581e1005901401041015403c0c943ca403901c90a0010070f02603684800c40d072054a50102d4150030303d0b01d44d800880412101141c0003031451249c00313a03244001c51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 943131861 1250 943130611 943130621
    0x20a0801090903230d1404020916090f0609080d0212032707031a0108010b0f120c030d0e01020c0406030c0e04051207050147010e041508070e0c090f150d 67
    0x140309402003101b50701e4994001014002034034080e500c040400c0204124084141c2a0820036a090812460a95448250170b034200c03125400300c000300e01841000c04c10601c0c1401504d8001c401d61001d41181e0a94a0000c00c850001804d1104138003200b03241a104220108600d480741e64441d401c03140e4450b136a29101c5940c503284140c1040109013040000341d000c1050048424042c4000d2003c100b482800050254403c806400302e4007078443e5112420b900c0c4c500b44082c100fa1070155440111402480c0700191400004d2440d40740030324640740b02000444c2c5045070040595100c002e1410154440c0d00385546000e1010b081c041c110600015240300b00141580040d81c401c62225012515030000d410f40b4401801800141c8528000c2c0003804100c101c1c038850035101d40c4814101101410f29550205040b40c0321172014071031040101405201ca01c40400061000386040b44900040b840c0c081d081001c0740c0540341c0300d0f40c000c4140301007031910f9039140b4007640b403a1040c50740d03040d864012441a0001400d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 943133111 1250 943131861 943131877
    0x70e0301020f0307200c010c15051302120d0504050d020a0806010608010f0b09030c130615120e03040302060f0a020a0b0a0c0f0e01022d03030c03010f0504020a080109090323 76
    0x80020890b24079800031928034004805d070780005414117210401c0151a045440101212920001c4001401120041c0b18242c06601ea070344010101c0d841501c10300031205e07404440b5410b9070b8041c0004032446603104084500341c0e0310640c0c1503c1919014404201402e610750000c0c50316005030000855100d40c4814818100e841c221031a0800030342d5027241032402c5c8104428160035400c00747d039000b91410b0049480c0a0101556000076410303584d152085205881d80303121000140103900c5840c0380c240280036201752480c03400b01440c80d15203140d00007551489243c558a45907580401d440c48800e00a104e201003e50f00f00509404505d01414007200070300105074000046003011580c400305030700c140131180c11800c3c1a0001c0410000d02e4080c05030a40301180e260180d8800300c2030014850308180043d501130400d8450f0240c1b41e504103c50100210030036007005000300c1c030600001348580c0d4400078145c1104e591030f030000781800150404907902c2c0e00358022602007104500304034040c003000e400180049 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 943134361 1250 943133111 943133117
    0x10121b230d02090a05190f0b0414010b0901140903071203020d0c0209150609150406090803091305060d05070308091c020906060c030714160501080915070e0301020f0307 74
    0x3080c868200101c040d80490042e4208a00000050701000258403507500849448036806260380040d100c001640c0078018503150707041e204e9110040c2400c1500501c034030700d0300a6810106560410036040c1140c0181d200150411021461484030300009004441c0746003000f8090350000d5450b0211401080002d4404034014414141030f414824416040441c81075801003110229803106400f10741e05100102203980e2000c42003060003102d58440b181d0b072212081c0038080782d03201d910b03250016014000c9580b003450f554001b000000e0065440b132904c0e8411059003040019180c41c0c05010901c040c041c0c920041c201d2240d1640070090000c0807000e012965801c580c2196440fa084404c0c42c0080405030000b03410105c0c41022441c00c1c9401000391a64809000469040ca0401d848402e404008000c2103000d94212078144209501d00d200a080501030a0034903040ca8146210025030780c4c0005a0801c40701101880850041880380e2a040080080200295141e107008a41131006510680d200e1000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 943135611 1250 943134361 943134419
    0x70c030908010c020c040c0e130f050106080103051002030403031b0314060a1d09150a06180216241a1e0102070605070c0b070302010504060e0610121b 66
    0x4115050140d0490b9404540c042d015244860f070070304c0090000c0d1600782d1f00340445003514011946618aa9248030010007002103007030240c00440700c0c102d54068004604100707014005201081d00008c1c02c01014000d20001039884d513071820110010034683c00c2e0070b04402488500b003404940c1c1504440215200710f01d01d05040d840741c104120550700d0301d1241c0504180f201d110448840101d80f0080d42c09000f500a454050040007480d42507150304907219010a9584c01c024800c142c040d5151811088450108504d0f050f021154202c110340540c070010300605a004104104515270100c100207035415010520075034458980e441544050302d00014000c00615110000101c048102003410400603000780600c242048130031903459003c00c0b010b845401703c4031000240d281241d001004040c0c001d07030001410741414501340c010b07160841d220004a5100000307001d10a0b0591a090703080310684010300b50400c032280f6240311307200140440305801c0030301d107840010a10b050960f04801c2c0c0054143c0b500d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 943136861 1250 943135611 943135619
    0xe04060c030e0a080304150c0504081002030606040e130210020a020127030803130c06030603260d0218060301061110020f0a0c02040e0f010614060408030a0e1206070c0309 75
    0x400c803500180000c0c010f600402254021031070f110003c1d9001806240f2003c9040b030a803050317800ba00c84c0600318a00180e0001170170021a0020f0226001a0b5138a4a06502d5030408500090741030065008600607810b040f400300c0c11030516035452480c0310f0b80c06004c641e000c120000c0c0103902c40620319000c1c3d0100ba01e0b142c1d0030031f2203030403d400f190005040a0b0294000750841e224146035400060084000841881d2000701248040b01224010403250303402160041c21442d0548140030800501d420b030403440003e50a00c81004802d5407008503841d540140c03901450080c1d20840780d2118074460304002c0010020508035489102900c0d003084160031141c0c61176600054104921a50240d0056524180546400300b48190050a4554001000480c4036030141c0d400900700803180c00c10500c90b80d50b038101089400408404280c400f00100e60041c20b080c80c194003c2e84a114081d01001044180010365080360b4810f040c4128410300582180c0042c90308100c05000c2008680090b008500c3d5800f00003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 943138111 1250 943136861 943136867
    0x40e0304210218010e0114060315060c0c0d08180d110405070507060e0c010f05090108060405040c0b13030b24131b0201020415080601170903040506040e04060c 70
    0x1000c88032101030100584074605a240724049054400b02e0340b11807890303100c5a0a80c0102d4926010704000791000e20994940070a07a00e0690580071706500940041c01000188400c40551006418040c0e0b030440e0f544138481042410004404203440d800035480d0000740500c54000043c2c002c41004e45d03a91050744a0220401c41880304072840104000003800800110781051f40005401800c1818514209603156840c4401d0740c0f252a0352030710ba60301c0141ca6408540c0e1042042c2c9184030070f4205140340041f1140004d020410040c401400340f5110400b10301084500d511700ca0050075110819038450f020300c0d8010305c0c40b80c9107220982e0655004800b00c1d10b4031002d0365402e03240d80030207449050b031402201d0a01080344040040c120307455942d0502d00d941c1031030060008154103030b943e00042e6103d040650508481099003002e10400186004115850f600201985c800300d80050800e15242c1c2c43e1406645140f02d43d0b0095504034202090014003000e42e00b02c7d06000d544180e00500062142c44012 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 943139361 1250 943138111 943138117
    0xa060b07080d050c27041b030e0105060f060414062a07090b090420060307020c0111030a1b060e031218061501050f0706060308070b1513020903010b0a0e06040e03 71
    0x1140c036406042c4520380420170f1583c0000130003009440452070540007030941110b802440312002c003094a984018824100c28032641740d0081045804102c0002102d02090ac40d00850107a0f18911505214140291742e440081d110447e10303400589a681e1850304008140c0304100c915500303503100b82400490003c409020300091a200030f00030307002035991511000801c202c0c0c009560a11034081040240c16102d0b0002188904800d400500b1001440800100a0000701c1641e00c4950400d00401d80b0076a44004500700d0ae5120031040c1c00c2041150401c60002c10f0301584038a09844005143c4040c3d082c1521103900c60035544202d64510380074198050b8490100301d80c240024912281d10040541c002e01c050000b0a927214040c3d030038030b401551042c007116003a410a88001c040480c01104004483c03c1d074581c0866800c1142480d0b0075000c012803031000d4500482c00c0d06540200d18402c454030301358052600741c10020103c0008694440303000c05080c030140d500b107010320300700035030b42d142e01c0300000403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 943140611 1250 943139361 943139377
    0xf06010306060807080a170d0f1d1002030f01050910080f070f081b090a0605030604151118060a11031b07090e061807240e04061404050a060b07080d050c 67
    0xc0707281f41c4101062503102ca5400079504000d1140e80f84103400c49401e491142c04030748038600c003046000c0504141c4840ca410419a43c1c1203100b401001003081501803c81c0080c1140d405690248080d2521032110501c141e10b82c001191512a030b881c507882c8040002950411101d07982180d035156600c0b41e030000e80716040b91031019a1103000650142841c18100d0400d903021300d83c00320014141361a0000282404000d603010703544500300d403903078440781081380c410383c8035048483e03845a113081510800d0352038188142d800c1a1158002148400925010b942115800200e90b070950340e849031840c65285001200a04100c01842004008604903010344150000c1544410007060907a48507a8036200118040305110020b0055000001d000c00c481e00f040c40e607142c07007100b10010500c0d003110001d016402d81c4484510450920408000c1c1400036150416005401d540c0854250340c0c2103034440c06016141e2280b50401d5000405606100013080948a020a80c4906102e240c40d18054040c06000c2c41c1e003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 943141861 1250 943140611 943140623
    0x301030503070b0c190207030b010b030603060a0c05070f05160801020307140d0e0d1211030c07140f0d02071805090606060d0603150603020f01020708031b0f06010306060807080a 78
    0x294101048001114950204d0041103082c0703804001e42904582600440c18000540c0c400c0b102403003000025014280500104245c050079440c10200203a80c401e00a4103540700f003965140c040034541e210740b0850711416000700b80c040f8000d04070300e400c0c0c0c2c0c0c541020645600ba011000c4022a21090600842c0c0c01030318640e031070f000d5800d00c40640d2840756200030403501c0340303550319185450000c006008003010501d00303448450000c61031000d11015601414001403081c001001005205801c140503102442d400c40907908820b50010211441c040e040030040c805031040300c0480d40c10030b0307001414500796500c82d650f148483c690404098241e500c1507602c1078503500300d10002101401c0c09005454184401e0308042403150307880c0c0b51480c0915040344500840303504d03a503080c010b60034802188564030600784010041c00d4600011aa168017840d40e80307a02121154108040f0010100b1040f180e903802582910f48950f504e14140d030041c6403904c41d03c3c01c1c80c026002c002841520114901c89000c3c0c000d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 943143111 1250 943141861 943141867
    0x1f0603020414060f0f0618031609200705120a212c1902061b010506010f0e030a0303050901090510020d0605010f1407032a050601120305160c03020627060301030503 72
    0x340b00d42c1940024002a20380500ca460720786041c41101c41100c8005000240ac00500b03103002d034181061038800000308403d00f1504000c40d800041e070006540c140c40a13210121078a07803101c444100c400160b003014009103501060210680505280d0004904400c0081c80320b045000d840c10580030706044a100005a400c4007016402080101410006481c8000e2101340391801a084107503880b04a4181079a00780c3d901c10410015503008010b07800d81010504100241c1000e0750002540da1600000040816840c3c6002c00d20341c0b1425040302c40e40a0707000c815100201450041103000350802c0c7d849101d00c8e418480001825405070380312070342d01010703641c418140e00c0044007112265031028004604103c0b241002c800c1854809000c80120b1100e1000c2a40a1040341009840d00b801038204072a070843c00455100041d80000488001d5100d00110540340c8240e81449a1061201c0d400070b908041d0016040142a6441e02001e5008076602d002080c581e11070720a11000740001d00009006610030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 943144361 1250 943143111 943143127
    0x31b0604211b0f0e240307090603030c2001080408090d060504080309010c08090a030e03010e01020f0c0d020a03120f0b030304060908010f05091f0603020414060f0f06 73
    0x800444440031100001003038040300359a44000d51003031100b040003a0b09051090902a07008000c0c1080020709441c07000d400c26082007910041e43e2884e4080c0c44c2c0810301025040000d64405218a030020a03642c0000c005440c0d590070041c2025916030011078803484010401443c40f154001204c0744040107039519605036545950f0101103a0011031002d50002180412800082841c09110b122b148a0400203499080c0810040c0c02d651303081c10314805018001c0300f0000d58550001e03104c40751603050b14141c0228000400400d005000e040c01051040d4000500000a006000010a000040c44040b0b401c4e21000312422030704d5085034107004001075847c04058469110326000411085444800022070f13059240020349194044d62105022031088001084680b8080c03042a4000340e07100f40c18803c502d44010300b1910303002c4103013205070f161554601403d2564070503840300000d558090003c200e0301c0d11003004109a050115440351285811a5540c00c042c02c042840d000d1000d00640060f0401c496 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 943145611 1250 943144361 943144379
    0x911090a0f06093b030307050703030506010905010f052a0c03190203070902030603030c1c170105090a020a02030f18090a2c0a06090b04060b01020a051218060711031b0604 75
    0x105168050300032404130744c2c0308250308148000c40c0281ca480d11039650300c4059190203003c1d201e00410361814001000e608206a9801849400740d809243c6445951011000c00c04188040b4103111a000c0b1900108200e4507250005000483d0139012030072034071031401c2c450007100b0104890fa0021741540119104111b020955000356404c007800600703403410b1421b04910700385444020350001a450020010b111169904400b40050b50520f46d18151910340c100004503c00c204064081103640e6800171306660414403e0007520320612003d0030755a52051154100024440b000c440c42d8400c00071100813404001e441e22810400c0d90803c4212120b000009100390a807640e4071f055003040d4015840d030040010414420941c03003a1240d0103103003480c1410b040150803540041407443c10b641c0a844100049440000d00100c5e00510142860703590f5220781c120940c46110010310740c0c0001020903010108100e00e06042104134043d801c881d20740f00a80643c101c19607840700183d41010342040306000b4410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 943146861 1250 943145611 943145681
    0x230319300207030905100f0815090f070c020d05071802120406090c0803040b040305060c040605030f04060627050603010b0609040b0303040302061306020c060306130911090a0f0609 79
    0x10003130400110711a501c201090950082011039800034401307074101898180c0040d01c6039049500038100c940f20275510b201090040c20058080e45c2c0401541c00021022071145805051160b030140a10442200ca0b1800b40c0e40d40d070143c01030350000c659002c10340038000854401e5603070420844458015030b0305c86403900700040011103404c0da802001068082210360081005000501141030803a035603629600f01242032200140c5a091040c400b0403003000050340c041c0580c0d4102519501c2e4010b59103503860610000c1c809641b00c0303400ca64010340302d01884141d0907200d48400903020f10a101666800342098200c0d2461002e403640301200b40411000c0303040c2580400030701103010b030480e440c0c1600c94000034652b41200039245001175100c981400460341c140b00c166503082c0306448040c00c40c103195000424603080301c0c10303068141c0d580303020b0101844000308448080c494082c00da61410304040c900c103406440d40018001241d818010001a4074120348149895410818004000c40c4103028070500c2e01d80e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 943148111 1250 943146861 943146863
    0xd0e1212030108030901180e180f061302100906050a0507051515030d0c020f0d0321021e0c250b04090515010c050a230319300207 57
    0x84540d0318040c00e0214414021806011000c00460b11035414600042c01c08046001e01201e8041e034180400108000030340b01ca030001c40c0004a2503503050070582d03944c60b01c910301801c010507203d182d0a0003404202044841181030007900c0001150347d81074403ea03002c0c02e81d4401c4c030300000e05c01c11440381c1083c49030024203045442642600d20b9031100c10051980b070201074600b01d00420b4441e080c0e0341c1d5440d04200d00c3c10a040301c0c0c14400d503e440e0503000074a44442c210030f528060b241c941d18074810184904404503040c074400201d12039610495424000a40001c0c05004401e0103480c080c40080c0c040006503034a8608000040410b4214203c95800114801e003103120380002008000c00d8940200d800b900240080541c00501c1c0c0c07030700000155a420200d840c00c2d040c40306036040704020480c00320380c8100882c0c0200b42c0c090741c241601d0b071341c0c1c003200526000b0a58501020801401c1c10008120302510303c80d0640d555810a605400d00c80c800103001c100701400307a400030034103203510301898010701409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 943149361 1250 943148111 943148113
    0x1020d0810030506040515280c091d01050301060f0803181f08040b0117151918020406050609060706150306020a02010b0909030a2309030f0a05010b01020d0e12 70
    0xa150b403a503e480c940042528120b605420115108000740c054400c6c0e03a5010019419156004600b0402190364840000c1c02c41a00341c3c80b1f44841030810300428481b0010b10741d101040c01c42c104110094034402c0c0c800e0256600c40d50a10700001140151003c0d02d8007950f41d800065407400c540fa001d00c00c01c28001c200003e030411340c240d07141181803554141c402400038079519003139807d2600b4940317550142c2d0160000e140c556140500c020b21075000064010049001215160450b00c86550040700007045082014115040014141c0e10b0141000754020703e51003560240500b98840c810071803076004580345681c100a05000703180c0401c0140e0411443c060401e0031041e078050b1641c84520690744100400300150791680840d40d0075080222615030300003284000b4504005401e5002424a030700e0070311030f2008001c08920360501ca060301c4110380c1c0b0031400070215020401186030302915640c03042d405481070b518203a0f140388194004980021801200d42c4c601e01c08007010300410260b0748202d04000c0a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 943150611 1250 943149361 943149391
    0x60306240703020d0c0314180306330f060f040306050c18180703020901030f0c03060f06050f0405120f0d110d030912110312010f0303031a01020d08 65
    0xa840c0205503804203620000d903a55030751145030501a203000c2ca044542c00421100420f51030103e94807240c030050507010422a580c0c0d07081c0395000c0301d00041101131410f40c5400345a0a001301c445c19450000051440340c0c0c1003102000b042190351140060800c0c056403c5951030b414162149400380081172014040e01180d4201501d0f07481c0e00f03088400440d03907104482c100089400c0b42240342044600540011205074050041c171b40341034dc12100c03001d024032084c5500071a8141003603000340c003c0b03210303488400300070005c54140c0640107010713200504c0f520300900e034104800f042c054411307402c0b1440540d030103180030714252808090000c104100500202e0038001e105034000b140809102002020303545640b03006000c005e14074514103003980c00000300181032810003050300184401c04420030070406400c004050008010310141107210f0b1075250030120750705000100c2c401072310481034825a8000d56040140144100c8117400d502d45542300c45025038005550071000740d1045070b69030703800207054602e00c0d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 943151861 1250 943150611 943150639
    0xf080a06150e100e0c0c1005060409080705030d0c090f051012020d0b01020c01020a020a170a0f0c0801060f0305031905040b040806060415060c080d14090f120f09060306 74
    0xd190000e442002180e0840041044910f0901460310b4120b80b850001d5840c109038010166540c1001c251f00d2010326403140d000584550300d40c0c0c403200c416500842d9246c3d6a508524000c3c1d101d602001c45038010318900702c6407000d0303d44620061015241c4a00210042e981030104012003030040748815810004034145500320310030140060411101c2140d40440e036858250300289c140719041d5003581c1107501402081026990700f400000854a41c603031001c2041d10074400c0039060090442010382511a80524481001070030300c2802e080358004402008115150900030a0f1f8405c9888050001d920a00c43c4014042116400303a04103545800c0051905907900010b0080e0340140c0d010100b5600004200010f509080c090080b810710014800d807010780c10880c1c050305100c940c00d00900003450104151151900aa1080c2410b011408140c1d13007601e01400700540c0c0b554044105140d5019400c0581420303490201503e0106481264036070a26101c8010f0048580004050590200501d94104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 943153111 1250 943151861 943151879
    0x51f1b18180209010e0f1e0307120302061008061b030703150b07061a100f02030918010519030b0114012d080c1c0506040e011a01090f080a0615 63
    0x10071a240c03948030140e201c00041001401c140d08500b03102d80500d00310159841c2c15038608030400007810256810040303845050700401d2602100350000e801c09070702c44152405160300000e19911a0b040420581461500d400741152586415030740301d400100c040074404c0daa0903083d8040d5034043c1042c0781c0015081070305582c10b20152842d500c400010100080d84406101c1ca038010f07291800109440c41519210101c0450568403120a81c0c400b04183c00141c690403d01c24400c8800341a0000d00c1a043c01036003000c0d51440000a03c42da40c031606042c10301065401c03201e00d0306001c41b500a884440c2c41d030718141d01c0c9181d0300e891130342503810000310082404101d98000805244141e00300400c482100410001a140580180044904000c01d0040002080341c0301c1c080030031205000d07000701e1952108008140a441d15008544c419420061003142e0359140030199035010300240d07500b140c65940d403e41141c45035030501903988a50000d010070300118620343c0040283c01c00340b032403000340581d61304000c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 943154361 1250 943153111 943153139
    0x18060d0c0902030a0e010e070b0703120608100b09042102030c03131505040311150427050a0209010e0d03050f031003030917030a110106050d051f1b18 66
    0xc0300c00e42c08000d00c10881000d01c2180c00b076034224802001a40300001400c2c0d69810644110040014009014010148101925584041500c8082c0413540d2a8070003940c450000c00e121003030311454510400d89520b41046441d01464201c0300804140d10704012002c4c460101e201010158031040000d503041600800040c01200386502c50181041e0078810b4042d00c280023004c030002048414002400464140c1c0103440c00b50404a4018524801948000c010750295070700c4050802c01c00c141e40301090704006040116241090001c04c080c0c0d8035025650304a005044104e03000400d55a41c06108ac1400360852031860301178100b1604042101401c1000d035441212080302c41c0b40203200c10010140c00581e483c000d8490001c841c40c403001400a903aa0b60301482ca00078042003101940318502d440f083d1b2040014100140020710141c007107040143e07590740e541d03030701c482c50030b818410341d0402c03490383d100700e50042250401c0140c0b0015008001c85490070074641d00c00d5403260310000041c90381110504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 943155611 1250 943154361 943154369
    0x20417030306040c2f0a12020f121c0b0613031b0602120d1d1c0806030a02010912060e01090308090615030c041505060318060702030918060d0c 63
    0x565507450074400f0701c002e482110000509001108003500034070b50445c400100000070200005070150940380d04130349008400c2101612541d18006e01c0004035501040d41c010400c0c0b10011103500003026556074103280701e024945c20303501100301c41441d10800e00e030304102400d50006140714140440d04008801d05800c40d4801c07640e441518404240741607106100e440140303100d002425002030f01324a44601e40c03144554165146949032000c40825074400360b880d0006405102700e03a80130706070340008010b411584089401086084000503890700d400128400041d506030f548040f000c2c64082720045820407444101d03070081d180c0300318890300702c024460300d180e582c040d0341c030300645050583c2845d04000c03028150707103407000d0862000e4005480000c0d0000035074000b5640050107180c03690341820880815000b080d0702c0f040010501113100000e040850309420364009480c0151101401641e50303101d00c1741c4854201c00d00e0551628088035403100c1c0d031382c40400984041c40c00b44a03580c0f40c0080c07140700c3d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 943156861 1250 943155611 943155613
    0xd0b0a0b0d0204150305040804051002101518020c070306020a05280f0c0c0515042106180309030f060b060706090c0f0501020606240a0c03080a02090121020417 70
    0x5401c028140b001c4c0c580c0d407180700c4203040c10082800e21b9200ca0090303104074041d0500403140808000c52461080007403024072800d6807410030031905c0b5080507400ca008940b00d0000300200003145c08103031007558400c039070041107200005e00289103143c0c5c1d190040e4001d44410402e125052080700c42c40340d881c602c42480004512020141d18030028006092501041030040412000300b80050006800c0c1c0407200644104031000520b2081c200071303440441c481c0d60030220480320034440c2d225950880300c0c03111a0143c46110b00b405010005030400c01c401d0b1a00101600241240208202188007401da0117251401070350041414069107010620b59404900304407000b40d564080902400a2141000007a10314416900790079407078079000039526080034100f0381c0b00c0c029150043d00c518000d14070301081e03415104e8801e6100c0c8115000a041c07415282001e60101d00e04030002600050240f08446030014161039004071103c004504107000e0000b1400346024507420840841d44020380c7c4400400444054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 943158111 1250 943156861 943156867
    0x8100c091d060405010b040506030402010c050c1003050f0106020f0303011e09180c0e1e0c07060e0d0f0302031603020a020a0506130c171c020a080a0504140a050102030d0b0a0b0d02 79
    0x600b48011030b0416070180c141d000c1b06001c20322081c1c0da00012031f600150246040a40da000da030610500700711031161034603400841030300b0240c1400c1d0107030411846880303030480d021002c0c0e99945080e80c4601281541c0005600200010300550210244000c820381014510380740d030719201c42c1001c0490700701d0383c003141c5404110714194040040c8051040b010307054100c2c080209003004000c03184200f148081010700d0a130b0040008400c0700e0074030181d89880d0340111003400480f1500b400c00752540e80c0180500005901824409580c60003030080340c2c050020008928a443c00c1190220002d4004104040c2107000d480c0d00040030810070080c00c3d0017550304111007000650039150240301d860b041e502280104c035601c0403412100c0382c0482e2004200d4038003940400781da039900030124109000317210014006d15002c200104207071b0b0b01c14040d0040c0e90034031015121080c0c8500400c8803e03c414410a030040c0d104010601015032650810301003400050960400c107516501d5106203604440880ea44407036000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 943159361 1250 943158111 943158121
    0xb0c130905010e240f040209060d0e1e071a1201380403030509180705030601030e0c090a0f020d0501091b080c18150c0109050c0a08100c091d 62
    0x11200150860f00c000904107006645142078a8400d9000f44d1081c401c42e4a0300d152400d0351640d0b0100e03500940010b0130303503945800d01040c0d18010561203917058114400c1c041c00e602d03001203401403d40442d5005004104080c5400010440c0341801c0c0c03d01031121400f03000c80008028900030030380c040e00002000b41010100c0024402e502d1609218680200e50940d0085800c00840422241502d826180150780c1d408144041100228010b5090f543d030740a540400c404150f126000c0c60081c4c100340e238140503988030041d400b5030322424001c8183c2e00110400105001d08641d41c403002400100c41300150030500c1403111350301101c000741e201032282d40d19028a1040013140310034801d03c1400078208110141042200c50b03100e800b9042c1800245004040b040740b1035076030340c1d880c1240f0013a4141d20310f58580310141003030302a054a1030125254031900e40c0141607840c041c603c10041c1c0da800f00051010511800002c00549010740c08801170006020f408a010080d03613443c10035066000304084a14100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 943160611 1250 943159361 943159379
    0x907030b09030703120b010509130902210606190f1d07110307060207080f0706290f0409020f1f0906050703090626130209150901030b0c13090501 64
    0x1d15000081c1c004010b01c800003500600f4803415907030200d1000403048240720040e25180704000b00c00b80c0c04003a11004500f04c01d800e400450300d4038030983d0200111465203280400f0000b042041e210203401c20000a8401e040a002c0760303104100d022250046103a80b10381e92003180c80b0036000604210034200d05114010044405d00360090014688112400754030b5080c039442c0c0c0500300e8010100b80d0002404400c1c0103951098a070104401440c156680701545002e000400880040c0d840a03c100748038440484406a020092084040c1603102080f0a10041000905030041c080742e01000c00d189070341d410b4031515001d20301002500e80350441c3d0308040d40090240c5000f80c0c0300d0401c00400b0000740f00007a5000507501c1c03c17100c80c1c0c1088084841000c0000d1041d01c0c40024101d034240d0300c0342c104210040010310b0f0000c21802a500c401a80d00c3c0c02000308005e401c84901d00d034001c90b20385c00400001e04c045241c5580311144410350380c1840c540180c180e240054585c481540540c85d00014820400c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 943161861 1250 943160611 943160633
    0x1406070e04110703030b190b090324071209080307050c101a0f1203030114010915090308210c0a091d0c0a0504091103040201030c0806010c060b03070b0403120f080c091e0603090703 79
    0x54036040bc1c048903050984071200c0c5820081c801c804000c1c10042601c241c441ca500048881c50f40044110340ba894203c400500c41c0e08170910b4050340b8410b14004c80710314801c1d482264940b241c02c15514882c034a5040921260b042d1340c0000d950000e80385260814540302c10b1001c0c60203400440c8480798403401510004103002c2898202c4030580200c14400c20b0150780210f503200c101c170b9211040d41d407a078042c40c03031070424007c83c003c115904884182c10005600c900200030311944403561102d618250700d40c0e0392009170148040b41404280c0000e00840e90740e82a0b0b0004d81050380042c074010303181540b01c60001041d2041644103080d80c82010040c03104541e0180101d20b2300103103030302d03029000342b402c000000d01342c1d8224080030740307042d580c0c000c8cc030b115840074840310000e040300c00d88150340c595807450015245800c8030714040008800706a026002031103202101d0188510390141400e0044007400c0010b2030140111201c1c04050000ca80c00305a1609400b9500c07a0100101801c1d10624500b0038441d650 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 943163111 1250 943161861 943161883
    0xc030605060909101e1d06010b040e13140d0504030506010b0313020f0111120c0d050304030c030305131403072013050c071406070e04110703030b190b0903 68
    0x1c41c2c408020320580005401c0d500008051004503210303001e10300080c02588940c106481041c2001c14056034411480503003148146c1000841d611a1390710500340c00740e80518007501040880d410301045520442400340b40c0164001c02c289400314184400c1c1514100009a0600118602260400c14000b052282074010503040411a02c5c500c0c001404c280000360f035203002803044a1008040e0714507446806815a44200c4c40704413442110903007900811908080042e25440c461844440c03050382c880c2d02504e00865041c0c8a4161562540c0d8064000d000002c03c040710080d1401c0100003c0b074200381840d0800f00501c00510341c1e400c0ca80c1400c6425050440d60100b42c408840415400c6032070b00304500400c3c1c80ca09000040c3c41d2036444126401d0721641c5406849441105903085410310041082e42c024866521001c03520b12000d0240000e07980c0d4507030800d54010081c807405000c81c0c080d801c001f45504005000307a00040c034549030f40000c030b051034200448a1f68082040071403414100610040d0b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 943164361 1250 943163111 943163119
    0x1051e04181503030903020120010c02031b0a03080414120f0a0201153803040303020c1b01120b041b08061003050408190c050d080709060f0e2b0c03060506 68
    0x30b43c02d6890281c6400644d1100074100089540c010000d0156041d000b119060000e00034080041c7c2c0e20002543cbe83c0218400445000d1440d841c0000321100040341406164584c58450055032652100a8044030758080c0000034010001d4007a001840701c0014401c040900d80c01c00c0c0c03114402038009003100d11030000200890b4841c601400b0599004021624281000341310302c07910b1441c141410760006442c400341c00021004001d11040540580107004950306580c1240daa8521142c0000010000000183d011414900c200551700c00103810803080d2035006000801c1840180a00e03ca023b403014141c000003c0c02c81c0f003403103461f01c0c0a5103520401c008c0342c41e0600850405890704045442404800c055050540c0c12501c11907002d001302d850541d4202054845507503640e100601000d04c11901d02e40020f81600d00460428050102003076544907541da1800e0111700041130019660021084e40703014001d841c1c0207194040a414185107080c419408510030303900e145404000d48401070401c92003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 943165467 1106 943164361 943164401
    0x90b0d0b041a0c191b0b10080d020127050c0604240f08041106091003023013061805030c0606010203041401051e0418 52
    0x760701c0c1c0740070000415510000d00e5040c610861501314800110840c034010fa50b4850083c10904403460b041000310724015031203e4200e583c0072200340150030002c03803081c000c105050004200f80031460000b0b201110345911160020394030707500c0f491701d4100462242c1d014810100710000c840c4402402031507070341e40c588070440194000140e0821a501d900840c101d5400e20454519003101d400da603802c051030f01c0d9540c44802c0300c045a0440c85e8881d40c14403046010ba510003150103082031171920016981d4451280e00c45004250580705d0954003a02f1140040126015000580c4006182c44581e100d490600d4150700031b00a000c400340c590031083c0110740401100000511844131283d080b55003e507105001260f5a1242e80030300034600c0c1d603020802d5840e50048001d032205031403180560100301040c0d80320717500980080d8011007040d500803002c2e00c400c105030722400040804d440c442e41030b = true := by decide +kernel

theorem cover : BRFrame.Cov 942985611 943165467 := by
  have h0 := BRFrame.cov_init 942985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 942985611 ≤ n) (h2 : n < 943165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
