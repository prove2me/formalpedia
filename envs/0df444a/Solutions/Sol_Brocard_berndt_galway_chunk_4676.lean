-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4676
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:22:57.634237+00:00
-- url     : https://prove2.me/submissions/4eb4d198-1d18-45aa-b5f1-974a63e6d78a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 840827338 ≤ n < 841007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 840828588 1250 840827338 840827347
    0x2060d09210503072706110d020705061b100f02030106030b060f040302150c0a200f0d0b070507051203160c0b0403140403080a08010906060302041208131a031504050705 74
    0x10444454043c0704103000104080e01d80c00070100391034003a09014121940d1106e10304041f20780c44525107110500c0c8002990084030040c4000d03101c03074040b0381c1d4441010a01c10b8500081c0045c00d07181440207501c144d02c0501d010440820081c803034000354121800e9990a10243c45203604100282c46011040b40c0550410402000103081c4034660141c00b00e280c0344101d09000e0034045180c140160600b0499203a40c203d5400f603580d4111a94070204580305541c11035094071310300b000c240c4904100402802e0b200c541c0d0005661944a00216070120341e00c001544d420046940303080882c0c1d042500c044500d400e51440e030700d0f24940316503030103207903941c01480008554503961425144a41400170006031601c003000b0100100382c200001f021806a103540e142036941c034050b0300b003003280c0f9990822420940100f00c20408138204491104a080e04004000d640c1c4010680d5480344815680c000d84204007154001d00d444552100550700c906448164003030040340520802c000c1707a03401c83c0c1441c0440c400f0701 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 840829838 1250 840828588 840828601
    0xb0105090f09040302030f0c0a2d03030e0705130608011a0303030708130b1509160f0518100210060b0a090e0702012715150506130302060d09210503 65
    0x4005803c07500a00649241c0f86c0f02400c0b0b81c1c456402560200601e80c00303da001d82c2001709078407001c1e9104040040060f40c4c81700c2003ca010a050b04940050704054541d011506011814002580180380041010852100d4a01d095010382894454044594a40440d00441d1036001e40702c0c4003030610090255245558408007030b252198040c0503a1501c3c2103001100001030b4600a0040c0900f92214a4110f80c00390700d0704000c0c0c284802401c3c0106003800c10180d120720780d006444107484002500f81903807116100070405004540f916455940600200c42e8400419004502c0c42030700d030030240090210316212040090b442c411613540500103002c040f01084400d05114506400c6041740c400499541d50f0030458042c8003880303c0032002c03210b051405070f0013003000c0e40c4a10301c1200000070041c804000c6002000c401e007000c520465005503c0058082d00403117180c0c09010146600034030040d103803040e115100b40141031801d0f08564102c0da69079403081c0081c010242c40c030f403800703240e5950b80346580c2d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 840831088 1250 840829838 840829849
    0x40c030803040609082a011a0d03120222090e03040902030406020c0a050d020f07150e120f01230f06060c03040806010b071209081c051216030b0105090f 67
    0x1030055480f20b640b0f04108000a0081000b40a000105210649100c1070800f126411215249131800300e680b601c00ca48460b0950000007003800282140c00c1340c800809401c090b03800e450201d140c43c0b60b4610000352401031003042103021034050601d102c04040d090302c2d19a44400c0321314504001a007a44180010404580c10ba001158040d01c1740038094103101c80c0390010b501d00080e15904a450b90401100c10f5881641001849449850b1000030301c8581d01e0080e41080112070400458100800c1c00082c40164440070341803240314041d0001c071250550740405182c0240a40d003048079a00c80c2c10000c078032002800c00441e9004222544480d00745032035401c01c00070141e00944028400780410700000550b80e0051004500a100301071105554034550316003100070719050010074041c01340c002000d1105145c006016150103500d507144401c071400c401d405490a00406512806014200c4104420603002c0b000c158036a81d1b1984007032050196190041d90f81d4054420b100d038000c5c00b503e40494192901 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 840832338 1250 840831088 840831091
    0x314030f0a15050d0c0302090c0403170f0c070807060f14090d060f0c02060f060a030f0b07031404030f12291305010e011a0702010e0d020301110c01060e0906040c030803 74
    0x802e00c004802996400205060641040c0c090740c18001c82c0034100107604080c4440f40c0e2240381058041c0c90076045a5420a10740005400c140c460707500032031904100074200c000c13104094042022034542590314008580e90340014003400340001e1810f61000b05803805001c8107a000317100d4801381420b2510480501500c90807000055961580390015010004064400e800341500389902034100780c9030041048680c80c00181081380101004001000031898807280b0300704507680040381c10419120410120041c1c415101480c0e81a0f000b50140000c240d0005041761401c1016122000d007184007008031300486000d07144c540d03440c408003a50120742004502e45120105c0d070003400300039a1301d44078100c41d08588090700008100c40402005001c0c09d1300c01e001c03c00b0b0f81038031140440e01c1c0ca04140e00003408152041c10702070090180c2c0e20000e08540c0d003908106241c84140d6507485e21040c000c4032450182a40344103680c038400d426000303d600c01c8004a2034620039900000044540c0c2c0c9941e030f400b07215510 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 840833588 1250 840832338 840832361
    0x130303110115030b09070b03090106060306050f10050a0903120e010f18140301090c06260903070204020c19060524180907090203090102280816020a0b090a0314030f0a 73
    0x203840c0c000c600b81f103001e009036003e00e084100003e6241c2c01c1c40300203021900d441c1c101910801d90044000c10507a10030494442244041c0340450319012240001d85108005400c0106001c1b00001d40603419640800001000b000998940100302e100c1001a94181c1040e91400700c50303c03500205004103250321a04468501e8050700000b038904c0386440d0725820750481d40280000079031084140141c0c260803182250b1200300ca401056890a00420003503030b03481070403c020f0242d500810000742da5101409503264001c688021403140c058a860814000c020440b00c1000318881c0c010b82e0607840000c4250940c00c4640940381c0030244030050b0031508180030003094030407540300788980480c0461440c005103028045250015840d104241c400c91082400444000d0361040a42c450403000d0342d00c41400790b080800b55480160035240440100d09240d2a04c901525105e440e10030710440c0e23840003030840407441c06a91040007050f00c0c042540000c1c8015244080d1441d01d20700400c2183c3d959500192075201d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 840834838 1250 840833588 840833593
    0x5040515060d05030712020f120306092503091e17160f03110d17180c10051e09010c030305061c0609061104060f14040506130303110115030b09 63
    0xc9030faa2100d10b9944200c500315100701940044608486c6c04010340103078400a00003810308214160448011800001d280900ca8900100881c2d0010041c00c0f192094032403a80c046640c0210340140540a40b41c2d10104035a501c3c0c0210410217106000e000644010b40c3c8580d00d0180c4011110714200244c2040c41038130448000d08151400141c0c0150140d00264400d03210072400c25a100f00040c20300340aa00103606002050720380c032004c400c01c41c030401e130300c0080b5a80540c00301c030b203904c1d54900c2c0c001c0318030700140c2180b0108080e01c440ca800c200501408000c00034462100c05409110000c7c0d40a018038a9011600810700d290000740a5007016038000e20181c0b2000642040c02020051080c0301c00041d110715940714000d005100181c0a80c1070f40e40461100d0340e02d4130785040001070041e1803d6407924100070841e40c0344560a4890406c440040100500b44c68232064100c801c004680b11034071044004c14214080c036a08104103009099403500d40c8a48030765443d00d5078494441c0e802c2c008011150341d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 840836088 1250 840834838 840834859
    0x30b13093c060f02130609080c06041202060a02010905070f080115081504110d151404030f0302070c090203070522030f110112051815040209010b1c2a030504051506 72
    0x1000b00585c424014890b540d5a203a91a15000c0360b1824050414403940c0a03060030001440040980c0342811045981560b40994501080d1310072401040000c2d0020214020340900080301c0090213040c0c02669100c03c0208800c801c0107a4441061480d4440c0303140c550002842294030820180b0910782c814084c03001d0028140170100055003900b0030341e1302181c40c0d000c405107103c191186480340341c0341204400742c001224105a103010700400202c101c55410103400081c1c0508010b260101c00c40144401e603010354803030405490140154000c01c55911540380c0700840020b180041c1d101100890342c00c44c0c6580e03e441c1d140e4039510510200c8080307c90500030030310003c100d016428030030720b0300c2007148443ca0040b1300041000d00d424140851183c4800101c200240809640c40300481070446581c0316180380c0c1c41201981403243c075080c01d424542c0040c9044c00f001c2612a0440c0c50060307038011480d02d80c500001c94a000d50855409035006402c55024a4892031009a102c000d00d07009035004140358480c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 840837338 1250 840836088 840836107
    0xe10050106080114310b0d0b04120914010509060412150e01110d091b0801060609050907050d09020f040f09051209010f030b13093c060f02 61
    0x6541003039100e00001004840100258402505080910b40c0100e400c4612910280a4044a080c0030a0301e41001907509540c40d01d2941e140d03210080b00240078215445052050810801e4000202c905841e0344c0c02e42c00d822000c031417041008109880000c6d4601c0007280c1d80100440e0030b80c000c8808690019401c1101040c1c114040d0070240b18248945240c80c8410028403909003034408100910f00e0f968101355032084000c02c8101514494000450002581070301400c0c0900030400440c040e9610408441003c910b1090640141040e0380442d29080700c155910814050000403c582046c0002c4007030041c4030813503455402c03410700d090005107505007044608001404441c00b503451055201c0e6030f01c000d1020040280300102c200fa101c1d00490703040562031000a0800e400f400003801c105035880c0c140c9180b50352503080c1c1802c00c0141c3c80042007044c040d481d00c8907050300425042e21303441d0108803a600e11202d001810011520600c6140050440a5039440024140c07020506242c00c1e000e0001448 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 840838588 1250 840837338 840837341
    0x306040920040b040b061803030702060a11061e070513050402040b0c01060e1e19020a030501031b03150e0a17091005070b0c0a12050f16031e0e10 64
    0x14000c00700c0d120501e0510101040000322000c44210b2401a03003040b080819039501c3c501614410388003914081032200650000900714881d00d00e00940c440c20102c2d0070035005501c60090414448804200d9401c1c0c0c84400d448140c0a40501c0800030f503507502000508200d1084000e410880403410f50407150359122070000342aa00a50481a0340400c003161041c1c07202024000d89004040820030182d803400c000c2207400d12080902d038101e40985401d03010421172441454109140303a4175020864944810141c0140903201c03c0c0300603204070f110704940018012001e45407904980e488a04840b418a61071441e2018140208040700240100825200843d500c500e0a00a1203500b40c1c03465a01e282c00d01c108140311104e008800104203041c80900001007000603059085490703c1d00c2d8a4590400c1d0341d00721880481d84040c016200c2c1040c043c001e40a07012440240034072002d0508503214152f1643c00c0b002c0340d00c80380a80b050f944c0c0c0105c5100c00c07941d281e0b002114882010003611244684100b0600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 840839838 1250 840838588 840838613
    0x2202060c01110306010f0809060c0a11010501060905040b0402091e0312040801050f0f100902181e101110180f031707090501020607122306090907030b070503060409 72
    0x241802000803c010f071542c0c0c41b80c80300850280b42e090500042c00c10008860350355000421340c0035244e00015040554074050100c2000c02e0006c00000d00c010340e12140001c040448900c681402a4201110304070249018004c2d54071951000c0c02100a000100304000201319848042a401d070085540000e01344941030010401f500304003001041c2c90070007440c01e00d0881c1000f050800250903441c1030003100444071385e0302011103219840158031190003070030b4580042610302c06160301241d406c101068036801900c1c203000303d0104880b400c404030941e400035641080100501005900078041441d501c54081d0310030a00c90760bc40140b5070032180d00340d4940045405d10742080d0040390b00c100e00544450070026a0690164143c6846401c2900d402c0020b50303038a0014081e8810300450211008040c40b140e0310401890300c4124000032999041d0060b000c0e08141641c010307015101c00000035071031040004d5040202c0703610006409890b91040c1c003c94550300060034147c1e100c0c0c5c03140c0c86840810840c540c3d50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 840841088 1250 840839838 840839861
    0x70209150310270f06020d151205060c030c0403020d050102221707050d030305180d0c02180c040e07020c1e2110020906040b0a0507021201052202060c01 67
    0x10000c44803c140002d1014079002ca400c3c0320b401c45001000550003101a410b102c0d80700d50003684641642440d00c000d007052460300d120300382c0201c80000c1c01d180101e842810607406074055410640b240c40300d2440c0792008640210403004c04001c2080107003017180c501e1540d40d015031700042c10681c05031081c00044102d03280101081d4107980040c4118034070b00717034071002250b489001000381c01c0c503280200354003006002e400750916584400064140010950504003100c800d4103882c0c0d1881c64000207040300e41e0310740c0142d00508801803804c2c40240c0503425130307020744000c0c2107541c18180350034001d07084940020032b00000c50140b128504100d888054214090100c403140c4001c080c003038082844442e486000c803941d01c20302d2181ca095a29000440d006209040c0c50a003d40d032440602d0105d05140b08641c0703e030f07042200c000f070a004002d82c89030141900790310032a28103d03203585442a13a42a21806e503044420b40c65401040780c00300400a406080d1644040d008a04080e850712401e0300b100c0044102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 840842338 1250 840841088 840841091
    0x40308030a02030906090105090a030c11101101140907030f021306090c0f030b18070c05061501030b0d0c090b0a15030e010e0a21092304061505070209150310 69
    0x240084130320103110540d44090b030280200300c149400c1c581255100c0b02074001400344145000c400040c0050568480e0b18070f00701174030341c1d20220100c1400408086040b2005a020351902143c002d40318660600c0ea4001c003201401451008c0c190b44802e400c03550052400c07a03011110007502d211081c1a40200001843c20304000190040041000f41c50b04081c000c2e207108042c50300c2040390181da10008940761031030408415400a0b03036814410740311108040070140491088804111b2000142d428411020b1000e98041c460110803a091241e400c0c030a21009202c000c3d41e403c107202800765980300340c4141c80001c01074416190ba4003400f03800d010504a002000940310030841c0c0020000b401410b40d010b20300f000401408030f0b6500c030082c9031001e51b280000e02c0c45025242e0800b0301e20904150f0050900a0440390038003285a403950052403100685501440c105640050081c0990003000340c0d4184544400d8541030321582080750b0200010011154011100c074064469203040100c2210305850010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 840843588 1250 840842338 840842341
    0x3050702090a0903052205120a021c02150f0f0408160e1006030504060f0c090314030327070f08010606180609170c0904081b0c06090114040308030a0203 67
    0x41c03150341c010003480c1c0c489850400300c241e0006907010b011104081c0d1032280000c81c144909540c003105012560096a021824100c21344400d4804038014565a100310f0303050300d868103e000d011000e0108480701a500c910382d00030701c0c030084195031b0090900a50a4441528000f8403011250b0f40d50000c1c0c03c108000c2d40240c00c0d007280001d40046800242214206200140c98005010040140d041c05400c0405440d10042000c10405170090f041c20710b1048010710050f456180c00401210040c402070351006a01031b9005140c82000c81164019444001150703d0411307840045207400f0031a8480303443c2441814030002343d20801d0310020024009510000c242503141041c000d29205507680d10384840d0031001c0c000c001454000d011801241c120b0706400d11803880800b4924201840015100d802014110410042005642c001c05881c40c44903407618800b01312581d0300781c2d24000400010307004402089000e0b0b580d070040c502d2440510880c022280340039260f40d2040c4494000f5110350306641e40200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 840844838 1250 840843588 840843593
    0x2101030b15010c050d0f0905040504051501061701090e030c060c1b030408070501030b010c06110423030a1b080102040f09110f0d0506040b030d02060601030e0a03170a1404030507 78
    0x880d007106091003468101c0070f0a55507210030352542407200c1c2a42c14842d0320004600720078060184d000003400004c00800180c0740c80d0a10036221044900d450711001b48a100200b461030082011101c0068190002e100e10b80c00c150034100200031001c6240700e58403041c030141444000802c0583e200e0424211095204c0c0c02d04110752140308200400ca035040d800601c01808840c03400220034045036001d20b030104554038500010b03241070f40c03080006001390b0b0400703115140d0444500028821541011f40d1030318100098450f000c14000b05461059240c1c004d00348aa001c02c54405203d400c0740c0c94003001d00c2c0403a50316019242244e000c0d90044c1801c005400080003640564851341d02c1100909141e00d141c00507120b010030b154802c2500c0003516540d00c4012403015122580440e4014a028007110308900885002954911080721340038000b0f800c0001d8020380c66404500307034803800e9242d20343d124061401e000644044000904641e8240c0ea503241082010080c2d1056034000c40c000c1d03e41c2d40c1c0d200c0c07060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 840846088 1250 840844838 840844861
    0x40f060203090d02061e0406050c070c12030e0d08090d05011b02010615081b0c10111c291c030c0c0618030f02040603051006051903020609062101030b 66
    0x40410100251002522136001101c6c510641d02550102c0001a280c2d50041c00541d140101c141c060003610ba0343c400425000d503008145045103000f134484e1080c2c1c600d02c8003004040f40e403540d4010052501030102d0100ca00b086000c1c0a02c2d103202d07034008582d100301105e0304000d4101c6170b000c50005030f440d0402000b014100e0f000030300c8100c010780307403100c40c500e0074010400c07107020103401210786440700150202281c3c406004400c041c00b800310b010f0012945030b90500c40e03c0d40048898445000480900644020712071040484824206081d0b03254036601890b0003901c0340380c51041a030000c080e0b41c00d012821028042d44400d80c0e10a44524a000c007050500603a400d04c0c0da0400000d01c1038003005200060b050341024000c980c1e100000540800b113a2010902070300303491340018103900c50701000c44021001600700c00199101a15418845071800300100100d00b03007840065040320040048c03403014100358005000040400d00d02070701260101d048811050401da1040c0c2f6041501000e200594614 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 840847338 1250 840846088 840846091
    0x3200109090c02072303060a0b040b040b03070b13080d030606081501140304030c06050a0209030c030a08030601050c0316030e0f241b06010b070308100b040e040f060203090d0206 78
    0x10881c040108000c08140070756100540d00401144166401c1e096600958505580c3c030290400341c282d07401d50500824500203000398400c120b00c074504141d1095200d04080c03240e0700105100070020100c4c00e00c0e2404020750707640712140101401014120100e6034807810000343d846022140d40c0090310a00d00300d401450700300301a20666030500c16000200c401da80c0090f42011041c4080c8903140d990f1102e107010f035007800340f0b05001820b040c104010030040c18459800390000a4083d01540c010761154010180c49949042c401044581d00b4400f01342194401d002410300302d01614120703031030150503949121566940e03000840000c1c0d800c1501e400281090f5800e44544032060380d00c0e0000c4152204003001255074644a075000d004040342c12072061402c400d003003012106900540d200382d43c4909001e501c03a0301001042e004120100c01090003040301c95113080440b0550038103181001d04040c00e060300c40c80b0252080d40c80326640140d0401203175940c4011070180c504a001450320000c2c60b540a41400340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 840848588 1250 840847338 840847349
    0x3070506010617010312140c0a051b0103060e1603060e0f0a1401031e2d050f06010503060103140304260105091b06310305010b04061203050307020703200109 69
    0x19010f0042000881e60512420404118104801c80b0b200740041d001d09400b40d0100744005e480f44484a8082c00004600114070540300c41541c034007642503200540540b6818402d00071724010f10b400168808010311100041940c0c1da245c0808c2051307176152401c9400b54280c925a405500f0003041c03104650151040550705210030482100c00d6156860b10701c440d181c491100a032410030200000f04205981030b044400400e0110a83c1440005216864020000030300448061050114200b0040340005600c0e0403654000c0082041d60700b1695403101c1340313503d410031442c07600c400d01c0081900300e41904c0310052004500e584c0002185c00042c85400d6440280000b9420340050800610491180c1d243c0340c801301081e51826036921032041002e030404101484058038818a40c1da4038134042c1c0b002102001c40b8050f0009102c00a281d00c01c00045403402c0c03203500f9621510220030400240200e010f0f580c802d981340140c0da540f6070b4030303250304042088507540741c02c1405c842d402c06002980c00a04440c05842d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 840849838 1250 840848588 840848627
    0x13050105040507212d020907020a060e030403050d0f11100c1d13020c0307141f14060904060e0106240503060a0302190801090b070e180f060f03030705060106 69
    0xe100343c641c4500102e0341c0031701c09541e540c14950400078035600c00726055465800740a000003445c1c51f020081d266400b480c8101c035014140300341da005028000040e98140c980101c042c0c006124032942c1074650020ba05002024060100e6000350b0707803407007400303155002089000c020400c00b00b840c0340105414080b44001c082e020782098040841d0321409800800c89003603c0300140d0790003013150018594080c51500801400203240d010001c140003080f0025810304181006400e0b00228501400380c4206188a010302c424140000f00c0303d2404640d02078105008840000c1c420f00c845981c0743c2514180e400004424007006605005000004020f0ba034015503460014214101a0005407070383d801488042d208420a410381040740091996241c010580700c4020490021a031425460301441122034201181d4002c006d0005030820301c19610111880078414026075443d005a58030a000240441380c10130101040000c06407010401030081a014000606166140100c024480540301e4440e90050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 840851088 1250 840849838 840849899
    0x206100603050a0905030301030f06050c0f0306040c0c05160305061501020712061b0e0a05010c0f1412040308070516180e100609020717030702030403060513050105040507 75
    0x1096428400645105260120b010f49406141501600e03000318050194000000004100207803000c880345c0180c0b068006202691318040000d82c0d50080c0030705c5c0e50124900b0400207030145403030343c804202d0180d1402d140082c94207035255a440d10340e16080041c00800e50207410704c28480c04014003135001000c044da400461101c040000d4079050584564003801404100b5102001700700d401100b2910303c4001c01d02540d256420700108050808410b090003110081004661948101280141e194019842c40449015503032001940034000e000c0901074020407c0031b90300401c02d1001003000354000c0c141c4130f440c0d2209007001c03401c20300703840024070f00030a6210040015010100784ca401113000068001108000c0d0400384d410440d000d80c05034101458240c020500050075409000a24081c4083d024112001d0f401c02c80c01d44420b90380200580c1c014801000010030326004503a124030362004051117401e2a695131401c0d00c0c0c0c10b540445d140d41040c0d07024050414441c00e50100340d42d19100c2d99502 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 840852338 1250 840851088 840851101
    0xe041407060e130905010c05071502180d15110702030c0a05090f090111070c0936080903030f0406140a090608071b050303060a0f0509161701060216060206 68
    0xd040c0c1d40e450300c074060b43d0342d144400e20301503542d03025001c100d800c04000d00c811103010304010a10b07800031504075611803441c48800c034940b40510940382c882c0d100e1300c000d07031b01d540e69001004148020450215a901c4000c4501e0306110302a005140c001030008102c10b13201d600f00e10425003850401c4040d00e01412201ca4101326030741c0c50500c403a80100c204005103c154680a86041c0500140712103c0c0e002c5000280c07010030040000107070b60450741581d000f003240c100b800c210042e1041c11800a90700051034400228094605d035800e104800313129a034114a49080c51010074115080b0101e070b00415072002c6000c211083d040400d02410810a02a0a14008540c50042d1000480340114001c0000307040002d10550b0181d40c484968101000a00803820342d589462135070f80d4003c9401c00e001c2c048903400014842841108041540c600500c12801c0e03a8900e41c486080b07a1301d14240b90200845030b540c0d0f030b41d40d04210901c14040c00440e8064541120002003203002941550b118404540c004020440c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 840853588 1250 840852338 840852347
    0xa0e0f01090207080c0105090303072a03031503060f060302040c092312031b0d0e0f060306030a0f140c010e0907140c01020f0301090e0703171c02040e04140706 70
    0x192200900010b0303d96405003004481c85c01054901c48a9601c0e29040c03100140000010f0351003011103603039040d00039030703100056083d02c2c0460203d02282e00d003801c0043d001900070303003100e131100c4102617a903c0d031583d4035150f0b4400d4607946440d0264142d5100403e0040d414180200301c40c1c00c01070f06100081529140d6000c4e45d02c01c1c0d07a00203081441030305c241c9602c030b40e60340b0021450249001045903103900b00d08084a0030524980c24498142c441c1e4003081e00094042d61502c681000c004220001e046841c034280000340d80010540740d07142c0603124642c030001d01d422890341a1030340507801c1c80000c40030780c8085038130b03007515000c84c0c0e81440800001c80c1d40300d5540d40ca101342e000c40c0516200240c0c1301e91351114801c43c041c100c01c1c90000c0d400424048e4518a00c070f00614101d500e21801403160411400c030541d1648103a0001804440f900c1811880000f241c0006280312003000010005a520101c94034089070050b401c926180d50f4010240010305c80100300011400302030101402c01c0310b00d4205d0203030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 840854838 1250 840853588 840853591
    0x5012309070305040c0302130b0f120d0302070c05120f010b030a111e060d1505090601050403170904060b04050306060117060409020d0b040303050f0a050c040e040602070203070b090a0e0f 82
    0x4040d22078000404100717210784101c00a690260100e000707007040c1c109178809440c203c401c05000710201c4420900300d190141c01c0c60220407220015062030a505803003180a584510001d55171012a030000189603100c1159000482c85400080c0c0500031482200c0c43c02e44180b083c0e40d40c842d030f101b4104040170500340c00e1450140d0303a04035041d050500522812100c400c801d0101c0c02d030b200f04003165800355450f10760080b1055034914501e503400135450300100005242d081d2841800140d0900040c00010821110300120704101c01c4401d0414040c00000f40c181c030750941040031006030219082005090401c5000c1d0003400034280200c4104040014160040c8010000c1e40302310707201c50040c0255291844030b00001038001c0d4840c1d10518007820b018004e0807043e46c805071030fa000b80300041c0c417074401803046600444150032528a000e12305800200214000341c42074800960801a900059030100601c2005285050b621074548040c0750400011040300d900c0003041800c0b102c100702c40081c0d90180706 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 840856088 1250 840854838 840854851
    0xa02090120030a0f1716020115140a0e040f0803040f050d02010c030b01050a0e01030c09091109010212070b160e030f06010512010204050d08070303020c060708090c010f080708181005012309 83
    0x11b034001665007040307001d000e022121300c03050350744900082951040d00c401e041d1800420780714590615520303a44015241c804a4000d03042076600707088407001a10000c0203642190017902c84200e80e4400380c803070302d09040c00c044d00100580c2d5168030fa00920764140c06010703291802420000d0610348600703009000d101c203100c3c0c0b060401d03603100d0001d0990350040c064203014011880382000003201d41c1203071044e50f038444407496000d40700d140302d501c012100a200704c5450340d43c010740000c410346413000300d020524103e5017080d041c0000110381d003845440c01c1040b203d90100420040c6419450301c4e080c002e41d070448808015240c1d0041100380441d407110bc03a00403074103031311204859503039483d414200c0090003004078144503406140c0501c650251f0261140d40661450415245480080030040d1003500b04007000d40045107a035400501c01a00480443ea4800c40440c075005141650320030352403c08402c4030f074400d06140d03510018014114043c195020701c004c4e203403015180542c45800a400e605004241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 840857338 1250 840856088 840856111
    0x2010f14040311071205070513090c1a0405041e051008070608060604030602040e0109051f27022101080a03081b0708030106270b030a02090120030a0f17 67
    0x4600411104101c03800c000c0145545c03240440c1c560307140094840b4030520490384181f41d913041c000580703411845021184d43e03000c3d03030144001e440c180f004944840c4c0c400100380d08030802c0c0400101c94a542c0a014018480c610140200805081ea20001c0f030340e015085503030705055494240025403001825505882c124102f542c11a07031840009896032080d074200400460002c0750004045512410941c10303201c40140601c0695940c008403100c2c07940691385082c000c3c0c2d442c0c408100c1c00003150811618807805008070068540c0c1d0700d00c0c68080c0c1e0300c41041c500c0d0350180400b40011962401e122540905015030240a492859440090849001822030a89414516005407414842004075454141d10111441d100e60b0f681c1409000b00b0422000c454000100280030311407400b41c4096036003a10803038100282151100e594044c003e40085c00028188001c01c0401008144030b20340c00340110b403d040c000c655807010f6a60007003064400382103180078040d0b0406140c03001107290b02c91540c8412401030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 840858588 1250 840857338 840857357
    0x2010f0e04090f050307030207120804090203060117090d09050102190b060a180b10050a21021e0a0f020f0c060304080f130302030d1803020f120d0305040302010f140403 74
    0x5002001844402040300050f81c10707400400101002030014613010750203131008280e0783d01c8240c0540d4240c2c500140341e400d081000340300c42d0700c20361b01840e0032907010b2401d407003510030350344000401c140142c03041e58559008461100e900c561280c2ca4802400080c8068100036040306005070712000300c0040105000140300006480b40c8502050100420124a00d0081801c07580d1100c0300515100700e8045c02901d40103031041229010340200d491111b01c6540c0d003c0c081604450614040410100c005403040c0c08101f040d0070840d8219840011403400021182d450078070301c0003c2c3c0403800c0101000d080d500701d624611210340380813546802c000300c25038100c0d41c0d0303996a2800400502c030f013201a01891384003184040201c0c890050107402e9910035030442d031400d0a058000c0c1c4181c2e4080b2020551200c2e1600d0034001410049011302c1c1c404006080318480741c0155a400341445034580c400320020342e43d0010030082c5a0309001740d030b440f4080c0071020070450fa010070100208880080c009014040e0b00007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 840859838 1250 840858588 840858617
    0x60c020a0905070c023c0d240f0509011d03160201050d02030a09030e06180409110405131106070209040f030e1c140c100c030c02061c050a060302010f 66
    0x1c0f04c02202c541c01051076a210201c1140b030b0302054036041800c1c2100b00c0c1508410040c4400c60000741515000902204440c3d0460307a80c0038064400031038403450503842101c54101c45c070440c0a00c00b50075111000124061034200341040c211a01c034040724803018007210860340b5400c00401120a0190740b12200300e0100000e00040e00c0341c0c4609849020090310002c1000ba4024940e40a030404030710990362641580a000d0800100d030141492186554480420000e940d1615501c212900c0c0d03c07403441c407015016810300040841d4400c880102c00c8000c60340021040260404078018035100c1212940c0c140852034002c2054088001d03c010003030480d640c030000c180750058003d12a420380c0204910030700480c4c03582c4410300741141c0100325801c42c0c0c1d006209820b20004243d02401d0034003d400c20348051004141212000e64416066050094540502e030158490b6401001c070368001f0401c609030442608100011240e00921041c030561078940c05000603a032080145e8a00242d030f160944403d420320 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 840861088 1250 840859838 840859847
    0x607050109170c0f3702060a0305011a0f03070804031806032301030b15221a01030213030230010b0a05220c110a03120501060c020a090507 61
    0x40360081c26002c42d4805a4540c0c052100040c2881034142c0155085100a009156507500c0310003800c440621031604043c0020742000030084090315400c0f8541905005500407840b650300c01c1081200003521103005100c59412205880c4651703400004d01407500a008045ca846404098900384c100541e51010409051141c00d10261008044180c0010160f0b40c0e80b020700180601194038070002d0f20451005446101d810f80a41200e400143c5490203642c0e800380b55000c210149460f52740400c4101c07094000300c0480340900040c069000c00000c80401e013141d0451600d01415072541014010006a00359042d02c0500f80200c03503059903105050341702440a14803403110405640c0f03891150146603414160150480e01703c1100c151041d000d41c60b110300074410b0f154091110001703082003043d044c101010f8154840002030714249807881c14030009950f06400c1a520b035005a001405020403a900c0b210a84129030040c007007810071703840741035055000c1590303a5601e228010700369540ba0700041c1c0c0d19005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 840862338 1250 840861088 840861101
    0x14030c0403061812020f0c060408071809080a031425030908090d0c0e0108061608070302090907020a12021c030b151b160b1b0705060408030d0e1b06070501 68
    0x240d1010812100c13860080d0b031812000e1010034203104842e1510744a040c414115025102c1c41d6000e40b04190a0400c609610f001d000b2039005403603a200100e1010444031009000086129900440c0079100711800c0c3e0041c03900036161480907264501c42610707440041e4455442406942000f1644030311508080b50280154200380c2d0304a41c00c2c107015000c010008268a050b00c0710000442c1c9566200d01000381d0328881150340380000c103500c0c29507140316801000915840003842c5800351030440c60601050003600d050390307920f000d83e0115150b10100485000001d21020840c03009269003110081004c0c0701011029680051681e560400e0595488040c0e40b80610302903400c183d550360080101512022251510464903401540c550907112501091500c00720342d80c0c2c5009605180360210181d01c000d441100d040018411503078000b03140e44071759014100620100018548440f540d103001029101e0101070b28803d50040c03980c82d0a00301a8544d0040e0402040d0758441d12106030303180c180c1c0101744 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 840863588 1250 840862338 840862343
    0x80c1c030c171308010501090e061f0b0706050a05090a17092106090714030c130e0109031107090b1f09080609030405010f051c02090307030b0f060114030c04030618 72
    0xa40035605440c40307003103c000c44038108000c20450384e85503002012500f14101c0a641070300a0404a908105804290b07900c030341e640205e00b0391069035450b030300c0305651096204440143e203441c10401c0c445600e00c2003079030281810024103005106540da010070031800300741c403a84140c0c01088024440e00e4144a02d81c104061003481c030b050030080d102195442c901200d00c640148291100841d4210014210b009940d5000e0001c1c84621620001c00403560718501c42070307408643c0c0b40c0d035810b001c401c24052005280d0082d29104078110315407142905200d100d030070501c00b0300d0814000401a4450304012500c401d00c102805105501182e012540c401c070300e500014040c41040103109001031302000402c100c3d0b400b40c070388400c0c01032200d0041e00d1a014111601421800422608480004a400030088450300606170b070700c0240c50344d45941c8062411f40e02001c0307202000080040139600042402c0c101c5400050701800c510302a820354850344aa800021300c42e50310f4072541c9003000380203180c900d107a0f0b5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 840864838 1250 840863588 840863633
    0xf0330051012261605010902101806080a090506130b0c07080f072102030325020d112503051905191a04030c060c0e03070e1f03050601080c1c030c 64
    0x313055041c254080c1114100c140d00c6040300307110303a1008a00807881d0300651400b01d5284842589800ca082d54441c400414104100f0f0b1104208400280c0902140b80b11308024401d50380300c01c4036400c0c2940032460017411900c2c100350800c10341000c00c0400058541c203000001c0307041e68400052402140c144c080480c81c000044206031840e081a401102a40c82188030454961003030099280c144170720b8291101d5140960400894075010b80c0c41407000100d10301c4d2000480f82003002030701c9080c038810fa00c44d00c042022240c1c401d0500401100b408400c48050400e000c0355015403690b210b8a03181d042d4000303010307a403030341d849205010000c04400510801c0500f059588061070141405007045695041c11540c180c83c0c48500300c1018081c001c3c84601c040d001e8000c01c1c186003030101320b851582c1c2c05050b0305240036811034844514901300b6440c0010314854400742c0700707075407602d10090725000754482c015200e265403c2030102c3d01010b07800007202c40754045c5800008a0050f04003105501003e000303009034403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 840866088 1250 840864838 840864877
    0x8060408040603150621110c01090303110301080312280c03050a05090607050c0304181b0801051509011b03030614030a0f033005101226 60
    0xc544180a001220215101481404800d03030070103004820600460000c500401e890b0f440207183e04602e1600000c0e82040000d0310f04c218144160507401c0f40c2030100c0c4d43e07910307071541004160b0305000d510384100717400d1059811541050111512030050580b040d80c1004d103040051000c20340c442c078540c03504917000c50340d0008a80c00d0130400040c101c004100c0c000320b03040c280400c0340c07a00740e07104081c8107000080180c08142c0324003000b260715074040d40ca02900741c0310500c8003060003022218001c0740c90305003020020389908020712051035202c1e180010010f01c01010010007040d00c40d1214041011600c0300c020b551130701e48800680b007500182c00b11254001c110b080690801d07070075602207020b0340c481d640d084070000103e50800d0f6940c0035180d4001e00c91001c08680f0000a4040e1020380e00e840c4401640c41c01409100307a5a0050145c00e00381c0079140390700c500500c41c00012601c0a403019100c081850000310100e5203400340701c42c0e0310800c144190550166400c90005450040e034200d50030030140a00103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 840867338 1250 840866088 840866093
    0x6030203040309140102061b09030f0a020907110703060213030503070b06040516021f060b0d050f0c0a02031602010e040f0209100503040b010920030c0a0207050a080c06090a080604 79
    0x94008079011404101c0c070500114000080001d200040a0164000c162595403500001100d800e0700a03000f2000030180401090360340c0034010100580c00714801844902c200340100111340074003070030311001c0c80106031440c2060326010401c07100f0b0342d0708000301607900c0d00d8980d03144002c100190710191050001150303d0080050012245000748012542480240c494595000c2100f081d0140b03140941d1040244e0a619081d100b0740c40082085e0740c000080443d80c844108881e540f00000b4000700954500412003a417810744409a08002c0840c081401e00340b1480e000b0395079110b64440320a001e8010440c90046a1051881c002c041501601c00d219007814080c114007c4e4011100c9180f091010340f040a417214807aa040e68421500401d4018059103070008510052a490b48480d4004e41440700300f000c00a500c1c0300950007040d0700992260b0b15080e41b20028209542d6410240c4580007aa104101c1401e0000700d2000c50201241d07000e80c2c1c3c800c1c1e0702c0020102c0f4219442501c0600850082006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 840868588 1250 840867338 840867341
    0x2010c2102011a0109090f060503120a02010614010903062a03061814060d0807050a140c10080123030106030602040e07090f0b0c030d09120f110d03020a1403010603 72
    0x1000e0529070000e102a1160001d155100540005650b000480102c02001900060b400080920100e00000121076071100042400d00049000320107096000088a003a15035092180100500254035000700b0740c641000002c1892200348009000d15459520500c0b5084580304680015508400d81040c000002103001c0c000e010607100b0b010100e503820720030011480300d50041c0740195200701d107103402e41c2e43e41d403040005550710f00c00c0580b011071080c03080340c000403010401c0c05000b5004460011948212403507151400c900d0078400d500400510001c403c00d150840b0030603065031550a9104071184482188440349a94a0400c66056017001c0000041c0095680140166846c0100403105c07070740c4100003603500480030b01ca2940000f03000780c5c0802083c01020042c064104102c81a00e143c0960445000180d0303542c10301c20744042c80340359440c104490300301110101c0329442c2c3c1000085016141d0102d40c9800034440c0b0002455000500c2883c0c151040caa2082002440072513a6120b58403010003c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 840869838 1250 840868588 840868643
    0x9012a0b06040e01060b0706020a050c031201030c1d07030b0d052506110a02090a0b09041a09161a09030d17070e060d1104050a06020609120a02061302010c 68
    0x9000b80e1030400c0c0d0845040042c00740308140e409610000e0310300407055035118000d40c041112841049000d0164660349981400240700c580e8814088903015411828206181c100a0b880601c0341d03131f00c40108120301e100c410003c41d401525414000380e080c0c60040071400e25035003048002c1050007000c0507102e40390815500783e81c00d0600d2a50008009854000c10b680400034900e07c040e0941c41910614010b10f0844840c40d07004403401c20110b60100d0500c082a050003080d02c0460b13042c03c90040003002c0440c1c1d030080551001d503603001040700f07180c0c5211a1100e10b0180c010380001061801c9110364540c0c0810840f02502005801c65111040c12540100100e243d52408820320280a0100740502d2142d400c00001071801040c4500d02294108014018030189651042c0e1580501002940d07075642000803005160a402a1110345044641c02e42001c0c80e010b40b40a048009020b1000c2c404d600081503544041d80c2810742207103805900040e60902c001c248002e01e47d003c241c060354141601c41c54840c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 840871088 1250 840869838 840869851
    0xe031e0609070911040b0f1308010209030d08060d1e052a0609011d01020703051b2b02010807020a06230906090303060d020a0308040602030919060509012a0b 69
    0x9801164603518640161351085030002d0b042c030000d002c00e11000f980000103104640680c0145031801c500c04101e210b030138106a003c4070082c1d5001c1a1445242800c2c050801404014980400e180c41c2010004516400012010302513007842c0f110440e80107140d0108041c9603420804070307030110a20a4035448204401403100726500340c091100519414031605403182c1c404161260b00b410001312060302030403104201498110b110310540000407913000c2c00600b01182900c0b034004c0304107410609012052480b03401a000da080450501807a412801406400301a424038109481d034580d1034040b031510700d1051028082e03d10303002d192011001e482ca50b40d19800c0c3c41c047d012100741e49040c6a140c40321003c81d80002150000c1002824618001d101030856600c001d051000702074803911400707041d810540100c0c025034400103e62005241600251242ca0340c4111700280d5507003400710051641c0200b200041c107101c00503080340d0a10070120141d0950190700d040740901071a1a0500d103507106001d8442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 840872338 1250 840871088 840871093
    0xe0915031f0b150a02060c0a210c1b080702010509060d180201110312010e060d06021803121606020a030e010c09140604030308010e062805030115150e031e0609 70
    0x1403401030f15402d481c801c500b40d4016165603551800c054000341d125802400400c01502c0d4108a19140780040800e0b924003030714000b9071078220290140c0f000801607900c00c4103814804003030340018035280440d0205642868451388500b502800f2900d58080c03901030b40c0490781030604005840b0030031161000c080f4000d0340d40300241d00740b11900d01d84034812a8503074680c010441d4010b00080d03140089047e044807020b081c0c510802c256407a007070200e0b0004041464240340c0a11084032030b03d0100301c00c069803c488030485d40740c00c3e030b030410601240c50300c1c0000800c500e4001c00c04c0c1404034001c0c1d10000c8040d030071030003d1001c0c407928034000305146014050701c1c55546841d000100315080c8841550b0590b6031540343c10700b660342409486888180010141079008101021052407001c81c0406030550102c82c142c40010f8a081800305801c0d100404031469001c411403000700407174200545420110205401c0c80a000d09128000c281048607140b404081d0310307480e24a1207550440025103511882e1004203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 840873588 1250 840872338 840872359
    0x3151202040c08060609040e120f21070c110d202803150b0a0609030b0f04150507020f0d02100e150711010219050c010c0e0915031f0b 59
    0x2800d83d00158180c0718103030040010300241115040646c4400c80e8011031004071081d0940c0004007400c1c0b0b5000b0b214141c82d210700414002c0d840700003010209100d100070405000c4078901100000c121301c0042202614403622072144a20907110011455403103134021000c46211500c070301090040501040c1900c0c05003112183c075018039070303250000c0f0b2002d800311103080070068a581c030f8903952042001c6090707400b00d560b0880c40300e00b0780d50b1111020080c01035403203059507181783d0304168400000052118002481c0320003008006983e0304910550f038102000c0c001000d40391000100e192400d81c4d0f5042e07406101d110f084082e035540004401020140360f00c800c0c031010310080b600343d48608440b583e5685210902c008100e42c18043c1c1c40c1c20f60001e900000060400d40346d40d0460030300440200034103000c03500000703a40e48880401c0c000c902172060b241c01e108480070034038800300385440c500909000d149801c11049006a50b014000c4806403940e444006428000b200111002841d0601d070342449900401d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 840874838 1250 840873588 840873611
    0x30b010f18052715040b010302091302241c02180103060f060509060c030a080f0a0912050d0207060e0706020d0c050c0d0f0204090f020108130b010b07030315120204 72
    0xd00d5103e44203001030040c0020300352010045207220303078210100c5405007130503c440e98825181141d1189008200308800344d490360040c098000b9004c0d044a580e0368112103140b000d600e41c0d0a818104008020031204000c0d0f0344600b07890280175168086000499a02b00b49000c090240c02400102c00ca607294101070700065070066040390854030278000c2403110a4020032520740290040c1c012000c0103010303c0c0c03515460100040c1968446402c500106a007201131110350b8440381d03d0941d120b10024070801800416445043c103242c2d820000348100100003038231080500698042c0d402e9254420018030840b00c0d1102020344038441400303008010b02ca00000c111030580714034031080000e034010016010310450300003480790441202ca0705039a40311040e4030400050311244202207800c0d00800d096651030209100040c083c0707401405402043d02e0101c120307004100d00c80c41e220304603070724184400e558141c9440d05038068082d0000440490022f805e000865504a0400321101c51007128204005400708 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 840876088 1250 840874838 840874841
    0x30703030b190614090a080a03020601060f1d0906011101020d231006050702030c0a060305040c0506270321041d101203111002091203030906041209030b010f18 70
    0x5104503000a144c0d141c41200d4980244000c11840e000170f00325881d40764903000c14a1504404d0902100103030b015100400519902a00c460880c4c0e140b407400c420403241d55983c02c1404c1c10181000ca00c68060300d0045001603000c1c180110701080c00900940d19103c06c00c201c04010702c91501518441c00b40304001c0b003402c4c0300f4038048031301c0741a0540d90789190700d042c4801215182c0150908a0305441025030110050b541c1d0803586005140c9550040b0f414905858000310a400d140c1c41130703000d104248043d5460043c0500803000381c0d40440078094290b003c410000785024420380405008104840780d403103982003849d00510039100ca655140c42481c9814140104604044420006442c07002ea000d000851a1b507402442150003071400b44d6140060340a80b60800c0301180c1e40300300d2180e0021b0414030a041076200d00c82412452800740d4114641412203603180c001c020701c001d00301d000c007040081b02c41d4001d103000000380d900000180c41661b11805811003030f501501600006a441e10315800011a07207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 840877338 1250 840876088 840876139
    0xe01090c09170303131b150f02010e0601051306030606060c0506070504050d2306012d03020607031407052d06070909050c0d050a09021002211b030703030b 68
    0x71000114916555041030601c0400796403001c51b000c1c40200580c00c0c0101051034204040c181400700346808164003100036081103c0348080406590400d03000740c410f000041140d034112102510086040740c4103201441c014441034100912a41c9004808120f1952064015200c144a0700489050742c487d82c000351058002d520420fa40b05074181600b2001442020282082182001d652041d125103200f00c00e040490076002511412000380d8404050000d400865800c41c1c140d1a0b07802c1400d042da004541a4842e40c0302c0034092085155810503180048000c5aa005030017009807001c0e0301d485001c011040c001c3c0e130b50709419882855074448142e6404105c0e103008980903210300003420b140422220280c4001800f030031030964240f203140483c40030341c003906126842c0c6010019070a034840c41000340d4002079020541c1154004248601d840c11100413203c0c555034940c1c270b0141c80341d4045450240501d004843d44030540804100c2401f0150580c0040141d4542251a40d040e1801c500001600d1080d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 840878588 1250 840877338 840877379
    0x1309060e0f1e01150507061812050403110f0a1503020405013b120d05040815060105030712110f09040b150a08090c030f10060f0311190e01090c09 64
    0x2040c0700400c030044448111304040e10302400c01a050031159200c03501120b100a544401c0c8001030340c0c00400308100c052014a00014904003a13040600b1350702d907401d82e080f03a000498081c55800c5030000003034be1002c1c8044001c15003016540741454910344014040d40151040342d0104580e590304040c009008081800f04541807224509108045920035142040844c41190850f090b1075014004000c18003000758005078903101c0d15038503454000d88a00e800b510740900880a421042800303280c1e070703100d011031350000d00c0340c5800404004424030711001461800940036004d40005005020041c0c0403014052a400440e001c0089a001500b80502d20381c1d0b4090400310014200002c0003441e010741c001c00e0300201c0e00c004469107890040d01007881c149010002215aa0044c0700745018008a0301454010f4190300b02c0840d1482d185651342c2c2805150240d4141c070440c140c1c492200e00c458045041c0b0f000380081c1d03049103055651519000f006102d2506450000707184440b01140070032150545040c4800e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 840879838 1250 840878588 840878641
    0x22101080a1a04060b03100b090f010e01060c050123090c1f0c1110051c0b011407050c0a030606150c020d06021e030c0d061d07051309060e0f 62
    0x540b211a414040050003240e043d030360303244c04540c81e44080141c4000110301100001c0d81159020810501380c40040c00000c03c81580001405050f2030300d8041411900c0d40d040100030313540c8501d00329000d80f080c142c03685421030300c001411204601410f01c2e03e0242a966087d901040140c4090201d0303a021a1030245400c4201d20070307084a22722030500610041d0051000041c0030549200040035800840b80c2203000907000f06200243c00c0070400c15001d095034070340c01048800c80a00010700015050307042010781c48c90228049050000611620a1001e402404c4c501c0c6151a858803600401040c001c1d28950131000c078511885d140140300410718150001c240082c0302266030350310000703548542c440107038841d040400500700342c04031800b41d40514a4580450b8031404858580c0c411a60244e01441040310039400c6a0b5285e1010f00030b10f50011218a40142c5d01c1607210252544a0f48a41c40201281d14114000944203001c8400d00d029010308414044180c550124043e4001803036144800c090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 840881088 1250 840879838 840879863
    0x901080303040308150f06030a1a0a1805070302041d011a0406090b0a050f0a1101051302090609103803091b181807090c05040302040b030709022101080a 67
    0x1e46194003100c041031001446c07603c061032542c01003001e5800503901c0c080616141c00404440199261503c01d100006440714140340e4507101c1d18035218420b030810300c0d03d81a900c40215004c1446070701250050701c45c1440d00d0003003001403041168003100922400740241d525407040151052074034200c4048030113603550104500e041030268040b507400210b1000c00c2c40020800e098002d40d81d040500822140ca80b41e1680c409071540c403140c02c0d00e00092080c501e0700482c82e26040160740d50024a03400401c20756006240b40e854045640040349542c00c06038100c20031135450102c252242c41c08071242044458500307140403c1c1510000310340002c0e02c1c002141d400c51408d030b00002c640c1120b04800000b00414044899582002c00d43c0d600c0410340740300e100d0b03c60f8444591b504e240e040010701c0040500380300c1002103020f0701c07000410600035400002c0c415600c1e0714a13508160360405c02100074000d1008115035460070402d0b00b085845c00500e44900412480c80001201d52000c9441c11103d03411003158041e2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 840882338 1250 840881088 840881101
    0x5070e0114031509250518030102040e010e180f0c13050115080c0d06090b0103051005060d020a02010915050f070c0206031b0c120d060f08030d050402011407030305060901080303040308 81
    0x913100142030407409000800782c02030f40e9403207400049075100c0c00d4840d10780c0c2c0c44151010100b0303410b4401d1404d0007680104010000b40031104e80050441e0081d0a90301c40f41d0f16225206c0306014440a0719142500c51524000b014050124919010b03000c1100c080c01400001d110100030303900709100702c90070f03c0c1107618000c0d000340c05030301c803540d201c00780800040c5010a41e030a02c0049407890740046e2409503443c2d03044129540c16105880c0c0042d03180708105066031904002071250300c1054a0344d00003503004030b00703040220700075006003103400c1c0e220300030324130340141c0350201c00c02440111040b490982da01404a25018014461050041d07006071809181d46c0e54400351b1941040684a180384c1c5000070494065643c4090001140888400382e0883d542d0003201441c2c400d507003042e0800000c2001c500130401191000004440c0d408030303407207004244c0b0b07902c1d0300050310281c107014074100c2d445000080c013500b003503410f1703010501c105811103401d00b050742ca80341c500ea668003003221300401144220012480303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 840883588 1250 840882338 840882349
    0x101a090402011107080a0b0403080708100308090607060f021206150706021e0a0c03090b0f070f0204020403081902010c030c0f1d0303040b090301050603370605070e01140315 76
    0xf4046814100d44400e1750315000903107000c0d049141691020002002d105c00c15900c50001c0b0b40292451808504900700203d072503060301e029220040000000260012079030700d410040c4c881d80790300700e80c041202a05240d403110180d0711000356410306804110000300d0a01d0310701015244d582c03200d0340c014107040090b55003000950080c400d60b81d4001000c9000c03401d036807142000340040c031030720383e201000d4000c00d00d0050508141c44d04000308804041c00b03440c200f000c15105851400c1d82041502e0f000079030a00203d0700910807504007a280c01c0000689080741c0415035841102c8120360340c02001640c0f103903002107089900101442d8001101006c5040703650f4420445550303e0441400303c041031a8070b550000b8515440740d131001030501c1000c00c9000203440c0a1140d03940c01101a80608907070110100100244041c05294007400c414860402014201c46144c8418003a44402c041015041006004c1c101514802d1301030700081c404100c00c01c04100303090035a805400703511640c1d40341c80d131100e04004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 840884838 1250 840883588 840883607
    0xf04020307050711041515080a0605030a26032a07080904090201031b020a1a01270b040c080406182001030f060f1e060905040c030b040c02101a09040201 67
    0x1707074002c1d01e60286c200b404a64104010003080c6401c803219104c0c1007084064a10b110090014400702c1c075000042101e503c0214082003180c2e4001074500b40e82c0e60640440c800e031241d0b06581002c0c02404020031078001401c800f1044010901000680300c04240d8280390160303c2070010003004244180019226400d20703400c00c400d114414100411171040105645035180d400c0600324005038016802d40080c8072130560707445a075241c00c0c0c0c8100b42640c10103480c0b85054081402000f107607600100300700101c0420742e200c4002c0002c0201305008115049000401d40e80003907500f40d50903840d00341ea1a48217503400e0046542141e01903800c50209509181041242c2c90700d500003418161150a0811085110700c2011b0250441e5410748002c14103000380006152040e000c0c000c10b08004a0051180300d802c01040c1040b100c08440204e58510f51070000c8000e0301d10080c009402504120f0f5002400d6004514401d8400071501c0c1000b4080000c42d00720580001241401d070442020404100994815041388 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 840886088 1250 840884838 840884873
    0xa030e04180c050a0f0302100807140c03070c090c09050105031005090c07171c090804090e07060e0a0e040204050615040303080f1042020a020f040203070507 69
    0x50300c44006036168120304070701002103880410740342c014010f600d044d0040074064009031450166442c21580455007604583c0b010700d082c822900d0010b40e00d10321448155202ca400ca198283d15018640e00d6955607030815070080300ca4890040010a062000b07200d50320480348903541d061344061070440159070903030000d4540001c8001458010450351501d440a81c004c042e1010040d65072241401c0c20841510711b00c0d200400d1800c10042081d041c1ca030522075512181c140140060840c082c2d2602c040680b0070399001001c0070342820111400c16034003090030001c41b1091303150348909565004c00c00500c003919008101c1d00440001c0030402504003503120075400707040901102046510f50701e000d9500c8e04560700403070004039450200865600881c00a641004618403d040c085042c05c1c40f03090018240b6803249411a034052901805030808226107100482d2030900f2003c00200c0d00000b921b0390980304050f03000e04840300c803201040c20316100722481107655940c3c86e42410b0b21903a54040d17012050124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 840887338 1250 840886088 840886091
    0xd09030909060b0403060614012007090504080304050f0f0d081005373212010c081803030105061b07090b010e0a03020f010c05011d030405120f0a030e04 67
    0x10860102a02c00c0001400030700ba4201d40355071441c83c006003541c90a401045055410310703140030784c5907005250004031400e2080d4115031040e1000e195071401906a015034207445c1001e041c4001c0c0200080210701440c0a83d05442e02202c0c2c3c040c034241c0d18070003086070104542c048840322900c0c0e4402ca01168002c5456003e5000a9176940700040c5a645980b20560030880042d0507610791400240480003a402481c0003801424a001e02442c000d2844040600030f200e00041e668100c005009407100b43e00301c00a00003540040c0840d00c4a0080c030404090001185212000c100d50061004d103503040c0c0c040c210b0003545560300b003006021031030304801d0400d08072540e250012990480c0c00d02890b00079005034200003a0100d6490001010881c0c416030980c0209900c9406002607110104c071247c28240a080c9a500c021951a1160050130a246010041038a08206080a0902000034812610704880859401d041c40c1c8040381c0708c50744007100c0c00303140e030064502400180c000c811034800c080c0b00400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 840888588 1250 840887338 840887357
    0x10140a0302160507090501081c090311040213090204081203061c020a08010903020d030c0f0e1005040803040b030405010b0a1d0c041502070501030f0b0d02040b06280801050d05030d0903 81
    0x2c43d03910740a155000030010b2510341005010742e101c10030a0510700750404407004c55040042c00080c01e188028000500009091111200b080d00e50340c04070b070b00d640d0403000d07050500d60399801ca0300000c0d0014083c480e618096103186034210410542070301d0086100034420300d402650096954400344640d0000ca80182e580e05c8009101300e001c0c494501c04500036009020904201d41c03000342200c403181d00c0701090261504014030503c0d4000e2640b100b444040d1004403a410700714000b0745140c00b5540c00301c44035101c0040c1c081001080c5078081e41c015446a002404182402c000304907030050b16006e41109040b01020407003000d800100041d401200f6580918a040d40f1074074501ca2001e02441c180700582d01602040240d560b240c41950f0100081c410b041081c441850009142900c812001a104680311002c044440d51001c00f21076620010540c11090b041441d030181040c6075407100c0d9140880c00700000020241421000c003e4016400405541b41c45032215800d401020060001d03820003100d080c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 840889838 1250 840888588 840888593
    0x304061d03011b1e0906170a020c0d0c0209010f15120b130905070806090d08091501080d08100e0c03151e03010609180212150403090510140a030216 65
    0xe0740360107210300680c1c0e2030a44002401d100c1134203100a030140c400304045408100700082d4000d14140821201d00141881600c8420100010340030700d016007402405040011113089402c0307d03c0c03010310b5100b0355400c2d4107030317aa035007829805c03482500c2004404092102540750042c031a03081a0114030201d400010180348400108a00040e1200f410000c40c0e1780d004058103120b1308200660003070504800511b03d600d0808217445d110000102c407002800040d0f40424100c031420b119541c40d800d00070410415a680d250143c3d41d503540c4540000340440c1030341d40032071034045110306902c003640e100c0c0c3d02075403603a101c0318000c03607442d0303c01004203199100080207401240c4d01c1c0d03c15203251514a0001005100154080500f1183d155104a01d40c074642940c000c40302030201e1340320200f00d40403100070201d45041d050003818071b01c2d21841008442a0700040108054010600c40140d503030030381d1103600c1c030343c00c00e10b0580c1da84801494a1150b108140b2038001070904c02d400030014860002445081c407042a0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 840891088 1250 840889838 840889871
    0xb0303280225170d02192303040e100b0406080c16060e010b0a050f0906060705010c051305061201090518060928030903060504080903060a1506020304061d0301 70
    0x1851502d10025200008004410f01d03100f81c1c60f0960141406030120403079001c0040d50b034a00c80912240010700d10b2040c40c042c82100e034084c035401d2920403000124003001c000710644035406405108404404503001c52441604140081c0540310034904052500d1309002c0700f528001c41c0180b80542c0c45004210003c0250241c01c000c80080d8442c0e0700100e0104481c04002c0c0c00d6402c252180d5000700100300d42000f144c0e445050701a454041541c244a01351110340101da5070b40701c0c44401422070340c20503c950381e000c0d500800500209101e518040c2c00140c44104000c070a2051040c4010340350310f003400601c1040c1c0350b0341c021030b084190903200006000b0803441141c207200f011201c461a03500501324200b1b103080b881c81c1d100700c0495120045d5010b40801c4c1c0c0c0180c0f0742580e901010f070411765580001403c003e0400c0440e20f403091300074121440d0b481c3c1070000202610002508000d000e01050002030360600001c00e540940e075442e02c030102c040c0d6012004444400c90300303900b141c0c1992175100181100381c18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 840892338 1250 840891088 840891133
    0xd020706020d080403030b1f0f091a030f0601140c0f0c01080c031602100e100509010605010912150615171b0f04030602130807050d0b0703051003240b03032802 70
    0x56455240c118a050107012b00000010303030042c900704154680300f1851007100d00840b41d1201c4510b40200894840b600103e82040c0e402c0228107101030002441d450814000032100d1120000c40c0881d4440c00010004440c108020780308850913113814030104055140c5411404184070741c5204460341d550301100e03008240d840b0064403094580250300405d0100d21240101a40a03040000a020700f5140000080025890344110744d440f802d221408410049103662995403071401c0c21041c804a034035003189400858040f0300c0d02010840349035180f880011650312051041c030249a00d40308100031096080e00e42d0b400300640400c246000c210110000712648050083c0c803141080244034035040039646c0d4680340060b04404d110301100d292803c0000d901d240c5a0381d0012046c0703004112502e4115101ca401031030340e04010500050580050145c0c0c0001d11b00203401c044141062141001c44014144c0320303c16204c501140b5035849801651034900b2140303207440c03402c1620445220224001e07446034402d90 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 840893588 1250 840892338 840892399
    0xf070f080711150c0c100e12030c0d051e130506061507061407090e100b090f120c0a05040501030809042d1a0105480d020706020d080403030b 62
    0x10003040c0c84400e00d03400c00000b046070710424000c04c0381d44a82103c3da90344510b01ea5040c8d01c1008004000fa0300341d03901c00c00f500e04070241207605022604040c0420070045008040c0d0010640040c400201c50108110f0762000035604070002e080103031111000c0c0320146a0781c54445141d0388007000b042d400607905200c5c01140c0710710042e030f001d094242034000070840e60f8198041041c078141d0724244804000c0003056101117411a542c1d81f592141e1030b13000310740c0c0c40c20b100e0f10740c0b0b601124842d4071441001001c40c008058600c12102074074007944074000c200c1250400c1c040074103480007d20510809092a62010403101003080a003400b1550500044030701c07189144190503010380320f20700d0b6084400c5c00c0c4007101c0884000d00b061814404174181c900300a00c1c1004100841d0100d40b410343c1c21504070800d003516030b240300524481250580800300c5680d0346120130400c0051017441c1d0000b031880e2021030301076121107480d95010302d55212070320103c0192100c03d894070f9120200041610100a00d08110b002114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 840894838 1250 840893588 840893611
    0x15030a0b01061b0803070e0d02030307110108090a05190c030b090a0b0705160201030902040209060f0403021507020d030507050c120a03030e0111070b090a0206030f0f070f08071115 79
    0x60500c01c0090481c5084030f400c01e544410b103865100029400001c0d0703540320043e49030a84e12958140000f440080d4207a4020750103002c001420005c0c803000ca440c52019503c203885800385034680302002c568600b001d10b0040d1254000c0d010717007031b25030420941c1c00300064000c0c0007003000c198490300c0c1c41c03100800a444000c0c00c0c0d402245090100003140600c95446107840c00c2460600703802000402d103004102070001e04042d5100580c00440d955a81500c501c0f0310041c02a0b03858210b0b1791324040083d4810700090744a00328044082042280030001c40e50b850740c0c003030051910f030240b603901610190400c0c1400c440d10b0040d10b080019946440c91032501c009800001030540c07400e10706022f0210307680c1c1c00d0860100d904060744030703600c00c3d450012501483da00840b140c0307042c1d43e100c01941c1001302c1c096009600100c000103000655041c440040e0040d40c0c140c01c81cae0100c0c0c58104041d101d040b10000d04030081168840014441c03401106103c01e1545c903141920040445d5441d468500403007100c0707031550074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 840896088 1250 840894838 840894841
    0x324020f040e0a141503010f15060210090c0e0c16150c0305090705010f17010906051302040e010e091c020607030b060309060a020a14040305011a011d060315030a0b 72
    0x1c00b44665440d0010907050b0204030030003040d01140e0800300024002220b5071103d0185502c252000d61080c00307103813000c00007080380e000d845000450343c422a202d5100103100390118011021614811210015030003030002c041c2034641200c1031010324005045000d241014017500d241c810140c1000d1002030b100782c02036101c00d0506c005c000b040300d03040d03200c00d02050324280410941c0c00c0d00042403420350b0000d08140496501d01c0100b218082c400444109131100761000010744c803401d5400c1481914402c0f6803110610305400103401c1240600c0c170960100c1400e0358010003c0b01c02842000fa006007208080d070f01c8002c15481400002010140c011005a20403410824079a50500c615840440300f1210640340d0300b040c81c1030b0f590310200070b000c4000d05030740000c000c45d45902440d030380300c0b170f1078003031201613444a45d81d007421402000c000203a41041c1721500b194460310b600c5000080c2c900c030049107290004107215400c1c0700042d040207002c602404044c414980d8665410020031130118401c0410303a140707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 840897338 1250 840896088 840896099
    0x7110607020d1106071d0307050a0e010807060f05090d080d14060f01020703021e2e030b090c1905160609053a0c0b0103030305090111040f0324020f04 66
    0x800034980c41e0740ca941c00400174091400d0b8005089820703400d0007114121180e2061002a05040c0c460340807542c020121540041e40900c03103454141220349840589001e90354901d000ea901c1440b105400d0000f074010013410b440d03031400c1058201094002d654072403c1510354a840401c480c0c00448404000281c40c0070005a03180040641014403001c0c400f9040701c525543c0400d40c03000d0301c511400e030070042c11181c1200c2900c0b09120343c55070309000591160034101c903e45c010b040ca4036000e03090300003c1c03d11072480c1c0f01d824012000d034040e40e840602d080c94110350110080c2c40c680c0c0168000208001080258031524038440409942b030b004030000207100b009858078601e0260640c22600d507618502040038203101a1440d030409030040d1501c1c401d0200303401c21040780c00c05c04c0401c0c001c0201107010008801c0c158960b010034402c02c2a0802040989209040345c10b20303006610403208008003216050000403100310488031700380c9288821229802010b84d40405907000a07001c103d4030000800c04001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 840898588 1250 840897338 840897347
    0x204090501270e030f0c0c0a0b070b01061403061e040e010b1e0603060d050a080f0a020615060d0b0f1002010c08070c080403021c0f03091404050f0a0507110607020d 72
    0x46003030704100400032080c2e036020b025240d0184401000000345c0102d8064040c00050002c13020b0000000c042c05156500c13101c000c0e0094110000560b0606100000450124000c00d07504003424080e400c0c50382140e5642040003000f144540c128210151280e4082e003081c1c541d1700038103aa4002c0c1e4000400c45000310b40500c55070001c02d55418944080007025102c2c1e60312607101712500040c00b924005040c0c400ba00f843c40c03034410400c600800c0d00d100001c0140f48500c0c504090a08024180d09480a941b20384582a0042c0d080c00314040d48420100542501c0c1c100542c400b81c1c00c85c2003c0c00c0c16281ca4001000035201d0820805201c0242c0d4542c80021301c20b41c2d2209000707038000741900f0a00103501d042d484681ca18050380c04004c0c019a1100d403090b200d07483c40c0b00540901648481d00704c40484461070014029041032040c41a85221002c01581c685003601a4601c070749c00300e034003110310343c0c0d42ca043c6403000d040090030490030b02590b50303000703044180e05200d61403007a0700340e800419035100500801072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 840899838 1250 840898588 840898649
    0xb04030807030c0230041503021209030705060f061210021b06070225090f0b0f040903080a09020f0d03050306030d14030622060321080615030a0204090501 68
    0x1c54001e450865030110142c60820791152140d190b540d12200c405c070b0300c10402d114540182d03c410142c207010b0142c02e82c1c990000d083c80b80303000030611041c1d216006101d0766805210001405078018034005440340c00da9a500c03e91042c4000c05041521112021300e03400d0102d05040e400980360001000420300c080d400400c44400d81d440700501007032401880094403000700032404070384660303d042c0140b05003082107600006843c40c11802c001e40051002c044005040108030140034601d01030f102e500d18030f8240b040109007900768075007040c19651038403003400514500800301d9020349025000f00b11503c0d50b10a4940b400c0c8a915002c0d540c0c00e2550401d4030341080110808104a4080300c0340d450242c80000f07482d085182a680f20b183d003142d0700380c50140d007440c605031009a107107400c600105008102c003181c03040c90207411340c4513007400d2601d03021104c80b501240c203150400c1f503400303036a14031040340c10055034400300d0700c4001410251540d24520550300c0030b03841490300760549026011030904401415 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 840901088 1250 840899838 840899861
    0xc051204060537050a0905270109021606020c031626032401021018031404050d140307021f0e220f0b0d030206040b0f04050604020402070503070b0403080703 69
    0x240c84490100a0a1000c102124950743c10000701040f0392403818080c895070000342200030025861480b85881201c0502007040c0d100d0a1050101c00001d2021490303c201e5031061030344841c040820b6460b4442c00c010754480611800d071444100400e41510303001142d21030400e03102d1811000002d5007126040b5401e0102c1c860080e000c6810014000104980c200071600425903244108298100c040103034140071003842c2c0036603010306282032500c00309a012884101c05200341c0305c02c0c40303021402000c2016806580103558200842d600303904003040d500b040d50f0500403030020469103001496804590400c0c0c01c100d0404502100250100c9003e0300410340114054068402c0305210a80b02c01c2c19030b11101401142003030713070f681c0c2d92881c8080700c0d150403000300013074041c090101140c5145402956040c3c200c80681d0521b0504000c20407012407000803900450f0007100030b01954413103408102c020341c41020f00300c075944420043d14000840d10000184180d0298450f03042510f01904040c0a0311180c0220 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 840902338 1250 840901088 840901147
    0x1b02012c090108060c070f030c0b0718060206012607270e010e0a021005070501060815010f0602420a150806181e0a110108010e070c0512040605 63
    0x10003005d89100c809440c6026013041c0c00403001d0703e050409442c0c0d01c00e10507015200007080d40801041c180c0003840d038442d52440c1564110030315a40c072800c0340c58401c28000d08100c3c0c0c20040c558034207000180614200c034070080e810f58030309075924441500c880100383c407100001c039107001402003084000d100700066105400b0007030000e1b400e82c950258a4400c1d0603802489282c0180780307003044510600c00d8656455106000b04541c9446281c0c4a55500032082e02c601000e0300c07031002145002e846d0013110221160f5800a00c1100c107000740400100c0c1e1405081e80c107560440440b004103024440c28001204460451448242130242c032140507501104c00841c819800448108100003000600c1c580c06040074100c591491035101c2e0342800d1298846405000e58080307007100c40107000205008200710702c196070b4540801c48440055136041000d01c06c5c070f07207140341c031500085425000d0703200c000e56a446401a110032803041c00140000340c10a03008500050000b0610300880712441c3c040410301c0c0c2d030640360f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 840903588 1250 840902338 840902341
    0x40305070f05090114210a0b040605070c050d05090f2805040e0a03050c161d2d06041b03090b130222020c1212070f1b02012c09010806 59
    0x14461904840d520326603001e000d03005180806d2003800d01e81c021050003150165050305416080092004006407800d039102480c10300480e281600a940500b21554010050146030b040c204c42900c858008208036034000c850f1078110801170303940510146445910b089095030a1000b902500c00f054095003000d40510b00c0c1020070002d018000031002c6034142d251a141b035032030024060881c11702ca054104000c03041044400892140002000c00d207500e0580c4500d1641030b42c4041d00c1078a11121020f40c40001000c920102c00b1011124101ea6404400640003040030324010380c0130500d42a0a41ca1400043d6584501c1402c10903400c00c01c0d032300300240c141100b000d42596000a0004541401250359042c4070a00741c05003101c8503016140180300d5001030b103103007816842e8401107580c050b207a00e845c40410710780000c18081c011507441085607080c1e614081b880c000d02d07441c940e0343d0048050507414403413184030060f000da6900588040c0b114000c070303203d031200588505200340a001a0056441d5400040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 840904838 1250 840903588 840903599
    0x31e08011e0f090c02070b0c070501021c050a03050c071505090f0f060a05040213060f050f010516080a120216031404140105091206040b090f01140105040509070b040305070f050901 79
    0x4110368103803400c65200090044c80010706074a401001e90044081600214440c902001d003c202c98085031001c0e000c0e16410104100700c402054000100007000ca442071081904192003030f4005030740088413904c2c549c039154aa03220004089018080c1c0420f140d1500100f002c070325806d014002c170341920b901c01003000e204420f4009407642c4004101e040c000742e885000401303568940e450b89091460140c003c2010503119200348450004500845001c1d0f4007609138495594860300441d00c550410b00108490318409a50359055544003034051410040414a41d032405030691008003000c0c1e40c2650351821031040740c6006001d00f03124003402c0c0b8001e0000e120410250a4008034041c2c000000d18246544141c40300020f900f81c5800241c1a51b14030407102000b04100e11202c6a40c00340e01410100c6201201a82ca030600b038030400b071060a0347c1c4a00100400c02424075030812900200900c069480ba41c2e1108540880d0b5081b581c02500c2c00d030310000c02041071146001c5103001401c829142c410300c0d5030410303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 840906088 1250 840904838 840904859
    0x612050618070f0e09010b060d02070309060c0809040b060c0f07170d08010902031b03090c0f04051603020705031b07150207150c021305103f031e08011e 67
    0x2407044c907043c0c1c8140400101d03442000c0d842984108002000107444601c64030400c4001e4112440c214041a00c0350b50100300c181c09a09000d5088c3e50041c2d645241c14104d0342070101034111314a10f150050701c184801400c03840309105603002000100c00070810640303020755040381444035001c444400d030820742186a020f9403000e64103064078141000580d1300c1d102c0310140340101c06141c1c111444041c001c018002003c0303010805400b06403040798240c2c800a1803004000c210350055903910542130b12100708100b0140a0740107030415501070000e4904042d500d444401c804280312024031001d4216003030a200015852400600494180c40101026414042010030b101108806802400310503070040c0c0c00c65440300100c0480c6400c400042c410ba06120300402c108903030501034480f403a008202116040c1022040c04000b100e260031319844040d60803000c080b04000c6881c4240c0400c290100c80e1030094010040c0800303d0f0040307035520705256141c03000d4403094194580681c002036010400400491020703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 840907338 1250 840906088 840906119
    0x50a1401030b090f1509010b1210151203111207050a03050f1c02030919080301090203090a060e0a0c0501180b1c05041406060a0b0403080d061205061807 67
    0x4481028140c1d101d00f50680d14254007122001c62a100b8450300107408400308240900406086000303004200d025020171030100896503007040268402050000081c4160b00080201a00d10320a01c80c0192900014041080760751003c0d004110210076680c41c11100300813080030502c84840b01070034000746503507040d1210b0b00400c000d0b0810401140c1303d0403004100080721032100c1a40caa29081c7d222003940040a50003c032921421801040d40450340c40c2904805c8282e8103901c041c0341403540e0309140940009410140146c0b415202d11058000021181d00ca08000345c3c001d0001003080c0c004030725040e0b4510426800003410045c0d848400055241d0b04403260095802400c1c07060f490780d00400c00c800ba1103804240190000e401c1809010900c42c1003848084103c08850a4030700769aa860b092000020382442911750f41030082000704081540c04028100c003501c00c50000c200382c0d0b1384d2004204107041d40d010903035a0740c2041c003d10200040c0c0041c01c0303804610301400362416a190001c0802c0b000e05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 840908588 1250 840907338 840907343
    0xe0619090b130e0106060917033a2009030307030f021c0806030106060e0604090c120212150f010c110319030807020d0c0213021602060418050a140103 66
    0x4540c004910320b03550380d010380341e180c200708041004402040021036010740810b104050201d202c01c41e011075030381c155031411000314110702d004601e0800c03c002c095500d41b02006250380794020f1440c0c0b030866006624082c008100324098007041c40c0500c5a10000e1802032004240c4c5041f4081100c90107980b40031058a2032184c150406030b240c0c41840000341c0c01c110010144200d544000c0002d207550342e0f0011841402800154020082e080c0c84100a44606403820221940240280001c010140494002d0406484140b800440d40300411054078184e03000508924100c0681c58100106095035220072112040e0444603140f070042d0740000039148090640300038000303690307420641c262514104001d003090811b050012004110604000344600015100d2000500542d80800c00b89031080d50944009a00240004c0402121400d210021b41c894500d0400510403418041c01584e40e1a0141c8010311142900352400505070b50001c0072030300000c00b5440021700d00400d00d44000c800d9041141540d9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 840909838 1250 840908588 840908591
    0x7050f0d0204200d020d1a030a020d06150b0307020c090f01050d02040608030a05031603060303020d12150620010204031a0415020c010f0c020a120e010e0315010e061909 74
    0x40c104903c0c0014980c81030150b0039a040000d004240e40a59034028100603501c69010044141d01c40025103c0d40240300740b0b16403503449204000050700d030078801e0014441c030031130001404009020395110984201e034413281030204003000300180141c0500a11001000403030f03d03810503107450810483e03100d00600500d030062090007000000c540740c540c80300c03010b46081d0341240c1d120848103000a05651048030503c864001c9105203030511402030003120150395058010f000d00280c043e20881c1c000a6045d402031480f5165080052803100701c0b40000050162940d07910b400840444001c503400d1600054141707160700c100800c0001c42c40e0440c00c5800100f40e030801d040d05440346e0a0a04004510003120314195100040c030030400321055005200d0003034461003d00c110f40410342d0686c2c80d4400d010000d8103207032540d03c0446c8060b11502404081c940141030684503440c2070f201091401c075280380840d520746d10742c000510100401d45907855000790704455545d8011080d10340103214440902c501200d95 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 840911088 1250 840909838 840909851
    0x1419030c0302090405010f1a0f030601030228020705010305070f0c08131a04090b0a080c040902031c0305040b0a1e0b21060709060f090e04080f0703050c07050f0d0204 73
    0x1d11039011038500ca02d004009106650710740042030340c0d0700c1c0e81c2c0c407a0100d50701c2d1180c4074110102882042d85e41c00240d2402143c00d41e07403404010b4010307520480104804c00d2448650100b908808010b1000749016076000b04609400c00740007404864010700103006100000383c400600543c048419110180d000b1049600d8007400f61460001c4500d60304401201d2201070554018440d5240184c0100c820820007400f140c02560300b444601c41080c00380c0c0d0b0300c94001e00484090303070a19402000ca461b101504903203410084035032101145180040c200c001949910901c0107100006080c1030304142c40810410040400b0640f842d0201c0ca00240d05100d50344440604003c0ea480c40c2030b004003005041003441c52940d105440c80d445403021181c200106075205404a1150300c1440d00f481d900720603444030080c403824110016860f07074004200b22054901000f420741000c100c58007501030b9601c00d40305c1d6a00c0303030204030503182414865000070780940c5800310311807070540d10040c0c10369000d901540d0000b40d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 840912338 1250 840911088 840911111
    0x161716140f0c1306080d051305040b0112200f090a1d06010c08040b0a0c210525051e0d0f08070f0e030d120b04021e0a051207080601141903 61
    0x241015070701002e2140200ca841c160301d290020020a507400c401c1e0314039000c0940309c40800c0111201c1c1490540090304c881c400c0c0b02c4544142d44107490070800301050b6031308d0072081076220b803556200c0601001414004100c007502d5061031100d0304003600c0b0003941c001c4102c0100108030b4000b07034000c081078100704050359040180164801110041c16030580016601c00507100040d1020034511f900303d544050102c080b41221117040c01e41c41c0c00060980d00d80d841c024000e50303000300260201440240e103c40d2294100d000510070400e608111074010b00c2c03941d0440c03030075a540d4144840300000c0001d2014000b054080143c0c42803000b5072105032802c2190018000000494603003c0308448150544608001090056000341601c401c81e403500d141031105031008810b110681c000c0b41c0740a00912000200d4150124901c80980b90704240e45c5805410a511840702441c5031505a0b00400130405040c18810b440d644842e82aa14402c41d1703005601d440046040c3c214031071402c0c035484003091b40d0350b03541c90f04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 840913588 1250 840912338 840912341
    0xa0b0c0408120304170910120605033a081f030807050a0b060d05070b030c0708030f0907060c23071e17070b161716140f0c13 55
    0x303400039604071500c5800b40b00b82c0340070980c4140c0341900d1091844200c004900c8031801142c142e40c3e405800c94410248803a01560280000c190f500c0c24561511004900303500c1c20080002500d04070310a041e4800b000c003110f22000c00349008040000316454580f268030b141c112004540140300c80e00600c030014064040718003204070301e1304004d1a1500010b401c0c4184100003c85000d480d01540f02c03424240c43d40342c2085580c00d40b82c00c0061480d001044100004c1d4190800340d83e011000b000214500744e4182d41b02105c42e4001c071425540694840240101c00d03800b0032050300504168184008000303100c2d200e02e60450003940c03120809207035894110075190790501c00b4400a01c0b01c4540700c08240814010500d64503414000d001c2038500080d14182c0c2d85a001425070116410b03030701080d25207105070100404011084500365984560b0900404140d5011401000104920104600c00510a01e40952402101c1d0b030a08020351102c02480c12114010503403420070201210740032040300c2c0d011100c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 840914838 1250 840913588 840913597
    0xc0b09040605120a03030501060207060e1e030f1b04020403020604090209030a02040e1b10050406050a02030c1005190603020a0603021e04030f050d090e011505070b0106031505030703050a0b0c 84
    0x40d00007500c43c1e484401c0c400000382402d425407098405001030f80c4c840e10100d035078440c2849403c0c00580150075044084c00c0400e0001183c4e0410114241e10031200404030b0b1400002d0080003a06038001d0300190305410302d0b0b0900100721001108d041d07150614640000d510b5026a000d00c0102e01d6002130828001d0740e04101c0000030f40c0d03014100b40502038007500020346071002040040d40c5291812656200303031814403031004165580303460302401c0078249041280c1c540c000b050840250b00c0704201c000014402000541460001c800020074140781c00051510500010846e5003046410b1000c148016518540003c0549556140c0161180104402102e801c400c4000021000200040200900480420b0745100c54029003c032a1307404400b80701212103000a114250112051900500c40401e0217030040d410340c2c24918000d42413003820b4035000d000e008280e000801082d6104c07640d1642629264030000108011005442c817a46103450302034440100c440000e100f0050400040d03240050401510b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 840916088 1250 840914838 840914849
    0x13080c011415040b01080609040303180515010f0902070c0302130b040e030306120a2f1320040612090305190306030201120911130f020a0e100c0c0b090406 68
    0x40c50075041100d0b801014101c0b01e9101c0e80120f0405040050ba9405504490b001e010090000c1d602e590320780d10100e00a0501d28580c2c503007444440400008150200900703003607003520712061047c2d545090340d83d103000d81080d480341e00803030700501102d00441e0800b11040100c9030160b840060b078004030f106401c001c003110005541e00c9850f0510030a9a40000070295110362000d8500601c84840a0850342d91130a469000806415940034950b102210080640c1144880880645a116581c00000d004c011000c880e103522159070744411700b2203804100c0c0782c01d50140c442c40d0007854035040910040914020f498201404d5850fa81c1c0802054446c80031900044103070565005c1c03e5801e000001c0c090160751000740c0c0051f0800038035108941ca503100d182d520f04d507c441c40c00382c201c0c404414480c3d40a45a08260301c120344c0d4980b684447c0183c0e0004101049103950307051030343c100c81d070100710b080c0041201d004104400790760b15000242c80005640c040d1881d40007100c1e03c03034005c5400100a001d02c0d4211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 840917338 1250 840916088 840916121
    0x8100302033a0903020310050c030c070213020a12060527061302040e0108060f16080a2901080a02040b030f0a0e0a03350c0d060305070b040302150313080c01 69
    0x1806060f9800b0401c003060b64401c406032100036000394090000e5030010b03203102244a81c2000825034030701d070b103400400f05203102034010050740000241c6003080307030440307003c07800440d0400040340e00031046880b030741e009080112010708407200510741203201022036008040b0881d10080125035650ba88444044003800d15001c00d5560310b44640413049507960078460030390b5512401c1e01003150489070018052055400e1a01200c528007070810440302203d001d48001c1d4025550030014801e5a0160482101240c0d0802059201003840000502401004150040040c418402401f040100c54212a00005e215003107072119164448840010b102c0456a10b10a100d103c522a0406401005c50704030201007800c0902001c9800003500b051141d00d582c0c1554031070031103000400704092540a080740c00d070788031000628075440382d640620384443d5070001d03da801400b090402c00c40c5809460150b00c00e00e0350304030a0441c2085500c40845c2000700400034a14503011461050407003003507204030b61840d40d0210707 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 840918588 1250 840917338 840917443
    0x3062625050d1202121804090201051303050607090e060901050d1e0605070909090b040201120e0703051b0315070c02060705011503030324210f0803070810030203 71
    0x600f0001d070000702120b8000344c0508881094050140e030195203441c0c84c030301c0004414030803200411000b032440c51000c030f041c0700c018403c00201900000c50940503601c2800184881e0400c40005040920194801e85141c0314036800c011036030302c40c0d142c00f904581301070312030b50400080e41c034194504e0440031a1030f442403880341c07241c042403004c650005401744445488518801d0b0302d82200205664600c84c028022079048400702d001944a0350741e0b07103e8011000c2001030f182c0c0c3c05d600d10505244182d80300760781f82c0c2c1c03250f41c0c0d12991503a41c030010245640d080b0000e00f407480d07900c6e40290003510024914401d1000b084140e40a54803400308440700b15074494020404c45480a00c04e440441c0540005d60000f40f50030340641702c5200600451101c0f54251036200c4100d0f20303001100d08412900051441e00020200d0324200003230941e24040302e000c0c81003401e5612403414210081200f1002001c84000e45902002000503850219074100009503011404440250b136000e540c80660500b021098601180752 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 840919838 1250 840918588 840918593
    0x512250302100c052d0f15010509061320040603090507050316090b270a140c0a0c020102070812210903160f0b0703062625050d 56
    0x1410541581c1c402c8500752400c00c0c071004100c4160a04100042007030703002c40c03120600040c1440d60603000820515031044413441d64116079080410741a914111a8001c3c80d9003801d107189400e0176409064241c07076413075181c41c2c20310009100700144524021869076503003850300e028180800b80400c40344200d407401d40e2240c0d60079006005101891040c1c0350360048941c0460980f5020807000000170f50452105503141c20040458000c004655415038402419007004540380c02c075144039031542c10308031546604c40c50507002c00d10a841c100e4942c103005005a600704500c0c1600d001c103445c140d0340e50b4603040703801c4546440140d02c4c3c0106900103010074411910010800390164004042035080c1003403107130203144558010b0308044400d640a000580051001003d4942c0782c1e95103411190041c2c0d0070761071042c03441e11183c0e00c1640941e00d407400262200300c20300c48100714103050340b444c9400100c82903e5601814500707031075074043c0b00d0043c55610113129140b08030b4080c034401c5010741801411180c0c008040d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 840921088 1250 840919838 840919903
    0xa092d060524011403073b030d030905030a08132f04020304050a0f080d050108070f08030a08040305090f03060a05090106080d09030b0712150801060909020a0512 71
    0x81151004a24041651200c154440e0000c0944004c924a080d415621401c2007070310240d88402104000c00004600e0092203031410345242a0010001115401400c1c45002d150804561409007400c0c181000e0908000541c0001121020211460620071035240c0e0078040d260402688070281080b0394004010004540b1100c0e54400a81c4c1c50b134200c0d18810082023880182d000840b00030b045500812905400714049000000525214244003031500c030000100748103e0310280c00c010004d41c00504180010340003040284003401100c8000c509201c01c00320020403240d00104001d042010100d50400e02d902c030080306055040005040c0c0b5800d180000340d90f001410b044400e007041e98200301000442410208610304140c2d03180d80e948c1035050440c1c0300c4420000d4060a600c01b0080c031280088070224051080700c00c00490b81450160581c07610b81a035080d2030032030f085454200c3c1380c40c01900050340e807003010100b218415140c2000c94120450a80e08080c007061041408078410284074001c0c0d41071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 840922338 1250 840921088 840921121
    0x13031406090d0c080d050c090a0f03020a050103050114040f021603121116140c0409112806140f0a051b0303011d060f1c0b0a092d0605 59
    0xc201c1200c0c42c115002c10101d50000b8401005480044100041c00341d0324800e4000c540e200e20b809130756914001100c2e002c80e6107441941c0c849902080018014011071a02d00903d81c003e03c82407806121550600292030510310607a41c12501c102e6072142100340740445501629194140170030504042030213410b028009603504c0d01d040030a00d140100c0789038010004801e03074181d0b07030450b01c2495400035266907107803040704007111101240c401c0a01020b81540c0354020000914410711001112042d00c0c2c2c00d01c16801d0007101c03a80401c960b2550000755162884c0c00e4442155220f1500000728000b035a4014214400e0317001548540700c0008240706401e8100300103040c440c48042e1040d0030381070090a03140d180d0001b0b00400b20302e0b201d0b4024080030907001026a41c0c021000424414034030204d8000180c2001c0b0650345010fa09a07070102c58814030108400c00d55010340c4d10070040c40b00081a50700c82c00a0603d0780070392325000c49000f000c85411401804455183eaa0100e01080726042652140904550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 840923588 1250 840922338 840922351
    0xa090f14160f270b0301050103290708150604080609030418050403020618010e010608060a0609090209070c080c060a06030b071b110607080d061502031c0213031406 72
    0x40c41800015880600c0c040d080483d851605100f410000d08403101100c22100462606115210100c022142d6000e103e10b42c001c52040008034000d0789106085040342c4100c0e0303c9101488000d03c104048a60000b5207107600611a92000985030310310030008a80e80215002540b0501c500402c105038107100200030402d8401c82042c100b43c6108000342c107000c0d1641101c00800580000c408200001541c03000303910484042000800c41c0c00503024001c0c00c444481d40910220381c021814000d2603240c0348115030140c00494010b00c00d80302caa4006c1401c03c500582000e040008002c0e01d82c0a02001c9004c0e80c2500340c404060352400c1c10400c0181020300482d0100b510301e0807411022404960091b5003594407444c44030303183d58000119403240e89070340300703031901c100e400c83c404000c2000003440c041c0041c2000214860005066820701c03400341d64003070b1108855410b540c003c00600c402454003000c4540134828819015035100340001001000c02113542c00180019912262101c00843c042803051007041c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 840924838 1250 840923588 840923623
    0x906012f0c030607020d030513080304060b011b050c1201091e1b0806070e0307051c1704180203101706071d0a06080916030f050607080f0a090f14 64
    0x485800c101070b1119021307901c22002d640728050b401c01d80c41c001d400c510343c020002d01d070a0040a5490321003811643c4200d904032049903039501c2c460000d6800c42140840640a810280c01c0442c19075201a500c22101c034525100ea210204003906104094201e080c3d40382c2d00c25111600b00301040c044181355841c11004981c90800c0741d01000400840d002d10b502120603101c002e0010b0744465409032144c0b07540201258050165000110303260b06e0303403000c1019000240740c1100002e941418118403070747c0d04444200100504200130046d08072403100080605941002c0103940b500e500144018166440e8058110714010725049103406c140405c0c842c0c8122000e44503c114017140c030010822640100031881e9000381403c3e4140b000d1481241e80a41c070131610402c03120790442d0715000451074403140e4001c540c04901c41030000c00300682800f019401c1202400e08012031308040b09140810040205941c986584e150100c405100003200d044500641080600400b003020700075040e00c800e0119041c7c0b4186 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 840926088 1250 840924838 840924853
    0x3200f07080f190e0301051017011410030501140f181f022206050a03020a0306080a1202070f030b0105040b010c14030d0605090402131e0204240302030f01050906012f 73
    0x71700307060044901c2005051400008681445142e003e0b4840700d10744c010f01596200394881300480508022809a0800c900400c403280c618500582134075110084a55490b01103018040e5016440480f1030300700e640d1380100505001e46160b45841c155854080c000c10100e400c0340354829030034980c000c01c03415007000350030151411540c04280c0c41d0b049501c201000500100900341c20240b081d40030304108100c0385000b00b5840d0b51040d01030b240014280d002e680d5142600005000107404120a000a046076200e4045203451a110b5103405d040520845000c0d98561007142c4460f88200a182207941d030001c41004003c1440c1c810316521703045400c0c02000d003882d051002c5004d141c003400440c410380c1c4c020040c900b04030180e0551005807030344458841c00e541408604664080090000c0d001810f80c4912040c84800c8070000d40d804401e0140c0c49600b454810028030440c44405c00c103942c1502d00035104030300f003070301c5000040340d00c40c24294294a44072007920824004ca20000c030300884e010310020889082 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 840927338 1250 840926088 840926117
    0x40e0a0506040c0903170702090114010216060918020909150301060501020c0303030c16170d05010f082a2e0f0203040e04080d0c080703200f07080f19 66
    0x110380c907404440d001306000240404c00944c00d464002c00c8403056004160408140d42d0108403e003030280c12483c03c8044840c0480c04c00d5a042017200d11440c040500c20720981d1600078081d10985150140c08441903c0700c04181240d25150121901018040c16072920f614044604000c00c164100d0445e1003542801030028a540c400201c100c4070500080145107552140046c040740790380b00014900c0071034044041d07100450305100036402c1012a0100c1940c0e07440750420590103c40c030582002c1c1c024132980000340003130003000855102c82050461011404654015950302444290b44502d034441f81828902c030002da8101071030600111104015031b03ea184070f200a850000b041103401006070f00521080101d02c0089000d290840c1c05844010b103080015070303160b0155078441c0d0f680c1c008a94500107010702251b1510844005ca05d1b0b580e561804091000d2100526225a105c121401680440c0407000c1c000d0384801c448199080191041e0b40311000f003080c0315880704070030700340d00496058100080c3c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 840928588 1250 840927338 840927341
    0xc030106060e0108060a0e01120506090601030317190e01090c09110909071b0809010f090503060a20220b0304020604090509030c01090606080d0c0b070509010212040e0a050604 77
    0x241c030032989418441800090044030500c000a20346680842400c00025100408124040c0605601c5140c0c48001501d81000da2601c00301804030040c40d4051401007000ca5802610400c94000c402ca05200700e40310f0b03804180c0c0c00c1c44e25070540c2c0c000320710342100c903040300c50154004804144135041e80a80d0540d5a41c00c03004465907040079461000040102480740e18180280b103500040500307060041c002030001c1020369040c40401110510310000d1148007660300250600341c000c2c2c1a14266440a042c000441d41b80c0001401c3e2240807030f122648800400081000780081015401016807542292501001c6880c50a01c690501041010005c5500c21080003168421038019212914061030070003144010300b00101307040800d0009210f0102924006e005155910f802800041411030805150a0400446088203018001034040758000200000740031540056141009034a80a0303540041c0c0c1401e206c1058030503803410002e40800c01c840b248411758001c006224040046a98241c107110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 840929838 1250 840928588 840928601
    0x12071817190f0f03050403060f1803050c01060b03040c0e01060503040c1404061e0806011205100e031201030c0602011803170a021303030c14010b180a02041706090c0301 74
    0x1045402586454a840c0d22101c404414140300d40d0558088800300e840b000008101464104c000400018040003841010300030f81c07138106000b00081002800114440d0f425004000340181488004251922013041c2984118018124040d14030394070700c1d151034603400c0d8000718060030038613040d000008240c2c1486401540d11a42e4060b0f13881c030a145c14a054a50205041c80c0c44076400b580303520010403070080700c050110018080d0410b2046003402c2000345820030070140c0107441040c220104000101c5c900280f8003080d00059100010b180e03c419081c103046110748070906482414110000003000810045101100e00a50003008001405c03907500041041398040a00040c41c10741403070081f40d000c81820741d04060f46076001403400d82c074150502c00d40c01c0c55920a50215243c0204003051241c4204a101c02c009454020000c1015402c006010310300151018021410170a00145404c1e009604841c050454a00d2040c800c90450246030340c0d40b001100c00217118005e82c03909420900b014040e0710b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 840931088 1250 840929838 840929879
    0x30e0a0f0b0f07060f0c0f120b06070803100801140403030e0607050d020c16081f06050303030705180a09051603090305091917060f010e0c040e04050102120718 70
    0x1145800c02c0d40300e008125811a0500b0750303805503240d401c84100d6489100d624242885030f2290300d140c902082020700ba2102c400c861004040c10a12552138541d201d03000c8a41c11540300385460341b00e40340e6039800044004941c003c014158a410b000078006a49850700a2165120355003d014a000c01031080d51503120545050f40410010300c030b1840302c2c1e00207401030b100f004020300459145a000101c0c20400390807503840701c1481d422443d440703100c0c808802d117152501400f0b1507080c8481c1d490040030964030301c00100f41008000021401000b10040c0d4990719030400e4000b4480c041a0b80c071603c00000030001955044140c01103401000310442c001e02525010907010707111903050842c414244007e5003a40c6414003036400d032500020868035404650b059449403500020441450100100d0031285010782016408845400400034400f02c20011981505c0000511040c0340d01d561800c03902901480c058284400e0b980c0c002c02551650044142002d1140101c05280a41d43d0f41100c5915001d0309809 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 840932338 1250 840931088 840931109
    0x4170d0e0d0201022b020d031a0d02031f0c030b1210050910050108060a060503031c0b01051c050609070e0d0807020303070c060c021306080a1b080307030e0a0f 70
    0x4404a40742600703003002100c0c010300684a41c6000300c80c104200321048086540c68104c0d010500a80680c104088200c01c21181010458001d56180c1800c840b031129111a20a50070049144110344045c412005011550340d807145820100c40301c0d0101030b00401200400003490b0030440481894820a0240d130302105e0805800c10600c02c04040c009010014104001e9220707105850901500a211304c5001303000c240083e05260620600780804e41d0300a90005200f070748140051400b100175194036032400b1154440000c1c401400e0001030b41c0300c2c020007810220340f1001c01000400d05100b90000b921602045504101c0390b91000c1003942d44089840c44a0b8100c680485604005035000c402048202c2c0001c1c12a801c0481960350380c28000440c2c0c025000040b1041c11007801c6086c0703031110300e0720001241000d00585080c007011641d00c171541c11000e05a0100790f40008148146103407410b0141c0b10800a499980490b4140a0014a50a00294000c1390f5510000440c900408244000d4901281a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 840933588 1250 840932338 840932357
    0x201150b1e070b040210091a030a0b060c060c1e0c0d0f0318060e0312091f09030f05030406060b030a0204050a08030309120307021501180e0f0c0112140c04170d 70
    0xc1c00040c0841e00902400c7c0500b5840c00b00311050341002d5224025400d01840d60f982c43c1c04002d00d02500c1d0030500e62405041d05219420740c01001203505a4080c110142807600c900100c0341329024a49003005060041c140018200300038100030440d081c001d982500e44004030000024200d04a6903a21800b0694120303030004000001d440d900f1034583c0200140880b03083c085144c2008042400075034501c2c0706903004808800c00c42e00840705032024100d00460410804c07229490203800d04ca49121880d082040001c001400c10107594800300140803840c00c22034491628480300360095229000c0c80d48601c02220b4005101e2030000226031050b041c0702d000e8840f00401c10f202005a0300060111000e600804221104281102d03480034001c1880d404510011003590038402c044444400c003668098014a20311003d114000400031061902072030503401c00101c44a40c44014000d002d0034402500640080c01044400b940181043d1040100c0c2c01c410000c20541c9103550380820290316011416515 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 840934838 1250 840933588 840933593
    0x8040321051603030f020301080d090b03070c030f210b0a0f0302030309040c090e0408091003150b0f040306021204022d01080a0e03270d020a150201150b1e070b04 71
    0x102039032840d03c030b410082100328003074070400c1c181e0701300741c000d1481980700e80803007100300c1d038482c0401004100d05443c00e895406c080100424481d01c804c0d020b024881c1c0640d001041c0c61150901852481514503d503642161200c0c50001070f10b81d04031054030840c02403002086a90304411203800b240d50050085141c10801014080505103504c410000c0c0585101d001032440001d40700944601c0c82040090741d985001002c012865605090400070940742034080c0d80c0814401c2050803da0b0000901c0075190f1550402010580c411034100600d82070003c074081c0141d210021a081c0142d201315680c44144032000d1840e000b0000d03042c040851680d528601105a500903203c240c0c1080a0340070123b60031180c040c405246510640022802007030b028002c482c3d146014440c410020350840300074119030000d800051407414140545079070340c2000820307003a0744c5000b54800400d6290090b58444420f5880360a440560402c1c28101c80c0e6030421a64156100821011035500503404405010a52500d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 840936088 1250 840934838 840934867
    0x7030512040e180a021002010c140324030f0d0c020a0503150f040f02100807030b040b030c06091f120608030f030403030209010c0c38030402010c060b06070804032105 73
    0x12001e19140106800840561034005848030006d903135800120380104080c00091880d61000d00c4981d04850620900c4203802680c0c05124604885c0390420729255450720000381429078004504280e440750302d140742074440c2c011420215440c02254140d41c455515003e042d110304002c100181c2c1c01d80700d44006180c04150b02c1440303401a02581913a0046c16050780828494000c9030740d0500880c96103400c01070b880d0381c1405030b00d45040081e6001d001046500c1c01003a59030006e803060500c550360100d9800c1450311604801080d0b042e00c4050500b500c1003c0304081c0c070800150380700700b03500390610001107240080082120784024000c1e68607071850f80c46071003c40094103d40c19150400421100c81008240c000c058000034202c21240640500510740006240a0585400c500d1100340024502c1840f20711406896000d6020f08240c2c01000031450f200000700440401d403a40301e040440c200080c002288068000c4d00d22540140300c2011b046071010184041200b408400a64100030b00c5612a000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 840937338 1250 840936088 840936121
    0x10b030c160309030b0c031f210602071a040b070203130e04021801060905030c01020c060409020f04180906050702010504020901090e07081f050c070f080915030907030512040e 77
    0xe00d0300b445020b861741d58070540184262a081c0c403003032010003446441441c6000d00840c00c011032410108040c642002101409401030a21070b050760f0a504000c02d02c034580e011902903561007070000040716000200c07034495640c151015110811280c0c00600610300000450300c4240403603e4407000c2d54501402c0740c00f000c81c001c10807600b14150142c01c0c20301d85091006a0f000e000241c840c545003504160602d813074035a40e00046811580000e40510468036a401190141c440428000d41d880843c904c0015503031040d580540d038000c4581d190203402e101c0c070394010b40c0740c503108010a110545031204101d00b65502520082c0d8016503c10040042d003843d42d02c1141c107100c844040d5030405507501181400c0640d00c0946a00d141d200081c48403c1c02040e1207100d5119044000e1107040036040c0e25040c86108441c07500402415001402e07215580da440d200109001c00340c3d1030300b6500d19010020f1a00e07120103200c101d0f458860b002c0a80082c50200c01641e080c2c80199181e10615076a40300b607140034000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 840938588 1250 840937338 840937343
    0xc06090f12170903030d0504020321090f030106030b0f0703050a0516120f090503090310271707060b03010b0a051c11091f0503010615030903022a0108010b030c16 71
    0x10031004680e44c4050001d854104d412180019407881d080c010b041c104144410701c0300f20f03c40d04002d5500081c02030810f444412009441e01a503148041d0007007401070510f5003001e40303002c4055003000b032508089141c992054030300d65000d11081c1c54034241c10082c0d80c001d5a848503d8a410302c2856445031141090190030298a2001714100d4542c04054044403140e50081d5407580002821a60b2820b0030000d1188000902004101101d11105c100c41c4003485850b10b803000135000b890b0b0109100300c0342d101e4088500c40c0400ca81d0fa802051400c10020070394a02c03441d00950800ca0026050719205024a0884401030030500c1409600790f90381e1020004030404072440c1c2c840c13000c0300c102a10340142d407922818000c20041001408428407108407240c90340040d01c0b0382c0c1812030902184100b03043c035001400d814100440c1103003080c5020f81c03c05521201d07a4a481900401e4401501d08018003500f092800380c0714641c0e1a6202c0100c3c2daa10300c001c956020040c90104040b40100e450482228001c60 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 840939838 1250 840938588 840938633
    0xe0d0605061f051806030106020a120507061118030d080c1606060303111501081c051e041404051003290a0501061409010f08070306030c030c06090f12 66
    0x2004910840c6482803040e05400c0002e801286400468011300070726240301c50201c2d8020305644c50140c0007961004091002001082c1040e0b15440050088080e12120fa40c000018000c130480f5203111900c5804c108144d21003403005030102c0d421824041052002c04590741d81c0d110b5603540e8860095400c1d80240342c0c540741428600030060118042c0d210b1b82018600ca41da5080c10021034510303e500c5c0005450f001030403c1900c900400c4003560004540340781142c41d001c891902a203000003035034280203031030318a5101d2064010010607089610001c1c01500c40051314152001c450400340000c9510442d180d00c3e807035452501c18408202503038200c2d9550020a4048441c0599105130701e113140e20187c600d100c1240d00d4000510110343c1000030100c02a1800c0d0686042804100c0001c5c4281d602d1941d00042c081010045074080b4443d800220186802c80300c003800140e5245800d008801c454445c58000690091000c00e0b4207030291030400c1103501083c3d500b0382048541d00c60900482d1425034072030301c030b030f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 840941088 1250 840939838 840939859
    0x412050a090902030c040303030509070807051003020409050f10150c021c0203031204050114040b040209040303110a021c081009020d021309050603070806220f0b0412020d0e0d060506 80
    0x42d07660005500ca008038001284e11186549409419948050000d0f4081d0700524018801480005035142c212401114203031100407031514198000d00c030301d03040fa6161a0a0800b04040790f6400f20034540203107103140c5d00800050b42d904950880b082c40c200d025000803c010200e401516110082e600e04442c0552403082201d425400240f95500c403d01144440c6011802c2009000d002c2c81010b80c50340613036a500c00c43d860207079244091100000c0000b0f00c594540c40c00b0a050611990000840318804503515a4a140c3c001d0081d5a40d003240c40c881e03031080c680c034130b2244c038580c4a00c14440c020307201300c200c281440d0700346414000030b0b4011000c0c0c2c20000c2e609229083d40d0b800e10414800080801c81400a8642012000e0504040154001e00040e0348048207211040e54618940c18058004c1c2c0c0400c1400c40051030030703205045001c2c0028014100020a00041c0403003060300b5070350031042c0c0e02240c0940329001c60030344080810006a43e80309148400300404039401d034000b40e900c00c000074501b0340f85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 840942338 1250 840941088 840941099
    0x40f1412061609090908040501050715060b09030613030504061101020c010203070504080105072a140f0606010f090302090a2a020f010b0d0221031201080d0f080412050a09 75
    0x1e1400440703010001c1c11000031842c4540c0d4000081e01e0141c40d030058180300301c0f04c95403a1000213118920400b03042000001e010018880c0c1400d00d200d040c030301008240201d40d0382d03044000b243e40299114074071a004400100380e155000e0074110044944c182c4031981070529000c400d45001c06161f0642c6980c4d5020084880c00d030314203200851150003030381c403055259400d04000c1c07803c54070001e003000180003030243e100120301c0e00010644074091000b02d0401c0c0214041c03401c1c440b03c1300400c910000c05e104a50400a59901c0450610302c92131081e40c0d00c0362081200741044a51086038400a500041440041040c00d0f0b0b6030380051054055119005107007a14181d0604480306940240000503080384041c0d580c0b20300c0a00405050b4101118500c3d103900d140e0b00064011002001035400c01d10310466010070350700041c4290303138942c0f00f00c0c00784d2807180da52018200d03200c2d40150140400a03c104006031a56030141d80940c0c0541d0b0016480320104140c00426980c1b039001d80852028050008400100d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 840943588 1250 840942338 840942343
    0x9090908120f06010c08130906030b1605030714090d050303042301061a180d0503251109151504051e0117040c0302060315090c040f1412 60
    0x21003845650500c0d56480c28621461500c20007820024074005040244002603a000c0011510b01da0040c8841e40d0b1492071a6070a510014240d1100790300741d06016000082c0711090500d00c0c4200d052400d0000f956000800c00c80300c070300c0b003250818089900d400e420b01181032114060100124040c00300c0003c81001d4440501e0341d00100c03001c03201802082211500c2c20310490541803130301c4010000388501428981c400079002001602ea070350070030012500c2c0c2c01c49a5604501c910703150003d850301c0495480c5043c89034a0750301c5103a400280b804d141d050307481710f5003c281c0e00112464001c1070005016405500b0010030800280110014010003014100d040e42c800c0801c14025203010710302c5940710300d4413003403080f56400781745600c030080c1d0722003c10841644c02a07100e0b4620500744600791140d684034549200c0040042d04040c1d00b058000c8100041d000c0c01c0070503610320020450f0158169a83c0191158043c81395020340007800f046ea940c204103010141144645042000744071074010515a4100303817 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 840944838 1250 840943588 840943601
    0x160507090608100c0816030f0b1903060b0a030f1e05010c0f08060a0302031f200705010b040e030d090f0803071e08091b0102030c06090c040e030909010506030402010909 74
    0x40b007508282d20b52010904035114026280405040c100c01d6450064405da498640d441412400d06840c1da015204030080c0d42e00c41c9d11003501c02807207003082d21010032210107000345901003101d1042c0b60011100e080d191512440003220b0703000442041e04036040d9100b140c114840110703003444420003070000001800078000c00300310080315651b01d8426000090300032b10b031281c080d04250040f02d0451f410f0000d80c5000c00c01c0815110f03d091050341005065510400401c1c480020180c0000e22602c6c422101044030014140c0c50f00800007070128403a5002040121000c0348214609a8410028807500c001b081d040300e2109805211200c2601c6150740704d0079440c2e0310850b142400a64450140341a409100200c9031000716075162049151520840e26650340703000c24022800220198158405a031003041191040b0200074155451810641038442ea540d0324003070f2180c0304505122900945070000400e54041000003000345283d40d04c4c20040c004290f2020340140d040000c142800f052841e141d002e0702 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 840946088 1250 840944838 840944849
    0xc1b0f2701061e1103030c2506141f05010e030a02191505030c07020d2a06201203041109090a030305100302010c1203020d060902030603070b0a051605070906 69
    0x640c040707601000810000c0c1c24402810f0103000001403100d00c42e01001042d01d034030243d054013159856408000c09004c0f114000402005006400004801c00025070840038803c480036410700d2494076081801c9114910f501c1043d61456a880e0f030410840d8440c410151000c50054291182020140c0101d0482c2c019810710409003032410310200706440b0045010440c0d1101498114154144030b08400610711031060040d10500d040d40c00c85007030141c1c80c1c4400c088240c01d4066107038400301482e5000540b84140c4158000710b0002c00c81e024103514945803c000751200000544003205107282c0055454002910a03108001c11603042d00b050740340e005100e80a00000f10041a160046140003026642c001382041c1c12a00360382000c00040c0d0f042780328030018540c0f01e12401d0040b488904d04070000d0045403c1c8401c40344c02c1200003e040d4503070b030f40218041d120590607504c440d910f03108105203034070400720b0b1030000680401c407111614071000315580d040b1b03104500782c40703401d40e5800703007103040d1411038011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 840947338 1250 840946088 840946097
    0xa060903020a06020307080f030705040b0706090605100b0418060902123103030209040902030102040f21080906070314070b01140d2d12050c1b0f270106 67
    0x500a42c40c21090351001014070340700a616001003960355006c11b0040801c02229081d010000c80c00d01030040081d070303003e0682c4035035258603100c40f03084c864080c0c00041000c2d02d9540c0742001043c0d039481b080700b24200b510a040d0800e40f60628101720b101e011804d01e0b002940040d45c0702c10115441005000030446c0c105c401d120440f0b80d00b040041c0d030007400400d541101406004001010766186440d40c041285034043c20010703164100080403078040c01001c60029819440010041013650f046c54002e0103860102210512142000e940015450107069000c6d05007001404050f09600c0c20380001e06080d4860310703007122080e1500c80d084040340c01c210800c45501c503801c030040c04148540c080c062501c0c00221050840ba0340b05442c1e611400d5036680419248851155410441e844201c0c2416a81940300d601504202c02c5045d009250360007007050100f4a001c0d01c9520480898103178124440a8402019020b80d070010740d040040810000c48603030500012034221860480304900c856000300324623182d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 840948588 1250 840947338 840947357
    0x8100f0507080601020c062b0c121e050c0d1104090605090405060f060a0801060f06030c030c080402040c030b090a2301030302071809140c01030c03020403050304170c03030703180f0627050a06 84
    0x100075055101d0741c0300130b201c401cbc0742c40d8010020b80268110546210404240003c0c540c48983c05103202e0700c02c80d03a541c40c07102e0400c44107545071358501008004071514403c041020b40e0b01c0e4010016080800d59000d091544030102181c814221580c0103504044020094440705640f196981d00f5250300303a0100343c074240d0300c610401891382c150248001c0c500703051504108600782c4c80005007103014040c0c8041e004641d5501c00324441c0d4000c0e0701518440100070140c0c40907140000d4910040d0100c0c1c0301419019076803180c0821201001310003541a02e5040d006804402d0502121034200344202000200b80d6442c0c182c0c6101154044030800700006142c4064000e2229100014003900e100b1007000003054410402040420f0307011050320285c2c0d00c160310306002ca800d0b0070000c43c074159454040070303030600000402c03400f01500103448040c800070340b03020401c009564810303a400040c0309111301000b282a07609410810b8550b030054000072007959001825170354486021a04580980e00200041024081c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 840949838 1250 840948588 840948611
    0xf05030a03051006050a11120705070510090f0303030c02150106030504140609120304020303040e100e01090c081306061511010e160302061308100f0507080601020c062b 74
    0x800303601030320041c041c0f440980b401354000c100d4818440640100000c0c0840000548018082030462a1001c4441621000141021501c136803143c46564410388802c3ea038080301074000c140321801c4410100810802c0c81c59078038280d001c0c050302c0352440c08500503c4a507522441014810038060809940c0005041c50985007500150440426010090703003d1410002400d10000b2482d409a0f0710450440c0c407504c3d2413000c00c5c41c3d4007442d0442c00e8100600c06c1040710b0255a600540101c466500c4107550b5640d94a240c0c0c01251600d01c00c4000207036510001400e40a03e010b141c11100344985c000154590f5265510800b0110340240c580c001445100b0810346002c090240c140d0315030106000d03001d50807540316840c2044085103c004e00480012603c0c14001c5101400c15008103404025525040580c00f4110010800f83c94100000d030f1078000420031843c0b0411a4902c40d9006030010045900c0e11000c010031070304416002046040b0f0300c005109400c2c9000e2000c1c0810600303502c089070444040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 840951088 1250 840949838 840949841
    0x619030506040b0604090e030c0703050c03061806060103051e0429130209040516090501050a08160e0604020d1407020c0d080316201f020a05030619030f05030a03 71
    0x501a24031403820700f00078103d2695640212801c540c40d02c0400229011480031060450048640c40e909138055814000240140400c0c3c44501010440960b0038039510b46540703100060004003603000540c0305c0d20001d502d0f540664006500008558502d0342d401e84603006280f40c680c0212800c881c000c1c4c002e00d0316910700d080d42905105207118800ea00304989400b416182c8540050f810282c41808800701080c10310000740010009403000820362000140c4951000b0054442071127118041e036244000014040c40100f070018200c191039844c90021860220840c4c43c13400041c0a00b41c0c09a070030081c501031174896200e41515550055508005803410307180190134803918107141c42c003400e000141000091881000c82c1d5101d4160711015149111050301204e60b00c908020900300360390040040c44055000040106030042c03091800100320212500000c03c4e4024442a50003244c010b00c00b180141c42d210354007680e01c03400e8002e1969515565101c20308003000710f55003907441c2e030000901101607541c507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 840952338 1250 840951088 840951091
    0x4090602072012151f080a0c05060c060a0e0c0303070c0905012103050c01090b0c1902120d0906020d0624020c010e270a06061106060a2306190305 64
    0x312511030301c60320350280294451100070854111944030030300160b00b402c80c10394041c0c000c1400d8404000c4081e00c420b6002d035200740c10031f030656030400c2c6241c00082c41d244c1181201c40c2040e004002d8140380e1900c100c040c0c0500040004103201d8051000c0101c5c1c0c6440800c007822106001d445444862840e1a00742011140c040e04440d401026451100c0918002190084000d81d49450b050743d039104600000c600622042c840146024850400d000340300360100081c080e10940030305811403c0c41d11800690b43e406038002c103c603c0320410300140000540c10b0b48540d041e01d00500b80945010489503c02003111460f800c0280590100321034440782d540e000e14596074000352800101019240b40c0d00203002c0c2e00d1044285d62091034922852603200304a200d5540c440199843c2088043c00c2c040c800d4400f8240c64000c0f103000501c0700d680c0f04444500020b01c540241c20291000b40100d0400984410a5107104000b02088010288121090322104014505403600d800e1090200a103030741d0003010f4410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 840953588 1250 840952338 840952403
    0x4030c182903120c010c030b15120c190c05061003110f0d0b01091e1e051e0c031e0f070c0c0e010f0504110702130f0b040e010b120a0b040305090409060207 68
    0x401041400311280010448407550700c2b410100070140d03034101c42c0801c14400c2c004124041c0c1ca01110100c98107070007802c08001d02d44240181c0d0768582d0344888000010840b0700c0050054512a14809814107041c1c2d9010f18642015107083e025a00030b85178020300c042e0070b070711250f0200da07650b08071000c6101030034403030b591042104020700c40703a410140d4980040c00fa038a8405203541d44c1e8008200300400c0082c00000080f02c11000e0394a40c07406e1000d413006504110ba4540c0800b10080c80c003103100e01075030411440307a99100d0002000340c6170b0100403503040400303031000c485141c1480004a0f0468070040814020702c000c400b840b880504040520081c0d031425170b04030398071020038481031006940d0012040c4200540c03860004001030510520409401501c00705900705281c00d201d52292001900309055940c0181c480384200c5d01c0310701c4c103907a840000b800c1c0609030b02c85000220b0002032203400103050042c4010310200da101440e488542c00c903440600c003102e0722216014140394150018031a19250035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 840954838 1250 840953588 840953599
    0x603060f10090b01030e0a050c090a0e070e10030c080607090b0a1e05210a0b01020316062019020d0908100e1204030c182903120c010c030b 61
    0x400e01e25506140403203020380001143c85107518580307644a0340c061200305000e60201d030f00c01030300f504040d0703284e03003c500200d4018488100000c904900b1409010002d01d030f80310090030f2140c58884241c0c101100a8035480492100c100004046149a00502c0142c00514060310443c02e00103000b030000c10490f80000240c0e20107010b07070010301d5000f0001880c49440002800340018201004940510a4040c1850141c0b07031095041005c1c1c0151860300e109030900f050400c140000800107aa89000d101901c2d190b0510003d4401c0000e41c1c0c0f0b030441c061328048406c2c0000f165010740900642c40c0c210201107410001c031203491811803541000080340c00356072030030030000300c17400d100406403141c034584424245140c41e0740321062a00c004002c076041d180c99120540361a15103070725103070b090a151480f980b5485060a84c09210031800d91040340c8400000340303030101c02814024180780040101d80c00407945405940245c9402d01b41400081c06508800c000000d00c50b4051800601111911051076002d01c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 840956088 1250 840954838 840954841
    0x4081b01140103020d0c0801051501090906080a1b0e010b0a26010b070305040f1d07080f0f1810020901030617060106210f1e151814040b0603060f 64
    0x1180612030b0550341c042c0e920342c94403031140c03d10b801c0a00b125400404a5031a21080129141d880d810400d00b900e0240e9074181c00d20768440d403600c1624880c3c007400d00c0355000b81480100154008001c0313060024038003460029240c0d01d004141c0d540000360701c40b9100450000d03118000d264006080704010032140305940101d900600c40d000070010500440d48100300000b20031041c58020030543e001028011303401581d00b5104d07020000090305401120312a0500e000109003911302501e00644a801500910601e40e51054820a518540680101c3e00c091014002c443c041c207003441400c2102c6000c0c04096910f1000350001021070b422079105042140b403846400c1e59440c00490080d04485982c5401003d0000e0198a41c20001c100c081141c08286400ca0154107102c03590440e508403514003061441c915070036050881511150100072120000348d1800384048200443c08010100e09100b0000341ca115449a9800c480d01c00d40d0241d03010f107106030030000300b4601080000d41c0011581460f190300d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 840957338 1250 840956088 840956111
    0x5160f050105012112080a0204170d0224040f0305090d0b1f0b07020f1f0c0501111602040e01020d0e0a0b0a0c0c110310020403211b030309150504081b01 67
    0xf41c2408568045c1007040030380218a8090b1550156130140c4810364050b5402c2d24045442541d9a0031858904058003c102e5001d158803034140e0540c03060202d0038034400a0390740b1a61030ba01d0207041564220284034060001068540700c0841c038040540c407a420b2150642002c0181c02d200c8140101d402400c0317450716800344001468502074404c003d0f410380c5c20411410704003000811100403454201d801c8070b50151203812990384160742c03c220034040e400801c924012903101e05039070310522015205101141380c0810043c00c2036440001400006400141400e61408001007955401504806181d21003d011400d018481c640b030794011000c0c100c2086001c0800c46c010300103a1140c0800f9103403a01d82e8050402c141c40600c000718510301000b504540d244c0d201c2c502200c0641142030481954088545194596030040038095a0b5076180344030300185c11060b0b90b0890140c003003400215120601030104401e04681400344c0750050b4071508a4a48030400b49283c40f42800401c1d211550030303810401034201c0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 840958588 1250 840957338 840957353
    0x6010f090b0402070512121003081603021c0c0314120f040302010b0d1a1f1a0405060409060503061506041a0c060108070f0f0e0705160f0501050121 65
    0x112640a0030125008281c0c500290082c080c90308041d0050003014581d02120001d0307030040640c09903600b0b0041c1640c455100c0010300710181d0200030700d2840104035046101468005140c0810711a204940b0001d2138a02000c03076180b83c1d0841180410403101e210390405801c844207800319031511000500303003400840c030908452809081c0b10000030038180440c2c1414801c0d003014550040241044485401520b400300c0136101508015070fa00e4910f802281c1503032201004548448010081190518144000c6042c0058801400c03444500c0400000079035840e00c8000c3c000510008000280e8649450300341414041c000700101c0d0b40c18186801030000383d0f500400d03902a61418481c80c2035550700b02030440700511905050401d240304240000a250000241e420103940c6202c51003108169103da080d80f507018140515040d542e40540080c003201d2265014060002080e550035002c00442c1c1c0740c050b4407228058003603c1a94458005100c081400c4518010a01c41810584454580c6484844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 840959838 1250 840958588 840958619
    0x902182e09020a02030705060c030a06090903021c180b030708180a080901050412150b031f0515150a0e060711010c020103020405130914010209011b060f02030c0c0f0601 74
    0x165450b50204903c50840d10030030643d20b04940c0001118a28140b20a90000580044640b80041c40c1481e1000c034001502d40640f085c50366140d00245024a100036020401044441e001c2e010400100000045a01c01683c0c1400401d4108081c6030b507810003410042010000804035010700c0c2d480905080000030000c4c1034864190412041900c440d01840100d40c036202d507030300c610401c41c00d61407800d051184007620645000300004040001c20150414036407a1120b410610190311504142003080603900e4004030303449174409089404551081000800c003111207400c0e40001c00d40414259001d9410581c014141039007111000d0400303142e940c03000d004101c440f40841c1005002203100c001c590181d015200a072000401100e032110704080b0b0f84004041e90f02080d100c038100c80184072107011041c82182c500a006130340d402129600d40c04181d941c0b40c201807040320319130755540100c0e4460303c41d440514040c512042c2d40e2681ca4200d0840c1c64602b00100050010130b030004001000907415020619 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 840961088 1250 840959838 840959849
    0x10915030f111801110105010f030b042316050108010b07062d0902011d03060105120309190311152a06093703030f0902182e 55
    0x100e16800301d80e010601922542101d8442414003103022040003049030341e004100c10b02130760394140d0040a03042c0d0f2426503500780701c0d108410b1502001031002c1039045c0b00341039015014001c00e061320751b40000403203002007072081c5424058020080a0303180000b210035400080c442440c01720055414104e452405118030300000300780075601c40016542c0d40000384000c01040f4020306800030b62070205151005840c60620890008880039125038048000d0f41c040642c1c118080c00400e0079078202018001c082d11610b060f80194070080c40010595a106460850b011020b1241501490b2035890501c0403840f1a042251240d038100b469400d100782110244e65a1a20305411402c0d0740b15100e0001c4402c0300300010059541c041d0381c08110554100240c189211201800d403040307498011081c0382803c00f224064141c107011101100c0020a12a400100250711040300000e40951268005a140220000c2170f403020403c2c58100010000c10400307864900c0d80100c030705940d0015a0300004203400c00381c01174 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 840962338 1250 840961088 840961091
    0x1080f1009050c03060109020d06061b0308060604090920010c110411040b07060605011e020330040303090303051e010b030907080312100b0c030a031d0d110c01091503 73
    0x1148240941000f000408010140a854103540c6031850640a0750003200440320450420000094081c070811003600d805400e00030440c50410541d45c2150200000382c11070b5440101880b011821240520500380580e114004000c0d141da083c0c2e03400d05980c1e118900d41c40c1441005603110001c295440306100d12000100c4000135042d221041010141c0290740100d19040d801280103410002640d202030160381003601c514000e068261100840310503813030001c0006810501c000b40d2005003065500301004403056042040500c8080350904bc50700c129015030000b92504400c1c010f142c1c0600c030b5107800c07a00400519081510800c1507800c8081c0c10312404212000000c00116420300500c120b0000e0b10200c401e03a030b83c80749244100341504505460442d6652203031500003610310b4558044511001d4082e0183d4104160400260020200881c1d0303121581d240490100b040c0805218103c1600200d031980035400d41e40000c9245000101a8041c0c140410554140001085011009003103155441c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 840963588 1250 840962338 840962351
    0x9010e27060a1a0408060f060a06081308071203050c030c0a1b0f0308181b061c1503030e0301020909011503060504090c17010621030203090d081201080f10 68
    0xc5104000c0e50360202180c1c0da00c0c61002c00030f80c9108002401101c00f4082110000e44440c0030111050030182c0713419520040c0041d080042a016040156005228160300700300c034140703030725800801e0f440480100d5800d0903003080030500e1074140c4940c0c0d400a8100c131086d802c614040408281071320500c6010350510980c50942d400301c007480c81c404071200b41c2c00810701c0c00401d110b14010f05182d0043ea0706802003902900b4441c07005000003854441e200b101601c90581c0d020500c28402941d00c8003071800440c42c124181800310204a01030104020549803800c030b50b103407560034010a0001c00e448c50324031913401080b800015a5803a10014150b0b00c0302080340e020036280e04e00070340082c00c171540041e40050905400700248035500e900e0380b0450b003c0e24803405001d04224152800c071405802120302c0d40c0040c030f48a4200580340d49000e400c5c0ea209004491400c111980007400c1c80f00a883c1c221590f410000382052101048030290380102688001003040e020040a0962214188208031a0b016658031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 840964838 1250 840963588 840963601
    0x3030e0d061d1e0606010207060e030307050d0f1101020f0703080601110111030114060a0807210e0303010510080705040b03041a0a05040302190203060a05270309010e27 74
    0x42c00320b8070030740706a807044544039400d4002c030382c44036051100110020b2600900e815100c01c04200140b2605059001e001010300340031b801d80d148200407140a07007502c403c7c04200d0000f4000c2114100b5810301c4e03160443c008502070801494110204503071820360f401800300d40266229581510340076681030a202407950b071080c0041342d000344000d1003013a080d0700f8409440d12000d01200154180d03103900d40b90800c8240b00200713101d083d201c0c880d200d0300090482c000040071544541c007503421200707004000c915511880c0c0b84c0c41c0140d80e000300c5201540c4c0c000200400072840c01146400c40500582030140c000c3c54010406080e0340242e2091700407a82000000604110b8000010203842401000624840c1080018203001b004103e174106d02501c00d601d046400d50340144206c081d01640140142000d0341da1900000180401810385104101c682080213850200040d05042c6641080000c603210483c100c0010002003411488038021003003e1400c401c4000410060801508100e00b521110341703500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 840966088 1250 840964838 840964841
    0x22107081527070c0219140a081906110a030e070512060f1b0307020d03060b0c5b060b0a1b0b07090e060301050c03190b0a0902040e090703030e0d06 65
    0xd00300030343c801c44a800400e1001116030002e41504c4030b400c0f01f8201c0350488000d1210300069030244080c650b05c50540c4944008001c07001c0c0e10140d2081c6004a480c00501203541c4d00d941101c0810b902194589402030400a0200824001000101d8240e603100790b04a903465120b080103020280e000f501c410014040c40c40c5140655a0714226446c820380d20b01e00890000d4841780c2e00a00c94000034105200048c501c04000c0c1034554080c0c3e80400b400195901224542e4002c1041c80d1001031082c41e100c40152034500d880c030307490951207409810900381d41c0120101404021020000145604c1c1100502440c0400c1056403e8980705091078008940106004c3d1079090f54410000c0c0b450303030b60208024038294490020740803528090501d030141d8543d00704041c2030390002c50708000f2070f800610014031402d9001e208842400001700b4002019100100821540300e4150400402250009810000303503c0c403100c0f49600c144114081c00804d4290b40e001000d200a941c2558440c8021414450038420203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 840967338 1250 840966088 840966107
    0x42200a08030a0e0d020a02030d050a09050d05010e16060206010b0d140702070501030606020616050919120b071701150e0402070609020411070c050402210708152707 72
    0x5000152645000d0b10070b9000f50042c40074010b414000c903101c80703040d207000150343d2070240c0c0e00402414009010050132199600400170303960800402840c0014035071a0a07036031a0b40d080c007450000c1801d0f010040002d252003407240e0314000c0742c40d0348041041a281d0106807141510880e8000c25650184000700001030200c410036480106000814010342c0c50700065004101c5100b0389060000f1071b070b607840070703a240c803400ca9031403025007020a550424070384901d0040444040040c120180107a641b060800c0440c029040100a030392080201e80500500c0b005840e400000351800c0c80400d8000e0368000d950403410310071107160502000400c04420b01a61a400d03007406c024104540362261414240040d005455050740100d1502003412007544030503048034011504000b0507240c83e86060103210080d80030084040d0009080e0f14003001c501d0800800900402556450380118100021100b680803641190b5500c1018040450301e5040d440d00320601100301250b40380141c540c0c4030101529034070031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 840968588 1250 840967338 840967343
    0xf0507030501051507150507050c0f0d080105090601020c010f120c200111031302040609090f060f020301230d0b0103080a1407030c02120742200a 64
    0x141020004025032691005040b20300480c0d001e50501e2004070341a0f000c0c807518901802c419458403140c5807503881c0760005900000f0038035000d840c200d030484016003050854003180200341c01c201110001c56070b0011440d8054041114040c0f420b08202c00040e513182c07048200141805142d00c01d8a000e14095600e07944905c2d41d0755030601c00090a0303035000b0140d605200c491042d00c000d0152052810030f052043c90101e0007401111840d648901c1900410101c1041d0100d078003c2d00c0e8000454206070074020600f400d8450003d101c041c00f840c0c038000d42658108046410b40300c4c41071004024000c0128040c40700c0041e61807001c840341c01c0002c0464910780e610300c4040c01e20031241000004002c00c690041c5600000c40d603820400040514401505200c3c90760b0281c0020341410380c80000d4034140711000c00080300182110305c820b594003c0b0030b0030500072600e035540c1c00104103100e0f40c4101c105950060341c0c2000c8c0b8800c1c3c81e210401c250103480040c00c3d00280d070440140d40362280004c0c000b044410680b94 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 840969838 1250 840968588 840968591
    0xf050a2c0306090f0f010b09040b0a0f0f051905070203091c050f0d020f010509030d0c050c1209040c030b130917030411010e0102060f010e0c1c0506040b010507050304180f 75
    0x10f00b2004003a038810345107030280a00d1140c0f43c2c601e0110380f0107100d50b4804000040c12001c150f101c0b40c0390314558010242c16518041d41d00c0304d01c10b060301090b01c105a68a00c0020300440d40785002500c41c40307440000172400c42920308100402401c1039021040301c20101044929041d000c20860070207100e400100b50040841c49150040c0c000c0790000500ea0301c004200d40e0840b203501060720710700c90907a40196030074003580d4014007031070400d0a8a40c02103000d05a061500fa4144100300798043d02d09440140050307607075040000c010a240c2841d005030003511403942801d0120403a0b600c0400c10012810540d103444d1982e0721208000c01058004112000c032000c00042d4030780c102824142e60308081c404000d80410280780201003503500109005205100085600390aa840e01030030316058074004001e20051802040030328400c0c40500111245440601000a11450081d0510003140c0c1140c500c141404010f02024001030800000c40d0b0949506102c600c3ca480c881c40a0300c1c020301076019105060a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 840971088 1250 840969838 840969841
    0x4020705100516020304050f012c091b03040f0309030203100e0106060e0f012a14010c0e15130306060b03160807170c0c0d020d0f050a2c0306 62
    0x100024640c001da410064003002103881d45800540000100034040000da041440f08210fa8074229051003511607060425100c0311003481c0482409100303c507400c1d04115540c40222101c1e0400c0702c5900c0e40804102c503c8880402941400309403800018030003001e5441c1d292a200425100f01c00c8000115405400c86400302038030480c102c007415600040e40b01c15844d1000c0050110b216080e00d0711410005420061640c0184004481c810024060601748000e40007454500c0008004044601ca005400e1000368090540c50390f402d4031080c01850b0100800104102040d6807030282282045003807050141d560b114000d404140700c410350348050b089510300440069408a5040218891190350300d10001040c28040d041e0ba14240994000c400110642d0340c0e4005041c4000c40c541c2c010340001035103810040e5109207a442c08081603240f200580000d800d0706410307600200d40c0301000c00c803070608a083c540d000030020710001706588410720042c3e400445007c01c061400104807806000b03011340d0070704d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 840972338 1250 840971088 840971093
    0x7170102071208040302190f02040e0a050d0e0109050f061606180f06051e01051201020f0f1222080d0e010c09061814010818010504060b0906040221090a02040207 71
    0x1004000c4130300781d02600403064024004601440c007450255888a05c95014a40319000c0c03000030108803030300480074880c5d101303030070302040c410000d110a103449503a0701c0520143c000700040810743d580e80f103540148210408000316030340381015990740300100c0e64103600300c48040c2404405003179203206580c945508845041c2c00d000e00311750f8401506001ea0428000c0c3d460302d031641c4030b01c03c28203000c1c12004645000148018034003800e00c940301ca45071100160409400900c0c0c0b40181c4d0004c018122420300019164070010a1000318603480119107046881d0040107a0403175007840755140c170086c89948000340f035490740001c50344007c0004036148020807405858200c042c02c802e4150094401050300d90351000491b022a07506802521104041f581d000062503005540201e800f400c510b4003540303140c6402148040920910384120f004a202140780301955050211103030024060601440c01000050040561075211008502190302d2030f0290f0781d80c81d4251800d0490351207000358000c2c000501c120a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 840973588 1250 840972338 840972347
    0x21323010f05100203280302130b030109050601091203081003210305060307060203090d020a03020616061805060403080622020301090c030e0d081b07050a0308060111071701020712 79
    0x6481c82992101c40c481c035401c00590b0769010348151100c1c86c6e207000764405602180c10004048040f01402c0260034035001001042068807942c000c441b42c40408401009014240d00489400c441c003800c00c007c0c40c500b001e80c1002080c070a9240a802d11103050082500c40481130140070080d9042a80810340c164007650700d80588014401c00c3c0000303410702c0c011a200b8580841c582040310417030380040d49400304480900040840409050340d0014040f100040545c6900c401428040b49800044504410720300d800d004546140c5941161030b901f0440490000b200020b000d5002a01804c240e0712a070b5440c40024003c1c0040c0d10344944209c0160a00c42030840b098001c0c0d41a900f1800781840f8403550030034200c0490f40c103000c9088440c0d025114205269000c1e840701908030b190007081c00d095034240724103d0b84079888080200c0b4141d01c4200588289075100106070b0304a00309181005e002d10b2050304c25591240c1600031803041c065080110905060700354102c50009610644034518409130080250 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 840974838 1250 840973588 840973619
    0x1090201030f0c0e0d0c0b0c07030303050c040f091805100603050c0f09240a06050c160f061d030a060606080106050f0a0e0d0b0103110f09010302132301 67
    0xd0110b4182414040e11401d1070050741c00c81c01c0b0a40c0d9200391010038100300011113040280c2610b0381081c07614013240640044006010552401c0700400c0c00c01d25500d401000c07900024109451400306001c03c0c000b4030424100c08007221001c03400451207030b034000f1a131409100810001480e1b07100b54084450b061159420078000c480c01032058441d20b400300c1041c00b0b1000001e943e003681c081c0d203403c0007402c0d0b4040070071000da00a0007034009038400440742d004200b0311849030700500c01242c03008c03035610100351017084a00c0100407529400005d0ba442e012000c400080140501018001d500130b12804006000100e980c10103001401c0703070718580032800d00d00001c000324011030b070029041c0b40003c10f085000d83c007203c1d65484800201890303c00f14203000c076035118448c80010350003030302d18440c000850307a0b08a19a01950203203090030300d0301f00ca81d01040303c2d00708402112805030a01000400150ba5503800c2d503800c01e680d402d00429805c6c441148491007021202c0e11441922380480041403c9100041c01c0c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 840976088 1250 840974838 840974843
    0x31506030b10031404060e0a050303091b0d0302120f07060510030201080702031c05180a03080f100e040b1b0a0305090606181501020708101a04060305030720040c020109 74
    0x305002000c10400701c090352844130018000e00106400310f000610260f01a641c1210020b003600e540145566030a41144d02c1078900d13080940c481600c805600203415007201403c203040b955a0001c0503260b6010b501c404c00d228213603000030702c00b04012521142c808101c54006900100c100142d10f052445101c03090501c0c0000c3c1c0c001140f110021303c04900000c112000401043e0202003001920456103025000060003010244d140c1901d660f40303901c0420054042c64031a403918071091600c0740740400038800c0100003403a2511401410003800da201e01100d501305802070800c00d4180d171451a102000030040c215007d1050700021501841e03581940322a001d0040442a01c0d0305860311002c000030184507038007036074940003c100800d002140400141d070b6554410700545003401c0d80c425805041c0803010395020143d82d151150a8541d0382c03661010184400c04035800c0020900b1a10342651300c1c012240000d10346214010854100386510400048040d002081840200f0300548000c0c00b17086e8081d000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 840977338 1250 840976088 840976099
    0x807170712020a12030306030b191b230f0f03041b0b0f0702010c05100603021201110a0f020c0310091a220f02030d020a0b0108030325031506030b 64
    0x420010441841d2400d000d4009040454281c10641c03888548541c10408605040d13540000200140704540380354402c18003031181101001d4222403402c1034901900011400000d4900c2c000001a00b00c7d64000700c074000300060104142410700d41020910656810a000c603101180c0c2e2240415100d004510480c0720300204401000318200c0c0c9001c00589d4056615148410300004070715190440262044034014074010800202540310a400c0c0a03080d0148004181c0311501802541011a1031003c1c114071030008000d1003400707203e40f400354021446034004001c1145586032100e4400c0122041c0c00740000c0c19640b02c1400701c01100000e1000c0001110340c1d8881c1a00c04500350401000c0030b1141d104038030f4807011030310904032051070411070490880d41c1d612108070940150b1020040c0900b0030041b60002c12141070107081000c0042016440090a58010400c02541c980318155100100300130200c0400f50115051003500a0403030078060109441c40641c0000d03c256260700900660841a00c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 840978588 1250 840977338 840977353
    0x60902030a062a020309010507291b13050f1306241b031202071505091e0d120204180b150c0307141c03050a060f030209040b0a06080717 60
    0x106203901d03c140e00303100340241c1c000b80003440081d400b031001011250300c00c200d4802c0341c000d80d425101c00441c080a4003000b2180c9241001180104514030224282025811134201040560907200c0d0301001e004850207582ca0b840c4000e42511510b408404100040b0028084161030b1003200d00901e1452510b04040d080c090381c0303146114019882042001022007100c41555040d403003e40301000c10044075680d0580c20010720020902e042d18003009542c801e0004603103418184600d07844c0210728888507911041d0701c004030703416040009161700a0001424030340540120b41c5401c000900583d03000307410940380d04025001e4074590303900074070001108440100d80016441d41040c6540602d903047c0d003195104000b0180400c94289041c61003a00c020216164075428044441040c590382c0940c40100303495006004421070240204805805000d00c410344141c6980c000070480c01003c0d001070000840c02000c611207032030079003105000d0705046d01101d10740c03590350804005207242c81001c000d01d40140107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 840979838 1250 840978588 840978641
    0x307120b010509130b030f0a2015041505070c03060b010212130b03250513050409020112023124020703151509090b09010b130207060902030a06 63
    0x1054940e240c801402004003601c0000d4000f0042445c50a0160300d4840d50381104202170040104d100120f22401034001c6a41440751448449003a0000003403103070102c80c01707242c003075903c41c400d130b908642481e41500c0000301d0604013905c982c420f03110007610708031040c00c02205100458100780310208003079080310289418049203110500480c0085403507081c2001c4100581b0042202031500700600034807206000700340052802481c4a40062000420b90208550008503c480345280051a040e1420b100c1c4d60055400240140101c035500d05602c1d50100c0d800e03100d0000010380384e11104d0f03880001c401c0c10400c5024840c1b074555610881c203503001d10041d8421a04001c1c825020002d090703400602c000c030b00b1944d45032569503811108941c0555140d20805111000782c210b100109504040019103401d00d0901100c9a000100480365603070408100c0b407183d88802d08824160641c1000060b25004240740042c007900c42e890010390700d032042c16162410b1010550083c0001219070301c1c0c00b2020444038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 840981088 1250 840979838 840979847
    0x1803150702030901180f030b06030f2808070b04051b04091a071106012c130b091f0f0501080a21030b120a29060d020d080307120b01 58
    0x2160880010b0300184046105540a607250344503c4a00c0c1520a05441e140e0a0600c001080d0741d00070b8507100305103024072a460505101c00d01c00301b541d0780c001c1d00036a403415501104019520860b0403181040305041c81c01c0c4030340901510308042d400b5600059608145c00d10ba070b44c1c0c0210442c61004280881c0079104503250a210b01020716903c24001e42c800030190050b900c4035400101a0703401c1c0044402c0000560300c0620005001c0c0c006d5008548070b41103000e00c0c4520601c445040340692040400c10b1240328400e810142480d19408040c42c40305950700d41ea41820601e4409018142d01200e06000e0075911960b0089070344019002020031241c0e984038283c82c1d4800c008a0041d281d50003000000e45801d4007035002c80f44d00e03a0705040100d15001e03800045a07082248010502d0190007064504080110400708080c6104910307041c8001c14007039030070303514010502504181c41000b40039881004c5441d8803003100f1300141c12150f0682c0300c0c07818400c0600b81001040128a8003880c10100209a41c00b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 840982338 1250 840981088 840981091
    0x7050301060f030b0a1128020d0f050d050402030c030106030602071401020f0d020d150b0a09090e07050f1203070b010e060901062007031b0801050a0b03032d180315 72
    0x4105019072100300368079000b008039081001c0c00c407100b0000c140041c0c600955840d81d203149a0607c425855000c14001e080081c03080d4544100700301054070304006a884010380d0003080481c14009065221403001910303184846103900d800d5424441c000084c80070b240c2c0600310303007030044100c4140509010300c103034201d101d042d1039031045480911807000d2011103a4040c001c0740007501c0c000182183c140d84010001040c80e48090890140050040c0c0080da11580003402000785074804e2252000050260b5110306642c0101030041f09e40d880415450750f1042c0c04401500003480079039a48001604214900403000d01800000a04000c003107270880c100f0015490498105543c3c1442c010708c1142001581c40d20325604a105100e4000088042885d0040040c03458600c05003030840790b40b0340005507003034031001010311088034940116a4003645000c001c6486003c07046507551b61090342e100030304607000141c0340c500e000080041400c4070016078040c41400403540441c100d51904110b49055090307485c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 840983588 1250 840982338 840982343
    0xe451005130201051911120a0e18150a03060609020705070e060d08210702010e0c03300f0a030603060506040506011205060a0e131a07020a030516050f07050301060f03 73
    0x4040000303405c91350f20b4a0303e02520400178075003905e07090400a00c0381c0c80e124a00e00705404070007002400c40f512641004041c40a07810a0b141841985074404003044001c000621f2403002c452400e00d581c199035107042024000e15402081004172603155501c202c003d401c90001200d0320711451802080c2c0c2584119424455203004202c0c400008456071840200d8000c20785040082a4154941135884100c4810502c80e44c0568000601c02a0a41b00240303025004c61440340650070906443c2100741c07a080e0b14800c516501a0185283c020341134529809100c2e0840206680c4000b144186103103500da007044040324010301d0240407a031942001c206c21520140c4644d40800d05950006180b420755401203540724078010106c543d44c940d04d40d600c0e0081c900461b01d9400d0b540c4080b10103001c006070440090b50f0b604810f14181601d14080300040d64030899034030b01a0511501292841c48107100101e0700f40511b52000c203984a03502d6282c01e03240d884129002e414425420322201051100840d800141100d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 840984838 1250 840983588 840983597
    0x90601060c1106090d02130f11160809010e09130b0c0405010c060f020c07030c0305010c1110051302100206100503010537021903060e451005130201 65
    0x200180100b080135440425010380008100280038050b17610f098120071007147c04030001c82c4445208460038100c950000061600c25428480f1010042c0d10b00c4425811a9100041d29520710910303005844052104d0030702a070009190b803c02200b2150409080070031440b40006009540b50000c20810901503402103900141e01c449102c404101c03140c0124404100c003130750062800e580310185038140000794109440c1070020010401c20001d017403086075082541d82c60009800000d0048458550742034030004e40b01c840d16040811142e446a044110b03900307030b00802130022801125070280d141c001c21100544044018000000c06060600a2070702c03e1003400d040041c84030b03110710800700460300d183c103c1c030032400ea0042a440c019441c0c40146504004000d81c0310b4040060000103007900c4081d004044801c4000707050200300d0030310720140d00d9214405489030110348846420070803410040c0c1441000c0c00c081c0040030051100111704031f1604460f9290070f222a03600d46200740d480c90b094060090006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 840986088 1250 840984838 840984863
    0x90f0105160e10120f06061205070c021203130311040f06080601060f12181407030f0204111603030b011115011502030403050304090c09090905063c090601060c 70
    0x5181c1083c811800c3c200c0c1d401c28444800c0c02100c81c0c01103035610a000c0612a0b40c84c842880603e4110401010a0721604c5041c04189090f1138000d01c511000032000307000b03040161035202841303810300a03030781888498210310f04001c3c1d8a041281240c030355010064043d0785050385820f0780454502407182171351500c00043c030050346425011201080c00d07003040f01c1044050100301e162410107002d20040c000502c600346281e5086402c010a01200111004025a01c186030400000700415a08102035804590008400b881c034100c1e80c1c0307030344102c401035403a20040d88a50006c150300340d0b100c0107400300e081e40d89a0903030381c001c415542c0e80c100c2d49042c8060311040800400c048009040c075588040e5461058908155890340c4492941d007158100d06901a00e414400d035a83d44d0001e00a4018103d90b0401c1c001803503540c4500d9161003000c1d00c51300d802d44270b0101c03603403402d007a520b81d840c11509400c9091600403140c1c5100855039100f83c1d84941c0700c0c0980030000400c144104080843c55400c601b000148 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 840987338 1250 840986088 840986117
    0x1a040c020a080a0e04110705010e07150e0a0504020a03060806010f081f1409010207031d061e090a080a0b150a120c0b0f0d05240405100e090f010516 65
    0x35500f00799588020041e0b501c0e0707a05110b850390300079014040b02100050b034841960b441e22034203546c502c403e0001c813544401780800c085d00105013114103500d03160601e0312042d0700400c00b00b500c0040d05e41129410078000215109119416441075044981c404144c60890340c07100700024070352081d842051941d81c890640404215a82031018240300d070042c1001485540704200c0d80b607407100c11151603020740d41c041464024190809184440c65640c0202207142c02c20040c00954035001e01d00300034001c5030640748500c2e00c00791001c0131210b140800401d0b2842466a44400e0340d42c1d80c25410084802007001c4000c00d0700d1038000e814105841c0030042040c0092800c1007c6010004c8040301c056401074030b400c600044076403180c3d00a00c03181a0070f40159503a140326a10035015500050900741c2d000782d0362026500e00351740c0c01d050300150050444001c142911400032190101c0026000303031100c05c2521040c443c07001c400040c004d444510440090004d0f54036100c0c00c03a00b40a0b0000454081103404461101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 840988588 1250 840987338 840987353
    0x30809010b2d01030c09030605090c060f0409150608010302540c03340203040807060302030c0a05160f03020c330702010c080d1a040c020a 61
    0x50004040000080c11001c03440021900c08407040c0304100d40142c9211030001c4100000102c80684003800c1c1400104114040202150098070014106950360b030b0100b694180b06100905100300000c1610392540a2400c6000c0b803640607114140e5020300c0d01c5109840d500e90f07250100221810340c3c0b25414660300e03603002e0020800501e1030080881c0c6050388102c0030800e035040c0402e90340c600540038904203001d0001200e5140d041900840c2c80d01000020071800020b1201200c1e40141d24100c031881603040d003240143c2d01480d112800031034200807180d80000c41c0d4001f0242003210010801c441c0c1083e80c1e0802913080b0310080e43d03000c0049104104510301240074000400000040c580c07507003424203041d1100c4900100c6031500310010307080b4603607000461401c0c41c2e036150140365505602d540002e00b210641d610307014030403400183c8800403c10906580c050031444d1640b94101102541d10440c4402d410010404010b07070a942e0003210078280d400781058400d5150000e295001030200b00100d44036030380c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 840989838 1250 840988588 840988591
    0x10b0f010c050f010c03020409060e091c020f0f150f010b040b033c0c18040e0319020616030c0807270b0316171807091802030d1b0308 59
    0x1940c0303120b20f0003c640816001d01c5104200c0d01c3d50b540068440c0c1c1054445001c0c4c505c1e503401008013034115030600c41c80410203c0c00451500d0060100f803103041e984541030f401e0200200000c241406141c814281d411070116030100088040500704150340d44440174984040028043c03e24210030500c0b003405111800c01c01160003d4940c0d440700f850a0503021660200d0404071400383c540904002e42864000032384900c9500322026a00035800c0000341c00780c80d0706041c5500303542481a0384a504642d00c0304401e00484a202d110b40c201249502c40e40c4030080e5640c8425501c2c030103406a070600700340d1418800c3c03042801040f2950780e00e07080d549070210202c550034900341c03212010f1a01c0c5040855220280181c41d401040c124100c5500c0345050015000340b006c1c89080300c01030140c500305c0c00d008a10306503203081d404100381301401c9172488040a86840c0c5007103a00444143c51034000601905200d81007000f2005208030200c540380c4401e0a17048a50341d1007030040c0b03148100c2c80a90b40c0d0000c0d000d00200c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 840991088 1250 840989838 840989843
    0x608070e16170708220609020108010803270f040507090e0f190c2a0510020c0a08072a08160e0c0a0203070f0605180c09040206090105070203010c0818010b0f010c 71
    0x10b000c2003400c554141e4800032500044600647e501250021940c100d68024014010f01010314101340c82c440c0c44503100f4407801c450702c046030b040c00445900c40d6104070008c50f860714040e1042085141001e03000d04003c0701e80c0a0b14604056040024030000030710540785200d25203400386011396508160520026000001c170b01414003102d1049034007512564525104801e11011a03682d0604190404a0500c800210200030041c010090140031203000240c0401e415400a41181d030707410203052003080e04098650801100800b4a49500d01410340c003020016a031400059520031215401c4010b01919544108249051300342c0018030315000400c00342c5a0700c0a1401036034908082a6141c50700d00b41895005c842e290f6039141808020f00340c0c5081e82e1040b12a900c0200f43c0901c0e000002200045c009000910444000644001c5031348140240c4203025805402807100780248007000e003848004031455401809074a0b80d03248948414000c000041c600500790f4031800c1048001160300c0011032005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 840992338 1250 840991088 840991111
    0x10f020435120c1504121b0f02060703050d0f0501030c060f12200d3204242f040f030b0406020708040605090f10020d080a0608070e16170708 62
    0x100e0204965503141030300c141e01c1002c0c3c510302c4011000d1b0250200e600c4610101a101107122100d00240c9080c061500c00c82e01102d00d5074036007030039140c2214284203000381d003890241021070804c0310300b1440e00b00c6c0b4142c0c1e00c6036440d232840310303125441269152000c0b40d4280028400030305c21034400e070040e0301089851750b8a4080880701c0c0d0780000700c44442e500a60b281e42e200b41d59844049041c074209182401200a030b6100b042140480102c446906000644050440c55101d620600301c00b000d804240d8110103150380610001c00030303107002c2c0180c0c4000710440404842c000c1342841610100b00449050303d809140401249081d911840e560b540000e000711801c0e6400c00244000c03451032000f82009200680e5000e55418064042c844184524035880d4007ca820b01c9032000402d8010a00c1d1103000e000b40b4140f403280d80d031400148040c4c00681d0102c0740500440401059602503404114851160014001030803440e00744211912000101a0502004603001003600c071446409520f803c00d034030020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 840993588 1250 840992338 840992353
    0x302011e2f03070804050f01080118020c01200901030b12120906070204060807081603110d0204060b0d0c08090601080606090c040806010f091b0210020903010f020435120c 75
    0x9801c0e10310390107030b0f00c26182100045800c019a01c0c1c010031380d041244080c41c20394540d500d00300711200310300b100d2a00d030840e46402280d03503101030f2400d40c006842c00350015a0f805032610345a00010701503200401e91400282021583c21a5081021044c1c003d05004802806070913440d00c10420260440c0d800300341c0c4500c0410802025903201c1c02604040c15506014114075440c103104d4525007826500e001c203c0048441082001c1111140b4503040383c1020784205840c8201440050002c06060b001003c04150200d240a442100e951201c070440d500740d1144a07450b1992084507544100034401c00c620f540c01140083c0007420030202860300420820340c504e0909407203070b00310703030600340242c0011090390500c550030420320185000f0f4111004002d4224040c10020900003512042d4440022510980015400402d6142540440b411000303032401152100d440e410300400d00e02c02e0500710603064200603201d18090880c59500041c401e5954018100d11695881c0150315801002c0c00c142140139040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 840994838 1250 840993588 840993677
    0x9010f120606050d14071202090f1305010e0102310303030b01090f0815150108010e091e030a02070e010b0904181e0507090606090326130302011e 64
    0x21369284144200f030710106080d054940390380380840b141c0c000f0107441000c1c0320440c0540c50b1000c149400084011304880340340d8560703202e003514035940c02008003551f183c00700c00c0d0070100d410741c0a401c0c0d101e80b410140c07002641000b0408045078646800b000410980390007000000d000781e001e1280140181042c984c1035960b6082d41d842080c490b44003103100c4d006048c559031810707551000c055005904071010710741e4000d41c0e00020030144050107103c1140748800d022038000e4030104030040c01103402c5c445451100601410064980e004400700c03402522035540086507541c080021641600d101501007030400250402b04006000e01d441911400b0000702409400b1070150f440161400c0a5502e00b8042c690307151828501d000c12030351004086e40d290500030300031640c0c007c84000c216500a2501001400c24241c3c400b040a130341500449480700000c0d0501030610652010021a03000f600c65840044d00c0c00c00786031001c0140459080081d0310040c2001c54002c040600008020200a001e4070241042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 840996088 1250 840994838 840994849
    0xd1412220807020f010302041d0a0e2401050a08030307030c0903140303060f0a0513090c270e15070f03060504050a0b03060603070e0408031b070609030e09010f12060605 74
    0x10441074904400001d500000d506069610341000c59080c41c08515140c6400c0710041d1491025240d00c030000d40341c0000c03e0340a001c03904540b00c0030056038160360901075851085e41243c0c56141d400100c41c846c40c00005960f1034601c0c5510708548203036010314070315640c40380210028032030745040d01c1c207004103014080081400d42190010f1112007000035541c9042c4241008601c2e0407003030200384503602c00c080620090b1100d03002d00394000c58000d00440c004410f80760402e403450070768010140d1a9130160300203120b803007501c10f50008012455420820788124098072900c1d801700d09071034001003901c90049007603144100d100d0b20151006140c005041340e00c800025040d6401600c00121b8180c40c0c40d403504461030140030068103c0c904a0050401d40d15165010300b00810081001c0d00800c0f0100000c0c040c41280d107502019050946141503603010a0f142c0320008145040040e270020303045028803070719801c0000345181603452601038026550b1825150341220000d446003101c0d5170752a45d000142540381e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 840997338 1250 840996088 840996151
    0x90103031b150501180911010309080903060f040219060f0c062003060a050303030405060112051216060f0b010e090903041e0303030b010f091a04080604140d1412 71
    0x15000045504c2d4948112421450108001140c3d1145016090000201d003120141280342c03007801d001c10801c4281c108525a805070000f915003601910003000900d5100d44516403145200f1036030040507041c2e8000e03c4212120034040c640100e0030400006088a0054803840c010b42d2050300c0c042064140e401c13000c0e8070442d85141102d40e140d40070051291a2404240071130180100354010350641c03420742c0b40e04e40d5808040c4602d00d1021185107990080c05001c0c00327a81d4a202e09440e0f05651030402c0c035000c0580200000068aa2038640f0303441030040c01050040c0602214141d583d40544216003080103105000a410b81d442444104030008180e00d881c40700301d01100d0100701c83d0911078030707504014050301d500c46019410009410010b9a41c00d40000081059030189950158072881c410303410351007841280c10a0603e44504410001040621040d0b01c13005000c0c4070581d22141c03010501500d0b1f0720000300c401c01e80e0318400d12901c0e11320341c0300d108003d61003009803040ba144100c4069002c0c3c100b000d0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 840998588 1250 840997338 840997373
    0xa050a0e101b020d0203040e0702120c07051507030e040c05161505100501080103110a0e01090207050c010806130e0a08030c0705060c0f0d051f1206050114090103031b 73
    0x2142e086032070005860804040101ea8a80081d080103640e9a00003900e03882140620000c007290365001c142c11034400c0024101c144840d51165581365a004070895036a1403d1040ca4811028562809074040001c002e8a9500b940340c2c540d82003070040081044068640c0509c6101040710a02c815058200c000888200150241540c0d09507800e8507404101942c80040c03001e810072145031002c0015036031144400c4e0440350409400a001460b180004500d119180e0000c036254007a28004120b0703c442d5070041c1042440381c1c04660a5180380c20055800e102c0480710140e00600c1840c022800d890590402c020740300034041502c1c80d1501c56920140590016203a02c0b03440e040c0801c0c140e0401c5010084280c118230340d030b18001d0074001d9098440c0d09a20646107141d034265101c0d0003150414a0502c01340e65407003c005480c0c0c0303c2d9900c502d00000c0d9a5010403040c1c4106083c1000010740f54030b403104110b28228090540c0802e0382c04e50700c00341c4845982c0815900d90b080d40c0c1c5416400724040f260702101015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 840999838 1250 840998588 840998591
    0x30e04050a0606030b0901031a090304030b010608090d0201060602070b09040e1c0f031803030f0b040507030e0c0901050604030803040f21200a030f210213060c0b0a050a0e10 76
    0x3420708000404664014072145c2c0590380c02c00060001c62740213650352000d10000840c01c000c540c2e402a6180c114001c03075200034065950200040341c01a00041c106100d043c0c0c01088840c0741d418403c1c1242130f18113910841003d13800c0000140400645400203084016028101084095074021854030301564410310008600030414038940c030035031003080005804c000349428441d40110201c480c2c100b019485009050555400a2601504c219080000707a103e00400402551501c554054040c0c013181c141e00941e405032503010310540c40c01e11f4409060b00c0000e41910308203411903844c140b50740d1000e00191a0040742c0078030385002400c0b03030364014158525421254501c040080011b06030b08042c1c40c40d007244060405c83c00e0032510002611404694051400d11400b046406040d2556203910001c904441c41d039030740400c40c030310b1680c0042401c00348003072070a920540d840000b11184030408500500100400307010074014034181d0003843d0003405008000a504081c00c89151402003c42540001103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 841001088 1250 840999838 840999851
    0x1110c030702040e06010608070507020a150e013c05040f030309030c12030f080a110c0a050610050d0303020913021902060f130b040819120c03060f03020607030e04050a 74
    0x500307103401041c44904c0000700a107199410080d0107045400001c040208121001c540003042d591641c1d4070000501d180f5109101d0602d07581d0300100400c030740c201d00c0d80c040390710400082c0d1412a010319109012140845c80030024170340404102d4010f0044044a040100030320008c2008c01000d030090005612076220039a103540b441c90b05c030000c001a6031003c6004a1144801d4000c603800040b00c80029a141c47c4c240000c0c1d4603803400800400265a05201419021030b81400900000600c40c080c54003520071a0500e40c0d452104108000d00380c0559038200c4071010307148000a01903006040d003100014200404400c03004120000c0340c001c03002c291a001e500d10319800e041d035014450590040010365501c01d0303515006961810702ca4002c24028444024100002c041c855558142d07000b103074240c9000c0c10340401080c801880da51190f404901800e18000719500360700c0c0a0b11420040720358445c031030b205103840c5400701316598100500540c24420b4458601840b0750b00e5104541c0310b13110b60800010103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 841002338 1250 841001088 841001093
    0x170603160b1e07021e04090c060e0315060f01110708030a0509010809121b010605030313030b010605040e180f0f060703200d0905031204060501050f040911060c01110c0307 75
    0xc50754500c81c0900c8540d0100083d6025071200058400c04109001009110051020104000f07141d0700001a00d8a00c220201203025540315140d503070f0003902102101d2405800ca4482419440e00791070865000b48100460102c030b5000303d05501250020740182e8032041d90354000c1d10f0540c0c2c0300c07400210024100081000440d81c00040303440d0030541c2480100401d5042650300c002c1403043c03010031444004100b00703141482c0001d41065014000c0641500d032140d41c1c82c41508c0c1201000e0000321101d41c001400031620324411000c0d5401c540c3da618150b1042d0b140c40020008680e0100d0702d0714094081d0440d071000000d0100107103040742c90014003c160718139107410000d040f18400c00030704004a0700d01c0c0b04aa01c0704080400e94504a410801c0054101d4003840c00926511030f0903107802c1c0c101c01c20070810051003005c1e40041d04071034081d42c110843c0890101044120380780034100524141644143c1c0c5000d04104002d0000c07044003000018406440d6032904a16800658a02c911a440050703001c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 841003588 1250 841002338 841002367
    0xc19060c0f020c06090a031505060405160206130c120c0810150b09010504030f060506010e040c0c170c0111250b040305030a060f0602060906070e01170603160b 70
    0x16a603254034020300c050039034010081d2500e0800445a104690104102c1d0480e034400c80c1c420000c3d41d001c440081c000400011050140c4000c949041c8980e107072900184a44000300340d81c018010700b40c0c1c040d211680d035091140ba02100014019210081040c0011a00380044004001158060803001d1082d0345004440c41c48c0150b05181d031401541407204d081001c04401e405102a2a5010519601c0300e54040048805005580c80034004007410b1410748140250350340040e000340c42c2a41c0342039603103000700700b0b0000f9680c00445900004184000b403030040780d4414080c14803903550406851820030110701c0242954440032410300140e41c0000d4008441c01140040e00e60101e108409208590481d164140103103170040c40a02400b0002000074620b0b4000d03808071018007091682d0800307150b00c070b40009564234802c03501131595200d40408649094043c440c1c90348a508140d48541d070031a08103004410802c1c02801458041c4a15140402c1c0683c40c1402c510240c80c1c118103107520b91490030b41298 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 841004838 1250 841003588 841003601
    0x6170a15021605100b1207050d061b0507110a050d0803060f090907141002120f0702030703030504060f09210204020c010f150e010e060108060126060f042703050c1906 73
    0x40c400d0401b103002c441d07901c030041516001c6507800c81d803100d82000c040c2804000383c00c0034503881000000c0c854590301309030341000c0500802d500136007112803c44c18880070f00840c2155409826845031311110000c0000700d00300007c5034009009013204040c50606800706000070b0742526054400c1e080f49405000780300c202c1c4003211480c241100c1002080d541c0280103515001c24100e06540d1410001e400c2d055055100f0445007810b901400702c8219070b54908008186820501078030000031142900c0e11410303441070440509841e03030b03000300038842480b00304180a10f03030744480100d030007940900c0900c40c040c00a1180302d102c00794203500464146d00503481c2031010f0301913401041000031010014061501843c00d400e520140a08000e200f545400005a80c101e2034045024107812900a400f0400000c0c400c0580c00b909060341d080e10039500d503904200586550086c03000000c2003010342c0d8000701442c201407190342030003420a14602074004107000e00340b4241c841c0d0743c148006482c0d40101000740034802c21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 841006088 1250 841004838 841004861
    0x309060903031b05070209161e020a1709030718060902030a1a01050f030a0504080c1b151e0a05040b030901061814130c2706170a1502160510 62
    0x4c0386486196400a9206040030b0210a0b541000504419047c1d005820121025060000842080701980780c000d5450350103035000c0b24610b030703003c0403c003104800400b581c00b009002005020721504103080c2d220300382e00f1071125500c5151079101c0014160f0f0b40c1d10041d40030b081c404d800419214803800d00003440c0803032a60014100581000414a43c02030201942d801506048001c50107454030300f044950341c0224400c4801b640221180724662141340252200400c9054407182c071706144071800020305000303401c801b00070118554000c00300726407128020840105a07080c00c508140d1100d01c2100c00f030700202c40d51221f583d541c140600c40703501c2400342c0c1c0c000961401003c0c050449412820385001d24040e00b0b10208040131141102041901d2002c440a44419482c1101d00301c25691040141c0c840380b6100f004c400c0c5004000b02d11080112488803802500300d00810469009945004504001801d680e0381c0e01d41c00d01105201c10080d070b0880080d01c0c0144000e20214010342c102408980e03846940 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 841007194 1106 841006088 841006097
    0x80f0405010b150a0215130308101509031a010312030f0b041802090a02192012070209130c0b0c0a02120307052505040b010309060903031b 61
    0x380890004a034201c03060948848a8030200d0b14040e210100d00802c40a401c80c0230a02035121a5046914440d605074100d81c8c42482500c404101007481c3c0000e0b40404040051100034070f8000c4000c01c454509500d254590707503c400c4100c03882130464003410f8445c0242000c041d035661091280e201c024005000304440a0713004a542c0809420807031141c02820003140a94031319209807544001c05694200154448450a40303181d020110012540c1c00581381000b544042401070a8540020074001c540b11801d501c10041c3c0000010042c00545030201a00c0d0301203413018200408945820081d20b50340e07108100c0d250300b0314030003042c080c0d0049050410120101c0c80000101051030042c030603540881090200d4003812440017200c0d041c42d0f981284107000c0d51a19902203a5500301c1414000f50b0403510340d440006850031040c0960120340e545000c80b441c1d9040c40780c5458108900c0c5071 = true := by decide +kernel

theorem cover : BRFrame.Cov 840827338 841007194 := by
  have h0 := BRFrame.cov_init 840827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 840827338 ≤ n) (h2 : n < 841007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
