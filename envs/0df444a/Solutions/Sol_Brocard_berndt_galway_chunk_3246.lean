-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3246
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:35.460115+00:00
-- url     : https://prove2.me/submissions/3482b62e-e1ee-4d83-9cae-484ce633889a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 583633093 ≤ n < 583812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 583634343 1250 583633093 583633097
    0xe12070317010b040518041232190305060303070807060612081206010302040f031104020c0d180501020307080d051306020a090e1803032701090b1806010320010e10 72
    0x4041c8100d0400c2075104500303c40d806044c040c0b85c50707e9111240e01c03e031604401c000b00480c40c1d0300842e00c42103100c203040040349021800c05d14140c080100390303c0c5500c2203c0b014072007440d60300c590300164041d101c1c0b13070b00c0340101801440c942a038640e107408855004000840394a035031180c0101c3c1002c84601e1074800ca5108016050361040e0b002c07450160030350010078850406004000500100d04141e20144c210395200d5401c034220b15103240010041e02071164050540e225016a01400c1544150f0301540b41e00c83d480c0203a00d05403507800490720f07841155400b803e202d600700500d09a15440e41d2143e540321045500718881c03d0329680c2e6201c20ba904c031409104c0028030602d018051410111682d54009200e00c80100700d000c1d10742c0200383c4a01000700040c420840164141c0d11240716044846440c2c247e2100030041c014051402c48503c040c01d4811166107070741e4582070b070324888000400034140c1e504000d00c809581240c151040168101d00c0c241b80c1000f404800c900c80784c1d00d40109c2e142d40600c0d19 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 583635593 1250 583634343 583634347
    0x92705040b061206062409030a06021209010b0f09040519050303100801020430061b17070801051903060203160806180411010302120a0c120e12070317010b 68
    0xd481080030443c030580390300d03405401100034003e02d99100c81c200d807000c44040d03902041b10055090200980d005500c1c42503094004d00141d5020004540d0061500e2400d07054441107607102c403a031590803104020175041d013049911040d219140381c03881c030a0b9403262088040310500800002c03c007004000300d0f0401c854681c0040244400c2e488140441c5003d448400e0003181014640640400524200f0000c124000032800103c0303500d510700c0c031422a0070b41c1c11100500492010244c1e803100c03181c4c541200c00010b401400038481980384840c17900d02518159542d4460369013003204100b4030105440074040b0140d510301001000503c1400510701c91000f0909655a606640304060030000700142100e00c1a140b658800c03040c5580311591b19007040d0441d0700040307800f0000006800071f1080c107510010b40c014010400101984980108040c52500e9503164840c400758000401592002004d800c2d40b900704400350030030b015002d00901036040c002c3c03814074a103030000610959aaa400c0e04425071111340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 583636843 1250 583635593 583635601
    0x30c170c0c01030605010309030813030504080f07030506060906221d010203060f0307030b04120c17130e09030406081e180c090f010b07050705130b090610092705040b 73
    0x14801c400042c175007824103001061207907034001c0104000030501141e1480583c01081450b03c87d1040c6d6000c0c1207428101c44110111412245e6240780a11003210302c0d101e0500000c07060f0400c005000d000d40c501500941d0701c1c0c2c07141e1140d8010010800101030308243d40788040700800704242c02e01040c904d0800c00044e981d0805100380a103012040b02c445000358042c0e032003040080c900341c0304985d02640203103034020302c606403910031036103a00c4c1d06070f0141c072451064101d954050441c0004005c0400a0b6a21104844d07a4a046503100b00044404d0704260700103110400400f800382c0117484c0d000c240c143c5146001d214420388090040000e4403814032003024120a1030b14144100910001c041c401c980072600d529111760b10b07c00c0f520301402103541421002c1062000c0150402048000e400005c0c0790f001c01014420454000300310b00740d4510320500342c54000c07030f100d414140c01008841120342c2e544c0b01e050f410400c00b90b00104901c00e24080083d41c03664500d4a202440c80b503180103501c98042d895007418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 583638093 1250 583636843 583636847
    0x30f0f0b180601020616030615030615080c040b071b03111507230f0f0d021234150f0e0d0e10090b041202011713030c170c0c01 56
    0x6071699941c0d9100020280300c0c00342c3e000036409a004012894144203030340c06100803409000c0562080091100310800382c590241c0607004007050707030300640f81030100300500202114902425582d81c0031a62081100340440c0d45088000c00d0214000c1c0c2c18003a1803180e040442050304290b40c0151001d507203000200060340341c100b10600386000016051810301000391107040703a00040c96010469000d00d90301c0541505824840300a0000101041e82c1c105e034070106902c0d44074051452040014002c41841d0807102d00e940085d600508170525140c0c8150000720000d82d14a80d5410856040505140c08840010030350340c0031140b048601c0901143c1c541500c000f903000d80d03025030003075986600322541075501c490341300c030b924031014500300c071001200c401c20107050384c0342c5c036031500120803041001a0124810706124030002402c0d00c03ea0f2000c9003050780c0d4285007002a410b541c0c1c006204035955090000c00e00c140c1d8003c80160092040c001c4c6000e042020080a9006c0c0d484a5450303044504a850b0661f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 583639343 1250 583638093 583638109
    0x130602070618090b0f0d0302060417071505060103090c08010c140306060a080a0b0a090b0f0a0303080a09021906020c09090d020c01080a1401030c1502011a060901030f0f0b 75
    0x85142058071840310710b030012449032140d0303000380c2c0c0d0261399401c3d00603032503600c101d40241d58480140c01d83c1d0044401e8100251501c90031178050b80c0c801010038008110500840c00c8540c111741080007211703940304450110000e0100500814109a11031502c0000f20b804580002c1c001c0107844d000240c526482e0340d028021002c02d0030702e0117441d11f09100b0001c15031103c008a550041840c500121141e444c240350000508030360034000c0e00319602250201c0d40541c0d9a1280d80401401c0321801c1c503646200b8104004950359000050000c0c3c00540426000455604809a418030080140010310342c00d5040c01d0329803040340c3c08000160310620100b0100e04203000f010b6007000c074100c00f17001c1d14449400e02079590801480001e040186490004503025a07a600c10240102d4001d0b16843e2540c1d01c0c20803041c85045405502080d886a0000031003040c01442184120600058070081524610741040301a4106000c010b05068440401c44000e454502c606a1560603002c0001080e00c075540601080c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 583640593 1250 583639343 583639349
    0x11b0507050d0e18071808031b0a02011b0309030501050a05150103060320010509060703020c150c120c010f06090c030e010b1302031b0a0e1305100603020f0c0313060207 74
    0x8000010039a40244d110380c65006502c102ca00071080319074a0742c0320101d40019000c0311480d1908500381c0013040384040030000704010007000220a031140e052017601a1a0148114000d01040c10091030081107041d0b80751aa60301c07030290401741c415036540e849003425100115101d50000307179198200100e405d156414141c00310420b00e000c002650130343d030b1000d1441d80d80079803880400070004403801803a0f101c0c1040316108540600095110502d624020390740c0d041014046104450b003002c420100802071099032481e84641c1c00030215880030320021003060303201c032042c000311f5502c490712128503068a0045100400075260b000805103030b0300c6401000c48802500e001001e07410b250a100b110350756007031031310a10720b0040001039070794035100795161030485401050300d0072010119162141c80d800498181d22404161445c0c40c0d00b01d85419051b00f11201244d805101403143c0e43d05004041c401e40c00340c0f81c81da211b04890b91400d195000340507c1e6070085d034103011200b4218102403150587c140440d80007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 583641843 1250 583640593 583640597
    0x270c0609120f1401060f08070806060909030a0516050102070c050f06040608060909010b03061905010f03020d03120e12090a060e03070b0a0909110304060c050306150309011b0507050d 80
    0x20401a034a41c0041c0c030125801500b5880d40540c18400041c085d4050310003000402d00111403035a5603070b60540c40e621248103452050066000041c02d6041018006100d00e10240142d03243c8419030000751119001142c59261880003410100300085091008201a0b4050628000400c0c680002c000d1203c502e0506140100c5091004111041e0000c000701c0d00090116005140b07951020358042c0141006401598107200f1041407200b40c4040c4030035051310f15007001e01070029a07282c0c58044003851b0b2034031000b504060120650740c003092250700c024030f05080307241c0d0114480f4150200301349014006001001401c60014100d03003149032400201e802010307e0300f0850188031001d40080d0315058544200d01c042d40000600825080c0314a10100142042c210100f14040c800d00301c03540c0e290802c942c1101c0b420700e0048200c40e418000c4040d03038420080182141105592080803062582000d001c20b0305641d21521342e02c602e072010075504030700c1c0342c42982d59603110602824150b1400d407840c0070700c80c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 583643093 1250 583641843 583641869
    0x604050a0c1704020d0807031e0c110409140601080304080114130b040f2f0d0206040b0d060b0c0c0a0e010305060a021c0c09060323040204270c0609 65
    0x90100e4000b61100c00d03024044503a030720650b80d42c1c004603590b2245010700030080c44001a4042c1090b4021018211660038841c50001c3c419900405862112042c60003404038461000a00c4082c03034a50894010315110301d40e40325070032440b800c15914140c02a00551001d03040860706003e1000700f4800c460b500d0046218220b0b1b182420005880c003007000c2d04000d03081841c100002014440b5842c0303541c0505602006c024071000c40410006512030600306560780c00809101e030b414586c502040c407911110b0b0000c1c08a80360a2610f0180600d551240d04188543c4c0e441c0c86c000180300003e000500f03190b44405010300b004007451010040408100d401200090008200600110b070001501550100c08080c005981e000008010185605d080d081c0810780d900301203102030540d52181101c4202c40b2240c60070700028003000b5102d04034800c1107076000f1007007a11030000b078007510701600306580b25105c04103102812400740b10b1402c1100c1e0180b40c2969107146820382002810f03440b12028000303080040c2900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 583644343 1250 583643093 583643111
    0x90d0c1a03060916022b110f15150a0306020d050c040f0506090a05100c0b0106020c0303160c0b030f04381b0d1406100504060809070302180604050a 65
    0x62420302020b4010f01815041c0e0400d000703d00d000300100d80311402d0400070103d2801041b0914800003d00c032440720700003080c0e011140e0810340c0c000b418451240003d0040d02c3c50368503100f080b02d06018001c02d0704040075205806140c01c0d842d41c402030406036010790f40c0941c2d10102035074100240e0300050103002560b01c08000c1000080280c480e12400d80b5401c9846035500d403400300000d01c5902058000700d5004c0d00050381c8115058200700e4494605110314201c1c1d1a45e80d950070280d8581208000a907056001080340004221140c1070b0b03101a07070b00c00c038035000440c0e40300d5036203034600e0300200c3d50306554044000900c002c1c070001c82c16049544078040715201400e80444651040b4a010300c4440c071500661a0201d9800350300781d0443d840b503002020074240c464102c01c50303007809064a911001006020030340407032a01d084c4a02810200c58071901c0305481e0928080c804c0303850020041c0f10401c1d03030046800100040c0e07100c42440100008080c0070355002e08002041104546c0701030000e00205140030703164 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 583645593 1250 583644343 583644349
    0xa06090509090c011413051305090d02030a0905130609020f221203031503020303030a090c05090114060a140a050d290d03020703061b0810060801150302090d0c1a0306 73
    0x20141170300e0400040782c0b240707450903200c1401001c5810130381d0f0140c0412000c441b050000e0f84100d00c6006460100e6100388088002643c903845044010400681507103024046030070810901d02807a502100002103d0396100b10600c1207800900301c40d042141c000541c3c000d0900340306101c2d0792415030391101003025450b050b6a400b9030402c9040080615403210b42000300c0c103204042040065401030140d903607134600009003000904100d90304490001c266440803e01d400d1840d855070580e0050450320b9074684c40c002c20802160403a60b61002082419141812207088071800b03000b80f510652a580c0d1075108014211065400101c04402c08000d1010000050407681d00640e0f03080344107881e0701f051101c0c2820221700b49003080c1c0015001500b00b030003141549d001010000c1103d4115510450161100039030f40c103401420344940b000148044d00103100348206000300c0c40c0c1c00350007030400518001c851404100c500401c042c0c280e94640c00c0642c10032404059080f502e0249d580d82d0529440c503d001000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 583646843 1250 583645593 583645607
    0x1052503080f0f151206070f14030606071e050a150f0b0a0501030e190f05060915040206032e0e090d12051003020616020301140708130309050a06090509090c01 70
    0x7040d200c025030040d04d18441d12150f0304d180170308400406980c0c280c60306040c00740980180c030640400081110000704120b443c40029a4010f000041120340346c51070640711000d65402d65000d500701d2095402d00c010004604021902880c0d101e409509441d0a071320fa03580c0300b100e41341550340c100c00d4100005038a9954641040f07034142c0d10b0900700040d048920413541880d040a601d15812180141c0f4107607024004d10302c40b800c0145114200711070342552140d004a403103801106d201500d68181001103401442c0c004007031075020310780150b1003d401d0004000d640396180801c007816401201300d841404805441c940c6c10b070b4090480310050605440409006042103a0002e10100d250340e141c0c00309410140c5c6240400c01141c00030249511122004070540c40d06410003000c9102e5843e0103074201103114800da0b0144152910380302e084150ba59000000c1120110a00403810072001410100d603960700c1a16041c045c01c0d40e60303290702e0920308100a10401d1b4801801101040c1c0c04100400407507a40182 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 583648093 1250 583646843 583646851
    0x406180527060f250c0203190201021e0c183c0a0e060408190305100302040b030a02040f090b1b031609151106060109030b060f01052503080f0f 63
    0xe002441e503e072a2892444403034013001d00100650a0219045942c1c08030848000c00e00840917a0700580c80c2e0a0000c442e45000301e0002e0241c0c0103034000440403015244807050340d1100c10155001c0344500c1002804074000d0b40c0c0d070725180c980e090040c0300c0440a521005002d41c0c0e1941c0302d10340002c1c035042405441d240400f00e480d060a21071000a0440300b0650014900052200116400c1e41485d18001d03041d0703080440802c0c411f83c09810101d004078401d0050340e0203520448020740c1c0e094159001c0c0070180800c1d90003140c061262511240041c0c80b00c0c82020b4a501c43d41c03c0010f8960150b01c1c1500714808040d00710b44072403d03c809600d5010118008407604614920700e02c402c407143d42030b800da81c02c032159441201e00300442409800c4c01c540114465800c0c5880409440d42d035070350000159810714060101801a000d000005405402c2109240a205205040c00350500035a002058203001500441d00d0340c6220b035240c00410103400803400350b00710701c800743c0c0f608441c03404540c602c0858100030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 583649343 1250 583648093 583648111
    0x90f16120906022b050903030c07031107060503070f0e24070b070e031006080606010813170319090512030a11070809041b0507061104030f050c0a08030702011409040618052706 77
    0xa14ad4040600035003198565080603030903203020076602c3c0000b500680003207400b90301140c003510082102a10a00705401c0c0100010028803c44000c84030114400c00100f44030490071600f00a034502080c00129400e1103241b95540d2130b90055004030500d400d2400b03040007690301c0c45c145102400400400304001d64484828a417020f840c1d9100540e00e04d0a82c04004054100c011101941012185c07900086105801c909114240e100d00d84130001c04a500031031018119030401090144001c4041c40296004103811001049003815801500c42c142e100748002c484544001403141000d08050103403004030100c0e1904021500045200a00349102e0024018007244ea242c00720341c610590001034034040c5400200e13500c400c01991070807603030301c18101120f9842403442650000d414030002044440090b07040c0c1d143d14524007000540748890701700048640d406a103c24000c10012118034081c440030782480d0021a00d41059402d506560103401d07550790a400501e00501488500040c1c8650016045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 583650593 1250 583649343 583649347
    0xf10090203010207120c1a070c060c02030405030708150f040215030705040e0f090114160e1302070302031201050d0b01060807020a0b09010605090f16120906022b050903030c 76
    0x1a1002034028071130240001c2c0940c03e152100025182c0c8400403810031480340b2501c102112982901a80800b4203e031881c000034001030201000468540000c4e55005941c01101d0805459000090402c0d131103800250baa0745c0200d124486450740740c03030901d1b00001c40307041c111030310708003a000314148c4001a1000c0280e5040040416040c070700c1502140c00601c04102521054107010711070070100f0700c054504078150360904280007007895901600a0003003060b00c15071b0b103044400d00300036205841c01142e003e43c03040441c15140901d5487e400141000c503c2940a990788401103420084e0b801c0c0103800590080300141d00c0c10000070008000300f81500c3d5103091507080c0c0d6803005001c138038298503201c00501d405030100604c84c0711101500100c081d034000704c1c0c4032950342e99011108520141d0844440143c091025030f40009a4000c4000d41040e080c0c80c0000708505a2035243d08050341d1042d030050007000085030141480d03001000d40100e0800600c0024821030914544543e0349001c09072510b0940100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 583651843 1250 583650593 583650611
    0x304120c050406170c0906090604090323030403021005090c1302130e06012303060f0307030f050607032405131e0501060e030a1a0a090605130201030605030f10 70
    0x4403884240c01007a0052060204940f00e40d0300250103583c08003008614410101e107258107103001401d03544243c4d03002d0915401c6542c0c5604100142c2441c400660910214415101c901c840040002c1103800f030291050307036a0b0900c1e2030024a010f0f090203804004902d802d040c4601c1d0400801c050004900440b5910941144100c1000086c03192500010a4480c001d000090802410f10854401c40d0b00b600c8a03d0481c0000300c04078498012880744d554401020000030f8040e282a0380d42603101c9002808072034000740c50f03568041c011070011006a45a078000340c1089206030380750003886a406c0700c04420b0142a04480c54000801c140745c05910b201d800c00c035140e0041502d1039806030024410320109101041c00c080c014030003c00b001e01400340080c510958005550500041e0307031176041e034040721840b0130200081501920020140c01d80c80700c2d90700c45600c000414a98041e4074040e04644c0310b40d0b0a20180b520000d81182c89aa008602a070450303000d8004940f4040f0b803020340c6140c0c1c0100442c01ca05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 583653093 1250 583651843 583651853
    0x40504030e030a23070b0403060c021504060203040b150607170f131503020405060706021c0f0b01080105040c020714031204030807260706022d0c060a0b03030412 71
    0x4200007903103806120ba010202c040c0001e280705130310040c2d140f401516507110010540d94858225002d542000c00301008100009071b42c079800030044800c0d902c140d07042a80da10098018540042c3d40c00d0b0b8507283c011042c80f040c00b0301114200e40080c042e2003034039030303420300a80131a000b406106405095a07600461038500750002800300c82c03c0b400d030110a40d42d03548000188010204540c059810801c1200f580d100c0183e000e442140d007600c40c0140b805080281daa51140d0295005124200301900c0c55602c0805d101c10034050390000070901140818118100300004110040503404144281e040065520f400354010034402c1c242e5941840f01170392264841c0200f4a0300e281e00c0001c01a985001a000051041700c1001d8900c1500c518100e41c0d20f04c860003044407516020b0120804010010000311340000d0881d40200242c181c26111429815a4801880402c0040c00000216440c0c0028504480c01061095070349c0f2000d14001048824a1480071a030f0340c2c0160700a0400b10b00c0003d10080c2804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 583654343 1250 583653093 583653107
    0x105010e120c060c070801060905040f120e0915040e01110a27081c030905030901080a0912030e0c06040f0e07090e01080a060e030c0a032a0605070206101404050403 72
    0x41d405881a03660b110454071071130b51240c451003091b196503e480d41c0820500414011580950340104424003104165112001411070022100c81030025002c0102d8860711103142c207611520340c11f920f162032603090703e05000c00d03a0407011515100da450480c804503080390503803c1e03480e030f0701c2035103071060640602c2070302d4088a50007008107007800d210105c0b001440c050005040301001045e5100440310400c1c01006806444502c0740c0140950410302c07584506521850341c00f517000c940c0d120007003a20130084d2a5420320300c0700403460304006a1a0f0400c40e5904038100304404468805442482c40d09241c01080c004410395401802c079129480c1001c1031541340310300d401d18041d0003220419840b0717503524540582e5482d5025000c80d41d0350b0402c018940c118501109a802500c10040600b07030050848c0d030203d90390f800c0f07100c50002500b804020f40c505000810718074800140304000c0043d1a0401d000040d113007a000511042e907410b000030007803041405440141c506000213580200341606c5524066540c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 583655593 1250 583654343 583654363
    0x806150901030f02030405010f110412150902271503280c080f21091201021603090e090a030203070602070c05041a01091a1602030c06130e0f0105010e12 67
    0x5500100c240402d07c030042d441604a0141e9010802602d02c10000c490070710b0149214500b49080c43d1850b09000c1040001c0552002000401c000341ca4000c580c0065401501c0c0100c66903482c202d001e0011034180d00c02c560580008880011700004200075002036910b03d9003114130b01c03503244821031092035540840d9042c088542c1c0900c919050b1600e54480580e035001c4203110800910071031036a041e4038080ca8410b05046800209154a0325110b80b00303000d6012450302c120000d56608029042908481d03402d80f01c0e180d44a5038800741c000c0e240c9980905c010401620712000c941001380404e002980000c00c40310304a0380180301588502881c100b9807454a015840b0a8200c4d041020104ca86e04121800c0034800109807980b48160361030b400c100308610000c0c50f540c801100c0800c16482c007401c50100108903030744001c044ad0384a20005c00480e1031074001c0c101c400f1025440704014030001c00030030100d640c03045030072404010a43c50000020018405014154015601607040d2000702c1c034148407100b85 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 583656843 1250 583655593 583655621
    0x10c02030a1a09070506030402011e090801020408160504020406051905090a0e07020d03090b0c09030304231320031314030c0f0601030f1410050c07020907080615090103 74
    0x20240c1480b0580601001110442c0f01e03401840400704180ca032110a503401150183d440310122040c948201c80c0c03030000b401808060017024900000c0028090000307100ac0c01030000a001c1141c4035628074200b00740c003134008520560060100344580d50b03008041c1d50141598002c02c2041d612402025185031058219079600004100804250559001ca0745401039040d54201c44030310000100032012a2040c00d0010a008840c4010508241010002d0810700c64020182c0e880c0668420064004001c0720324666560603100003040168a4512044041e40c2603441041c80704074640383d0400c0c8564020f4070003080400740880070400310b402c42c048007098194406500c1850b0b100c841c5425542c0d0300b28034000200c92140081c540516500416264101c80c1d0001c4881005030716640c800f110482c4030151103800380b28100d2002904440c41c00b17054000d4008611440c3c0d215a103005200b88041c00a10030350902600c1410302c102516440c2e400c1c1d0864031003c0c0c181c0c1e02c40000d040100e007e40a41c0511035a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 583658093 1250 583656843 583656863
    0x60803160602220b04060801050906030c010806031e01090c0b19050a05040905070201060306051023040b100c050d05090d06090503041802040e10031703071e03050405011a0f010c02030a 81
    0x10b0542d50400040043c1d1302d030307602d602c000c5aa075030040ac5600002180c0240e09504400c0c2a15500c0d4041c4400580040b001030544006a410000410290a10300580752050703444050803001e01900c0d15174000540542c0001e180303815a4000182e218440b120000f03000c001001450f401100c0c0300e00251005800b401c0c200384018140a1170081c06840d160100351201c2e441d0001103110300003000c02420484410407020103d0b00441d8503900e000e038001503a6260031548030751048806a0306c801d81c00007034900a89800e550300c0d4090409614044490704480c092240c100244c0415650381036100e10f606500c03407400309042c4003918059003140560713440f01a250340016481512207030300b078002d40140c0e4000e80704180c842d030b9031081182c1202c0c08c40c40042c250911040c00c500c010f031110b9000350303417082c071a02f1700340120083c0c00b00d911191115280040c001960350400d0008001080c000c01040d41000798840000c031a4150005031202c4150400f603042c003101c0400402151018448018803e8000c03045c49 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 583659343 1250 583658093 583658099
    0x308060613030602130902180d0f290907060c0809030f030415020c0f0d020904080403020a090b010e030a0203030a0f0e04020331030e0904051905010f06080316060222 73
    0x806500480b034900da907002400f40c0450303406994401c0c0c403231400e0709164550040c1900c2c2c1c2030110030a1503140968406c415600000b0100e02caa60030340b1860820031010b90400c030040c1c500205c6903007010700600c580f500704078820008103500c04009044160010441a51101110006441c000340520200028000481c0c005800095040030401400302c2c0d80985414900c4481009128800303803d0065209014503c0403016040065900b98454411003c036454180c407030b0009202c0045503803154515540f50125058a96800311001030801070540090403400c005600098880c0544010082000750409036014414811201d294042002610441d541e00b0100342030800c01c40d87d00030b4004640c494140004000b19006100300d5001c0d090355070a0341c0701280004004401c1e0016009861620842140e4501c1c90203a8005c3e51106205100010310491460801c4003a07640962000000760130038406403010199030344d91040c1440e40b1000060751048001d401d40f0301c0c1c0881c8002c0b9002c2e484030501c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 583660593 1250 583659343 583659353
    0x102010e0f0c150c060112171801030b0d0b0105012a0c080d050c03031f030605181e060402040917030c0a02061b090108060105160b04140c03030304030806061303 71
    0xd40303045030607a151000c110421200151620881025145030340c051001004100c2c0b07e00e0700c140c071031442240c250b601072800030b640c0c840981003001c418007641031020049240c0d41c0c16104445014a05451200d580c800343e40b50310403100c2d0148030300b9051025005124046210b510001484208003500800c1038a5207030a0003004444940071701860b500c030309607004039941d0254094503080706d48540214a95514482030103103495880b03003980d001c0c458081001c80010102d001b400d00c54405c1c1c1c0c078000c0d62860440703401ca00e0300e074404640e6241c04000a40074004d0300390105460303501507015140450241080e10b4184107041c03001161a681032008024440c00b01001d1008001c0719040f076003151050386a12040000b2401a040c031540f0408040000d071000303500030001142e018005051060410a00c640c02c0e420042c035080003120168907020402c01000600031a03405c3d40e0b00c0150003800313008120f0f030120780c5c0d07840050806000d20401200085560360792030111000000e0401c0c85a061980d24a88 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 583661843 1250 583660593 583660603
    0x20309090601030f1415191e0306140405010f06080a020f0f04021b10050f060108070210060f0305070803121819030801060314061e01091a0a080f010302031002090102010e0f 76
    0x75444612880d81c0b9082d00929020325104c07d480c41c0392200001443c9040d044540300f40310032000850440961000002003a420b00c5801c0144940904003d584e1420380380150844a0041c210400302d80307071910500c40c0307100c0010b80390b020035415641c08a404c0c40100000d0103440b0030882080d4424000100700d0702070b2260121410502100400303da02070301c2900d6000c015540d0850301d8039491102c3c00c0010711b8a622403422070350440e145005941e18030080e50014407d440e020f800814185150746020010000c080080900030082000a1070402101d54140b880c0745078041e21000c15441410035041d498032051007030b22040040d1200c500b8200c1c1c854a006400c42c48248240400302c0e1030042ca00c0305103c802290544130740c1e80141280c01906071520188a031842c0c0603a02c0d81088500700000c9803040d5041018209002d101e40c00e161524500c3e00c004144500080545001e1111a001080140c600103a04109010425405a02c0d0410040100d00414410301c414941c1e2084c11456480c012000c90 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 583663093 1250 583661843 583661851
    0xf030d020a02030c01241d07120e0a0c1a030c0403020103091a2814071b14160b0a14030c0f0d0e0d050f03010e040c1a0d180201020309090601030f14 65
    0x4c50b240340c1680d41e00da585113500e01e511110075000040c01c000b0300180d226003000c000c030407035003000040c0400c03040c83c000c0d2801141034401c56500b0309100052005060200c002800dc0c11005900381c550316108a5040140c020f43c80002d05043d15510080c08122500b0070301d800d400001e180a001519089400481510200500d031075408100b1034103401d55006030003196403402c50006c210b9100c1c0c0b01e40304119414000c081600001205066440380011480c096044420b9042c0b4001d043d1885843c10241143e070856011145a1b02c0400001c1030301c1d500701d103400b00007071007220100d03440350b90b00300143d40303584038150180c2c10071030000a40000c416104e6203c98820042c40c801ca8030740a405003c15185803159254140101c642400104003010304286480da0061284040c000415070b01d4003080314280c5241000b01d081000481c4042d030060b024442e03a2440700041ea20140e0310382c0c45400203503c0c0c0c442e124501b8001c06040002640c0340e4065048100040e4020000f080f501d400c0010181512409036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 583664343 1250 583663093 583663151
    0x150102190201090b0a0f030b0a0602191e0318050901030519080d09080714010506151b03070c080d050a08070807230a080a02040b0a051c050f0f090f030d020a02030c01 73
    0x9000300d565818189d1341c16059039800d400411010042c1110780c0d8449000382c00455031501c00910b01d244244031105012081c6109456200c480e03003164400c0070000041e80c00c294013480c03144004001080c030028000485100030300c0301c810300300d41906001c0c0d01881901c020841940c10140703410100403002c001402480d0080400c0c40d8a10311051000f4207072581981e20540c801d00c50800307422079003241d00040401010b1101100c0c0042c84c0c145003e401d40e00000f0058030044042442004811014495982e05410514200d45460461080a00000c4c2c0103003400080204040c0000c480500a410004c021511201c01e040c08031203c03c142d81c4250310000c0c42c2d01c00100f014000c1038400034940251410354410380c41c00f600385040c42000315110781040c2e41d007507600c003d401000319514080f07119003401003081d150308148034901000d01e1200c2500280c51841c555000e103619022010011050f40c00201c00c07a400540e83e941800000c034914010320040d00059480c00ba02d003120313640c115100d001880110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 583665593 1250 583664343 583664351
    0x1205120307050436110906180a032103020306090a24090507201b0105040b0c01060f0503030c070306150e0903191803030c0317070215150102190201090b0a0f03 70
    0xc8140c44040d0b032003042c0d8241402d4014000700c6c00301d1030400050705103035511290305601c03c900700f40000d8020115510a459640c0c6c0b00e412303080f0310804140d4440340703542907003000e41c0b41d42000004640000e8000340203d0520359910103004184000d02415090104000c0d68030801d00e48550400000780f01c00d540e01404a844444030580c4139140031a444081d40308035002d804a94265071900103409090301c0c605040107010800860003041c000060a030703602002000003200c5007400d038015140c01d81c0e9049248660300600c4150f05c0c20400080701404c1c1d961000c4003081d400d50510241c4045113103500700c00b480300e00e04010003204a02c004050441040200103030200718813030f250103407440c500c5440c5a0701d0803d800581030020078004c10040d80c2051080c503242c0001000b0f02c03c54011150252800d10050300041840c181c001040d084050304030a100a031054820704050000c0d6503030404006028160300d039245580c2c150381c040c2d801600185020340b54556640e07115880209110720302030a1102003450 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 583666843 1250 583665593 583665689
    0x110109080c0a090509071509080d17061e04020a0e0f060a08040318051315061d0f1f021c02070b09040f0617100612051203070504 57
    0x100203200703004941e000d8a4042d085060244420103000010110310303080c03291100008250007071340a22081200b15a88000c846130400e41e0301070804010513903103020041d03403a50010300066480c0d19544c0044084400e00c8138014510b202c00c002c00000381445500603c0410580c80d182e401450341c03440c0c41d5088078000308410b02c2e84100100c07401040c00100020780c5020000d00024001c48803c0140303410900d45000d41070baa00c001402e18003400140d001441e40382c0250031100b26110401002600541c00e01f5080030980d0706020441c401c4841c0903d104456810b4030703d8440d11070000b9210000301d65200c013203c1c0b00181c1c3c4060b40e1200c244144031600000340b0032900d9054400300314141605c0b052100e0500d49456481040054100c2a00344001c29684450000c0e4100c188202c400c41140c800d00a1b00c40400c1c07098050b8100e0300d6650214441c3c0001030f0007140045c0c070201c0c22038606110702448588a0b00c9420044400d8001c94100307250902e80e0032032602c1c04c0500b00ea030b000d4403890300d00a00c8101540c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 583668093 1250 583666843 583666859
    0x5010608010b0706110a0905040612120c030c050303070f030e0a030f03111c06051002060709030b0613060e071d180441030a0905010f111c030b03060705070f06090f110109 75
    0xb2f007032440544005429041c400c091446540200460b40c061300c0c100759000a0703a02e555080d03610503540440410b440300f614074046034050041d03807200215003000c0c0c0241c03000d584001e060f00c2c0d81e505042d001c0680d2003128054030071808082d54440b116000d00454605040a85500184454010301d4411141c2100203111184000307034071881030020f035030750f42d0009140d0365842c40c0468001c0d0050350710428034400140440a144640da00030300c080c28844166003482400608859442c00c91910802c94134840c10880f500c0302c400e65001c3e01c0170b90b21410981c1c0c0c0d540c107000b21040c0082d80c40540e096210f500c030000094004401d4103860440c1448907040901855030582c0d2480342c001d86030041031603540300300700030340c042c04540e1059402420304070101c003842c495490400d80b20746c034141508002403404a40ca240e05110703204d80140281c0c0240100c3c03c1186016005028000c0024012018a501001000426002515040d9000c01c2c010380d50400d42c0b0b4803107c44021220300500084003d200028040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 583669343 1250 583668093 583668119
    0x106090b09011a16050a0309060e0a030201080c0318030f3004060b010e1801080c010504180f140903030a0f110405060d0b121f05010608010b0706110a09050406 70
    0xa1985440f40200c89800f0b80b107082e5640081c1103c0c003c45000307210600101d0814040c0250040c844d80d00c5c101c07181d00302407024081e41c00811030346009000e4403200f440140d81000c801c42d005210034043e83e8807030303444d1650313100140c03c01b090800c890700010484404001b00d880c0541842c005003c01c401c0c0c012126131038800b130581c00c541981c04144441d408240855401d921010703c5c84010300d4108442c0241d000403900c5640880076902c442074801740100180a0305020420196409290141c46c083c0351410766943d1034070f85403120a0140d6241c20000301a00b25034400381c00704181c41444070051030085140c80d01c98000701c90700e4841c10f040400303240101102c2e01c22102e442e10303040c0c0d00324185400e0600344189a001175081d1054682c5d2140da4281d160b070740d00446413114855000624000e4100c010440b403482c00031169850392410a801444001e800c60b806506490301e48041541301c1c007441c107151001d448903500aa0308a40001040303141c041d403004403582603230402d1398203018269569004002c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 583670593 1250 583669343 583669349
    0xc060a09020616050a08040807060806030c0d1403160308060f010e03060703090212010509010e15060f010e01021006060e0a1706130f05190213090f08130b0301080106090b0901 77
    0x201c0e082111549200c0d00703043c80e680d10750144040341c440c1d1041e43e5802a55a20540040c142079000f504200700380c82d407050806501c200c041d0f000e40140408040401d10003685c100005003e0109142001ea60007401c000365074407034189002100c0020198100075002e484207030b07252800380a000c281401e940d4000c2c1424100742ca000740c0240b10030381d00c030f003012002442e000340101d07444041c070301001c85840024050301d0f010380205000087c40380911480d40386070141903903c08c3d20242d1504100001c42e66840300d6020381c070400b03007041d002b41400c210040382030041c4c14074000305180c98042c1c041519a445890500040310a41d403031041641c56406025411240e10383d5803405a02200018160384c1403914400005403013540c010314a038416960f03031424404100c40001c00c032081034407003006514141030b049110214010041184100544803880d41c02c000760b101074401c1c0300000d844844d448440c42c07c403004040c8010602d48958444507041c1c060308441c81a025140e08004a10600e032400b25034050407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 583671843 1250 583670593 583670599
    0xd0903200d0c060e010e24070c0b01031101032a0801090e10020705070509240f0906151608030604060b0310060e0a0504060902070b1605070803060a17030c060a0902 72
    0x70b0b03000581e5260007400c18560611125525812485030240040040c7e0301020103c1d06d07240006050016500d107007400082019081040f0041c407200442c00f0300010605494000704114540200400181c0144c00e044594500c000054110301c1da41e00c3c00d6a0403a210502140c4d0f40e015a640d13030300000741c1641d001044140e40c90300003409180c440b10259005002d00d51140d0240d80065a6800000d00c00c12411a6251001c02e441805520741066000031200c42e054122004242a401c140c00b0590240d0000c09182c0a2080884080051411081600c45041a0841620212a81e450b01c2100d540040e0b440b58011070520101041314a0450152031150b0421790010100600c0d120007280c100408203a0b00350014407411000c255602e503400f1340702c09030054241c09a50b4152618080d000041f0042003212280702903550f402403243d0000850342d0f05904012001c1c0c89032500800520b68510783e50015589406198403400ca4500120217494040900000d94030596200c0d0300000586882c204020741c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 583673093 1250 583671843 583671857
    0xf0105010206072c04060b0c0f0706050d090c050618040f020c0a0803041511090111010b01051804110c010e0d0305040f02090a240f050105041a0304080d0903200d 71
    0x42c0d04a038660741e00c0c680d10302d400a064404c90b2100c01203001c6030f1072600000001080000d00950014040261142c161107050050103500c0c0b51200003400313806030707072072006045072281012001d224010320200c02405d40242201d039643e03501107004104550700e840050007641404030f909005215803090310079500c20030025000b0560281d490003003d42c0700500442e86030440c1c002c03089480c20036120350b200036014491400d40c3c0d8204030001402080c481500015075a0500c92100e4035640e0200035101080c101e0f140d40b4043c0e90315040040c000d40303280480c080310000b020808400070b460541020580320000005d50351018080801201075a8080740e014160400001d0b0300d00040c1009004107500c807003100000240164101050681e40c107034211000f420035003884090201c01c10b461503d07001040d0900300f6a24141c640405400801080c40c188144202d02200040900071060111410721505140400c889452454040c04e503080e41c0010110400a02d031350400030050014044032075118030780b41c4e90 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 583674343 1250 583673093 583673117
    0x501062a021203160303061a0c12030901090b150f1005071104020d0e0601051908060c070c0e010f03060b0d0312050619080106170601060f08060102240f010501020607 73
    0x41c0c0405508650180b8882000b81d480900607115107440e1140c802e1b079010a245207006541010ba00b210403410321500c00801030181c130250300180146a00c3c0446507496201da8880c000180185043c41c0701901e02c0c2d86080420044e02c02c2600c03824441c0e0000c45150f0b030724a601405001d002001c807401c1002145c0d0402a400101b40480812841058000c04c05864010a04000c030151584c0e41d450080740e5005074010b100f58a00480c0400c40c0c0070011b01c180740000e103490461640c4610143c1044c0e013002d00000c821052191000d40600070b051400980b200c1540e4603172100008600da4401920381d24039140078290b0502c0c20362003089445070556181194402c01c8024040104000307031240d607001c460f0843c000c0010043c0e041c240c00078003490340000b408038075122000300c409180c0c3d40d8800003600701400500a80b81c12140c0865075504034549078603036564400041c3d184c0380040045101e941c101c0a0250b01c0071207040c1510303214800221200f44c46982c0d400041e030b59004161072039004507003c50707190 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 583675593 1250 583674343 583674349
    0x13020a06030207060213080a170307020a08031f12030f050a0509060c0c040c0c05060a050c07030c26190f0e060d090f110901080c06190519030501062a02 67
    0x3403e225801110018a04480803219603c410b8140d0f111244542040310070605000f0000900c03c40740711545103092441c40e100b02c000b5101e00f2080c100825050303002c004124109600030340800801103080c0c0804070f003a15601d076042041010307607040700051604120400014407c1003900d00300e04c46a00c44078188030110701046030300d030019040100c03d80b0070040d42c95656912030003005810141a1162100013101d814200d0500e00300605018809003400309101c1c5651540e0102c941451300b5140401911429113000020512400c0840c07420807000c1c2100b420500d8007100400700000040c40c82c0b900322102c040d042d10110400c151007400300d0840045951142000c50051201c201403060014a4039055550000700007201c0c007003560445c9044c99241c0d00c1c2e081ca00031031809001c030040181040b101050010304244250088805040041100501d10300e005205582002041075644180008614002801001c091181c5c3c800940d28040e001401040e04e24a1207544000140e0017052180e42d40038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 583676843 1250 583675593 583675597
    0x309150e0f102703030b040c050a0e0a030c05090601051b060109061508010b0f07020402070b09070807080606012319030b060a05043b0f06060a0c110109150206090613020a060302 78
    0x3c00d030141500c500d05458141c1c1d07581b0644040c00226103c003a1100030b040001004445103c1129005a005000610100d0503000d1180e0450b00d080b0344190b001d690345c100481d5940186101d107441c07003095a003009003020010466074140c8400782e10402040350742d504401d104448804d00800230031380740801400b0081ca0103009145c0050342c215002d25003a0740341d000c40e00304c3c0e100c0742e01070b80c0d41e489800c1445603000040c0700081c01868004003c01003103080c444465211740002d44824188460544a040000104041070141800044000b608c803c00300002c907040d01c88038115580082d2920390f500c1da4a01d810400d0750414241c036036a4a0400c1d043c4410440056400c81c031125040f1404260744040100502e40003001c501060344d80d10f014200410b105070124409440240715140c10f1201c401d01e140d01006903a8059001030700741481c3c400c0310700181c41c0e9607100d400040c8074003503140010a28a40010701c4070b001c0c10404048446542d00c00602d40b40398028030000075441032104104104a507c47d0300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 583678093 1250 583676843 583676921
    0xf06030218040c0f080303010f050405010614071a0a0506030105060406080a0f1b1e060e0117060a0b180316050a18020c01020406090806100807060309150e0f10 70
    0x1d2602009445130203801865a46911444240d44000b005000c18407002440d500140000e840a008a50500101824803400401180400c2c2000300b101c00038030030134400383e0410030001c400184880c00d0049008024000031079070380b80250b0820000c0350b11400c0c46e12804040307070541c001800001800365584016100a40000d603250034425802440d0b0007200b036607020082a1101c0801e1039100703000b04400090109500840c21702081c81842602e41e40c02c840801d04e2a048040c42c1c040a40e107d50000b02a40c036141c0040c20040f0300400c40b826070641c100e040d201c2e5410708600b01c84080d40c6808910b900300860740181500104100010014514000d491042441c14414054100f80705494842d0880c1c1081d406600002c0e01c00c5005c00020106000d01a04203011203c041e1103103080c4507050b41e907000d041c8100d1b02055a01c036000428400400340d03031800d40c181c800060040000411b082d0f9520940c1c0048554240126040c500e00301c0a1480388840a281d02030440403041a060311500007030380071807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 583679343 1250 583678093 583678103
    0x1503090203012405090c04080c0f060715020903010f02190807110a120f020309030a150902040f0f1103070c030c020609040519060501020a0b010e0a09021206040302010f0603021804 79
    0x2600c0c0038440115400001c0307845482c0d40c01242c83c02d207054200003c042c8040c003404900807003088280400d001c04034008003170040c191120b070200c08220b40401c5851158800c054081442440b18105540321a0024204604101d00910203134015400d04400c80c03195401e0a0414a207501e15101c030140103d0b070700e945c803040038101428820801c441e0b003420b02c0c414403000c907220042c1c1c1c2401600a0b402030060b01018101d0b100130b5003000c0250b00400e0f0386240100000c0d201200c007001d406030402d410341083c000c0544c00750040c0880d030004030801e1701400e85046620952420034040c4540c0c2d103e52400d032480746411380d07900484010580c4058030041e030300c04010313a0800c00810502e902a1164020907018102210220013014800c2d1400e800301c03415900540e0454010051a00110b2aaa68041c0c15549502038178646510340740079000040455080c02904007004c100031440060011a841d4840e60003500240913902c000841a400c43d112800021b41c804002032680d4000441000e84a034003500c68 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 583680593 1250 583679343 583679351
    0x32a09110c03030903030703360507050d0303020d050702010b01210f1e0608060601050d0203130203010c12200f07150e1608010203040b012c0c0d0510150309020301 72
    0x100071150559208072080c403000d9100005000e60035505109800c003038850224101c1e000e000000c6911483c0084131420800103081065501c1031010512541000700030007844044060020700c1c2c064041e40010361580e4045242c10005124a4018020b0701d5900505035610414840204030700d0400080e1001050040fa82c0c0315403034810714107a40b041c0409180c044d1205505440380040c040d06840c02a0820800d64001c4010701c549d86e600201515000003400a001d61030340d4030500c494003159003a450195156080103200296942c0000c5003800390040c031101804405080c4c5c107404558814030a00e5001810100020b501d040e0f40c880c080c0440d00c0c03090003c07820660b10006001c040d14030705642d507612900071030399070050403600c0920031004101c1c1c44001d5041d4a066203130220030300780c144111015110312030603d04140c0032280341c2e400250ba0038104050311f0b050102441200c0c1d0480c00b2311101213490710011131044030340b404440c0c2c111903081a2107040240303139600440250002c1002280c041d925 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 583681843 1250 583680593 583680607
    0x1f020604120212030106051c200a2a05070b0307050a14092e03140406151505270901050f120f01090203150f040b2e032a0911 55
    0x400fa00a41c02000715a5038107440360070354030310840c0c1a003180d100920b180c0e01e0140030031549415000103001488036000c1103916000811025503015034140300300d041d01e000c0c0050707020b0381e2801ea0032036051450140302102d1081d5161a182c008034031050340d00e41d01160084c070120440b1480f40780024842c2500d81c00f4142041ea80b0008561b0300507042d00b00303055414100c14400ca00c00791413150100041d0552800340a280900034041000c1a0b02400144c0398944459515461400214111000303040b030b542c81c00c00304000900000c01e16046000c0e1403d0301d286030011500b00900c0034481281e000001840a85030f40d1a180800c4220221069459000710440c5242031550106010050710040b01e50700200f0b0740401c030320405050541081c50b01c9512090102440343c0c08800d00c000719032081e4008a014000d8690b034003544003189641070700c040010600000c0490403c8240602e81c1140e100704070041c004c4039030800c0d40c3d8480110038482041c0d12403010b8100250705503a08240f076003005010101e0316002c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 583683093 1250 583681843 583681873
    0x50a090c050a0b041a0909070c110102030403031b0503090303070305070302070f0312030b04060b0d1407140d051b0c0c01080603060c0904020708041a070c0911180a080106080a021f0206041202 84
    0x41183c801c80409d030000102801e1040404000700c54140c24400b95160a0956038003604072159418032442c400c0c0c141d9804801c00c03008000f00c40e000d407002011a61a26903900d0014a40e40c40326504500501407504005405030400744181c05503644030801614039005440110010800400f82c1c0e0740c025201d00c40064140115401004240e804080101d00c05c2000c2103c54490103000e84107404000070034940041c03608219040d01c1c21f0003107455000c01c0f1a1249a05468004039114018a55002c001811052841d0026030382c2d91100c03007231300c031030480c2c0e500c00c81019110314049800c40110882000380d1202450264001c0010502c5500c2246c24141c8840c1c0c1c0c00b0f031190700c0801d440501c103c0005d08405118451241c00d00800c176404080c000300442d114900d9041c0038018941c041d90320240006c516940c1c03441a110060f02d401402005560341c0e4002031075881440500c181d004030000d00004d4070141002403405003820340c60300202003607122039503881c4000413240d000c0b400310f004441780582001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 583684343 1250 583683093 583683109
    0x10603080d020409050c03090a03050a0c150c030e0c0307151101020706020a0207080d050706020d02120709090e2113080d05041505070f0602031801050a090c050a0b041a09 75
    0x1c640c1d400180c0301d40c20700030100121400500340e0400ca00041c01003150752400000c09109041e810315016460b802e048100707031507410f0b449400818019070800c6440070b100e0b03d944803201c240c1ca6a03500b80010319245044584501c6654941c9405130403201c0c0900c82c0e0560744140d1500c8072410b2070803000300d00100116500b243c21000f011102c0365000140c4003410b9034100128006003c0c1d0724017400c040c41703904101400c1031058074ac008003195004108518001ca09905592101040c24840006458182c80080c0b0003181c0307010740030701140f610b410400311030400902c164030303505140740042120094002440c42e5030014243c40c0c0305074011502c04103040b0f400b8421032402c48100d0700c40c582c036241070443d5040c400449804207420042c05009000208215008a14013250001e80050350794440c8464100082600f03aa0203030150b08000c14090100916801a68158040c50100340d81c1d036292001c00205441c00d202c3c10015510900082c48044403141082ea1101d0050b0800d030314003e00000408c401c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 583685593 1250 583684343 583684357
    0x9060105250b010509090d1419020106050411040e040803040f021009030c050d201201090b150405071205060f040e2a010903141501030b100905151201060308 69
    0x4840103812080070401103090031070242c1400c0300c00c105a480c121902550707d2074122200e40c01c020f0000c980745803400e41f03407007115503501c10090400c0c1070000c00342c40680a0106c3d44a5503014528000e02242250b0781c0c0c40c1550185e84982001c500700e038aa54840a425030005001139414001e214401001682e8000c024103941003a5203a100000d0b00c1c40c20024007a5500d5407025004030300302201740000506c03004183c030390403080840341f414910806020600b03a0981c840100b2456103000c0e541d50a00485103003043c410b07980030032020034030300421060005451040d61801e001c1340a00110903440742881d000710780d001c00302070b04004030071032410002816504036248103106504241c21a84c00d110b42e8034041503a525110460392500c801c00700000306000c401b40300151455252204410b030003007040c8600c07281c1da682021115515611f90500c00140002070700c21000b005ca08a400281c0c0c81172602034244509907000b041403514005030240652451501038544455688902c04030000c1c100c200036004d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 583686843 1250 583685593 583685647
    0x172403073303140a09050c090c04140607050a0210050c100605011205060a18090b2707120314070c0608190e031e0d050a0902101d09060105 61
    0x1003268a0401070240100940c075410030541005250038150150541c2036810005040e4001000a03803800d100d42055030710305200f50b2100941c2d003800070101c0b00002070402d8075402070111460a4105d002c203c2640300c1caa50003480c54000ea01920003600e0882aa1210000d2074205940f500c45598501d41c204508502c001004a60300d00c014065568846001c017020f4206e0700d001c00481c00e00c100010644801442880e10b0040d01088905002e05030b5003140042640c4801514282c1c100407800443c44d06001054458016004000795040d21001418070101c135a0100a1034203410281c9003110461a111402c12400004002c0760000941c1140402c000307065564600d411800d24000032045030b041c004004510a0600341c000b51401c03004001c0710242c80340d1440e8848030034100440703c150381c06050314901c5140d240c141040701036050340d08089a43c40c82103400e403007402c007a030400f501c494200203a08046030019420240490808100e202c0c1c2264050603e142441c8015001b90150051300400c404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 583688093 1250 583686843 583686899
    0x1b01060902030709171e0a0803090a05150c271206010e0c0a080c1303140f100204080604021306050607111207150305041a01060f17240307 61
    0x1030042d9020094001500c0040c2400c94100e10b01d401c40d5603203840110b00c1e0202c1800c03e0031b218090b09400c1001f840078a501c100c0701c680320315103c040c60380c0345c120180c3c05403001c0c0111501403001007030b4105954801e0312030103d918242101100c098400078008800150441c200c0c000d40c0a0365075403170011100c4004010000c00c155814031a95254001016120200340c5d1010f011043c18207812503201680840301449a0b915104031f00403020060b00b03d54130280c0016160541421170707943c04101084070f014040c04441142034070820b918101d120344d1190207450303000500454010f00c0d20540b1880c1c944208a0046015034843d4001901b03030344211811240c212100c0c00300b003140d003041d4a446050441c194048c04409152404032216515010403103010155100000b50410215440c5010718003102c0d0700d103000319a12403030007400740080c1c18031003804500405045181501c100391401d00c2100c0c45110166048416849090400341041e0400d5043c0030700302d0046481c43c20300301e84010003c0700e100440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 583689343 1250 583688093 583688101
    0xb07021515130b06090405060f040606090e09061e07020109050f0c0103061406030c1b0a03030b01080a09080f1b0a0c030312020301051825020705010e1f051b0106090203 74
    0x40345410803030020480c0b603800c00c0321450300e0755982e405543c600c0c103043c3c9000c20f05560b00b2000440080c000c5105980c085e2600e84086902d503845001d20054803c0e4a44207211502c0301c0003420741d1008111022030042045240b00c1d062041400381c5190041042d0001141007802565494106880840803007587d51082135070065540c0c2c50b0065100410907100040c88004025010640300e1000a1503014200b00004a81c82c2208e03100d000c00c8503145c101d60a49612040e2490b000700039261442c00b1900003118900840e000443c80e1181120707030b55220b80e05910f00000e02c41d5081c183d03000320780c1614000801114815160005112509480388601401c0d0426070851a000e006c0300b01c0c1000d480c1c802e510520040c00f66407203000b4241d0b009880000c00c501d4540e1294500c0d5187d480701142003604039107900c0c044400a030001010010307031314240c80d00701d11408000b0602076040403405040301c2c92140c48a003190040d001c1e10040c1951b030801715402842c54840c80c491400e40b51180d110003103180c0e0001c100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 583690593 1250 583689343 583689349
    0xd03090503131e0b0414090c0f04080114280f02070b0f07020609120a0e040905030d050405060105030a0f0b060d0c0f0f050105031e151309020301060503030702010c0b07021515 77
    0x34038040c3c0002600300d401c041c00d094003120400c0e041b2503140e00401c114000b18286040c000c054403100000b0103141d5503210b4990504034040c0505a140c070b004003480c800401d030034140c4040b070a01c0c1c0003009101c1c40c2a104408400e18041c2000304c01c492100c640c00c21858001c50324800c1520300c100c034030302080b031000d0500d02c200034604800145000411f4214902240f06d9100040864500a10074500070107001c0f0394000140041804100051182c03000103202c0c07064800d0354120610a9001c1c000303881003a80c0c0c07034040c140c80b00c00c9100000c012900c0130400034006052070790003a81288015280084101c100e0307890701e034840440e401c12203002e0b40309502002118460b424000113000203180050843c14074001c3c0000501641c801c0d00351107001c1e20b0000d84404445031854001d014018900c1541300718852003c0028003461700140d0083d400d20002180c2e500740003017142e045a034184c0d80c036840c81c0c201780c45100c000070f0068a410111300406400004c00140d148003140038000ba006050b41c01e120750410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 583691843 1250 583690593 583690649
    0xf0815060d1d0618120903100626060903091306030f051f0606090306020304060b220f090b130f020d060b030d0c0209010b0a0905040f0203041e050d0309050313 70
    0x14000c503104d4502e0940403031900110b500000301c040761820589820804000908200f40c10300000395044c5019030004403012400c403c1a0383e0041c400c0d0503000d04004d40c8085440f042d040340c2c1d03004542e004004520507400c1000401003001c2e0303903403800585140c90b9940e04500f000790b0f000031382d5036900000d24a20b0f0004108020703018108110000c014407450034901421031540da10014007965408800141404800e0b08807046582000b0b19140c01c100b0350b1040d080d03d0722000c100c803000c05460402035121256a1b032007000c0b031447e0807035200300950342d400c040c00030102101c0038100e42cbc60366a280c1c0307807005131640c011080040f40710780c00201d0300440c0d200c241442c00d00d103800f11000300030500745034a0258035000701445c1503c9490703403040d43da40042c01081e65004040d600030790300149002c0001c803005c91a41e024600452041c005620100c00440c07103800d10021900d000b4100e9044419050051781c0a50311001c0761900c0380341680d090210a00c0c4800c1c541400d68821b080514035201494a20314007005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 583693093 1250 583691843 583691851
    0x4050a060309032703110607021513090e03040b0721080604110315040209010c08070b0106080c070c0905190905060603010605190e09031c020c06070f0815060d1d06 72
    0x24030068091341c000d001840c81c0c1091001420308560025091029103448003103d2990350040c1000c1e501000c101006040c50b441070403040804d2030700c03c1d00031440201c00d0041a0341454810000c6003014180b00758440180c6c000c500c111045c145076050786a0b0780c9400c072889100c18415454800c441d1400302c1c244029542c10f001c50700d000110400c200454480088112204008141e0340180c5564203080107850b47c1c40410302c060301c191004141c030820031044c080f2803410382d051641c0c1e82445031610603200f0018000c01100034404501564280240c8407a82e0100d94848800040208080c1ca0030800e00c045a2010700d055032190400390420141e41424000d050060009480308250313143c0083c5a00380d42c0d2101c1c050390045441c0e000214003003041c10070680f48845c2c070494034050507a0910010394001d5100c04855507140c051000015100c60083c480c400c100300c04c0361106046691604c80304150742d112000c0f03165220006002c0c401c074000d00c9210300d040714000001c0101046015004082c54190020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 583694343 1250 583693093 583693127
    0x11a3105010c021309060e0307150b01081605130e090d0e010e130906112701080f01031e05010f09060605040e1c1b0606061e09140604050a06030903 65
    0x90342e25030040e190010b4500c0b004400303101c00108108180b8200000c0c108044c0404080d10000c1102c4060000020721003403442c181d200e08000c14003001005680920046410f81c0e1008240c0b2040c61200c0d001d0350040c010b004283c01c00d00d165a1b1604003c4080d1070301600c8290f00c030351000280c000d45030b4110054a08180c02400c00e03404046d0300d140091281e820124020341401d44688003541048615041212409e10401d5031a4640d18804510034048008200a200704400409140702c6c550203022034138003404100244028981c00c0d5102d01c070450507003018407000c4221240e40203000c61400e2140b8400655a08004200da00c698204041502e00507000148a07a2600342403030a00d180c0001e003951040d500c0c3c600c0702d0071071115a2060700c00110136040300141466482e50354081040c1507001c14159091a03d8038100f0140032440b4110010404040f034001c134003064818031000340845104a0752000c000c068529158030384000c601d0403111640160040381c3c850351440b04060300101c402c00010410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 583695593 1250 583694343 583694357
    0xc0906021506030601120f1a060321090103021b0604061e0e0309010c03021908071a041a130c03060c0801170a0b1005100f020f03040806011a310501 65
    0x90003e92141010310070540c280d82c20140d40010001d0110207a4401c94110f40048003e84258001e05032500045811368801e00a455011407001c032451062800151500e102a051010640042d402540320001400780349030f100000800072041003100601c5544140c802181c0c00d0183e6509805040d480b4560703c040b42c3c200400c14500d1480001650030000d82480d00000010003030030280c3c1480d52080c041c1414001071490001846501c0c0010000588180030b100040da541304a8054211030942d4000c0c0300705208504003200a800d60303a0b141d04603030714214814956040e81c0e50054410006d52045503040c0d00c030103140c0710f51a044900c150040034548050072119001c42002900c412031690010b10020b180000725080020f088d56800242c0b0b805460021401070f400360140c404003800c011600144130b414240d004e807240200555045130305003001405c8503420001e45800d01e25074200000c124140034001d107030b9843d1007000e41408121410b801051003c9481504031540706503604113038140580 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 583696843 1250 583695593 583695601
    0xe0705040b0105072d0c14010302093d080901141003060e0120090f0f0d0308130b0414060a060b0a030c0e13020a090905070207060c050309040c09060215 67
    0x50460380b20580c401000010317061500740348500416007184c41203c20b405960b02804005900c8035000548480300c203408000d00d030784c600440c185d200301f00c0400d4000c0c00d00d4540601840140024050b80c810b2268000034180b81c500e44800160408040d00c40040c1c05d020030300c0100f0600f80300c3c041e20032401c0f000e140c00d149481201420400418030004060380d030b80d80d1400101850030350181c00345260400011203040c030400960700b240d070400c0540905c0b600000c9a500e00da071070100600354410b84060503402c41459191001d84132490000d04414034150030683c4140090b07210907159114074030400b00c0b1644002610b0300c4502e00a0700500458940346071800501000042c00251820b5038011700e00883d50743c0921000b140c45555000c0300e19042064443c1c0c109290201c0e4019140503201c1e90740d00d0300c2080d900c2501c0c40a0343c0d0103407040d10250704032010500040e8480c0c0c4030494023038050720841f0303d020580e42c00710b01200c2c026007032072001842ca031409200ca00e2703041c081e032441c441b03034048002800d0070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 583698093 1250 583696843 583696847
    0x40803030408030a09022d010306080c0d110d050715020a0b040f0317010807090b03030f071b030804230303070c0e0a0e03030a0219020304080705010e0d05010903030e0705040b01 78
    0x80060301c040e191040120001c0c54500941e007082031590390180c81038210000e60400d94000c0c0318041105074a4040700001025154400d03c510740454454000402040d42c0940910091100108040e1020002420320351455129039034030070fa25a10440082035590b24090b9149684a041003a0740219003100c0103d0000c660540031030358000b40c1040d071a994141c0c40786015126090f00009045075423501304c00004016402041210880310003e000340a04501c0204140d240d03c508004800540c0c0148948404141702c01044c80b0001c8150b94041e642d242c403515407030301e10b402c00ea10241003100480d011400e01c004002c001c0c00700c0d01e4298001c500b030400c1e0b0f03940c030161100d090180c0ca880840b0b01c1c0005101001d0754108130300407003c0da030589030b59040400d894000703544080c20148024071210154030304c15100008540c2280c02d0300303014068035400d042c01140c9015503190320303540c000c82180514000c03880c00c0c81003141c224465100064140300075030241c1c1c240003182d4016849249000f5100c001e81c0d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 583699343 1250 583698093 583698097
    0x2010f0203120615040801050406090224031f0317091905060304140316060506100f0207090902040b0a0602030d0f0e1e010e1f050c03070504031202011e0213050402040803 75
    0x1000c4a11400048442c01385140e140640d60180d00a0341c20310044c40203000056000c3ca50315402a42c45404074203030751444c5007807084404a40707061600b00f04005505944100042882d0110282502c140707107689882e00506821700c1280f401c5442d40000c0ea1010364034010b1180506a04600c4440c80f00c903107000002412808010005443d8061404c41a44a500d040c001c550081c40781c29010302524480d030804000a100450340c16000c1c0e642100d03070116841c083e000c001a9590540c0c010300540d03003800246000790481e44422a0455100e041d5603070140c0e10300c1d0030480640a150300641c7c54550f00c116110030740c2c00b8500100c00c1a464480d0038103e590021503a50201c40014825241d000c000002241c01800454600c17004c90158495401304180380b0030217000302e074190316418031050f16240764124562105075904408640c3c10002040010781509000132001c00c0c0d4000011130610040b14603222201000c0c0001d41c00b41d001a174101116014110103001c0e0001385e8045040500348250540d030784c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 583700593 1250 583699343 583699351
    0xc0c121803060e1005010e0f13030203040503030a0f02010513120302072a030b070e0307060804021807090807080307050a14101806051e04120908011802010f020312 72
    0x4845016400c1100300c0c545110402958400b4082006440c0901ca03039489102980d40428110b0412000046e80102021042c0c020520380312300c00047d03120135584403145040c6040c11015400f0601000489039400e1029017206000d644450300044032010300282190303002410118603501d45220400400c0300d101d00408523048a0a006a07550018100b0381842c8d030804188000da000c2100840b403031103403143e5414048a210386d528984503114558180c0d00c001c0c00c001d5203a0142c0c0329400c104040380c459543c440c2c0050014020690309000155618101d6108403900004160f000804010100382001208000c00020018504000240d55007035281c484049002e8192100b0749680c6207140803d000c042c4000d992100100405507180b00141c2e008641e00700c064038801c0c60a4001080d000030900c16042e0110324001c40785907030303446643d04001c42074500c1a850402c694a00c0104139aa024481c0c40100042d0950b4181c0c1d45089200040c00d000641034420308542040c040c0daa15410341d5081c031500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 583701843 1250 583700593 583700597
    0x100206070f0516060f0b040b0d0f0f030c050a0b19110910020312090703031d0f0d030207050324090d1b03030b28090e0d261006030c0c12 60
    0xc2e5020004030a0104121600701030130503031178101640d41c1c030000c6610010904105071000d2102050300c004200700343c030b101200540381c0b5a240c12450005801e034a00410141d119040c501e090002903100d8a14044241108176005c1c0000c1d000d0050881e411852800398249807002030104221682d010f000500801907005d009400c0101da6081181c0284103642c041080d880b43c0c0412072519070a4179039203a400d4031091f4041002c00c910030400e0914020305080103d405011b01c14000159018044420f20040d415000c60150a030085020759080c000c980c0c030322502200380c00940310a0110503c1d040409050036100354000315410903460341044102d9803e8103001c15600020410382020340c007a003420500140d005211740400c0214441c100003a40b0a2058108202100d1b03494089050480d8580b109443c140e41c0201b00d10308020744550f205a908010004908111900300c0c00380c100819000d40d145100d04c0e00d0148140081c55051050400c12100c07454144001c0c200c603203541034149111000601 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 583703093 1250 583701843 583701847
    0x80609010f0c121107020301110a030c090f03030507020a08010f0b03061f030803090102041806060e010215180f06040503070219030213020c0f0d030e16050a090903090b0d0605100206070f05 83
    0x142d260001800d485d0700d01d070003500038844100381c40e0050030070390711107810000401d01d8007582d103034043d1086402d1010f454403d80090392035400c41d1030541e081d4004040803a4030500c041c5002c540b8007428003408441610310b10003c9000644601010300701072008059540c0d0034908003010010305440c103e44000c8a4011801c280c0d81e842d804041400781c41240c02140048a050104640c1c004e800c2c3e00400440340d2995a00c003104c0070382001285c4071920300020f270892030402400320b290759407040010003003914002c046885100c16160309509180040310127880507040400c4031419800c08501c07178241c22550002011069045500040c0c01800750340e5100c441d80c1d40070410728000501009409a0540c1d50401c6824104560100501910002e20b160845004901c1000c4402650b81c080800b41c0c0e8000300020390a0341070040c076000500707510b0802d904003c0c80c00400a40c8159180c0204660060103030701040560908081c000458100348070201158021801c01a11507400940030714984918500b0035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 583704343 1250 583703093 583703111
    0x6031302060c0312061003021e0307020a020301061e1a0717220303110d080c090102070e0a050103050c0904120c06110408060907080c0307030b060402070c080609010f0c12 75
    0xc0c0d6500502c81d111541d407000050030600540e044030060b01c6405c003100c031070300300501050048040e401461524040032000c000220522092a0b01a6511510340d10489100c810260006801e5031003903030010300a05052460944058040c0c501000039242c000c40e030f4210016002a0088240b013954400b07400b14480c0c1c02400c444001107011603a0034890780d015011000340c038142e0420103d026120480205110390a500081100030035075050004003915041402d5549000c607413aa0750040584504500600c180807540c1c15401c070126009a40c0c0300000546581103103052441d020110346032500c6880031004020014505c0032401d03074948040e241455181c0c0c003a213803201c040c000454a03446400307004607001c00c0700036001803001d2248064404a49409694100c2c254a030505103050302d406410000d02840423904984070f1941155014200502d00880c54481c001d6959840c2c00408040d000041404000c40c824011500c442c0110001002075840280c0058190100c506900e000c0c0780d1107224007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 583705593 1250 583704343 583704349
    0x1d010906062307020402040305030309060a05010501020d08090106170a120c0818041e0225030203040b0c0c060f0903010e070b090f0d0204090c1517071b14070f05010e06031302 77
    0xf491000d80e01a20654441c0d89920380180c40741c0084449d401241301e60000544a0105401814100d550607000343c030340141c04440403242200002c10212072913481e0000051032411000320022101c034024042c4c840e0700051300d811540030040c1c09100702001180014003002c9400c600032285c4103084182900301d8591103402007000380c500310140d113220032440c4100000461007a0018440e0a2a86d001840c005d04480b2241e045000040340103001079100703000611000350108014000d441c000c208589004e15114005807031503010036900f4504550100b40307000030b402c0074050345885164800103000b24504003544004923018111236140724012041c4086001d0301da644040c82c515030081c0c4280b1100c001030030b1802e404000c920410001c00b20152185c2000c1d0311648c1c07004280407884e0041d49543e21034a10480f16040c40603040c95a074003c1c200f210b0300107580e0070402c004031040c07400980356003490014500c5010b8003a074840d40c1409010003040100c3d81d11102100c5e40170b9045405412421414004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 583706843 1250 583705593 583705597
    0x307080a0b2202041e030b0106030b030a05240a14042910030b060a06120203040c150c06060b07020a090507020a080c071412031914041d0109060623 65
    0x154481c002c480100d4000308031119002802964003680d0308909007008406009030b100310511015141102440050202c0f43c42608a44501c046c0142250072a80300c40e01c0b524100b904140c410540402c440c002c0050403240748911940c002900a4100040d0707000c58014201400300810081000c0c00c4040c06421b01d000851101c08000030f109240303c054a80300d481c602c6c0300c030050300064034840f003034000041442c50180c1038030003526100d0b590064500b000e0a85440a0741014004a40e00c0d0354090003c40c2c09030000c038039800e90b01c5499592025004060515908450340c43c1c00200c681c000070040c02001d605c42103103400c102c5040080004440e40c428404a050100c51503008002074400600445424000110729082c0c0703070395043d01101140b0350004c00030380031600740a0100940003400300414490184030300d04000102c030f0034001a541c020141054499000340c00180010300d00030424080050005030503409008144000c004042c14200c4c09004c041c0313a4003946a01500345150b8221f210f0350002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 583708093 1250 583706843 583706869
    0x6070f02031905030103170403031b1502030a090209011e031502040b03041407090506010801230907021e0606010c2604030804080d031b03111606090b0702030307080a0b 74
    0x110b4030405520b041c000d0a590080c44107680ca40105004800130034500401c03102180c0c0c0c9903c602744c0140380e035080c04504245c003d10a0b02c1003100300300c00a8142e0842c1c001548560b10729100002d41060794410042c24140680000280c0004004044070004070690450203030707070704903120100b020500401040a4401c0d5080304881c05000b0042c8030420481c80d5082c0b02554460007902c08d141d8480b0032a40455500721070f16030020b020640100060141002c600104000e5403520008940c0004003142c01810151175440047c1d001e6030004d01c04052440c0541254031460001d070805040820000300201145007024007005004412a030310710581540c5100d07405048503001e0380746d1780e0b05d04180000f46c020340300d51300580c0990040104114841e02c544031105414101104052110b44000c90003001135442c5422500e204103e400b100c3c0318965602031125200f000003044c03550303180c500f818a1040c05000c0d00103542c014000d215019801800143d030290081c4000640b640b142d04c001414004489 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 583709343 1250 583708093 583708117
    0x30e0c0301140f070e0d02010f03020702030111041502070506030c3709060503091f06030602030c0904110f04060c0f1a06010206060a030305030c07020f06190f1106070f0203 76
    0x41c445801d400c22054034071400710510003030b5181d81c5582003505c0401c201007906620005070307490800158040d04000c400d003402c910b0014103003c4180d000c2400c460403030b20344c40b120100100c1c007005041940c042904031900f4901c09460751510b40004140d0a0101600103d0250008105004150760b90060310b2601c41d00d10169050709240c41c2041241310320035100050016003444c1000c51a1401241228001d980d001c00800c60042601d000700c0160054450798440c081e110080000400d000b400554000c00070012244c6d03444000703030100030071900507940b0000030030301c1032164a4140f1101d1041d0b03021130f00e80d0300308924000311780e10f480c040b84800c2c0300f00103017034200c040c60401034403250300c1342240301d20380c20b0302201c1858a50ba401c0020445107840300400155080002803500c81d01c00020f41030b502d10217098030307800c40c0031000007030340d02d07000b0a542d0044085900350b2000d4140e440034529241207428200200181d200500d40d5803a448000c2a203c1031048100380f0005a6108200b1512000200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 583710593 1250 583709343 583709351
    0x50f0f07140f06070809030c100c0605091204090b120601060503011503020721020c030f1b131b1d0f1c0b010609050a05040c0e151207090e090715030e0c0301 69
    0x649485d124a070800c601c454064403815008640c00d08090840601208541e00c485510707500c159180740c090b150040020086000d000300819400140401a00c0130f810202d20120f06030700d06209015025001071096402644000010801350380c100c42142c4c159901c02d020510881c4559009030007038071944500400103d100c43d04020402260090007248035240c0c5e0940764810035050400d6a00c0d130b0b140c5152b52403500642c0d00031181000002082440c07440250102c03400c0541c04c45840c04403010808840d410b40c3d085c400b0300002c0c1e0341c4291601c1c01e40300341d8104402100c103280007247c0000827100040d070180c0c954410180c035507140110800420386d4030070f10781d130f9196860700c000a0104801d44a40c034014080c1100200302403525008209801005607910f8540d80401c80c01c0000351079010790b00c1428000700f0031401440c5001c01000c503106036400c0e203604c081e2610b48041c907425500010a030380c0c100e070088801440f1000301946044400341d11803401246500312103803001d00386468500b469901d50701e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 583711843 1250 583710593 583710607
    0x5010804033f0f050103081602040e0601060206010317030405100f020706091412030609060907110304090615030b01020706030b01090e16030b013006030618050f0f07140f06 76
    0x580c8035141e2010b822140600030f80c55051a404240d90f070070700005140380e03002c1c4000509209084110340c7e41c0e41c001000810030400c400030704c0742007103001e0b00500c0044c1c0141c07005105008480804c145081d200d0321802e450740c07034641c4501d0740741e1321302c592a030056a88840855046940f60f8040d51400d580041d0200040384031032808030000441c0d00b44154413402450240c5520030030310007d8074400c00c0003a140820540d900c070108441290000c106100348005914009107110040020b00050000c441c00003400f14140568140e0920b000382d0103908060070803120103d80c0c0d0b808580101101e14504020507a0000c103801619142c0046d00a0f540400fa0070040107644a6032030301800690071a0f413004c02400258000443e160042003024040f040541c601420082c60100c0794031102c000400c00000b41c880e02c0790b403620f06a41d01500d05410302510180b5500620000340011144000c039100107118a4a140b0103442e00c0b11158490300840b041c90b81e450340c10640713400169008090004007442d41d2044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 583713093 1250 583711843 583711937
    0x1080a02040e1303091505030606030408071403040914061f02011d071517010b090316080f1c020c061608040305060a110403030909051801110c0f06010501080403 71
    0x24031543c058000640c81c4800288040064140e65001c1a06a070307a10b14561302c001c1407040355440544100c0c1e940c04100813400101d105401c101d264640381d02e0103103540e0381c94083ca54090368003041d00c035001c600001c03051000a0740c80103142e0020442d035003070306850800254003c0c0e0040c10740070b407240205035041e948a0708021010070b424045d0b51a901c0301080300c803c2200100c5600d428895405221f6060b000140105040d1001501662030000c0481c0c8100c1c80502100b00624455031040440e9405484240d11200c41405001c038045042804501e000c00c003003c00075920001c0c1032003d07004003000100b500342c0c0c2031480c0303910400e550441d00c683d544a0390303460060354442044619450152504041400030002c0d201124112901a035940807980d04000d80c0724010030024090041c0ca0844d40c0055034050402e0003a402102001131a040d1030b030300e007110760b6810b0520510129613035802c000c0c01400b0a0781c0000700280c12503010710300011000c8408503000b0455040c003003c1407216013011100c2065207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 583714343 1250 583713093 583713121
    0xe09070302070311010204051815060409020a0e0d0c05011d1f11010b18132102010f140106050903031b01050415150302040203100504090f020103052401080a02040e 72
    0x1446a03541c0d6413100203c20380c0324200c0c0142d0144641c00102c4004410000d528200516045114030303d00c414038040880004085a01035440000c000b03801140d030600181c4c00c0b0b481c12034034945c10307101c584512946503907088401080d8040c0d1414401c900103100c01100a5000325118524085c01413812840d40f000c5c002c8008a29518a0300003420b00c1e012842c1d0300c1e4040c02120866400900704d4a2002c20600b0108401c020040c0300bc03100110181b1340501160401016040441d083c40404030801d004900c000c1c203407110101102803240c24013030001c02440c42507070010304441181c80d02c5522014070740002030462040c0303000c02e0f90f10150f5081d441b0394010103500c10f03400b851240f80b840b01d50840d080c3e1400c00381c2d41880c0d1aa408074015078001c102500b0207070000c50748914409811440c15482c0e40c00a801c490f1010019603056003203520f50400c550701840303400e40141c00b005600002180013110254401590804a81040350401c08105c0ba03145603016580503103039410045a10f49003c0d0b006402d88 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 583715593 1250 583714343 583714357
    0xc030e011410080a21050c1b0103060902070f08070f0b0a050709061403131e1113090803071805120a12111e0a05070f080106080d17070e09070302 64
    0x1e08082500180f501800203240d0a1560b000030004003070990460380480900d08000388106000d02045403060458062044184c03060400b0042c608800c00c90300014111040354204292903881000014082a02c80354201c445c1c5600c085015070314041480c11100d210000d80005140026800c02d205c80300c03059800c0244291140e60310b4514440d40c40808503102040402880941074040000c06c03d0448205036040c4080d00031481841000305400071414004072408050b94000441400058a45080328005040409280c024440e9206603114000340e48000391004041c84880c01c41a481c5c802c00246c140300400000748000740045508002544800d00c805041301c44081c600c0d801c182542c010420340405124240c010180c00c070a91900c80c111005269a680e17940c45100491000134004010400107070001004076038441c3d2600d0035407420b440302900503001a1f044803c01d10141c660250701c21035100882c3c4203503800c1d5200d80c54159038050724003aa054000460104200c20103030150010045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 583716843 1250 583715593 583715611
    0x11040603051e0c0927030d02040f150206011206150b04080105070903050c1504170106050a0807030201080f0a14010306150e0c0412031110090201030608060f06040c030e0114 76
    0x2035248003402c0d5503125005031402990201000000c035180f03401108910034201c0e0305071aa00c3d1591224000305165400c105040d80c01c8680016050000348042c3d01500018402d150a50085844030500030b0745900050107035000012454040b04140421034110521038003401200740e07886034840c40e001d00280d1050284050540c20b02c070110b5049442004058212908075002d80f01d00c03920134040140380001288201c8406000b40008a440042c0e0702481c0071a501c900300005125140005000c107030702940d8030100340c0343c10040703080001d0f03608103642c01c2d4000c070034109403071142c1d41380d240c102c004080c4940f02d10114103050300084200545503000d02c0d0801c100c0c40c0d0070700c0300c0c46da1a00403c06c1c28404403010b4550300824401008660000000e50960520a040441203540c414041074035011510a04400b41c80c1c03540e0380c102c1556010f05c2000041e181040140c5510301c2c003160600d0400b400035240e0b034041c80d0f81d0791900104600c281d001c82000350b4410000e1100b08204448203035164419510044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 583718093 1250 583716843 583716883
    0xf0b0f010e060904020103020a0c062a0c051c1707030504060e03070f02090a0902091509162c040204030c0e0703090f03050901020715050a020c0306060d0602071104060305 75
    0x20344800c500041d10301c1050024405071681d84d540e030044002e9001210303031006014041e0210f1001030841c0c0121540f003001403400d564400c011100d0822072010360020707541440306503118400031540206a82054015600c070801030051020803c031861440030005400d40c08a04082c012201e500d82c206a0049000f00c1c4184500c07094505003540340e00c95110002c000c181c5ca0070300140141000c0d40015030040701d810700080d2108090700802e00300e0904032204c00b4003002c1004e1034006840c10117840c6403c22043d000d201c8040207003e50140594203103e929000703041428100940744c542c5940c0398280301a01420a6448076524a0000c414100da4007400c004259a4400200458802c0c8564080c09410201181c00440252800e40b03403a0302440c0040c0c110f01510b4000314008210100e80e61544205a6640d0794405001e5002800c03d05c800307444030700c20703040700090000316990400c0740701c0d00d5500f02d040144d035514a807501c1c0031010040c20440da0082d00b40200042030190108a01c0c0071003013182d09000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 583719343 1250 583718093 583718099
    0x31706060405131514012106080604120305131a0a060906090209040f0b060301060c0503072f01080606041e090504080c070b090a150c020301052a0405060a05030c070f0b0f01 76
    0x42150300c201700c1d681d80010000c1c01c0d440140001e172040c40702001d648801c0068070540358107002d400c04404031801d075404100e0002140301a0740c54810150701c500410780c6c0c1c1e2000e180540e00c1c220103110182c2884804007224020440c148a00d9002000a00c1c0c502030412141c0e80c3d40c0501c0001e50424061a132140e4a0301c541c44031241c20a01400300505001021140307560308040c4190b5a1b10310409041d100351009000726800039a100303083d05004062441190000c58404031003480800f000c03100785040140740340038030015441c2c1c038050342d040e40d440c05c80005080c414205491513040c0541d01030803142d400e01c01071005000300400217226110140040e11200358464111098910400429603000f480403032007048a408084842000c0c42141d20b03002c40884000d40000382034640030780741c002c1820359070342a102054288416080003850040451400d00745810001200d501a0409403410301000100043c004500c40301141d070910382c0602c0c40301031410181003800c03030703c1c030200e48400c03503212044008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 583720593 1250 583719343 583719359
    0x20c04050906010b1c05011214030703080103060e101401050a060206250e09040b09010b04093801031505010b040b0a21091109070503040317060604051315 68
    0xc0d1003090003600505480e407a141300501c19a1101310016100611454810300729a69405054000c040f01c2d0304550300d82c81d03142010041c0d04100c5c17080d80d000307030300070000c07800042c1d04507a85c141100d800600000340b941400710100d042030101d81d41c50091501d041c00c4c0100c642c021810040c142ca006564010358144c031070006a075111015200702a04210360341c0c2c03058002658121000f400d801600e010b0040541240c0030451030b05041d101111000400010880c00760b509108560096404840c00d00400320715840b041429803007a108001100c040d00d1841810701c07440c50484d245030000c95525107240d0307540d0908000207083c1038075070702f40c030303810000002540b400d1030741070320180c4000c41800d41c9032103e10481a10080c92618500d600c0342c040500241d45074045220313035156a805140d01c50552481d000801500d1803000f080300381401b0b010701c18000881c0d88000c038140c000c40801070b800c0d543d40780c9000040c82d41c002c1d5441150f000100956100b09500075800010360594095010a0710030303250710741c07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 583721843 1250 583720593 583720601
    0x30e010c020d081b04030c080a11150f090f0a061205090d12051806070f11061003170c01050a06080c03060c1806040f03081c06150f020c0916020c04 65
    0x4100014078881c0800c44902101c010100c007004182d28803445c29a0740d5070b0340401e01354140d000e2203e54000950140034020711096040c2001c0c000c130b40b074112001030507894405500481d900110a04004104040107481c1c020b01e404041600500240f4210b940320801043d998038903120300245814600840c00a980c0002c0c0d69602184d1070301c9401c1d9541d81018004010f00c070003880030300d11076007002112004400030710145010b480e503551000078031034805001804662040e1170a5a603680401d08002101404904400030750381c0c003094203207a4070740349038501186014900c0041d410f546001c040c4240d85040ea40048100d455200550f03580d9084101055210b400031a24900006810400d001c061f07100c00000001c0003500410b09414140c1f00c40d011503100140d0782040f580c01c1e07000110444080500d2183c0d00502000172000e1041c1418821a80ca640003d119080e00780b12001a075002c0d083d0007403080c0300c40c05a0140400c141443c0c5070406c0003921505110000140c003440c01551914101406 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 583723093 1250 583721843 583721863
    0x30601091202030615131b090602030f04171011070c1202011202160c080a110a0b0405010c020d022e0e0d0b0403020a120e01080601050712030b0f040c030e010c02 71
    0x4050301e130700d98030f910b070100c2c00f1500c1107601c82e4014415504041416294414040201d940c400150345003910340d48040d0501c1203030f8101c841558030070312110f4081d80f008006c603401c1e41c10321200444143c1c10380ca8110300d012850b00da074542090404090305c14446c4403c0213081c0060040182481d011b035104e00c2e00c02c140c215500040d00003202544010080b1400750020310032001d40c14030306800e50391117894504084400e42c0017010280c1221001e0000e000f0600c103002c5440000321940d50410b4a403003100d1000d44100e200701410b0018200150042d0b640704880c1c03010311a000340002031001d4030510060b200216045c0d01200b4862002c3e080101c9510900440d084414040d00f030348100c0149894009146400620032000c5205118444000400c2d0707858030030484984d038880e4041d01500000240081c14000c0c0b00f00e04000c8103000c9500030074020b081c64035491801d4240044c0c407603040b101103585a1300480400b90401d080040c1e20154a501d81d100c07006101080b0002c1040b43e00006c1e0032a00c89080b58 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 583724343 1250 583723093 583723099
    0x200304060621140319021c09050a030b09070e1302040608030a0c1b03080f0c06160f20071d010e0f0601080a0f0f0606110708030a0e01031103040602030601091202 71
    0x2e40da00000070102110481480c6900084030304040c42e00d4006412028000300340f00041e00424911580800f00d4000903048141500300f040040d03041c84081800c1000c0e521004d4100d081e228042040b111042c03069030051f00044055880501c0e12007407031000401412400c902940c5400310005113760040150340030201280d032480c140303400c41c1c0c0300c0ba200042c0c00f1402e03412000880304c0003c0000c0482c0c009014502104850507154902030354903070304049008190040144c2d03801311401030b841d400790344140c03c007803142450712031440c04410200006407024908040c92190600125204030b100c81190141881e00c0c464500310782e2a503151001c4201d050ba001c1c071580d081d540c08140c0960191041c1a88210090310001d001c0803103068170019104c0318691455403681da200306120f400e0740928003171011a0480000d080e40351030800490b550340314040c5070800301b00e9210840d40444c1c2c425000b81156501d194071441d00c0c1d040c1820254000c2d0b0040d248140890f0000000003146201d110450070403076002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 583725593 1250 583724343 583724399
    0x1214100503060f150d060e010c18060908100518070e01090b0d0804050d1b030c090501050f0a0e061909020340020d0605090109020102010f0624032003040606 69
    0x1c2c0921038040c42080c000c41b00547c6070782520942101c24480c2180342c60881c0d0307920301a003401d443c2c950b40c1c0c1c210a0b004801049a1260107000b8043d0009020040d2075070030b100060290380380d4840546404881034605441e00a0040008000903000c08203030603280021001c10180c0c0c40034040290244100070000c1c2031050907c0300b04000c2c40c10400d0001050300519440c8a200c0b0048418542081d050b08100c0300f44103802c00a10000e40c50b885200c2c05030400303880806d00140d00d64005a24111a4407e807100c054170100010020b40b60700c12592003c00e80c20f10824801901c9000d039170f01039041252803040100710071092201c0885c0d44400d40c4080b080c0340c1000080d0041441042c0c0010301c0c2e0740c41c10b0303802c0901e482d00d10b400601d15102d4540314503c1d038000010110880d00c0020309481c040a0740c04102410f00ba010b1005002518012914404108841d5083c240814054016000e0840b41078641c0240452051481110800035441180b107503100300415616a0680705d24003400c005510820205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 583726843 1250 583725593 583725631
    0x2d090109060e0115031506020a0b0a0501030305031b0c0d0e0f030a02180a021303030503040b07080c090105071106040f1d011a0c07030503030109090c241214100503060f 74
    0x220b4101140b450100d49004540380e06c5806a81800ca00703158800c2e40103038803100340030040c00350640f035868010b00c40317070000d0106500d1a20010410b000280079015a0040c01000341030600c82d100880d0803d440303180c166011402842c4024200041d02010030303000300c01070096080c06150218124191660091844005c0e100303810403141c2140000303041f00b103081d60070002c50701c00c0021449031400640c482e580b429600d00c0c140c81c1181c10b081003c3c040005018800e028000c072250100c09a4075081030a1800d251907010605000b0f02c0c2c284400c1d0b0860700664009804640307010100840d40a80f0144e03101c0704000e021443c4490520982445121076a0207a82d81c1c2c1c01c81c2c48120402480d054003003030100e5549985a858850441d4020391107550b01030707901d50140d0100704000c00d6800040c085644203c0ca51010040950740030300070000760208103d45000c180d40740c0e0090b03074490481c076401480300403458a00704280c0d19220000307006c2c0c0b030f1003881240c0c002042040c0e8244020702c140f91602560801c01d00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 583728093 1250 583726843 583726859
    0x10e1303050304060b0d060c02010c020d1d0d060e06010503150403120b03030d06060509240a050307170a05010512010e0d05030a0608060a05041e08030c07022d090109060e01 76
    0x40030700102d038000d03201c00d41c1982c140d0b1010000e0f140d1300d009507c00511180c4030140079084079000a00241550050704081078140c0d042055140c3c481000000224441155000940c0008002800403c01031401c0c4054801480005510b416184140c0c112011030001d140b401620000444000b00021901c0703401c5c0020030b50315004580441d0000d0304607810182c842100009550407a00404002040030074092050710300520700766030903068140003220101121f078405ca094480d0501300000d002d0f000000c941c1540c460302c4400c0170401011022070301c40c00d20890410241500307101d00351140c03c10851b0311148d84c006224a805000d1110000c00d0300c4005c1e1841070390b480d0801005da02101d56100070002d40c00304240010b9110769015440040c0ca840c0c1494100c2c0000a92600c0b0b58140c0c0e2807070b12040000340b441d412681c00441c100400383d01c0b4131152000503205158440820481681190019268004045040e201c0700d400c07a400b01480e03072252080c408a40c0b045c030038026900a0500104a115 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 583729343 1250 583728093 583728097
    0x1209091d011118040c170a0c030507090f0b03060d02130f051803070f1b140a060810060302130504090f02090f150909100507020d020f0c010e0f030a020a0b040905010e130305 76
    0x1901c1428404804940d008090744e0002c02198011609501d5840813140b15030706105072b1b80d0114880c184401d109080c07525031004018075020f4090300610000200d96196903041c0c5803407200f5801020180c000700c1c06021600607190340421511818100401716291031800c42c001c1a5200d08032000314280340041d1140d981e0f506007280290781410380b10b19591554091692a0005807000020b48030001c0d01040c180507006030325520010410481d08240310030900c0a42400044900720f20700540c6448071401585640750603580b00e01e5004d451310540c81d00300b00c00c2c0200d03020381e640202c5010180b907844180412141e6000c40b403000c071781c100070f981503619490003054407500a03807d002100c80c01c010740034030142110000d0300c501d009680203480107000e01da410010400d02d1801c0e80080c0c8048140000003a22001041000c035105a102403240c0c5400d403000c101f001c01098008080024041c0d0700d6402021651260285221603418200003050043c402074180e8041c0e00e0a031030790008819a500c04551036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 583730593 1250 583729343 583729361
    0x1a0402130906060509151302090306010302091f030303050a05071d040f0603050a050105011707051807260105010e010801080a0f05150a1d191209091d01111804 70
    0x56921000404d154403040c064601c03990300c0341c02c00081d1070715190400c43c1050000300b00c1502c950040100c090756403000314410303044940c10b460400c0a5145c100c440e0601c0c03c2510411002984030800010074164503811041c0540c0496000f00129181c064003200c00a04490a0440e4200105100200743c00c25a002c41600d010f10540096501c3c2c8030380d6103506000c2c4020094480e40c0d140c0c401031010241c0200c0c810200032141c03000b822a523150001080075900c0100504000005180014801500036a50070141d0500d1440350402c04008510301001c40400b8040c1500242800990b940254085c981442c16030b8541d00061242808980c0c8060801542c0030003100d9500420106082d406070074400c00d0b0054105c0c00e004600281c684492113980b030300c1b039440007485511884005281d65a6603010804441e00101814500c515000b01031b604d022543c1c4c07120b0211031400010501101c070406ea088603d41d10301d00240030045181c0e00400c0140a22606240090010303840136111740b405034812000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 583731843 1250 583730593 583730603
    0x816020a0807061a061e07020f06161104091a04020118030303020319021c0b1c080c100c09060f02160308070c0e0c09060c070509131a04021309 63
    0x42030840e6904040741e0000d140031540b031903c071048140260070320310800c01c210304107079801401c02a020700807000c01c4807180d201c0341000ca0005120700031340d22054065103024801a00d82c6a0740c1082004a01150f443d2800584405c1c0040ca9401410310b00740c0541c0074003a0300a5102040700040480443c03c03403c0140c4100d05100c1c0644e0120b09810341c0c1c000520055019450068503031400b15440070b013070b018110105442503c1049424810040c0c1d00104c1065140450006124000301c000314903500e00445d901e011240e00481040d0403c10303c0c03001000003045001c15901690000300c900b07019510402680000b107a107001050000030300c17580f1002c10000c150f03c100c03140c101c1e440c44000021203480c3c0040d540480c0000d00341d0300344030355400b004d40100500f40d0014040d1420520100c03250192800c021311841d0001469041d40c08200314150140c10001e1288241d420484a00740c01001c10300d40458100700b00000b90080c0c9a03040c58954400c6801401114900321b10400300001071100b0001112 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 583733093 1250 583731843 583731853
    0x40614090a2405180c27041406180c0909120c150c0c1605061b070b03090604030801060305090601121e11122410080a06050109050106050a081602 64
    0x900c2d400a02603140030b03840d504000e00325054104500340c01d0001d078440b6940600d404008201d440c4000300c03543d0340e54490306001c3d2003060301d561070451410302c110300e000b001c070740300700c0e01440b00c0700071900d1104119050f52001c95410070091b0051000c0380c0012600036070300da04102c1c2214a1442c07064010b00209000900340c480d603074242d007007a500c0c0c424259480a8103050200300107441000400114a43d0825440c5e80043c00d46000002501445184118500f02007912914406820200180005400c0d07050005840c1d00d088880e181c2c0d511001c030f80070340c001603482000041840c02481103500542d94200681078580c00e080b802d18503058090400c8651101500c10421030302c00480d00d8041c0c0038410001030100c503a41c40201705c00d028045d565100349400803000a044c04030740d50301156072062104000e130042e66403410008081200303540480464010010040704122555000746e040c3c40500808001070f90700c0b07000072500c40c02240c1040c4081145c140c0414042e0444451065008940d44103c0d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 583734343 1250 583733093 583733153
    0xb031002070c03120804050606040f090c1e0f1202060702010e09090f070f08031c200c12030403020303130c12050708070b030408070303050702070e0906040614090a 72
    0x4980c010001640d0304208000b0900801249041d140c500554520345240b2500301503c803503490305009010148519542e0a44031810b4110380c1000d69a036402c40c0700d0340307901d582d46c0003003545100380020503040307a054503200416000d03c041c0c8a041611044485290903411680c01d0200300d034052003099051003003444c000000384c0c0c1c0c0c01c059075200345c40c0000039050003404440c6003458082180c01109001d400f030300b803c0c02080000010381d100c008000c242c106225402041c0300c4003c00000d600a00b2868103142c3e1251100c200f04001c02013090440308032000034194541c060081d000a42d0700030010f030000c00201d039005481602c4110607078090b80361108a15610100c085805408500c1180c0507007011008001255041c422343e0000c00b051074a00780ba519282c1d0b40d480f01840707001002020315a451000c070300701c40d208004890240c0001203203a103250511100c15a40c0340401c503021a402410711070341071811170401078040c1c0030743c48030030041014440030307912281c100100001595120b20380314003107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 583735593 1250 583734343 583734373
    0x26040509010306020a02011a030a03050702060f0a08040309120c0b090f041a01021e1c0e09010303030b0306090d0801170c09070e031603050a060e030705070f0807060e130b03 76
    0x1600031840303540b0041c0d071032100c21740182c03c1d1140840040c0c006c030440075003026103403404030314402500c2d80351424540c0c81d006c3c1d10020b420b5004440e00c2d204281c2020400207001e981044055024074001c0e00d529401c0e90381c400340f0702000880c500f401000407402007010000618034401174150030200a000080e402181c80206040f9004a40814010307004485201071741c2d601408507954000c641c0b50724561000c000004e9135a01c0209044114505003e01001e210b00761040b003510100040c0103040440a59503170a008010b4038013205914802d0141c0008203840c4400000c207030603c5240785e26080307403076881c003080c0684005016410301900d000300c1214401a0f5101440c0500c61209a1540c800140210007030614110a0701030920910510380800e201244001842403800c42d40301e40041188080c1500d01405c6000d0341c1d00003040d511960300301040000400040b40151080ca80c21911000e58811003218450040603000341c106028001d601c9106071036400c0f0500c9500041d00312a2000040c0c0c4103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 583736843 1250 583735593 583735609
    0x20616020c011422180e0606220c170a050601200a050102072006030408070605100305100c030e0106051804030c080d0b010f0e100807120c080609060d260405 69
    0x280c441c0040c52484c0902c4621000e29891a5241c1212800c002880000c03d00329036600016104502c1400c4070060041c44040815400c003442c0702c1c0d40400d1100303400056018016468020303048039002076040015064521610980b4410300c4160340d112001c000c00c0081007095101050511000d024410014012500c2400140354961107030355015213903c040390a070624094080c01d881c1c0308090402c20b100c003180804060381d90003600030340700082680710b0303803041014072800e40c1c40100315001d5401c50002c0c2c6082e650140c1d0040b08517440602680b40f10214240c00c0f26910f0058a5005403a40c0c100f44032100c1e00810160300500c00d0502c0e402028554072455425000980c45031035241d15110017144035603029054031b100c2d11a1b814046081401c00000a01c4248141c0302101017040c880c0004051501c2038a0440f0040808202006002c1d5411002000881b044800c980a5600704010030414140015020f4800350440641980d91408041c01350802c3c0c0721b0030700c1c42403540d414440401d9aa07039040b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 583738093 1250 583736843 583736887
    0xf221e09030c0b0a111b280b0a0906050c03060907110d0c08090a0f150201152c0c07021e0d0b13061503020f0415051011070305070303020616020c0114 66
    0x59521302c01584451000d28040f03600c20160b00e103030a1080140c1e4031f2131680340394220031380d07100034070452540e40c080c1c1550090800740790107420207090805003e401c0e24414015401020706444103c00e83c1e81d18002501c3c603c2d50f41c00c01d0f0280341d120003114440f40d032160380000740740c034424548035180c0ba40840c0010341440c0310b908400382d020390700c041c00c000c25140701d1240004105140028800e150540c03c69005814071485041003a0303000c5080810b09068040d24840c070080701c66081c8a460a14210181e83c541101404a014060ba0b00003110150384220305e0a03102c000091540d15a080c2998990940341c0b406440300f50340000700c0d20514000782c1c840c01240c010b00c1d01480c0d0030303462030b1030760040082610941d40c8050040b407411109600300c070042c10b0014107481080c0ca8440402c005010708541d0000c0b0003008403880e0203884404010024041901c00c00c4a002c0d41c02c84046444141119031124a03d424030030259116030312080242d4080c511030103200002841580c00e1040f0f8084014059103010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 583739343 1250 583738093 583738117
    0x10c06022205090f1527010e1501052a0f0703050a0605250318080d140c0f07060b0d02040c020f01051308090f221e09030c0b0a11 57
    0xc014441810100f055a030310a49403005000b00c0e091032244d40500d05165000e841c090380b04a052000c201603251a44401d8031109240d586556079214000d10b0240d6060703505000d40740c1c1800103c05198031410542e91521201c44142004c402c1000300381c074040329110f09210040c000d83c070b200d401c061402c1c04200d0055000b20301500002a0390f1030310000311140240b01d80c2d03c20003c6010743c0c1000408003030b00c8052010700d050000350201c46148040c044c1107101401000306c44005294814500301d41c10840c9803c102d900c051045448980700102d02e400740d5501c21a07080f40900528010600d82c0e0040398904c0b2000d01030039030b800c81580208085d68103640315980541d01c603d01c100d041c91001d10417168807004070745e0000c903003111691b5141101e11030380e080c076403042400d00410811342d5501c0c01404035a811400031203200020f04100310014044003d04184c070f041401d507011400f1001c2d4091000d44661580c0d0307018a1240c181d9484945400150a041d00d8503500c007000400e08001a0042c1040302c120 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 583740593 1250 583739343 583739407
    0x30c030d0c03141306020c03040b0d050108012a120f0c021605010f18050414040c050913290907080c0a1a0a02010e0a0f140c01020705010c0602 63
    0x2414600c001d40300007000c07500400d4545485085111a5242500d0308a10003941542404600d8104003019005071010246503000001e80010720715074003030043c0704640700c4600610640c3c0e6500f140b6400c80e903100d01c01c0602d40503900c0100c107070010301031001030103d0007505000b611101c0900144044461680901d200039540d40380e6205900d4041041322224820098030250f00ca00340b600007094038580c07820350814000c001d46514454800603101c40042c11025204000654042c5503a00c1c03600000c1c0e40541d5810340c582c3c0085200c1c20714103420340c400c41c0700c00210010b00c16135946484081c2c0c8401c1962000051038004a080114019113641c0900c448600405010b0304004400e8181405007000c00e10a00b601d003020800020b42d4440c0e10340203680e1101c680c0d15038014101c103a025040034401c90b0f915004201c1c00700c00700500314202280d813900411442d0180072902d10016522080c85410758003580c4850001c2000b50b204131990541a4070485025042402c08039180c1d43d1b845c43c0c2d0300740d241e00d0030300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 583741843 1250 583740593 583740607
    0x406030203090606150d02090a030b0a0510060309030e10031e0e0c2d0102161d070f0c24111207020d09051c05060f01080706020115050405090f030c03 66
    0x2c10040c41350043c404a80c80c00342501d880c0c1e010001d0b40716480124043c0364000c5601c0e1160399070b5006183c020340e0070982d07150f00341c50030302d00101c000c01084811075550050b6050100b4807e109200c0e0120680c0d0680314982400304060822044d90a21501d03002050380750a003a048036420f024810814418030350010038a44222015541808440818540500c440d0042242d0f02819003004c600d010021191010300c88038000c0040741458240705064140c501c0c132074000030721916000c200c1e800040214a00c0001503e0700601154000a10100d21000030341e0f4014010100c2e6066211700201c410201c9540d80e02820481c13240c09031740210041c145460380101d04000165108005503510030803910150100008bc4030000c3c1000b00d01c7d00401b230052460300d050302c0038020003070010074440350418120380840c0340000c0c00c2a0400024011541940503041c0005150b600500459054403682458821102d0410f01448001c01d801070450030a8400d00b038504c04a00b6051006051102d00c0c580610350f40c0c60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 583743093 1250 583741843 583741861
    0x1106070516080109031e0c0218090105010b1c0507050c0f061b0c0d030e0118141002131701110f0304030908030a1b03020f0601080d1404050d03120f020406030203 71
    0x2a0710703481041540d051076003140c00641d01890201e00c4015140d66090000e50342002141c5c14412030038001d4010705100d03003501c15910180070561092803400c0007400103030f032074412902d014000c1e070000d00c00c0310034844001b007103004058120a500c520ba901e01141002014108640341030300e40c00329140780b0b03006001400074118100800c2456904040748031403038040c601412030340e00c00c500701c40c3d50100340c2d0740c41480228003829040006450054007000c0000c0f1050700b0805081000019200d500f03226203003001840d440180260346080140740d24041c81146404040c010702003003c4c0d1020070655840c4149040c0d000c0c4200a1322034209041483c945a2520f4540644481003d8202910b2a40700b446000d4140340c3c01480300301134048400c1803250311411450140c3c80c100d00c010310b0b41d00c03030b02580700041007400e000600c1c040c00c06005c5d6070b0341d40680c201502c9030383d443c4580e01489030000e4107040c01d540420700030301c0a20701e04420f8040004103c6c109008440c00ca80154100b800065000402d0244200c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 583744343 1250 583743093 583743133
    0x402040b120706050d0e0a0206190201020d021309050f0601022d10020406201209010e130203220c060c0c08030307260f011a040503010f0e0f070803041211060705 71
    0x3070041c6c0141055115030300003414a005850012600d0840300f00d049900385c0c801e4042d02c005c075209680a540321101c03181b40e0f009940c11402503c0c22607241400082840008041c0640180302c182c01030000408945030b8109140d1904075500f80c0c40300c0c80c61032880045070811102c0000d04c00344d4001a20346092802c000d1a50140920600403150185543c448291000c0340300d481d0007040d000c0c51542c48025800584408690382c40a962141006083c82ca81c1250390b0000e61264036002e1a001900c42c200014190180f04404040d0007140001c00900000e0301401e424401103020b6020b0702c002a68600c00139207154403c840368000502c1c0c02203294203036003c640c203000003080345403c1ea517080d180c00205040c1d6444144200d1501c2060302070044038104004003180d0242201a00038400403429203004805441820304040c258400e020b00740e50024000300d400070079943c801d00554a010300d082400340030495020b8050b40c9035100410302c1c80c06a510403000f89041e501c01d401078201c82501070b0a0000b16 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 583745593 1250 583744343 583744361
    0x90a0f0804061806140306040605041a090604111e070b040c08060a050405030307230c1612020d060905010212150406081209010c1103060f04060c14030402040b120706050d 75
    0x10748002403d101c4d1641220305010721614020566480b90780e5403000030f01900650744020b8100d4074107001c081140240c015900b100c41c10070b07100c10440d51291424401122003244e0760006c404c07802d2140741d40442d01c4514456055154119150400c10203031a00c00c0742004c1a0b404460488414030300304602401401400d074882c420b80b84c10491854035458417916407000400800030083c09a410246151039100d003540c0c154210b08000d519949504622599842d19103000c10b0390951402d4005404069000300490040e80500f5412010120b03540381d4000e03022104023100d055409010000c0a10880018140f00c0d600c20310341c0e0500325a0b44c00c1800300b140d12680000b01c2c01c1d00b06100a00e08802d4100488000306400e10b0300d080c02c1101402e02c410034208030003101c0d915009110030b12900314165100180503600900c010418030b031030314034151505402000e100090450a03c005809071030158403641d84442e0243c482a180f45603e608a4284120fa0300805d000c11004212110b079486907118811603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 583746843 1250 583745593 583745627
    0x70602010507080403180b0a02010e1908120a020909070c03201c02150709060906020703050604150216050607030b03060103080f0c0f120901030b030d17090a0f080406 73
    0x40d60800300b2005120440080015003445800035074036104944440c00d6200400074804016219440120020301801c0c401600d14403621814058000b0b089011020085065000c09901e20703041000d41542c03650b4000a013070740103c0707500380141081a111040500e11a140c90b0343d6900d100c00d410702d40039007840411403280188840011100d503541c43c00096052407811410b0281d503502c0e5801b101246404040f00c91490b40b00d0b1100140420a5003001c4008261031680d16280c01c80741d02e0b0340342240e98003002e11007c0d0107548aa0701140202d000705d800311016407882c620141c40c2c5000100c00d10080305c08150210303031540c0200d0801c10324545c035100e81e84011004a000e4045075244d901c50b0780719802182445480f0711400101c501d041003040101d0480502c0c5001921525841042c0110307003504603500c1e09002c2820700022210741d00c0c000c41c121060300c01c1c585441c5419280028150281c50000300308800307911503e540600400c0b20388050071400d40c4a4507129594508082005018800840318584 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 583748093 1250 583746843 583746851
    0x510060e0a0504050a090f060c14031009051503160303030f020403240e0f03030f1b0315121213060903081606090807080d06050307080d030b06040e130507060201 71
    0x465507007141860407240100c40203e025124079120b0402440100d90060580124401ca54100011604400712120242d22401419180101e4102961100b16a110f64100820b98188141c1e80300350f015030f820005010103e0226445100481d140c0556512600c0013109900420410145c0c180920015116220415030400d40755550b00091315959444102c04101da8018000103400ca50f8000c41400b603d03107085642d2140d0700c000040d100d0f030007511500035500130080040c0c4140c0c8080f115501c1c04001901c1540f8658031444000c4840c00070104059005e03200c042d580700070700c000304110002080e8a0b40ea003680c0b5401165114842c1d50598001c100380f041030342040010030021800d444070104241a0000c000243d07282c40303030043c001c8100080400d00d0104803141880b00008c05000c115040f960100000e607114420140d5038540c901c9001d10303960000c0100c90049109401c189030001d0060103080c2070548801881c0740200c400c0340c070f020b941d51104c00d0420034000108003030801032680d030000300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 583749343 1250 583748093 583748117
    0x6060f0504050103180b040f0b0a09030e0d0c0e070908011b0c0311070906121101110709020c070812070b01091a0405060607170d0c02034801051006 65
    0x391040c0140e1040c541851350310084503a0741300e03c3c2d0003041c091a501412000031890b2901e0021540100301d4002d940302126003000a00d21040382c81203024680d015116494200080f10170094005103c0c1c8048441441260000590140d051401c81c000c04864813841941410b208100342101c1c0400440120510392010054900b034020100d80ea00b00c0d01458071721080900001003902e81310b0b907a4000c0600c0c81c50140000717418030041800c09039052281c00d0014901c107206004460300544034441500d07680040e0400c00c80c210443d402003040d1070001c416034101da55152146802d200846800e220b201c81c0001f5810100400702d001d043c0505805081080f00140100c140c0070001044008140100e68030f1303000c0b40e2250346180580da041ca40c810f4601401c0b55260000d40c081e03130040580c030010355080190342c01e8820700200944440c1d11610f4103241e0420241200c0449803000001c0d0350310080346103200e0903442c840c911345100c2941079030400880c80b82041c8058808903041d65003c00101300c02c249203c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 583750593 1250 583749343 583749347
    0x100501170313060e150712030e06060a0e06040e0f070e07080c0a0c140d030608010c111b150f28020a06091112010f050c030705120415020f030a06060f 66
    0x1095854600d07110211031140d130082864821401105001400003040780320400415070046c050029040d50709025032100021901d90390b09090f2000ca920041c1d8a1042c0142c680c0342402c19400a0014030200b44c04250b41c03002400c000c00385e82c00302d48642010328203000c0c03400c0110405810036451324010707030309142048003503e075401000002c03020400c000c81c0c45428050204120f8482a403d4010744031003104030760006c2c0050032a889051410350a00c403080304500c0c090400329286400040c094064101c14242902091201e000c50b15401040e13110304540480900014042000300313488401e41c0c0b414400d0305a03046070758804e50001000c1c85400e07442c10155010078078001e156030148021405c2034003440c1400c40d0b0301041c00100d4001117000090908403805401c60007600d840410308200302e8440494401c405d201c22034001e000314404100c062100110030300220780c0f0a008408a59511544d6520841a42d00a10702210405004410b010b0340c03420a00c50900106007505107103043d25055000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 583751843 1250 583750593 583750627
    0x219080106020a030c230c03010b0402090303070204110d09030804150b0a050d032c1201180213141003030e030a03021b0d0c150f030908040302090c09031005011703 72
    0x80101049040170b400401c003c201000302030454540760014142c01a219815541c0c0d44001c000d40b0b109600b4042480054281031003110f5503480d0140145161440355001d00c0040d00c1c2d404504400c844c010880602d9162082c410520b10340c1c130a9039154024185030510010b41452585400703212441d080c1c182107583e0381c0d817840c0c40441d4400c0d903010195008604007554000c40c4488814002d800c41c0052640e415a6015010f098447c1210383c2c00b50f44074010300c0b140c00c0b1025941360700394048424410fa00985001d0f070400300b50065031080030a030308401000b07103020f01310140c502d10307184a54481d0500406810107150810818181c3c0280f170300407115200250f81e840e04105170024640d00c0c0d040384d55107444480c01240d02d20380003140d040000d60b640c0c0e04040382d51510881c100004007001c5402e217056202c0e0003942500c40d0051b20307690805045408201c0702800251007a84941c1040001c4e8400b030310203101020f0145103000000502e58900300e82007000001511034052a6003003048011011011040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 583753093 1250 583751843 583751863
    0x140114091b0d0201120905061b16020613181d0607120f0902060c0708010510031208060a1e060905150301030b041704090b0a0504181b0b0d021908010602 67
    0x28a82c112490b103400141c2c0d001c1d1301d0703a4030400d03180d01301180c1754188800003411074000d100c481500c8110000100f0904e19900450341a84040700e81c40003184050301d8480050500146030a490b06484c6a031081d401c050944c0f1040d03d07451064644c1401102e814510003480110705800000d0f290070302d40400c9c0101801c00c00f00701c208646079224001040c01045a00908000d9030240c00b035561004010740d92640d58a40340b254103815030078200050000d640000203207007280c0e4005203104015008036411764100b20024403454018602c0d080004846d0070404500d045625805900c4580e00d04143e001444a80150841c9010380e03400404402d140c00c098044a04494000c0d8200003030740ca03903241071141b00019440c1c003010a500883c0120744519298450b01154008030340f500d0400f6a110103100c150b504c921006264421184020300103e4a0b40c108406000b940d05a110a00c40d29140300220b59009480c1c2c1e40032055001c204010013416000c180503980a007401c140f8195031400100a43c0c82070104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 583754343 1250 583753093 583753099
    0x40605090904061b05120106111507230702100527060405090907210314031005060a050418050c0a050d1107060509160f05100c140114091b 61
    0x280010203000290348000c0700d145041d14242045110341350000d1054202c1d400c00500c2091030400080d1031070041c02c0f0b041d10406801e0140c40d0440c0c45000000c0c00000c0180441d007804034222030302003400c505142207080409002201a1aa90180103005400341000c00d84010b00800b0000468103800038115626141040010004000015004600240156404a034204e143d95051050300103010a0700000c0d61a650648820314084a9403c08020304001003c2c01241c40281c00f0610b01d50348000950303200c2100b010311400d0b640d0320004240580d00401da08000200046401e11603030716094102155060910400d214070304005600300002d11510302e4140034000009420b00c0c1245042d00300e680d075011200c2180c0e4441504e410000c0140004892441460061003024a100305500c0c00d80b4050b43d41c600d40f8803043c681401c00340158003007551000c1d42444902028240010361003120801c607244200004910f0805d034103035880e0040c0c400f42074080310750040e582210002c084420b40003a40c0c0022 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 583755593 1250 583754343 583754359
    0xf09060604021b010c0305010e070c02010512040204091401020c070b0c12070c09020f0711010c150e0f0a080d06050109060c0609020105120a060e15030604080c16081f0204060509 78
    0x4050b01403034145480342c80c00c0c1c5550905c504188015010780c44641203a941c1e080e0015960b039081c50845600802d040001c0c041030080c040701507985d001c80302c92540103201510020780d103521904d0f08034402514600d00b841a03900010810103800e414041c113401041100c010301c1c20720022a580d02c0d1034042401800c1c1d0320140c089008000e1206404e15403008001c1c545086654a62038886244c681d80505401c0d188450b407500c010381194400c07040c0c0d10740207412030801040c0c0010400d400c00900340f6502c5c040010f1281240d500d005403414855100003d110b0300304250382d1f49480c0c03608001e4403800e505c440c0c140030111400f04030782504640302528070307a0f12000c00904ca54140c030043c0c42c68010103500c0c8440e403641d0010401da48605178050310607030323003406a00c040030354502c0403000d0200d504e41c80b00c60300342d0000b00100340002c00300400750500b05165030903141414400b58544c605016107602c5420550b20100c0c074040741012160380c40d46e104070f209005515050074400094107174420211402d001785a8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 583756843 1250 583755593 583755607
    0xf080103080322151a06120612030a03060302360c041a090114030c040905060f06210705281124060a1d100305060106170f0906060402 59
    0x1d0003004003100c07011400d40b480c003c281410740c507400d00085083c2240b0b1030241400000d607004c01e4201d80c1d030b0000030300e4186480c603d0a4114815580030b4070542d013042841411381c2c3d9020060016001c40c0320950750000c0c03405d03e50f004000c40c8221054508444407071401c10900041c01c040b9068018010b20184c5c000c0d952241d950000148c822980f060b045110069101800320a95400802c4100d200b680c3d81d9809403ca1101c2c80854441031b10308203900310081200708090207943d0045a0300c40703001803803580c4802c02d42000c1081035219070f40d500b40d40c04598004900d204210400c140c0c1081c02440c0c068102500074a8120010103e00c1d03015600390b407290741e1011060300c200d14006c013035a04a02a00c03c501c003c2034031040d0301d070204080500c0d0740380498006641c80c01c00c480d1107412501500d19280f040e0480794521021004043d001c198904d01c07018001c80422402c104440c000c00c0f46591f00c00380b0300600c0c500030703000e1900074200021001540003407100c444400246a038011000b16001030b41d40c44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 583758093 1250 583756843 583756861
    0x903030a1805030d0f020c090145150611060708130c060905040e0115060c021f1205060607020312030712060909060e0f030703030213170a120f0801030803 68
    0xe159030140e941482000c50400d044d03640105103010143d1181c00710b55410303c0e514104040d600c824001e501d024002140c0071040740c402d810b01810b801c0c00d0820020901a2007404001c5030300619090204403036120240c5090900e10030200708000c0455180c40c0e0302c111002100580c45000251894042000d0400441d8a4200d075114429095500c001601c80b1660760320f0028100461a20034144120b103800000f01d418541030052041103403040c03d60140c0781d800c120064804905060090b03800c9602c00081c1d41c0c00c2004000c400760521501c1d156a4500220810b0090543d00001e1220f401082d05020700e000503200052501418404c0c0c00b002a07da949a040490f0800a40000c03030342420b04000000841200c2984901c0d802409032900748040c50b240d0b04900e640d49003003011064554010031849010078070940c0946888030241c80441c5500e555502c03854000c8841055040641e00a00380a40402c00074201c000d40602480c2003048000b0061180030309031510512010381001000400545408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 583759343 1250 583758093 583758137
    0x20d0e090601090503030a020c0a1a040306020c0a050a08040905010f0b03070806121b100221030c09041b090f0f0e13051c0306240c0303090206041d0604020903030a 72
    0x703c0d01408690710303407603c1c0c10f0080d81c4007000749070140079010ac5040814610003001260200980c3c500040e85000d107550b456000035845140180540d00039001c405002540034898540758070300900308203883d0381c100301c114011180c0690201300c5d501d03458001048407184050589074000110f040058007541c680000c2000d0040251088400740603010f0340130400070b905560504100340a544c2c44040b06d0294000741d940e0614103101d520740c0e5076610300d07156100b15002d008541c46810400441e08048420001c42c0a56011152140c044d50b4505018083e50354401c01000c018201074030344030303401440c0ca4542000301c1600d006e2014003040010000307080c2801c640c1032841455000048400310214840a08405065502c410f00001d0809200017259100800325031804004132900b03075a141e00c2500c1c00d5803104440c00c03048050503100c2012401590750840031300014070440214140c200e005080018500d040100307118491417050290b008682c5002059558041e45802d1001c40c00004a101d0707003143e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 583760593 1250 583759343 583759349
    0x90d03151401030f0213080105130308161202191e08150604030f051c05031506030414011505150f0a180e0403020d09050f150a12020c0a030e01020d0e09060109 70
    0x600000781004004111070040041f507030108020003994035614001035990407000d0014000408500c01b0800a1801d5400e9000f045020304100d030119803400e000720260303084030010800200c20020319066041d0000300d5401010200102d20510b114900d0000d0a140406030045200307500981e200c103070a480e41c2045402440d00303c1c03500800c035205484d1480d66040c4481e0040700f800344a13111800e0003809442a02e025200da01114852280c3e900c041c8450391b080203000b9245501035540c0c00814103020310800c2260480b42001100c01c40c109410b110441c007507591000d5402d001008440c00b205125000c3c2c0c1d1051a0600e003070004000500c4403400360f84401e4100c100001c00c480240410540c00103000d0191380e1701c80d2144010960742c2c0d0100000f054103002e2050704040e6100743c041d6101340e000d0040c101501d084c145658100048007040c402c80c0c01100c0d04011607817200d44940b0034180c0003000b03000f80240902c0140b07100341d07041c48014130401030709964902400c595804a405680a60808006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 583761843 1250 583760593 583760621
    0x12020a1112060a020c0c120a020a0f080309010507060f050f0f011d161e080103170c0a24060f051813080a03090b07081510020c06090301090b0708090d0315140103 71
    0x4400030b8031f00003521125506404c900c12880d0030310000f8102403250b9400112070100002d1820200e4000042d1030992040c202210042e5655015805e600b00c076200b10b900411b0a0483d01c1500d25108681003400303801070700004031009544100079400349140107401c1e400101c5040c4400c010700f03200d4060740d05c0761004d01da003e070f2000341c1110899070b50ba00c00c2c0c44c00e04a034055441d01038000e901d081206540d1260003c168a41c2c1c0007002c81c100802c11600b00ca40b040c1c0f104594106150700c80d40c845e201114041c1e00808828040420f0400c01403900417102c50140021a07040092400c1806040307000f2001d032607000f044080c011450141150107984414400c5420052085041c94521001803110004540d1402c0e43d8a564904602c241480701040810f101150000c1c00d40341d502c50300308143c9400900346c1c0c6a141d901c0d451040700207140c26048a00841042d01c41041600700018010304080d8441140001c2501c1d060595801d00e1404034114121404400d0801101c1e1280740101c0240082983d8924 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 583763093 1250 583761843 583761859
    0x4030b0108060726010b070f150902030610060804230102030708071205040302060c130b07060213060305060a150509030706020318060717031312020a1112060a020c0c 73
    0x1481007000301d0740c14400c040658449950181c00c1c0310308252000800f000c4c1c0c42c412010380052140526850050086901420107100c020380700d071fa81d40da941560001e9840503aa201c04180c0c0460804020342900161075483c89114103052079030050100c40020800b40c00c891070005107c0300500c51191004944280780c2c025513036071400d020041e2084900b0b84a210001d0814090200642c0032440384600403a40756018000707036220140d2080844e009021098003845082034001b603100841d0008080756841520b0268403949026030156000305154014828903040c41c0403c0342d241d503441c1c02102911480c3c80c01c84044001e01d44201d4a0380500b1011036010300c0b407130802140950700080030341005a400090900c541b01e18500740081c500513048000d000741040307411003003520300f184c2c06554040d003d02c3c0c0e10035240d241a15486000c002510030310700541c001382c0308003062081300c03c0f6000d107424095601c1c40251f120030500c0e981d13a02001f84aa43c4680e404100d2065419040c86441903003580201140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 583764343 1250 583763093 583763099
    0xf080d06030c05091807090203100b12010f050d1113020d15050a0b0412060c020a020a090e070f121119060210051810020f070204020d0504020108090f03090f030304030b01 75
    0x30020390b00d1405181c0c819114800014010b24800c1d070f0100c03228081030003402e50b0307601c0d03c58498017035000a400c1d003411400c505c001140c14900c24010b01040b00091600c202d1a503d80f10003080182c070b80d034220a000711000281140450f0444881c2049110300752601800e141a000d884402400b03005000d4a40605240d40d00300c047c042c0c145c800c800d0b100101c80c80074060b035542030142e500380700764410071032402c00386443d881c04603000d41e0140f0141c8a2500654042a65641c00200c1001c3d0380c0e000704107001e5079103001c46499001009540044e00c40340064203400c03800d002d4840350000c0000401044480b54030354074403a5480e860821601200e00041103850305403680b401a44804100140c145503601d01000242a4108aa41481520044c2c4050f01c09004003030524006940640c00d415400710b802c0040704010b0310fa603c010004103901d270310001864206440014501071020f810510154000ca04021440502000303d454104003280e0944c0900e142001290840c0241e5101409480380c1030000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 583765593 1250 583764343 583764353
    0xc060b060a0e090901020313030e031608062203121503020a0602151e04021302040b030c070b06150306040b030a05010903020a120f020a140109050d0905030c01110a0f080d0603 77
    0x201c142c00702140c2c001c5081d5103002d1a81d00f00d00084400780c0458460701c0004d00880d002d6850104c2c80540501a2900322400c0c4045405500c0701e50710002c0d00398451003c10512407219038009558a008160b40801c0249540700201115910750202d10100e58451b4072102004040d814040199400f4090782011036a540000c0d498110505801c0362410320303040081c07001e8180300d886d030b003540d50b42d000c030b803600364407140c09005400d1101c440c0c2d41c0b16503908010105d65005020301030345c03080f8040007010b0364500f61460440501c520140009000340048820b0070480300c0040203882d44900103a030000380e01410300700001e01d01810384001038519440c20b6000d001f81a0b000c66400e100700c5c092451340b07181003500602203c00007568440800160000014200007031014a0580f00d15070740000046855072903515000d0400d1496100311001c103080c01010422400e00740300604d140942420020840c0c1000b000c503985031114044018100b00c40c880b644010400860183d411182240d90200050340e124545 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 583766843 1250 583765593 583765607
    0x81f03030810050d0b07030507020a051929070e0604030c120210211d0f011d0307020105040b030405070f351b01110d0905040e0c01020303070c060b060a 67
    0x1419502d0040d00e0020a040c242400100b69071544800502e90301e5444020071801002d0207016241180108000c04012a5081020800008650b160011440b130b051603d01c0c0c450036100c590582c210900c200d0300703503001804100c89901c00500c6c180704940109030300002d031151040ea04000c1c5602018040804c2c40801b4890a410700361003030b01e01d2840c60008d03002c181c03160b01d000c0743c0350351002c9000c040000e00100c03c0e400c10401c0321210a9008804504060094105000005500380d139a43d18280c0307690480801c90741d42884021200910310745021900024041e100c0c0340148400c1100c0000410100031040004070014151380346400212921110485108040d85142001802090007070800c1100d86c02c51040350300990000411584c000c01313030340f00d000c24030041007a414841c00c40d0a01c0d11101060049000041d403d5403108140307401d010400003162240c8894200300d52040b13003458040c0c1d0700001201e41061050070042402407103860107801901503528210340004011031410103e58100309 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 583768093 1250 583766843 583766851
    0x32105090c120a20060304120e0108060607060915050c0a030b2b11040513060e030a05070818031b10081021060504300906081f030308 59
    0x41510807010503542080b440c040e042c4811601030b08000d4200b00040c010702d400440d403034010010340725104403280006400740c00440d41501c40c0e40c43c035150210b60a41c03080c0c41c0c0c2940042403c010005040800114480d4041d001008001d55916580001400001c88070103540074401041031206182c80c4602c00007540000d1007003004a420b15124010a2501300b82218400810011007034072203101450440d151007402505070b0b050210304000760140e48590081a214000c5005110032014091030220120740d03403912170015540050141412581e44242210001600f01c14440e440d064281c1380e441c2080681070310b0a60510603011010300344061201c01c05590402219548801c100300e010a03141d050040321494804440588103000c840503880d90318a01e0908000034009070f404540e40c8104039001606c00341c6101424440017940301c41e0401c055103420030300796601281000c1183d4042c0541030503002d076009008042c0b0002d0506c0c0d0300d0b50f0328214030300d402d00140b030700c8565a4240a094414103403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 583769343 1250 583768093 583768111
    0x20d060f150305011a0d0f29010203040b030406200712030b010503040f1412120907081b0f01120f0b0910080705040506041506110c0f1c032105 63
    0x44501524000d01c40c15040318249105045d6042d8109100c0d01140c0c07016642008481d034468140004602910030150a003100c2e20104161043e0440c0100001c0300751850700341158400c20003171000403d450140c98025610180205003110350a2251545031001d980c0804440ca02140440c18080e07030341d81c1610040c4068a0421404240000440392407208682c040d08055442c1040b5002403d800c00b524034841032407041c0c0702060408900b00040743d010480d03404003030500b0014880a120300344050001000c81400804180c17082e886a6004114490403951250700715106000659004a2070750105000500e010088024600c1c6075100401c000101240114080720000720030305a641c9444064a50501c020100c11b440c2004001c003030700005000b01c0c1c1003511307103040401c01e10300188000042e00c841d8480c00000d4490810191800150310132130b0344205103407094043d2a407108030f56112015040b00c049010f446441c282540d403000c0860309810200203190300d501c0c03032925951125008103a84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 583770593 1250 583769343 583769369
    0x7080405190312021f06050102031e161b2705091005070807080906060109170106051504090f14131106030a2304121d09150103150e1306020d060f 64
    0x11441d2176003100c205000303c80c00740e80704024810408544260174080150408001c6107440c2c100030842d41810551402100d00110400034445214511200756000d000c08840101420805001600c22034410902c5154025a540f001c50a114800e206400380009481c10500031420301a80c000c01c544e400b2201c00001640000114014910205601e8006c0c0f0059546040c603509261046c03c110310300c0409072110759620300000a141d283d122000b010a14945112501c030381c54500088152800b8030301c0500c61030316100e0350303240714401d900070690050150581410215050700d0001d6800d45142c3c17041d0307030060000c0200710b41a5050f0b003250740c10705040364440e0113a4401e40c04c901c00441c81503600602a008401c00c09a155200b05d19010341e0080819003d140f500003100032483c13450080c0d0704004000c2c0741f0f1003200083d582600609481480e80800350b941603150460302004102c015048005180b0021103690501803190159804c02a0501d4208403c0e81d9403420088404001d100740491060341c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 583771843 1250 583770593 583770643
    0xc0d080c1203071d01110d0e030f0703060e1908040b07110a03080d060602060603030a030c051b03040509070f08011a070206030c03010314070f0e040303020c0d030b040f020708040519031202 83
    0x8580c08006c41856000018036100184140035036040030080303941901032080c0d01520900c0e605c1000100c1c01180607400010b161a06003405509102c1084400c02046051341301b81c00004c0ea102d0101e404a9803944282c8e501c40b0010301e01040822101d001c103d5004100d04030200600150000600407001003020030050583d4402040e61649001c50716640d040e04240014007005000e50800200b013540c926000d49030211030940480c20304440da0a04603141c5c0041000d000d28240071003000c3c0c01004a0801e1100e1200c01a402040303a0320500078030703034104040703643c841c000e00110381501c144c0c0c0e80c010700703194232443c2040100070306400902c015243c554000e462007031841404161001904ca149100d12501418000e0b8946200700240040b81015400c201502c031141c0244207191031a001c5176000301d45110107800b00019221085440002c1c5441008040c0c00211a40d00300c07030803181d09407900c102100410080780d403911101e40c070250500b20540324112402c4d602281118110443c0402a004500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 583773093 1250 583771843 583771847
    0xd020c0406050d08071a0f0405150f0a1a060c030309011a06030a0506030a0609060b010905060307020d0e0d0506090a03120b0904060b1201111201080c0d080c1203071d01 74
    0x440d1141d581c20400e042e0fa00e4001c191401d0040134114012620b01c2c004201d600c59900e039405044403903258210f070306420300007000340034004480300c3e035050b1001d020b881c245000000d600c4238014001010156545100b501c0082042400102c1c038500149004d481d0490302d5010364403039004685420055203021404840b501002949200603607001d0308250640c1c2d603640c070301c8004190261185605104541a4500242c0580035002c480c0e4403850010400c11220000502281c1040d0051803081405108206040c1c3e40043e0409030782a0b0707460041140300b40720300418484045000c02030514000c01040007200f1000184007a00c2034030030798520460040548040085031407145900f130340500101c0105010416a802c000c0720080700070201034000d080c40c40744a00b1286250001d05e81d4840220702d1040c444200c0300028010300611014005854034000050303152000c24000800d414000304165056000410503c50404020441a6903078144420090b103500241c022252243c0000c40507410154 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 583774343 1250 583773093 583773101
    0xa0c03110a030504030215250201030c02010908090103092402120703021e30061201090209070f090b0a0c02040b01030c30060e06040e0d0e090a0e0d020d020c04 70
    0x2601542e43d981404c1c110307800c1103c601000140c0d07001c0204c00b485084004000d004000c01205229948510300c003150340f001500352001040c4c1700c025039151407100c001091200f011244200380074603000400181300d103404454211460301c1040380100401c5403100c262241c0c0c0c024001006c0d00d12122440340d179100000c40684c81800030100b80907604a400da080c00b02d00c0c0000d002ea01e006c11890302202c1c01510f9000d004031117030010080303218410a0500095060210f64040e042100c400240440025a000300310000b030042d110408000c2101a24180035100b41c2c804da0192001190065481a50b944020103640d203048069104070710300100c1d02001d41c028818450401001c1d03c1e005130041d128810801401d00c200080550f10145282001c03189243d40b181170007820340910402841e0904600340011219500c0030b440703040e40400302c060b040f06c2d0805000b0419880844083c007043c0e03680507034100900321450860f4a03c0c071494010149068011603543d84c07454190b400c0701e40380e281000401c019a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 583775593 1250 583774343 583774363
    0x8030901151a0f0a0306050301090c030201140c06010e0c0c0601150f0c1220011e0f0c052205100c05010509060613020d0e03070b0103050714060a03020c0109080a0c0311 74
    0x8142c0410081032a55480000f038404d198a500700000d000c0d0352140404e00351000880111010324074400d0510031907030031012203c01e40714900039903030034826803011081d5110700600485401900190015400c42d4002c0b089441000d10381d01910700c0303942d50f40300d0aa440a1924000800700303c15805414085125125000481d50805c1140040c016408416110a0b1100e41d07640e140750700d0b20752840900d0200f4015401e2104a031080030b01d640450006603000c9079100c3e6440340780c0724145046450255800415280941d0b4440d41e4249820221304030321405d5801070380140c3e044017091f017041d1b030802e8004804c240110b026100a1095554084041e84c41d40002c48016910106250000c1000042c1d0703070140540004005001601401910865107950441403080f113018161324010b104216086c00b142d0010b00c0b840502690340f001034400201c0501548060b05c04140e80841d08480d6640c09421003049207030010f5070ba50381d40129140c0100304c800e440c4801e0700461380645600c02ca20800140b100a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 583776843 1250 583775593 583775639
    0x4090804060f050f070b06011205090313080114041209050409060203190b091305010f020f03060111030301060c0b221b141f0909181403030f1605070803090115 70
    0x500017040c0d80d110700c0c002c4007504940c1005098550008902c0301c922626019180c00c400860311035041078148007651a498100709242c0e4140619120184022088985c101e07a109480c00d880400080003201c194241e54005607100707080c010307181c09200181d8015401a4201d1804401c41c0147c1400c64090b200d580c04400d1300700d00a0000074003040301e0700c101c2d20511446a400880c03900c98151507507042e43c000032282e03c108400081800500e41e0000622021a8582c1002c1c60070341d8034107d0050a03000156401414a144d1a070010701342c81000702440101440146598000d60158204030b0742c0c41200c0500c0c41c405040ca4080400d114030030b0548085800b0004200c841003040107020501481d280364189818003c821001103a075402c24001c91090465103410302301950001d00300814816250a600c1b80359800070020301442031203103c14030340e20010800903031581c00e2201408650500c00c052010b8003902d0040103000c0c41082c19007000d40014242c00c040702040b0348030300c04002c04000d40550880c2b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 583778093 1250 583776843 583776847
    0xd2004050a1a01110c120606030d08090d03021305041a01030e0a17070c1a0a030c050a020a123e01051618050901080604060f05010501020d030504080904090804060f050f 74
    0xb4561041641c642d4180000003940c1e030030a10b09002c241413042030942218280c01010420500d030408101d40030030052140f92415060401b501070703640312020401c0d18800c160300014640e03100c0d050705455400801001d0410800d41002d070404207410860a084c0a00003801c003403001d29810300000740c0199441c0c01580002d15582e1384007041e10340b0f9202c00d03801c81b000c5003642c0000a07a1602144102d0743c00004c107a4042c0d848940010050451795000750b4081808414059121450790004001600c9a84455141951802170301d054030440c1d8010703265410180715820700c00b00c20090890b541406e4004054544501e510010b5050990390210741d801c248032000714540c45aa4071501080803241588000c500420343c1b1540820302500090300200d040703908c01030a010401a2a108205c19400490f0080002d0f5040500013034a880e0b086802c2d4041544071800707d0705020000303080780c4882d140200f04001000745c901d000845c0d034100344952400700346089415541e05001701c2c100c0d00070305031190784c82d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 583779343 1250 583778093 583778141
    0x6061d01030b040e01020f07150204140f0409061d0f0c01211503060902030c030604020f150c01090c0501090e06010504121505070216120b070e0d2004050a 68
    0x4004154030b031000ca5010707071194440000c0c900c0038030040860300e5240d40d28035030300e070160b0030064500700300e62042400e0a481000104007039205080c540ea102a42214050300100c103050000d8050496034a014062926200c0421183d002d41900007201079a000240c90303640300c19a0803245c440d4031410007207000c80d54407803220751001d003540c0401000500c00780c00045d522912840105001110b07400499210707540c0c041c16010b40c039003000086d00144080f001000640f502d0750100d00d1522180613964050340f03040c2e41040e10081c40302c0c103031180031004000803c45001e890401c41d00e0b40111b4402c590104041c654003145114200030300910644040e1151443c182c5001c0c050305001201c10000d03103100c0c020003035078545100705001d040d0040c4c0315030340102000c03c001c0d8020052031040b039015001c51154103081c000003480000c0a19880003407400c11049011104c000300b002c0329240c007030040c01c0d1900114410300b5080b29241c4064080c0c3c065500300079170b0b40d480d61500300f100c80003c41d4030301d0001403101c15 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 583780593 1250 583779343 583779347
    0xe06040c140703080a050f04110907090801050c0d06080723041b080a110a14070f050a080721121505131a0418030c05030f0408010f06061d01 62
    0xd4035645001c0c078014404800c0881200e840d80c111003422070002d0007410034008410304500541340c1050310f402849129040079075401c04010008480903000d0703c01640003843c001d020310354490051028200074050791400e10011a1254419290380c6000b601c0c208020940c03200014801050320320f802003456030040c3d800084003161950060884e4081d4480348114a110b00a4000e240449082e40716040a42000b86405095072080300f1886090300c801d00c04603c4241d0b00c9803201c07481ca030030100400c0e1350308100c0c01c000309078002508000e4040e02c500f01481c0700b0400c4a5000300100d40c0a409a101842034911078020316140340c5a9081c00a45010790035140010968421100007250360003099250380c0d98070104041c241412005080b0316951600c518032130038401d030004209a8200c5d0104002c644118508aa001c203100c0c0c00340c01c100d50f86000c0400c100041045030908100c07000720a4649a43d007821a0113001031021818255003003100c0000c51034000c006000012840d1044000c424000c0001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 583781843 1250 583780593 583780601
    0x1c050f071109090c0907050c01200d1413140a080a050d0b0307030b04030f0e0405090a060e070b12090321010311011404210623010f0e01050f010512010603051509010e0604 75
    0x300d407201c9d580c400c400030b25510711480400e200030300149829202c1200c80343c020122184449083c080d00300c80341c20080c2d0008050001e0821a60042c009442c450038030324a28504140014028500c090000b008041c40e41c01c44041d140141d1065003c3c480500e00380203268803085980300c000c21103d13118000c6070010f4080c040c1030400d41c0442c5407002402880da0006015a001540d01c16055007211a8010921500f070207400041c8220000400d120742c40c0180d2010b02d8490090000550741001012480f0071800f80112202c075843c0300c02001c42000c0912105100311828441142e180302400d9001009501a00d0030b203501c4120802c119060038640005404003407080030090031008840c140c280002205ca2190800c0c202d4140030907022884030760f507501d24440068100900c444503010041045000040c1c6080c107607203042d15404840d400400043e60030340503006a80203262406d01c00881e000e645517101714841d140080302c41c00180761810500148450a000c1c03840404000b40000e4018142900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 583783093 1250 583781843 583781857
    0x2040608210f04092f040f0b040e060f060c011a0f1804020402130503030313050f030415050d092003010506180402240304111906021c050f071109090c090705 69
    0xa016840c00b604116200211405d003401c1d6500880071900f44820080030113035501800162008900e0181010120b01d040070000b48143d1040303a0308003982c840d540b036060030348904010104c024000c1a030602ca074800b040c18141c0c021401558048000030040c030304624092811151341e80100b549840e55001d220103548000038144050320000c0700001c20740c030200000c503c5103800801d0985000742c1c9140440c10400511314410065100380001e0018a00150004501010f82d05140c0e64540304042c0f0003018040010340500210f05402724000a030455190301c0f050b1000c101c2c002c202e031f6582d1200700203415400b05030008400d034002e03001400500303166070110b800528a03c1c00410340b0442582e4888113501c111412285c2c80010380340b0348804e00382810f4030300e00b6940b07810001c0c00d80f40c00c21030f0003592010045e01c0e080079003400700c600c070003654080c00859064125903039110741e072081c40b4204131414811252000b4060300741000051404880401c01c60040c103001000d101013a202c00500302c0382900540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 583784343 1250 583783093 583783121
    0x90d0306060512090f0714091e0a0905070f0311010f0f09030803040c031e0b0f0705070b062b030216080718020f04060c02031e0d03020d0902040608210f0409 69
    0xc800c0000e00d8800c215406c0242541e4076a038080c034a5160a10030390400203441620300002e15540c24000700400519071386d00840d00f03c00001d04c5030207420907610b8070000383e00800c00001c41c043c01205214a0359080b5441c0c1d2000c0c4c075811496114030380d0807a1100240c0b03c0103030001e0001030040c40081e403103000840e002809461003010032500d90b1150300380007220040561002c0c0d010119503042203915003200d0740c81078000711050b04601d0f000c240500107214864004103240804c20000f00c5070387e00c803203e403001c00200750080040e4284c2c415240e41490b110003002c1c0c0243c410403981043d160800184841950304400180090520b0490ba03c02e045183c10790300440180c00340a0040035160020150000300305680e160310320000d04d0f005150502c80c0e101c10980e440e11081d000522600c82c0020740014583c600d1030010703580c2d81155200e200421180320001e601609048002038282c100140140481c0419600c400c40901d9040c601d824038460070078142c0d04918188420810707404103070f00c14004e200c106 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 583785593 1250 583784343 583784353
    0xc030513090203180d0818010914060907090218010e0307031a070e010f09060f05040f2907050607050f0910030c020c0103020408060609131505090d030606051209 71
    0x540c104414000141d00000311071030780401040722001310b40800352034903400c0724040c200c0f40c070440d90000c1824000134844c85100a52003100c59501350250f2104418070740250143c0e00841070b0321022911104260b0b4035544a104031306011a485420f882140c1d0700800080b444841003907141c00550314181589603495050048480020216040c0400801c5480f004001002289405100900b081c1c81410690381008200c40c102c52165401c0450682540c0302402d0081110300c001c2d008840030301c1550010f0604400701400080d00320721680d08042c2c420410102f104030141801890240da02402e200a819a071103d8041000280500d000b40101c3c00078030200d502d001001804125004020048100000c3c0d40c0d180c1d1100443d4140410400c0003000d1038290b00d0b00c1d00d000941a1b54034400ba12280c0b2403100c0c00d0204600d411000c0000300070f05c2d07001032084141c041c0102604002e0404841d1550180101200180164400d111340c5007941c556403501c60829070314601010300100002e00c47c0f80a48a1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 583786843 1250 583785593 583785607
    0x30b01020309120f07080c01080a02040608190b0418111507030e030705040c1706010912020909010209030a0f151418010b090a090201230406080702070f1715160c0305 73
    0x140295400781c10040010255150058001441444010400544cad640f0501050002950050480c0d03000303416410740b40d040d554040352003401400c2c41c61140e83e200d4a06100280500e86000e841d00c40d8500413840c0076007990820040c0812009007525600b51004208602c10000740603035500c400480780075040b1903800340c550380410102ca42101440300840c0740300740c60f00100b049460950398800c800b8a02070101130b1401c00c048428084451000744151100d2000a28002096040e5810170000070100c4262141a0600d440001c0011388151000c2c1e60303001c07a24080c00030a00804821301c2011030015810340e100416600a503074a10400d4049540300c0282110613070b2035000850003051000c000040d22400e520000d00300300030303001550180440050004c04060788100c1500d08542043c180080c45503101d840880c00e106072500042a1010082c070007003920040c00b6100c0004415100c100d5960f030b8900071000c840d01a080303d0004004032090307900c014141c416400d540641d40f003424110305002d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 583788093 1250 583786843 583786873
    0x1203070c1e050a3314060301060302030706050703030209040f0501050307120209070f0c060603030503070912050d0e1807030203180a0b010b090a24030c05030103080301060804151e0c030b0102030912 87
    0x100c13120100f2040740e1548a805100a0305001098000004030002c21000d4510340c080703a2200070610400c1d041c17000115110381894040d804032964020b001b01700b00001450301c0c03615401814280a00c6000303102c0c9403004104060110301c0030325001e4009064800a91fa4131204850701e0765a400300c5000c01904400307410004503d4040e010140d07120341c031421340f6854241c9000f440035001c1c0d482840c014034101e4001c4003107900841c403c03a0183c5145040e910003181e031008241094512940340028640c2c1e50108500c0b40e41c10b901440c080c03100c9464104902c0d1301032040ca6a610700d481000303042040f03010010800011000d008212111000d401c001d02180d5801d003d0301e060740030480c520013000700d6a02a0026940c148156440800b0608100707080d941562607110990005003d120240051440072a0600c1198a01d24011951809084c407020782c400500c00b0001e5849000300114030306006080c035056000740102404070303106a0056040262920801074280422042c0c4995070107507540c00c02d807010f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 583789343 1250 583788093 583788173
    0x22120c210203010f0b0f060f04150509061309110702100e01020c03240903030c0a080c190f090b0a0c0605040f02040e150c04050f060c1203070c1e050a 66
    0x1402ca5440051803600760006e00c50102840314815100307003800c01c42c3c1204600d0220545042d00d04002e61420305918040d015541d42c810720040c2a80b022001c280e801c8000301c441d0018041c0c844251051001500009d0078072810301900790b000703502c450710b00e030303520f43c011702c1180e4100030014140b04480f143d401c0c00300800e041c0500b00d1403080c0000508682c0025440710340c0c104640200004005502d9480c025005d1001c074000d09111a04104600011030500b84060068440b150300c18800c030b840d10011014054101034000044030041020b9180003e8040700311029215205040e81f201e281e805140d81d074400040c04010021a45440007038000e0002d40c039288103122400400030028840d00d00b2605101210401c0281030010320402004148180d0b1175a0000f804806026140e40c3d0302d032403030300724010304014044562010f044c50100420030750f203901080c003181a03402001650000d6041303100c81c001d0558224005007450380152000d4000a981051090030a0b5090308100044d003d90040c40840c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 583790593 1250 583789343 583789361
    0x1c06020315010905030c0d17040305030d1d0a02060306040b060f0f04061101053612031005010c11010e0d080412030e100f05031b22120c21020301 64
    0x101c101d0301d03000d4082d58000302d4100180104400801c0000510b1000400c00216090001d01070b000074901c88500159020a0f58040c6901030140c94940c040d028220000b4514503413400003088403042c1c0c2e07071401c5002042e810708854001c0c0040c1e1841c0d85000034000a015142c04030f54202400301714001401100d40301900403d000d0400c4030b03568515006000702003082e01200d00c2d58503407501061224000d4400c1c01a14158843c1448801e0403601600f201c490940c01e01441840f030003400c06000101d408d6000461040e103c148185810a48400045401020b08a801092100c04161b0b0124a602407140071061000080c80d014a00d01d2a42d90700c00c00307030415808084000084801101050307000358421101c0901070710300200080f0143c1004102e40000c3c05140c0c01d1280001c04901d00c894540f02e0b403a0405000e6603c141e40f030100d20300110300c040e04415030040c1140c0d0303444041200c0100c00c150034400d40c1c210100380741035814280c0b59a06c1424404400301d007441e02c01007040040e01d0a024502017 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 583791843 1250 583790593 583790611
    0xd0305060f0a030f030f2c01140a08010302011101141b190e040b1005091e0a1815080615010e0d0807060605030718050406090b01180e03181c060203 65
    0x40300000b4039019080c180d07901d0440b8244034400d8084003061054183ca020615202e604008507031030b8800040e09e41c444c090200e05e841c40c000151001013903030001060f40c100e078804c0e40c1d600010f00741804064200d4410803d81d00b400b00120b80860342e03052025419074450400902c105103400c86008058012254124594012030340400114402d4030b4944503802016105481d110111000c2a1006104d44208501103103d44900365005c00e01110542064184140c05892200e0480d2141009544207070003510219415080c00206203420407861311f44012120020300828003070b100c003104e40d0080d0060a40c0581000b0980201841d29903400400c0d440250149080300c0d5201441d003480d0090f1143c0707030020f5010b5489114100f061180045071a11030345071075a0002580d440318034204e8040c0c43c0038032014110a51100022414404042403102c905114210421400e0140344000d80c8900420072204810008001c184129007004c542c40c5210303044c00c110318882d90f40540e803208103e030000d546481c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 583793093 1250 583791843 583791863
    0x1030c080105070201020f030f1026010e07050109030206220e0703140105031e0a0204050c12160f05030a0e0a0309052b1704090e012307020d0305060f0a03 68
    0x48816428452650000080d1000f03600c7c081414103481d42c284006014001a0000200025201072146001c48050b06040903140078180910841181044483c11011415440d140300c2210801001690400310303441a1250481180f840e020441c0940101c00548a080c415007801c800204994143c10050032880c4100c0c181e03821b10480050840b5100b020300c1a2107615003005108a903000100c088405020002094805046081d0242000401c0e20029037003402c0000b0b05c16020407000240000c06202110500341e90766112440052290401c40e02e004528070000f17070f01950388030300c0040d54405d80700d010208580206020039894544841400c0e00000c0c2c01400c180480c0c60101003450f00380101d4024000b41d001300701404507400b2a0307402c005001e20b13006075000000c00000d00a6030008c0c107030110104184940c40c02c115020306904007e400d00400c03030004c2d044141c8006a01503001d11070940c001c112500c00c01005400929002e041540d000301c102150310304550f500c0b140e1700701440c4107441c411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 583794343 1250 583793093 583793099
    0xc112a060f1902011505191715010f090b0a030b0c0a0302041e0312020c1c060b0306010914010501030e300a0518042003040201030f050a0207020f03030f0a032301030c 73
    0x240710520a81c200500c10082d4170328444040c0900c450704001e0b528021230014440440017002d034a80a9203800c8101c1c0406000000641507243c0c1034a1811200a00818000d200c0160304001e00b00741c0e18000100100720507008558000302c40000340a48401c2410010701c0c00b40c50f0000441c030a604c485c0030f849a050001c01c20b0082041724440140815054001001c14020301c1c000125031003440c501740d03a11200021894418000d154001100a82015081c0e1b002540c54141503000303800b1003541600789200c00d000000b45944280b08181300c43c4d030594041d10001d00c4140408414100307888699564410080014100c1e80f915401403508911503100c4542c3d038850640003502c420b2441501c00c1c8a1450100c96408494205811101003180490000d80d2a40c42d44010390082464080f5040001d281c4001c0080c81c91555000704061402250100500b074170000415640348142c24228103907800a0000c20403244c000d400c2144040e1604403000501640900c0000406000b40d00c243d0b030504599401f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 583795593 1250 583794343 583794371
    0x80403030207420510050d05070f0803180f01210f050a0209030708010e030306120102121005042409090c0806040812100f0605090f040c112a060f190201 67
    0x10701c0383d1000300030107119034074005130640c00b20421481164052904d1a2805040100a0240314041c0c60f0030b0403801185602d6007480c55403900408009c0402540c07078a541d00c1540750000440f007403400d0507510380300b2001030300d11401d80d04440640d840410545030b5021020000150203068410032040e4001a184c44018042502c0d0241a078800390059140406001d4a4403020003100d0b400901582e40e074142d00003a409143c021f120f00d14085180417103040500402e14000c2ca11032003243e0f4126801d000c19180010300d0224009a034081802c415940203007084241915000210b07014019036134421110303070b5a80030504150048404503108000055501c0d2011074410701160429040c6942c451007a041114808081101340606001d1280c0429076000c503a491000e5138a41c1c4038003420a200f6010100c0c03028060b40420311400216000d0a1a0110f5402c403940b0100e190011440c1c031800450020302c14004280e0002c111000148803c000c8044070144086480106c58140e900015191340d0607041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 583796843 1250 583795593 583795703
    0x102010e2a090c040603090f0b0f010f090513150e15011a030c0702010e04110c1c05070c090b0d08070b1b03070c061e0c05030115050406080403030207 66
    0x2005102e4101001071150010070b1000391002d4544c103080001d401070950030111822821f80c00300800d0007860800300034101110b10129030407584e0070604024810f440e80515002d40e541203607140051659038074440d010480c114824550100343e00400110f1100c0d080607a41090120055050700781604030041100461300003041c0ca0360003003070011504500f880c0029121501c21241e01904200c680016024185d403541d1082d20740c8e06c0e0400003031340d0791250200311586592465807500d02c4d801d031419140d010103000e407040390302c2076601140c1809100e0800000200a2000082c03460f040075110382c051000402007002002032030b015050108071803030a49084100e000300110740041c0b9480600500c4002500682c40d2800203522010101e80203d04a02100283c2e60000169080d1420400840e40054015000714141c9100ca403407030740c076001e5001c0181c40d40d115500c6500001009040080c011034030950141056500c6002c850701d0083c880141103c1880c0c07001040130b559003050303c0c03600c1c072a8080e2603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 583798093 1250 583796843 583796923
    0xc0315080c0a1e0e0106030c0306090e0705190506030c1210050d080306030a17040f0f0b040605160c0b180f0a14040f09061b02030f0313020102010e 65
    0x4000d101d1200d28802040154030148100035401c04044526040c203460742c07010030042d000300c8a5441c890f6035620300007405001c1c020801c4000ca0b1900501280c00300313186c01005d00616641005042d52032402d02448021219480001e4406810920204559941c3c20040d030041079681481038844120b044004c03031440010707060006485100d001009551a500c40001a02e90480c0a16840303640c1d03580480d043c44001c0c040142404560307001507281c503c015000d0800c3d03d000210b0103403040c0d256100b103910002c2d90b001e8050003a80a010070042d083c0300d000180090b80c0c101444140304040d503504c0c07400f0909650000c40084a02180104010341c1a09464115450841e98031200052180104021a0450240d001d1011521107014443d4466802c441080ca2980380100490b118a007040001416540035481c5e80000245070718244a100000b52144440c03950506855030700e48031a0680703040040001241903548407940030341180b03403d00040807061071081d031904040c2d010301e03884240c0d5075102c2c1d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 583799343 1250 583798093 583798109
    0x60607080c121b16050114070209040b011508060303121308192c04230108010b01020f1b0405040c150314070903110f0a080601060f0f080105030a020f040e010c0315 72
    0x80703108107101240e02410b04c2114402c4c01c1c401c2d060507112074000240c0c850104081e41003141d1805100c10407034042130a60499000c081d100804100da03201c02c44600c4001d481c06035160b801817054184241c0d8000780950440f002d8841a0042c0c031080d5189031842d00001843c03140ea50721803480400c8150004295940d084c3e000301ca4a6440040401e01706203c1d12420407140503c1e034503400450060382101c00c025003035105580d01341140d82e59242d140e01070f03e06d6541140c01401404080010440d00065120b42c9042248113403214010074024030009003002082540d000014000000307904600e4956000100c44940d0081840d41544480c0d80c44060007410300d90030443d4030b10040001c0b03030107110403400340d1387d0460b07d11142028800c00900c00002035000f0705001e0103041d00000f0420b8100200400d44140303911051004409580e040e02c40440910a180d0960070401202c1c00526251386800c1e00d1303a400600c00507132003509801c005d00310f4020303a602001190380e8000510191003403800403c0200249 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 583800593 1250 583799343 583799353
    0x90d030c17070c0501110d09050715120905031b0c09090c03030715060321080105010513030308040611040f0e010f42050702091608060607080c121b 65
    0x81c200d00e00540400a1510701040301601c030031001c1001c20b41090b001030402040039034482500b524a600104451340302107405110b413000015861203204104c0741c081d00715803104d002d0000c0c88849034002e41139100089030680002c202c0d880c0030040c1340344000300080d600002018112062400d202001d84044c15845095000c00e004d001699400002c69101c2540040460050082040041c000d0035550f04024400c4c4070020a40f030541c030b221035101e00d0007005946c0342e001a90783c0b0300065a0714414031200c0e50b00201d1006040c408030b402642781d507411034030078807000030075200b0045200d03038035001034104001c580180c12081204801e442c0203103002d0314a20160307015003464802c0000706c7c200703500320b818a6070f5450090b090503900c025070034003152000811401201ca48144004241c0d5000d080102e02c66441200030a598141c0a42d03110b0740903100d41c40d42c01440d2940810080b060b00242d2003203941d1581040a00c58000041c80040074285d2034520f401d440d4405149003136424a03088218590079400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 583801843 1250 583800593 583800617
    0x9051003021e030705090106030e06100308120c0d0516020705040213050d0512030c1306021c0e121614030f061303031b08010303021b1e030c09090d030c 67
    0x59110002d84070160701c1a074403400b000c940701183c101022540301c140d01500704070001400a8068101c0c01c11f04480005481e00d0390740380320382c040e40d4a525010140410f40c05001031425030032400d01441e04002e03003031610741c10400020b605c003056403001c0f9200d582100c52400305114040d0100100805850211010750074a80d80c01d1070b502901082d803198510803c0075030041014854288010184800c1e1640b107a0303a285807000902e845a07212a002e0400340110800000340035201262081c10056440028040401c885004440800311001c0c1d8990140101c1d001e10142c1104000044a6405030302e8680100391403e601400040c61400301f0600a81116500c240f01000118141da0b1180a0100107981005c907410b040f0000d20b03940007404c00ca01c1d01034120154254100b580305040364841c0e402c440c01001e504110700c012000796aa107a40007183c00c2c0c50184041c07103680c0c242c00105c0028046904060044001400d04803090f1810010b075003251686900859042c003c000c0c40080d5401d007400303d088 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 583803093 1250 583801843 583801849
    0xe1210180b040b0c0c031603021e1515102c150c19060905061605120c0c03270301090b0f0a0e0106180f05060306060105070c15090905100302 62
    0x1100420003444000f100b000034100002100c01d42d4022800b030011a9210540c801d005081003010030401d9025105490b2240704000b1000700003850000c0700e1002d0002d42140459002d004940a05010540e0145841048258861181e019200c40c415a0b078803070010429128080324070040d43e4040200c180682e115581d40d19081c02c26030640c0781c3d0100d00c59607080d580d038809043c851000407140d1000303803450303010003805011f40251800c1801742050340c16a40707850f140c0300032002c880c01210020039010301c413040c041c10365407a0040d400b80780085640d14064052180034210360001424001484484c86a0724854107084110445618250000c0008466946451500080c000c09200c80280000e0028600203442d80220f848903841900038403102e5180d0b000440141030040060300390600d0710100540c40340d15401518090715018015005e15101c020045a050703018101c10b480caa03140703020002c1d00141c2000300f4032045016a0b2031106441c1001074610030345c1c1d8082e01c03440880250320700070b08c007680e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 583804343 1250 583803093 583803113
    0xa032a0203090d050a08070803090d08090c1504030c080d11010c080406020706090209070e0f0105031605090a030b0705090a0b09010e1210140a06060f0c060c0e121018 73
    0xb5402c90365082d100b900c42c6051460308a102000a00084c0c3c00706070710081110010265001d110704900307549400750301c802c007103400c181c08403108001a0300c0b44000c80c605080103c031814160100d440441d04d019100e0f1a0010101c64030f0740001131903840250780412a40c2d104500845035100a0000e12181c0d02644004050a6000d080600300550000358a002c000f4954008a240c5030701070000703584c030f00c3c0a0300c019082e8007461004c1ca00130341040200052940c42035003121b203d10008540c401a01e00000c07001c8401303801c00701c44c15401064800001c0049213001000750311820b619034450b651021a02e00344000e01c2001e5109909212040c048203070720b83c0e001400d40c3c06000b0191400d0b810b0145412841e8034002130355001002080c0780141c4c0d045d90f4280e00c0403446c485c4404800611400399aa0320450701290340c041080001211041d103a4005840c0f80c014011940d5030741f170090b20312400c00d80001c4150302d00040519640d44144000070f03010b5500d001e405040d000e00e0341c0c20000824103450b17180d411 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 583805593 1250 583804343 583804357
    0x2031323060703022a060603160b030114030f0618120414040f1805011a0a06020709090501090210050a02010c0801062a050105040f06060504051303230a032a0203 71
    0x10540200b201440c2c032414001d41d17868201e0502c4d9403070052024412003a05c80609486850190080d0f2a41c10103421075040301c01c0441e042c0c070507517034a541e1900f1020740c140c0b820325440c140d05000701c00030000403160400c0321601030350302c8401804c01040016501e070f01c3c0416121010400c0c00060004003e03101c0c0c2c074251001081001d403004660b075110004990700604da0070f20a001d48142010308081480780c15802404103044c119185000703003440c00c0402c04840180e20464005a00044040c8401a0950094452140701384001302e107c0c0041d5000444148494101e100010b6010500e15039180d0709004a010001c030a00f0302d8040c550410308024400c4800f94002d500d100c02c00070401380c409072640001b0303054a400200030001d41c00c0500d0801e4650b0340200041d502103080c0700001c540c0e0f1a0520a0f01d010b15a01c0b241011a022548d07002d541d1144030500c0d4944200034500e003809240710000c021300081d4401e641c005001480300e1800c0e4880741d90b07040030b8080042902c0d42c036603c0c1a0008100c0f216 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 583806843 1250 583805593 583805597
    0x915033417043e040b0d230d030b030d0305040308060f0d1b0315020f031b0910030b01090f030f0803180706030c0f0206040c0e071101020313230607 65
    0x1140c2e41d07070400000d41c512142e0304407820001048603860440340c01070b4043c3c032140050021002004160100b00c10b4603102c02c0515400444140d443e0700240d078942e0002900c0c40f04102c41d80c0460b42d00003203a810400019a030380086611100c142004d86002d20003d80d03810050300b0708014904041d140144070880040a642c01001c00424a800e00c0c5c6e1100844010107070701c500c18048100750741e90b0a4012008a01c0b00f2180062040300140100b0311a00130f0300c241e80410703001641140d0b14041410549400785002e660075000801030381085885403480040d00c1c1081c0d4501041c44a200070004044521030f501c00c83d03000da0178007000d0002078600303482240700c0c942214030144c0b039460329404a458060000c20b903d040f4401c501001640c1074243d0401904100c05848a010507402aa426a1140030445004214001c1c0354801e011818008239210380040c491f25090140c01c81500e5041e0880c0c0c02034809052039104e200c3c04a007040040c1c801200300b48814000710b8499030700c0c910720580d94417000e4007000c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 583808093 1250 583806843 583806887
    0x1202070b160311190807090e131106030f0f0903040e0a05060f19030201091403190305090604180f0e030a05221701050a0e070b09150334 60
    0x1a420b200f60003202400f0200c100e2160f4814500300c0d083c0103480790821007004a90000009415240100802d04c2182e0780d090350340300030b0340e01c85004460310b0305d05000c00c9170007100035018440340e070300e0303000c0650311403000c0d100540c0c142d003401d070101615100000c05240440d8001c002c06d00400c40010701c0179030002d044100210b180e445480021380b121007422440c1d41c00895104003100e00c4000e10055100f203c0c002c2e2240804103407548404400b20904c0da04558051340081c0304818400316444010f042c6500a00e403141c280440d103030001d540c0780c2c400c0d0702c0300600e003100c60000c03030404032944116050103904481c10000a07107090340140e2240113a4a0f0302042c06404a015100d40100810f010008009030014900e8a07032248503d6040c80980100d40d0400e618100008061110a20402501e206400001c1c52454640000e042c0e050b4040c021194001c00301c0c0c0c904000804800300a10b006001300020032082c10718a4a402000d020141e205036a603134040c1501c0408180c211801050005182206207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 583809343 1250 583808093 583808131
    0x3020108060f0d260711120f0d23070519110409060c23160615030c050112050705031303030e120c010c0e060f0901020f0115061202070b 60
    0x115082414440560001d4090b01d41008201c00f00c0d01801e0a1320541d450340c41140442d41c0c8414060050344401051113a603002c0f603003200e2400e000e0215900100c1e00072189804c03403a0a1450030554aa039010000c01c40800d4480c8600000c8076001c40008104900c1e5400d04c5859100c5598608020607888510390000d401c02c801e1043e8001c402d084200302801c00e01c08030750a07290000040c02001e80217000105085424149884100c80780804200010340590610710101c007101d20401220a0440301e250b40c1303060032800120890441002180100340c1410250324210000d4000045c07810250407036440c050400500c0b40d0060b007565003000d83e440c0b07807a51503031072442e0a80003070001c06803201d464400c208848059481c104010301510305a60000e001002c03030420705803600709441440c40c1c2d02040c203000102c1c906111802a1010040500c101d4240340c2544c4640c0f400c440700011010400258500103025154100c18400c1c980c040740d180c01c40ca0203e8540b920020301e54080c00744003160010341645 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 583810593 1250 583809343 583809349
    0x90b010f080408191107080307141b0f0301020d060305030706060b12191e0b0f030d1e020a0b010603020c010b06190c020f1806041b0807081003080403030503101e0302010806 76
    0x28282c5c0d1202402210178054a80403190341ea41c01040e012661144525500e501c07111001c10143c03081034641502060300601001000203225918080540540d800e110328500d00f50300f0301070b00000f035000f00040d541e968503904180341621080c0d000100c1d010340030070100004074451421503034000f038001c0d8143c0d00b0381440700d01c50000c0e1980c401c4018108495001150041501d07030701c002c51700e100032141d00c0c60304882d10f81419201e8060003000000701700c080e000300308000b13521203815200d0315040c4143e0b5508078080e03643c500d00700ea007a000240040c0d0301043c1e801161a003482440380d4144115103076414511440c158810b6110954000030402801e200d0f22021921980c400703c03076603400109501032207000d03841806071074a802c984c103038802ca003481c50100c0c036010041c004191005240e61004081d41c0e40700c6041e9a0034401600c010300305400403000201085009014201540c03080d83c03916540d05000310f001d051030003541c024207043c01e00d00d04122001e51004040d2030860fa42800d00d82d055580320000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 583811843 1250 583810593 583810607
    0x105090708040303090611090f03070501020d110a0b090a0506090a080d09050708030d09020a090203100b0a05070f0804080105180d030b0a080304030506090d0c05070e090a02030106090b010f08040819 87
    0x1b00245e041c8110300d00c0321302451002d083c060300180d40c40d50608208104049e030354049441814050780120325546a2107200d01d1040840354541030880e450210240e580f2541884c04480180113600159003000411400f0b10810b130f0401d034500010003101d10147c0b182c003020312400c0c15032454a0307031300c60b110401c2003400c1c0900300040c001c40056a44860800c042d000c060b1040c1201240b25032072600c00440d0010b401e1003528003e0007804110b0181c01c0c10200521810344c807c0c5c000d1024844107020a500140b098454100030360301c10204e80d43c446107040d4507142556000b5000c1c85511907076605064800c60001740d5081c82d6009071501184d40014540400c1a24030990011480e900001401205100c0c0c0018128080e40034541102c4040064a90480c1c0c2c2c5001d00000401e00d400c465800c10403060042503507500408000c080d07403150703825940080d0840c0d049610143c0d03030300c0e1200707a418110340c3c10010002032102c0703908061401c1e141035a101c4e022485154060070038004005030715030340355104981d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 583812949 1106 583811843 583811861
    0xf12060f060302090102100c031401060c020d0605130b0a02031006050415080709120501090b0105010e0109152c0a0605120a05041103030f12060303030105090708040303 74
    0x240c02c4001e0740c044000343d4114801c08011f03a914080d14030940000207580c0e10005540c0907842600400c00b4416813000040c81105800c1c1000360b16040c4c0703126247c6d5841000000c10b030381c07283e41011000d5080da4026107580060820045804046d40c02180608002c8510070050766581c42c080ba0b03035216500504d40004101a42e000030f0500641c036560b04200a810480081c9460340d41d22900c21103042c00c1580d5a80d110820482071000c0c90b042603014000030301c2c003040510b100200280481665104d44104142801c0409408a202d411009201ca01514070081c0e030420fa0103000d86483c88001d15139103d00c00c0040c0003d1154010300031624203c2ca41d2000c000c05948203039005004180040c01954642510800052295420320081c03a000c45503149007a00c9410507901c1841405c1d0090049000783d004100500c015074550b104a9402002460031446507552440c0c11005004109 = true := by decide +kernel

theorem cover : BRFrame.Cov 583633093 583812949 := by
  have h0 := BRFrame.cov_init 583633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 583633093 ≤ n) (h2 : n < 583812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
