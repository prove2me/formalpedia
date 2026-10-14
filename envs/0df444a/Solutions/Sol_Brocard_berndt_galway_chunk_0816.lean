-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0816
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:57:40.351113+00:00
-- url     : https://prove2.me/submissions/a7282b34-c0cb-45c4-9225-6d214c01bf7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 146582733 ≤ n < 146762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 146583983 1250 146582733 146582767
    0x10314070e0103080910020703021f0e030d081f090c03050603010f060e0a2708070302151b0c0f120301060306080c0f061e0a031d0a020901090e190602 66
    0x1c03030051050318841d85580c80c2c14a06015080c0350710f0180c0d1018856070b2a03644248181c0001d035900410819485c040c203a03101020044c007210110204017540c007100e0340b80c81d00140000403e0792585d100c00456565401d00e14648030307100b200781c044890545003c0307107154080c0034407032003103d0300d5a000503e07282100c101800e59028480d400b034503502e04038041c004401c0d80c40070194071492064000c2001c928000c6c80b0383e41c008039041e1540d48103108060541c00c200c1c540008010960084e806c0b141031a07200342400190040582d820b06800b8a101294103280e00134801410041901d20140c814441d0702c03108450801c46d00b5110314046d96000001882440d415102d40000703004440000d105104501d070200303151881119a103881054081120011541c20005040c00542190303011398031544d0b09603000c2d016248034000e00228090701400030f01031034800102040c20701d4009140d40101d901e8841400d000380604102007525016007000000500034081c80911258403440e00160340f0480390002030700074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 146585233 1250 146583983 146583989
    0x10c080123011202030f04060624051303050a0f020a0509090a0b191a0108072303060d020a03050601031e050d0e0105040f08030405031519020c0c0d030c0c0506160f050f0601031407 79
    0x10320400352032002020460300b03100302a01c3d07150812580c0d070300706968041203501c47c37540020228841c0c0c6e207900040018140301200b0035403081d01d844014540b603508000d400c00c012100151a41d1090024038049420b072140c0a82011034a1140081c01d007000c64114140e80c000354140340388525800d003510107942c0c4242032075801803451030041d010000a442c0e50524111032802c90b2401c20022011604556131500050800b5034020440d8000710fa59150150b102c8109202c15070301c1c044013880201d00c4422030080c40034991303030100242510307400b8043e0030344681e801104120b04001d02400301094a00c00200000e02034080c60005684840ca0300007090b10741451800c08a40303090302081880929442002541d0610700c503040c006d62104c900424080c90038070300d001e14503400049a54220240340c1c110a0504006004083d054040b07900d903030a0002c18814007003010f01d4400001400d42c085490b10318048101e611034001d4031842c1c0a401c0300c0b54605131007030f0810780d85010040c0034481d05031010403a078401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 146586483 1250 146585233 146585249
    0x130c03020702090a0203090f120403030309050c04020c061008011a1c060c020a1b050319080705060a05010518190f021204110108150d060e01020d0608030c010c080123011202030f040606 81
    0x24034582742300d6075000d402148801028183c0b691070301010000c090040b6000c0640c01361046440c0c1c0011004141d4408081d00c2d00c809140c6541c401096440c2c7c180503c00c011061b0b00c82500030b11205000b40301115101c0840c00c5280002400030100085580c05800785505041d8002c00c03a402842c00c2c031240c045940244480c881d442882c0401641c1c034041f407200d5800340c0c804c00c8012941c1c0c013410401e8030b911440f0b6000708603005550400c4000483c591145042c4c480a680c0c0700040300c5d00c08100158800c6c15a0450940304000000071700f4243c140d00860483d0a1406016043c5030f607100414459001c03d8a08a42065101c0c103103501950b0320030001c603840503600700006020502e00010072980b0032040006006142c495490800c000c0094040300c0070a5050302040010b00da4460310b650300c0360007500c03641c011035003000d0394445210710910a20b4140c811001c91103030000280701c11202891006070001c0e05203d56009141c0713018036184042c61044281c0c071440c2001c0e18051401c44122412a085100d0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 146587733 1250 146586483 146586493
    0x708010b0a0e0411060307120203101a030915060f0402041409060901060804060225030903031202090f190f03140d0306030515040c0b160c050102030405130c03020702090a0203090f 79
    0x701168140e580380c080310740d045c0d03070555607038030b42101c201e0b04491049407820f441c81c000410301c01c0c0710801c010a042164415090380b4040100566000e80911050750502c040e07510100b03944460a00d03030100d02d41c00080040c96010408480c4000c902681c000c3d40c4038140702e115203100799400b810b01e10985a8000002c6a484c0c0c1d80d581407140140034000041c10103084d065000c210381c02841414226881c0c013070a0100a2841b0a180f4940145444c102c1d000c22000036403240c10940f50031055000f902c240c204001e01a000c42040d4805206000c408201e008108030080140022108428414800594010040e01c001c03822140707801883c1946901c852000c151501c0400c00c0402d40110b90b040100228075141c0807076403118100125011025000b11049410002d4001207003080c41c4015012036200d2030a42d011a40e9940059848e40554818990002c0500d0107800317800b19182d0140b400a20380e41401410f00140350045900b071901141c4010b90141e001042c490840410007401606841105c0284 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 146588983 1250 146587733 146587741
    0x3130f0f090b01141204020f060301060c020603060d061401090e07060903020103020315030d02250e0f040c24020c0d03091512050903090a08060708270708010b0a0e 72
    0x22400104500c1941207031640d840090510360710941c05100311000c1c1c00025038a808803990b41c1c0d00d803100c0c181e50403072254015060780317066810440d040c2c90480d501038a400b1049000c07902400451381c0024051540804000b40c003d0000302144145540690030b4148008150305150032402252840840c040c204d80c00300208120303440c0d0080c29442031320350a10b40940c40c1c1d01c0760030a03800c0301c1390014481d980c54000c2440d12190340394002100c0c2203000d40603591201d40c030b10f1051040c400000b640904064802c070507002031018000c1440d5990017922607000b01f0440b560760400d066650160100c0b002c408043c038809201007950402c0113a05415049071030b02c00d40c40d485c0d030300608181000e116402c3d8001540251100c01c0340246815418203030b50b14014000da14001e010325440f5400024814440c034580d84020500b40c1c000a2600e100c0c10071522510501e8468118001c0442d41c030515075050500d844483c0d0340d034443c00740b2488004024540c00410310164039070401c6444800d9800c0f0b25480c0c01a40c1c100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 146590233 1250 146588983 146588999
    0x20403050a0201230405060d0e0607050d140f010501030c0c0609110108070e090a1a090a1401080f0d031a060c0f0c0f0d020d050111040b04050a120809010809030c070803130f 76
    0x84080b14403c03185142d840948181d8400945103840d10449c86000700c100f0001407a40000080001040050b4108680e400d50300c80d142a001c820745041c200003c03035000510042d4000c2d072101410101c14106552a07400b20780c8c1c2c401c141c60150004540324100715611442550304101142e80102060070040040c9459030007054070f0390001018040029141c010441000c0012400c2d0190140098035045042c540340724118081d00c010301034011460500030001665242c01f28500411000f541d010b841c43d4400d01c1400c07400340c454000071402e6019030720031000d0030740d480710028002600c214010b0710f001d50185c0d0040c0d04180c02030800034081d17102401d00c00450b60b01c441e021f1a8040e4100c40f400c6c05180f00303040c484d004041c50300158280b050001000f0811000b050081d200311101164002002502e40d0b4001e442d110070600020100001880300f440c0d203602802007580c0c0450940200d030f0074005140304a514004880d406550541c0000540300c4100290b9140100641843d440744510320303181c8440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 146591483 1250 146590233 146590237
    0x10206070e181906090e10060303051c0b2214060102070308031015050c0d0203070215070303090b15010915050a0f0306051809060a09170705010b04020403050a020123 73
    0x325040158103540003c40c001d9a0f401c240f042404400390802038107844030709250041900707104842c1d00c0d00c100c0d04400e590103010701a11043c0c0c3e602d80e075035030b042021080400c0749030848400e41461041d25a80d1912054841c55403c0a40c00c0304200c4100b10207042d001c6030b80450340001c0c1408101040c000c1085116600002d000040fa940f11603455030306d54070415a003080a4054000c40302104d8072210207158280c4c0000034052801100055402400f0903500c00d80c0c1e43d214481b402900300d045002e40480c83d2a5100140c05118080c1c00c01041868141c0e032485803005c003c4030b40d05020f0100000c0c80405503881200e04010b40010801c100d000075440801411501581084200308441d110b40780c0b83e0184603810031002480c0140100740d0741d1482c81c0c11041018011a801045407050350005105840c460194449491b08070704250311b0a401509006e410394060102625290b40307030010b805141e00c41c1d100400003140248003420000d0400e2000501200307a901603102c8510440d031000102c5801042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 146592733 1250 146591483 146591509
    0xf160c061b0c170304080703050d0206010f050a1202060705060a020d0b03010b090a0213151d040207030e090907030f0f030806060309030909060d080a1e051c0b01050412030c02010206070e 82
    0x40141c0f428802c034500c5a1035031145810180c5640602c100c000104100000c45400c00403240d0255902d603a00c070194081724544a200720703684281006001c00a04120007030240740075001400c503500d4400b850722190720b402c074140d5208640c16800181891940070510501c1c603440412402448440358050000d946000701400c0c94464a41c0002d403511541c00408130140184100d5113401d0900b854014003a0242802c02900e014040307052500140702c3c9060b05c02c403020654141c0721404280821414841c2c80c00d4010041099071050510100210700d00540a03950b075841092540e00032003941c270f00208080c0e009132015010351380510601c04000000f0068801d0300400ba80ca80030705658203c001820500088405403000400003000e480860b40034601590b0465081317200b25810106d0340c001c0f180d6110303043c0d010700c1110301c0c0c0061b90762140d010740150104000514042d401c2c151100d45400328691042c40480200e040c4080d14011560140f00040d40710000e401c01421030010640841d10314204e5507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 146593983 1250 146592733 146592749
    0x90503090906060c0609030d050a05010e0703092406031506030c15030f1109010e1c080306032508010b01032903121b06060306100b0f160c061b0c 64
    0x8000038406031116804e84000000300e50031200e032800c00c440f04a45aa1001c1607110f001428000080c5813021117025480c12660b0700c44140045956031081180100100310701162a51009003160400c1d81d40d40700903040800c0c040500203040307407071854020401e8401c550341d5032400d820300301d01704007059154030080c04542c00c0d00d0302030140050000c070840c024a8414100600d05140450208a400d07814010700b80001081e2690310b085108042000340e00b145d42d14006407c0300c10b209d0078600003201d03d03028540116014003100c421040d0041490142c51060070b5841081d03001640810000c1c100b4001e881d50305200382800c100042c001c20040c11455411000300740ca01c00442446020380c2c80801900c1c0403117400150715601c0e848840b6414000b640c00e411844810320034080070900c80e2901040c202e02803040c4840988481e0320b0025086119040300c26074031042c40c41444880f00c031030011078500707858910510205101508140b00500b070190031540809008031340400503c0015801e00e0140141c0b1429 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 146595233 1250 146593983 146593999
    0xa080d020705011422080606010c021e1903060203040b0106030c14090117010906050406061e1b121e0201090c030605060a0b0c01021b06090d120905010213030201090909050309 77
    0x1c0e01413600301d01c2281d500b581c455507002e8940c0f84945450640c0400d45122005540030f40e1140c0004603810181c41001075801090000800000301e020503014140b020f01600315150401c0441e4050b641001d240d01c142d54440c0c0000070002000724062040d4003520035420204100c40f407048000f04441207280390700010b40c01c0044d075050180e01030980114083d00411281c00c0541e100d21080340605120b1040c1030043c1d0a0000c0450130a004e4021000585001c016a0a44240c3c44104031103010040c1400c4445000521a11380803680e40c81d801d0440300600c1e15490302d000d02065014074035400c00710b2454116490659240e0000c0c03115060342c022290031600109541d150b24000036611040e83d804070303c4040000421110001c0107401800c081020740e1000e40c4190461240c7c2503c032003048616181d16003104150707000b07940c010850314140b14081040018219841d135079003402ca078020100703183c680b03000820400071507901415079000303402d00450621200300781c0c1e90383c40d82d44d00441c3c0b030b40346c895141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 146596483 1250 146595233 146595257
    0x607030e03011a1e0f0d030e0d030c030f090e04060b060d0c0c02040609060b0d0903030207060f0e0d030e150414010528051006110a0209010f050a080d02070501 70
    0x225251440322014000e008010003074103080310304003842d04a405540110041250301403010f0320489030444000024011620031400f070000c03c210192088011005d201e0b001c0115411902e550a1803683d151117921841103210b564100034000c0a0002020420041d09490601c00c0b04000c0a82d40d0304680d01c0140442c1650300c081c00220203000321110380ca5400d03e1b1602c3d10060645c8803488054040c0240c60800440b91980041c40030749000d030140705502030082283c100350300c0156000b895254003a16005003403003180c5d40c904054840c540100b1002a8a0b1403001c50b01000074002491a0303002e074107003005031000c508512501c90308841c2000320703a244448006028003400218144034401010f0081203a4500841c84e54503030072131607510040c000f00005191a8078020b42c03294600502a0f02c4001c020f042c5040300032260200b10442c0740c2044c0c0030304401d010040c3c484141280c003824640101c074207024281420321811040d241d00c80f50069010f1070040c0503241d004148403094403000e1800440c4059 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 146597733 1250 146596483 146596487
    0x60503070612020304061b20061b0c03070605010f0e090606131a06120106080703141b0d0903030b040b09010f140105040b13140f0a06050903010603020307091b080f010302060703 78
    0x11030080150040390f441d03120165503c9031410061f400c1c5e01d41d4081c0c4040d108480180e86010440d0380c480f100002b05065007146500030003511103598a001203034030303044890382d45000307407042a40507000303100c1079001c1030103030078440702500e40d004240c00700501c55480d103200020f6502c80840304100c03a0b15500e404080e0501700341010b443d246040030700ac0541e0b841900e40d030800c0321003092180100190925000c5080d0f00c1c4240140303840781e051540c401425031202000e00080649030003096150b40010000509c4045460080101c03c6000303440000d5511081418001a41c802c1c0403118454004040144041c40000421f1000c2d80e60348011002c1240354400161034621070f94021010780a0007190350118441540405401e07210352a0211000710020410300044020202e6104e510594000080c01143c0c412006082d40f000001c0c00070800d01d5882d0003003428441310760040240c482d154820000201d0005509109051483c42d105d035191a046410342d2001c803041c08003e110710320000312282418 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 146598983 1250 146597733 146597741
    0xe04090b0114040b0904050307020a120507060f1b050c030606151e0c0a05060412091401030b06270916090b180915030f0309010207052103030103080d06050307061202030406 76
    0x40090817080240c181401c0003942c0390032040c0d089102e030000703a1011a04c00001c14a40901d594800c005108144c1000c4054030b4400710f0f07001000c20483e0100201510b0030041d200031099a000300c0141c00c2091103501494104013004040300d00580d217000c0c0030007143d030b4980100c80c1c01108031210030ba400d0010f02200780b414071400c514403001d40300c0e961078401401004509640101e214035821840b0700342035141610410100e1040355a00c00404030b5403142035010b900403407111075000309804d107001103c20314040d502040400341c6510b940c240160110038101518580c1d00000b044010140440640768010a6201c03907010b04d10340c1c3c14022a120982209a8040c1524054000d000381528034128403d840103e01600d030b90761081c8240403070148407e2020040760101c58041c0d0141488604203410302c02c9996440692034401024001d241802c0d00c01440a140a548a0780d001c44d40c402070f01251505540d682d8000520941140100b0803c443d00030132881683c4000050140c0c0b2903442c1d0400c24024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 146600233 1250 146598983 146599001
    0x4020d02060c0709060e0c070b09070906060f020c03010e121e1c050f070915020f102a0801120510090302010b010207080712080f0408011b0e04090b011404 68
    0x56008a600020705802040100076580c001c0030800c01c45d030344c0f4101c0f0112100f0555144015060030480d40001c508441c51190b0311503410b10032900e182d56103204910480b43e16074000000101c4d9915115409641403094000c0c050080b4003d0024040c00c1060365140e01421804400002001501d00d500c005030b41090710610146000d0544c0380c20301030420f8000070004206007020203240c400000d20405150030041c2c040d0b030b42507480464481c2812a1100303030310310300c90b481c0e001c0d841004201c90078405c00300440c44c1c4001b1000008100035a8030480c64030001e210405006101e040181c01d80002e03607111114030b044803029000c0f9940b001a50405a08001c0400c0405800e9801c10b400300d01403540541102f07400220aa085860441e030720386220ba2500014041e0020541080403142c01080001001d4140b0304243c013081403600f0f99440030942107c0700f051420310b81c0c80d81c2d078420605494101c036034000c1c900003c1d10240628042d581d1428404603050041c1c0301c0d882055403080c0684d4071154818420703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 146601483 1250 146600233 146600239
    0xe09010e06190909150e1f111b0601120b0f040c030615050f0a03020a450c08010605190201060902072006160807061b03150501020c061204020d02 64
    0x14940b5a200ca8000e05482d4034180c8106108065414410045100c3c6c0d0ba1810558000707016900c2d00c940110b150f0040c40d40101304c15944960004c0c0386503003410000d0980140000300520030588200c1b807681003400503030103118801c40b80c003015070204140081481c0d0100b07060803096070541c0c03103141c0140c0403121500003a002034a00344585602d134135101c00140584a04440d112811140c502c201f103074402c11030100035004100d4690800580940c800c0c81300d1440c1407007031982620010201c00703051a1000200800881003140b1120420b90a079201c0c01d08840c01e1481e02c10b1181d03052040207070240c030a40c9045108a101c10f10218a12407007175000c10040c10440c64199510300b52401c00d80201e6220010a10f02d070009a08000ba0ba0700e4404112684012000e459450708501a12160f0150300b000100b40d03440c50b2100f40c1400c03003215030100115803401d40d44000940b100c40080550700141c29802c12815035006100300d00d01560f0345010344071200c20100b05c40c41c031991144041424030980c884000c0d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 146602733 1250 146601483 146601529
    0x420030a150b0301110405010912080702100203030a230403050a090305010f0903020f0c030606090c0904052d040203031c0f050103210503010b160f050a0302030306100e09010e06 78
    0x100039040307608601510034044001740a0400180c10ba03440502c40c620a40740440e80410302000381039040b40f0700240c001d0103400140e00740802c80e00400d0b64091075410b80360068200004200c1c0101481c410645100d40782508032004200300561041000f1000e0005000d0041c04035021125034400c80300c00020b940e2103002484086c2343c0d15a100c0182824000440150203221200300a8010010b4410b040400050003080503484031170a008c00b0f140c000e40148001e810401a500c3c55440d14010302e4010040d01c1d00107134644040c1c059650784401c9a21900400740954024400075075000400c1c1c4a0806000a906c2001c0700600d8001d4010048907034041500b6041c13000000500c40d200505400d00010140f940d00340c001d100304204c03403d100c00d0282a000543c06e025071040341c0c010001c1040010b10a0011559500694071414905480004220016480041044101d0411622081d4840640e00340f81c11211030b5000010401101401801c040740007110014a140e0742c1d84854201800c10310342441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 146603983 1250 146602733 146602763
    0x6090409060e0c1003110d092306061806130b010c020901030b07020105100602030a03090309050d060b041802011202091903080301140d0201050901210e070305070602060420030a 78
    0x140c0c481070f00489280c4103842003200202d80c0c81c044d0285070394804000da400c40c07505100809603001441c0074181520141b44451001900c054159a02c0c01c08201c00c5008001514200007009030700704e982069001890225014490b40740c84008002c50707110200400410300140d20001200e401e81d00d500301a501c442c0c61400042030281002150380540c919034002c1c0210340d030700f600c8a141c1d0140c81c4500e900580c400c0100c0c1b030035a0320a80c80b4030000da101e840c00c590600d51f20345c0090550f591540040c1c581540d0f442d985c046c50324051083e0800064241c0d140b0390303c4481900041d08050881032043c034500d0b0005003280e180d5036001411080c2140444010704400c0d16030410380c8031a0400d0003a071114044900d9100341038680100201419a4165a03540c40c0503807400c0112110000034408442034481c03c0314924014003180101d008410300d10b00148062840c40c28102c1c54a50035038422015900031400340004100700300c1050314031400045040540c1405032020030325110100c2401380447c00502d80d20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 146605233 1250 146603983 146604011
    0x15040609090510150e060d06020315040b0307050a0b0d1b08150a05060910180803070b010b0f03041e05030a0804050c010f020d230f03040213020301080307020609040906 74
    0x300c24403900582c201d45400d02542c4255003150301c0b2500ca521400d20742c0e00200a001035845d0102d5212030090850203d0701859640c0405a0b041070319600b840c0982e8036481c1e003103070400b031140121014040f00181003c0d072801d40442c15468180c0113a0740f150340c000840c1440d01c072160308900c1c524080c0c2e65180002140c080b0f002801c102c001e030780010943c07410100d260b5803890008142c2c01034540050a680c40d05140c64100703c00001c81441480a00003624840f200001040f01808001d001d01c9001d580d980c202031502c942d0000058010020520b018032042030400041d0056075801039110b01440341350580701c010460480942d410040c124800000d0750b00307015074007545160184e84a1000c8401c0781400c0760040d25115505540f50380147e11812400300002d1180e0300b00051f0300b2848688085000240e501200300c0e5006180c1c601c1d078600004144011810401081e07074141056083c114159414070400c40c0e241c2c4504c46010380315100220752000c441e541ca0f0302224100c0e620800c1001007038210010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 146606483 1250 146605233 146605241
    0x206041502040f0b22080f0d02010e0c01050702030a06050c040302090106020c0f040b012d0905030708070b0304082101140103090b040f0507030506070806130b0303070b15040609 78
    0xc548000e80105140c0c500c9515000340c81c241c40940c0000b8034250705044807404a034010381040c500d404c0d6801d503403105202c0044441400361441d4000341030071078400014a4649002c84000d17808681c9811004a03401001047c588a540000d03c0e1041d6118040d00009213420f0328040040d01d110f1030003007400b14035200c1070014030842e0f1080e154407a0981c1d807000e082c0c0c0c48900c000002c03900114010116a52450141e0000320700c0601414484088444244480001b01040c002082e1052a0390324200100350445c0b100d07001040c00301c001307100850030071a44585401c1c4a00c280c51607108040702181c10000d5000954541300d04103414000300065174038100b9002d07282840341c0f141800420038405c80c294400e020301c0d8480c6420412140e5140c446540b404c4030344200040684140c0600300d000302c000b80341407015074025070055960300090b044c1b9904104441d40002c050b15861494031107404000d48000c0150794200e50055140d5900d44d80b080581c103a01c1c05944600340d4442d1400501240d045640e41c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 146607733 1250 146606483 146606491
    0x1c14030c010506010e01080105130f0609090609060e010c140a0e09070e040f1802150c01020a0810050105090d063b01052212050702040911091609050f1f0206 69
    0xa1002405c0c81c00c000107682480d000c0c010240c201600350b0001e841140560052140324943c00000900d00c0d0b40c1d1000030040380c441090460b6a19280c01c0f0b0f10302440141c1c000c0c0a03541e00b440b8000c0140745840b607000342c0f1013610984110103e240201e44241500d00a07000039030440c002070910480d5240828004150060340800c80707100702e15280c2400c0b004500351107100c0c10303010181c1c0d4200c24000c0c15002c1010140c0200d90050401c501048041c05000f02070014001d8030220307490711100c40c04c2c916201103055045410150401c5003c2c45204900d035250f0b60201801030300200d0004154201c0c854001041d050a10041e40c407425180ea451200d44100d80c40c41c441443c0705008000a8562515009031000c0d030009561103c9030040b414004034003640148012148182081ca280080960205040d80c09070300d016181c04038000303170f18800c5040c00d114003584807840780c03010700d000065200c001d45034030160300445003c5c2d91100d0441500c5d854581000c01c120341c2103c50038008142c0000e000b0358a10080b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 146608983 1250 146607733 146607737
    0x611030108060a0c2106080106090b10030b09161e0807140c0709050c12160f0807020604060b0d06050916170606061e0a021513021c14030c01050601 65
    0x3400900c040d003042c0320703000c80d0610f1542d415440170100c0d00c013600c6203100e0030105114190388032000602e00c0001d1240b54010b2645c034001060f407103070070420450303d440c0007140d031000d040c10310082c0c507920b40d0b0301d5030301c00e0784243e515120780d1403110144021510b601940d04046c0907040704c50202c0201d070b6000041180300b001c2540d21190000d40200d2020058054400c04910951096074284080c14980c3c01982d40300b042c482017141014020900da4541e44410307680c51041c04040e1505500b15a44065503000280d40d504100441d4108200300035a100350003000070b81560340d10102c2d0160b596541d00071030316050b0042d8040c0b00b02e0905820300d0ba1512001581c82c5588100315100060322404038031034105c21481c0c031020348030942e2031074103129030741e8003008441c00c154120f070307036550142c41c103110107003085036907682c01440f12000300e010102c034665020705901800580c000c45240180d44124000220400c1e56034480050442c41c5031501c6100c0380002d22a605000100305100201015400544280000d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 146610233 1250 146608983 146608993
    0x30c161b050d020a1703160303060303090b1c0903020c030f03030105040e060c040b1e04080c0406051504061b051504030807031116020307170703060501051206060d050a0611030108 79
    0x41c60800c0355807140020000c0d0482c060300c10410400b0303e060180885544240203491400e455014101c0c503881590786c04402080e9030301428420b02d5440384980c03019150405c2c3c030b14944445002080c03a04001c00c1e1201c882c0d540c03500c01c0001014030a00440b120898040d04682c3c010115880541d206c1d0000d0052038040da1910365100f46042c0001801030180a16003580b91529091804005a82d40000030042a54141c2d0030305100110408000348010070101d0301030801406194108005d80d082540020700c0341200c420b04042c0e410003081154215031907402e19802190030310422482c001401c0c400a8a180900a01c0194134884c8080e400d1082c1e12035a50825283d81703602c0140c0803603000d051120114241803000d1503800100c09000c0c0603140c0010200c840a50b40d5502e13141141c02ca40920340440c0e00929030070410014030340116405800c045403e01850f20040e001160f940e540189802d2190043c1a00082441001d001c40103040742c00030001c0c052005a807103000401d510a01c185980d9200d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 146611483 1250 146610233 146610239
    0x609022a01090305070f0311100501030b0906061005070606050402030423061312050c060702011d120901050a051c090b0702031801050d0e0f06100b03011406030c161b 73
    0x10b1250b000b002c0c2d4140c481074100705150305d07a0350007100791322000c50034001002e0700c04100032000c0007050207402d0f01d02c001194560462a0102500c0805040c215003a4004011b008050b950800c1c041e122050920f0134a0702c4003014200070000d807182d40d0145070014800802d00050021004a140441540101c00c00345000d00e06010350783c4000071200c0542200954640c040060401034004003511024601603040081b09541a0b05000054440b0000f41c2c0d9a03e50507041c0c2046030307003180b080080907800b030300f0090116014025a440b4410b040c030f040000003c0e504c480742c0d000c1c2c01501c070300f842d815202d0043c80e540101c1c1c050050054513815070b0040048000906290b200100300d41c0031280c9c625000c0391180220006541d1500080d0400d14039070380b51100c100760400100040798013110460000d2900703003005001605415000c0c0c0000d08480e4080005000b01d12031684004485501640e04903aa40d403880301c0d03110240611020300760812802c42010050140c400d4950f920343c00d01d10f0113039280c566 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 146612733 1250 146611483 146611567
    0x1002040f0503010b0108011a070204020919080609030703080c0a02120c0115050406080a110f040c0306140405010602190f0c060c031223060a120c0e0109020306130e01060902 76
    0x1000d100c0e400c08c0901c15100502d0f286c078010081c04000c0c3c4050000350070010a0400651015151100080380e20880801080305040c20030a044e0414080c0d009585411000d440041c540d80004115134240c18000400b8808544200300000c00040f480a100e500c42a0340d2103041d000e801001468240000030481c0451140340c144504000c41d00b00c003000740000034242c2d5502650718081440140e20038040903080205854902131030075598031640d0002203060800e1103456508050f0003200740580d2604005000e119000940320a04c00010004078100b25401e182280150092001c0204a2500c51310300240003034020f00400c11451180d10b41d2510b100f040c100d00801c4800303084205241c0294a041c401000d0000340b1725a40050000c3c000071001900c0d610503822000300d1030303c1142c141c000708004204040d070403000240902a00e040a5103542070181c00520071004078071a40d00307d59035409885200a000354881e2004140414055482d59800900780e00850780e00e010780b01c0110403461031030310030b0740b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 146613983 1250 146612733 146612747
    0xb031801060f0f0501030b0d06051e0a0506010804031409030703080301080d0c0512070c05040c0804050f0607021509010906060602070503010f0204080706050922051015020a080c1002040f0503010b01 87
    0x30249003803100d41504d0000118007428441e241d10342c0004071203030302c8070100c0d0740b0340a414403540e1804440410140b83d0800d29070f8424004189011180c03901c014450113a9100340d00740e803c550940b030603480803c40c54207038103146d00c280b091450303052045440002c10094040080d604945034001500e10101003418156983e01080f0700042ca01d8100030195401c018405018101c3c01d8099900ca01c0051344a030081811a40c402c00101c1c049641030003004200030081180c90000204000a4500ca003030410029540714141d400c111182509200091521002507015922964100c0014400c2d150741c0c0402079200c020342c1c09094041e500b4500c040e60a80c52034003c40c0c0c200c416200003001c580e803800c0d4046a06030424083d00c0e0b4019001204101d0b450050302809203410445080020581440354140c0c41a4020703520000a1440310242d41c0f68058022884003c00c54112000aa0b101140e1204a00b417014030f481001c40c0d10305c0400c0c04240640b525502c4401e41d00298001c10010309170b0710042d1040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 146615233 1250 146613983 146613989
    0x603050108030703090611030c120717070b010909031407120801080f21120c0904051b03070305060301150612060915030305090102010b10050705060a0501051e03070b031801060f 78
    0x85045d0aa003000568411900420101a488192070425054540740e60800100d41031202000c040490044103024400b40380380680d40c00d0324800c62134150b5603030b19030042030700512910005c0b956602c9c07100103150003544148407030b260040040755540b0f540d00d04280c03044100e070079030800542d40b0b41c00440d1066000890f1006107072068028030080b11030098101080234950030405c15103074240300c03480307046640001641c00351052850698956008109001c11100c00a100510b00c429120900e100345a044d41240c1d0031050914002c20141d483c600801d0261150445030490001d00b0303a0300081e41d507442401915042d509480078851566110b02241c04c0e101a4000d001340c0e00040d800070030000c0c0c012002000d00304010b000100e031940b8001c2c002100e00d02e0729034007040030400005001c2c0070004203020103a40900f401c9801c02440d41400081214225448a07000c00c151240001d503034195010814140185181c44255542e460f0241c00c0b9540c82420202a140725800d00e1000300c4c40d000c6000c050010f07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 146616483 1250 146615233 146615237
    0x9121101090314161406070f020307030804030b090d05041a070c0315020a12051522051501121a040b0406030c081c0f020c01031d160609080c090a05100e0f010603050108030703 77
    0x401f80b054880301c8403140b85a1040381c0c1485980300000009046402401c011405002444128909038400c1030900c003040b4500300070814100014400f10b0b1140c81110784e1030b01c0c02e41c503540e1905c04a250480380c41826402c0909802030280c2400c043d0419a0000d06547d51207543d65071940a404420b0010340b9019038904032210542d40211740c00c0e0400005112208403190315081110500e2092201140c9094405050a00940c0c01040d20343d60406010185425140010031141d502148407200d0040c683d000701c0c2c0325541320340c42251303c2d5803240c009001964010300069021a51904020754403200c490407800740e4000078903114036007030140c07505002030120f40c0c000d010282c0503040110010030240b00001ea03070007244d2402e0502004208240e0540318108100541c101d820400f0181c850340321940f0807005e80c1d001903a400d82540300c418046800002107600401c8903112109a0050b42d6076a8201402c3c4400b2582002040b41d00b8008181c103c0f801a1001c01599803910540d41e281e10a8204c0900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 146617733 1250 146616483 146616487
    0x320031303120c200f010813030c2307150c05060a050a0905061014090717070c06090f030306090e0715020712060212180a1401060b0406021b0109121101090314161406 73
    0x202190141c0d80e05ea00701744c0b003450788200d00c0c9220b030bc0175101510006030306001c5500c01501030284101da1070010000c00003a00b0a410b01c903600da60350320341c3d60000030400700c6125141e001090019649030041c0400590001c00d803184c501d01140542030080721340c864054103510b01940b503001d42c1004005907004207119600c0c3c80400807640c0d2003082104c00505a24108005020b0070303c0801c240744110158140310b030b625001901d6640c100207054666580110008520f854202c405860001030108201c480300c40380a00040b0041d04c041e824400158030240c82c10981104c844104149a03005002d503256904e0b4007040c0392254140003011110441e118860799000e01d017003070089a083c0746844441543c3c0340003c542c10352580c1182d02250403607071094000d1303484502078848122610290681c5100207103420a840c9141c154089516070440c2c0c0054985c003d40500d003403880c0d02c80d0f803081c0d02031a0492020013554101c5011070381e9409130f00710054807800810070041883c80d84503089103c4c111780244418 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 146618983 1250 146617733 146617771
    0x210c031213140108070804080d020408060f071d280b03010f0f231f020c010206010905060901060809010e0d091503050c040b0f07050a0320031303120c200f0108 70
    0x150300946c000e08107840d80b60042c004c0c140c00500c50300003000600404005010a0705000c1541c16074401c0c0a1702800510800d0240c4005048085114061002c0300316110a00c0004410003c1079000120300705401c848154400450682100b000650490b9001008072040303a50b80d5586100380b031401d008520320200c40f003d015003060b280f1b4160051b15400105440100d03c3c0c00c02c1140c0381d4041c05100308003d0381002251103455030301400800c0c01416609424042480c0c9503000035440b1b001401140c06000005011a02040b0700350f110b01c0c00745410008075038440346850703006400301c1c50b141b00e00c02401c94414070107502544240182030103030b20002001424603090182d00002a041440c3ca0521000b0500021020030000c000c41e11025010303445080c6c1030350b0556540d43c0c204554142c020b601d503000704114000785107491001000c8981240d06020301c61001042100c00e60241400a42021082000e01001c0c003940c401030f80b0075140488220701d00115003070066984001c200c800b010031038203800c411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 146620233 1250 146618983 146618987
    0x5010303121e050601030f05040309060912050604030804031704031707051303020f010c0512030108070f030f02010e040b0d0b0f070c020328020a0806060a1202210c03121314010807 79
    0x107a4104d1014107010510886400d84001194000c4030164005002d00304c0c00c114490b040034011001d4099101c8800c101840d507100c290781c1d91030140c001400c100c0c8140000e414036109440c0e14944a03109000c1b00c078181028100240750032403070300307007200c1c10305601000ca07e07a9030065007101d2074065450b045208582c510340030404410b51803107001d41485a0705451000262003800f0b100300f4400080405c43c0c480d41000910f0b45410142d0304043d0011003d02c0042c80420203519040d218a942442c00c84003000c440d101140c0039003081c143d101d800070aa1000c82c8100103190713009074400d140103041e410441d92004803c44010441060280d0150003c1d01d00e02a4209611100625180c0c00900b102845513a41d0202d0301e507003100d0b486003a0355040320b03060100c1482c3c04920480141102c0c0100c1d4000c0650b41c00141c030a401c2003603034003070314420103044140c0c1c1042404954000000103003078a849041e2880c940e1495030003040e0340070301c5580c82203000c55502030f070b0100c0002108042e0f54696a46d0740d07107402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 146621483 1250 146620233 146620241
    0x30b030d0c0501020d020409050a0e07030203100203041b030b090d08070f0c211106090109020117100504021306081303020d051c15030501051b0307030b0d0c0905010303121e 76
    0x1a141d40d50200305d408048101400104000c03c445400050903160103200305040b55850300e1300c603166400c182002c001594001600c1c0903401410400107a5a0b00c46150035600c00840302102d80800719212400400d00241003204c80c801da01e8070041d5054002d0861040b240040100e55102c04143c1050201034540d220b00900e8000c18400c420b144035a1000022106d410411581d02000080784120701083c103400a20a0342d42140c00007009004500040e400644050b80b05865600380082c5c24002030b8040500c00d0b80e90000b4000508115a14000e1b0501c0984841c0d0600030000030601c10408030391000d91200350180400c2d01039000d0a588140144d0840d4a507014120301500d002401c2101044984030340300b10340d46404d44141c550f404515500e40039080d1030000308004c540c4040c0e040030170214110501265840402854005140c50400000400000382100060064000380f50082608150b035403115050b00c0c0241c81d03070007003d40a001c00a05840da41514001c1c0103080c040c603a0800390b11504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 146622733 1250 146621483 146621507
    0x1005093c01080c1c050114120d0e010c0f060501140f06070807020607020a080609030304030e120706080c040e04050a0203010b030307050a120e100e0901060201060602062205060a0f0507030b030d 85
    0x3c1303003c0c08608491111000d440d42a0004030346082000c16450061401144149a0440103006461648016034025164a55a078000ca05010402014500304011190310040007a40729804001e00e5841d9080c02c280325080d541c5941c021400108040e00ba8581481036404055026035200d00d081c0065003840415041128220b0700640070b413001051030311091220510038000600103603101e1a080c1801001040e0000409004581901c91584c0d0006d02040c1081941c1c41e03410801030540714100601036501c550362121041a19a6050000300140410000c035294004c034001e00c98803c002082640768485d20300001c01903840b880c0c01c480000c3d0241464419400c0d503081003c811858079010440d2820400e0188000030703501220f4603003c0c603020700b0703140c05422144001c010141c00c1010181d51005c000d02429040100012801c0e20107041c0340080c50302d41d50200030307521b25040088411000d004000b0054a032039040c40c0018020b5480b03807098a0700d00c140100101039101900e442036541c0c001d841 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 146623983 1250 146622733 146622757
    0x1030f0206040b031f0611210c030c0102090f030105010e0a0f140a0509010c090518060a09230a09020f010f140313031205070504051005093c01080c 65
    0x404009001140700f005140724540c241c01c00350350342ca003c98150030540400e8005805020140384169801c0c0d0000546131114001d856010665000b269010601400f80c018415004d100001d88603204c11f0064002e0302203d1400d40300d140c1e171a9074600c100360070b9501c24020340441c000e40320009402c07181503030002040c444c0c4a881c00103010318003502c10220702c90100c4000a2094a079020302030000000d108400700c140e22454903280d41c5003800c0006290a02e60b00c60b00c01c41c9000d000100c1c00c01d076103182c0c010000703000c030300c50420511007480440008480c40c0f0f45003a04040c1c005000400d104818068250890b40c01070040e4281f0000320f0054694803006114001002103201044004110364801140260304c10701d01ca030282415841c001341241094443d102c01c00b424030041c80050380d0000c05440c213035901128003040002c400711080310030740902207045030b011442c000340c191200c90f66281140c401c61916101d0703a1028600b240303070500d40d00c406081c2e400201003c5c001080410201c02512000d4240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 146625233 1250 146623983 146623987
    0x7080c16080313110904030806061803101b02010203040c090507020c120106051005090a1203180308040f1203090b0a20010605041b0c0b04140d020c010e1801030f0206 73
    0x19407605441c0782c104440c0308a1800c0014524014042500e41110524804070381c241040d24040c3e030010b000c0d800182540c0e0080d071011503031440e803568002011500500c081c0c1100c0a0000407a0f07103001520341d5440c11008071404414000c42c89106000312480f441d00030b00c400c0c500078581744000c0c1c02090007e04100031409400105800caa40d0028030000d104803141c00454600c0c103060401c685448003070000d1007440010044001c050300d0388400e240865184c0b040c0072000c0900c0341003e0b01c50454400c0d0500450411480210401c10340c90050426514400108401c0030b80707908000100703502085024000c100e01c0c100401855002c0030081c85a210185080310340c10501c0101c070300154a00000090059440d1001800241001d1040040e40d2086078805140030407010f00283c00d070b0552840140901a151001505000c242d090410328040b801045594403445064006c0d281c42010750f02ca40010302c0d0030407080c19803500e03041c00b05e0041d2100c0802c07420b0741d1840e6107032040390f8a8000d0403a000313001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 146626483 1250 146625233 146625277
    0x70e37080a03030b030c01030b0f0603090c10020f0c0603010e0f0603210715020f07260d1401080607020d030e010b10090306060e010e04150608071701060e07080c 71
    0x1e01003100c40e248a0386020511060342e0b01054100500e210030345040500d00905070344696120148050ba90005641c41c550705c1e15090080c6041c503003407038041c50300001200006c1c07004950000d0310180c200c12580c140c038200e2100000300001c0348020b11612001c0161240428044034141040a4004100500b16075025210320240d8400b605240f403164030440001c05c80341e041c080600d40c03140540985030070031071803c2c0c002c0e995001180902c200260180c203074110501e206000039090f1494220fa005075458507503056444004c050f02c08800104e00d07444480c000081c284600140303040c024100790b0041c01d19900d16610450050040c000e440401c0e6407186d03202e1805845810008820000c16030318200c0081c11420990150b4410b9841086000c02c010010004007045440443e00a68000c2c03003981d2550354084803801401d0f154200c202c841c010032200066104e001849101031391070040c002d0004035a03860384003026000450348030010800480014883c0f5295800803c1c01c481003a00d40170310b90740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 146627733 1250 146626483 146626499
    0x6021f0b0a03021f030f05090706051602180403031b050a0e030703171201141e060c06071e08130206030402060409020316090e1003080c07030b0f070e37 67
    0xc2404107816102030140c40301810540c11b01402c2c9003034202d1601030180e4100000455030340c0748188601010000f000c1100d0500100381940745944c00d8005184038120040940c546007408030076038046000c0380c034088100626590810412000801d15212070781044603080c4165010040c0610240d80340c01002d402100061240e10681e0030444642d00c915201e0342c0140360021040720680156074110108540d41445c0e1b52112940034013442000780303407208001c410000c250b00d40140c99503610a8000c030f40c2000b10382030b400303402a400804c280741e4042240543d40010380744c000098a94081d403c0c00c224420026040c500001d5400a1003d80401d10b0555076445980407070708107942e1100c0c800c501080240d41564080da103c03018040c5850381d04001e0606000b400101c0b141031000500c0940c0200305c1b40c003410000d110020080d90002441c14413840c120082100c80102250840042950105101c5150810351141108440703107411000075403c2048030795015041c8104c1c4000031590b207000228000c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 146628983 1250 146627733 146627749
    0x613050405090a02030607140708090f0d14010506010c02130903020c060403030f0905061809070909060303270602060109050a0f0905060403080a0219050c0106030501061e06021f0b0a0302 82
    0xb0404802070842c040c2c05104250a02c5406030481d410408150940040b910004048400903684041410b5441d01d5480201d950103a82c85080c0794048190440b0109014003101c403840c0c0050104000c002c039594010040d00c039030000d050041e41000c5034201c15070104056a01030812603000303004542d01a4005e800040382a401600201c0002d51000407646980750072551030006080d0444070319040004520303d40720366078500e001c0c4912440000d40811089809044201c02a1565000910007142c9030708010f40350802c50a1090703401802074040c0c0d85040418104c07401600e01d036038003502040c1d181281c044043c1001401000c0c100c1d0f0345052411945c1c1c40e61181c40c403000d206201a240d14039181c1800362039118000d02100b442c03030041101003118907140c1c00c01025002e2a052164139500e5580314540100100e400040032036180400104034a03004110f400043c010007880540c40790380f110402ca8645003c012030050122241903101c50a00b01600440104032019110840302a5290001003102c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 146630233 1250 146628983 146628991
    0x5030618010305150c120a0b0f0a06020d0908070501170417070f120c030212160b0108070513060f0614211e04080304030c1a04060605090a14060613050405 68
    0x44e90000402d8010300c89129034090384080040b880300c1c00d1071001351016500d8480100300d024040d680e070b4000203c0d0342d5503a4441e4142100608900180780d180c4c60702035651031034103404c003010500001c0000348a2100044950603114107a40780410354064241110400c180988220b13043d014800b00307122803d46650117800883e02074840c14a148134241400d000301210b0040040404c0902040940400d13000140c907040c10f4160035205990b11241300203501110303000070700242036410310741c000114544e0000e465001e54404990140f044464100c409013218494800d07906000303461a01001828052034000c81081400c0120303601c1c3c0003403540400494164100444000b00c400d5051044005001a51090081203201422814103164840642ea4000200b0003410000c002c1d40d4036042044002100124003040d500d42101070401d0b2a00c58080c06090041034000c01c0004001103407644c990098048248051300001007070b859802c1801b02540c49044262611000c4c8a00000e540d2100c0c4270329072107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 146631483 1250 146630233 146630243
    0x1030b01050409151406031b0a3011090703020705060c090d02090115020c03151b0d020d05040c080109050319090f060824010f0c1b1202030601050612070305090a02120609010f0204060f050306180103 87
    0x100007000010000cc0750405000354040501c18840c40c40007540001e03209402c1071220701070036190b60b8101c00181c0c05000d500300003904885610000180f5902c00c3c401c0300d039034103850780075940071145010515aa800050107140201d514034008241d0b5004192244903801d01e22000217460164130b0000101030b40e120680202006540d10200010301990441d007101501346d9174024452101c5644a041d581c0c000c202c401801a516040c10f481a1030182c81440c00602964004510940d0395903000b8119103403c458401e469501c1c1c0c9a640c0c0b41c201240e00000d0710460507100c0d0a81000201011103070010b44500441e2a044070112420b80144201d02940082c20030801c0700c00314604c984141030808078180d200601600042c04000c07801c21002641e01c1e4000c3c054940000c99a807079402d00b9180000310301c40a9044035134100e090f81c0e40f4901051503481140340364028000c0d55410740c8103c04a202d40d104560004103150038a0751103500c50350045411110081a55601800d10491032602000030b03801294 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 146632733 1250 146631483 146631503
    0x4020c0607021e030702011206030b0717070203091507050718060603060e0c07140a0f030f0206060d08041514030c19050301030b01050409151406031b0a30 68
    0x295840d4100541108204080050180b0030400c9020355a40d0180c621700905015054500c080c41d100b0030b81c050f5006580106071980700f801c0c82c04e8041c0c042e121018603851082140d10003d0000e0340000103c942c4154050702c1c04046551060303100781d0503080007904450340c0c0145500042e07051f068800f80805055449400034481d440d0400c003a0031941140c2c4400395a80103401040b111126000a40b0b030200c1d00451042401c10300c40c0b0740305080c8201038100030851409000c4000900d07038060102513a6120507022500b0300d07100c0104024285c0380841000300440030412083c4070000030800409140307002c03402c040300444001f00341030303186400843c1c0c01c101e040f0380801c03d02d45010900640e0003920801d410614915410f64881d14050f45050003000d00990f29401c1c00c008000303a043d85448082085101001400c4803900400413411050b07a28620038440c0b080b81c01c1c50800003409400e40d4180c020300d08a51036140161000c400100116070034804960418400c503225501e0602410344d9200d880700d05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 146633983 1250 146632733 146632741
    0x3020f07230f01200c04060b13090f02070b01030f12080f0a1107020303130503060601030c02060411030a020604080a1b080c1306051903060605090603030403060c05070204020c06 78
    0xd1820900750300c200454030a0101d00722003404100e01040c0c00750002d440d038512092002d0b0060340d110280543d81185504002441202000e0102d1200c40e0701104071401e020044e520f5003002228041c4032003c03d2400d4110348200103c072440e60019080b116a02c40150030000c1544032080d5440c000d0340b043d41e0082480200f6010818200100b41e040c10392400d00203c00e080038401c1814021004054042e5195a0341d054060050b01000ba10351240c0d0060403070780c1e51640b240c000300700045a407080c18001d200d60740c08076a0940c0240a412030030101a401040300740e40700e031180002d4090001b101c4c0c0e014018402043d0142e11084010301c0070708544c500920603400300c0e203044a241c034181d1066944060181000b8407085901080061406404641c0f640c4a001c42c0c8800000402c00f56118982c1310407541103028500c000e02a200c405c40380580d5041143d507076241d05100b010b4000b21400c0360325800400c020720002e40c044d80b000036200c56030300e0940d0a01342240d0100e000c81c0d200c0700c00c403070455100707000704 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 146635233 1250 146633983 146634013
    0xc0e030f0c18010e0103150f020a1805100f180e072105010608060d1113060602070807260f010c0c11011707050a050c0a030503090d03020708070605040f02030a0302 72
    0xc2e002030381c1d42a20701258504442da0f000d42106000041000c1f6030b0300c0b0111494207068114007034810202c682159a030b800c10030080d00109402d5910a0241c0000704001000e2030064070300c8021509a4a5003d50446480400c4481501d81c405100f0b5210341d4100101d100070003424458402c2010b515030002c045000011a0a208072000c08468030070300b0310005000e60340d03010800980018068619141f10f011914024100e0072a0410b11508900b00306030340c0f1a00c903050341003a01207a1654007034071580d43d16292142e84984040c0104100e01c1c4400e8805044d8a0070f14045a0094541d0b1081c0c9031501d211101041c25500007c00000019004010b800240302503852034800100090a01c559001c80441c0315200c2848001d202d02d0a02c4001315141c800b0501803c200c2d80c402c80032109a4402c030004d4030380070f80290416035001e8000e214258001101d94042d1003105c25a5030001906410325030182d41d0100036060040049030f25101c034400030740040e2010030841d48003d1194000d0060440c0074034171 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 146636483 1250 146635233 146635249
    0x90b1006080c03060a090b010c050a0c06121407180306020d0f0b01030c0f03051305160611030f071104020702060d05010503060a150e09190c06020106051807030c0e030f0c 75
    0x100100b00700e010418480a55101034889080b04c80a100c042000d019140040c0c0c0d80b8aa8844042d150b40180c814aa0420101c0c032100e9040d90f040ea124440366240452070001241d07002082c034480a9400408100424003e40c0d0240798072810640c0b490b0030503241e03a0b401c0c0917a009002d041d0103080d100c2c3c2c004600781c0181d004444000740203107010096010000e0b801003401d0041c917140d03000c2c1565240455041d114003040e10315140d80000c01c40e2030012540300701711008a902d05c00c0400180f4840c0d1940c0104001100320b44007201d4600b0404d00301045e035203820002d0b04150341a2544a6420002e42d001070321014041c10030f001d0740035000a210341c034110600d42030603c002c02d0440700929141c104040d09283c41540c10903100304111521a546e00d03007052a01e4400d4070354802c0206d2148145510400c00003140ac6015540568002e0007115910018030140d98820914004048880350010361105e11030360041d4a4185107140040c079140e020008242010b40d24258481d00f13400006d0b9840a509004c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 146637733 1250 146636483 146636491
    0xa05040b0f120c03070305030d0f0905030a080a1407030b0f0114070b0a0603021206010f080601150f090b0f07020405060901030f02060307030905061e0601020d050f0d090b100608 78
    0x60a2000548020000d4401c40102000078490122aa032048038403608010a504110000d0f08641c103103a140d00f44680d1300d400040001501d54100061002c18852314015032140c90b0b8008001d41c1011040b89040e41d40c40320042003003851076901c80201c05c551030b143c1c0d04c25000b003166840002d500ca00a100b886010348040c4040ca05101d150b00d6070860035603e2004403406035800003211082901c8815100d006011035500c06980200c402c140120745040100d0711a04071000c00f45218030703150303480c1c0260b501d80030f0074840c103401c440c0401c801c0c0d4180c0f4080d90541d00300c0360b03952400181040d01d0b60400590380d000b40381c00d594101d0020501c10118100ba109082c1c206108890358170b4558503540c0c400c40d00040c0c89200074020b010110100c1c64050081d0061100e45602506913409450000300c1d600c83c881000705e0303400040e48440003080c00d650000c2948100c00e98a5681d481c039100c0025400c40007640400c40364a1441c0e954000280410b140d0350056005030400c0b035002c07500ba407400c03600a0216902030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 146638983 1250 146637733 146637739
    0x140d2603070816082406030708010e010e0f0c0d0b120f0c030a110d03020304090f090209130b040605090309040203010b040e010506040b03010303140d092301090b0f0c0c0f0304050a05 80
    0x15000482d0b003500404c01c139600600c6803012103003139818540c801c40c443c011020301a4101c0e1001c000d10490a4001b0300a44c183e80c124808210755170781e1024250940070095440b01a4403040101040708103c600008003040c5407241c0f0301181410380b0401060025407910340000c884d4025a002111050f002d0180000a1100f10000d01c0035070080c3d01da500da0001405821840382c1c41c05400141010300a2042c0e80c001d00405808000d56015603d81102814150308101d100720110360000e0300a640a040003090a6040720034030b6201c1e503032a62040001c000c040d02c8800d031407109111120300380c0d8031400198040d003ca42d0070b140c2c455180c40c034a6440540c040c3c0200c1d120b03170b01c240800e11281c851350b01a00d045942501d4051074004080001084030f01c900500314481900742104a814014201386c94000758019040003052594501109401c80e1000c00c8010308138422000440e182403040c20f0402e40007040081000c3c0740c20a140b911920305008a24018540e81001c9410081d502e00b10180030000c120039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 146640233 1250 146638983 146639011
    0x40b03010b0a3309060201140705070f2303070b07090305030f0d020403080a02010b100e1005030615030106080403090510120914010c0513080304140d26030708 70
    0x400000c2c107007252401800d10100c0ea01d8246007000040f940da5034a582280b40e0010b00c40b03162030b5001040d103422400340e03102540c01c00d10140a0102c181c8403140c814040c0c4d03501d050504606544030302c0034081400b001d4807480c485540c19004245c0d0f4100d01c0710302e1042d5600440e5286c490740740c180360030100102044180800c420080000c100301100316410052070140032b40d038410966a0030b40090060b82c002514400c4081070390362209805521148951208035643c080c0d203064484200d486c1d0415111458201e4000780b909200d580c040c07009141c100c10020200d25514906d412402c5464009900070400541e9040c02e01c400e0542051404020f81420798003010f00e015446c0000d80400c021034030f9102c4856849c50450140100e40c01c2c0078010351180070091082a4400308005c0040d041103a07410642e103031040001881c02800002c0b00c08690707410314002c0d581440681000901d010726103054459041000c2d00b02d040348040203500e40002d502014403500e0b13007016074009124100080c2003444040345 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 146641483 1250 146640233 146640251
    0xa03090b01060903020a21080c0a0b07030203010806130201050d0b03010b06030a0203070807020a0c030308090c0405012d0f1a0408060403091403010504020a05060f0d1b020c030303070e01140906030f06040b0301 92
    0x1035034481803c6402103c0c06540d5018992704902d0251040c0c03025041d4a5410140481554190002c40c1260f60010842e011501c80600049204c1032048000b0b001c50001c2200e500a4071702500301541598000700005611025000440e403d548200c0c0d0803000d00b50700104211040b500142d8454110442e4401040c2100c4203682c3d180800c1e00c1408040e00b40301103880045e0f00c0c903d04100304042c10001400510455a540101101c2030000c504000d032100c10204290500601001c0c0080854248402c4003410760700e000d225200d050811081490851010800814442020008580994400d41c2e50102c4246171480e40d0701c501a0b16034100d440313a4142010701000d030361003001000684a003103820320342e21200f212420703d1a02c9400d0301002000d01f04a01c1d5581030040412255825009400381c8224046100c201500d0303200c00c8443c0f101180c001c24480d800340d4420b81d00510018817517501e051074a034810f40001c000303400c11145030f144120901c04025040c00c0a00840010340403c1d00248000d2407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 146642733 1250 146641483 146641529
    0x903071d0c0f12040809030f010504060b010c0b0a0b0d0c18051e160201151403060906040503030106050f072118060507031d0909070303110d0e060a03090b01060903020a 74
    0x100d4001459400758420000c02c090006a004603886008007c0490301200d60054442e8081c10701140d00b80c51280c500036610480c2c1d4041c1d865000300c04d03881980801d803692400c08400051040e00e11f1503070461941212040042c130044814000390024410303505070284104207580554000510110604841090010341201180781198020b600c0342041181d05000d03120480c0140b11441216215416105d000107190000c05208803070342c00c043d404e4034a10b550b100981d81c1d8894043d20f0080841c3c1c010001081018400c1010f0b012107100148000e14101450301d0700c64012440280403070848a0303400040e00c085401419a0f4103008105c45510030340c52070318038050158054110050280201400310000303444070148420000d041c010040b551900704460348543d900d1085c0070031000310b14070004a6101c254001013100e0303100c91540d200041000c0c0d82c0309203d8660090b400000030306844c3d900e01000211700710740690103000227940d4080480d2540c010030812040176801480700310f20180400038800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 146643983 1250 146642733 146642737
    0x30201050a0302090411040b1b0c0109121401060e01180606210f150614040f030f05030c0d030b040b1203180604080316030801090509210903071d0c0f 66
    0x7042030400580312481c030303008100645220850301401400005011400e10301c0030b0b0142054030203c1041c5950144018040e5036205d08208420740860ac00320020442001481466083c552280c01d030741c50310541d541d90f0f0a0070742d241c1e03801000c40c68003041c0042c025081d0416000038040c0d007511007801183e1030402e001d002100e280b20404081803000300c0340d107030700030f140e400008014204203010054081e1603450000d0303081490007446c0025036055450003507040c031001950217480c1d004d1460004140f441d502c1c11103210040344216054042030040c410b41e00810301901240440c1078401040207030501080004554400420314803d1800354480b80a00304000185e8800744004020000e50404010010300b04d805140c0c8070840901c0001425680e2a280c1d50980c5003a07442511681d40990702c4e500090309481007110b03000b06560181c00c490f02c000180c514034203038403600c0c00d00141c40c25008501180c00c004503900301000303443e404e1300301c0d80310500107920702a4440c005050040c249003100d219460f05d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 146645233 1250 146643983 146643997
    0x20d0303020c19050714090405031c0b03030d15050607030e040222090b180609040b19061e0803090a090902040b062d09060a110a0b0f04120903020105 66
    0x1503804a86000740180c10828124001009119010412603502e0030a50b038840d94004c80c0c1c008000d006040d0b401e4141f10700400c0c0900e03800750180d81050300300726400114414102490385c20a4403918500c40030349003030006001e00c43c22044041080c20708180c1c0d440c1c10100940c40700d4016101000044042940540c1ea1001000c04846c0540c1d03800141110115110b026164501c140005a40005051406a005a2a0040a90340b15440003d840305072820003034101e0b1580e41022900f000600012100c182d41940403d1084901c807a03d203ccc09005c800f141c24580180501144034280c4c201340714000d203143c00c0103103600310003545480002c0c40483c00300d01881c4582d060f243e4803861010b00b15641c5401040c3d51000c0648201d031185c104030020140c1d2a513011003150015107098982c00d0905009080701c24500002e40428a1310030100740407114401141d0000d80c0601903075034080002070030f050101d03014400b440e005d6001801c003070800741c070b203115510020001d01540260400060360450103a51003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 146646483 1250 146645233 146645237
    0x80a03140a0f03090c090c0f0e030a020f0918010c02010207031e020c0105030903121303120b1c050307020d0602131e050909150103050d0f08150d05120f0a0318020d03 73
    0x4c22041c582a1820101900441c68441c01c0c440074500e06984002c0c08007070480107650f410144c04219062640781c2c07000010181d009081454402c2ca02d081004034290858a400c40180f00c2400c2d000081d401c44090403114401030750002454000c6c5507000c01e4030303481c15003114000c0c01c061149540103940ca000315441c0030b05205010001400f0342c0303020701c261b80170b440360019058520724050b8450030312044005d0003200030030798407000f022054015200301018036802502504060091460721004464401c0c822142403004114000043c0c075484031803034115101d4480583c1701c440b24100f0b80d2494186801c5032500c60050308114101a0341e4480300300480e00d050315103101c03a4940b0200c190601884100f441152030310b480000080110015080d0300e03410382561001140b0304054800c890390001981c0454040000480c440c0e00391505c8640302d503440e44102e0403a000604810f035a010150000b501340c407004040410080c4c070b140e401d40140c15a07041c0814039103101d000f02d6400a100000903000140c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 146647733 1250 146646483 146646491
    0x122309030d06060206180303090c01140403020a090c0806031606030b0112050f0405011d0a1103010209031911060f070303090c0519031502030112080901051201080a03140a0f03 77
    0x14008424021644048007040050184603103403100a90707144010784042441000c6004d00140485003c810b980c000d60140014044400c9442d0044460003030544c513001e000395040000000595524031a08001c198001010400c0300520f540940240c1e401408240079810100307900200780e06103903109068641c2070a0004000d903c4400486545c4005010002c3e21850075040c031041c081d0840c04070b480b480c8544002c1c4040d010b4146c451a5110a00d0b00d0050706a201da601c4800152007104030b070080c804040c0006050441180010340b420303003111349425480c2c1407403600f0400d120030303202000340e010310590341c0710300e000d819086000140c402c02c4d1024007095a1603469104000040140c030300141001041c071948082508003084030304440344400c0312501ca20502d0030a5030301090098074101c4600c5442d0610280080d100c500c81603100503440da040200c200103a40d406506401c089001e814442c00034a518141d914024102c4080d0300d01e00c2d041100c0610141d031000d50b02c42c02c2e07200031100502e800f00e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 146648983 1250 146647733 146647741
    0x31303030507112106150f0f1f080106020d080f0105190306020f2701080705030403030e0307080d0f06260c06070506040c060f0203070611070507030b071223 69
    0x20038841c1e403000305964080300c50908520408041242a0b03078402c0060243c5d0b44640342c50081c18008480d0b120066088050030106031510b01d014021462140f40190842041200e00c1c0c0b001d01d038200512540001040c0c00400501503581c4c1003215002c6100c0c1400c1c0306559041180d03c00240900512403141b0465402104c1e070b68000750022250015a40064259101d1a5070308082e82507402c041d5815200d44502010703140310881c00b81031160b0101b01070b19402c13102e44910342c00f21340c00d0340003c0060b0185511144504681081080284a0f150040151a40b200c0140c08044155a101c00d00450850305052050291400e06003524108030203d82c100424404180d0307100f8100010340c01b130142e008101142c0795061290110f00184110b01c5030980024003501c0310015100103c550071100c1c01a40700344400c4000402592122410130840c4080074104056076032502e240009a8000700e6084600b0020f0081c41034001000b0544142148005c0c0f00240d90036400101100100c9840352031907030710801103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 146650233 1250 146648983 146648993
    0x1b180803030c030a110c0a0c0515070f030833040e010e0c210304090204090c020715030203130b090d03180206090d030309080c01050103020a05010c0f110303040f0f1403031303030507 80
    0x81302140300c44c1d070664507c0c02c81d605000c115403241e803050901400701c0e418100c0c411070b6007204403911643e000050f6080c0d6201d0f0340b01200c06940c01420890900303014100340c1001180d601c450b0891761030b51001c00320480441c000b400140c800c044116a400da040032000e1107030030000715000d010101c06541007503121a00d07203060300400c685000740791128080080d004c110103111b41c0040042c0c03207864405000c04402d500f0120f949680901c14201a140c1551103204814441e800858002d80e21a92600f02c450f0b882d2144001500c054034913880c55030080020341803098141c042c0e20f0800411060714001c0c11040c1e0045000340c421403542500c1450b400f005031017014080d51003007a88030307002886203440701c03821045035008060a01041c0d12508560400103400e41c45890708519080d840102100c18520640d00d40c100505a02c1803035a050000b4080401d0011040040000824404010401c240d2405e0750003138003900c8442d0ba0380e009410402c02048118080708d01c4200726a0b062400c030f41e031400b01e8100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 146651483 1250 146650233 146650237
    0x203070f03020a0e13060f0b03011a040810021804050c0306010201050105040506010219060f020301120b01051509040b01030b0910031406091c02010207080706050115030b0f131b180803030c030a11 86
    0x44841c545100e1000c02c8c003044420140d4140c6410300c1030400e82500c1120100d00c1800b481c030803d185a40608803048601515401400b04442c5185a00050401c10b20000e01034540c01c481910b16a0070102c10004150b070f090203000d00612080d90708011605040300001c1d1260404a00d050b0700801c0c2c090350704204451580120030110b0202c0045489503150901c0c41c42c20712001d00290340c2880b4036000402c451410007040d210302c03032582089514294052041c40082c0a8060f48181816a00c3c04010429141c80b81c10768807500c482290100c4403030552038030010200c4500c0d00000780307500034000c00c0124a400280384021444180240c40180001d0702c003240a44140340f002001c14030081124800c10003542c000c181030307850000c2a180b48110740c85088048030640079000741d000c10440d44020050a00c540c1000c0c908500d51000320b1001d2002504482d101c0301042407030700092024401058825402c48241c014020b104051841c0d420940130b05c803114000a00380070070203542c41c48101d1003144030f001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 146652733 1250 146651483 146651489
    0x6041407022d060405060103021008130f1a0c0d0e030405060a1107030804030c0f080105061302090103181b15020c041805060405060f0108070302010203040b09010912060203070f03020a0e1306 84
    0x2c00c035049407074070380303031080e1101020b11080740100c48030b20090380c009003e02040340c81b07500500c0a010b004803903038485402c0c04004150954003002c0d0800d808021800710340701d65100d41e40d550381860342d66100700900c04c222101821888220b40007808148802c0e514502201c0d0b1141c05490128884080084200c1c2031400b154401070410b00e000400004012889400c202120510100069410340e100011800d803a0110381103030784034a194081140340c10199010380500401850002520f0610703003000300010619045c10703a26840ea15800381000c4140c01b0255018120a1680c4603114540740b001070f54445806001d14410f41d1248031001c562210400c1c600e0f0400d4001040301d02d1420241800d07920389a007540c0a901d030a42c0385c000444d090314006403403800c80b58103900a52809190001554039900110700303260400241c1180014183c54112038140007034000e640060750390506c603a01030410180b0203194014036005004011441c3d030890b0041103048001d0f03603030650a040c00d050080c0140a2a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 146653983 1250 146652733 146652823
    0x309031207030f050f16080405030912010f1802150c011e020304030206010602030408100f0b030d0f0224040f020f0a090606081014060a1806080604140702 68
    0x808214a503a4560451402011640f200f04000d40351039031510680a41203c01c80c990b0452025034416543c0f04642481e409805042664240041c06001848082c070952620041380c2d11030040e07840e00380140c80364408440e82544c080003081036075804101c4403207010340c0640140030f010842c3d55190340c080d04030309181c0210086000c0703c002c0b030b142d042000307403c25501940144210400419014000400c40d810b0319200801005514074002c1c02e0806003104044000c2100d4980080703603010380f400c00000411401e96164040000ba407171600a203401e4890501d90706401c607401c1d030f8281030301480c038010740c1068000080c0201000319001090b61042443c92260700a0000030f000102c4413115800307002503450036034401e040c5440b100100b0301e40c00d03501d0049000c11226002c1140042c60078a004000190440c2418624412116104000c0400607800a00072803096020000c16141a1007030582c503040c0c4180d000c0c0f083c01c081134000c0d5103007029600b1507942d41c1144013180903243d569508074042c410351 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 146655233 1250 146653983 146654017
    0x80601150c0203030f0c011a010206060607060e0a12140703140703032408010f1b0305060d05010516030e0d09150512091005060621040c030b09162306030903 69
    0x1012041380140d210b46d140c81c1e1035500e061145040c40c1c3c20203482880f2598140e00034265611143c1c01c0105541c44101d0881c3c5481c3c1c0c3d8114420301b800207202c03200409004200341d6086810100d403b428541d1090f181070804202040b0040000c0d0700201d0202c542c034240d8650a8549880d031409a0040a02405c14000c07408415030f043c050000f2045041c0540b503404000f48124400d1640c0c0b40180d80b80c05104c1c06030300d01d003500c030080068880e9002070b50003c0010b0506035440440d803206801c540007611542017840d5102c121070b00590b003500880070308902404c010810b180b08117a0081003058180924501406500140c40742944101d05031510300e00415036400c45401c146540c07079035917900303e60482416420040061400e03d805801c0d5110003203030101090120f074012209054083c00200200c85548521202102141c03428003200c1c4100d1922006140f00130000c0d10f200d6074035205522440c1c0024048004404101c10746054a85487c0d0545025880e500c50100b01d60a501815070301d180340c00d0326 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 146656483 1250 146655233 146655247
    0x605060c010c0908190b092a0312032413020a020c1003060503060f06060f0703020a1109190f0608160f051f050304030306030221060f01080601150c020303 68
    0x106510403080340205482c0c3d504460f542d07148040d10390420007040103103043c81140807008076490502c41075105940c0c10544010005804094001c6c3c0688800c204100400704842042d034202003294180c50240c8250355819868a54891504400d1464002c284c80704035881495203510340b030385100011010044299110700c01a10002d41c0e810340c072001f00c4d1141c20449080409070380240700b60010798801402030901643c0c0c0d20315000d02030380c2c00382446420030030400c140041c4401d41405008118400d90113441007054905007007240c5000465604e100782001028002101000102460310742400c100129150300501d02080c002c240c65031010038140a400d620844d52b29840c156402603503815011000300544030b406001c18030305c0d01180c80305000d106240c1400f1560280c4003a5a015211703140224500f502d0303601180f1080040d00d8070460103c5815282c43e10303400b06004c12a40149010005490742d8504000d4613a1810107110b1204008100b1a03940385e00b0340300724205040c481e00a42200d079a401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 146657733 1250 146656483 146656507
    0x30613110a03020a0e121e070b040b0901120e190512040602070602100902060703140715020c010c02010e07050603091011030117030703021f0b030f0a1419030c06060506 74
    0x8411249540005c1c041120500b2034a000710810038001c4d4071000030f094618801c11344c019000f80c59020b041a500c50b21500090800010b0700a1004d401489440e0b07031290a0f1100242111006800380144142401c80d26200c0e10000030301d494181c034010389250222407060030610300f082c04003080c0400d5011b00050114003182c0008005c41194816400c65541c82074074400b0404803119040000d50040c4104610030219201d0814807010b01400c22006150940c01e030f4a078449039055005404820381c0200c2c2c0c1d2185500300388188215510746000038040c0146040030345440b000640605841518040b0102303002c400c0800421082148030740302040700744501290320303a031074000748505240c0d418640d09401034130f040403083c2c80140380c0c99001044154a6100c180030010000101951803c0d5543c45203201c540e0100943c5440c10307c201c020b41045d02c420700b46602c010303c0003205144540e20002c040c0c2d1000007806030340300c3d55940515221400d00742c0c0b841c00c032010707100300d501007a809240400e00c2c801c492 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 146658983 1250 146657733 146657737
    0x23060406060807060203030c070b071b0506040213020903030304060504060908180f040903020c01030f0b0438100c0302010b090408090a17070909080405031f060e010308030613110a0302 81
    0x15550b00201e8140640e604000c07a600e120445009040d0306083c8486000210f51281e0b0369080308850070850080511482e04400200044038241d42940c0640c051200b5400e102160801c900c503810b00961904041c800800c2c1d9034400900000c00c0d040d92079000400344900d0ba8000300800340d0000025a468008024941c04000200d6203548600c1421000403024a41032203812040f95054020f041803441c40720042d001020460b0120303c8058480c40301d07050a40d41e51007801a1480c1442c100b005aa0328542200310048001d00e96500b05000d40034a44619905c2000c00e13004aa9a0314090000c5181c901c0c04034050701c0d10360900d40e000f1038042c003884100681c820180c14007050a0362703081c8803142d076407103989841c4400300d00941d256000008184800341243d00b2400320b03e8018500d03545040c0e640c0001c2860004c4001d03407001803245155841c00a0032050059100408402c19100303000d50441e102c0c0560307481302608143c46203061201c4103100419540060310003020001c80c60b505d81e0814207000d40a9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 146660233 1250 146658983 146658989
    0x7061407020c0303090d02010f0e0301021c050109090302060c13030b0c09010e030721060207150516030b010e0609032b120e030a0807090b0c070f0905040f2306040606 73
    0x1d8041c07840e1a40306414004251048004024540c6044184640040d241c810440f140641041264070403504e40792001d00081c010512621901c81c000030102058034100d40041e04503100b66414004902c02190b0300240d56a000400c24025990351105c807134280109103145d034002403c164141040000d0f009079040a040c41210a1700c4a00d100c000a2081640f0780c0c0b458000c880c0e600e11500860780c9804400f551a03141030b80f29590046c03a040480e03c90b507202440c580b00110006445004004100c0d000803030a200201e641d00b4280030079005540060304010f040e81c04a4018500428600b44655081007680c060b640c00041c018a102c4d6400c3c01030308041900c40d43d280c0400d541190b04000d402207449171540605203113000e0350a014910070f08440380c007005058101040000c2a01003240d40708640140700041058000b403900b81d00e00f07900d00c401c554580d40441e00140c0782c0010032001c28401c1e040407211940c0500c0582d6008003212003071a081c036028824017128401c1a0401c41084402c0d4850310507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 146661483 1250 146660233 146660237
    0x8010603060c1707120b03030d060302010f08040b160e090403030c080606040f0e0402030321011a0a02030a030f061e03110301021c0e0c060706051b0405100c050307061407 75
    0x5800440281540c0e00180500c06603603da1140340090100f52113001c0074800310080c00004945c001c480700010385150803100322140d00f50744e0343c2030070421582c020130780d0b14101c0c40030b0500b034074940f4007a00c03400300f1144010841d039440d01000700a810395520a9140c2c1d06103030801809105a0308080c24010b0041c44446407000c0031466000201e00340f858039500395030072581c140364180b410600700a02e04c403258101070000c0380c0500c0140912000e8010004000306800d1a90004072440d6142095280840360b03041c8a5049000307080040d00100c9901008641d60078069082c0840c65881980c5000001c00440d407002400d22007112641c02d4041300764031040102c9000c0c907686c0c40c8000703401041500702d2040a802441c0d2510107620403003145041c0d0450010700c0764100c1610000180c001c08120150b010060845055a46501308142a14251059003030500d030241c02d2401e2600309404144004070f04100c7c80203020348403204e8070802104004881003a58490300502c42d0780d49050380c003800b6080035550140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 146662733 1250 146661483 146661491
    0x403120903080f0c181e0904080a021009020901140a0e13030306090b010e130f02070f03110619020d29090a0b0105090f04091a010518090a061805070801060306 70
    0x250940003098070b05000c5d1800119844c0c1001e00c0401140343c2c650002ca21152080301c00c00c500c01c1c2d5031400341d03900c03c9000d6180c00d507803001c043d00c00a0801d660143c1401249103800c4080d4050b807611180507043d550721101c0d25500d40348120002d142065a580b280707440440506c2040040700c0b50181451996100c0d813824030509455110340ba050b40e2003a684c10b4006542504c0c445070500c3c21720744007811489420300020714552843d0265040e0ba102400541d00d02141c07503187c50425500c40001c818100d1024081c102c6406e0011008900301c0120031210116500400d0030965291654003e081d40c442c0704041d60075402090303100c0d841d0301c40000c050911075140c500010f03041c01d055025490500405070354280c80d14461204200c000c1c00c6040e0780c59007090740d8403240380020300081a40d003c20640c00180b00300541c585401c00484554011401000f040342d0760600107400e0000500c0f984a40c0d03c050045000c91014481e02d50805100b00d000c0c0c01031007202c000203184c21040d0311050640303000b000140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 146663983 1250 146662733 146662741
    0x90f25060c1709060d0513020117060108010b0d020c0a050606180f28090b010302091302010203030c09180103030c0309090902060901121107060209090106081306050403120903080f 79
    0x59081900710030068580c0900306080c0c80081806001010b0f040c80040400f42003095080780e140454004032a00040f64180c0c0c85104195a00700c000c844014000c5103010705a85001c0740003c104c0c400610580d0400b01c80410803800d01141501070360940c418620450b101c0c0302850520315a41c80302680d40d07500a8910410b0348801b00e480010480c0b2130014004001c00c292100c5d0318585e452404a00d4428200744c9144844048600b14002c000016008a2051509c0e5055004101071480050300300c0c800c0403000016400181d07008000d40b40e000c02c48031f59282c2c8a90b40340c0701141c01042da8031620020340c10a4800031003010b4102c400c034022603001c1d994001016072079039002422541c0c100c001a40c0104184441f0420303622800c0481070740b0407062000702d00205629214034003a000700c0c10403034070b4940115480805090a0a2450040c0305c185408401800c19031030a001801c0e4031200a0213107502d400001d41414000d106030a850391841c40200040903031030030000e0050005450b519103103c0c1c044042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 146665233 1250 146663983 146663987
    0xd0f0207021912030c030c080f0310050103060f030b0402150c0f01060504150306020c0f030307020705130b210304081c270612090206040b0403021809070608090f2506 73
    0x11040d9145007500341412812510184c41102d00150206c08100f0a4041840022500001b40c49140c607141101c588a00f0301b00c0720803400c1c124980019040509e04001007103c0c00c0d4035540c45044a40000c014003107a2034500225006405c816a03850020b24006480018002d000400860340f04111002308442a210800c200581d00c1d50380d614011104d4100c1c00303001080c001d43c010078030020321100300d40000710215000c07421070704211440701c0960083c1c00304000034200396144203201c802294041040e00e1a0400103411000001001d000380410b240d000e40240304e003082220060700a010495111a1040c3c0c5e106802c10801c031421130014252508403000e80100c0542d80013641c1d81c030620355500a062580c2110800000048003080a03191610800982c81d00c00080024003c039080c80d40e9214154014450024041d0800ca055180c00000b00440c074403000c00d101007aa181e501d0079010b140c490651143c5803013050008500c0b2401a420350082c40c1010191180c901d000b20401c03244903641e18841 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 146666483 1250 146665233 146665279
    0x603060218011e0509060f1902030918060603041205070602030a150602010513020603090a0b040818091e040f15090201030c020a0206030a05090f07060203181c0303110d0f020702 78
    0x3d00f07010503000e000105a0f03150480250070b80110032800e45007411070000549601d012030001c960090f030800501c0040c28104103050f000d16408501f08070300641050b1000c10403500c0020800f500c1c186807034401401c80f901c524201c8040a4200c14199100d007401c0040c82d004200c00f5841007850342d201c10001600c2401809140d2041d05004890240c08001d902801a5035000908900060007840581d4000860301f90600d4040c80c045c201e072a0f1218a81e002c000d4042d6003034409644192124400c20410300c0342c1c0402d138800d102c842c80480f0b5940e1901d2408850013601d049005000207400070030f801102500da03110000d464000d076000d05c8150700700c81c0c040e0307140d141c540d4010790801310030400900c203901c542c2c001641000cac008049a03001c0d207201088a0410f041074002000503000000c200c4e905042e407407004110000200c40700e100300c1c10548003441000600d104020281603d42100e007403c8420001a07684201d03401c401408400010120440250f120b201d04906c02d00340c0310284c0e0300810105030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 146667733 1250 146666483 146666537
    0x611070f03030e091504020408100e0a0b04061e0204061d0604050a120816050a03020f0610090c0905040c0302040905150609010c060f060905190c0503010b090301060306021801 77
    0x59441403614840140038203458000d00146840e8605d80901d48a030300d80740b005000500c02500502a07070031010201c0415512020107480f1f003540400c116101107001c000b41c003034105900200001d62017104103485940c0003145000c10610700d00c08200041d0341038100c5211443d4410b2100d842d410741034003c0400c81139024a01521760056140c4405001c2c0316440030f8600307201c50260082d40e0424001034010400b20900340d800312460380180861404054040090f004540c1e4210050000e82c42c1c03e10f40b02c40036440c2c6109a01400da12041d510454500840d090000b8010103001403061151030100980a58041c1c401c2e02e55962420002420590444003013804402000b42030741c0c030f0300b2500001150075031402d2405072505665007125864101091249000402c03164a0200740c6162460645c2038004080031340c88001030811518041c505d6000c07007100d0564000c40a580e840f813940002090040480340c02c010480b0348005161000b18800c200341e0002076000340da03034420383e0010101d01018000e03000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 146668983 1250 146667733 146667737
    0x405011410031109060a020a0501020313140601061d0f030601080d182108041805040b07020610060f02070504090501060f06020d090308180303071109150a0510180611070f0303 77
    0x40702085091030102e00401b0311259034411a846d2030f0399038031010300320390003500d00980c42d00c00411054100302040900508030446200500392542c500032002d890381c000b00000b03040603004c0c5070f6491042c0d038945600501090000e41144d0696840721145030382c420100c1d4840c0007041600880f043d007440c1030494002603030000c03030402071140c4048000040682900a04a828000500c80841c01c04031160711078040e0419107002094a050038141181c00d000050280811900440e007080f490300034024248044655515000f24000003c6004070304100c01c1e5002280c2c4281001451030501105402c554103803001401c074034900660711907043c5c0e81c4054485902022842201d4100082030264000e007001c201c0d6441000071002c80580080d04541c08840100c41d440d40858045c03500c1e0031302d0400594495159000984c10078410400a8040040c0344200b40c4210304140300303801c185101c4e800000300f800c3d0400c9444e0201d61502c4001d0704241c0009282081407140312030000d95015883c00303100443e5016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 146670233 1250 146668983 146668987
    0xc010914060f030c190c03080a05010302090f0405010216030c0507050105030f151906051c050108280503270103150506030a090803070207090b12031b0c04050114100311 74
    0x84042c0341660401441030103100340c14080000059510f2580071340c29605541d17a034402c4c81c401c7c81d0107400a880074150740300312454940140f00680b0b50b040c00b907800c00462006410541da5914103280a84103003040c074410710010100780820560004004bc28152191058800c00798807030f801107820f40404c540c03010700e0300c10388004103401c14485015000c0c000344c007810030081c2e0301e040b00c683c01c20820340703074407000010310001600f8800c1e203150fa40b08084000000c1d070030f020365413602c0c202c0c60344c9140c4a6454154800020407140d1011489145104000d0f440410b0702d4490810000461916681e039100700400c0005801d141e0720b81d8440c3c4900f114100741129188202c90601050107001d030001000b2449190b0303140e02c1034011803400710103184282c0703095009003d81414503178030809690541047c03030701848401c3d0b8031042010000c016a0904070401e03481c00f00701c42c410302c150b526045994694503002454080041031440904e25810f8104000f52007808402a00030b400f1422079000b01420f0a0042007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 146671483 1250 146670233 146670247
    0x80c0f0907020705030d090905090a03050415020709050a0203010e010803030603100c02030c1606030b06120103020103090c030f080301030201030c0f09060f11070b0403140a030509060f04030b04050c01091406 91
    0x3200340165005922441102c04054407240800e140124140000c408640b044104004542d49401855030051400307004c0c0090f408070303940c0901a1b02440c0100180f00d008c00c84200b00c0b403403080000344c0080100c9201800582400d550600080d402030003030303111280d102800072900c070400204072030050802034000c245500340941183e0040002070084800c502007040380755080f100c108607510061568044400d41145403050280485101625450107008140500b211080d242e07100340c4d04494080c00c0200c1c11703101e68500801015020741006101c203009894200c00c0c0490744002d98180d0b8800c1c0c030108802883c980c0140c4034900c90404403000030f21000c0082c0000b07032052020141c40c10640c2480180141d602000c50304046e050b81000c01135a40209082041c07103030410468109603070550241440706865200100380c0d1086400030b60040030002030700c910700d070541390480b402140c200071480720342d05041c50100c0d200c840c00507205001450400d0046a80031b12800c0380716012034024600ca2410f03038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 146672733 1250 146671483 146671489
    0x6060b030712021b06040c05100e1f090b0c030406090609031e02060c0f0f0d0503010b03241201090c050402040b09010315080609030706050a020f042d061107080c0f 72
    0x3c0842402c00f01c3c2002d41500b1103440720100010fa015031310401d487c3d40564108411310103c200200d10400800030951941d45054490315400950201c07000680c95000303020700340c00c1c2c07150441c5511a40100c080050804d0911002001410a5a90a40d24440e010350fa540c01211031540030300024082c030400e030456030f00e148004441c0c5d03e081480a0001420561600c17140c9091900240d00c1c46015000130442d030310841003d201950a602c1c3c0307801c0440c29075040031100c01e594000180580d894515120a8804503c482148288416070042000004400301c0c3c40582c041c00c80a00215200c21201a0104030f502d828000c1e40d042d600f541c0c040d03a05100802c40110050422503104001c440394900001c9980b85080c0042441460000010f540e501900e1410100300c41e4018130b501c1110f441441400d4400070740b481101c0c00c85800b0840b000450003a29183c4441d603c0c01e842400d03e260a1110009103180c00c48804140000010160b0310101e54540d025926a00312502065101000710394420300c600d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 146673983 1250 146672733 146672737
    0x50c010c021c02031509010605090c070308061014031015020703050c04020d0605060d050f070c050a0b070513060906090801090506040b100f08010504020f01180320091306060b03071202 81
    0x43e0005040300c0080c100b40031940365402c01039034043c801d41d468034014081400c02440070b40d000810346512034503041841d1401007800c0c02c0984181c0c402c904002484206c03611600e480140922450790203aa2400c259219a542c1000c601c031b09180401d07610f058100c241c0c00400c0c0c8000300c90701b00f409000074601100802c0001e502000c0400714072075443c040414103485d09801f92075402503001c030008180c2003490b0b092101000c0103140008201a085c000f0300002c501184404426621090001d0261121401600c6502420f111a580031048880000b250303a807164844046442c01d882c0c03900216194100a802d032002a00c020708158400000b040000f0030342d1100030703408418001c4030010191a0f1511000000f6075500001e21a9111410702095240840842450384001d080c14011803126040c88096078a00344006468401100c40d251100e210556580c03000030f2009180205078500300e0b081a04120a0400036104180740c128049200c55150003224003030345068840b1207990044141f040083c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 146675233 1250 146673983 146674039
    0xd150b031303050c07030804140f0d0f0201030b1314060f0d0816030302040b19090b040302010c0b0405011503080c010501272a0e0906031b010507110307080a050c010c02 74
    0x5101d051170010104241102600203410724454220210068108115080c142540c00c01c1c0714114102221000400180c8081d01041d0b0a09000c140e003400e0318001a154003074580060780103070a26060119040d070f0000c06603c00d8008440c0c411004000800303001d143da039110070003400000108040d48644400301c1d0008a4588a40303405441d29440c1c030400f0701143c1240c40d51480748080c40c0d01c040051038000202902501d140d0070060705080c51600024a0880c0c00c80025028004e40c401142c140301080d0480380d1584180c51084403000e83d60301d801c1c00380350b20000780303408903502c3c0500115104a0700c00700c040c010500700c1c01120034140e0340c0501070f0091a640210041000c0c465020300319414603103001861801040d10f41d099010030900c10f0090822008041c4c1d03101c2d82000703640114002d03640da80341031000350038a01540c607500249000c1d0599134212269951502c1500c41c0000c0c000800503c20b076445118806494002d0240001954007c0120100039409a444109030505800001000d0340c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 146676483 1250 146675233 146675257
    0xc0206130b1803070312061a042105030301060c030e0301020406271a0403030f0807020d03020c0a050609060403020f0604030c0605221119050a05100210020d150b03130305 75
    0x9110721966841c0d00c3c6030700281003240821000711052040c0c0381140b103860000d00b0842c00f20b6800e210a00d4002203d849a801200340340c00240c2148012243d41665200310650311208880ea03d51f15010080d20030140f061046001912000060301581418001d90342150700d02c1d210461444100c41c0c02c0081c0c20401c0c0765050b541c0d0300001d40000c0300c0318000d00b01445411030400466550f4107509004011400d1400000140206034042c050004e50024070000d03d50614036005844070350306c4003040c2c1000d5240b040640300b44914030521003501404903035180543d20079000c55409103280783c59180c442400711005004582207034a20740204680c6c3c0c1005a0205c0d803404040360b4a900041c0b110301518a210041d2022a00304102541038184604007040441c0d562046600b80e07407506000454144e03e038040c00d80942d03001c203003029409008102c402c903100080030040d5180d094091515009201d01403c4200c0f0041e507540000308040890104c90050070981c0d0b6880c01e009843d141616103910800602d14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 146677733 1250 146676483 146676511
    0x40810060e0a09020111060a1e02070b0105010302031f030c0e180606060f210907060e0f060708070b010b0c010c0f020a020910050607210302031621020d0c030c0206130b 74
    0x8030408060005074230402c0350720710000f14002d03041351051070080c00e1528424000d10411070000420503e41103a03045075800d00c0c0c00340e034076600c41c19502c0410034221580d01c25014010408010815205262016540741402500040e41c1c0d610005540154004444071030740c10900110701d01d400d0400050400e120f0030100145000010b03085104140061b107a6459000346c1c00c001d011200005000600040020f4600075000307030012000104a4014a42068032609002481e482048031080c01d50703507403c3e04a42035903815070b91295a00003c1c1d0000d802e0031455480c154110a4250141014200c07200c2e8550041c2030031a525800e022100b14064002c2d0701d800102c00d03000905a44030001800418459610a000041608030b680469050700200105040c018010411031365840f4140b0300308070b88103140074000c0040f50008000c00f044601600b003c1d44d80001000050720200d034026079405081990204045040306104a0302d4080540c0c0705001480300d1140341c00407410010440b03421015952041c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 146678983 1250 146677733 146677757
    0x9090c0f042d06050702030124061206030b09060702010e030319090c0320030115050f10050909070f02060f1012020114181206010b0301030303050a0b030106030602040810060e0a090201 81
    0x80d07400c3e51100d000140001001d10441c20280541816503080c245400148440c04034948261291801004108004001580c1110038180c000301c00440c0c0000c2145181d00b0714891079070b1501411941d5038055030826100c41b40c603110020440b0300c110010011328260410001c0000041c1c194a0801d450922020101001040750110004460340640f20200d4102c1504800c1c1400d4640c0c405030038020000b01c1c0e004002d0754855144003401c1c94000c03601080c0c00c1290780c40a481d940904001c05070440e07070800401140580089021102000540842c0d0340d550750741c074590345001022607072180f06055100040140d4080410104d400d14814104840c805040340c82012168100144660301a101c3c04001410360030300103011010000903070080d021641c142000c501d618441840000d0815640c0c00016010f8126680416007080d001002803107229500c1c2030202c042d4101d4080c050707450082c01202142c8038440d1184031300b15002c0d44001e0b030050b650f04410000511084105a0520000300c42e51 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 146680233 1250 146678983 146679059
    0x170a090606060201020a0e0f030304030b04020d1e0204110c0d120204091e0e07031e02010306080f10180c03020f04090b0c07060c05030402031504080d09060209090c0f04 74
    0x40002c0d0030603900041c3c0f2403020410091541c41242e2a00c2d010b50100262041d842d2008021203080d030b600001d0450f0561038a00c0404c45942c2040005883e10707502180c5004000b10003e45509000e000300c80910454120b1000c86200d8490b40c10030007001e03440341d0580c2c20054011180d0806540c010100142400d588111000c00d6a009410785506c0310150952503102c0320081c450b0140351440b0000504405d030441c0d0714113804035010224a06144880e03150101160f2103078005401070464002526002000052015918405000c58401241c10001d50194100d07a135000910f00e0781e0806121103841c0d140d0f070280601a10804030543c2c20503115902031011881682001740104a040804e56907010241800011904884081d0080000800501001daa0300081c02c101c0921b0f60120f018464844d032528030040d00c500528030003401e04101a96041c440240d001e05900034080c0c41400c03107543d0361013062205200ea41020002e88105101c240400d01c1d1006103038451035200d80741003c80c6447c400d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 146681483 1250 146680233 146680241
    0x1f0c030f02120c03031f080325200306070e010c030c06020f030c040e01051e090601110d090302031902010f1103070c12060c03060e0a0b03100c03150b0406170a0906 72
    0x80f2081a41c80007062240008000c02490711211101d2041000c450820303454545034491424003640100b4400078200315152064240040309620140e8659035000c40340c900716050160f036000b18400d00542c2c0000340c07110302652466524040582d110300664040e41d4050701d411204250035035015500340301d826074601c41c010007503002e46140c1c840d5035142c81ca000740050f010001600114010b192000025002480d101c0c801104d0303140803104894103030b8403840100c0700c00048454542c0f2911402e00c99069490300040a0340651307000b503064400302118060400104072000c800240010080400c4420842c4a040b112081e0051601a00c0c40d01060b42c41d02c0c84120215004494904400395080c400c200b0507206040c1d9002c8141018000700d490841286030380c0c4d50080a809c038064a4a140c000705030350510101c038070fa070b032803403804c0120f01022580180181046101c072008965844000308a6110040503a0200d0303900b40d9804244810300f0b60050018900a0100c225143d12840c03481c00203045809 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 146682733 1250 146681483 146681497
    0x10030c05070b13050607030b060a11031e13050a0503030a0507050a0507090507090504051e07020a0c090501061103032406040e04031205160e241204021f0c030f0212 72
    0x503e8100d100904005080c0100980150b0a0500e0000030204981b100b2090301c151443c942400244002c0d00061a410344c0310311200191807003110021402d04070101405401482003601d2a00070ba6038882050298011a501600342d160b80284840040c0c14401e4000345900c81c0f20344140da41007603840c3d076a107107040044d41003250065207481c204100d281d4400400001030204071418003c80c1407403c3e00700a1100111113400004030008001040c1030b008110300305083d45d101000d03043c01e42d07441031464001c000030f004000c0010744030a864032082d04000160390080c8000305101500812504c0009005800300a0941c1c120f0024803000078000d94440081c3d22403030281d00c45241c410b5808045004480b0010b040b00d0002044c03038141005181c0c0490380100000042d25410365041812803070038203210444d050601d13451400142c07036403003d00000859018600c2075076441000c08919544409a000365010900003408918504000c2031041240e648068801d0050b10842011803501c60303c0da502440b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 146683983 1250 146682733 146682751
    0xd031e1d0a0302030903060a050705070b10080d05070b0106051228020705030307090608101707050301020a0f020105010e0408030c090111030409060611010e03040501110102040b0d1a04090210030c05070b 89
    0x4174800101e41401c0c4030300d50380044180b000701304900d80100d02400760b015085024102c800d0440000303410040104410014103094000c40d010080000c40c010025408844101c0e0760030402c40c00010014010429602d910b80008801d030042e568040c10700600c1100c1e00007104403105c203001902c0c20130328a44018860740c1e00450280d0f90380d103006003001d000b18505a11034400c214100703013081040d580242e6104c2c181d8201c400e0440001440700d444c05c0c9022084c0e004247d0551000402c003941d03c1d08031509034040c12064000b032095a0340d038051114001006ca40185c60074104000007002c45080c0c00041c4540343d814104040c2480254041a14541254001034a4160783c1e5101340062900481c0303a103210301000b8024000304464014050b02d034019481354031306000406115801e202e1081d0162400b0307002030700800340c990031000240c101070081c1f411060340b005a00701220303920741403d0007039115150300903154000c0f06001c01c0040300103080e00c1c00080b08000080c040f11000030b87c0516618000c003c49 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 146685233 1250 146683983 146683987
    0x50706051003050c030604110f010315060302030f0f01060504060e180c0408010b03010e030714030712080612030a17060103090b04050f2a06210a05090d031e1d0a030203 74
    0x1500e080c2c0c2c600841000b62622a03801201000300180c52035182300354800d41941c83ca1600440c5c6801a00582500d181205080480c03c0000c590140c2c10344c0a58828603046a0701c2c0701c039880d01c0000d020482428002c0500154040109001e4a030040c00aa0070b40d01e0050b115540311080c2181744950b81b00c0554800c0440b030800242008048000d000b013030300c1154120001c204441c000013815a4922924000030070325281040302d4207800c401401a03c001c1c03504814801c485404005004121143c1100d00ca44540c0841ca80350700b50f041b0000a46210214035180c520b045000caa4420a01c04c1005000c941099101c9210790000f55609500324015480b0380020401c036030408031240d0800c210100300300f003c511881c009206400b48050181061344040d02e0040d03503005001081d00c0307400d80e40e84007042e5210100c81403011054440c2c0c046407169608200f60b0b00c00b0195030030200c05a9400034907442c0c610640041000146c00c40e0f40c041420160240d10300307009040d90300901c9041584c1c00e00c0540241e000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 146686483 1250 146685233 146685239
    0x30c1a100f0b0405060306040c0203041703090108070503061e030c0301020a0c17030f01180212071e110d0806030f0627060402011e020c09180f0601050a12030507060510 74
    0x140381070064100c510149041604002c0494501d0000904040c801c580320302951800070b0007070089402500c40302d100548004071450f5403c0d0389501c58084d840c00118004009a15a480f407000c0d68066900240000344600541c240a1505510b4800041c2c1c1401a00d10110040d030f424401030485c4034040d100c414000c1007a04001110301c1c1c40d262456460281002000030741c00303050f803805040d0f500c0425014084c0c040d00c00504001d006001390505010309103010300c4801a0460344442d800c803104140440801c1010008039135140c49011200c14a40c805101d078074003030380640c5546501c06005001c60300e280105e2200789140042c10351f801810603070280c00d1400c4035180001040801000b050045c21941000e500003821100540f0001d000002c5041404201d40e2090011000181005020410314106403a01400481e02c9000c250301d01e02c0754504890300e81101103803a45c100d9070010808400340d490000316a00f0320200420403002c100040113010000b50281c40364038003c001c4000d6060b102d40c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 146687733 1250 146686483 146686499
    0x150b0406020f0c0402090102150c09150309010f09021f18061e0c02010804111c140c0307150f02100216020f04050412031e0204030f030f110703030c1a10 67
    0x50000c81c3c40340035030300410035502e180c0d0700010300c1c08401003428001200d41e13036818803041c070a0003012503581d1b115585c0403401c02003801c40c102660195000b41c0080141c0c1d4403d401c0c0b5811203010b460001d422851400004038200c0e10104a19400c500034186000c0b103046410810441c0070654000c040450700700c00307901070415041010b5840c1006107041030036401106e6000a031549000a100400440601075042465114880c9140341d0254280c100d80841c5042d1034000c1280982040350385c564450030030041401c3c0b40010303035101128170b2580300350310103101da1000319081c48000c5058020340c0700385040d1000912062000f4440300200c00a0260054820300c10407011070f01c44105148901d0500042c04049400000014020034030350400050f24804241480741c1c0001080c800301d15144045000001d01c00022240022244a961500709a520040090301c1c902c00c000503401c55980005c6080c0b000902072025107496034050680d01c817406142e83c40342c0c240d070102100c1030102d180c40000200840341c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 146688983 1250 146687733 146687743
    0x18050106060206070807020a080a030207080a0210200414030a080403050c0108070c1104150801060303020604290a0e030d050106020c03010c0201020f090613080a0b0405190b0703150b0406020f 84
    0x1481c0d0b440c19200e1780c100400029503903180480068081100000c00d0341106001c0d81c1158855640b06540f96243c4460300300180d181e80c440802010301c641410060060b211402d0307000c481d0050103940d840c0c1420304216440c00076079119450303140c151003095462004900840080d100039840341c8010014000711400042c0440d001816800c1070000c0600c044000460704000c1c607040300304c1581d00203103081450384100342d00380c050361040c1d41b02c0d4600000030040c541c0c0072901a1095001d4101c101004082d4940009000e510762085603c501a44000c5800e0740d140387c06c1852801076a800b100d09082800d03a98100701c417000c3e8058405a84440c5900302c4504003070052104c029450300003142003000c80b9404280307034860b00d04510b200d8403000400c108122081d100301d2000c0e000c0c110895108c45024904441c058170305503426100d900c6000019001d9500070305011a09642c020100e10254070790142c26809082183d1309009040403550010880c29080700c06003004200a500510b040e84031480020300701 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 146690233 1250 146688983 146688991
    0x1090803160c270b060f09222301080706020705090a02040503011829011403010f0e0307021504050a0603090f050a23060402030604080307110106120c08011802120118050106060206 79
    0x200d17020302c0014072000079a4140d0709403840945070b021307c03550080c41302980d503d04200c40f108103034071300421600c8a1264520074a44e500904003800441d98840b00000d030707a4000382c4500c50059000c48400d10440c03c000c10043d0b0000920318001d4105900c2d03070300183c299403008008a044038040072244090007080c4419604480721400798003003880c0c00082102148005010b056103c00c004174040046407000d42c40740d403c14210300c0080108031204403207507031603900c040303030503441100e20040100722503c22101700c0e02111002024032703506e60710b0140241d018001c00201561000c0c45403181c2408600c080c8505080c8500c9514200ca012503240800902d041c00948440c1060380103208020040e140024610341058200030119100d03503542d60100c41ca0306d086880c5885550a10070001480c0c0d40031400c0c4c205162213400711034105600c807078800b0700b214002002d030b02000d202064100c025003810002c0241400750f0b0000401d03100c4001501100380c00c014001102c040e950342d5008c2041c0c960500c9401c2e00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 146691483 1250 146690233 146690239
    0x20a0201151403070902090f0307031a01171908040e0a06061b050a080d0b030f06070f0302030603030306100e040207080403021003060815070207050a03120e01090803160c270b 77
    0x120b5066203021980d602d80d14050601c489900040542031607981e4208020b0030a0020200c510480c0c8901d0b0004500b1140603004012544400010904600842c40c07c3e24a00d04000140b1a07000982000900e0520040b07096412140400000c110303035104120031031058524142c0810b00528110b001030a140c0d40079001d09170103852600c0070000401c041054940c5581110b0b42a4903614540140001050141c0d0450b0741b610a902c1f408000f2000031650754400d03034098441000c03003459040c0a806070f100c01c5071603d42c03540041001030403610708070b6100c0c00e4000440c43c002c2800d905d15008101280c0c4201016035800002050810440ca864807506080112910b020321105240580c00c41c1d9500c01c500d510b11086d14030300001101a8801c00c0880700a0000621100d07250b81d50341440c107101342d0520902c2001a5542d41102c809500501810045480c002c00561601c01c1317100740c0c04c2d01012071680c00c603450001343d00f000035651620002410b414060040403400203400484000450f910309142c940 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 146692733 1250 146691483 146691509
    0xc0d030b0307180204150f020606030a030e01080a111b012007080c010e03040e0403030c090e060d030e03010518060708012303030720030d05041a0a0c06020a020115 72
    0x103060300e0100d0000111080054080c406641d4000c5060180c02140c01c0100100b041003064500640d00c40c030080c84414445c1c082d00c2654542000b4543c5803042d081000e0040f501d6050507900d254401e00b121540500038400004100700111110442588000708410303402800c080e2000f9500c00a100e003144200301c510840454002c05900c0030340320301138030758050304c01080800c2c0085200d0302900a40402c0e0780c1601681d0340d607a00d030030307006c101104182d031709800082c9010111000c2e10f000c0c1e020802034400402c5603240c144d907200100003951800c0b0708110300301b21902d40c0141a036142405581d02980700394404941701002180c0311850303c00000c0045082056120040102c2000171184441010b4202e400300d50341401c1c01c000c240340d0702c40d074080100400c0312800540c12600d810610200c00400880944160711140c0340211583e010b24060503422100034107042211086036002480d4524940c01c08004400550b00d03950201c2c1c100d500c621003d80d44541d824080c031002d2303840540c0500700c0808494 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 146693983 1250 146692733 146692751
    0x1050f0702070503070e070509060c07030c09050c03042609041e050c040b1e07020303160b07030e0615010c02101e1e031505061803060f040803040308060a030204050c0c0d03 76
    0x21606c01600507803e10000013501c8865844c0c440c22a80e01042c0703107003100c0b8081c2c1d5910300031020440310310801c41c52a01d13000110b81040129421280290740004c0b030011040f840900601b8070000100c0c13454001c3c10104020380242c1c40d0340c000c00d00036103506411011140780151641e030546200510705005c040c0104403d010785000e003419a0b03d008580f14000c0040510b140c4041e02510074550b01a515100205c0d80000b103122003014469014464403140d0001e0f00d805c00c068003036880004403d10f60341c06c07070b0000407581c0c0031030003504988080500d8180c510b034490741c0100e007201d410b640b490320000f00722840f180a101903000d10030401103014030309504414a500281c0c2442d2481d4400003003015103401f00741414035900b9640740060080105619072b1400c2e40c1200407000c0258003a40d88c040e024010000d0103030302c032034000c591142e90882c12903840d555581d9070460300090020091a44203800d07410110141c0c96902c02c0a104040646020390740c2d0b003610a07a44d180862200000c0c00309400c0072070300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 146695233 1250 146693983 146693999
    0x1314100905031b1504080303040213060f0504020711090c120106080c03070f141317060c0301050d06091a0a0510030203030f0d060801240e0f01120503090301050f070207050307 77
    0x7800d10304200080e403240300b07019100040000030300c07018501d00108085000306e010103000c0025400b55100f120b0280e00101040580340a950461085040300c0d070304098100240d00707107a0001d1005512070141c0d19000c000400000b1200c170403d07034003805ca107038010800766035071b1440040040c050704c820b08201b50300307183c2405030006a01c4002c20a00402010b4412409000d00a0510150450001a20544840340131101e00c1e100070082c4280e0007003000c1da1010200c540c0c1c02103801c901452680100301d1440c1e007007805014610740780100c1241c0070b87c0e40720451804181d041c848800c549001040011060510f11100346c1507620181c1a07140c0000204020001071f6400401c0b125029540740380d0300c4e02c1ea0031300180e03040144040e03448210a542020503210503641004a407050060710000900c0b00c40d62580c415140505007206c0c000c03070038001c800041c40340002070100043d030103126000703e0345011044000f003420354006032491080300b10340d14180001300f6018045240a03200943c01070155601d042d41c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 146696483 1250 146695233 146695243
    0x1e090803010605160f080a031d070501050f040f0306050105100e010c02010806040905060a050a051f05040209130e0708010501120b04060c1e050a020d0302041d060402131410090503 79
    0x360000c3c400001020032920103803d40301c2d0001500045420204465801c003088a940a000b107100020f00d0310440d011910310301c083c14017020301a07400030b1042c0d60070140190f9099000c5480002d030391009000c0010365450108001b00914420f0f40c02003a0340d4034003070900045c02a420f00761002d01c41c0503808803940303982c000a101060754091074589020348540020800400c1d04c0b40000e80f00b07000b048100401d130b20a54200070b0140c920200100080e5480f0038a0582c105134000c1c4000ea82d40d60f0f114104007c0c83c0540203480801401040505000108039000301120380d4285003602c0d58102c20400c000c40d040a01c2000d00605074898141d140304039644d1401d419400090000b040302d0381e40c1000610072842800700441080340e0405104c0700c51140c19010301250010042800144100c3c3c0d9004c5001e4442d009440c200c2d01c0004150344000400316028035100401440b85800c25800d0201d03491240c40c058819008001c02d02e102c441c40016401170281d04213464543c40c080c02100e0108002c6038500143c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 146697733 1250 146696483 146696489
    0xb07060f02031501031a0409200405060607060f060509090a020109061809020f07021503040b0112030c0b062404050102010b180105090a09020603072616050901110609011e09080301 79
    0x40c0001c3c40f0417240d6440311b003040d00c01210315082403919900c0d80801180c1c2e1600c1c030500410381000c4110000301401c01054500480355035800940510000d0b00150301c98004c00703c81002003402082ca240c9070000300e80d405604460b01d5055921070750031603080d540c026040101401480c6081051100d165070082c0300f05001c0e01c286c5408903400100ca03c6404080d00035500195030051a92500ca800e0031069030841d002600c0540302003050500004d84000c7c2c003480c0d180d80d0359054036044500e0f403042c2c0350485280300040045070402601807078034841c51081544040c0041400c1d0440341c5440c100000242180c49102507240101440d0b50764000c40881342103540d04640044640e021580d030340f491000003138040d512001750481800f00031b005825400c0809050307800341c3c071340340d0010700829800e945200e10030941e1004080100481c0006800d1721405c0240141601030400b580c0d00d46030400068540b1600315088440c99540ea0203000c4070640c2c2c6030142c01003041000042c41805084c1d19440c2440c88188 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 146698983 1250 146697733 146697737
    0x180806040f140d0e0111070e0a200a0807050318160f322103180f1f02071d07110d08060d02010903060e0a0b06030102040812030406090c0b07060f02031501 68
    0x920b03030746c0c4185003c0159401810141e00526518200a84041e024000300d1138002101000600d110441842e400d0503203928403442d55076240142c0769a0026603c980c005085018101c80007244405540b00810150717044036002e00d90f400c400e030310700910095000c1c0c66420007401d145e016030a2010500f80381e000008001c03d00d44103245031001c0c040000d40344060b403100c28860000c006141c03520070b510100142c25980000480d10400c2e030040c40c1042200c8840c1c01c101640f010305607010b0001f80c405d281da003401c0c00505004a0354069120311200c0707102e04044c4002e48080c0400b40030060300c60350042008020209082c0104250380311403074041d18103000245520b000d904450039102c19a071003540041c008540245040000343c5e464090b15449108006095613900602c0e00032071a503080500c21242121940c001070641c50322084440800707540050800e4450fa51a2240180030400140e000002011020401a5950000d1400c1025103000ba046030f84550710510030030058580c480022401d8403424 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 146700233 1250 146698983 146698997
    0xb091603080d02040f060e0f18040609030207080a0803160e0a0b03091603030206090d0513170102070203030a1706030307150203280204030c15090303180806040f140d0e01 75
    0x30718282d8000d00850744803c4450480d098001060343e000410000d01420580398180204503490030720000741c0b4598103000d5140d084070b0002d00814440c0d40250405031207031042d904d004da41d42408902d81a0407a1060b038001100006202041100c0e180c9050340c40607500b480005c0400001c0000c00c0391000d0311442c080680d001000031018441405190b13011358242c0c10144090b034807030400a6a0788030880310000e06102c0c0404001c0094002d40665a861002d010900b10450403c0150301904c0b04402d404070596409001d0394005070781c107102801c448007250b61844c0c084003115180e0300110801a00160203500100000030114032092003142c0c1440d035200703000d641c94481502a1210820301841100d01d1015035100301c0741601d280d001041101d0142c0007544140380c6640b162449803c1c0c0100010124a555604000190048200c41e032518928800107884c240d40b548003e0030721408036002c490030a800b519420422406072502070584450000421080c041c071800508501c042c0c64285042c0498 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 146701483 1250 146700233 146700247
    0x80c070311030f040618080304121704121e080901142b0c0921031103041d09010c2703082d07080406050708160f0b09160308 55
    0x1241003140300d075504000c8941d01e805500c80424a42c015016079400107078001c40507516102c8500200c020344003201c01031403500345400c0345100204a1604215029000c0080a90702401c47d02e01800080c81352b118030000c0030845140131042280c0344d60300c2e01d403180314000003800803030084001da6105110070700b00a002130000c0001f0075003502030340101182030031288007002450040c400f8a19070740c81d03941c0c10900401950b00c3c81540c510406008600340a004030104103c070b00d00708140880c026000742007802e0318030410401e803419a0300c40c0d0403541c0da001038055030105403c1da04188035401801003000304405a03901c00002d1603581e0454400c5210801600a44c0d001c54000c4840d00055134403130ba5080e0703220700c0c000d500414080c2102c8440b00c100920311120034803c02610403a80790b00e50104100e8030302400d0510564580d04010740c00d498844041c400140e0f400c40c400e030841d94a41c003c1910802c1c10320701d031920305000c5d50000c01c0d42880e600020700c5000440030842c000c81c1a00d5010390040e0319124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 146702733 1250 146701483 146701487
    0x2060703090504050403020d0809030f1c18050102040e0a0905060a050a020d0921030c0f110307020d0f0c0504020f04090506060904060b13060206010b030105010f2102090a15080c0703 80
    0x4903a0b00301c035500a02d01014807040540002d20080380040e1511844219a01c0c140c020707490b40203800700500480000c001c0101280c020304240f480f05040c00d030303001801e40031003e076040d0203070b0640e013007125169070010f8148215950341345401c0d800034103500180b0543e912540c0d1a6190b00c00607010b40b030855141e4011691503007481c0c06440021000c0d080820643c1000d003003d4000c0c90013003061251014042955407141072103400307495401c202c40c0d100c1400b84000c10b80c003185e802c50034102806450105011090059403200007201c0401c0c01980503d1003580703181008420030819922075485103204104c428015500e49040d5021a168660005120360713954000c074015104030201240e101e440d04c500443e04449150181022020720740390107481315202c4d13506a0345d03000280644422030f40240010402d41d845601004502055864260700541070040040c0490009001600510340c010540100038140f018685004101442d80c22070070356070040010340111405050034040182c0002e44206240c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 146703983 1250 146702733 146702747
    0x804030c0209150f040507091a12070e010813051902010315030c1d04050712140105070503070201180b1302031c0f03060e0402010e1318050a0c08060403080402060703 73
    0x9401608425040c605001c88040e600841c00283e40710b01e00b48071100106007864030034284220500d48a9921f070078204074800d0040064488501c040a03401c201c01d0008101c0050014042c1000d5219094175103c3c410014084170001480410610400c001802c003003080041e03281100711100410b46030f00515400108c020382014030094a6450004d04000200070035040490100d526030b0072010f10745150807000d11440c42c0107a4015080c1d44c0080020303c0134010307085004501038403a1290414100700c4402c0709080d20300c2101c0791800710b10b02004002a00b5020b010b000000c140c1c01040c4034940d0115600d01e503440002a203080382c002000d9101508645041100061111001e00100b414480c8490014580040b08141e1000a41004000661200900a50340c0140e505856543c1181043ca05000242400c01c4031755002035100d1521011106208903402c40c001d01804c050007000b046070805181004407640100856403000b0100004240d000c1078071604140d040360856500c200a0800315125 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 146705233 1250 146703983 146704007
    0x8070201091a09070501090315020306060706140103120207081203090712050604020f04020306130b03032106040e0d0206010b0d0b0402030a05090601080c010c111c08030103050c0a1203080403 84
    0x20ba560900802c410990520303000d00c56403058003110041a2590011101d061b41880002d08003101003516005080c1d4a401842e80004044d00403802c004080e00c0320010340d800c040b960072460f4124030051080c440134034501c21881d581c5000030300300c262900c070009984000709004181c51000c041b020444c07960041c4210002040ea440384000b401e50030f414400e848010956040f8403560b190102c4031254100343c000d40f40b207440011b2600c0c0c1c3c012a07881d010b0000d464081141c075490b000421001030101c03d01c203409103107644141d034280070790f2038000207010403525051080440b03580168103104d016680021900e040d6094001d4031a140d40308110310002030070181c1c0540d540306e40040100002e00503a0f03441944204140422070340240d1303079088515100c003031090055000946a42c2460301155184414004065003d42900012600300460401d8030000d103408680003d80000100248030003000709904a0b54111001d04040d80713401381c45003841c0d100d800002d06200c01580001c1c14075002d099400a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 146706483 1250 146705233 146705243
    0x1021903090f1703090d0c0804060e1801080307030806030102040f031410050114010f0c0309060e03070801060b0c06010906060e1516061b03090f1403210f010b190807020109 76
    0x203c119640c5105641c00449441d007070b9126010901c038100b44501c3c004401c6c143c00c070241a20746414240c007240d2104079151a0360300003140f00400070030403221780c04050003000804059610f800861400610b801c10182800f842603005101c12b000201d503c2c880340301101d82c45419044419034803600581488160701c1448045c0d803404000050111004027100d000caa02640d40074400d00c0082c100707480089143d00d001e80054107084080c80014090990310112880040442c1c5c0c00d103503248440d81c00c1d80c0881d081424002c90103c2e4888102c1c00030803c043c05441d14000511400d03041440080030385011544291082050350040303182c9803920313130441e800b0031030700d18201c0009160b509100b4050400c0c029145140200603c4807c1c0d120320a10a0761225a4850030a104010352500e440c0d0f8003180700c0500d405103010400940d036441d030740e0620224011502c0c1d00c151070b007407802c091403902408050703205a1000300308201d80700321813400081d9030580341e1450900c0c0307a07907454407402280103107284540204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 146707733 1250 146706483 146706503
    0x304090902121507081f0510050d020f0a030b06030106021002030601090e0412021b06040306021806030a05010e011502031b07080307080d06170703030c08130902070c0801021903090f 80
    0xc202d030320385078042c82040513840318000360706d489902e02c99a600354802c0070002802d0420074009850198040c88450303480b1b25005085c840c420413180c0482e4040d01c1d00c1181018000743d070b10a81ca03018029681658011607900b41158505100652a840802d001a1105500000180240e0f01441d0840007509003c820740307800b0302e0645400f8002c500c2038920000544961031405944160303003800e03c000c03068040c004a06092039585d441c00a50000040d080c148103920b1000d40c829101c1d40040c5114150b0b0400200344e65141029a078800401a001500320103940011420800d070000111410481c824001c1400c0c0c5060700720039424403149400c0301c10a4080000c01c0c0742844101e40240c4155840042c00700500750746d41c203582d000d440c8104401c6503280c125800c2000807034020074034007541c14002e808051034001c6441040c4408030b41b03a04124046030380030070068180810820240301800e2044000c528110a0220071141000304440c064105515800304800704024280458821544458144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 146708983 1250 146707733 146707753
    0x20d0905010e011b09061b080a0216050d03090e270a060e1c0c03030e03040303050703030c0c02010818010603060e0a0201140405060304080d0b1005040609090e030409090212 76
    0x1e010308000500c1140540c2021102000300c941c1e403c1300b41e0282c0c183e0f1039900009281c000140c1e58040724000c02451054a0a800404620400002d001c0052135502030401d0b0041401e070750381c03d038030240c2001d801a8040301d401400280c10512103003d444094120207215614042c0e00458404d0b1010405d04002421b0fa0201803040005041d0340500c2c070915041c8480f0030b20b102169a9036503055603c0a000001c0303402525510300070480000f40314000d10700420f41c4c092071640585907500c00e40c421400140d0008041090540c1445240a0240c440c0b0344401c1c501c1c0103800007440207102911900b43c0311003100d01e940080c1c0342580301e10021030744800240800c2440c1c1c2d03507164036144061743c182d000c1070707120841c0010b8a02d0303841200c0580d40024030b080e007503854544580100ba08440151a01a50380d0f20110855030b59501208480e040c95507516a5214100b81000b0100c1c426079209180a90901b545500c0f0b4071408000d50f01600c0c034841000500680c18000100580c203403401c003030628010b20302a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 146710233 1250 146708983 146708993
    0xe0a060c02062a090103020a120e0312090613021e031207060b0d030507030c1a040507060306050a08030904050c0f070602091c0f030309021f0504090f060513050a020d09 74
    0x91281c00100302c1242d52041d10302490391040f03142c10300c540c0040c504101145196001e5800707000600c0b01031034040d4590b4914040032044402d085038002c29a400854a6125824405600c2d58403026150142080f0305040f0400e0880d000781400080c8202c450700c4c1656480b04283c031040c014140b005044603440740328520107980c26404400150350301400e00f0741e19a1241040d00c0c80d42e4810b6410b50f5500d185c420903031400c0f59082500c80e0f04a0340d010413403c554048241d5601554050b5000c1d10251643c0c500d050005021916242d0025019540780302d01000f5020000c000d481c00c0d02010703500031070190b403001c8481c246449082ea582c0c1400002090440600503d07502070102414107490304210041480d4030524030403c407260040c001d420400c020800030340300b9000b02d400e02d407014001c62440310307942124288030300f9070411141c006503011400300020081800707000448044140104070b030a08240c04542c0084c0c90322012005162580c1c042802483d2981c110703100d59541c0e040400c40300300c2a10b84 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 146711483 1250 146710233 146710243
    0x2030c0d030222080d0804020301060504050f06030d020606060d0911030601080f0f0111071101030b0909010902010201110702010203043b010320031c030e06130308010803040312030e0a060c02 84
    0x21006410000343c0020745500356240d80c900a84070314500800316140301c041e04035800380c4000c108980554032203800043c6520b8030301983d80210071480c01c1b450303c0d203840c20038103240c0070154880c44115404013050194540390a0112820241038240120f80740c04281031004080c000006c016030075100d840000217000d50003041c0c281307801c1c961030140c44102000b018520702341c0380034605059940d10b040000000003002001000900c1506050110303a08008000107038142108440c005032036519188000110340c0d080c0700324014503131a452482d00b81889600002d689002c0d07406264511b603155100919034a20100d4004251805050759902c262021807220740d00f05001e00c4200c516920f00d40d03e550851701c0d807003580d001403100a8010110383c07000310402d001c1c49008000e00c400b415030b54100000c8110b0180100345c4164200042c9104000031460001c0c00400140d00201807070b0024041400020740d40104c0c9514001c170b03403a000c41d1080b0388100d000d04210044074001e0001c0e00e0712000001c0d0a8000c40c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 146712733 1250 146711483 146711497
    0x9040b060112021e190509222415021207020d0f05060702030706060b0711100302040b03090607020c010f080105011d0316090b060406020a3903060f02161202030c0d0302 74
    0xc20b2410003128200b094980f4000e501c20142d009000200030704144064150500d10102c0c005400b14121200c8144100800c02c2740807407209000c0019800e00c001880f032644400c1c1c0300001c1c4000c0071b1046030741140d5013190007901802441003040740b65034014802c0c0418061420758104080d5920b80c140004081e40e04c0d403020404a038120304080d0000b83c00e40042056402c1c154010b01c104901e400c800f01048a07204800d030746a4180340c0e0038000464520303c10005944030f201800700421540c20161406480c201100303031913a04101014803001e8000f40c2c001d0425044a000f803d02c0039008885a140764500c1481d0a6103d0f01841500c03010600c00300540c40c444120b0b10348210401ca582c08101c14040300e440f59024500240e40b00126510000c0c203c103094184800220381e1140380300e941c808a407000303005003620300c8006a9198038207000b4400517114480074204445000c501c0d010641c83c0c201c9104d082640e010b40380300c001003041d00c0010300a00c11200403070405010b4400c800d03a100b00140083d04484c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 146713983 1250 146712733 146712757
    0x3100b030c1f030905101a0301050a06050105120a020706020c1005090f0703140f070b04081009020a050103020d09022709070803190c120503041109040b060112021e 72
    0x198445140d400d244802d54075800440200c0341d01c071072000d00290040c21124204407280d200e4000e074050102160311844c00212944144004c80784d85010400d425120b01920701c100072071400c0010001d40c0e0300700c0c00316400044000048441556201034800080c05501d40281455000060841e451000800e03840035402c1d0f506000c0000380c440c01020360b030f56035080c0d9000040798040c0346c041c0081450500748030154809501112901c903144030680707082c44221b40c0b140341c901d03002040c140700050702030040d00e1a410680d9010003940d21142c001810a9400b031217900d052560008070aa1a105075800a8410fa90081e000c480800c08400007009085c0380b1280b94414295141d0224505100125a030310488030104010f50502e00d1140104014076403c0d5031034014485d40c03102410029240040300a00540745855050316131030141401d007862400b40c800c1c03900c1404001c2c10031000460034036055421000a01e440e09140d200da20340700700248220751000e200740c00c189041404c02c0385000300130701b2407c00078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 146715233 1250 146713983 146713993
    0x180e0103081909060f0e1215040c0803031513141611010207080a0e1c0812090c090a020d0b03030c060103060e03070c14130f0506040c020d050d09080903100b03 70
    0x80101182c2c01443c5005480001d4054405500d00901c01c1048040a910007400a0402e0400c0003c00785408003801044400028090400040c068100d058070018010074000d1883c0d458072916072103902d501a50041c2c4034981400e24601d07920b015502507426079486548410702400c00500c1d8480d2900d07081c01001c00900e4032402c0004603c018000e9034407440c0d100307a80d603040a01da000c0076540b201c1c0c0c0001c081c0d040201c01400346c500c200040442aa800d0042c0d04ea2681c4c2d40c0e00350341055178a00000c00c1042c003640203041000e0140c40303d04541354040c41e0440010f071500342c03003006503000d00508003296034140b00114401100700404036009040b01e2042c2401c2024920f480100da44030b000306070001e0b104c082019410002c0342502c1001c1050302c01d0041440c030303c42c0034001c140f804840c903000202c241190344104000c42402c092040c0300705d080c07450005003143c11890100034424410500e0004a05444129103010820304909903080c03d0401800da032038581c0d0841e0040024114014164882c3c415 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 146716483 1250 146715233 146715277
    0xa020306061009050d14031201030b0c0301030807030e0301110a050405130605060307080a091e050c01050c03090607020d05061311180112031808070815060907180e010308 75
    0x209100b81d044032001501d50102c030502d00303001c000304050110010707100c034803a64801c0303003044006000400500ca0f03151038407413141d4103500309205a1013008000c1c101c03e940800c01440810142c0085c2da052682c585017010309522040b0100303014280d54150104012408100d03441420780000191007910b4081d00c0710540c070841c0c19030203030070b0700c4c06846000d030420010030209001c1c80c82030300100e074030411894011810343c519a075810314117015200010100c00340d00341800704000c0248864911080c0c24078247d401d2010004c0c0c1c0540b240318680080d4844c40001032481c0c210b46801d40c44900843d0003205584143c83c15817102d040805c0c441400b211000e070046001025458414203da0548400010340d040603800c00d250706036404100da00690a02002441c060b92581065401c00080c14400c0c01910089140400507072a01b410071100c90b510005480070040e80c3d41b0303011241c550250717491608a4184d1082da03240d03000100c1039004240070780e0f4440c0010003807210001c003c000842100c19003000f242d40d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 146717733 1250 146716483 146716489
    0x20406030f06060c1712040804030201030b03060f27060703020903061014010503060409061109100309050a030819050106020304140105030f0601051309020c0f0601050d0c06050a120e0a02030606 85
    0x10901410f8041000c0390040c8001c5248401c2082502c03a0560801e4a40440705840b00900c4500710f07022a0304080010b000d00031568140522179484500380d00600d850b08001c925000b58160041c65070340b50000303203400c41034000c200d5101c4617628010501903840b5030900c034400401035486210054060720685020036000390071492b0368021904a00701c403142e03468040004440590020380560360140e101d85007034021804e0b510540d401408042c51241c4e86440c02c2d014444017035500b00801061601d06941c00011840103d50710500176454070701044c0030740d64008146040241c0c82200c92885181a001140898000005000b03a0f2802405001da40300401c00440e0148000c840b011030035841303076000c01c80310f50241014040c0c10356900b1301b0540c125120b42c0c90008a07040820f03a23090650100d48440c0c0c07411810302140f8050007003900c8884240c01c054a4240c206119841960100800007460510051107039000c00c07281c01103081c041c81141e080541e0b0070383d40c0960500c180c1c442d000310004110245 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 146718983 1250 146717733 146717741
    0x102102040b091603020d0e0f0604020f010c020604050d030c050d0f080a05070e0d05030c0f1605060c070b0a0e0913031d1c14061e0a05041a090109080a03020406030f 72
    0x2a441640407903e590a0000031401381d040003180f0164640c4681111104001c14020b0291f80d05010b0010025490f01c0d0040244003103d42c1c80850501c080b1030140005030315007400311415181c050741d07104c000e80514507080300d49480036240a0030500603d40b000880d294811301ca140030101d035689009040d141c03810000102d61003921094040f0b442c410144c001c40c1840c15484002c03c0c012004d880c10000030710105400e00601d44c85101c4540c01214540325084454a030800140a0a40d01541007440041c81e195850445010704da440140203d00e101a451188055041451002d820340b05103007000c500c1c0c403040c210060000c5000c500c8040021510b072000d00594591080002c2036144126014402440d84601d052800d860b002c40342d03c122090980c0401503a400344c06228840010a01c0d420111070340c0f010050300c00659507007000280000318000303654001c00800540e11910007038440202542c01041d2058004000d000701203103000e0380a41503405882261203a032000e1000581e00002e0340129 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 146720233 1250 146718983 146718991
    0x30204290f090604050702210a120b100813021306080c04050609011a070606060f0f09050a140d05070611010b012d050c030d0219080618102102040b09 66
    0x80104840081c603d49482d4001e10b8000e00f0320700598418038000d4180f6000c885100041e00798503100085c0450b4403c2c6d0241d0b1a250003105110700b0058510402d00003030314071182011880420280b44045400d481000c412002841d90040004d540003103070350380c180003a001c1c9100c2d204103801000c035050354034102401000d04c6901c0042c0f90307000d207170f080c10155409184c54103100e0200344024000303600080d81c98850007024044540f601d0194090702e481c020600d84d8103000c004104041c0a01c02c10458490007ca83e05841d003400a1004c40c81c0f2000100b600700c01200c802070800c2c4142800040c8007a000140e1a15120680c402070080481100064030013400c0f400b891607c86110003403650349940d101100360001c400c0303803a249141c451107203000381c80c0d0382200c0b5411260301d0780000d0004d030304031400720701c0d0a643c0420700f450286840c0c4440082c0058650f0040300c15020300030800500740d852a000480041c00071450941c0d4481c0d1000446d04810641703035000c0b130003603240019480c5180352200c400b40c86 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 146721483 1250 146720233 146720239
    0x30b0c090a17010207080414190305030414130f0501030201110c090c0901030207020d03170a1a0d03050d060306050910381008250c060b0a030204290f 66
    0x1801d4a0000700c0303860040d42055000c62950b081c03040000007003034500200002c050f025280421071600030104111504c2286400740040c0346140308000107103000c020356013116418030840c403804028a011420101104042c9035841e49003404d00c104000da59480141600c2c004c3c0d0354a40ea002c01041c5a680e40d811490303809600520100005007007040f5200103190a0340103150250070111300343d01284200c620303404120081003c000d4045a00300c0c115820f00e0f4041e400610610034983c0380861030301d50903600081d82d4000c3c41c2d24070180007494010001c83d00c00040500d001c101c1d143d6282000350003801c040d0b030384100d680201c200c014107000050145007001c4004005001d011032111010100010300c440d5020304580300500307010200d40d19141c804100003a0703521500c0d9a40fa140103140c0d520400d50101d0800038540c5503000801592100e1950301495000714005041480040024000c1ca0560300003036009007400381d40d1001300320315031075000c1c819211400020203000c40e10400044581c2c0241440d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 146722733 1250 146721483 146721499
    0x6050f010e06030a0609090309030b070806010c0201181802090f030a0c060c0609170a0e01020109080307030f0e061008060705070b0c030406140907060212030c040312180906030b0c09 80
    0x1d107450510000e60f0803054840000542c03661b616021800e072520060143d0101d4280c80d010414840e000311400c0e4407000700c1c904007400b4074006001a01904518030060304000c1c902183e1042e1005105d8488050300041018141c1c2c030f24a20328440180d03015a41280c0a5440141c0301c04503070800041804c081c3d40d000c5032030350071b070b40c03d10303201705c5240c4010201511480c0d01e4506010115584448280c0f136502c9881c00300381c0c1e910211a01802c0d2503400d00c0343c50704680c500810138001c1005003050342e41005840c50041496200855240081c0c20b0f9411000700e10701400041c03008502c1c840e80c000742103c0780c0c407060721002d55a049099681e03004100014001c548020f00181c46044a10001c44d44203220300d4000600011b4203449800104040310304008981c0511024000d00340c04001500310700040c000300c41c0c510724104100044900851200070114400c400780d0400d00e41c003030100480e49004e401e4085244a94410600010b00300c24801510307400c03860300220310200040d4040740c65002010380038203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 146723983 1250 146722733 146722757
    0x7020a08010e0c18010605130b0319050612060f0601020106030c08060f0106020d02060105040b0d080a0e09060a030312020c0f030706060e070302040302010c0f02030c0d0b09010506030d02061b04120302010f06050f01 94
    0x140312035200301043c055500c0b0b040380102e2700407003120141d40207075140b0780740290b02c40b00500c2c100d0880b40040c0100e889520b98001c411403103480001c0c0c00da44003940380442d0b01c403904c9200040c0c3c003418042d000101280081b0501090103070000512900c01c0b035407107908102c40c0e41c0c0c1704c0040c0d881d00a00c11184006070800d1005008508042e0441084800e0281c4040d49101c85a12105125045140c038000090a20441c0b0102e502d05904101d8002c4001c81d988109140f441e58054800c48002480303031003013500402d031030304290000d110a00a064501064035600d80445c039104000b0300d0345002d4508103510010116904170321920940d000d5136810303103a40031031f4070b6281c490701a503907807001e012641403051200350101c98a60940e0704100520900c1c0399125820601c2250b42134a10007440a8082d500c4130380c0c2124069400107840d50085010304401460308851401c058280c810b98000840c0e40141c5401038080590540c0145e442c01c440d8030041108644500401c603640552014481c00501031180b14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 146725233 1250 146723983 146723987
    0x180302240f071b0804061d1507030809030403081b0d032c0708011109120307020d170d1503050c0a030c180209031203160908030d05060607020a08010e0c180106 70
    0x5010f0401e40040b415650f04a5640e80413025840b50300304800140002e280d01c80320320b100ca01c408004100441e540c0001c200300011501850150500207420004100041000c03102c0c00d2044901440d0440d4402d030359010350102800d402e009882e0f000c500ca104541c551b0255501c24843e032040709240300c8001e04580b0003101c0000240341006214503160040c0c00c3c0003e1a484240301c1d1420000d1400305050f02d400c10b1070100100c1d00a00e21001c071540c0c000700650001680c0300042c00b030304542c0c440004e1320614600e044501c1d5a01071030325400c10080ca0002101203821200000000303d0784200203c400c07400c01c460610050b140c4500c0001c2c80c42130030030801c3c070101091014010982d1b240c4030004bc2046041c800013460800100b40c100103a9400005201d44040c1000b18600c04403260b081042c1224a0f000145640c0c0c0301c0e0000e00c0c0d600640d100c021501039610602103071f42d5650010a40303407140340c83e18226402008460351030f08140c85440400c0043181080304001c411700a28258403601a032a0803c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 146726483 1250 146725233 146725247
    0x105041110030212010e07030c02010212010504090317011404060801020702100e0f060d0203070806011d04090206040b1c0b0114121308130509060111030715180302240f07 75
    0xc801c040c1502842107220f9280318030740160003080d05906c2c545060400c03480140444085504c0030045900402180e0b02c0c844003000c2040c1110300580e000a0442040c1c01c044644620300010f202c80c0c80100d900016402c0040c50125891000854040100664400f0b045080b4030400d840203400c1003400795040201c9000380074005806001810480440c210314002031130381c2e40200703040740d811a40030051103d007503404540c4c43d44c0712000382040c00610041d11040342d4410122090700f84660344504424045480740c0058400420b1100e407540d454a441c15842c0c210303030100801303125006103080039003a51588a420b000000c4095504407600d041804031025906400042010210640442d162400260321200034440000029a03c50780b032410700c420040e0080c006415681001104010045098400f0040b100140da02038280c410095281d54104054400c03200c0421a0702c0d0400b040a0506801082c0c2040070b48204c1004a42070000d0500c1b4021030405940d80b1a01d0040308000031030060007182 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 146727733 1250 146726483 146726509
    0x40c09020c060f100f27090206072607050c040509010605010c02060318060403090f0503060402060d051305011815020403080a120b130c080f09061f09180201090801050411 75
    0x7100740c0050316602c174004c00c14002c3e4454044014020b20003c2030344180030403551103149120050040c00c0140c2c0014000c0d001c1d0010140c54200032004040284080c241520760070b810341080d8544070301070340c18481e0721a410348040703c0c0200c2c100b00000d0074000b130620905094410586400c00912200c0e0240310040c0c00003404000c16081100c1240d055070b40411085100340d103c5e944900c55603080c0608079a000303100d030344418001e41c09601404016642d039010b0301c1c031b050300d440703400500e81c1c0e076500114100ba0614203001d015546445010030807040106d001e0000b0074001d0540403134240400704040c0807803142c0c1c400917006003070074810061414814002032a550000300c801003440021113000071070380310b280c03038200000720740d01c40410803100d80003506034bc1d00607805a0032820501c0c002c00c049071030741d10007001055140070f00c5031150044602400c115026040320b10080180c00030402c2c20158401203c1c0c02a0b004c45c1e5003a400003546041401480d1140364000ca070069091901700502081c0040c3c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 146728983 1250 146727733 146727751
    0xd0507020a091503020a150203030c03070c0f05060a06050603060f060c03040b03130624050f061b030a0e03030c0c01030504060f0c020705010e0604061b0201020f1005040c09020c060f 80
    0x20000781080c2c01e4010b005620b44000301c1802ca444c03841c8108486420294054200314080d44c18184400e0303004020b0320b48c410b42101d45150344e692091821510b26041c0c080c01001054050020410310900140803441034107024001c10200751210b0411256000c100c0e00d190344183e14040c250114180003000c2d10f40404828126818a5100d6825110035001280c50703c00200c00c0120344000c0c0150341c020604004c1221042e40940c0f4071031040c1c0f4405280f917004050090150340e1034881d00761103120480d5503000001001e0710028250710100d5847e03501a001800001d40d4805000382a0710b40401183c442240d0301000703050344c40310040150080d100040041c2c40d92603a40d113240e40e40d036140d4001c0411041446d030181610504000c005021151410700c0c1ca400380f1024403080c03020580041026034400e080c10554590801e040c070040b440c3c09a01d240d900c02d18020303040c0c0c60303043c82080e4110718010b0348100c811054070707500e07800d66100724010582207000d65400f000115000384244074055070008541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 146730233 1250 146728983 146728999
    0xf03050705120712080a02070b0711100e0315061207050102060a150504020f090102060a06152001060e01030b07030203070e060c074a0106110f120703020f06090d050702 74
    0x4c0d010821003101854801e896001c00001c0600c0101d90501181c40a80002e602c00d5081603c10386504250f4462036005a002e102e0010719909154052054444c4004d0000d04039070300b4802c561544440210103541c240d0181001c0d0302e9400c41e40341e01003000801d031081a8018100340c0d5a801ea1200030302801d0300c02c040030f4005040c01040d9078860b400140340c01100c0c000704035070303400c21040020301c2c14400400c10070f0100c0c0750504c10700c0b91080e0244081da820030b151415030300b420380b8a40c2c0b4a8200d2401003042c800e562902d100002c83d0300580b0f0b41607040380e000380b10120080e0780e1403c0075002e03840700300c0c3d107540017801c0e050042e8260316110340640105940301301150499078a43c2101c10200700c40c3c24024400c500101d50400314822013407220344103071500583e05040030b00c2601c403140b1440b1060003084140901e52240801c0940300300002c24403015043c0c00c4074050200000240c1c0160700000c03080d0014050082c0c454000e80001840901400b84800104020307030244a04548982001c281242c1c04011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 146731483 1250 146730233 146730239
    0x5070813030203030406080114030109031d0316030b040209090111030703050411040c02010f0f06030c06200d030b010e04090f031b1b1508011401050f070206030906060a0f030507051207 81
    0x800c1002c0e05c090011034650313141075410705400c174085103024800700f0b2082e030401c2d59480c0000d40c820b00d086044182e00b07202c240303183c2c44e000000742081c5030640004082d03407045000200340614007d0300c50081e8002d80e003006807522944d40d50b50903190807940e00e005003e42000424800c40c800e5006581c410f008100c0410740d041c0c02e10005064401811040c00181c1d1074950003c4114250320429180c7c031180300042044520315510f00c410800d05200300c10a000b08110201c1512400031480c05120051006482507007038400f0015005103140b280c0c4c240080c503001020002400d1602c61080410780001d500d00391070019540c21035039003102c0070301c4400d460900304200000400c01ca14800c850708541022420850a010508a422482e500304408100f0070a00400c01e25003090981414000d003880d10a0b9034021044200c3c515201d6110002c0d0006800000c12410039801301306980507043c03c440707501c0c1c01c0d40d84140008440c40d40e4000900143c00c003c07410006492b2064800c8400040380c000d80d0340b4559 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 146732733 1250 146731483 146731489
    0x1e07030f021b0705120a0b0a0e03040621060b030a0b0f270606071208061f0c030e09240a1203080a05010608070e01110f01020a12050a0c050708130302 66
    0x20a100401d90140b100c1d507645845001400104013901d41500d04441850101a056959980340003016240c1c0d140c004c0460280000b0341c004512450541084035911039403148010080201b0003a9034003940107070030f81003000350481d005201c104c0320098445070941c2c031404248002090007041207540107003001c154803400e0b00c42071100302c0040e5a031209242041b42c00c54450440c00e5004140b08c0c85913108104074400500e0a510240c92008240b0740500240c0d00e500c08252070301c0e04003050020000145842001d4a64400c8045041d07a210f0350760381101c0c82204081c404046005d46070310040e400c2c08181d0160070b406103213821000003001042c92070a2943d40c02c0a20000c243c0c0b0303d06600090110003040032016980c001c01e401041d01c0e10f0200014505898010171014440b0b0310340341040002642040340807420400014407242040007199603c1f05443e02404d640b000c07001c02d00e034207418400000c0d042280c0388104101a2026101d49240040a40da5005654044484400854000400440562 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 146733983 1250 146732733 146732737
    0x130b160204050c09180f071803080d0b1207030b150103020706150519050102060f1e07020309010e0a0503060601050f07051902041404020d03050c010b060d02040314061e07030f02 78
    0x1406150f1565662010414040d20780419155190b0040d00042400ba1580f46503414642c010018640444580000384107a00d00d2a07003580701a16038000810a131440740c00d9540300000f816021a504440104030304101a10b2b08a5844094030415008000401000300311100f00040d6070140f50051030f0074410780d51401240e4424100d05944003200c0002d00c83c034140503507890080149d0780c1d54007070600d14100c0000c0d5540002040500c441c0d00b81c0c0f000c40c0c0407404800e502d66120001c48043c001503c0d040c80020b50f00c0d04568031590024001d01e500b01c0d145c0c14118002d5080d980c01902404031551044010b40380b541c0000c160982e4070504000700030100310144a116000d10004105003034032000c03401008151b41861021130340d005141070600c00141d0b601664000901d62604280352541c2d00300a01e58018456501c2d842e410100001f20303c1d000c01c07266401041640e00c1408041402d03d240c4e0b20459613004e088540a965080300710119500c0070024040c01c0d44030840d0329011402a25010f6004141d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 146735233 1250 146733983 146733991
    0x20c01021303020103060e0f0c09060c0307060b0307050604060e0f1c050c150319090606090e03030402030106080f030a0e040f020f07110102010e030a030e0f0d0c0512130b16020405 79
    0x9507005110038001c40d80d00d409088000c003201640d444d52424107446920032224098201c200f006000650b200140d00c51806555800d21424113a07900c944060070650094145100c5051280c0200d12010581d890402d0a41c1c0a803520365a48400b00c0901e002400545850080310950014040e0340305d000c80601c158104180702d20820191148000c84001e0000c1c0442040400c0c038000800e0080010340c8441102d00803240003604030200b41078425040040040c107194000761101e90401081c0000e40307400100550199100707a0003000707641c0d900d60249445051403e01070714690010014500d4451203080d140285290052001074000210b54001081780d121409102d480b520101e10401071280045c0300c441d84c4103080c002813290020600300d054991040c1c1481e2018591349001100c041d900412070301c0d50820010f000c9903d080600d6030090400f62007280225030310b100718200400014107000039a5070012410040450080c207000005200782c1203400d601c074031282813484d40000340c1d940c0e026142c05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 146736483 1250 146735233 146735257
    0x305161808031c150501080a0906060503010203070f0e0609030a15060e071d03060c0a0c060b0904050115090b0f09091c090810020301140405040201120219030507170a0b04020c0102 79
    0x794030b1442860500303035801403c2030f803003413003290700204070300c0e60040c0710142c0c4003040c450700243c507004031b103000070040c001908003a405620200c20803540b2a0402c004100c080d411b0344512084a4991040000030310030701c0c07801601904403c69860000fa4800c40382d881c84940d2000100f605a2601c14000402034100e070030300c00054065011040414041201684606041d4050815441e088105810501c202c0c440c010800040c42801c40500071103612030300b4940301c010000c3c20142000d00306540030305038680014144562191002494903001c1c403507803107080009440400c42d000202d041040404000f003906c1d0481c0101320025040001122841c03e0745082c5842d07885106040902a9140130050381c800d40c0b00c02d10400051142c1c81754102c0c070001100b0100c0b008101340d0341340d1004079040a2650203401c1c00c54000308002c00101c40b00004036080c01619a0308000c99a60401d0403201100000e083d14200400000411900742c0a600b00040100d0080e1000d4034100d9001c039510308982c4041c45a0760 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 146737733 1250 146736483 146736517
    0xa060905071505280e03060a0c080117060106050703090509130c08010b130908070210030207110f10110c1c050609010912180306090b16030516180803 66
    0x1d0507551104014100d0214681941000420f94a0030008040d04000000d5012120207507204c442c810312055150384800340513603d403420200d0706036000e020712409080c085a250800410310301701402026120440c0c0320f0042a09900c1c240041d5141c0d0700a007810b50030030908401c00b14560700c40c0701400303004244144030928400320038103005149400b950802c04069041892920b92691842c0c000c543d00c0c0c00c00f0b800014540d00c90302c0c000300e0a10074603d000b900304003e04907201103240c1580c00b80880303031700429640481c24054070412030308003080784000c1e42c0040d048081c03020040c401c003106458644202c2c1210304424419000a20b001000151120001c101c0b8210030b041020500000743c210f01c0707140003400f0824003641c0701800ea86081c80140f040080c0c003400d40c2e0361000c60203441d500031030300040c0c1003041d106281007140d641c03003084500500096001c410103684a10a115043c031a000b43c010b0240e0507040264201d51440b4241000d041c0450000700c085010f00c01030000301780f01184600416 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 146738983 1250 146737733 146737739
    0x918040201080f101701020d0c050301031505060a0e04020a0b18030f0a08120403091809020405150a120c1505031006140711010507150b011701080d110a06090507 71
    0x41c056003004000c020780707600301c0342800b800080c4218a01c003520349142d03e0340c59a1440e20170f1140240510410104800d0a10301000745e120703004801103060b0790082038004100000c02140e5419214160781d40c03a0010070710320081203088258a10541c00500c001e00706800c0d59a501340045c1070f80c01195500300149550307175154050313290070420141e209880300e002d41801c0b03030f4130f45542c0124007a03009004000b1f0000350000d17041500c9441c6a202420490540b64507014210f160b0000034440060128002d51425021418151212101d4004080010200c211203414080208500c40d1942412105921a500040b80c00030301507000c0e125a070b28950301c3c50380341c6c07400500c0e454002007a54480018000346040e4500b90283d1182110160f9800400e6543c2410703074170004807032030f204002025203400140c006c0458071001f50340290030318000076601c8a8484c11040c4c89036041407801c2c82030500c680c1c019112240b909010f5120345440c010808195240d55a4640b140e0040c4e40009070300701e4041d00b102e8824 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 146740233 1250 146738983 146738987
    0x301090c0f051203040504090201090312091505120105040c09081509010b0d1e1a180106082404030309021f030606030c080f0414070608190207120c02060918040201 72
    0x30710000c042c115100980300841c0550651a40b0560085500030380c0c03104284401c2d0f900071403400005640c032103514900c0144071032004144020074041d0b000a55804035410440381d1103142a2220b11541100d9024203910380b0003000003c0552980c12000c0c030900480008540c8018001014000140c040103407551419010b41400c55100b2000c0340e1203400e1409428020030b080c452100b80703c14542c64580d00a00040c101841e020303440800701060401d080342081307000200c655040440c2e0640000a00038107842d07880301500d50340210f146814200c100c0001810600e0b800c4c89094105c0e0080c100050035006079008282545003600311104c030148880c840c814070a9152069500610042c42c00b00704040306c0d040010711980c0301402070708100e1480e40220341808032543c800c0004c4d017044002c486010340d4030f09010b010000c003154011a0740300700c0319030719003c01c855008840c689a4812070101c10340c0e1a4180070b42d0200c21594043c2d07004201448401c01585607801210700350b01814170000250300d414800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 146741483 1250 146740233 146740259
    0x203040c060c0308040605040c12080903060601080c09370e151e0102010b1e0306010e04030804080f0403050703030504151107090c05070501021201051201020711040c020307020301090c 81
    0x1c1072040000140e494400709601c2412150055808100407480d40c495040c0117104200c5500601640d00e034181e25101040602030084c030303d01406500351601c1e035840c840151200d060484400f20149800c102c0013245203494820480b942203030440d446a580740014032106032204505108486942c013400a001e00ba505488103035001d558000d80b2070b098003d10300401d6152285c002ca42c015501040412081c031f038000c0d0040500090050f1405c1c40e143c40318414000020207000c0054028010f9000204002c02d5048080d48150381544410078aa00d42e9500d800850388000d0681d150020103110200024000340711110045009503a255203a81c1440c03000381118900e10000000c1c081074610481010740042400f400f1181c1181000441c040c08840030346152040c0c41000b0259440022410009e00b00002c01a050321000c0d20000c40d940c080d155298200d01c5209806840c02c19640030703482480c0303859089922104002c0c81983e00b45280e983c007081c01c1da603907200e04171012040e42e0010321403050322250b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 146742733 1250 146741483 146741489
    0xb01060206010b18040903030e01090c050a060804120522030501050708010b091e01020c0d0b070e03030a050d050c0909072c09060d06021e090906040204030308070818010608010203040c 81
    0x248940781043e00100c1c44e840d01e0048400c18015a2940b807460245406640480c0350020b95000912460055180c074501002150003468400e49420002080042c441c0302c2e054401c55014210300c0c410101341500362550b070000c1d03900c0316048980140b600c0f82c201e402080e0f98000e5200704004502c50400c0302014110f140140c2101c03040300b1060152501664540c4812400c1050031103208000740307a0070004034140100f080c00c082d04126900103900c00c011403207000f50720800041d0784042d41066034030704040c0c803403007051a088001502070040007240b00c602c0d8051900f03c50503500715440d165216012401120080740d5020226001040343c0040d08150251110400e00c0d00e02c42508102d000c0c00001c0794107c020302802c3c040c1c5000c440000400030203034116403c0110520041031310000c41d03060218182e00c01c00701c0034010160130b00070559500346402a1410b071b0b076154903004010b40d115501200d008000400c1030040b84034038650301803404c00070b100781c8020307100f8000050ba681c038160806040c00c4100398 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 146743983 1250 146742733 146742749
    0x80a020c090705090111070b0708090427080f21090c0a050d06050a0b0d050304180203130204050402130612050708070f171203010608061c02010203040506070804080105040b0106020601 81
    0x10400056aa0243c101e8804080900306810311a00440315240391100302c0c0c004500d281c00000d044018803c0e41005803100e020126024090441e000300b40049910502400600c0d00038090600c90000f60351201504088401d0103020b800c00480d840d01001b50300780303034808203070300d421901c02e100401c0001e010101c2c400c1c4043d0344417410b262900010a040d0f000711400501107c1c0d6810201d08854520b0300024480030004051014010160030030644991003881812414090013417002001d14150098a1090003174011039080001e4a4080c00098240244106e0f801046101203141811881c403a8a01600e0890070f50b80c1010501d180652400d0700e50381004e00030360720100b001c2182c400c0c0803241106071782c00b5907440840e6202e2034505c00d142c103456401903102d41d24040700110701b00c4d03441520b840c4210f41c203c901c814029010841040723003d9524a010380140c100300b20a01403410000c00030240c892090b09844c0ca095580d03070007075007107440654048800d80201c000401040385d04000325809081c10b9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 146745233 1250 146743983 146743999
    0x509070506180411040b03010e07140703030c020a02040e07050411070809010c0203120705060f01150c020105031003061406010e1c0b130803130512040b16050a0807080a020c 76
    0x844001a540d014100c5105458030b07a0701c040588945403600322615a00490411a40780d503141c1907010b10681003409805800d40b640400910200e104203001600b00340078400451a142145d24110090f0800da030a82d02540309044841c0010307242d40c400e000c0ca0503c100081c194a5080c02c1c100401c1c2c404554240140801c184180300c00716110108540d2205400d08001c01800d0305480880c5c1041c1c1d40403032f074206107a00400c06805203d00856031500c01d800b82d40c6d841485a0303c90092070300f40d0820080503030000c3c990b001c0c4074006500400046811070020001d4640e42680c0b95203980564440c0050120294039a10900c1850f50300041c0000e03440c10119200482e480c40030313002901400b18101c001d88903000d6400441c26400d68603c01c00c4030033f50010890b507030300d02c1c04440f0280c54040014003102d980c03281070011514100d48200341e8081c1c45a01010b549880d0006000d000d4a00c2281000e481c0e0340510026400002c0c951170041200714400c01a46440c0c0840c101d001c0c4c140309a1004150090b408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 146746483 1250 146745233 146745239
    0x17100b0a170c1c020a0e150c06010510020d0f110a050f0105010501081605030601030b10200106060917011104080d09050303190c0f050f031b1605010516020604090609050907 76
    0xf000e02c5544403008000030050703c40200360012101c42c442605110341100320b41400100c00042071009189800314082101c401d66078400c2071022001601d03c0410040e040710480302c0d5030a2151410a00029192034010340d4203207280112400c000030030008030f0711644002541006602c0a02a0f2801070909082070600d502c2e250b14854401550210800c040040c00000100142c0c001e034041d0f6003041002d0070681004000107000b8003c4c030383e0145001d10005000b6414010804140244000e503180c96550541d003d01e000307005540818000f000c410030b9521181c1c04811030f1110b13800340000342403660041c0000c04600310060021000c0b0b4008a01075042007001c1410031034041c8d5005400d0b9424a42055a4901d909049529003000a4000c0190080c0650181d20f50380c004054a803540310707441402424070720f8001003951803900c900c41c000c09101075031041280b5802000030309025800f001c89507142c4045980060815845504107064503540e0344001d00c0b41c0c141612481d548201100c00525020341 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 146747733 1250 146746483 146746507
    0x1407020109050d052104090513031b020f0402130e2220040f06210c120201110d02010c030b030309090604020c010204050a14031c17100b0a170c 63
    0x640d0b000d22409481c2060019007000410094581582c18080303040b02c10320b00c0385400840390b40c0300380716506a00c0e060001141c00104805076120405d503142e16a40e004060018101d20f14110101090b070b4000020480013029803140e0004224800d00085010b84050900003014400c05000c0c3c00c101010b503519152010500141310310084160b0422102a4010200c12101d110901004104d6400500700181c0120132860354205105940b04000e2010310342241e034400340034002c02c500c406040701031844410011040c900303424220450062500329800303518007481c2442d02800d0006480140e54485410400b80c1e81403241c400070582c100c0c055840d1200c040c001a50b0040042e0806114960000d2818209a001d5044800a2002900c003886195a44514502c1d0003040d0151901034084d04032004d0024020951003c5100613075154150890846844131000ca075004001d820fa0901e0405c0115030030f568140a000c0c2c0401c02d9686401c003c400f401951940200a42504281c4409200700d400ea84 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 146748983 1250 146747733 146747747
    0x24130525080c0f0d09030c030201050a09050604110303120f0108060a0606050a1d0d0c031e0c06030b040b1f02010e0606010e010c0c030c24091202040f060e0709030314070201 76
    0x60001000c0354030340020000c3c04603a480780e02484000640f80c044403408050b005030074000014080c0d002004503540e41036400c41620080e08008003140c01200020700060b5410000e011403000240460782400c801122400c1c00748025201e9040702890076004011800081005a0380001c0c06003040c80f40e5880e20101400c1405a0b81001c42403144c51600810705903120f070088903440c10014000c001102080c208411420600d01040d2b85032111802c0c1c19520b0907120640e032000503406030200400728039105045005058034050680d00c15120070841600d90769000b103c4a0541202ca50010080c5c0560b0019085859051a40c0100d03005901040050b82e00a449101000001c5c20f020515800c1494150a041240e410080c030342c00c8142c0001c501840c00420703c00c40030620060701c000314828040155448031403841007544a4142c4070209006080c140c1001c4030002d0b42c5600480d02e681c50f410145659801140e001c0c0010701020010414540d0003c807880100c40540a800d241ca01c050f00024015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 146750233 1250 146748983 146748991
    0x1809131527020316060e0f03030f0f030c041d06030f011b0e04060e09030403022707030e0f0d0f1206051018080d030c0905030102122413052508 63
    0x41e41415602002d5440038003a01107812000f107100c1401d0390f00d445010340b1141c644e403c1c6500170280311610551905001084801d0300b16150000760800702a8007640b021707584010004030303c0d820305001c00a40a002da00d080700c0410014800703004640352400506162001000a44903103078144401d076a0521006220191400c03410701d480311200f0654800f160141c040c0703034001c02d5400b40b00b0042216902c1c000c006041901c2c82103c21202e8007401d00b40145003440c0d101444142207000344086603c11340241d200707440560b20502503904c510052442e00341000d0307440307604c0d801182d130103042040070707036031041c61034280014000d0200049402d143c08074120090b440719500900001c1e401400c000343c030043c3d00d20002c006e01c40450340d4500650500030041c110340c100500120b9000040030900b40303418020349038110421100d1101c00e9440514241501101c558000048000c0b148003c04a0722941040c8030000f62082010a0908280710301031020726a26150001081ea0140c0f0610f403213902130729490700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 146751483 1250 146750233 146750291
    0xb04060c1b080f07050f010b10050315060a0c1e0b0c2a0307140a0308010e010602030307031d0709050f06030d120b0109120b09010e06010b070201030218091315 70
    0x8443c41d4004040d40ca205008000c1c1007445510703500c142e045415040b400d40f003e03095600c21024100888103803140e00041d240d410003010440c00550b401e0411070080c0040810074500102988a80e840300c6024801d803169188035880e000f44100240000c945010342c0111100b94aa1b00d881603c041e4a004a018203c0401c010003802d91030900d018410000e440d40903400141440305004006619561414243d0045020405480000402207507541d402c17030484445401440c555a5401e808038000c0950300d01c40ca8008007441404110400d081005501034400c50300005450b08005030110440e400017480544280e00c000003410724a54458031143c00c1d41c042c0480468403403042c500584288415800400c1521081a192020b1000503141c007400f81c813028000f0802004840340705030311040b0034040c0c003240b03a801700030301401940320f0b90003400d91810480346200300080744400565116000c1c0e9012030b5000a103800a400d22038012600d040c038a0110000f0001c03407605400042c1040d20403001c0c116 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 146752733 1250 146751483 146751487
    0x5011404170604060c0203070c03080c01090c09060302030f0307020a03020909151312140306010507150608070317030609160c05060f01080d05040b030f060d0503070b04060c1b08 78
    0x4015046080c0d50103001c1c1031505804060798181c0003036032a00121410b8030010f05080084185a00101c12134803015009a0300409140c20b40e1211307255540120b02025082d0340e544041c40c0030881c4c83d44e800001c0c04803c00085022461401010310f030039207046441c0d141790810001c1e100103a90302414901282d60640b07010b001c0703954070a5003030b0070030010349500c040c06d1189104000700520f00d005410155886018612458084018200c0341004040e00c582070700324041011450320360098000c2c02e0010702c140f440e2140301c13100c0d150340d005940c0d9a512038107007640b00c0c1c00c0030f00c10000c0741170551800c902180311081c254070301040069443c01c1c02500d94103042c24049403030034011b07101e103a09685964000302240da25081090310000e00312024070940718a801015142d43c1150320071011902201d2003024181d0940e00e40c40c440e01c2d03840b80701801c0340b0340c0300d80715280e0500052010f02c050700d0600d01403481500301e0300c0c00c2e040400c01d86558008000030040c0c11005004104074041e0401000707034202007055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 146753983 1250 146752733 146752757
    0x105090c010206010b040504111204050a020a08060f04110a080a1104050106050c0601120602210103020907050406170a0615030603110f10080613060803040914070f0e0f0604080f060c040602070501 86
    0x4482442030ad200c948030302003518108000c2c040c00007800031040d442650411012070b62082e805403514416501827400418100101e8046060070303040b0301c00364038020f0607121403c0c2c0d1002810302d03001410030112140031b005c0c503140f001362a052145900421031820081c2c81c0920314541107844520501603040c230802d945202c1d8040c0104c683c1a10184191172440d840c5507080b11200001560003440100d1050b07100c1070005000521072404d4070110b03812522041610090f00c3c2c1102040c6070000c0c2140030250b92400001031850764840b0101c1504190384002510318103505006951041c4480b400340603000c0c0a400c0800c0743c0319188030240c0307240c0c0e901c0c08540540f20f080000e034241110a106040785411f10a0109142d00044000c000721260072004015440800c501c40c40c9604003211420042040d8a40f1400c00700d000b81e40009655200405500c00c01c1180300004103d500709801c41d00c19584107003058005881e080104e02c1e00010b018281504042c900035000f980c41d8800c3c059241000b400c03400e41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 146755233 1250 146753983 146754011
    0x100302031510030804060809010e030a0c0f0f05071e091e15150f02011a060306060d0f020d0212070903050601090b010507081908100509060d030e0d050105090c010206010b040504 78
    0x750003e15400304d829640e655a0b220001c00b00c0405440c0020341c1d510305285000004030000440302d0143c41a220a5000b10f155112280c80c0d0100a505645034007000c12440c0004200707004038400341ca04d402c02544098090010070800380c4a507040004814500308420303810100070202d42c850300d4049040402c419040a040707c0c1e0a1000e030303007c04202d03281000310f001c030300d0f40005140b04a400c2980c02008251031600030b1516085c0d0100c8400c2e00720f1410408030341d007809c0001c0140400179400d007000c24110700c0d00203884121303408440c070103d04603801b0600c022509101e903c8a5000100e030f24041d90384608586840b500c58006102e15641c1c3c960b204500155039014100351440180c200740015200e030b03c02d49800407245840d01c4140005071118000440c080c0a0f0717500d01056460140c048841c43c0d132064248118055404c5d026001d110700024024119030342c0003620b0414502ca200040761a041049046150401c020203060541d0072031030052182c3e240c0c0800b65000ca800844012548a16404103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 146756483 1250 146755233 146755261
    0x4060c1407120b191419050c030606090a0f030317070206090d05090312040e04060c020d0903150908070614070c08120408040e1e0105120a021306090903090e1003020315 74
    0x40900403810080112000c40e2482e4030b85101b07500900b04020b807004190042c104440088400c0c3d840c915043c0042281400d01d600035188000300600f180d01e00c103031035030480090b84503198011400100d0241c00380000f1038009040740e8011400d03000400c0107041145c030440d240d100b01d55010b01040408500b50b0990740e81080020f1040c400d8140880c3c7e210703150b4071900c110160803501510349508081004180620004842d0305602650307489000c04c506607903c00100e44805032282100704d80300d160040100d0800070041020f82c1c0300d1a00025861000502a502e404004001d4000d102c2000005000f061080c000c0300d130803150607040039044d03a40724505004580101e8002c01420640c500404c40d5400380c00d4592550100000b41c0780131140c1e65801008040c000e00800882642c201501500050402c2078103c40b4207235201602040c4151030346000d030200d400341e020503000030f10700c03075420040f507200c40c00f401d030b00110000509600c15055402007540c07100c0c003903e00a41c482410000521617400802 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 146757733 1250 146756483 146756521
    0xe07051c0b0607051b0a050603010608041a1302010f050a09030b0a020f0304050f070e06130c0c0204240909020609090403030b040501030b090c1219020d050304060c1407120b 76
    0x3100e50b8039032440d428071320340e00c00c50200c0e600804481900c86001620b0034030b55a200b00d035401001180380d0303802c2c100111956070001c0c1084414104003082100c0c0a140c10350554840c0c0880c0314010801f0300c01740001041360451503281014840108400403c095210407000140c0ba0010031042c0c081d12039428041c000d209802c042c8034803042c04070612041000115a0303c01c03403050102100c544540360f4041900c409000d170303001648104145141840500550030980c002512030400741c012090075000328040e900b581c1000d0030840002d4021145481a8040c04030142c44040b00821038402c03031f640464460300c41c0b144d13581d00c42c050f00400a0101032007a000b405000d20080d109000d9944d4916200e80b640742c0035104820300d4000d2000006490904a20021560708104020400c034040c1c812144002a243d43c03050381c020b80916626404038004100070001000c143d41d500039500c0150400031065107a00e14405590b8001c1c9100b00b001e2802d04146000700c0d80c1104140446844030f1800106070882c0d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 146758983 1250 146757733 146757739
    0x1090503071403070828020102010b090a0213120503040b031b041202120109030210110d0e03040806010602120a261e1003020d110103090c0803130e07051c0b 69
    0x4103010941081c0040b00060801c0c0560072240040e807109601078444070883d4240312a00340c55500c107008020310003500c42c1ea203401800001103202c441c4000c42e000120890713904503210f4001404c8030b000744104541400910200d142e0800301001550303580c0c0c5921480c0309440c40c42c80003001046a02c42c10615a9485518405882ea0740b00d540e4009038041026032070040e44030303000c070006c00c4041c81d5041c007a1001d06c55041e4040e01500000d444050001d051286c100b083c0303900e007400400103200302403050503212401c0c400219151441d04000c03d140401c141c2042045410040340c018007040d4410581da01d0303041c141400188064010000c5401164101501500b00c2c2c00d9414402401b040d0f200010411405881d8828a03544001900c002140f4512009400c10001c8010b08003203040c100115100400c145804189103610b920354084101c02a00040b032503400000b00e4a21102004440740020304021442c0e030240c0c500003c001d400b6004c0d140c07a202110582c03500d0001081519071180d40078603401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 146760233 1250 146758983 146758993
    0x12020f07080106030501110306010c12050c010e0105011a040f1512180303050a020c0304050d0204020f070b0115030911040e0709061508010905041218051e1f02061501090503 76
    0x4000d807034003034007061000381d80d0303035103804080342078002c032101180e2050f50181c441915060740d0303960703548152626070010410000d041c010710050280030302035601035445100c00413840e075040c1080d8072148150305030303d0056100204400c0020a070000522811100d4618212000030101582920700443c0004001da1881c0340504946034441c6011004801d07602075a002c001d0355031001c0400c1c049104400c00401c1d541d0090204001c5890001403c4c01c3d59403001c4d00160074030030000c60000f40c0e0741141c03c1c221204010100180807141e04a10b2066046c1807a141c180720001d070b03640f6030f2076280c0c0b84160708900507030b25058003181c0180208203900007030610040401a803556507160f0f08540d1807600740000005c0c40100000303000d04407070040b14060b0b5003040e401c41e025a002802074903541807410305c4440d14018001c00140640d107205c0340c041c440c1e241009a03410b4010807410405c0c115004078000c884403513010201422980d0000f48541e20070480038440407400070581c0162064040b0b40c2c48242d240c031070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 146761483 1250 146760233 146760239
    0x20d060b1302210403020c040c020c06070501060e0f0c07020114130f0503010f06080d0c020a0b12070f0f0e10030e030d0204081204030f06050604110d09051b030a12020f07 75
    0x1580240f6203012003050710300d082d81a80400b021002801c0e0750160050b48030000c45c9115180550010380088018012200c150b4000004181c058001c410b003a076650b50354050402c910100c0c0c0c03920603409200582030060320303e0092901c0310140034070203000e810000071702c43c66030b81110034104a07900340c00e4148498680582d941075402816017180202c40c0a0350070000280c02c100da15000340410750b000381e001781c14640840c020460716421401c6090780d10003c201070004d00c1a081c01c0c020007060925400b00c107041d2404200c0508140940e0804000300308400012560385907003c29004045141191850a0306046031801c401034541080c40d0000303804001803994641102d03071700800442d0219000e8800008441c1603400300c5000310f00c0050201c5480c180035400107400380d4013031a84010000d00010744141041509a800d8000082c038817580c82d690316810b001c0c01f00400c145c00c080c070364254240c206030303032030344040f9480304582c24005003640c030060401101c007030081c4514070403400407070212121165 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 146762589 1106 146761483 146761519
    0xb03060a030f06050106020d0c08091327050d02070602120906040e04030201050a2909040821011805220606051525030c020d060b 57
    0x21140d00c0c0480000c107401c118140d070394050a400500c560502401a00c0c02155160b00b41c00e01c452005980c001910200841e550345c4010b9a0300001d081c0b0001000000d0008141c049002c900c0d402014141d428502c010b0020450042c0112000601c0400059850b101d1900942c40160004c2e001d0341c0381c00521400500c09254003400f000d203096640c25100c840103009a0781180180d46400c140b1180e00700a01400c115801d982d61480c820502c040b04c0380300860300d0041090702174060100060306000050080d5452600c02c07036007034003e1210740203018143d03040034000e41c020440b00b1051045034035014480c0d280704030042441d00c040b02e400082100b1414141c01c004440c119158040841c2c0354076a4052588410746820203944ca4009031440078081a001e0195240400c072040210f5020070340c0010700b5803044c1c3c0c040c1c1f130045e107132122414070030050002d80350504c0d08001170b194031080c100 = true := by decide +kernel

theorem cover : BRFrame.Cov 146582733 146762589 := by
  have h0 := BRFrame.cov_init 146582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 146582733 ≤ n) (h2 : n < 146762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
