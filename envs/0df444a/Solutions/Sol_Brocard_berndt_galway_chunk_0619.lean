-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0619
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:45:46.411133+00:00
-- url     : https://prove2.me/submissions/f3a8ba5f-5093-4f74-b086-c9ee1bcfe23c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 111151079 ≤ n < 111330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 111152329 1250 111151079 111151081
    0xd050f0d110c012304030e12060103030305060a1d181905070911070507050d0804030f1407080111030103020d03020a020607080d0501090e1b12070905040c06080403050a030207030905060c0d0906020105 88
    0x611942c0c2c1340198403c1c1e040c103058980d5030f4500d000484180501444000c14030072900003104065058001e18000d103c19105400b41e51703103542084241c0212100c203102d9103203e102c00074450480701150780741552960002e4075521020000a980a1052041b0588a5610041e0100521b900031710984810400048045050200c659980380d201e07680f61141c148541041c41000003844110705c1100c0007550300c21f60462103da0546001e15a5045450b44030059000710a00000c142c0ca040c01120328840024052620750b81c01c41e8200306c4809688075050302140701d028140c500684814000700080c0d80250100c548400c0702d0f511240a4405c1608501d2065050015180c0780850014030500909050052071811481d202d021440f1600b00303606505c80e501c00e11400081182d0f40c2e0f446039000b68000c515a580b00390b2101c4040d03454403000c0c2c030000d0000740c0402c1441183c034400c0c2d0107400c5039407192810740034659880c0e00180c150f0300414418000c5400004281d206180c0080c2141b00500d250700080c002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 111153579 1250 111152329 111152381
    0x30d17040803100b0403060f11030105030d11030d0e03040f050a180509210c06060405060619030f020a050903011b091412010e030301060f050c0d050f0d110c01 70
    0x18a200152004204079000b1001c0f03207030a040b0102c3c03040030700f8881c00c4054a40740d40e400d180002c3d0030030002c44800c00d480d06d524003c0a83d6442d003124140c490140040c5a110342250b800c5400360400601c0f85243c0c00107000c01d01d03800b1b01c10301032000c00340c203000b00450700c031404c0c48054485003125a02161042209c03103001c000700320030200447d0064084900c001407647e40c201820303042039076030b040400040a03a001c1081c820707900715005c1c0c42c4824038101100e50b10782e60101031008032042519101d0307001c8800d1003900341d855024101e100d90b00305649408030381c681c0701035983d00a036004001c1d50710220701d0106142081d81024460b01d090f203206480e498003540d0100c2c3c8043c2015030140900f000d140c81c0346d03407201e003181c440b000540043d42c8014020400b100140300340c0c6890f90000e010b00b000203040074008500d224440d070242e803080000c0710041c15808c44d107c00e00b90361b039038040700c080e180120b42480751240103402c274840e160359411102c5a16035901262501e0030308540008400c4002c4200d8880c1e8444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 111154829 1250 111153579 111153617
    0x6090905122503020102070b0408031503010b0f1903050703080d0c030b0907141c05160c0503180d080310060809070b071209030816050607110d0e06040807080705030d 73
    0x149610038405502c00900d114107040b0702a00c16108041c0408684000340f004012000c4000d44c410244000e10101e00180c400402d8243e42ea03092031903900c003066002c00d04052030100701d21a440d1000ca07540742e4120741d0320381d20f003410047c09d58400d89071340c20049030600e844030b0240507145000340c5900d01000200c0701c00f00082e100075006442c46007002001080607028a14110459011280c0752040000d0703049034003040380c00390600700c4448055940c407070308003451603005003210200142d00c00040c0d4200000030392040e9002101c410347c15404080c41c0f41c02c1c408900e640c030007180070718082440001c0e0603080620103043c2d004003078513078083c03a4400841000103481000a44441e076a0250120030240d4040340111010306207504058240100002d01e90000304080c0c240b9594648075030151000c540e5180ca003500c0b9046030070700014094214501c04c3c981540b2a040351040a400202142d0825446407080f915000e010340205125900480307040c0001e2800300a01e01c12082c052170824040320682c501c2e0f103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 111156079 1250 111154829 111154867
    0x6010212030441010506040609020a0507030e0604030c030305031006091a0c01020c0105090304030c0b040e0f06011106190e03030105150310050402070305120f0405061306020903010609090512 84
    0x364420381d2450b030501001e11181031040c038100c0c5900300100100300c50f40d182e40202401e84806100e10328101c000202e54450b40241c0d01100030a49855042030b860f510180c0e0050203a69003164008001c000100000c0e4540b082800070358060b680d00c544a1078203003880c0000281c280c00c81418441c10081c10070080c07040a044045089085442c16110241450141d01a005181c0c04060f55420441044160711001000d4000c4a001d045105800e50b95024030581c580b01d180113001050f024280001d61410008202d182c01c0801807403d0041e02010f0035200b0309011040d100008000301d40c15445010070901e01039030200340f141c1000b85103103514100002e50741240c80c800a201c4d0900100000e400142c900800e8401050b01078025940d5151919008090f94005107502c281000d0300008651303100741452a692003954008010002510b42d110281408142c0b0740c401c4442c02d808010066003a00c081c0030b101c0040603218004510b0451034034056090585003c607040340c0345001d00c40c000e014801c0c10611 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 111157329 1250 111156079 111156113
    0x5060901080d0c08070c0e1014061911011505100905030a0f021206011e15090b0313081201090501050315010e060f03010c0905030c03030c03030103060b0d02030d030203060102120304 80
    0x1040100300b69160541c2c480c0944007018006c00c2c0d10b0007000034801d00f4070380224840c0388903080c1d80b460703a512541c608a00030105040642c11090501108050490409040384514050b04007a0100c0401c11200d6081d240111002c5505000303e4004008508040780d401507451091708140d83d84505101c0402e40d101e4482034040e12580d403104841e8150f4940f080c08081c01030441007950382540e150001503144008010036445011400940010981c2e58070429a50804041da140b100766841d10034141d01940005d000311216204808246001512a0b0003c0290b0041c400d0141c0d002d61420081b40c080710130590000b80650031030907400712003c1c205410b0358155600300000390b4568031800040b03401c03956a800c68039090340c80c2ca9488990720b40c0201000040740d100f14200c4903100d080d00305043d201c1c01a00728906840d0f00900041c0300040035a001800032400291042404810a4000a2a20380301604000101c0c5c0d0005c00d00401e56410300117500e0380d8980d13100c01480c6041594422022010010301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 111158579 1250 111157329 111157337
    0x40b0408040f030605100501140910031b0c0b090d12020f1b010209040b190311060d060e010305060c0f040504050a0e010509070e0916050d05070b030403090905060901080d 75
    0x2010003104200703a60281884224111403551289031120040c0415145600c2c04072460038009101e41c41032410300b01248080071114148038854080c8440520607d80c441c1c24591207240709010810a010782420040c800e03595810f5200590602d0f8104080282c2800c0050700700d25085002913802241080001642c0f04005980d035001244201c0140240661482080905402e20452520540262030601402ca40401032041d5040402a043c9600b8101c05a2004204001c102040000b000001c3d642c3c005440e440c80c001990040c003045a0954100342c1580c0c00d060018801d02104200c40c83c0d200d200d0851507407400341400b000d81c0c00c41c0124030540b03124036110300000300091600d400c010201c41c0c0c01402480700d420b117503840350f86420b8540a400040e050b0790f0002003644100140b4042408649003864000f9402e10061240c00c11504206484902c24a0b070006651564680207521860103940d440340b545080801460a90700b01601c06032142c480c04006224007840800c0d00030700c90010b824 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 111159829 1250 111158579 111158581
    0x140703050405030111070209101401050702030c091006080a0b010203040902032d060f0f0f04090f0b04200d02010906120605041d0f030304051f0e06150f01050a0503040b 74
    0x1a04564501c22500325940650800103010701c0c0c4001031001d00078103842204d04000541d200d1014107c41d980e00c2c400c800040d1803100c822650b075400f4400801809001406842e00d82458401241c41024180c4011404040c000300c00c2000650084600b900908103003024010070f400b13030000035a41c2c0035900030307440b003d903000011031112111039403000002d014044000c805100c46184107000d50200329070207070080e003101c0202410b0f403900d903900b44290000240301e06480180e80c0148802055110403c840303421080d00303002e000c5009081910301c40c80c8034020007a03c2c3d40b03040c41c9902101e10b55020f10380c02030f605140c0000041c1c3e0890b88000940d81c103071a010304000341c0b0021040c0034041903804290040c0c81c02c4c40c8841c55148044815070030003803060850300341003030106400d0350341d1104840280c500d410070000750b41890f900201d01d815541350030001040100701d4498480c10b00030260b03159250801407a0ba025414201000c140e01c1440c0f00b400e0041c09c00310040303000303001d074130000b40014240c00d2010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 111161079 1250 111159829 111159833
    0x70c05190e180a05012405090a0b0301090b0906090d05091807090f0902031506040302100c03021002031303020706091d090f0303071809051302010f021c051b030a1407 73
    0x4a0044540c10520308807081c5903001d041c41c07170003030101c00248a21081030440d40b0406800c4002148215040640b402660b0760320b0000803c024201041400d505d5525404001b000c213281d0381802c1c0c0128006400360410741402e030032075807034000c1002c1c000041c003c06000700242c1d5035900f01c017494809a0102041443c2c3e0b40d101c004c95074196039420122018200c8400419111000c0d8080c510850241d40181c25900e0914100b040c40c0c02903100c02503010158043c0c40803c644604485050719100e4011204d00742c4030881c5080a0780c1048502e80c64003190486070701b042c503a042240e10010807050401c505000c1c1441c40c6036803240b8000303028000701c0040c4000b007010103400704a40440740100d40143d075240d00308240014801c0401a909807800b102c2c0311070200c0d040745c5a100700d80c000c145c4040c0c1d05441044a9006464600302c0035000002d5020320a0010301e000e00301801200e0fa2220340e91400d0342c40b115194140000c032094951400694424072007511280e030081c043d01040d50149072440c0d2945418 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 111162329 1250 111161079 111161101
    0x9060f121401090c06170603010612020d0606030605010b03150411030112080903010e0601170c030309040b0f03060f01090c020102090a05060c07030501020a030c09080c0d140304050d0503070c05190e 87
    0x84403006054210b011800100389a110341000c80324681090b08803000d032104408c00d426a2001d0080d84086408151454018940b07a650450094403c0d840462600c0e07894640d0011100241d1110144080000802441e45a10a0721120520044a0800c0408580d40111107140014000c0b83c56038008504060244800c480544138201c01c02002070005000c000409a00d6503070078480e240243c0c226040110300d00720082400d0502ca1005002181007102510800c4090700800c0f10306d42d0000b6040780c0c0302d400d0f5102800300074400d108159010180d940b5040309441115003004080b011a403040c8122905541c03159811b03001c0f514100d0354103444154a090a50821400307500081c010342c800a006481542c16402000310710b4040d0701c0300c4900725a07480300c0c140c40340b00f08400b0a42c04030400525000040600d11814102120401201d04003502d50300444d121400005007980c0b1544045000001c1140302ea4809000d00350994444003a03240201c000d54002d610b900540c0c8109081b0701c0001e82202007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 111163579 1250 111162329 111162341
    0x30e060306010210020705030a020105010f0605190c0204090515070c0803040b06030123060a12080a030519060807032d03080402040906240e06011b050a020904080409060f121401 78
    0x4c103040840d40e8005a00d0a180d9952001c0e24000165081c4000054100c140301090402c0360030a8840034507040c04150881404120725404106010901994102689a034854054100d1180008012440c040240310301384100c014900001c00419020f44400a07004806a9800c00c4e0702040046450300c1d080006400341c6010410403a01500c0c041140301850f0040503c9030081d50143c9000e1030306a01c45c0140400d00032001b00182c01275100b0005812464400c2e400f269010704c880741c2804079a00301241c0401501c406a10103809a40100401c0c400c0c403070820801001c002e40c9800641e10304038200d0200e00703043e5030a140035044c0410f800015040d0340340d9400569003aa4410003c0011030220b181013510f803014044280340c95909404003003090001c0c00009405a2416140c483c90700b00b501592046240049800b02d416004501042e0016192064060300692180d5040c9446d182800c1c0300740d00300d6140398030020400506010401c1101d0034010011202a0040111041010300000701805072007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 111164829 1250 111163579 111163603
    0x12100504050102121f120c050f010c0501020c030d0f0c0f05030a060e010e0103060b090417131a09011404030f0201111606051b1f020a110109050304030b010b0304030e0603060102 78
    0x2060020008884101114004901d0360210642400c50321081052041b12412200406c4480415414891450100e00300c4414000500d4049000100740c3c1d519400d80c1c0010304403403425400030406601c180168020170000d40000401040304440901e0001c0a0040c1003941905201001003c80c41b82c0b201600080040d0054010815180d6551450303200000c80911080d100715142442e4401030b031402003c4e0313030701680e0032807510b85640041400e0100168412070500264508001000a80300201010724000d202d03cdc5407640e80f600030040014040c82c0303882140c0152208204000d10008050302007002c4e0158080ca000500e00403400c400c94034206403211085d00105180000050840c0c0c807070b00a20b40c1003030100c2e0603e02c01841c18161941d8501c000b03c94001d007801041285080021540a014100f00c01d240c00658004a180caa500311649150300b41c0302904001010300500080c0c903103c0f80100b80010400d85940b5043d2001816850b1000e6001e00c5a1400008200d4680c03003044007501d041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 111166079 1250 111164829 111164857
    0x30705220c051b0331060509030a06180506010f0b04090b0a05030609061f0b030a022104030903030f090803030601030b190e011a0c0607050703090e0708100512100504050102 76
    0x50403074414555a41c000c500c8103650408117040c1c901c00c507454034000c040521760200b240c0c25074900f011003e40b6031740c10500150350140300300480b1001145040c001c00100c4a0f03100b10500d481c00043c1841400e280050704501051102c1d41e60411a491098040701c040f150001170000f203d4540030005031011005034041e1703506200750381c140070ba0200045100d6015240e541c658040c003901c0326545460400051103082060401400041c03000c44032a0002c0149001c800c0c0c1e425141060804802131882c4203617002d4000070381110081c810142c00c65000805a00c4609001200624040500e0741d240300081c4000e040644515500e5440d84030303415849544041c0c00d010040580e00c1d40203102e10140c0c01d208423040b8160203135100321441c0d200d81c111803800302520007418403550740030000d03074482d40800c404404208000c030b00091074414860b203d0713005000b1a030321440d150500c01d5410381480101d4202c50301c5100d4210155456000020301340341d84441691022555903211300300359009014805040c1016 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 111167329 1250 111166079 111166117
    0x10e0c1b01020c06090c0a0308070c1a0403030e06040e010b090d06060b070620250803012409080c0103200f090306010e010e0a0f0f0e01020306030705220c05 69
    0x240d0103401078040440500c0c11103803299110400b90b035441982c850b2a13a0448031f40b03d001e0011400510080500c0c03802601000300c442d9803039440030102d4089860b04000c55001240910425a012003100d44004c412189541864144248102d60000600c2040500880054207110310346600421103107150708210108030055580d184141d455014003822199989020b01d6020030302c07820701c1c2030300305070300c2180801e8284035048401016200d003102141000e03585406020700080c420308020350203461718000481c0d5a8880c2c805440c0480b00300d10020040c08140141440f14070070006504008200034a0041030b000b400c0c1d0201401c464842e41e10824900d00020340003021030002000b0310604000b60300303e030b40d9aaa10100d86400d00c4081c01100524200031020564405040d0803101110100b000d0020311700b090940300ba0304940307800d4040c62a40e500030040090a203024026280200f01c1500e807030308040c0c1c1080e0000c4603000310348a03200c083c036035841c20010210300c22419510000c00c1c0c00300c0501c003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 111168579 1250 111167329 111167377
    0xb0a090606020705011106060d02010203121303030f09020306070305070507020405100303083106020412030e0306060d03020a0206070c030b1009060b0406020c040c021014060307080a0506010e0c 85
    0x180045001d518054441c6400006082d4421070b0800e1391000600080d01c0d03a0b072548000c0000025503d40203904501c02444040081c141241d0190700401020036500000c0d40146000341c207542c00e50744088071503403402e6408000f5860100d0aa5880071862400281980c0e070840143d80500036000c0181d0000d10b00130800055070102d0054405407402500d851500ba82c4035105d50f066110344807100041d040c85900d2444060f0041040e5911140c818003001d8285600c3d2051003c100c26404001e80000321021600c807014101407001e290890400e89040010880586002c0e41e42c203103c08000b03004640c00030304001840908040c2c0000796501c10001c0929061550b80281d5040d081c0c00f90544291405400188024401088a0031550142c01801004070032404100080c00900c69080a42c0500c246016208040384280d41c1e190100d030792200c3c1c440c104501414a415201d4011050340e9000c4c0403954040382d000a00d4604441d40c2d40c500000300d82c1c800084407001d004020011108040d08444030134 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 111169829 1250 111168579 111168581
    0xf0e0f011b060917030103030f0509010203041d2509060509030a0204090b0f060d02090402061e0c01060609050306100b210c040801051003081903093c02030717010b0a09 74
    0x10629000e5901310208400410041000f8442031000601103015031424a4a5901813009030998040500503242455a10301c01078042010030502e903014141c00d80100100184011008445c266125a40548510003100090703e8040c49024020a01201080c054103d80d800c0000d4003002d6400780090010000303034500381c1042d820580b054120618003000084150500a95480059800400c003a503541c07255000d100156100010050400c1c3c135400c1240030400301301c4000c101080403040006115850003400a04000c42a00404d200c0e0b0050800d0080001505021074103481e02c40080540da04603c00e10a40c04c202200c010030040d0507168108091064900013401c00c445480c1c00a02c899514654038207902c0403c1d0200415126092001554843d854401c0c68044441401c000035175410b9602ca00400c0f0300b03171000d040d408400c0151214108840f0380c1c1090300e0080040302d600389142c45c950000341c944107076010f48900090309012110f48000c094000d0b00e4076500c050100c43c4a0390325802424 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 111171079 1250 111169829 111169841
    0x304080a020a0b0a0801060c1a01080f0709050f0402010311070609030504210308070305070c0c08010c030e0f0309010503040213050901050604050610020606040b0303040e0106050a0801060f0e0f011b06 88
    0x2034800c64040b00006003080e00c03502140c1440c00c00b641ca0030b54503800d03d51700f500d1140120805450f40c4040005619089000507000303801390800d2030041c01c500300305801040c9451078a41014151a080000303000d0040c8150f042e0301d410590900700840d001200c2108889140542c0740c001d0007150504071030805064004006109852022180203c00e078041e414109010300301010050015600c4000190401d1207580940e800008034030700202c240081d40c65010400d100c3d034200207281d0f503540640c91440d981520910001803880030150194072442000e00d42c0300c0c011600da260600100100041c00c40d605d134401d001904428540800040c10816089802004100e4000f0301843c58040410030610307100c201515a00d40650050025588107800c0c48041d204080c4c05c0303030f010f100500c4003250300b080000000740600700b47d030380341c9803201e0300f03450000c0080c04103030b01560501000f83d5011141587c000040c40340540140d583d00001209000100c40549010713024200d2000c0c212411000c1180ca0307000701c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 111172329 1250 111171079 111171083
    0x302010e031207120e0307030c05070801020c01021b060c1c02090d08121b0d020702120307151b092d14030106090b0612090319030b010f03090804140a080304080a 71
    0x7601000c51100804040303030030560175184180d00c00c0c00748030002032083c8250b080040c46079044e28450380d1356082540c02c2e80c01401f00d10449035008030780f805e40a00413130719003942030700f801000741814104080d40d000f151080c40d1003801c00702903803654100c0056444d012100740c0503000c0e2482000b03030700c1428103450541100904514604d0110045901010714a0003401d80d4080f007000e551030184042d9500000750f0114600f02d030446200425900d2626080c07014068207070044211000860400c140d032811a696002c10b80040c48800050001e02c87e442448101034905c50031800c107418400028010120303501014411249031060008070b5003100c41c5608c03c030580001d038000d11006440f04003d1065030388422040d40c001a061200c2080044511285a08000c8890a49140485400c11100c0449040201c0404292101310341e00982d41d03c1880c2c4420f501c0b440c0340030880304500f50307548142c07441984135100406041d14910502aa60758601000130800141201e0362150b8074025a62541801042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 111173579 1250 111172329 111172337
    0x306081608150c0313050c040c0302040f1706060d0609020a08010c0f0503130813120605040209071827051911120a0504030c0219050f04140408070302010e031207 71
    0x140721080002e00050b50050807202002da096980711040591138609800707003034550348685c0c60429180d440f18810200c0e80c00d40b50b0703800f40e9618108500c2362055401c40c0d01c02c070484d4000c6410030005903030103d0f810f0340091048800c0400b410b00b505210000d00354000340a9400600e4840000310020305501c030340d4024071140c17115002802d03801021b03a10307030104039072202080501809910020324a00c0041403503800309680d280e141921171a03400d410496005c8104e5420784d0341c10511040d8508600c0165000320035242c0085600c4408030080a40e1005102e20103030410440c0d85030f002400403100e81041e01c005203104000c42d10b45481c00781c2140d0340c1480e09003c22403800e03900010700c80f003032030407900c105a00766528bc819854186204c4004c0c24003e0050341048440400310f00103a03102c030702b0152060075803001c1c80c2c0040d04004c01c10004031600c0c0c48040c400c0c1e03e0114034901d082c135503c0c0311540c86500070080b241c441040d800c0a9000d01601c1c40c40031580c0c0000180248881086d002e02c41c007500859035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 111174829 1250 111173579 111173593
    0x3020616120903021c230109110904021c05010b281208030f19140f06040501150525030807020c2d0a030b13022b120306081608 56
    0x54030040e0543c00082c1d0400c1010020081a407914041d0540b6944a8008142c0c040203408034011010484483c940c20b69445180700420321015058503050108100c0d016011820b0641c000f071103894240c1501c55046010510b200c1c00c1c04400e40c09040f41c01009022044507100700c416202500c400748014625044200b0b10105444410032101000d507503000110618603101d0300b1130f041c095400113040100c01c1e90410140b202c2ca03030550080b25151100c1c12065107060401580d403c0500300020183e5000d80c1c0703803c0040041d080c0380b05c8500c69800460400340d47c0c4811008500500441c240c6103540e00c607501440c02010140c2c00341e40c10f4440c1c5110b5081d40c000b104003a04100900f950f1f0b101d03588034002c031342da040c1c1010010700c1d502440e03010004001100c40c0ba030380d40d502260400c00b12065060010400d15100a40c01c0041c1160340b19551a190410329600704194003114040215018003007100082c0351140641c0207501400280c0340040444010386081c03150700c0800d0f2610701500c455401611 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 111176079 1250 111174829 111174863
    0x10f0e0a020301060e0d0501062c090c0303040b07020f0a150f0206040c09050c070204090b18072d0e0a020711030309010f0806060403080c010e0705060c06070507060603020616 77
    0x4402e89050310780c56076422503200080c2e8100440b0800c03103e000d48082d541e0700c4000400d4404811404070080105901d10640c2a0011b030380382d420340c0010702400e0140c00154868105680201c00c035025079941c1d642c2e60703864035128001b0074600f4072007003a181d07001180d0940108164071600c100401070710166586c1315480c000c101c01240c030b07442d0503035004003a807401d403105005810043e0803940d4000c070306460340340c28032090741c0014066030303001c0703800740d441c2c9010344140700c4188642e145820880d88000020034170b9602d0141e03140b1140c4100e10b10245042e1990040c0305850540481c0500105101c0c004003d01c3c1c03c28010200095212100895030401903040c120541e040201c00d84a5440d416122210700032044c0c40306540e004401003085a112404110200c00078840c030000d04500c003401ca00008010f024800b586180211540050340319030300500080300601c0000910a510225524000343c503219a850300401400c1315402c001d500038404140302014450300720001c0c031f03060b000b031070322030741ea54412 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 111177329 1250 111176079 111176081
    0x30c05011704080d0908130501020c1017060d020d080409060501080103020f010c031116170a05030322020a0e07120507140702060405040c1220031609050405010f0e0a 73
    0x50360751408003800c50780000d004100c0e50006000042c02e0b0500104d01c00603141d850000a901c2200c900e411000540018005541d0420210600c1c500545410020704103103c0c0281c1a0b03103041c41c49110741224580050510f49403d045099840d9028258811103281c920b000e864a4103e17015829029140c0b0300001030f0b0350701c21200e4604030703600603108803940d0aaa000450300709914900c103906000c4043c6040c4e00e5180100086c0c05003134028041d4100b258241885000760b0340310280300d1201c0b641f00400440125001004803074004042d015108103140003501c429075401d1040c20044d40c400910400003807244900100240709035242c0e926a244080d50303c1c08a4100ca0041c0c401c4000900c0540341107401802880041004030700080079241002e6403140080c3c07c3e160040304c440300081c000c00e0858401c0d000c6010362200c5041001e450511860b0340c1034101c0b00c4d070000038078013503910180c0d0300302140031405214580082c10340503005202d150703101c0d03045044001d681d01c41c0c2611142040e001440a50b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 111178579 1250 111177329 111177347
    0x709060e04050c0f2d040602010b040e030a0c0c05030312060f010c030f050f090a090902030f06071b0303150b041508130201140d2306030a05060a0203100b070606030c0501 75
    0x401e04039075007028102c00d52600c5581001606200a20b9400340c645c0f00c0c180c2011020360801c6100c10f407142e90b00e0500c41c000b42500c9041080314002c5003004070031010148044140c0d009461a031500b84c0346001c080c20500400c521a070702542d01408000f13802c0c00e00c840d41501562142c0c206603515100228003e0044803d2801590301900044400030301c1c0403154401c0c03008000502025242e036081c203042c040021031001c221341c48044c1c426600c52801c411420140040b03003190742c203140a041140381500004c1d0035542440c072a8408481140051810103000307501402d5008260900034020a480c2c100c07612003544640941c44100001816140b40c40303100302040d500c130f01c0740c42810280310222a070065811511040241ea0440820f201d109440310300d61081d4039a0300191702510911001c203c4801220307031005000c040c02900004040c1d404220700081150f04011542c8005035280c3d60103818255030507081c0c0001041800000318030050240c1d541100003940d0003001d550100503602c3c0015106011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 111179829 1250 111178579 111178591
    0x3070c05090415020d241d1308070f0b040506010e01050301020414060a021c03050411091303080c090d030e09010906080a06020903010609021c0f02040b0720090709060e0405 76
    0x100003901070010f03daa40d005010fa16180c5000450b100c071800303201ca0802801408a5202d404184808000b5244c00515910344107001c41003c6140741040c4c2070045c81c0c4958010040d10312040040c196042103203c0280001c800d402c0341c0b00081c2401c2500d0800c2d1226020b10582000302a020000f003091318042c801c039000c44042e0350810401c0c0c02c00e00e05000064108041c403d0941c007800c1c1e240f407103000c000d0305004042e024565000980303107468a4541d6a441d58034644d030f40a1444201000030382c58120007201e10315034050501141c69682e40c0140100c62081480c0f07550084d91800700b41c410035800c0f03070f446a041d1104a4000ca0942c2e29024010100c850500c07800030654031101c202d201043d41d6600030721a10002030300218409444a03840c4003aa0701594400c48140307401c02a0b445254810301c5000c00804441e00207507c4c1500e0001050f4941c0102c02c40981050803500079000248444150f4241d4207201801103140c514142102600510440c030034500440d264007400311741c524151143d00d100d58 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 111181079 1250 111179829 111179843
    0x60406141005010305090a02040212070201150b0301030605061306140102190b0c0706020403120503061e0102060703150f0b090111010902031903020f0106080f0106080102070b040204090c150203070c050904 90
    0x1c0d20b410011005410090203220241c01114400000b58840c0d0000349100e04540142204900300504000d08459a5008050401c4141401409610301850481e41140d1300b007000420385841e00c10008000710486c00085860603d070410000c2c04204040d4211540802602030300d1a0104500701d103015000e501c0002083d01159000203004030068070080e02d00c1c0d600602d801420107440303940b8040022079024080010403404000c000c810326241704040d6200500c0400901c00741d10321380000c0c1d0386810143c400c5040c10f8640010068844101c80d550000f42440040725078419942c0b0a448032075400140308900261003048540030755441405203000702540540140142c5910005244200090ba8401c50460043c1c081c082ca01c0d010074003680020304824001740042280030441c5508544c0c840c4e2191105900510000000c190300c18409940b02d901540d01103280758061a01508420064200141c500e8550f270103045102d80c0080980440d81c413072200006c000340c81c0e90400c1500c0b0382c101c800400c50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 111182329 1250 111181079 111181111
    0x30a11040c0809070323030301090b0f010c0b0703050a09060504060209040e03030106020a0b040204060509040506010e15150c0309130e12070f020f120d05070b0c0703120b010e040e06040614 83
    0x5800340e046e01c0f10800d100022070b8081c245103000241154001c0c2d01c0014190f07107450b004000391a00c1050008a1a42400c102c40c0c08025581d0b80c85189034010701803000d1603035510004a01f40ba160b0028844c0a9104400708154986450400004e4105400c464041e81c5003841440b011800041224140c1e012a001000000401d541d0001000c1000f00708a811130317201c2000081a8582540d40c4d03002d6440341002d001c50f0742c100051800c0b1110000e25078245258110700000c1d9540324407801d55012542e03c996507550f1021510098514491142000e0300105c070181c6103081c01140e0b41c0510102a0325400b0358940c40e0600094070124040c1c01c0340a007440c4080c4510030014035050400405400b4040c0a070040d600d406541641031010803c0d52a0104400150340c008101c60101d04550020b812040a030900b01e442d20001c0c02c407103081c2c3c0c2c1245481e130746860181850780500a0f800c0c6500000b841402103401c0304030041e490780703015a41180c102d400c00001d140e0f010f803840340440c4641e0705108a0809 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 111183579 1250 111182329 111182333
    0x50a02060a0510030b090303040203010b190b0c0a0b070203031501091505030901060b0f0a08100e060d170a0c14010b130c140a020601031a0f04080d0209030a11040c08090703 76
    0x810b0302030f0084041d0380091100100090300130800c50f20820265010719207900d010700600d825a1085949144103102c540700e40840d00304802440340580c2c5076060590b454020000000d86400c1514802915020780e440400180550000080d8403030301c0790805454009641c1b8006544501036402420714184003d840d15900c144124080c560080c0c02030000309085644401c0b0089552000240109440300000c00842903600706415907045548042d803030440078a005998502c855001d0042d0b07102d8040e2403140e40512111880046803100c1c2030500540d03e90244c0f4025003c400c80120813141c00c14003030181180100107100d00c54070060041c10010410f00c090007440010095590903c0c00e00c581c40416810700060800034288501081e0000d05003941141414030f40488404c40144400c041c2c0802c2150101c40d0780842504954440805901d8030304000341200a401001040350f0180704048240301803080d04645156614001c0d01c040040c030084d900101c0c0c60b51401c4a41d00c80c158018001040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 111184829 1250 111183579 111183581
    0x81e0d030902060d050c0a0314040c030f0c170601150e010906030c031503060603050c0d05030d020702150a020115052d0402040b0d050f0c0702030d0e0a050604080f0607050a02060a 79
    0x2a07280c030080c4941d14080442d6200001c588003511850018500407803080c4040360540f0420408203507007510380c60710740303810360ba001079600c1540030061002c1c54420074842002101d5401602524a080a0490000405400955400342403192090800091840250a41c05441c052a01100682d02c8201c05070a010043d0054030408082004240d82d55407000000d55034072581802861003408007141c002d00c0c2d402c0607484d047e07940c490b10b489036600240c001c000030b000104840304800c83d050096118003150001446030141d00f03102070b00c4074030000382c003107261607066120f07040c44048003400c0002980c0ba0410300090403500c040c02c40b03664401c20100910a09a04100320300c03c0030041c4050301c0c168031000b15808a4028040c4a12201d4844003407100c100007000d800c0f0750040c1c14030700071030030460703c0c2e00002d54400c040d41e100014403104070108201911040e160001902000e016296619900e1464646c0c03145d0185000500d401107102180d48144610201d0380b09a0542d8011300c4a5190021444 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 111186079 1250 111184829 111184841
    0x23040201080402010909020a050702031501060801030f050705100201050406060e0903090112020412210203031009050403020c10090f050d050d11010902041103240a090b03010e010f06081e0d03 84
    0x613062101c800e00c0010791500c0d5000801d41024540d071004e80f030f0081c61043c9450025400c1448100100d440300600026600c02171036811640c006602d8000c00e602d0b41003107405d14459800003900f001c2414070782e40855805400c0700703000314402c1200704121139668030340c800b04850a80f18004180c2040047c42101e43c801d40d01060503c0519400525060781c2e1a030030060072003d0841260382103050703011918042c3c018101030165036190300203503185290920003445640c1e02c81c0980515541d80f000898141407007041420016080030b0500585400c00400c040c1030b5042d6481608210182c2510200382420065500408149d01c00b000380300d003400c08682501c00d203c0000c880d405640d07035207441c840540d44074000c1c41071801842c0c822503601e003007016210701c60007401c4172a003130600d45881013144151540034480048646a002c0080c002001100003805050080b44000b07035582894242160854190300000c01c0b48c1011b01120355004654a6209100340f494581c100e40c0c0d001300ca044c80105020b50008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 111187329 1250 111186079 111186083
    0x1602010207050405040308041b0605040504020a050904050703051005040603050d03051308040f060306090c0c060b010527100c0c05150f13080601090e07150504031703060301230402010804 82
    0x9140c2203510b46010404680c400c44064002881d001d051100780116900419641e881082c60441054105840030306030b44100d203e410b000702d500003600b1010502ca80c1c10764907030900081c024480ca0402e0800100540416541001101c500030800101450300748030380700031254820042e00c01c5c2224084180c000b80001001e20b0a0f00f40b4096445000078800001840138000d00030343c000e401824038000400712201c50b0005d0325890300d00821143c070650041c40d0300d070006030711400200c3d034008600d004030346038051b00c24452a20030384203e80300c03585014280e0703800d0740490a6400f407402c0002404119800240b400313002d03001c05410390090203581022280d072160303545101d01a074500308101c00fa0181d554030112240032441d038a43c0041c00f610100303101d5030f8010031042005001c403280024416880c1e000d41c0c03107200349011451070401c6810b80250241c90003140c21051820103480b58070440203480c1d1046480510039403070207000d4010070b08516910a95440c41101d460120b40d129070041d070702c509002d002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 111188579 1250 111187329 111187333
    0xc0102040513050708012c07020705030a0614070305011208070c0b031504060f05010504090209030118080415081909380a330806270c010516020102 65
    0x1180715140c045400b100b6021203140003d4524244400418424041e0041020340c10b09200442d20300d0304c010150304d210841c81c40a910203482d0f6107401d80c80c20200fa48119010700801c0b140100b4058250302c60002c680005050f104565100c590407012218240607225a9021010500340855211006840442c2c03241413848211921404a038003d03402c00c0340d416120200e0a4089040d038203050041e80c0c020034103680100302c09400c08001801e58040c42c054070a1030713503002c0340b061100d07038094100b45115441c03500c510b00b0012050030000640e40c402d0060b1000190359102c2c81c442039200e00c1c00c00f81b240051070700b00702e2200c8110b08080054004008140c9900400c680e01101c5100113010400101001d1441496074018130703a6180e02c0d11200510714504580b9004140d85204d260000300a804000f0f005c6048000c00100c0a040384100300f80c02c111060f00c19142003004802e4884a8030b4810307140807004444c00c840f0300a200b591110104c4c007a03400200b0074040e10111159600e40c000300c1500c1401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 111189829 1250 111188579 111188587
    0x105161b020316091505030c010f140403050a05061803070816240b06031509060112090b0105040b060a02070510030b1c06180309050108070309120206090f010b0d080c0102 75
    0xa0301e040f40d2203820341c0002c0560402002403140c00d2203140c551100314907820b0f80052625001944401049a10b54141300f0010086030a062090803d01d1040358075203221074071551039081c01995010b041d00211824030848000c14006042c4000341071007541000011840e0100c00d47d2802142d802c950440e50b003c1c949640342d0b81c00100c410100c0d0083c51120070480000000200204080c0c1c0c50880016005400400500111440d0350190301d040d880d080d5144080e6031155801251102884c425105250340382401c51800c01039400b800a0494104480510600c540c0000300111071042d000c0c1d15016030f00801c2d00b0485402d041d07031a140300d00c900341000500043c074280445c0c0d80052031200c000c10644800500c80c01c21405124142d044c2c3d0703074022031251159056501070825940c07401064140904030340051806032280e08040b45440e80039898042c400c04e103010295441005540541d0540030f4180fa103481024140300e46a90818028043c64a000c20758039034400d50390207c0c54108455400304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 111191079 1250 111189829 111189833
    0xf061701062103120204050904050d020d0c0b040b060a1a0a0806010509180a180605060a060905060f030a09080c0f0f010e0d120b0406081510150f02010b0901080706030e0105161b 78
    0x20b21183e22460091000d4040110be40b40024144000c40c1255000c0c4140f03100e020000c20088900c00e40c0c4281d006100383c440b6107030400081c1035650316910008403041e541e09408440901d030b2014080030403e41d2210081a12030324010b4425000d00e102c2c0c941c00c5004003420703502040c9034036070302908605c00250004074044001440041e8500d50141903840300d850303100b848106d0a200130281c00414151420303048040c1890009000c0381308546903413107070b5003010000c500c400740907074401016183e100ca801591102203800070351301d80305192120a034a010302015110312140600624400f485880701400302900462015100a00700c000075686565a400c8a41615100d511801c005045650000d00c00080b81511103103620200422024450070350000c01c00143d0070b8a280a481c540040c144000390901c0044100e00400103452020340c4402141d0002034000b4012030030806540e21a6002e001d01b451400c2d44034260b03101540c01d032105d01280064085450310882c2c0d80d034031503400480b158030105226 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 111192329 1250 111191079 111191089
    0x1030905030f040807050306060105040e04151a12060c032706010303200d0c0305070602070605070302040614130605030910060e10081c030209040f06170106210312020405 75
    0x1100200041c510000f81413001403020000c0c04d00801c0d0440c014031003841c00b100000c3c50f174000c51098006031104203000c03c0800a50041840c418218011f0410404420141400b07001d2101400b09000f018007189050304404041005ca11500050000600c1c40e00c5486143d0074003403a4003040650780800f101070030810320090180c0d600171402999101140c40b4070360103094000402e442c03401500c0d4010500641002d8014800780c10058140c14026212091410110040e00c600749004040c54500780c10054000d405038003401c1900d16035504c04548030045030b00c003a0980b2803c104003003042c040d1407042052a21130801113a211041304e0581d1507504807078900c2d0003074414903003100c6044480d01c01000302e940c400c3c041080040c2005030041c5076184803101000060560020b4090416400003500c000070344454109010070a07141c001000410b0760ba081c0d484041e11402420003541d401d01a00040a500008031410203800640c4a14282d195a650590710300d441035101d00500f503000e1100058950f21 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 111193579 1250 111192329 111192337
    0x403091e09050f04050c1206070807030f020a090f05060418020307020f0d210203010e070309050f0307030c0b0f0403080c0304021309080306040608010519020702130221150d0b04020103090503 84
    0x60702003c89281031a10b015403c2400c1100d01600a80c80342d408110714200008015801840f1420500081c0d01c1c3c29208402418507010340042041c00040d0014081d42c0c004041e00445a1800c482e48400c0d841d1003c22181c1e2003a88208103e801c40100360360003561150b8002d41e0000e440b8011a00c24900d00710300b840c2058011829174010520550040020164103905c041d24081403402c11880c40d8100344400070000001f400d00ca040640c2c480c05502000700420448810b42c1806080f41d494203c01e140c000c000c41d035070700001c451100100d808518555520782070703030340140e9254840700119581c0e040d13218081e800041050340d001c1c11030382603107541d42164460480c417140501d448503986e01e07298091005503486603200c40d916138505006c00c1407168040000c10704003c42100e026a441006000050003500a84801314540344001403880c0442d006000002610020014900c42540c41e5503050302c82503c40790707856421581036400307030707000404400440e544140705040015280f15540c88503451908 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 111194829 1250 111193579 111193591
    0xa060509040b0a120606091b0f020a0203011517030a170a060f060309020102150f01210602030906040311010501030203120706180305090a05030f0a0807240f0509060403091e0905 78
    0x20800c01000d0040038046c4001610848030140003000010505460303194015068000700106450608030143c0300380503417000d064000f0000c0c8102180d410607013641c5030203886101c40c5400c015281058007000030082d10066003c51b02c95081c04071102c21040840e03c001080340840360765500c0c001c01c03805010480c60026102c239640013b161400f034400a49011513029000c0c00701e0b000441005035243c400c0941c1170540c1d485481201c400102240c41031220611118000d103168004010003124030300008440b8412030082c1d8407021500c02d00442c00b4200c1e0000e01008e0740507040f4415039444050001c001b0011184210000a24044501240003100300309200490002d1302c00a00d840352450554400d0000d04021400381007204070781d81701c0742e03501c1c90142c4004001110200d020000e2141e0341c25000c9175103151203460b0840c48507804500c0c0c010a0000013241c46a8074080100e41d0340000080c13200c2c402d681c16190390141c2800d10541003910701501c800786550381601031000c92010002e00030580108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 111196079 1250 111194829 111194849
    0x201200414060f040807051503091209040f0509060601090b0a05040b031005030307030201090c1e03020f01111e160510030b041b0e03010b010c2312070f05060f01050a060509040b0a 79
    0x3a040c50200300342c1131310703201408d202a4424414426004000b1a6815614101a0081da505e9484502040103130214404026825160508010030079601080003841107500743e0310600e07100e4488000840c140250b980607400140144028030900320102d008680114a0a4040000700d03035501c0001d1a5500c106812001070351034040400401c2802c000843c0540000200a038000da805180402403c4c40d5120103803040d0440b0364880d43c144d0145580c02003200420040e0f030f07072003020645000c0125007051034074601813240c01d01c10708000c8088070080307064441c02402e00141280d20030301100a0001c4c0c16225500980d03038480340300c3c3ca1030240e400c0d800b446aa51922200e0b0340c2803074205404c68440c0852541403140380000000007540c0489850344100881822403140c1070300381c001600d8a621101080c601d001c0014492041c030003c03910b4690703802e00c214104c82c05541c40f40828001406c003031144907040b883c103e03024001c0c0d50040020303000306200a0000100c5402c030f00c00261000c0c3c82a80700c80c01e09 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 111197329 1250 111196079 111196093
    0x70b0705013c0207060b0612011406030105010c030e01090b0d06030c1406090904061103071706150301120305190e130b0d02040b03101401060201200414060f0408 71
    0x2c24540c070101e50000a19181c0c103036107070103160a269401c00e080d5041c1c0142d60b40024601c08109050348425020403000c0c050035156800c03203c00b03200d14403080c01819001c1144100d081094a407803011a4140e6206039147c1e14083c00036a816102402c62502c00c5050000c464800302d00309492501070080304402d0000850300502d5400d0003034400407140c0205030114500d0a00004139121107040380c0302004103035640d094a94450821f0401800d00e0f000803c0002800401e206119520030340001d0501004019004141c039010104841c030004101a403c400c40280b004200c40c903101034040f100380e4000e081081c038060799280d2003500145aa028507002ca8111168041c086c00c3c031205001f00e4030f4a10004010360402e00e0006034209502c2c6e1b100070f00c61501d0381c4442c84152018809194008074a0005004502d41c01481080e81e9100b406100019072070080009060820000c0601640320100b100516081c280100c407102d22038070b91402030300001c003080103c01810343d500c0104010055400038100c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 111198579 1250 111197329 111197351
    0x6030b18040c05120f030a110a0c0b0301090b0904020f060d06050316091409031c0b13050603060a0908031f0b0301080a062019021e150604020304051c02070b070501 72
    0x4a1000c04e5500800d50700c4002e500390500c80000c01ca45e503114013800d1180e12145046803080c580a004440203000b591038040004a400e0f00350081c505070b40c2200c0d4144143c400840601c280c881e0115406540f0000112040c00d0358280840200b0160040540105516459002203443c25a41800e0ba403080d0f100c0f42c008000c2e0761424802c1e010801e00142e0040d980c0e0920041b901e5490042245002d00c0c4911302a114459998540c464400c0400103424264104410421300d8010704085482c0c0780240116400030320515407900c030b20400c070359001031080d0458030342e011584e0034403a040240d485003904010010504107441e401541c0280070340801030008040b107140c00d000f51a84640102402414602d2240e0002400c1003520100300da000342c4020070200031042246840c0d8109007003d01460401c10b4074464004c01314804051038400a80c0389102c0e2920402c1c08224032003210007070456085000e00199950a80da81050003442c5481211030641d21a8800b18203607004d076000b250309070340d1106c0702c2103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 111199829 1250 111198579 111198589
    0x30f110403120201050702120d060e010e07030c050a23070b0103050303041b0b0f0703030609180507050a3203010f060e0f0c031b04120606030308180706030b18040c05 73
    0x1500c610346100a1001d0304150502079a40c21503600c230407071883c10100740c1c042e804165502000c02040c46040380103255075140d0707450382450019140c14000908100c1c1848505004004581e80c0310f03040e664040003110201d0135a40281c111094448002e07000f04001000304208406d02800395000d0b5000c1c681e00c2c01d180c504140781c3e103010404080541c15140c0200075141642040c0c1d0705003036200014a0360785000349001c030010415908000081031400d040307641c01825000d503803214244540108c59055440e4410402140359910410b8125030003003481000c45000f00442010307000d111540c6048030310041c00042e09541c1c641611218090b41c5400811054440310a0607800c403d803816201c0081c2031200c6003114510004042c0034a0081c4907480c0c2180c481d4290480d8001d11082c034900940752018908100508541e2000707500244d180d02c042038650229401d120500e001c8180106402e034602282a409010074900c41d40e800b28880d80c01000160044101900c150f11400e4130201c401d0415003040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 111201079 1250 111199829 111199853
    0x140a0216090e0a02040209030c041113090212060123041d0606180405090712060501080607051312020103021606090b0702120d05040203031b010e190b1501030f110403 73
    0x141d15500b0480344082c01d040c04100b50102640541c0e01680c0c0300025404245401070403c03a444c2c105281015034900c2800d10800b0301100ca000000d002052580c07598120180e0060102e26401080345c50085061b56004899281e08685c181001420701c0044030424071254105512919a020310004139174801d40300180f00661042c02150454180b44120403594125018001c0950059907901d0105003107010801000c1d0090203440055082d0410b98031f030010140600780305c1d0803003d10552000c900c005008600341d0340c02044601c8400d907528130b000480e100d040c03a1140140d06140c1e0800ca24005540e1002002c40560701030b075800320300b45403185001e03841464014940b004540200c58400381c540180300494000045080020a890301c03180002030440c03159107030382540030488480d00c50b05500190807a581d44840d4000ba10100010361080b00d00c0450f0003200140a100c45000103000c095000c0840f245c0d10006140000e030342421020480201da6250511105100002c102081000170080080d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 111202329 1250 111201079 111201089
    0x30601030b1f08090f0d020a1104090803040b0c04180209030607052b021b06220c0303120902130905061e0103021314010e04050c0d0308010504020a140a0216 69
    0x28049040180b500c55031869200a40c407020400d07600c3c00310300c0c1c056040196103101c0c000c10301550100c0c07211210103913481c102500202e0b041000c0005141c003e103403601c2590420790300310705d00c02e04e15542c5035520043c2000003072642440700b0042c4000715203c07042084070203280840042c01aa61400042014030b00800102080e007045020410140c0d80340c21607500c01c00480c159401c00d42004007141d100c801a00034402401005041600b4440105c070001840d680079401501010084c0c41901019a801e1500b2000107004036401440c01c00010380300302c3c40e18042c000703140000036410038645c0c0001c1944d244100c001362400c3d15048500240641404055001113110105080c032007000300c20202060414400a48100e8004204030100e4030946c003c01c2900002640c200c03100c0da11194202041c04040d20b00340e0341481070314940641c07800d00020500000b6050b4a0b1380545c5da103441e0400011303500c2200e034201007000510728401e421001b800074010001c4690088d080300307900c052040e51103014076440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 111203579 1250 111202329 111202339
    0x140703031115070e120f010212040b090f03090d0311060403120b0102191119030f0308010e150f03100e0312061009050907050c06070f080a06031a1f0902030601030b 72
    0x9002109030448040c040113001603580c052424614001c803402c5c24600408103946500000780885000c8443c00303103510031440340c640c042040d100d090200799034044908400401da8801c1117610b62a00e04401c1508a003842481c01d0f80e248440130005c00e091402c2501c00320302080b0710010110030700380c0e0703400fa88500080a1006003440c81d50585d0b61401c0030214080501407050f00c02c000072050710740142c5101890000590034910596928201c06d00d4400480702340c00007182540040b4610420704042d5014a1a1401c4034111b0032140c1c040010541c1210034696052180400409914056000c4c2c1456198200061034480701e402859001c003060040205d40700b140d842c44503403030311340d04150035130166081510750148542e00d484007a1110f00c81c2d40340544d000d01c540800c10803561780c00300114400e41619607a88045861f05460705098840500008180c040b510788020f04600404100c280d10204d42d10880f030035490344040d190749582058000da248250000104421540c1500170f0000d00701781510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 111204829 1250 111203579 111203581
    0x140a02011d061903180309060905041103150f15090a0e0f07030213091806061e0e06210f070b04030b070c0c0f080a020117060319140703031115 63
    0x1101403152410000410901d0f060300e2040d50b1080c0d0242c070044c28180503c60400c0e040e030401410790f112622542c00098424400480c050a10380507103510103282c0c0344458292784031900f54188500148403103c1c0c12019100400d0135941d20005a4095401c0c40e400040d078581018041c4813031040c961f0015065201c8000602003031a50314240d586c0c4c04480d9140050326010074020759810074600358041d20f55039050211042c0b1009240b8180c2008612440b000c0041d190b8a4000c03080005001c11142c440d11010a0200310403465100407543c011401000090000503864409190182d04c6841c10000d030322140241a801a0400c4820007501401d4241d50800e480c40c1d03155180380c90010824410044066078010400400ea008032001e059011a003242d05500da55805594100712141a070000e40d98000038010030340d4030f1945a0003820082c026003405d0840c002c80b0040c070890407508032803140e40c81c1c2d01c2117800402401454040d600c26526490784080b004503a40ca0400c210b1004040c00941c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 111206079 1250 111204829 111204887
    0x60a0605030c0915010c0f02130f05100620070909050105091b0f0411070c081c050c0606010c020d05060108010f0509060f070e010c0606080f12030907090b0d140a0201 73
    0x90703005691310b0003460403440700811842c0c6001e40b0030b01388200942001e88282c1404502d07001d40c0003d080d0016404041040355a419110114035138036109020114022580d00c5040500c810a40d01101c50410b00311000c007607840c14080c00301e4050b000141c0300f0741d540c0e070700348800c4010a01c00c400300401c41d090301560400c00d1130006006c03443d0b29813031075201d00e0703445607800d05c000d1011007511032054103c0c000c201620783e943d28040e00c881096a942035607081450919103018043c10560b24484580e800615466941000569030140b416030141c0e0b111002901e0040052010085207000c0c118074070001c6042c40b1413645260580c0d401810010603500303c4001c02012403c01194194010b03910701e0000c1e01a0515001680c0b1504203000241c1240d05000011401500004401c602c0000070800c0303801c0c0810000d01c0780c211303000566080d000c5400c055000c108010b402c0c0c101d1032031041c0c0100800d03c000700c2a40d4142d009200c058555209800400946c01035607000b01c940020241c82606400d01b52120b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 111207329 1250 111206079 111206101
    0x307060b013605030a1a071b0816020d030c02032802090a0b030d090302150705060708040204020904050412080105040b0a0b0c010b1215091203010308090111060a0605030c09 76
    0x80d800004030302d8016a000014a5406440100412028082c1c91015a803420800b0704e40c1c0000498136600b00d0040041144144614081c011020002c007080741c1c2d907021540c2d01c0c003580c0c1c4422180206d0202105031500540d4480f83c075400100d12a840f1903002d44024030601d800c041d240781100c15100103c410705480154000e40842245504542245e01a031310683d96030001c00381c0c40003040d01403080e11040d6200c250402203250649008035030010101e0310020944d0b500c0d00c6100e1000300700b6041700b4041001c0b60300a5102d00c2c2c01a1008001600f091a048081030880340c0864007a80d0414035010703440d00c10354000030340c540581800e039000d1203d5201403011443e07003001403094448544001072400301c80030080d0311840c2540c1006062070501f40b00b1901c820380d1341070302051007210320382d02d20b012460040300060f0242c08080c40070070b801d003181e01c0d68803070301120f412400002e41401f40c4c09500b0420168184003c51081070241000500d441c00c04c0140751030a14040155030042c89680280100f91a078 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 111208579 1250 111207329 111207377
    0x7060504090903030f060801020903190201020c0910050306040809010e030a02011b08090a0f030215070c061413080105070336140105090d030c0201140604050c09090103050307060b01 80
    0x1484102003601c0c441c0e0303d022402041500007011400c0e2030440082030b03401c4190020000042c0c22011102c8178007040400c01d80038982c4480080c0981c0c801011040303141081c4c41841e034440b82c40e0b2070300c200c080d41d5000400d040c100300b02c40403100b0100006000c2c0e010b42c0c1066200218810903001420b4040382940064038010700d0080da0980070000e51408002c0082040c00c50302c1c034180150011078125583c0c600a21400840d0008920400c2810f5050310084034020079504415085034500421603d40001958825800440800c00500030803611003409501d000c80b0340104901d500004551900300402012230313071400b500d88020750808071061070407030084149070850010340048401c800158074090300c41180351300407003826509003010030510100c0403d900a0034421900c1c1400000c9401004030f00700c0b4014100390660b141100c010600c1400d159005550101000742e2003490000320790001011071a090780210780d143c0c0000713000d00804c04240681c41e04000e0a080002c1006032945490000c090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 111209829 1250 111208579 111208589
    0x6020d06051c2a03050708030c120f0403020405060d02041a210c090601031d24040302031e0c120304050706050c100209010210020a03020d05010f0501170406060323010e07060504 78
    0x440303003d01c3e1900201c440704100110350001c2100c1c1136940c2e5100f83c544030742220803900450301408050141045024049032a10081003042070701d014103540c00c200007885d01070070310342d08400418190700058030f540c42868040b8030306911680c50b603003018040007085d0314134500310040305250132a91507403a0b0000540039550001140e10000a03910800101c0041040301c401c20100c0801100a0b8020f000115541803214030742808404410b288100020412009807001801a0b004101d600765001c1001c1c4a4a8907143c6804443d24180c50032007454500f010072800c1440d40e010000503c410031000308560030080c0743c10b051103810a0700850200751250700310045011181c0d0001034241850b80b081c44880321000204404544807516910020001c1d00010b6605422603e028008942c40701c100e0812811120140d664014081d441d640e20440400043d1080701c05a44501000c00054002c4541009206481e160b43e5140c20090210030301392005a1400c520a8100e0700061100f50b0340942200e080e51 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 111211079 1250 111209829 111209873
    0x2150d0501060216050918060106051810090303031a0303041503180c0312020a080f09040b0301060b0901030f1119170912031509070e0a0905010b070b06060706020d06051c 75
    0x26071003c02e52100b21100d141f9900440c02014000708540740c1010141101d00c100e002401071142000c418490007402c00da0f1180302040782e031401000081e120340c00081c1244000a42107485c032441d5002f09156800507040707202401c0000c0b0036402500c0c0d051240104107218840c40005c00c151540300c41010350071a01001d011040e094000c41d174181e00800c05190216402079240f40e1341d191540d81207100c2e811003050b003842241001201411403505014130300641d4428940c0c1c515080180e001580100092507202e40d0564545c02c1e00d0812840e060042d03c7c21003080e10a0034900600c40303600410214031444041c0d208907004050000715100003c0f00c410703400030010b040d035903515400c14041c40d040c8810400b5502041c134000304045540d20042d13001821605850400703c03a230300c030303410701b01070743c00900800707645c1d24091050602007071070160186d80016015103550316040f1710f900d540b42641e0100c054101c041d80c8401040005080c00c400c40e601401441e00d1203846500d880d80c0d141c2d1031400380c00c1c19420038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 111212329 1250 111211079 111211081
    0x30a1812050c120a03050612010c02100b010909090501050a0b060c0606040207060b0d05070e01210f06060302180613050423010e070e0114010c0302072102150d05010602160509 77
    0x1212081142c00f001083c814455910750358020401000380c82c3c129103250050b44003814100c4c44190500a455800d001a0040c1c110490345400f01d034010000051000d0410116038070010b451015840b8000f222030050001082c4c41c070300a0381c0c10f002e0754009400c40d07014404c104840c0c4400000414040c0c0c100390115005a034803091410404007a001c1203000c1580043c4201c141d00402c0750015600741180c0c403641c0140d80c140c0e6a0f05002d070341c0e800d44050700c2d2140b034031031001e000010315081c404543c802e125910008190b038480d0007091040d088a141001504070400c1072141c64030f010600e0015882c2880401d2206150956400b40030316040540401c11207000c8941640c503030070a400c451002007410381100c0980f50341d8080e410464000703224000441081d030035412915449001401426600354000708690762521000411420341c01201050100c0e10301c85910043e603502c8000121200c04035041c07503c4001404044044031010b034016419940080211103840060001c46401c80710115600c0b401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 111213579 1250 111212329 111212347
    0x210030f09020a0e04060b0613030803090708070609091a01050403060b0d14010b010e040c020d080702120a0f0810060801090c02070308030702210301051e03030706060803030a181205 80
    0x7405040300300070b520000080002c504551604641d520172409203d0031700681c05500180595403150012546098169038001d1000c102031400850304454148101c46c03800c2d5441c01a40d00b42010343c1c21140008281200c200700440c801d020f00400c114080d451250405004c2e40040d000744200e100042482c0e84031552100c0d20f42c0d41c000740d400d080340c000b16175408010aa150003402425075841301e6002c59001d00a02400341058800c06100000c1d5800405440551031001d6641303160003040c000840c8030b00b00c444000301c000c10010b800c0d4001c1b21b0301d0362007205981d608040c0c41d0060051050038603144501d070401145e0740c08250340b411680100400244554110404c904069031a00f024117000400001d01190a50008541200115842208403d1009040442d011344000e129043d4000007802c1c005075070700c8035084603510781e49009088900d020300c1036541c0c0003603440c44d170b00511070381d04003004008010019001d0000809202c1500380c110300030380d59507013590803411071405081000100b00d080c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 111214829 1250 111213579 111213581
    0x106021e06131e03050406180305030d0e0f070308120f090a080c01020c070f0302040501051c08090a270e0c03031603021501080d140a0815060f070602030114030a0210030f 75
    0x21010103000c150006405103420082c5c0242d00074401d1030005845501c5910940c2c5005a5510039294002c0c00381d4a0708000c003c04c1e00141245540b20080da005019000c079411f013040014000071803250f03640130b80340c23a60500d41c500021001844039031410041001c1208105020404201855000d6101622050b04511150090080c2100c407492031045500210317800c030031030a0b544101d03442290700303010b581c1e00c45040c402d0f032401143d14480b0324032055a43c00002246503024044007400134018260056551062050503401210b130801c01d20441295601d1103c65030040c0d9890361410303001424910401070201c0c1d035070311440445d001c0e074065086604080502c02d20000e040c10351450380c15800395856084041d10303150034035880400304100310300008051a2403000d40c0d48402983e22000c00d641c0d00c091080348030906401c501035001c6000c101c12070050b034000300030303140860140b07500585070f40c1407146c030350324880b010f0904511175800103800d90010380d078103c182c3d0560442850049036140000e10b1800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 111216079 1250 111214829 111214853
    0x70c03090914060a08011506050c0c06030a090201030e120706050a0b1f1101060b04050603040303060902030c040303090803070b18070f031104050a050606030105060a02030d060603050106021e0613 86
    0x30a8a41003400c0c0b818542c0c0d00203411802094120384420107550b03145c0445080310048540c180a81c40c080c0803c009141c081c0001d03007052030744101690280303188000001d04aa108603600c0c410380e036486050300255640b51140c600420901e200070300030100ca0310b003260546d005030744000745401d8440b400500d1441e980e03040880c98040c082c007209100d4030341c4c04019924501c0c1c03800200010344038131a007429000d01402450201c0301564089890281400c05001856000500907001d00d900c2c0c0900154040341c03880110711503601c0c041c4040d2210b0651800030078a0030a40c1c05688558010b128078004201c514003695000702403a8044002d0318002803000d42450100c0d4011310554000c00000800d020000e07080807803c003002c850800c429030350b5900000803203000391502d0f07400c24000e200611080c107000b401408040010300442c0c0c00c14803200203da050b14400d0300514000307625000100803540e0100441d00d51450140e60b8058052a0b542c070382c070b80d0703000018945030074410340c5002c66003400700c100428 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 111217329 1250 111216079 111216089
    0x90e010b030604120216060503060d3e1203030a0203130516030b0f0714030a020d02030907050307081515130c1e0306030201020a0f020a0b160204050601050c06070c0309 74
    0x1803400c0340f030f050808003105071504072040094000d60f00f00c1211042003400d25819100503840303983c1907460303200a1107018042d080c0c04440344010105481006404000404100005621f140a80d14943c04500c40c0580b410004c0c14000c403408694540d4045010041d0380d03000201030b000503180d03074403103404010100c1e0340813000e031660054015080c6a0f41c412105501524011115810181c03200000c60504007821101440062052503002d0005240b01000356040360300e0010250810701c01c024130501320303802500d000c085540400c000b0409810103000f18401003000d030b00a40009010361420f1421204024455040c69020074150346090b500d60b42c070950150302d03595082103c0081a840a04200b103020b1104514000009540000c680b1074002d040650f079040c1d000c1c2800b41c51955504220b041c4140049a2100d0583d60100c2c92200820140c559000d44c0c602c4071410701e00900511003100d40150201d410008104091074a40c8000207030341c1d4022010b0301d010031201d070060508503210700c00c0743c01c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 111218579 1250 111217329 111217333
    0xb1f080106121415090a0309060905090402040c0e03032a010216060908070611090306010509131104090807030903030323010b07170307090f080d0e01080c090405070306030624090e010b03 82
    0x20b002c94817400103411400c680c842d40f5a4081c1a880b42016180c008042c13088503440315100d0001070060610350015251042c603030511007103c1049800017401e6400400c401107505085802601040d60528103101004248900031854005c2900d007400b0041c4004c0d001034541d40e120305203a010402c072070003100e00c100e0b004402001310405801d24480c442c1e100e00311191003442904d0022510389814001e19000c1c0c140076803c0c224041103503654400789070134084010780c010380e1100d1070800306070004000d01c0e686110b40e41d515a40c03820b42c50003074125040108030b032518920407100c50201c03a5070202c01d24151550351403c40d48600704c0345480f030f400410141c00c014205102001f03101c401604559403000783c5100b161199010358554100030366a00241e0600000110348054401d100e50007000400e400040081d40c040c030741a02003021a0035901d09480080000ea070b20b0342d04006002c150b10400301a15030701901c43c680c9000e076001041303565015010701d6500699440b0041411402540400300c142c4020307003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 111219829 1250 111218579 111218581
    0x103021e030a0c0801051e15010e030303070807080c030702121615050712020c1b061201140a0b31030501050408041e0608070c0606030b1f080106121415 67
    0x81d142c0780c2c00d0381c0f620511090b9824200440d040380701041e03200c402c00802c42c5003071210396207410034084102d90403100d00703040c004840750450250b02d0600003144102c541d52500800d50500b444000c004100040c18031400d0641801800605a8086140d800c076804903000c1e1900d81900c603050180384648020000d110702950001c0242140b1a47c1210740300d180c0d152544400c2d8921124107105a10031555009000c1e0413012002684010300b0182180c00100904020b041c040740391154000c1c244281c0214049512103400c0103010b14100c42d22a029103840c0d201c0600300b8074500c1262a50840780c0c0b11913407004103d81100d60140031a07041076002903800500034052400d09040c444116803081c00b946100c22070354000c41c0c0400d40781e540b40604865403641c86a403130390b9030b0702800c1710a821400b400300c8030f0680b507a0001004c01c11540006000d628400d84602c500010b4030b50f900000d03052681b00078503c0c0d04101e0108480d2090080300090b15411402941c940d0402c52031140c14a4500240034810f83c002178 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 111221079 1250 111219829 111219833
    0x106050f070614160306080c0f0603040302150408090f1f0e0103021303030905030606010c08040e22030e01080f010f050904060f06060c030908010605060a050a09030b0717011703030103021e030a 85
    0x42d0744c102014245440c10007840d900c0b680002e071682c0110030b060f9041462010010f98604054005580c014001d1040d00c0750100041607850b440710065400781d4180e40c011801e1b07000e40c58000f00d4a1380c00351044501d1012008d855081c01c44a40c4500d0124080c072000c0070f4500c2642e4000e8044408451907240d071651040d4891401070105541c50140600a120301000030303c0d10750041c0b0750f8190320f80d0420640d40c10030f0710b0f00d031030b074140c800300109100000080c2012440105c0301540e1112a845e209031101048440d0040004150780001860301d03401c022010010444039100403002c0040c0c03481950129520380c0c6a0421002500c0da840b1401c51030342c0752410000d08568403002442c5250721940d5801030543c6d6a82240e4242c442c00d001e11580440100a181d05042c080c0d8001d01043c541800c24000899803601c03080e0706044100c80d003101054200b16104080d2a285500c21302500312500d03082d0341c40701881000d658178041400000d00880c58407508041c0000d1103951103102940007012600040d5880c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 111222329 1250 111221079 111221101
    0x9040f1401141003050c120106030206030c0408100b09060411090904120908031201151701090b03010c020f0a0b06010c150c120209010f0509060405030709050f0106080106050f070614 80
    0xc0c2101881400144049003c05030240341140c02c40b0780200003071800c2080780040010b440a540d02400c00c40d962400c1c0007005031500c90240d4441d24007500c03195115850809018200014074800d60181490300420308816038400c42c07a40d80000d002c0d40d0009003458a440102001d208481e4401c0d4806c407840e04000411403141c0000504101c240d840c402541c2d52105040d0307590290040c0d1a1180c034002c80140000e1410600e030000e80b9213145801109104039107100c8070004c0c3d00380c100005903502c60203c0071180c02c4c2400b07002d0a8428920040c600200740200540d03c1c0d01814000030100980c1c070020840d142c4c4141e1628040701e800a0242c0c0085000030481801042070b8407003040861446040c022000c4810700c00e6135481801a103d012820719000400c48440d071040786680e41c811428400441c040d1000c00c2041701601444900142d182440e4120f100e0316807050784075400300405e2030018081998801c1c113481e1580010050350b9110201c91401c60007804d822400b50000142c40e0003000500445 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 111223579 1250 111222329 111222341
    0x105100501110f0d0302030a0914070801060512030f0703020a21021006270f020406030203060909030702030312040f120f030f150501140c0613120c1109040f1401 71
    0x1090721030000c0090741d040c2d800e0722081085a04840740e0445a07000d0704042c02a002103900021000e8002103d280a6441c1603e000d40c0b112110f13003030340c800b02c0c0a200c0708209104500180c10200d50440403058820034880e603c0c0300728a04000f000b00c1c0400c40e1010503008000d1240d40030f501010045150342c02c802000000c4101c40811700044c41203400007015000c00744160400c1e42c0311805002d0b0208280350104000d40c1d4211030720301c4031135079884000d05e40b2002440a040945421342d00581d8074200702c0100b10041401a00b854120303002042301800590b4008103ca9451007800c0030300317078180c0e41c0342004151900d0301d020140000c202181d142c602c259001070058511585c54070101f00d60102001c030300040711001d0143c80c031507900001050007258004e800b90120105d8401d4004d06e0801c03e404114140101902d51080d548056a800d508100100398004074291091519040c0d8a009444403400920040c403540d000d410543d0200c3c0510400c01071051640d60403d18400031180140b0342c0500800c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 111224829 1250 111223579 111223589
    0x213090f080c1203130201030905150114120d020c280b040602060915010501051c11070c120b040809030c150307030e150c0f040e0c071110081b0705010510 68
    0x14621100700d211a60030075a40640d0f05c00c0403040543e00594010760082420f400e040d1050311941000200a001c070860040c081c06144140c000c80c1c00d103000521200e954040f40b502c8072a0060002c24030410f80c005410f0b4040d0108a9010b450f01d8081d4140305c41501040c207079a600da681e8460701040c842811030040c0111384466085504036514a204561904003000c0c40d00714031000280100200d602c03540c081c00465814044aa0300d40ca40c2080300000c840d41d82d10b00850314000428614284014242c406004010010075454103410030781d110420082e00400040a0410201703002640b43c07030803c051085c800d0b0150160100c5484280210080d0308200e461200190400091919684002c40e5008039024840c04070702031502e422a0f400d159030403408070017642030828040000c844540341307000c034010b81c0710342c0c000c0741d50300d00c1030802290000403011440d001380300c0c10f80072444223a8008019a80410303c00d4200c030b814840c408032072004d440303210806040c1c0d6082800b400b44410300c1018500c1102c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 111226079 1250 111224829 111224833
    0x6020a0209060108040b07030b01030f060806010e01050d03021906020c01052a0406051207020a050618060a0e03180f0a260c0102030a080a060e04200301050606070213090f080c 77
    0x164605004541c513034030032500103107804d05c00000b060b00503001e80c1044601c4041418085110351700321000300c0498180d5807011009a01040c01044400d203545411405050144d52208c218401c0340c40181d990035440c6141c030391900945020406102c00c540c15100728620000c004d00103403e00d040300c1650107003030300300000d092411209480004961202210110b0302c007a12164104082105182c160410007080202036008202010300001d400703000b1248141d60030814185080c0030402c0c064500b56004040d103100a15188401d103c4007030000644400003080c5820200c40b43e10b50b408554407925a98540d50040082035000c516008107125221008002d01841408400301ca040155248040d40b02c49001d6042008078021092240c03100b103910070075614003c28130a60780c05000030b039803038102c50035180c01c040301c110303901441f0514440229801c0c1c00c40c000d02a0303003880000601c041c03290ba40028480d900c00d20f46004000455000000100d0300441c0c0f00e403c442c514203000b9860340c001d0200e81068 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 111227329 1250 111226079 111226081
    0xa0c03050702070602121b0105040b071107050906060306010c05030c210711060304050a020d03051207021203060d111f081b0301091a0d05010b010927050c04030c06020a0209 76
    0x8030b100103126000c03950781754001c101c4c2c0c103003a80d5141456071144454201d21103140302c6111000f4030034041c10740103c0c4600c255050920313282d03034001d06146604088020300c0c1c03c1080304001554403942150342007a8115135041c0c2d25250f800c0180c03816514400002c042d40400304244c0101d2a0106000603506000030980c240b08044c102251910301c05c0c2c40004003000c900c42c110f04900c2c20994080c541c800d20070382c00c44408001507000102682d8024401310f0002704002b4003000e4803000401072642100b45030009111025a03035075940c60700d01004007203d0203280d81503244400e000f50500c03003010000d006020342c05600c004041098110b40c082d440a0041080280400e05200c1110000c080d41ca643c40801411070f4208070b1001c010b0821043c41034500d88034400600e48a5650350b034004034282c810b0000141c1e0416440024050f404143e0100c03035442c03120340b40c03011419042c20f903154a01600e04d000007002d66403800d0b00d14003401950800340a0f003003620400300300c1d41e030000346400d02d0034001c40d984016 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 111228579 1250 111227329 111227341
    0x4031e0203030c040b0a02070308070615050d02030a030e0a120b06100801080712110301020d050123010c020d0c080d050d180807020103090c090906050402040e0d0f180506030a0c0305 80
    0x56844103580d00c3c1d801e560200700400c180c88403400544508000b907c10b451a084d9251699249908510b100340c2d04076a50700110010b04e000d904030350300200010741b0220300501080d00000d842d410f90f503101506001c1100c0d00f81103290b9999800c24050161600c00010010803400c3c078914681049900c1405008000000343c62140928070150480752000001c0c042c26040207000d03000c141014104071440c50507a10395480c2c607035003030001d015000078a510008540d85000b00703a82002c164500f074061220f0a00017940100c2c2d0f48400c80020054041d1000c81103660a460f0a0f000e09103182d01214490103082c0c61001480d41c44402031104514400c018488458010a460341071040301000605542c01000320ba0300650081d000408c416001e20785518000d0f9440c0d007050300b0b4542034030007110b40503600d404000461800d88038641254001324000c01c150880d9100c054840174000d4100700501208260700030480c9200028000a002d000d4480c80d22810225000c1c0d0142800305103200c04241003000041c0c2d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 111229829 1250 111228579 111228583
    0x20904060303020c100507120c0302030d0c020604050106091b080c0c03042706060e01030f0b04180308010b04050904150204030501110a030b150f1e0a020d020706030203010503060f090109050604031e02 88
    0x39002d030001c8e040029911041c0c025100c070320410f0421003c0d400284030740d80d551a0188190340703860343c0c00d402a14962420780741042c01c6900039000300740400d20b00307801c0c11b03d2250120762000013030840d82084d003440d031981211844c0034062545c0360b10b203603c0700060218210010f0040310441c141c10031710020100c02004e421308107070b80141c000c8000194110400c078000c2e61003504141c140075080907000400d0310042c40443d00f6036100b0504a501941c0c010780c03000406a01c0b40100d80141030304034030542000c0c10900000c0c4644809007000c0c10203135540c400305c60301c50aa54120f0300110341c488000c03c03200e041e5404500003a0480403070500840c2c608001a107450030b201184016891688000318034100503025132104036003081c610880082480500c0b10354040400c0c0041044080580040c0605026454024548201900520201401440104816200058419040114a1107140042e60707a040e10364010700f107001c0701809500c40d540600c400e06401110b80d00c4140f5403880c0c808441080808281e0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 111231079 1250 111229829 111229837
    0x7140c010c0605040204090c060207060f090b1e0f031f08061510030e0a0b0406050105120c090c09180109060b270a08030301080607090f030b040b0604020904060303020c1005 76
    0x60200380d480751900c0c00140c0c15800720358000e10081000400c1e945a4a47e00100b1903d6000707240580c2c4119814866150400540303030000d05603182c52241c40703051411810481c0038a009900780e003501d80401d040c15030000400d031441d1041c04d813100ca4136407400803503803103011801d84545841000000004682100045510b82c424812140b032100c42888400a104001c0006840340c2c08040d95200c000303c200100340046c114441c026110070340c550400c0d0622500715041a40403500c501c0c100300c2a00801c900104200301a418204c96001c0300e542e03221400c5c145c0348602d141080d84010610500b4106814020480b41a6680c1c1c980c10030a05032210740e000700b94403502d183d082c110420300841024046d0912038a01c5180030107041d05203040e58400d400c5242d50004e0700134004c140c10000c100642e041d4001c20980c000c0c610903862a803440d2858442e440000381c090700c05002010910009480c0303888540407954400d0000e401001b145540e4200251292703040100c0300d210740d003401c20403011a031240c0280c0e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 111232329 1250 111231079 111231103
    0x9031b011a040b091b040f17010c030b15070312050c070605011401091a090d03050304030e090402090a0203061203040f0906091b120b0604030f140a05060a02070c09050403050714 78
    0x100c581c640c8140c1c05001045c1c0090210391000811001c1840f0303500c52100e01c0101f9141c6c1001c40ca007585100c0907070a5072413404100301011301d44201c0c8192590340a40001c03035820810b0180d0b42d6600203050031a809001d04280710240c07810f00d403d006814a810300100101030281108000507606e90329540c0641540074182400940041030030321500308894150b518164070140e000d49407051030b10124400b42c0520381c0a801141020042200b85604400800c3d0880011904252145066030010f44040000741011070038590210000740951540180010000e400a08803603e807070340d40e54002c050006c40d025501e040344c2480c500203140c84c1c0c0d50189003001c0e815480e103d08242e200f00b1040350700c0b0404c00600e40c8542d4948140403000d4844200520245d8020030840c0c902805c40e080c1100d0350b04035516070300c0135548856010341c0401d4020450b076801c0350440a0140c1c0d2042c841c180501042010f80054003281e10308014032040540000041c5251880b6407864200c01c040f05038855101c0901d0160 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 111233579 1250 111232329 111232339
    0x4090b0a1b090b09060702090f0103140304270e060c0301080f0f0c1005120a020403020f09060102070519090e030a230301050103151d0609090708120309031b011a040b 73
    0x2c3c45210041001341030740f4100907290b10f00b0000f080e00000c101a40584007030140c49400d40041c400c1c001c10369510100380da640c000031032900d0700c2c01c462404404105000301e51b1403042e0741c40c84117056200360011000c808004d022a45a400c0112040c1c00c0c0743d0080c031400c0c4480c070420350079005145010800712007600112001d13051500061013400300b14241c2c00d1000b020010b04005000319086101009800b0361801203005031124110b1060181d07c03848005510700c02d00e1100700300805aa0700003406001d80d8001c0e0340d42e0705440241d041c44161a10b1a0700804a43d5050814019081d4000000f0f4050600c841c0c0e5013030101204180f005e0106000d280041084ca00100010720065000360080342c0c06000484007120100d66629413900c0c1000b0300c408018070789507c10240100c502d4814070240e002203220002d00300d0180381c2082d540c0d5034000076040b881684800310010b10400c4080c000c0e41c01c68844c0d00003084400d010f02050900034619802c1c1c00c0d444098000326800c490801d44626840e460000d04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 111234829 1250 111233579 111233597
    0xc1522020d08041203090303031a0918010b04090303050f07050f0403121b0318170d1b0c0f08060f04030e01050702030a121808030a090b0304050a0204090b0a1b 70
    0x3880030008840790141c4000008200002d0804503111814011500a03507508003031170b0551500500b5211501e0705200d1480743c00a9140c0f0603601d001c44180c01864540e2104541c100c40038081d400741c0451685c40c0d5011b031911080c84107050701078029612034903201401c09c2c1169910281038a06001b80300006002c1c10081c00140b0008030304000b540090700322800c1c09019800d0144280176003040c004003c800180381d805d28030b0440d072482e404400240074040307aa26002c1c0c0d2040388c2955504015031b04401000a60340003803a02a40310810341d00119044903d180d001500e0340c81c5c045a00c021031080c8038540c882c800001d8403140039005400d015540c140e4039102c08619000045413a500900310590749802220642e0001500100046482822a40320004091030f0300a0b208501403060740078041d1508200000c0d40d4059002d01c0810569020b803a005880f610755045c01072801d00d80c00e8009402910340032000081c80708001d07d00c0d2140e030302c1d501c050100d01a00303041e1842c1c5001c80c616440104013482 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 111236079 1250 111234829 111234833
    0xe12030f03071803080703030e01050a0c050a0f05090a08070305062805180706111b0307030303020a180f090c02150105010e011812020102010e07060503010320060c1522 74
    0x95000b041e01c5030700e043c64408891310b94503007007011b510a050490100340c0e07403010121100000c1c01803030350102c1004020044480c80507030107040c510074241c600c0100700100e0a00c10040c0e00480640d10b4100d0041c2460b42048d444644103565a40a1700042d00c1c0e42c03140c0000151214410768090136265101c0c41440c100344007012448000d442c0260081c0412600688040030340c1c001005504000c00b6030f0390310803a080d40c00c8040c0b203040c030400d003200103000d101441c80342240d038500041035012280c1c035140041c0e4403000900200e4401c040100300d5004000003070400610382500d03001403400c0d100e001a08008c42c800000041e40e0710241c0b0700c03000b40c0552000004204a60203003250181020041c14809041c40e50007120140c0415541c00c4210034a4101c0080400d55909100300682d00343c83c1070042c00c0542c1094000b600d14001480000c00660703041d1103290b1501c0c40700d84c6d80041a0340140280c0e4562036812803081e103a0032500d10001009000741c000541410846c1c96407407094184142031000c00700b9607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 111237329 1250 111236079 111236087
    0xb0906070c0803030702060411060a080f180d0206011d160c110d1a0f0403050f070305040b0f1810050d090203010605031c03050114010801090b04090506070e12030f0307 74
    0xd54000e4031205114107000071500014070007948100351503406411075180c41e10300384003c0004203071007034041c0d2400e10881d103280303800400a5800c0f182411144239155a0101285000c4840141d48541801075423040e00d0819000180135050715000203003503822803184a11407800c0d8100300c412201d84445038103001e1406002e460b03041d0880f4003808280d4030004481c008501c2a90b028074080320101e02c043c1a003da1008480d40c11500b005041584407400d041a84006145000d0020150041880060014101070003002202c1c002c00345514800d449411800d11070f0701701d400c4030001980c2055111030b050310303600d0032030107000740740515851f21428140c070118000003c041d8480c00b00d03015961840041f40555042214810003d1408180801c1d44a001c0c00201aa8070690101041b0440b024a0115680c1c019004c54151041807034002050080c3d6400a006805c1e6520050326901402082c40301c0c43d43c6c020180c900a80007552800d0030306d010b50020503a80c2c410341262684001c2c091010a50b26482 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 111238579 1250 111237329 111237337
    0xa05010318140318040c1e0215070f02010c0e090a0b0a0b0c010615030c0c0312150b040503070f0b0301030209060a0b0a03230405070e100e1005090c040b0906 69
    0x318082280d0400450b610038420034400346280100da8000b0501500d402402005180b0340d40c01a202032000401541001d4503150440300e002d60490300b14005098002e100304401e4040c04405200407565042400c000b1717000c404400b00c108010350030240c44011290045403280741491020b860170701243d942409407001400d0441c40c0c190b11414418000941d050705001804d031b00c0c000440001100b0380f800000d01ea2200301807030448145420014183c50180e004001e004074141c040c00c10031300004000c41c1d1403006102544901c4410900317817101181e28003061b409001034070001c0e0201d40e1940d448104070807140901c1e228403c00900f0400c01440103091084100b07400c150b0190102204070b842e482c00317840c6a0045580c64000990f680c00320100509080701c05203031040d00c20940c0d45103051548130140c55880e180589030344030719800d01140d042c1011220140090041c620840c040341021078241084405522a10744030300070a202041c1d8070300741c4104690803a00c0c0d02000500c0c190200301448180c0d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 111239829 1250 111238579 111238601
    0x13080a0b0a110418020c0c010804080a030c2a0b070908060a0b0d0c0e0402090c0c0303060907050d06060c020405100f09110f040605071b0501020a030c05120f070b0f060a050103 77
    0x2440300040c20f044a581c03440740d4182c1355602585415140600038a410310000c41e050400000740280004a144c1104490341c02e0100d26005c038850241c000b0a645403400134122040001142c401c00f0190001c900b218040a0700c950b00c10941502d406200312821a21401180344a801a07808100b01d803046508c000d40c0e440003d82400d81441894441d50020940741d0302c172039000502e501c01c01045207004810540d0020f46031031194280300c1200402c1d80d40b0f000041809000b40640c01c007081d03400380600160785550811075000c0c4105a22000010315803a81c01404034011410000450110752101001d4425541940000d030011440c040c4440007522500048002900e01000361142e0706550700010001750440f80c44450f50f03201c0c1c920b0b06512000c1c4100d030310485c3e4440440280b0940c1c0e4085102c001c6145c0515004001800c203007401801c1412000d00e03804a0480061075088a4011401410300d4901440d0f0f16011940c030002d18040c0c15008484140c3d01c001001300a00c4258025440114488 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 111241079 1250 111239829 111239861
    0x1d0d0318020406080d030e0304060f1b050105070f0212030402031510030b01120213050405060c0d1104030b060901120f0f1b090f0b03010207021509030f0d0513080a0b0a 74
    0x14a4640100b021034005410804841c0c111001040f000d5800d03004082500b0b5040c4011880d140c9040002060344110300307100810000140d50801400622041e034405403030f00305000300f0035420f000301c0c007800c5a4034191460016005a01601c440c1d014440240ca104a40180c05001e940c08130f64905414920f0041c4040c0d0025901d00003c0b0120f80c014180780e010702140c00301c26401d4601401040040480b0140c001c403400c0c1484100800107a000c144190806801528580c03141380b0054200090000c0c1d03240b03464145008100001849200311015014103000c0c1c915101c140d0304c5181c0c41b003030101e5254000d000c00c0501c0c80f2503800205100d038a8091343d4011030100c0c1000070b0803601144d40d12510340c464a041c070b03190504d01140c90b5091080c0344c0040385c110000c40c50f21038942d0100e42c2140c0b50850142c0646070104055002e51002c1c0004610480c0300c00a5076844004084050416040303e140052901080b08001c2a211000140700e14204d03008211006d00d50754a01c0342401402e84103030380c10004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 111242329 1250 111241079 111241121
    0x20306190f090207141510080a24020702120304030605010e0103050a1e0b0f0601031506080c090f1003090c0906051f02010e2a03070f0303050f040b070b09011d0d03 72
    0xc1e014810015144126040d24140d41400301c403e01d401f1030305401c91580364218080030400a1912130381280440300300f00000c40300c070483c586810020f01992a000e90007461803040708290f11404401001941d00c1b4050410503070342c1ba0f961001c3c00d0300e400d001c0281184e102c1403c920104190040c00c0e0580c0c17080701c601000740c0d200341c0d407441108102951141c60080140007444210368141c0141d82d25a0b40c40c0006a8406141c0503000304a034201401e05020f024001484070102d460350300d40240500c402901421480b0340e13a000040c0100404c50041d5044a8a0349001c200c00d04103000d0300048442c020005080c184540c00c80c0d0004102c800400070542d903a036500d10320000320038011940c11050840c0705002e002840d600c0369040688402da01846600701c0d000502c4941c0d901c0740b000d801d032030301464407035220421050150068403030350300000d50442b40130421074108038100500d6031080441074000c2c842e04038800c24030a45600318120b000c4032908002450032070305100c0ea00c05d12800302008546001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 111243579 1250 111242329 111242363
    0x80d021308010903020f06071b05071a03071803080319060e130b0610090b03041a0a06030210030b0105040b07020a09150303140301060507030807050c0f01020306190f090207 76
    0x68a40d0740c089241651100c2000080c5034040c03040b04442c0c0e203410050700c1c80746070106000703000324502d80300b4821801005a008050100c09c01610000e8024171110840e00c8015400f0406290070407102080040e140b411a0501c01c0304a07404a03040300c0d44085054210740b40c8240c0c84151651070000c00f4005c55075a580040d04070440f111b400d014446214819194402905000c40e02c202d008207032034000d0b100314044006ca40da01070120001c0b140401981e94480d01e903460031090700c80041c1503400c00045c2c00b00034090f13500416801030084a200310350750381c0101c1d100b540560070380f81c01c140900e02180051108029048050008000d40351006042400440c1c481111034100d41e007240102c4c0c1d140e203040e40c0a00405400815032010680025002030666141500080507442003c2c802030401c582100850500c501950640300c0c004444401d070b03042c03201011080c034000c1d041202c0c801c0c8035400c0b29603d004080000c2c503020040e902000e410b840d0725403e0088030006503004500031a4410403203100040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 111244829 1250 111243579 111243607
    0x21525030c081824011e151404080109230c010206190e0102040b0d050108030705100f1e05150406031505090c0a08060108120309061303021f06090509030702030a080d02 74
    0x1c01038040c202e004980d50400a45640f1029842c1b100358040030302000902c404200c4492503820b4000c1460100313a41000b860b0034942a01690344011003039800c0022842c1002540518406050080392140100d1603030041d100d956a141350b48038901581151020130a084965000841840c4201d03070701007444e000b80204182264000c0e84007280c14200400ea00462012174060180101801001142042d205844298407840c00201100c4c850342c1d0341c060f004e10f0034900c1d00321003204502e1107040e043d2401841c10780d00c00791500700c41c1450b03480c000f9000c1c41500d01d098483c0d01c060720340005861001e03030200030401c00200000703440405c5522408100007100d5445c102c205d006402c607407020b00075079490003c2c00d5184c082140404c00c18904103101f0007904140000e4116800307441007158a9540001e41800d030300f0011200403c00ca44142c42c40a004441c2140d04408201c6105c0070003081140d40788641d958886c050070798000e51581040340e1000c0443c2c07401001d05910210700900516090080d1101a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 111246079 1250 111244829 111244873
    0xb0a051818071707050109050108071b060609150f0b070206070507052706010309030c0219150e01020c0a080d180909060c021911010f021525030c0818 66
    0x1c04100500e1801c03c55800709101000041c8420700300f005401c3d04040010380034000c028508020001c0072012400c0001201c02d1300807a40e41c00080400007192112000030152046680e10f001d012070364400040c8904000e14100111200c1056260401c0010350802c94540d110400030398003403180a0000c00d0585e20b12386e601d041094542400d04121013005002d50742c445e0024440c9051614000181700400d402502200a10b0703411640d400e6031000000340c500c01540b807500003503d15108201c5d80034002d60000c1c54082c0501c001d13021108100005810044403000c0c500a41c041d6811103045068071501881486104501c0f80e00460f042a850b00451004c442b4040401c0d80d40e5900c070180105c1c40c503010f0001c0411440d80c24609802e104090300c860014451140800c2d0421404000c001d400d00d100340805c03107640002e90101034041c2801504e0100640401000500c00179800180c0c0c25044c0c000d11542e04a003c83d45c50b80c82c0181d0b0b94030202e0072820f6400300300d943d607400b4a20604804c192006020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 111247329 1250 111246079 111246089
    0x1b030a1a15040f140303030109020c0307052e05040807020904050703120f0f02010b030a03180302040207140c100804030f14030708160201090206041a0906030c040305010b0a05181807 80
    0x400e858900d80380b5070590a1100758400d110560035251301c00300c5a200801100c2c159000c8000141c0da13401c903840400e1540c450340002400e1400303400ca40362041d040944006005c00401080074412000c080e8850040318410344d00101244400c004402c014241043c810364098040c1050b03401d4640d4a0b100c68841102c0a0714032800107401c071100050040c0c201c80d088030800d1252000b0040d281128001c41c0ea10040c0781000380a00080a842c1031410b002030000401442d0f01400070354449081d03140c42d40c0034150880302c2c05c01900407040b0340b0320f103400e203c520384801001a6031401e5003a240da0710142da80c0140008075004000403280100a050341907801540030b001241c0d0340119518102e02200000510550050216414000e50902580c0c4110603201500c1d00841d076000c0c042280c1405141610a1442a0b6000303203010003040442460300000d8008c6038019002441449407400030810502c109024543d400302800071a01d1520800d1040f00358417039281140c8036080200d0b50f008914003030803640f03c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 111248579 1250 111247329 111247369
    0x90e1f0314061f0501020c1e04020408030d060509060a0902090f06030429091b030a0606120b100e190f020c0703020112020a09120303270303051b030a1a 67
    0x144420410308600312203c400c150b000c0b40000d5070030007000035101c015400301f03d8440e0520303007035001d01d0441c0a010303041038520083c021990390380c1d26100241c60b03800c040b4010445501e4910b0000d490304140c03007054070a140080140007802e0a15800c80025000600c010760000b0b8201e44010007512540c0045015074064440303441d4490501c0766400d400781c82c01e008042d18814440078800c0b00703000000d404100e85013682d001c42841c180980031902e88034507800702900c040d09028001402c0c1ca00c4002c80c0ea00706029040580441d0303030b1000509020b02140c41698001d0101d9400a1a05042d0b10300100d11880d8144003c80c0b0300d01e007641c0070001e0783c220318064440b94225010400466811101400404641100550900007000c0000e4600500c1e445078007400100d0b840c6032010184a5840612004a040460100341600218401590917101c000700c0c00300745080040340803c560f40000a9000a4125240d03245690300034091010b0030304902c0007130ba590868103100b500e5980710380c90003400c1440284 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 111249829 1250 111248579 111248581
    0x5040c030510060305030f0a11030304030302040e01080304031101030b01020307020405010311180408030601030e100603120e06190536030d05040e01060c0c090e06070906090e1f031406 81
    0x40281c103000b03046800040292900800304005180071040d1450f82c0c208000e40745c0c683c03071540e20036100400f50740748410441c0000010002055015400343c829141c0c5180307180481e03038032040f0640c3d0780d108038040074180303a04601003c1c40542c402d400074031180c001803050320308015855011509039503080e0001c4415141c046085000303401d045804d4242140001d64141c01400c2c0750701c07648034604c00508001d040503242c80540081c1c80c0308000ca10701c03201e44210308102082d0b403410910700d007980c1403a41000088441d400700200385048000d0300c0b44128000d0101003424000401501c880c1d0000340904c0302d003090750b200d80c800300340301070341480c1240d000394101149050700004041c1489040140c400078040d0500c428000d4048800c11513040d03074a11706058041600d141043c802922482d4020381c01107040240400381650301140a500454150711039183d03140c1c581c0340548502e9030b2400344040140e101400101a4032803038100306c0c00031a000381a0103810b510380d02c2d11550b2031112010a003059124030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 111251079 1250 111249829 111249833
    0x7020a02090601020d0503130204090209090705090105060307052b0c0302070510052403010f0905011b021222030506090a030e18041401060f060e031e1207051005040c03 74
    0x660050b0700c480d00344003403c07074010610805081c46c00041e000440c00030805490303104540b1650703c4140e440c0d40042c001507151808104c0e450342c4070b040340112070088041c0000024541040b105480c041d843c0342e03c03268104601003011075500b41081c1c0070042c021038000d06858442c00c0c030b8800c40303002080e16500541d0b209003508019203864155602c407801e4600d00010082d04003090410040c081e0805021080d071409403d0000b070240c456030301c80c0c9250500d001c0914003003040540c02504140c14418810341e442d045108140d880b82c0d00c1103003a01c110107003080391010160400e03401c0c011b800d505c1851141400d44a407101d40c0740000440f130390201e581c01540c11405168120b00300510764101142d0302d202c040c2c3c1d10f001c9004691400b4000609240741144070340c00ea48420340011000e002c50040711000d090341c1c3c0c5401000580a0000b10b4041c2c0a104d80b2000741905e882141c0c8480e1720800c0040642d0040700e21498410b601c40d104c190fa190040000d1051003110b0307401002d01a50003401440440740c158 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 111252329 1250 111251079 111251089
    0x1e1a0726040e0105030a05071a04030818031c0504091e0203070201050108060a0e0304060507080d090b01150203070f1101120606050901030c030c09050402090604180515030a150f0f0507020a02 84
    0x60700b104c3c0c4030358040d0314414005131000500200342c032aa01840d509600e0b140c55500c031940641c0d04010000000420b40070f4007038080c01d05940000b80704504039207285905000c81500144040c2d164800241c0401051204141542158036204084842902c0e400340c0350110383d04a81007a1030706001130b51101d0040003d00803c200443c1c1041c8040d41c01c000880908010699902c40c91180c04140400400c02e4414040000c0c10389074100407050003070140403018a880035003003109009c0c042000028000d004019840001a94001e51b8801c40c003084450007a20b4a030b48001e0076a50680c1006041034200038165018004d0341c00411a946403141c4481c045030015065803101c5410508140c40c0c8200741c2041a071080712042114020384005984501a802081070740c403da411101d807964218207410486c48035940300a1083c4807501030050800070344010103880303c250100c0645400a94030700300050102517842401614441c850003d503c1504c461968142c40c0d04861301d00161700110103a00030b43c108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 111253579 1250 111252329 111252331
    0xf05010605281a0403150b13090c03060e0102090d060614011718011b120f1506050a0207051c060609061211032103011e1a0726040e 58
    0x501c9004200d0b5115403605101e00481501c2441d00c0030240080c0c4100804443c800c07280510740003840394074055030182200020f020031092840c01404c0c03040071261039410b540301d00d844140c1e000000c1a03405295031134082c06032100d52014100d5544c208158089980e480ca890302c0340d103219000c0465024940707041d42501c144901242810700404d841250407211002154039800351158141807192117906c00c006004203200e002601c0c621070414004000d445e002011182110f440d0381003880070a1240b05004196081d55103018901910307080c0178812940140040d004110b824812504415a20b4002030308507001c005c1d4850441c1c800c001c80700306000080c00381d50098062a80d003484080c2c50190b0641200c0e0400501900d01d20b452800c00d10166000d000030702c0da84030f0f441041460911282e0035405039905c28447c4c0440340b41813a80d0350b0b01d04058002e008084070400f0b0040e42c02d280d00340350740c481241d0000d4002c42d0911450044043d150f00b45180051440c0040d105140d01e9905203802004002d01c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 111254829 1250 111253579 111253609
    0x606130e10120201052703010e0705031002040e16110303040812060109060905060c010608250602070e1513110c010f1a01050a1707020d1e0903080f070f05010605 71
    0x2d60071004401503600141125101c9010701032552084040010017824803038845100caa01d5400d0080f82000910300007040300946030b0031410b0b90080c0e105506500200c1c440c511442c8007503920000040c8010341003d032005109055420080880000c1d00c07469400c541c0100c6003140c1041c804902049442d09801040b03900200030309020700c3c00ca0800102404549149c03050318411240000c2c00b110700c0d06c00790006801019601c0072151000d02c029905825030004040c030308039400c108500003e00903c0060780381c0450360500c802c1c2c60310740c07070302119285424500ca0505401680b8541c10b0801d042700b6204140700201954075141e1113222425419080d1403000b800c01c044c907070404810b0a4950950318207141d40c06000d00f013081d90741141d000152049041128030110403490306040200c10354000c01e42a0b07800d1080c1d071340c102980380d4400d003c030096a441c80340300700041c079a03907010300c00030b0b031300c08000d148100ba80d020b61820584903036180e0030640d200740f6003114943d444003820009810040d0038411000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 111256079 1250 111254829 111254849
    0xf12071106160b0c0708070f050c10080703020a03020c060a060302090604090b0a0906061a0304050d05041503090c050a140a06020c010813020a032117061302030606130e10 75
    0x49580082c0c4011620400280c9891003000c04a960301c1210800c580b8000d0b4072081041e01d400e030070308140c00080390208055a030350043d03410100c400d1801030510204841c06442b501c0490311104d01c200d0080d000b40d00d5200c2410b03804c0200c2c400000c41004842d10446200d080400c801d82184184488070034085c0900e0f0260303040c0a40d1400240380c6402a50b030011510310b00040c3c401c070710706103d0301a2101da801441e03032110513a0780c0f02040d80c86c0d8008501c56402101200e42c0603a5000b0215200d106030710504007050b0a402d600c01055100b90880c4240340c2c0160942804107031110b0004180a10907403050300160070101c171102ca2820b040400314003c1010340082e0031500a00c00000c1c0480038020074212402d1140d80083c8115520300c0403071400b858102d404113040307484007400300c1c4075105181080c00120703215814444c83d29200031442032088402800701c2d40041300c0500c101307000e50005090a644284240700c000709058100303004e00300a040760500c181c001d00340840300782d04a2003682c102100d02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 111257329 1250 111256079 111256087
    0xb040e03040803180d0803160807021911010c05060109060501030e0105010f030201120e03070b0603011526101b090b03151c0203010c0e030c0a0305070b03090f12071106 74
    0x40c0001c02560007421100004110300801300300010000c0c4c2c01048000c14a620201c140210481c2d001c00f03002180e185601c0300e801d6600c0f4090b050ba5541ca00d03000d45201e042c030052101d400500c07012000ca007411410304050494041b544d80300d50a140c8260000e402140d940c8500304010b690502607410b81c0600303c002002654145001040e00032120300001c2e0501c00d244148075a100c0341d50f40001010f06a00341626141d010310f16000c4041402519054803e40c00d12003c4004403a90391000c00c02c83e122031460404440301c0070009080e604c24410450001d01a5805010380070415000b100c4c102c00088455650894a0180c080c182c01c10a03001403000071001c0c400c001207210b085100c8002044201e5a40002c008000f210562100d03008030000c3d0103500f05101300c00e0b001e402c031406810040c0c040341983c80c0850b4600c04d20401204900c005001a40845c008118940f02440215041b200240135203400d26152105e051500f9041c801d40c02c02d8480029800062082c2a51000c414440840305a460 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 111258579 1250 111257329 111257339
    0xe010f03060b0412030c080301080303060a050315011511190b090712201801030c08010b03030306100c021503090114040305120606041d0a0507080c0403110f0604090b040e0304 77
    0x2d5000724015003d80d1810071602005041c0206541c041840c0d00c20802640c0c0d60b107590344542c0307135001510118010003000201140c83d24001c5040362075407008200c0c8071016840d15400700804070700304400009000305400c0002010000f40019600d291183c40c0c0700c071181490345400200c568004091105513003004105100341d80010080c400180d03040b03030010840d407a990000e00c59549a0422455203e01c07503142220448400c00800d0381200d0094641100540d81d50703140d28280c0c2e042814403541504100005520361920451241040b90a480d2107030800b0840d5000c1401d5540764081102c0141011003040039a03c424020b00e4010b415100313007060181400c0c0c0d000f40c1580950000e0341400291200060002d4030b4480944004060300420914000c2e0084078040c25401d06440c1081d000341000c0001d1111070190098500030f000420140f03160501c1d545807186403078041d9100542c811407182c006c1c0b540e541e50401400180144030b800064909a04c01040200e030a0039505031040c1e0000d00c41080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 111259829 1250 111258579 111258599
    0x406020604121206060f02120a0c030c080906030708090609010b061219062d0317030c09040f0b030c090c0f0a02010b04060f0e0a0b0d020d0203100501060e010f0306 72
    0x5000341c0c0c80360310060040c4803440306a807900320312480788943c245050f5000800650000701e10361800c1c810380940b0b8042c1c1e40040a0300031840b4a03c490000f1503030124200001a05c1140d12003a003a0048045c070b41044e00c4000015410350041d1703031071400904a0750030b110b034110040c0209604501c181c4001c020342140392021aa0360b0255035a11f103690340000000607100b00b440342c1d55015041d0404002c02c5110384034005a546110a150980725440e8201500d03200d0300003201028082e603410a800148529080c800344965074401040028402014040c824041c1c40e240200c04042d00400c03004104103010000745440c08402c6c032622441a0714006c1407200728001c1608503408203c0000c60f881e41c5549190307007a070145c92400e40d1560000e10382040016415030707865054040d66111102c15100341c542403803841c281e40150042d1f03603000320140000401132400030605040d40384082d007a16401c801d40d00d004e80071110264050b0004c02c000e446002c60039079101941c01c807050b5050a0420a02d4281101b90f8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 111261079 1250 111259829 111259831
    0xb03010807030f021206010f06030c020c0d06020a09150306051003090b040201050a180b0d05090f0c09040c090e060604050601210c0e06030c0406030f0209060304030311090a0b0c1204060206 83
    0xf03848504030841807000e5480d04400c00b050301d95041d08a80055a40b1820483d06079890300c2207000003844c08918800403031002c1909000811300504d92040055617031596070096000360449414001801ea0020700308525221800c0d0f2413101d500c000071011f181c0028002855665a0b807a81010b15103462400094800314078950000d80a29000d92201002203094441c0110102e4100e100340000a0008150320301b00c0040c50306440410092140b612190035180d502c0205081148027500510740850807410301030000d0740d0160113030349000d11482e6101c04043c211100e0a9903290140c2015042116a042c01d01034641c20070428030b080000900c4114003410340d607809151601500b41c441540d07440e1680b06000209814a00403e003e54a0400c802014841c0d07210388502d50202c0d08000c5070b107041c08510b10171303500540409090305281d07070380e150380031802001c0c0c0c480b40c0300806e44140300e400156100c40b140e420160103800a81a9180704441c101ca20344811205e00300801e40080005003c01980402c481d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 111262329 1250 111261079 111261083
    0x4021309020936150319050c01030504020a0b0310090203010611070602060105060d020f0409020a050301030506071b151104120605010e040206041a0702060a091e140f0a0305010207050303100b0301080703 89
    0x42d01942d181d11a21018032049001c44e95810310446614028084c10b0740042d02450744210111100680010015016904125030195000b0704806080100200304e1000b56885092401c4150740d4540f900d24020480e042a00072a00003100811800c070031f01c80800c00c400240c000c034001031205e036160000180941c032507244090180c81e000725800e150410700200307413005030a40c11015525607210f000c0007007458000744010b56003885440d0114480c40c2c05071a0100066502031844600105c49444500302d0992036019042d2041d510f504890301090000007a10180050142121410b0f00310305040301900ca040c0c100360700107800e1400348001a9114011103045911503802d00d445902c9030886420a03001b0141c02a400c041c00245000445034040852015601030421440c911318500f07440c0c20094540c1c1c006c0f40700c0d440944c0305402c4946000500e4181c200f5000b000c02c600d5549960760182640c000201c1209e45038004014408250030a8000f400904000141c141c1998901124695a14040d01c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 111263579 1250 111262329 111262429
    0x711060f070e01030b0310020c0d0f021b030f100204080d09050a05090408130e0403080c0a09091e0e0114070f051806040305030703122711040213090209 67
    0x2c50920b0b4001d410414041000505a91000b0f070740b00f0b4004080d51055140349514042c0303c4906d10618007032a107010003007102d540108840c1e0842880300d03403890b030407142d6a0352510500006501d513203810000c2c1084c1c146050805a21180b07001d04082c038011001c458030080c0a490315041c0041d45404030396500b240c03c12030304242c203504c0754200081b05100d00301d010320305080c04100c04104030002d4086075000742c0c800e680e0640d45a4450700c00840500405a0f1400045e40d82181001005503036003000324407810201c4601100c0581450300d0040318029160509136945510101f004181c03410321040d40011a410961031000000100a03d640304a42c0080d0291501c0d410340300040d11804140c9001c0c50f404030450366141c0c00e03414083c1c00c00c54030361004c110842c2000b01c941c0c075040c0001020b82070604074009030a100c1403141ea90300e241c40e1000605c02d402a509024841840c91550280300080003070060044c0d03218009014009113055a01d100050000c01614190b4a12807101c110b990748221812 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 111264829 1250 111263579 111263597
    0xa151a1204061803020102070b0f2214010e0a050c01080f0103150b0a0303021f0e15150406060f141c020c07080607090e0906011a0f13030b0711060f07 66
    0x30b01000207150038065418050000710000040640540c01040e07480d00035824030300d086d518260a5030180004403018205040100d195001c200c4c5090000c020580c400ca800135040003803100a0ba085946d12592404603522850204040c0071041c090069607000c28030300b6000c01d10300000c849200d01c9041c880240034024410094502d0030a40c0c1c01040d010400405080e082c40c0d4a080081d40e40e40340d04c80952003d9000000c0c44032226003441100740c4c002c0400050070003020845a40102071200074a03466044913003409070700c0c03240d8071481a84080c190700d8881629010314554018180c0c042203141500300c41080050103064103d40c14648900c1581079805a40e4010210000e4100303421079005041a220701c01c240008550000810300585116a4041c00280d84000c0350a0f034400007840f039078058000b0b100c160355144803154014120210101c0e580c500d001600040350303429004aa005907140742e0500d0a000b92994004548114166060020011400c0c0901c55000030b80002c0c01100500000c45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 111266079 1250 111264829 111264833
    0x609010503090a05100f0e010507020c0d030e120303160314130f05060103030509040e0729070c0f0501030b09240409060203130c0b0c030d18050102030a151a1204 71
    0x3c0c4040803036002d4291820282440d018501610b005401241c2c002e040c80818207060005105186c4911403a600070b00c040ca074101700740040b40f00c82000135400c002002c035140307403141c884c250b95610a00c81d1000079582c032b00d042841c9803500328840c3e4081d0101800c01c00340c014111108000300b0b40141c40c0e40c00188941101d4503001c252045917541c01006409201c00010a043c3c0000180c10302c2e210942e81070103074081e00c0c400c96468140501810107003a0305410844419404a2040e00b094580e199046d4070304541da4845c10082611580905c00c07580b1000c60510055915000c0c507414154141c1c1c0079456410000d0148003ca00b0322141002400c001107038480071036846800882d0350790380281c0c0c01c665034101400742d4140c18245040a44691080c40030003e80c42c0c0e94002200d401c0c440ca080614100501d99100b2000b4140e03980100d0100102481e061001c24401c1c07000354054065400300141c0c04030000c070b968035480d200da400403d40d480032056401031201e03003d046401101e5803000c900f20340d0340d4034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 111267329 1250 111266079 111266083
    0x1d070c020405040605010f0b04032a050d080a030c050708030604050403261503030403030807050304051e011401081b01110a0507030c030b090d0e120f1920060901050309 74
    0x64540654090705000c240b00901009034001c034140d0b220b0700e10704000c00e034980f0f030000c2c828821484002c0c40b0850715010f0b0614080c0c00d0000d00c90002551100404940e81d8a0009022150300c1c2d0080c4c4a0f0390700059023203081b0350180304003010807000d82800c5042521a4451100c24000100080d000c0c50300c40c00090300b0144200c4200304061000c0aa08032402d500845840860100300c416101c442c4220821403000d190000070f80e01202e0707041e03a4203501c3d5916600200c1da0764002520413541c3d4800c3d595469200488500580626000403000150340d901d00400e1660152042e403140c40305400841031010300d59115860b9078480b00b000e003405090380148800161411a81002c05031040c0202c20000c0200502200711808803400780c1d040300d5180d1a4121000d8498040c10304910200e0f1410001403a50b080c40030105c410389020300103031410391307502404071030900100c000b01c07940c1c4038200180501004103115010014184a2001448104404011400504c101e6288505020001c0001240c035001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 111268579 1250 111267329 111267347
    0x8041805061f090b030903130e04020a0302190b18090a0e0706030c0c05060c040e090105091c0c0b0f0a0621170c15040201030c020105060d12090f0f0f0f1d07 69
    0xd034000d9541c6d150800c101500ca80080198a90b101100e03180020760303807a904001400780760020400c1e02400d166500f008490030542e520702810655000b000214008180085d010f00041001d402e40d00010540801c0f0800000038103884607145001c84100c1410000034604080d81c0c40c0c1c0c1000942c81c0c0041005070b80c11015a08000d203d481884200f048610521010344200e880055020b03005072201d01e203450980300b0440d0285000d601c10711541c0381503180c090b9214106801c0303050400200f078040d2161010940126040c0e030000c0d07003800034048482c8103803007124010000b4040d01000c28941c0c010048040c0030f0b8001c0074000031310813641da486070300404e812220384540c2c960884440d0300756080c0700e4422500440c2c0c00e9020919043c0040d02081c0180a407906c00e01e4020b08201c419032980d921400382c02802c880000400440c00000b140c440c0d0000e0600024002c0c640115030321901d002128001103015801c56402482c0b120030030000d101000103000c0300d14602ca00a16000d80c3d07030480440f041c00d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 111269829 1250 111268579 111268589
    0xa02011808120609010815180604030809160602120d0e06040609030806040902091303031808070c0803092101111c06150e060c071208041805061f09 65
    0x3059921440800603900300504889240000350482e075510b40d420071644030340910841e08940c001c0810404e403124902003c543c00401c00840d0002d110092400f5440d1900c2140c089011603030180070b001d007010040000c40503050515281000c0710f400d11500070b448140e000c9004201b40303400b00d41060107254542042946d01044002c540c0c0514250804a002c0c200084040d07010816000101e0031905080c0289180e19801030403500c0162207074030000012030b005c040d00350201a9905100c801d0b0800ea00c0c91041e209014600941d2180898282560f1142d150750088200b03070301c00c00180740d05d616007000d408562101000c642d4031012801042c0d9014103042108049040780004821100948091410045151015003081031070f84a460290400181c10f9000010560134092802c00f854810028010038234107400760b9090680e18403404c2e803503a0400100300c0e00103901003014081500741140c6004204554030040c020b80c1854004a1002d83d01d80c00e01d07135850b03e1001c40001c40b2034040c48424000302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 111271079 1250 111269829 111269861
    0xc061801111e151e04120e10030903020f0703020d02220c26070e04090213060312081e0a02030a0b0d03201203010504050601020f010c050a20120a0201 66
    0x1950082c07950301e034881c40c2415401e071440a00404c2e0b21001c8104081280d0b800c00310300e20440d0720355482d600300201c62110300e0002c01075a41c461100540302d101031360880d409035032408561201a03160190500b400790404461941c4045000c00259030742100c0d581034150140e03401043c480c140340d005006060342d61840c1242c181804076501720385030320040500740c1500b9895941100e03a0f40b004210748141040c3c60800c00140088810b20040c6010740c0601c4401d0301c020215034850701c5501400d01130711419803081d51200240810340c5000703034205c4541d581c05146404111741d20404100b0900700003030301030084200594044000381e03850038954040f041c04600103182c2c180d100141d00d801022100c00042c1ea007041c01c04001018024600001c8003200110707581845400c6a0800702800010140280403a046120700c00d200c0350b03005828410307400d2110f0300761b880d039175680080c61020f01800500410364041d01d004407100d0f104a1400f04070703c62001030f40b551140d562a007200f03040f4050486d02403810a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 111272329 1250 111271079 111271123
    0x20c19050331170709021615060306050c0f03070f050d1b14040b04050409020a0506030c131403030a03151d0f070c02030a03030915020f03090c06180111 67
    0x300d00d4200d03400d00c900040500c10301080c1e0b11424240e069142045428103140d000c02c0c0d0030300580c0c61741e4002e4000d0329050b001080d0003c105231140305c140c01e240141c0c650340b59503d9000b801408094040c442c0e020685158081c075040d8845a400c20510004190300c0070070140581034000144141c1c121110680c070b940701802106050040102c0a1410500003000708441114011041505400b501d007151001d481242c20203142400340005449900d40480c2d1001d1799440c04141955844050340c043c0c3c1405900f903490754010325450400d1541a000b02400e035403801c0303601c00c00da1b4000045603200209441d0200d110031807055400000c420780d800001940c540ca000034069100d0300c1c180c643c8902420300b4803072000c2d1284036082c2c07201118400c0203901a000b00400c80040382c020740186035098403d04108076004a05114102240c00100c490f0f08400000000e1189500e403c10014007950800c842d110f203001e400c5001009011682841281030101c0c0018640d4200030603c000031b807902c040c010008034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 111273579 1250 111272329 111272377
    0x15060a090e1c020d1709010e030318100b060307030e10020c16120302030405010815030a080a0f080601081609030204020a0206090d090315050a0f0c180603020c190503 73
    0x8a03a60340c58400d0300314a100210240b66803001821802002841d110540030300c02c12402e6aa00640091000400390349425042d1902c14041006501c240940c07450f004c0f0b8007001221403030030880b15000c444032035800d00510040e40c2d5900710440303801000908001541803ca0a03015007860884804100c8075440883d82141980d030200c1d00341c015103012074170a030b141a15150810100320620390060b0059006120a100343e50081c503215030880c240714050160740c041000041d26160f1100c0007200c00540c0482c0070070b046c58004100010308041801c10b113506192400000b0711510008004000101d40e03000d100807800c1c00303419840d01031900070b001956100c901d40d20203507840c501540c2001e014814045070100b014800c1280e20103072a40501100804427107070760340c0d00c043c6c0409412040303003135512194600304d108a440740718800c101c6501d82c040420968031468005846c158825014180100301039500c8031401f02e0655040c049404004080300c2c00e0f030405519502501800701c2d000505450300c004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 111274829 1250 111273579 111273583
    0x31d01030f09110f04050c0a320405010305010b16030e01030207050303010b0702090f010b07030315120302010516051606050903040f0b03012313110f1c06150215060a090e 75
    0x2103c04080d02d6000d100040101440201c42d07044480d00c011500c02e03c03920030883e11400c8100501c01c1310b02600c0404480800078507905656580002c8020301c000581003005581502406004110b80303880d050030400040c0b1442205210b268004041043e80104800c560303001e0390542d0303441900b00d1701300d98807503071103054010643d031010106038414415180004c0b0880c82e4200c03454140c54444013181d0030604507540a8004d00141b0340d440c0034650740000c01150a4000880002c0090300070790001c01d00e0f044c005d8481e040c4200680c104400c006080005002c8582c240103045826079204800143c07590350302d00410309502554020075946088200006074441c0342102540c160f4402c14005c100300406940020090806012800d401c00312010b08501d102006a1005040d80c1424000624040803102c1000d050703803106101c1003440e40c004083c02100403091096601034400701600c4200b40882c0000603680304445804d05004080d504002485500c4d400b01032001060b07201c505004003030350241c10030307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 111276079 1250 111274829 111274853
    0x7230a120b060705030706090c1701050601081602030a0507080408030c0d0206090105070c0605100b0309010204030309080f0325020a0b0d0b011701060e0409050a03110d0804031d01030f09 82
    0x10050801e50201d00034980641202c031080e5011000714078200051380d9000142a071004181c881c20b2280ca000641d0b034145014800000076420000941841c0c6540050030700d00018210060482c12603412007800b9400004480c480c044604019803074025606d010305442c8510741005110b4000031603046694540040c201b1a01e0707006400765100c1e555031350707007640c01ca48048030f403040010008064000030403e141e1005402c114814001ca80da95101c02c00056250700a0310480c01d00c2c0e40c005010814103a002c00348001a0400101a000007a800d48041d0381d24000ca11b0288162048031901d84c203001b103440d0b0f128180d02c3d8040c0125114555076500c503c0c141e045002010344190820b043e03a1402c0d0712445031032030380a002541000080c1d003048411200c600e05442516000781c9d4591080010030820030078458076034402d556405500c000b00c545903041800c1c42c0620360500400400384000030340c1241c440c80d01e050046402c0e6030300007024801240034201010605d803400f4502071400040c00345859a178 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 111277329 1250 111276079 111276107
    0xb0f180115020c09160315170d0801050625150501030c0b0c0a0813050415050315040507120309091b1103090d082802070503100603030807230a 63
    0x20403409a0000d0042e62950704000000b6030203900c110020316071028500805640c2003951600007090001c0b6420804440c00301c0d0407521603e4403401040200700802c0142c00252034507845c01001951412000c1303080c6014103400442c01c0070b4901a9580c05440c000c1000036015000340001800b440d644a02c070b0024502804150364a5840c0355010a005c4d01c194100d4010140400083c501d1803013030345581c114ad800101c400440750a280303500040341e07039403406031000402840c0202c2c1101c070b1504080610380921000c00c02c50081c148000c01000c00c0c03020a21104840b4040100301075040e207403804443d001c841b5006084a40e03e07120b85400307141c20385990803090700c015480e21505e00328603940c140c0d03036030040510b1154801204203040f400100c0076030180a5a0b6003000c60354410007101480001740174a038080880c0180e21440041101d460100b040500c850307001c000030000070f402d40c0ca009000b1030006103900c003400180158007040a0080c1c0d0802c15111243c500241c07111490400145040700307140e40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 111278579 1250 111277329 111277349
    0x16050a12032a05030a0e010b03250509010501140703020111030a020d1a150f070c06050705060a05040b0a09020d080406020a03110607080f04050705100801051309020307090b0f1801 79
    0xd02d004002e030100b168111a5001d440e0b01c0e0071951a120700070040c1c18154040c0809548403030090010f80c80c10000c51302c3d4041d40030140315020040c204407030030806182d0303c030600c101c03841001004541d07040162a0540b000c400c800d240d8840580c10103a0142845081407169035000104200382c4000325070203003411000c1d4480c24480d000c1032000140c2420781c0003500c0341d800300c0070001d940018290300740101400d80c1c110404504100c1c6a8841c2250b48041e98000c1000c80c0b00051000d080150070310090398429081c620410103800e081d141c400740755000400044146a59002110039940c400d00241c80d610382c400c4105580d070351103903030094540190090403400b242141941c00d0407800c0101e92075210701195038500306240e40d82d1007a807040c00e8016105441d42d000750840440c4a888242d00c500300da55040c1c842c0e0382e00354503020a014440c0d8526401e203004174a81030110700140c0e40450500104c840c4207001090100c0d8120000d400b0301500014594440c42e0300c45140b100301c3c0b208000604031001004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 111279829 1250 111278579 111278621
    0xa0e09070e041805030901030c020f2401080a0816030e09041209090b10030b0105120f19140619090906050609060105031605070f06020325020c0616050a1203 69
    0x80103d4000b018080080190300140071466155100c3da0140000c03100783d104442c00c0e84e9060707540da402c05c2440d14ac144942148018145001c07038208141c640105203a100030612000180c0f50244640201d00d0112400c81210f22041c080c18400e00c0342c8514910003c1580320242000c2c0380405050002480700004241261400a2480c03800d11030701100c42c401422404a141d20880c08400404007054403d06000d4180400f1085c01441c912844c4103d511080c0140c1900308044220341a07100742c10210f14050400050a0042d0094001c8580000b4141e6010000320549850380c24171140076000350300d02d940f0f00040c01d0705110190308982d0007000261152040768550000444891100304c961058401540c501c42d0081440b8000403c40d140c0101e240c41d040c540303d5034030ba4003641d2090b60014488140c62000a1220a01e16034920b500c409500040000304000700204040c6d001d014800b040001d110b280f4101070190622003035030f000b50700006088540c0d00e0104064010104960500460700c20f0003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 111281079 1250 111279829 111279851
    0x120611091f1b080f07080f07030206010609051f0e01020f010207050105010e0f010f030b090a0c031b06030515040e0109020301061d0a02070f1101020c041a0909210a0e09070e04 77
    0x5490a0b40b0360f0003810240c5084400c40418049900031501112809010060540e00348102c60150003907910a5002e4007081d451710030300a100d04100d401c803034890820700c0303051a42d0079280c0300c01234642e0790b0904112105c4025007005034145400b42641800380d50000400030704001c0103600c118160390f0303d42da07011500d455824104140e10b2090281d00c2c500d1100b80424004030309a212003d03400804c0f441111b00200c183d83d84d4003403152041c1c0c800c5824030944c00520307182c40307121070b007400181c500f0b45020407076841c0080074200b00c0c6809151050007640c4d14040e0410002c82074114044940c0c01600a1004a0795580c01e04054902e00398141c0428100d540407030700d4a82140210b03512f440d004200c090381101503485d0251040c1300c0032080c07415840f4984401c480ca03159030142d0600c1c0c00e50340c40c0560040051105001d482c8800900c0e8031015001050044680314010b442c2d4a001c000c2d0001458440401403030135030b0b201045800165000612004015a40740d10084000d4010000c0c0d030300340b110303034144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 111282329 1250 111281079 111281117
    0x70602070321020a0803130c030c08190804050f0105040305070f0611120a0e060d0603030f0f1b0308040305130801050613090f02010513120b0601030b01020601120611091f 75
    0x2c420350740041c0c00609148000c2141d0001441d0003200c82e541042c0345040315551f204000031540d108954801e050032040003242d03018000c10061803040f0700156024001c55403580024801d5001e141d114a100030700500b11a44540103031000356900c84d0880784025194000c450040c8001d1280c040051a007451801208002051898001c1c030146078060a0071140107090303803114803000c0030a402100a01ca04961140300b40981d0700154000c0d2506a160040484020011105560303510140f02808200d1505d10580010343c55940350145410141d03a107030361400311401d00c141d840800c1750b001540e81c0443c40c00d4041d4002070180c40304660004200d42c00c001d615040d900040c40c09490149071102110165010f04014101802612207640e2007035124031000002c0610b0075000c0d43c41b035200360104031039560035202d1a08501001d000800c141d47c50000c2e84c40d480f66a6110080c50903484032a0504e1007652141940d10740070000b000724240032059268516448c2108683d90002016255030020076021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 111283579 1250 111282329 111282383
    0x30906160203040b090d1e0501060f0311130207020a03050c030c1f08060a050d060b041103060616050a020411120736050402072001140d1a030706020703 67
    0x109402850803e407800e01c05400c5a0001504c00d81c0242175004a05c00140182d0f12240c400c2c24040014202c2e00c42034100070703003162082d40040c3c1c0b06460140051010440d42d00007847d030114202d68034501400844000c0c4040d000781074000790092303a004004410041c0200d600c49003034a0540c1107039a0003488a04002e41103000035410380405129001c484003c0f0710a8181030341c00301010380844480c5540340701040d080071180d1000e0714060741d1049086450324042c01810380c0c050000c00f405082d800d10f9400a60180b2440041d41d883c4412907144070f082203414444201e82c250028402c1004560020000902e940603001400325900f0600004901030301900c40364004104050341072543d401c000619500e80741c5415241003c086411304000f070b07940c1e01d030700090048500c0342d658103102100686400b4042039100303000d18184600c0301c82c90080100104182e42d801c002c0c40c0c3c40485c1c9142e980d02c0096020101c03201058050040c030303101245580d00011307001c003101c0c40703140b481c3c800d41e1030444030b07552001c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 111284829 1250 111283579 111283621
    0x915090b0117060f0a0312121b050a05070c03120504031509030207150201020c0f0706020706080415110d0603060b030c010c0206070303050403051b07090e010b01080c0a020f01050903030906 83
    0x201c0c0b000305800c0d04100f2810100f403000600b0358500280c80b80c841100c06000c05039800001481401041d110903958044c021210010081c20305e48842201c1024249004000401e01000400301d5001c062100c3c3c032a044005640114a4039071009050800410710343c803d00003a15031f0004030190f22514045e030710512552070380682c085d021003810010b00f900e185d00d424084004564080c03100e928004020700c180300d0520302d01001405070310300d4800c0217810040c1d01d030f11000a0080312410440894401141d45402c00041c08000448200c0030b040940c00d17000e2034102818451419001004000b0298804140c50504904a0300800c185000444c2c024080440c000e41001080c042003000a00a4000d1074010380701381405803e004151022200d00d90103044801c2040d030007500100880900d0b031082020154084009020b01440400040d08020f00500588400ca9001942500c514403e1041100a0801c14002d11081c2021071800390340384c000765000c032424040e03240410510400781106c1c4070700380 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 111286079 1250 111284829 111284867
    0x605030f0414010e061302010905010215070309020103020f030a06060909090804050907050408060c032401020d0f051303060e0f0c031b010e06040608040c0b03070e060705070915090b01 81
    0x903856542d1a805901106152881c40d903d4045210400c0014040d081c402c02c0080c0006403445014000142800b039207502c07160654010307255587c40b00d00081c070029030002d0103003400f107403072007042c40100c00074400c00740c010403108400f01c240002e05185421810403680156618040c25451b44d240c001201d400c00001056614200001c0000d8105021a55400f0246d400d00500786991840c40c0350400108440c0c20080b82000000c001408011200340b41070301000107a140c130f13070fa0398260002c1d503940f81201e6401c6c18401821420380b09148980111030024910954802000d83e0300d2604c603002d842d00600100c001e000f240c3c070f1180e18407400502036040e004010020096140144000c9075000c0c00003201074100b21004140400315150fa42c01800207080b030395603810492030107041100105510790080072290008000b8000c00e039911035500005200c045440d9035440b002c61601a00d450015400440d443d0f081851030b01e050041d50b4031000c03c072561002e003803000e000600d0044590425160305860b00c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 111287329 1250 111286079 111286081
    0x8070302040f140a03060204150807090e0c0304240207170703090b0d020d050708041b031104020c0f1c120c050313081b010c030b09090601030308091e060708010605030f 74
    0x59285003080c00e800c003c09460400340e261170b5110700d0140c0c3d0042d00038031103809040845032206030f805071086500c5640303840c2c401001810180d14510b141c00141081c0c0d5480c030080041b4040c0a01c00202440c4408071220f0282c0381403288014101035080042c1c2030703412000d024500503032800040c041b266200e80c103940b4054045e0a0401c0b520643d080324240140f00d507400d0140e8981180316104c0c0e04d01814450f154900780b40f605150004840070020b00030290640c019804100140c01c5507005001400215000f5850300170409419103400d000907082c020611907a00c008414080b40f032183c0b40340d42095551015541840c0300d0100903240d06c11012000120208000b0f0100e1421048403180103219100e110301c1c00e40c0400100b0000e0395443d20000060f591a01c2c0521841d40503c03038a00341c10000d07a6003034458600b0400e05500c400b0140f0002e0309116144001a84071801405083c80d845a4031404508004004860903602c810888880000c1501c0707600218402d4043c0042d2031080503049203898007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 111288579 1250 111287329 111287339
    0xb1903080d0203070207030507080304050f2409010e030a08030f090712061107080307180602211303050303040804061701080a1103190b04060b0405040c09111209010b0108070302040f 80
    0xe43c40280000211300540350040000740040c011440100402001561140d00f880c0810146078800c08529100740d11325140351090440d103040740c00303c1d11080350425448815050068400e10718280300c9070f50601500040301d0400020202030b5000307100008140c6602c1c2d0350944116911a05801541603120402d80c0c42c900040f000e8105858a4510704004d900b8111580d41c1c964481c0c006581110224141c0b0600700d010011079858000142141d100510305000c040e07000300074184804d582d18001c03460004034542c040c9000304000700107503440000c40740e0340e14250424201c039400c00d01444000520340c040d140b1000625151940c1658a8600a01900c000c60350311694030780103071502c60740c042c004c482c8820601034400c000c0020320ba01481d4a0461480c00d1b00d401d8003201d06000c61144200d01e00340c14840440c40c00a80c40c2d05a075a02640003601e442141c1402009015000c2040c50f0181c01c1d400b00810b018040d000209000e6081e2545025610f80706002d030709a002d1070180c910301c014124030402c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 111289829 1250 111288579 111288581
    0x50904120309060f1a0103020f09130b210c0102163c030312020f03061002030405060a030911030708030d2c070501090b090d0b07030f0f0b1903080d 65
    0x584400396040001e00042035a03924001d0320000c003001c0030560380d03a0036641c111281003082d86030f00601c00d1030118a0003852900388900307070203401d04860080e80b45441c032052a14041c1c0c0703c0103410b18000d001441c0c1c2c00070800001c3e004d141c2c440046d00d15001c1d210240d801d5500010700314869a083e140c14055403800d0140c00550800c81c48092581c01d1810700003440c4070703611180ca5103511100424030464550a40c20041c08002c0392642d81c250071341c8104941c0b0710501c6481d040c1c030b8201c1e108480104203d0920001203180d07000b95081250f0006000900300c042e00d4250307104244a0388541030311866241e21208040e218013403403140d52500e03001044594004001940724140b103208504125420482d030b90355600e030310101c00c00d080419900c090014800b80d038024507a03100401c0c0c0c40d6142890903410304081540500f25030001004ca4501c1004166824001d4020850b2001e4510040007085084c01e030300406070190003201400f0b0a0424182d40c1001c0c0d03514004070a89400818141c40c140d5443c0d03d00c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 111291079 1250 111289829 111289853
    0x304051c0611031b040b03070507020a18021305010201021e1b10230106020316030509091303030b030d0e0907020a0212070e060a081c110304081e0106050904 69
    0x840d05100c422451000602144101c407221008441525280c2c94803000c007100500b00d41c2403126143c0c209000c00c12061400c80200d960284d00c03860a951540440e00c04a110102c843e00b0000c0821026100141000741c140e014044032004412031420351a07035030006a081b0300c9195031080721500301d5000ca81c4502d032008000e00304540c03185440d0040310046c1e0b00d0740d0305000d00008054003c40d10307401c4134102d01c0c09021109140c00c00c2100720001321751400740065600e101c0d922000c0e541003c503010010034940039005a490030b0720081c11201d01840c0901c0000480d10840703000310046458040380e42043e050019002900910903255a04848000410030202c00e0000700701c6011489922406c50050b22980715101001c01750b50010302d0314600f40300300094a445c0007000d5501030303210a60308014036040010b13100c07020140c1034144030f8001e4642000300c0e055030b000c41d41d010b081e110008000038082c03000110000c0f12003001c40c41148141380700080c40c0c00d80706588200c6900096010106000ca0000c400c11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 111292329 1250 111291079 111291109
    0x1b101a18060f03070b090f04061d0c040f06030b010206011520071203170906100303050d1104140307140f270a0518070b0d0e03070206070f0213090203030405 69
    0x420342c50b44019000a01c3c2c60510303000803900324004162030515040010a611000e00c1c101c038140300c000e0070b201c007a00300f40d03c904031400111f000d0750000c130702ca164400d0101c1d0041e01c0d91000380c1d0f250940701c1d00c025016007240840706006108070800001c98540000c420600c9103900e64918405d45622464800d0907100c09681e07003218024544006400c221400303030503003258860b4407017500d214205412080c80c40d20040c11000b080d08505e0401610761850644882902d071315050942c1c440c04084042c03001841c0c4031400c6200400002408201003444405d500c800c40c008900720b42210f07886518011040a01d10303125074102600400039030f41440c10500700800140b804640044503081c151000029000a0321500240303940d443c1401041800044428800124440141140d500c4c0402404030317842200e90000c001592003143c084000c80600c00c81c4c031180d8000700115180d00c0c25090000b40a9580c07902240b042c0d02c03411280112900601400350709c15001000b0350700b020716050030b02816072160012 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 111293579 1250 111292329 111292339
    0x50906190b03060a060312020109050309090a09050d021c030e0c01030b01020a081603031a0a140111030403050d0905010f02070501200102121b040819020102031b101a1806 75
    0x40810726031020000341e4400c040440d004120b803880c2d4100011809030703e844002c01c5904000d0700d8000f09000000320b49110341c0a842c0d05000e50386514081c03000717041b0050004c0c0035008000700b50711016400035400b4800e4902c0d25480380701020070392090301100c0c03001c0f00240080d048452a0280780d030080c0d00400b100302c018010341c1c5000c0d10907924840186c0c00a08038040700e4600798205014194540301b026020883c07400c0080e10540c0700000070318a05094031030080c20f140b0201c440025640309444000401201004483c4c4640c0c43e13107480c0b6294403100c0140e8000a0310700c807001549620503090281141095000740203110f0401c001105c03415080551106070501c84150f24050701c10034802042032550358069104141002089165003184102c011942903409000600c500c01c00450000706101b0f54544003000a5002c0c8010f13401c40c061221030758400007581140c07290084021803107002c108060300b070400c440c000d0400c0c004246040074420395008100c0d480e00b4117002d403103841c07451f1300900c004103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 111294829 1250 111293579 111293591
    0x17011d0a020307050c03030103031106010515030f04020a1a04150801060807230f1809010f0504240e1e01150c050a0b01060e120601080c0105030705161101080a05090619 74
    0x252641c40c6507c281e20440c00601c007001811440b00707050120170b026090445003003030a004140e440008c240400b8010040045c0c1e4a0089000c564505804400414908040030300207021460f40100c940c0040c0b04051035007804041c0408038034440c80d640c905940e196241e290041d110602d00310f8520615900f41c2c80d820341c4020407107150440a001500c80e451010780c00c1540c0744001c060000600c01c175254100e000301c0000c40140600071003840f9140aa0b00141c5000864440d881c0d8401c210340031140101104084108010400380030100c1c0a82c0f04d0300040f00c1c1580300341e0501c201e2020a500274416204168500d807100c50030607114180c402c442501030030848209103010f448000c044a0300380e100902040b02005400801d003000042c0d00344425680010349250340c9003d10568890780203080c0b003410000c00000003100280102c042e1281c0401192444400034183e00d41008210355060819012401a800040d005451400b0340c900c60b0031050060692078030b4040041c503480301c81c116401e06098840c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 111296079 1250 111294829 111294847
    0x30f120a0e0904060905010e1f1802040509070e090c0d060c050d150f0512121b070801090303050c0306011709120d1a030307080a14071217011d0a02030705 68
    0x82d44041c09640186000600028645001801c540c5450000540b541051a010041038070010030070f414211581d00114010b50701d64003059242644000080d445840d02051281e030020005070030050310350500c152a1140c031800500c1d0f944003d004040d40d4000280100d540019619411109003541941020350800c2c019412100540b95000380b802400442400100b00d003020f0030801d84000c1400350740b4264040c5441008603211842e9603032142000c17000280360170160021b031260f0303104640c0343e8040c0c0751003076207a1003494040c02d520401600000d0811000c03644c89040e2030100d03401200c0585410306000c1c02603994030003050340200081002d0190041c08030050381200000e000300c508500c0e00040b00e95881c055001d2000f000301c44103020781d106201190024200c03004941111030030382424800b5100c101045e2541e4071489400070400640f80384d240100c1394000428001d181640441c00207541c2e01da182c40c108041000842d00c0b4804012000b04a451003a1b41c01103401c80c05a240032880d000e100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 111297329 1250 111296079 111296089
    0x1090504020d27080414010e0310050703060515070b04080d023f1906090c0e010909020f0703031d06040302070905011a070615090606030204080606030f120a0e 70
    0x900480c00349140c40c2d2030000120500321480001a4140f102d6038070318024691510801d500a40c060036400203420501000c1c0c680c060450026a0f0000808542e0240f01003805000030301401d5030b01d9404241000004078061038601005040140705401840c10701002d901c8620036400e0190068981001c200300d4500210020300040240f8800d20710452601d6109124012148800e8920351100d03044807004a402c0e00007203206290044040c503035050508010520001c000c00c143d0784070040444c540307004021801e41003a40042441c10907200c0141c0a0b1b900d2541e2000d81c402c0c15094040b883c0c0420013400024007039400078074232039146951007040c0100001a1880d004c1c0588003a00564404041048420b2060140f140034101d646074001d008031107146042c0150003404801440d90782c40c0c1c280d0004038048410644000c100c5c0040c00c0c087d842d6205009030095020780240d00d51030240800188040c180051011003042d490700041032042e00c0141c826039030380c2000c200364041000090b1200000d94a03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 111298579 1250 111297329 111297337
    0x605090f0f0a180c1d0a15140d060e060a0506031306110307030506100207030b041101021c030506030f0a1703060a030f08090109060810180608030c0c1002060c0708090109050402 78
    0x9410800070302804881005010039898580d03205545d1000496281c081c1c440041510450b0302030702d03070365400d040181d2040d40e00031441141c1d009400c00c007160400d601c81c43d40d04036004540340b01c42100a04e440340c030140030860380d10f4025071350404810404100009103064802e40940d001e0790b800940c01c0000180ca00e01c40d8401d4680308006a100e8040c0041031808421102800d40a8002040740d00d255544404900400500140200f24000030f002d90300d0b4000c1c00341d1401842201400d484821003080050014001502d12030b002e03101e0302d11202200400000d401080d00e0b00803480750b0012081031100f500d2940300804075508001030f0503000000441c01c01000c101544101c5186860740c182c107000400990f441d600c00006c000e501824030100b0007010f56400b055500c071f1211030701502681c0d404103003e00100e5011180f01d1100044d0300c01d200001203194426450203c8055181402d0700c00200c0c0d58a00a48000c0555003041141c40006403040300240312024042c1040740c200c560301c000007403c03071700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 111299829 1250 111298579 111298619
    0xc14030906120603010b0d0c05010f0e030a03030515010f0905090402120a0501060918030e1203091206010e0108011b0c020f0a09051902160609050a1202030a090605090f0f0a 76
    0x1006000f4418a481c003805025a01ca4003950f5000e00e40d40d550300e8a07191074904d48a201c2c148076401d07520101c03481c400d20700003250f844040c1c112280d8202d903240080003030030300700c1d200c1c03100c4080d4015640c0c6075032088401902600032036036660362450511080103126000604100d81c45020407800b40303903085040c8407a00c6075a004000015107145405401c1081e0b4254010445507080d004900b0341c0001e402242451803414141c030203500002d402e4481c14a180300319401e480c0d0200c0212200306100d20000760041c1600d1031030080320040e982c0c0b0f0b6030076130a80e48000b415490030388140d03013640b07032062040c500d8a41c4140003c0007004003051800c0402c9203045503400c510f0b003007616242000070040d4042c0004841051007401180b070801203249106014a0409004111035200c010080c18000100510b0100315080303400d0291100c201c1001035034a5000d21a51400b040b51803034001101d0f4007030026690100c1d000382001481c26a503c040040b500b0bc1c6014a1703600540501c000b0803001a1580c102072030b82 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 111301079 1250 111299829 111299857
    0x1b0b01030305180d15051003080c0309040f0b030601050d0303060b0d0614010f0f14071a041208060a0902030a1506030b12031c05040f120306030308160c14030906 71
    0x26607010b082c0c3c0f4807654101d80b1a4002c4200b0403400001031340320708010540c1013006600061549034003018038103003a040c1c0e03c043c00b158030205094001d008013000520844004450802502d003425000c03c003500c21004209615400450040103541030aa000a160a20900e00000c0c06610741040f0b007000e0b000342001110840d80e4900500c48107401c405425400703042400d081010003020703d00200783c1e03060030140004100e1003a04401c2c0900c486010344407280d42c00914401510b002101c901210304003180d042d80c81c0c5e9020340031842440d000f1480c9074003400f0050441480c90b805d294040c0081d61000d40300300709040d51810340380c480e0044984040003610480d94003050404031530080014140c0c414854074107030b8208000300400030004203544170a4100044004c80e103951070781000400544424400f0317240c40d03c000401c10215905500c84401c0c2c0f40b183d01da0348040d4480c5011068050441544d4a01042c02002c50304049202e15855400c1440404102d0b86403402100100ea10f54200002440360743c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 111302329 1250 111301079 111301087
    0x306091a090105060a08030c0c010f0513030f03090e01080601060810080d02101d030306120a080a080603010c11030a080907210605070c030519050909011502120c0c011b0b01030305 79
    0x162030022414001402401c000b1420401c913801c80275129003a4000c034a0520041801c104a954050b40954003005031100d107d0b0390f019603d04200d07843c2904004100c0000e02a03180105500801d210440d040e07607080401480b8076802c209059500039409810307068001006c200004092000f00000003511a656018001c0325080307040740c0007030f100114140405107002486a08011900100b078039070001040352444070a440c1380090fa0305108002e1006007800c03000281070007403c2e40003580306000d014150000c02509120340d40c1202c411124080fa1060fa030010481c064039144201501600042d14500752084295555002e00c2441e503000d401081445c90300711898140400351141d00e920200314102070804000c40e981c014460b204103000150707007002035941070b44458450f6080d0f0f1003800026198414a5840e80340054504802c01803c200601c40c81d600c00796040011000c0d11f01c02e0f64140c0003018003020500041d145520540000e040b2401c0381c0200c180429924800c590003103019817a01551 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 111303579 1250 111302329 111302341
    0x603041208071b0206030a09080a0804030f081e040501060b04080f01150602070611030904050a0209030f0109150b13021206120703050601030803060d05010e030d0b0406030209010306091a090105 85
    0xc0c5400201540280800e101c0103a107901101a0f041e508994115160b071355a42d50145a00014144003802030000c540100d00001d03940d4109020380d02076406078803040043d80b0440b03030440ba000400c507410555046801d01694484c3c0c02d01c3c0d82c0903005031180e130000c207405481d94110f02180d045030303009000e9030f0300046039240009000c0c8201415042d10040c2116441c1c00c000c4007075540c3d00b940c0b24203001c1003000c03009500501c0040c415a60481c10041c0180107a0a1440159001c5c0d00001d080360720a006925464660000c144035001d0fa41d640a05488211075000050100816104031040d810003900f07074000a0111081c401032680980b07070401d41420f401c0050500c40110001e100000407980444024000f1500000d231860450380c0c0310301c000e42d5a56a4402050399003501100040680d802c1180e220301703000010010703204034510a2010815620788c10104002d0f20514070000e50061804001400481d1880c1c11818001380500e02000c000b0035080020603080c0c1c402c44200c1c0003655117070203203d0303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 111304829 1250 111303579 111303587
    0xc040609050402030c0a0503040f0b040b07170f161106010b0403060c0c051b0f130509010b10090302100201022a060112080a0804030e0310060e100b070303021806030412 74
    0x8007420781a2411400d61038603411540c500d1140a04c4442408008000141040440c0d0742d00a211540700c00c00131654280b03860329104805007540c1c00c80204841c000d20b840041130341406a481034400e0840407030140c440c1402c42c0300e6455110101420012a8803186030300c910100100c600804001003c1992a844c41c140401200e000c1600c032010010364000d2507000c550001014006040e050fa10a40000c03d080c00042c0c1c0b190700b0140d00c640195240c0103034801c00c6440e500440c410350781c220090003d01c002100304040852600c005038082160b1400030700142c00c00d54000d0007003280e540001440c003501c00c001082005911341e07005007441d07035540d025100341c141440020b004141644d041039400400d503440d25111300684000030100039003000018149881000501880840a82520600d800d14007508010b80006d01840515050010100b0551703103660007070004a42c0000c0b161400d0503170741d81d403c50195220031004000c0c13140d2042170f444e4581d04e0500440c000c078030800d0482401009000090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 111306079 1250 111304829 111304847
    0xf0907081522051e031902010507021c020a03050d18051b0307031106090301140c07050c09010303020706140c16090c1107060509010c06020a030c080f0403090b0318060c0406 76
    0x704540c401420202d0001c0c10000e4610481c009910105955000308000d25186010741c82e800d5502e0002c84001c080181d4045d40018003d03a07503075007a04c0541c103040381c00365030700100e41c0311100050348011490008644030f440a010046000036004c10400e81c02d002600c811881401c056405810a01c144000c03840399a000081c0800141c000d40941441c58981c0c10884d0300090356a130292000044440c42c1d43c0d020b6014086040d43c0300f16142850034801031850042d001203a003100e1501c00d1035490303d914034005001c98100e030350590041811038101081259041081424800004014000440c0042082c029641d13480074605409114034a01040c100c1078920311610311061041d00301c0360205482c00414054140c500c41e0030003580c3d480040004071481c0071186d6000d002c482c80842d41f00074940d4150005602d0104599030561340e91140038903080c9943c0c0a8400034040f50500d00f00708913015002024560094840d841c2621121907408035505141044030302400030b183c006810b00406810412030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 111307329 1250 111306079 111306121
    0x405031b09010303030c050705060103061e0921231306050702011d06040504021201050306071b020d080c030310050103050a111c0905030406031407030507080f09070815 74
    0xc140c030450310380041040014180000303410103440d41744000815014900716076030340ba400004c4031181e40c1c0d0f80c104600100303007250301c40301100250302e00071f08800810b0181c0071000d60800508250310010042d82c280d00d481c444200001c0c0b050f003000a1a200ca44146900749160380130420a554482840c0440c00304481070300710805110050001001607640005036101c3d8801030144055104124400074800c0d014541c41658060300004d041c0303c00c015036100c13060480300141c048400c680c40d0701c01f080d221048030130704403071100c03002080400c054640301c0f803a0200c460142e03a0040c40d20400d030300c050b07080d40e10840740e00c203031408800002c01c03540d68903200e101da1010880341c1c00c110400e20584001c0c540e00c220454181c2c162110344410950812507403000c0d01c0140d2004c21281c1e140da4500e0007401504940f1011110002507000007242c1038068041c291103103030280d48034000e40c0d42c1c68842d15440c03000a0101882c6200c0c542e0b02242401d010007501c007a103103000000030100d141403203440007039a04500311 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 111308579 1250 111307329 111307363
    0x4030f030b01090b09190906030f020f01080105011e0507020d030f02120901121a0303070c1505070b04140a02090a061404060b0301060c03020f010510170f1c180605040503 75
    0x20060030003e1019222019000c456074800f031b840c2a807502d0b00c0d03400035800117030946180030310010400905482c0c00000c02d00c01c0c2c50700310350168080d0054503070280910070b46000c00d803d820400e844c18030340380c42d000304031145090540c206801500819001d0100140c02c030081401e4000300a0865010092404540b000c05070540c644008040001c0070041d00704100d030030158a40d0043c0c1a15016a03200303008282025040300e03210720090030941110317503130381c440d85440e20110012050910301c50400c940c2d4035a0000c9400420380c40d44e603144006040c0001240c007032400781c81a00d0740160303140b01d603da00a010100003c20040d040403451020200085070345072145181140070400750800c0c006a0b03044941c02e0400007040030240c01c0a0741001f00b082c0c1070603815460300c0b0401000007189001241565140c0342c4070001c00e0516151607948071500c0c02d0b21103155002c4008160007502000c500355480039145843d0301c4058418810f658442095080b14012940200c1d040c0058101045a10400325050340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 111309829 1250 111308579 111308597
    0x1031505070f05070c05090705030f0a020a02030405010806031f060911091305100b070303270f08030604060801060803071b12020d0807140f070602030901020c0d11060304030f030b01 80
    0x240c042c1400c003080b0800410f108000c9808800d0004000e070750b20041c040074000e070030315140441c4002c0031a401160321042550041c0003040042149200350340030f44190760011494a03007080010346003000010b000d5641403086071043d41155494021311145c803848808007040440c200031030070041e02c10010048140700c0d0240090050740c0d903005e07a540400c06607d2400030f07079500ea07001c0e0045400615000004543c030001629070801d80d0503401138011601d002c510240602030401c0b03090b1514040c4d0009002440b5000c1c144d0042619980215000b81008000280044c2d8540140d402d450089e07000c01803c1d04042002c0c001c4c40340f031480a805500356515941d030754500b000c0c5201440c41e081c010181c00385281d0b800310001c000625086901e01c64004802840100c00d4600301d680d070344c0c00d0040c0d40c50b02d4000c50b02c00191382e50002080d039040c2039058001c1c0c4200b8580720107005100d00045025a11003590200c5104503446981c01540141c0c007a41d5000c0d440c0d005580080c003906d9405a00c107041040042c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 111311079 1250 111309829 111309841
    0x111305010833010c020d05030a02011406060703030c02031308010e0c0105090307030b0a0209061b0d0306060f08060f04020a2303070804020405040f0203070b0408150f0103080703050d110301031505 86
    0x1e04901d038031411202c241140a03000e140125820301c89800d00940102c812010042407101c008050f000340c0b00181e0081c01007400840c1c6104204009030390b050b800460610800d00003a000e40c20039001111948103da041c8980919034034104007441c3d110b51416550341103840014001070025050700682820103604d40004030700442ea079182680f0000d0300d981b01a5001c6028521107404803500c158000701030720b880e2026a50091118204940c003c096441900b103680c540c240240519412180c16850b0702661201524003038071111340003013460398070003140b00c1c2480c25681c0c0d0b0b2000e0080310100390354201860440c016006076491060f18941c0182c0700600400c1150756009107440c0c0c1c010750580300448c003910795180c4460315040b080002541070040407004203040d4641c201170422503843c001107620381503050002050552084d0381c1c2040803a041d1005001084500e0700070800d1030300c86d2420610308541c040381041241e404040c1223428140c0000100305010609001c4c851b44680d9110421260502c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 111312329 1250 111311079 111311131
    0x130512211b03040309030c03060c02010f050402030c040c05070c03120906020705090a020a1b03020d031116021504080601090b010e010201050709140f0303030c03040b13080d0f1113050108 82
    0x65802081400307030000005041511401c0d00c54011640030640c420380341c0e26031403c00068041a80c9100046d86007140003d8020110300400b801150083d000e0621185440c09100151012040e11010b210b0200040000501c8020b1032400450084140308500b842040b00103007540711960140701190300c0042c060126a45401c401a04010351074001641c48400722001d81b1085a003d00030740c1090844031000007416000304640c00c030021a0b540c20030107128160401481782c040ca0344520143c7c150401d02d5070050800000f002d000c040c030702c25254109691281d45501d014401d8104002144d05c402442c01342d96002010041c504000340001c0c406450411801480306a440c402e1540c00403181d0804083c0c0d0b190b21600e01d0804101074140c0742d80b454400c800038510b5005440407125031200c9400502070f041031b88000300003103a115103010310b4040c04140000280080c038401e0024156502414a074040141004240b000300d00002e41c0780a900d42000544020001404448280c90400548054031b5034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 111313579 1250 111312329 111312361
    0x90703080a0503130609200409080f0f070c080a05120403051f0b0a06081803040608040303050606040f0e0910050c0412051014010e06010c1a13051221 66
    0xd00d03026441c3d544410341e0034182003407a90040d05d9607151035028170600603107081e26082080b412108881c042103040a10044481810002d08060414003d0441d1418400300400c031818285042c01e04048140e21850340b4110310394800c0d031f02c50b8488155031040200c107001087c0c802d41c0340000142007600e0354469648a2080b4604507001000f203c81f1030790701d54005d81c00400c041102921560102ea200e48001d03100803015600e001d41c0006030344119040040c00011207003a2800c0303a44020700c1e5103581d6020340c060900600f110390300c200c0500c03010a8484800d804280100942260b403a05d80c1400d490039410175003003545031800d031402c03c02005a205d00d0300d42158210b908a100d0031050720418100142004100c100651030641001f21541c01408190038450580304621402c02d403903100c0b44010744602c03602100040c0541950700c1c1d2018155003035071403280c2c080c0e01d801650344006155238500341025611444081c2a50340130940d444031584c0140c2034521052891200c007440d040125002d101c00d11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 111314829 1250 111313579 111313597
    0x5060414070e030a050d03060501080108070f0506072a030303050609061c14070806100e130308041b06030213090510030b040804090525020a02090402040506011b050106090509070308 80
    0x4002c40341611600c040040102c1c2940100c02c0d24918664034a005018091034440c4600140d2100b00100d00d00102140c10821280d500740610445482c3c5018022103800c003584c21b0b6804510440300b805060117000e03100d82d520070086600c900c0c5c00d0440c40d000d001c440000d07000c2c1c0d020384103000800031592140c10300c2c1e6000300c0649016103070070007880c0342c0311401d021714071820416801104000580140c0029120380154181450584445c2c3c03280700c0d00070030040c1203402410103d050300599000c83c2c0500d1580f50054010445018222800da010f00000200d42d030107000041c0d800102d01e84100c00340540310002c0c5c80290303c14401b505140300b81c15100c00a501000d8180005038002c501044941000c580003400d08400c144402d207801425081c0c90880da003c010f01118009008111203403022403250003c07a4002d0604600b40c035141c00f444001c01b4000c04041c14012098040c03105e03000c0e183c2040002d54895400482c0607401c01e801081503d00213442105580c0c000581400040c1415058a221072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 111316079 1250 111314829 111314837
    0x1030201050d0908040e060a0b0a0801061d06070f020108010b041202210d050301031a090d030f0e03070b1008072706050d0807060506060a050906211303030506041407 73
    0x4000c108260000f80000200100040000500040c000b5155403078240708107402c0751491101139840d900e503003a500c1b4040d03500001030076840040c44900d000f490400010082441003042c080000b8001c5041a44000000c2d02e44040021a403021980c0c803000301809407011000307281c145031500703038a100a4004854020700c40c000542c81c20a08001c0c0806510840d400c000c120742c40715070f0b500005030481d48207010550b0041c80c6149102045103d00840e02d0090018100a0118142e9060110010301d0b031062120005038540d00d40090550b0300300058007205026111030200b50074101001c1040003c02d030b1141e9407d8000c0141027040034030350b802049000c07540014641c440c013080040c1100528543d04540d6001c6144507240b014040c6407005042007a2003268100829281c3d0700c00c2011500441ca003c9000500421080c012401c16a025092610003201103a40210b064120050ba20030100c2c0d0440628003100055024142d050283ea80c010000755010000360001501c0d02c070000b04010300c070380244 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 111317329 1250 111316079 111316087
    0x304051201020309010e21090f0904030c0b090a02220f021321081b10060b070302010b01021605120705090a270b040809120604051b0a18180f0303050f01060509090103020105 76
    0x6d40c07030309c612000303560b14000c100035554a89458040e01c1e031000040c2c16a040004600003403030f04c00c0c001594014860b002841c4030380540c00d44120300010b0b01c2c0380305000c0880362100504a91404140060050702d241d00c0c07814624141042c8400403c03106407440c1011603011041d007000491030b5102107901c0c0d030000f1100031201d0201400c24501c2d058510083c818414980840010390f041854003a12141344291300902186602100480e90307824014800260841300810801c0740d490070035025200124440d00350b03500311f0743d51070000d00d25600456031001100e8403491555000c55803210038500540c0b0034162065100040d460301c41c1c034444002c0005018035030015140d121682c50700c2422800b05021801c5400d80c1c03400d46805070325103143c4140c0c0c91a03a80c4e81c40d9804010302d07100c000340c000e580c0c42d205008420781c401f1031582c0c0a8080e003d241c00b00c02c22410040c0000c10b44480400c0a03ea003e900c001c102804c044010240d8400140e0000c41002001c1c44501520387d5114078290461f502480c1854035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 111318579 1250 111317329 111317347
    0x603010308031b0712050409050105060315040b01030e01051017160b0706060b16061505060d0c03090203030406031a0d080a0e031002041806050316060f020304051201020309010e21 79
    0xc10720131500054000b40b0714104601800398040300030010b880c0b00f140c0601a90360303920240709981c0002d41c0c158581c804a00048201c0d0b0503c1da200400f5114145004242c120448400d80d003194000da440c080c2141c01130b94103028501c1584c1e0b2070380300c03c0c00200c000d010441c0904103050030f4080c58051304260080001d50002884608d801100150610039282c0e40d55802c2e0102503481880d07041e504841c031300d08044514102525503400181200c501078081441e0a00c2080710000502030f9408143c245a910038954015071070400c0500050581902c0010b00703241c540d01c0208003441c01d9502c00d4443c2c005201d680c8003703405030054914540443c01c25145c0300809000280c140760112460f804c0c15440030038001980c03107040ca501ea45401d41c0e0102004810340703890030705442d6005410501d805061803c010000107114840000c1420b401384180ca04003074444c8001380194491099500380c0369004014441280000e10485156481c1c500c0241031454a2a1080c00c220400d400084a1000041001a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 111319829 1250 111318579 111318631
    0x2010c0b19050a0506130b0d02060904020f040b12090a1101050315040c0c0201080109020301050108060915042a0c03020d030c02030c01110309060a020702151804060f060e060301030803 81
    0x801071031006102e2440c103095500010481120414458007202c0080c06d2544070300d11403940701d00c2e806402c0c0c00307100300c45409001c003a5000540d9240c00075401c1200c03000040d004009040908014100c0750b0742d4000c8444880005100039000c4103058001c4c008400000d030203458100022882030a003a03880383e80b15101d010080c030001d070400d9000360800c122005000d51005084030054803d88828130180d032194101d404a00007401003038045a010004100d0902e8211041c5501800d90104c8a596003d600040f40c15503552428803040040341c1d13240d08855000320740070100310310020b19102498940035200250b4849040c0c2e8484107050759420400c40451083c401c8800145105000340182908819170481e683d00480c2d0311040350007a11f001c00da00840364000c9a82035a00101044500388030349650b00c22940c0075040075002524a01501c00040e1103a02440b002401148620304a5501c2c20402800358281c224290b80b140a0400c014000514860300b501e4010903c02c452040301018604024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 111321079 1250 111319829 111319861
    0x60807050d06061806050c060109020903100903030605040b03010506011d030f0a0516050d08090603070516150f09080d1a12070906050109030f02040c030219050912070302010c0b 78
    0x1801c26080c28400320343c45804c861119080f95200030041c10080d5521800c0303403140206512240940c10410040080b44050340140c031500100a05845400c030300340310b120b0210350b03070550100c0100307490304001c0015140c10b1054400b6260250001d00c2240750074000204549107011201e0350062521114000b103480420101801d214041e04440004505007040d0381e580b081c00750b0006103220580801300301414081d2520b050707140c1c000a2241426418003c0007580d1304000c2c503400800405100e07090302406085201c4a1181c05528551030801e410740c0c2c072000b52460044190850380c2007107030550000d907071007007182d03a586404800002e512511300d8030124150f004d085480d92100c0702d00444950303404040b5421089858529080129030b0b950340c015a9001e07aa0300c00900011000614071000d8145600700c01103c1d00c26140040c81c014182545030030b040303400305800b0001040481c8411140c10b24511807002e40c14000000c205040c91680000d1162521410040c42c00380700c4404501560396000c0300c1d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 111322329 1250 111321079 111321097
    0x60303031801150806040b01060207050a060507111507120305190f140c03070f080606030c0901090f08010207030905060c0a030c110a0e06030607080420010903050a030e190f06080705 80
    0x16003e401d5982e414117641d150103481c2907171102d4440d000020703401d000103246411205c014040b281150303d003030810b440540200d0021f0360400c5040480800310365403026441c0f4122200300c00c85441d80b1007405d0100504540d441c0d4002851302e400103000180e0804680e0b0350301042401d03400b1680d48011141d4002a0031031340104240320015500740884400c015000e940310750b5082d82c07000c01c807916400044540b56410380d89260401020400308400e4044a802071a980f80c06041441d100e5554202c200f45035481580500c2807a580030680b00101603100e103860b001003001b10317805420111002c00701521804640801014024201008410403440007003000d83c0043c0101041d0303030b07155200f50380094907100701d40d0b942c070a000d4100014410b5000c2c2002a0086800503150244140189126001c4210304032610b410f03c085040d0000020b1810042e001d00d05206c1d568040300c401146050149401c910203006040341046c00040c000605d0b4181030700112a014035050000c0d44a880058626105410f91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 111323579 1250 111322329 111322361
    0x12010605070209090d0c0303020706090b040803010f0f030c0501050307020709090803010f09090302072606091b010504120204050a02040302030a03020a0311010c020c060705030c0303090a05070e060303031801 91
    0x145190404040d12180b40240c886001596885400caa00c0e101e9444c40c0c54045034034400b40d000440c2c4260b000e48950f40c0f00d01c00020b030f201c5c46d64030b511500240c100d41c1201c410100100510a905140c071803140101041c6c0b2010003001c2c15960b91840001c41c40c0100ca0401c0408400512890700c05c1102000801d16014200041034003070a1044c265030090042c00c080c050030304400030300320701240700e0340514a4141c1c0c0a001007509010022072280701c2c0c200740300309030102c4504049401109021850040d006d81004003030104060003410000d45400e00800c0c10300400340020425541d851070100b40c20380d0b044030000b8541c1d6501055800900541c1c00194042c800c106085d42050740001d8881d82c820b01035114408903c20468115090703454040c802401604521881d100a0a0000103003003907078401d009403810811980700441c515001102c4c4510a64415000e80c5c051180c01d00c400720240c0440c030700d440d009180c29000b1a9036840050600c540d00800784004c5100781400707602c0260140e080080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 111324829 1250 111323579 111323581
    0x3090603070306030302121c050910020f0904060b1e0a0c06020c0a050c061e0306030c031c0905030607090501050c07050306070f03240b030c0721031b0e060901020312 73
    0x70040040c03a003400210050f03c1443c4080410b030414505032681044080310004c01009202c070500e005c5c210140c4141042d10a400c0c1c0d443c1c41540324009451103460300114641c850001c02c0402007a40d03611340c84840d0261b0204000c0b84040c00f0b442948009071125500349503680806001103800c0ba05104006d05080d02c0412a02e40207100854060104d2313010340c003181c44541c4182d0800015200c0d4500094a500090410254a402610107075502050050640b45811280800710b1f0602c900c2407100c807071f022802c06c0c8074092150854460000f42405400034a40da1400281c058a011450301504d41400f80201d0180201081040303040080d040140c2a5050b80c103215801500c0240c840d03420070702080c1408254400288106c10030740c2c04c1c1c1c0015814104840c80c0a01c4684954409001c086107a0300402c00c030b20209a99140204c950528008031080503100755000404640321119540f500701801041d0080b90303a4000c0b80b00415460403560180d88844460041c0d28605c14100383c00c4807004180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 111326079 1250 111324829 111324841
    0x50a050303041218052b0206030115090602060c07020f0f120609010e0102070519150207080306040507020c030a020108070c0c12030e19090209060c0a0609050d020c03071703090603 79
    0x10101d804000040c1c03204508002186a074440340c0421380030340b54100743c0c44e8000048a1001c1c00707149100360420390480c030095046d5001316046a20981101c0552030400781d60a420542c0000060014541440509050309181011140c03c0c031405e00702078070807003450f080883c0e00d5550f0310802c050154014009942000e503da0003944400040720002c459520748565401c240301d060007103611299018000d000c01c0c84c01c0a40444441b51455015134105021a140d41303110b0103284001d14086004002260311303454103008000984000801a00440d04980754818051b10002504007440744d09080c55040e50703440d10006c883c00d4000d00e09c043c2020742100b000050f06004011b07004040c0d406070303031410211040e16060115a980c00c0118101042070404104001c0c031a070380c003508601000500c0329141c070100c3c42c0103928002c2041c0041d40c04030341d1111000708200040002101c4040c00f400a4841c0451290000740c1341c40442c03142641003001c003100d0308002a03003071080390030202000300095124144a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 111327329 1250 111326079 111326093
    0xc0d020a0903050f0f0307060203070903081201050a050a0e06090a29150703050d0e0c1e1206010b0f0304060b0a03080a080906060a270f020d060909080306060304050a05030304 77
    0x60b00c400d403150702a14404030b48030380010800c852100c8000004602d07081003691504001e510084c000e60801101c07802c044000781e82200103018890644220032500c3d41004104142490b496105900c80c101c101420130000d030304d10354890384c080c10403a403403030165450a90920281034080d154001e4a03c40c25407100f52a069100c002c12041c0c4240d07207042c5e40307150841012441d4407070b0358800740108100303000102800c0516001410707060f507410700360364141c82c500d0040342022a00c1141c0c2c501d0300c85848020b01e820300740394003010300b91810070004115551400c4203000780d6106921902340c00101c004009020b01100d41c01c40d184190000c0c04803591030759079042a180e0343d04051070310400150400d011909513100003500c01c1c041d140003004404002d2918000d0002100300c20861100c2800034009040400d41921848481c4181300001603a00c0c0040360344102202e10760703004003403c50724012100e03001c03c590750290303a4496025a055070782c4c1d850354104035107001c003822070042241c480042048100001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 111328579 1250 111327329 111327347
    0xb030a06030b0a020a09030f080705120306011e0e0607060b06070b070f050414061b010510090b0604030804170f010606020c09090f06061012050114030c10050d02030c0d020a 76
    0x1d58a0340301240c64950340b99082c3d1080317101042c0040d5100009001141031583e502a1651083e07002a141034090790704e29042c030f220920200c1c200d4a001c000c00c0181d5802203000c07089000d20b0003040c03003042d501850180c603920745848803d0203104042f91120401041e54000164000002c20150304c034600c80c40c00c8042d400d0219504000146050f00025199019405070b60030780700e981400a0182c40c404c0d0900031160810500c01c0406000320150031891036080c8111400b0300e0000c8242c10740355041916043c240c079140035000d40101d0b01080200042100542918241c0300380d40c0c1680b420034021101d15103412071074000c140c41540b9207100090055000107031a07504500a075180469955414000344d102d181a0460803001e4102c1000542d241c580400c50b0a0010140c2c28030800301200000f6641c11104260008403042882240c10011460100411469540d044507445440d10b1403110082090080c01924507590b5001720108004903101019a5454150704d801103455100c40c100040c4507400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 111329829 1250 111328579 111328583
    0x50f0102071e080f0a1413261207061103010807050a0506040501020a022e0207031709060703030906201b0303010506341410020405010c0b06010201060b030a0603 71
    0x20030410b6030301e0040c0c02c1ca61881400750040c00c80d5003400c1800410714060741c0150080c20420040d146018462880803029010410185942c030305040d05219800401e64401e54440c104054902040f4069480004108645006941030240c407a225813900e0809414000100510380f03c000c80045030310840028418201c8404695041699590300148605403240e4055540142c0105203408058100b41a058103c903c0c82d998008590b92200b4400000c1d4441c0c41d103441c0184c2005908005209090b001c081129100b801d419103001c1e6840000f1b0b240e8440c00d00000c051549401c801c00034460f0f2580881d105100040e020116000864503640300c0d0b40c400c09090300c0200464103080550300d40003041d02d060f5131001e8034181c0b0f481944907031803044441c0081d600002c10304440c0d14078a1400c1004400700c3c010b00c00c0300c1c3d0300170041c0d046212038144111686011401d51042c03208002c0380c0c2e40007a2084403c1d03080108100c850700c6550040b80500b01d00c3e0002d042c6014008280022001c0359070000381224 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 111330935 1106 111329829 111329843
    0xa1403100e010b070302010b03150117030d020a050301060f02060c0a0e060c070626070e040c03140702030a03201b07170102030a0606020a02032503050f010207 70
    0x301003608143d0400102044401c1015024020300ca4007031005c8018000103004544901c0c0721190520ac2d20280980c12501825103000610888000045141c005c2d540d4040b660070151895000303124010000e031441039840300c91440812034601a0802080b014a040341180089404c6c1d40340e4540d00d0351180c8200310130001e00e803040100400902241d01da4002c400c0002080713607004c00d0070040c031195600c107807400c00c5002ca500c44203540c1c0e00c032011a000240d600b03007010220000c10314244144005c44900050000c031b103030008013825038947c5581d8140f00811505c0000e00060034007082500c04075200784010702c86200900000c91400101d030b8202d0707007040da943d0400150016060055142d41e5400800e0016400d6070780075142c05020a4002130103020f005601180d41c030040d5490380011180c5c4510a5001d0380c92050a00000755040000c444501c50449030150003980b120100b101c4103 = true := by decide +kernel

theorem cover : BRFrame.Cov 111151079 111330935 := by
  have h0 := BRFrame.cov_init 111151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 111151079 ≤ n) (h2 : n < 111330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
