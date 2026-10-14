-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0433
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:46:56.445594+00:00
-- url     : https://prove2.me/submissions/a62b0b86-4290-4ab8-b46a-aa72b02d6d17

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 77697843 ≤ n < 77877699 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 77699093 1250 77697843 77697857
    0xe010807030203090f070b09130e07031716050c01090b07032f030d0501061403100504050403050910090f0f08030405060a180b0c0c1f030504171303050601050a06 71
    0xd060096025607000403a0208940c0307003048401d461880c0c1401c9802c1040f16800c04034400540d890b191041461403640c80005010003160301c0502d84d503881e603d0000a10300100520203203942c0c1d9405003580c0c400000f90320214140382090401d1a01e40c04036200c5e5500188403544003003444190001142c10142d415620490001c0140310311000b2041c44000d070a40b42c15401c81400081403007080600325140780f0000004065141020141c003d0118803d070a10105d400e00c1000380580c0904420001c41d0000d4501081e15901c80c90304966a2042d46842da5201441c1d010a80300c09a201c07440a0942e0403025218112585410165096207036911400c082680100003d0149007002c0c1c000d401d9040850a003841c00554980034002c5c002403940083c4e18100700811480341440042000c40d038402c00035144001c2804c0110b010000c1c130340940c0711041c1410b0302c4601190400c0104400100c82c0d400c080c401c140c0f12000306818206400544c402500c45203e5400003203101d1901c580c4070000c484094448071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 77700343 1250 77699093 77699101
    0xb040b090f07090801090b0118060b03040b1509040f0b0603211b060c03090d050315040504020f0301020a2001060b0702090405030405060d020408300c0109020d0b160e0108 75
    0x8041c2040103000c203003000044040001c01150902900444030311400400707840c0e40c1070107044140392690340f5200c00c1035404c1107010001c0440b100100c0c2d800a8018281c41441d07501d030300f2041e04207030081c2c65554000410500300014442c0780092243c0c05031080d240d0344420f494039410076a40e045441704c1c0c42c007465054004120108800c000a00058090104049102000c214494100101204e001d9100307031002041000c907502c10b010001440d4001c1c20141d0440c00c1a01503c1c52445005010b14052030340c1380042000d41d601c580580b4003d200050080d95103100f240801040410301b2054075800c0e91850142d24010781c018082e540944481945982c20104a9020044c809801400c2507410f40410440800e464440d6001004101c85e1140c01580da14034004000b0b1a002003c0c60f0020310850009100160b02546003210442c5890f03034461648401c14004642d005140e2010000d6001100d00581c0082180f01501c2e50b11031044654244080303030300050203540e01c0f00b0540e506800105414009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 77701593 1250 77700343 77700361
    0x105030c06090409060207050c030f07030302070608130f29010308030c0a2003090a140a05130e03130806010e090c06070303060b07050a15111e16060509010b040b09 72
    0x5030640b0b100080c004906100c01d41c03a084102d034030080d0195515084070807040c07540d0800300101080e818400c801056030905c2c684001f0341350a2580900010401d0301030114000382d14203010a02c1c11904941001da201d1864580b49450b41d122180c3ca103107540481107030a04003c9035120050480f50411651031540d6600d002c65411944040d14290511400744400d58440448070154000c0403803000007540d42e0407000301044240081580400140c1d01c6100c1d444190392502d0b001e42084440c1510424801280030000c0e40c098452400e543c0b078103200100d5495100740c0b03045070300000c80da60201640c0c1166211900440e84000440d4080040d0b40440b040e0304190914170020b00c00180245800184181c03100008074040d403024505403001d07806400700b20140140349490b11010000c0000c2048600ea44441c685e0301ca001c2d1000050000c900100313203996031108042255080d0b28002c0c0e104041c6185403405000900c41070307624000b198681541010039042c14070900030008001050240c0da40d8800c006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 77702843 1250 77701593 77701597
    0xd09080a0b06060403140d0e0409050a0b0903190503010302040b0108040816060b060a02030c070f120b090c060c0d0908070317091516030320030f1015030f0c080105030c06 75
    0x102d150401000c000000200c0c5a00b460024800e83e03d801400e200b00c0c070b00100400030440e107140a8400d510f4120310700300041c40000c4a0116540c0709a4686240c0d60708039070281503010303000403022101c69012000e8a019400ba0045044c5c0340f003210104801c10001c0011540003070b080350010000c1c078003085880320440010400001c3c05100d14008102403980c8008a40c41c2e0700700400c048056880400d030100f0009d41030114201810a02039410030582c40c04802d03020317101c23030036401404598008000ca182c080c0c040c4809440404080c2c00c0c20343c0c90342c26070303801682c0300e0003040301c030000078441d03100410300550101d10103084036049040284501030110321101d203680100300b80c42d4442920444001150264400b40c00012144081402442218100507040e42c642e0a80700b00402d25800b512200c45001d0070640b41c01c107038140d04407962a03407405528000028a80c0060030b2110400003088400ea51540051007881900e500c02d00032404040d0007994080c1080c001e00f1740c1604010000e14041c200b07080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 77704093 1250 77702843 77702851
    0x70e07080c071103070308090111011509110d050903210c070314070c090501090f02030c0313240f0608011b030b01030f050a0b0102010c020303040c030b18010213080d09080a0b 77
    0x121403c2c0180c00c20000a140c510a80d1044131600000b1804600d5583c0281616040c0007204000703000620f01100500c000081c603000380d8000c5075540310454118164017042e91601504a0020051400c2840c182075813600144040244401618142c030903440d1205550b600918580203441d0a02107035980507100039404e000c45c0c03840160180b0140d4042400701c6c102500500da030041c00213180d41894a9401600c041ca1400c3c00030740e0041060201900b4600304483d4407102d100010b0030310400900c3e00034801c544a03e0710b03410700c00700d80306117103800c114039400100d02c282c46401c204941c0356101603442c280c0f200800b500307c088044208030560940242c11400042505140019242241d0802c0c2d904441c4142c1788400f0b83c0750f90304110040395809118406000c2c20340d000860642c0340c40d989401d030034845400300410180f03c110101e00d800b41e01c0750b032002080081d20000c0d5221410f44062205800340d61094141c02d100d100c020b042407074010030105086d1071110001d401054019100c441d08600050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 77705343 1250 77704093 77704103
    0x20f011e050a111509120c1f060b03070216050a06020a02040c030608030c030c10090f08090a0306021206030d081b03090717030409060f0f121502030a0c02070e07080c07 74
    0x14000400380302d080c41810600780d0210134200381d505100c090715141425580c681e00340c046041000034030003400010100c14041305251156269028031608002801103507100d11091031000c401c0c0100943c000c03900300d00b060703880e42d030091845030390744200811808030f40315080243c0c004035024400750905402001c2040c000382000b0595540d12107503e441e40c0e00c500700e1400c4d550804119980c40141c103002440c4095503c1d98140004841520b41c0c1b01c0e540c595083c0101046000680c0e0f8509840e0360003542e0095400c40801c40d20340c0121500780f04c01c00d00c2150072a11078007400300c1d00300c28a8082d0200d1801140f41009402d558003081408580b82e900250042031a03201f5003100007140030324180030f11101030b50440519225844c0c207060100303940c1c0d1a0012111140c484c0030620451001c03002d0503040350700001d036091580d038880c14000030600c04550340000e8140000b080286040c6503812215102815508035503e5566819020312401800c1d166940000c4c02034021841c07211414000c0e011081c011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 77706593 1250 77705343 77705357
    0x307110d0f030f03090b010f170d0f1115010f08010c03050f060418080a0f020706030506010203070314120109022104050a030e0616050c0901050f010e04050c040302030708060103020f011e050a 84
    0x1781d11041020f0300264000f1410a8040c1c0042c03040640d0b80c01280c40313410010700144401c0e0303400a00074020b071024201a0742000b1034448c402e011040701b00540112074000f008603070044c0d40c48017a11072000310503005006c85503080c280c0d030301d6840b44a071003500d2103200f01411880c81a2190740c10080540031941c0c40c818603080c1010007002080c80c200c02050066841c0d00d0300da03249600400041c0c01c00b000b540c0200d0501d071901040040e1643c000c4100c4041c1545441e00300f25110701c8000e002c010b802107103203650290012000204500c0e9066005040b041401b1060149040c00310110208960301294014611b8010420700340019000318075420040d08020105800d2012951075031941c00300c1060305030ba01c0e6010000c0d14801d4101440218050070b001e0310100c07608082e5a0018006440000c1c0c4d0b10b0246903070714009941c1000e10380548002d0341d80202036070000c0e13a50346805a503c4100703010580c412701c401c83c2d8609156018012554140c00b0524201002140000d020364040d04411300d0b101c00d0000c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 77707843 1250 77706593 77706611
    0x30703091e0905091c02060906040f03050d09061e021315030908030c0702041515080c09030f06060a050609130902030c061912020406022d0105090307110d0f030f03 72
    0x6240200340c400e07111032004008007412240714031840c5d00c040c2011130030340d0041c0d4144045c00502103005035020750044a00d110f065100d00d011140c0d88204440c82c41000d00c1d00030303444200400ca400a5110141b0300030418142000445400100d20030302c844221074a440a00c104000070411418001403101c50900189411f040c0d03c41945035401110045d040c2c2d403001030b018085281c12301c1582d115201c68940089000e0412090310790090420380f030303401801007001c000f40480d04020201d90211802605075000420150403e56072001c00340d400c944160100d003804690ba040113429201e01010040400c5104020344101c000108200a8266098000c40c02500c6094803044018007481040340102280e4071080f550040202c81002607412a10380104401c200740c50340000e000794904940030252280e0000d480b200041103030a511004555402c101c1041060040030002d00314850084c000f40f50342c3c01c412010456000c005850091811442c81085401300b071180a40070203d0f40d2509000401c0c2c03107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 77709093 1250 77707843 77707859
    0x901050403060f091e170a050a0c021f0207140f0d24060308040602100b0108150102031902060f070c0201080c0306040209030136020a0e0c0409020406080612030703091e 74
    0x610002c0710034040201c5071844100443c50410404122000080b0782c18407d100100034000d103c1c4041d82c004018181c01c40806644c0e6049140b0494181944040e0b01000b503004041d4580445119100a014050398030041c5828440b00c0d501c0058801082d003050700c0d04581d500c03011951860a600d200015418000a0080d614826440658090310b14180c03a2880e04800915100000110100481c1442403c0e23545903000290b56800c501010b094803110703484940101d107140291a442c29003030345500040c403081a004a00d0b54056400c000248415a071004070641d080c21442800a002401541c00038007004118009960800740c001c002514180c2500d0020703003901c0e4014041900000d00d141400c201c4000560300d02c00000c040c8540d4180308509400003045a411071040031001c00041e07000031000c0c1307202402c9074050040548110b40301c0d03480b0312006003030309012103605003d80040c0f18109040c43d0008103603400c083d0701da9034846180e800d0030790807091041c4010302904554820302d4041038100b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 77710343 1250 77709093 77709113
    0x9080c030a0909050a021305120307290f01120303050c090d06060e0105150306100c0203190203100603050d0e030f0a050c09060609030a08070f1a0a0608030901050403060f09 76
    0x15070035070320202210b04202811040361006007608203102d1041140ba00b4142c00300b059042101d00894802c3c10402c458800359003180b00d0088024406400d100c8543d41070820490000403640e1400d941594940e6044110003a4110a01a0181c042e041c1c84800303001078030a0b08840d511904108004d030501c00c0e00d9020030300014020000302c0e8083c0d2104424040c6080101404e40105030803140c540640c00d42d40b0b40c01c031007484051310090040740d13180c0f103c0c56034600075100d044240d68050f0407078100e0550000100076030180031808a01c617010b81700400345440306a01030031060300e03003100c00303004001c0a908003529200d041c0d51201e40c050246003003020601c0014070001150b90f0141e4094a101204d103010031aa00f500104454441d0605011803085920001104696158014075550340e0300c4590038580151310030204014100711511204149200760110818061030a02030180112901d501036180c980c001c0c4045140003a005000c1000400c21a81001c00c03035001c009030000e4412004c0d03c43d1081a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 77711593 1250 77710343 77710357
    0xb0a0b090406020c06090309100503090c0909060907090228090513150504020a08160903080a1e03090302120904090605090102071a010806060d020f03010e01051609080604020409080c03 81
    0xe25404106542c44c08002e1004c90340c4036041c0070182d8506400390000622142120b0b400c0400c00c0300100009401074000c0004120035040200184da203403502c480b0060761107100f00c5010200c0c0c003401c2800a42c508082c000c0e55110800c540310416040032400c84840c00d504002841d2040003079110000840341c48841505200b260200008620b100350343c1ca070314000d80040d9024502441c410410f141c0b44a900084079900407010b070419410140380b9000448070b80400d600042d008010028040840c00d4104c9040c501008001141d41403800ca0341c0f405078100e0b07a080c00090090703001805c030140e01309005002806ca80b94020800034142c00c02d81c4501c0c007203c1049441202582d400245001445030401c04651000c3c0070100305d4002d0340c14000003940314100504468010f007040b425001c1155030309580c500030000054003c0101c4d049995146010348019a0040314180d000718000909500c076905140c180c0b40c042c0002c0a03643c4466090000920ba8003605480c40c0740e05111401c41c22800784010014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 77712843 1250 77711593 77711603
    0xf060834030b01091d16020708070b0304060f050f041202100e07050316061b02060d0c080a0509070509041b030b0c0306180603061302011404030c03061109030a0b0a0b0904 75
    0x20240c5001c00034020011681208104403089000702d030000321071079880c0c1d6202100c6c10b6001300450501405a01c0c1200a800c0312482d070044000108284d840c05000d10300ca03a0142e84240310403020f04903800c045500c10b4440c0300c0340824080024002c1034040c0d1202c028485284100d500e01e83e9002c5800707080399080c0d40240c5d196002510104a04d00c2d003040b0b10825140100d4030100c0c03080c9401c1024111000020768039404c0f0509001850542d0f031020107403500750322820000d1006112003200204054012580c40480302c3c46c180124401100024010007542c5010341400050b03140c81d15030100d15051034904100444a030240400081c440e004194010ba50507440140c8906201041010074400c0e00c6144d03048410410400815545c001006034004111b11a21a038075500c900048800c40e05030b401d00c1c98050400034001007003000c0703010560300b107074011501040001d0200801e030307809208002010341d059000c0c003081c1c40820480c00030701d60803a044040001c0d0800c1c0e11004111a120101c8050310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 77714093 1250 77712843 77712851
    0x4050a09021309140a050919080a03050a02130b09040204050301020a11060a02090a0605091f09030302151017010902090106050d0c0804081b0316080a02070f06083403 73
    0x41100c080c90151014160015080c0440048040e113000a42070003042044403a46034004500c400105014505403da0300502071401901581406c41d2181c2c002150000080d2401c00094541c070b9040c400d8a9958240420f03200250345443d00210064001c22030381684140e080000049030344c0c09100600400d811134076404407240b10707944050300740f02c0e00604100384140100f0403806140d1311440e60205450482c10329549415400004c650b040b1074a41d54082040700c9001d05900c000c4e0400c0c11101164466400c0304e010201c000718001c0d80700c8082e00c40941500d41c2440610110034a81c03549142d03869160b000086807c80c2d41c0005044400c02c0c1c1c03024002c124001403178041d1210314081e034400d544c6941814280c604041d911602a80700340d540e030720305850003d24110060541403007101d5650760030701014a518811824440e40d154803014803480980b080c5040007a1500320500480111581500c4a01c21a41d5500304640b080039110003503106414150070f07403682c1461185183c204600c50781d400007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 77715343 1250 77714093 77714107
    0x504050709090c0501050307030b03060103030206160203250f061107030e0301050615030c0702030f0c19060f030c120c0806090603010b030a02041d0708030a090e0103020607140304050a0902 83
    0x1800c204054000510050030807842c41d01045569100c101120820b2a1461b41ca6840000c201c00034100010016410b00640c40004107041d0700140700c074003a43c0c00032003a2208100100044c0e071b0b00d124018080c0b0400c43c2c902c1e101c0d65004461000407242c0c500440f940d21244a030703079550500b1075030b000c9041e980d0010042010001d01d079204800091a24040d40200140c0c1042000203405000405100044d02e00001c0003c41c1c050a0605031118141d01400300e071854072809201c2901c502080360000e00071102c0031001c918050550401b40c7c03c03505142c8603171514001c88403045003d08010111a81880799100850900c0307025445043c3c81042c0740d660b020194100001040ba01090103418a031190381090f44c014141e0381c021804000d015412240000c7c00c803d400401868030401041d002c56a01900d02d0020743c041000c4003d01e22020683c0c1c0d101207584d255030003174024a0081c0030103500103000b800991300050032a1901028500f030103003101e080c04d940700c00140340c481d0107030440b8110940102d901 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 77716593 1250 77715343 77715353
    0x302060a0501051008060d02040209030304090605090903070201090e041b060c02010212030c0a03022a0f1006030b010612060b03090d031803080f0a0f02071101110c010f030e0118060504 81
    0xa0141408481104c0404400d602c01008608050125485040c1700800d81d4119035030b6038100c0b0100c0c0c17000380560380c48507510f4249000818192180c2c1380501d0304100068065603022040b01c0b050340c1d0503140c1c01c900702e00707010710382c642200003c20407284141d02c004c61060050070755411800030440d83c0e881c903540407001e00c0021b0a016582d9040d145a0a06100b40b01419010806448014016290050310303507041c00c102c50260100b030314003680c188844803640803080314007281c800c0d085072080c011a0b03156100c0604c100100c80e02c0788005400500d0791030050003120701c10643c0746540311415201107801038455842040d0303541305903540d0030551f0020546108841d0180940580d00e02031400040030043c0d2a10040d2250000500b10600300744082c00240890880380d01a0b18407180c40700c01152140d002d8500601070300c0e4081002130200d041c24001000044000400103c05501a5213082c4019101394041d80036268a0703400d01815500e07140c41009030032001400c80e00f21406000040b402e41010b01b00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 77717843 1250 77716593 77716601
    0x903110105090c0f0103060504050a150803070c0905090a050f07090e01020301050d06020903031207050d0b121002180d0501090c0b031501050d060306051014060a0c0b061503040302060a 81
    0x4000480d074140000c11a1019002c529095060000e03110198041411401200240620381202c0c4d4080c0c80d0005000071841c265100c44404507662040c03035075081c0c8030580c141d92405019070007031106a0940e010301900d101500070316002601441210700d0310701e81c2d684550030300400790150201c0b0341c0300030001c00005d00703a07029600140c190040210325550610010401c09003c841015100940010340200c1c0d03502c041013107401025403608101d41604041c0002002a4003000d1001203027810204a0104d41c6071003801c601c50690805d0003400e4642031303c4030082c01f0350000c0310309919100c54a40c00c280d00b602c0e24220880100c0c800d000028244400345060146902c07640c006000041c5c043c8200100c43c501c403a01d0826414090800f66150843c10f02050b01515080c0c0004001600f07180501c92003030b44518000d0142c914400c42c0c204110088000d00009002d00d03c3c1c01000600503d000c1004030300c80d1002590004130141810324441c0d48801002015801580c0843c016400b40342040318819941c45 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 77719093 1250 77717843 77717867
    0x9060e060709030209011502031e0c070914070c02060405040608010e0601060810030b150409030c060c0e06040e0a09050f06090706260a0605030d0905010810080307150207150903 78
    0xa01c605142c1c03e64020441060707050141c0c00002d05415109803484c0c0c000c000361240342c040d02100724142d041c0b05c000c488990300a030b100c00f10075100d860710108040c0900c1c0a465041c045145041d60581d44040f0101c4031004d91000c142d030008410040070032941c44030702400000c2c01401f000401c42402071003c880c80d040d8141d10100030000010b0a0000000a8418203002c50750000b00b2465151a006000c562807400040280e82c0507180061800401d604400150121802040708002d0404944403d80702d1880e0f00c020a40e03c841c082100b84012080840c1468000b00d48000010b0312030300680e9001d15103c3ca10159080740c0d4403110402241a40804c00032001d0701c40307450700d810141c0800401c0b81c020208201d000002c00b0300f040008a8400ca0b9070f10031801810020b00702d82441240c000041c2c0741405600605000440300030004004500040713071390b81151814001035180c04415103940300840328140325245015000c02c0241c01080080391100d400c030340f01000025032540c6a180142034021411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 77720343 1250 77719093 77719097
    0x10603020109030210050408011407020d0e010926010504030507170f090d031e03020406030b0108042d0b042d050a02120a0c0b040608010503030705030405040b0d050109060e0607 78
    0x4041840141da0142102e030490358181e420b14554824810705603120f0250760040220340d8a400151082c0a6000e0a0540100b0701754003031320760600d681d94003107500317214481a180c082005410704100c0b2801038040d01051004e042601c141c00f400045180b030030350360140da0a4000840103c0c02a041c0700e0654003000320300380030202c1e091070000d00d86002c0610340200f0642034824526003200c14145030154041c40e180722250f400c002d04555030160040c00a40150182c10006441c0c0784c640441940160702160056401c00440b201c82c1001c0100c104032081c4100e1b1900c04110600d180320300042c20300d001c843c000c9100f034000c0d00c8210000b40018840302c03101158800c10a14260b250000b1a1020800d41509038054804209940d18286414901446224002c080036000000018114191006001070b030b1090b507a1401940d03070301d60406580340a5004068600d8000b08020003091074150702c1070302050303c003618881180f006511014212003492800f07a07021a20b174100301c0704a200901c6001d501142c54 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 77721593 1250 77720343 77720351
    0xd0213080606030706091206020f0c0303090a150b01050417120a0903050607050301030f1205040b0a050c0c220c0c02040e0d03050f091005040f14150106050a0e04020d0605030d03150801 81
    0x4c80d81d05a501c260401012300002c3d40014140142c8441c08201e0b9410300c103810850359281421210b545d9188170482d0152080f03a882d15502d001c805541c09003228100e01699024181424006800000712085010a08a02c11490080201d507000800f030404020b260300c1d58070b02c480c80e43c20140e0401200402c0b08042120810050000804100c007200215400410240c2c58100424080d9034521454204850310758010900568880e80035004100c40250901501c2546050384240102d0070444141e6420710005aa018200b842440e400300360f406805207001117001800d500420112501c881801e00540c00c2030ba81c8522143e014051590010701d200181c017414178214556940700c403102d04005401c3c0341c0322008201480f00e0707000819102034004d10090901c2a4076004299115410030b200110645080000158140204d003600e04400c480e0311011400003409003004029404081e50b0102c0654955000c0340c6500e080007401c2c0000c07446e440001c0c11342e6190b030b04210003034081d500c480c10b10383c14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 77722843 1250 77721593 77721599
    0x106050910030b0406030c0f14030607080f041a0717240103020703180f06020f011112070c060507020c030c030a050307060504020d0f050d140712050d021308060603070609 75
    0x8240080480702000e1a001441007440700009024020590014002079020800401d04440540172081100c000781c0c1074135040841d0105040d114001110500082030458000800c41d1701e128400079403007413184000c0314001641c84011919448180c3d1680300180d0156420a008030041d90050340282c151507050b10340030811004e03800d41c0d04050783c0c01810540c01048440c10107001e4071115401d0342000401c981815110700c0340d484280c045200d0719006219081074401401811b00c41c00c801000c6815116240c602204410342c01404046c10810412a42240420105901c3c1c442e02d4003406980c1c2c05050800e00b65800c162500001c1d08109100b5005040c8034000207200108540b80d41d6484100459903546900015512803ca01c40c040d1100d00e003c9034800c1000008601801443e04546440c1074545140c8012031a078000d03541d0050002c841400a03103d104d001c0c0d005046210890170001d1b181030034101000c54005001c2e40040d8681d840030b000d01c03c04d4941408910090304242c5800c4c5880d42c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 77724093 1250 77722843 77722849
    0xb04090b01090602010e120a090909060b0103150605042601021b0705030c01080103060f020c030408010603020301050a090809010c021c050606090105040c021b010c06060602031b0111071103150106020d0801060509 93
    0x14103c26616101c40700260480008e800340250344000c0a0421040140c1e03c114205980035054002c85c070313800607141c154540c002001f480c8040099a5041d96000d04040c10700e4102000e01e41e803140a01b15224010384c0741c0b041c2c0d40c400d0005140301c1c860006040310500a074480c0030701e4403401c1d800c0503220307810600703980105903440404581141d82100700403541d01c84c2c460919001f4440c0c078555140394000054040f404540540008084910940c020040c50382c80703104c04422540e004000500c900340402069811390f10800d40d2030315450006152654102406806014868148804503044c2c2c200204102242c80c0c14a12640103040c16282071185541480c002500c803c802c00c6030344100860003c0c1c008943c0d00c82c030450021541d1020341041140d03222440130395660041100c0d5920303051540c0a8108884040c010440320012034016036003407070150340e60103034481d900810140d050710903031582c00b43d84c84841154500030100340d00980b80c1e4901895004101c40c1c4160404400c0c04403c10040380c00751 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 77725343 1250 77724093 77724103
    0x9071d0619030203130203060f04120206071e0228020f09070503070c0c030204050a020319140613110a080601020607030203011211040e0709060f17060403030b0a0b04090b01090602010e 81
    0x141280ca80113aa03960b445080001c8200c0c0030724080c1d0588a0902003241540d5082c020a01036405092010f020301b104403000c0b41c5c0c56004560030320000c0c0c44a9000c00d900c0480c02c0d800340200c480ca005a9820102c001d2913900036403c0c1a143c04064162130300400c056044c00030001c1c6c0c0f1424103823081a1103180000018202c1c0c0f2001d0040c1003000010b4501406000820f5880405558006c000740800d051009104c4040d407c2520404021508071240000110152003880e961740707041115000c00741d40728000c04c40003500d00c035011003030f241d21855001c1d40a42824001c1400810a07142d03805a400c00e000024178080e0f005089c1014544100014401d42c802c900e07a40d071901340d000400818100418000c2005880440b0003038030644071b401c0004c07070200025044401a0760000d80145070107542d5017010800c01840d8426032545400040119011038800d802000e030316000070b802d0f500c01d02c3d518944002e480c1e00551060601665a0281c2030310303583d000e04010010300d0248001e100c01821090b40369154 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 77726593 1250 77725343 77725387
    0x3040506041a07080304030201050a0e150c0a05040308070606031a010f03060209060d020307031406010f050d0207050304050d0303020306010318031d03010f09050319080910020a03060509071d06 85
    0x504046802c1d5034044010030846622540c80b0010b29101e00b81031501078040e0009482c0c8600060070f281c0940103130000020300805c0347d04c0c0700c1d0404a168450711100351860340a80f21131401c0207010803000c03001c600030400410002c1d1082c1e200085040c514100042c0003494503000383c405250500040240d07080340080c80702529041400180d0310001c0307600003411881603121600307480340044100502140c15602c10380714000740200180055403000c0044582406008140340480c4c0c0c14080080702021702e5025011051143c4202e0380303029110800101c1c1007560500440000c1c0e00041000400e590500500150001d121031000e61540d00341c0d0040c105414015903642a0840c0e0b0030395480e01c1d64250009240c8410850b41040707100e503141411a165403280e45008584105041c1c502900c1d0f200308000c0740301b000004041d02d40b82d40119026000380d0312031801c6404168540c1008a406e81d0b803000c40c80e0140c01a0b864000d01001c02500c010701c044800302880703104050600c03c00e40210f481005400c24 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 77727843 1250 77726593 77726609
    0x406050a0e031e010f060b0c0312060607020303070c080d020a0807241b021e060105010f020a0b010b07150504170c0a08070b07091e050103051909080901030e0304050604 74
    0x8102060380101c2c0c40c0100c030712203d901050780102c018840d1541075003c041c4100b01e50f881801420307221401700d1503030700c540000003400758420080307024103540c691132958212100405440c45e152090300001d103150032111007610f120620784070070485a2000c100c80c0c00c2d02c01450001c1e221107000c980321181d040c0214103014099000398810281042c841031501c040600ca05042040003c0c02d00011840503030034100224054880c5190302d030030500ca201d0000040d032840d00018030644e070a14004560f64000002110150300c5540c845000040101c60268040e180300c05000f41c5900c40b80c140841d242c100907041c40c0510f440c120502000c00d694140c0080840b0030151150f0740c03222510b12041c900300201d4405401c041001c14039200304980845142d00034886583c0f11140c40d6102c00c01c003030074030300c400c5002005402c0490082040c1d501a07040f0680c000164603040101200c6501480240c58a648003150046070001d040c800c59038141c0300d58111030724003400460a2a082c01d02040303581c4124014140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 77729093 1250 77727843 77727857
    0x90606010c1101121406040c05040e06100c050102030f061003090506280509060106090b03093a020f01060f050901050f0303190c06050708131b0b070c0306110406050a 73
    0x21140d000713401d803031003501529104000c00fa008240c1c82100003003d45515120341d040526010784584113a05450507914041d481c0f881c1501c41004010102c5641c0c1444400e1024160522011400a1002d03620510412145860034580001008a00d0380b04481c0c0c081414a840400d40120701c2c0010481e51090a01010348600340c464071802c0314501c0403030034001880b800d00007004800030000c80c17000c4c100d80742c40d101d2102054544412400700d00040301c507102164800001000001c81e00d000010b0754030303100b9004403852105503240e449400c00000b50540135a108000004059101340701c1e20b00140302d8416005215410600000c64a01045c03103401d00c00c0941c1c01e01c11100b56410701c11600300c0b8806901c0d003001c0c0c0400b0a805040320ba500340041c0d891364640b80c0007825403401040c841340b1440c40c0485458914450350b80314001020042e0600c09090400d010200d44900800010300800b0b0152030314200c0d80c0d14510b4181f060f14051003140101c1c6000784010464907401c10207803185a8024100740d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 77730343 1250 77729093 77729123
    0x90611030910020c032b05070f030e04020f0301080a030f0201230603070b0406020d020d090303080c160507080a050610030f030f02010b030106090e010f0504030e130902030d020312090606010c 84
    0x92404030030006135a41341c054000d080590440818010070403122804204101e01040c940588031401400409006011040741c0c100c0020300c90015446044c4006000601709a44039046800542091b08640c2c0564400d070310400c24190003070f21244103440a88002d115060344002d42040007034501010b010800d40010220f00c40780e50a0103420003030b1624600c4181c0b1540c3c0ca62000b507554880c05015009401070341d000003141c62243d2045000e598054807a001281c4813250806c1c140e9100201860b15400481c401c640080c1080c401e1000411003c001025081010300b000d07410103001070504001c0401c07001040000540c04500005800c0c3c140c106013042c2414444241d0142202e940d40e075a0651034034502041080440d40880041d0017040c00800c0070341004032200080364015a030240201c1d00101515000f440c18500d42d44480140f2100407031840c1d0305030b0210745000a1000404050380001c80c2072142007031110030641d40300306810010480c90401c0000a440400d03092400342070101100100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 77731593 1250 77730343 77730347
    0x152904050f060702120a0308010f0803120402060909040b0601030f02090f0d030504080a29071d0a090212060315010e070309020d020909070612020703120b0d0f06050106090611030910 80
    0x501c3c0115000b410f0003e10b034641c21705c21516907520103000c0740402c08040c00894250000c284000507900140c000718074042084029035891840200100d034000010068010561603011413107008074443c0d40643c80b0760030100300160581d0000718030814454810b11290000d96140a030581c10560141c1d0303190505513017410112401d00c1203030092a03d03403094455000401c4104842610b410100c0c040418032001d00c04680c3c00d608400f0b903292000100d44000300c1c41c84140711441c0800101d0010310b881c428594805500003030360025180d081c081c00020040102d28203051204402403107110031003040d20340c10043c40c1d5420b80b00140ca03020802d41d0720000e0300219110800c02d80325072034000303040002a25181160310399843d524002c0074005203010845054405c038600030340d4200c0b40d15442e41d41e40289800078000050480c54210365204202220320004145039030f9540c06054024040801e05604051001e4039841d515072245003040100007075046080404070079121010b10845803c44015182501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 77732843 1250 77731593 77731597
    0x30a0b030d1101150e04150608160305010b01050708041e0302041a01020c09071b06141e100b040b070201090504050c1b0606010c0312020d152904050f06 67
    0x82a0184105911801465081440c0d03520601900009010051141c0c07581503c000b40752042101d00031854000c20f00240440191219040a0060000d851b99032280ea6500c1c140c100711641c84140044001071060003403c1c014250008800c1c206585051460740d66800d05210300e00c00c40113800074149018840081920740030000b55002002072003601c0d03481503540030710300c01c91b800240035102c1d546a4a03018140f40b1101c80c4901d8580c1c803074540d520152151403644201c02281107030000d40d02c074000b01035400c4a01c00c1038000c1c64058403d01903070400314004040c044001c3c1c08442c1300074411074100034a40d00003003290240c1d80741c2c1e10303511f0702c414140c0300588048985130403d0380c0c030600f09001c0086200e40280030702800402000d41800185480c0310041c0c032010259810f40c00034130081c0b98900072900840f901034051000843c0149004600f01d601402c44240241c0c5005022480d1800c210900d1204484599501501c1d2504d850b0202c882e50048140308500c01c07103000f00c45104104c10350b5628042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 77734093 1250 77732843 77732861
    0x30c070f06060b1210030816050a0b0c03060306070512010b0d140a0b03070501050f0909071b050604030807020606030c01080a020409060902030103060c050c0307030c140f0f010606030e03040506030a 87
    0x4140560b98403001068801d8001444401c064a000b9000038400050200000100c0b5000303030300285030050f00c050780c20700c1e103007000b01c1550355100b6051400c2c00100014140703031060948400b856242c0c2000c604060901034082e0050f070070400180301300700e0081c24a41d54107044405000405a5035400c0c0000c600c049e01d0039840200e01c2011035000c0143c10340c1e560300800301490040f001c0d00c4049840e500151100e02801da1600f00b001824401c0210500301040384c582c10201d07a00301001c884a402a503000b26a0b459001140c1a800079002d2008068120020540144060014018610700080801c1d070384c40c081107405040061810105e40d14040b41e5044401070203030f0081c14040300e500d0381c0c2e510713000c0d41c130a01c4102e4005280c01c41d40500c842c801c00580c0d403e85082da001c0c514115403a20204ca2508401900707940c070403c01d00c1841c80d1508c0c104811400c0b8440c42002d4444940d164045a0841d40154403000c14036007172011720b420405010007102e0075128101d0321a9103c1d00c414a101000b13024101c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 77735343 1250 77734093 77734103
    0x50f010e0708070c050f0607020d02163003030b03011a060d0c030e0a0f02030601050306040c09050907152003040b0d1a030d05070605061906031d07060c0201020f03030c030c070f 78
    0x1004245030546c004c18045d11680c1c068085400040c51184226030764682c01040540c4440d8140052040c0c61241801d42c000020030009403179400e40d103011381001d030162700302c00710082981d401d040f03401070400707009201d0090030b0490080e410303100f00c501050041c421446950011030356030640f01000c5009a002d03a52030729a2208031040304101c3c0c5810340c48149003400a901ca403207030000004480c900003c1081c4a83d50001c100200145072942620140c00064411045030180e118041010b2074400d5015500b0400760342c84200d0302240359201c502040f5155030b0100d103904200414000384240c00111603401d580000c0000300e5541c0340c5204019004442c003503541c58002c05040078025503210000c2d001707090050318100b007a500c6481c00c00102003e649107225205060036000c001d0140039602404910059106083c92203c15070311040c01c002480d0407010108071051907071010b41d681003100c800000c20f0b44005610f50b042040c0701c603600b80001803080880d00740002d540cbd02000382084140340142d80c80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 77736593 1250 77735343 77735353
    0x3080609060307080f160801020a0534380c070201030b03030301090c0207080102040609061d0901080313230f0102030c01060305030306041a01080610050408060f0901050f010e0708070c05 82
    0xc04443d580319201c03d07254400040c6001004207030246e06200326404038a403901c9007460f204040000751101409034618843c1d91506140f000710070769070f8032400d90542e37128a40403028412000c81075030751202c0c00e2000941c00780104000102d000071031130520740c0000260710b9042e02c5d00d49620040307000c2d01c000400c1da6098000031000013002046c2d0b4000d80380013883d503000e4807840c5403545101c82c00c0303001d0351141000044001d00c0412207203000d014580d5400c0d40050140c0c00640c0b108000c60700d84c00081c1d01c41e8505500028100c0d401901141640c4041c1a4a100200c2813049003a900101c4000480126109215003040e2522680c020000c95030f621000c031000780255507603810701d5a1660011904c0070300460030315074155a84a860030000e654820141c4984010751151400e204648146091050500c030302003001040304001004803070301c04c003041d0b04510341c1e61519159203400d40301c01420700e91198011000503c46541c8030445540d00000d181b42410060351032030300c110799900c0300f044058414010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 77737843 1250 77736593 77736613
    0x12051b070605040501060806130b18031813110403061503050a030206010503060c09090a111605070311010e060a030e16060c110a0602070b070204090209090604110d0308060906030708 80
    0x2c1d0401c80c03042e40100000c010451b41e902009031a5042110b0400544600c802d600c00045c50300d4402540020b22032807141684a240900589180d000505000b0b02480c401c090b82030030701d4051016001d0faa06103d003404808118803018080380610300006164980343c80482c4481c1507900800c000030f507000030032542d01c0c441030b0034060b49594084c003805020f4040c010004010076110011165203103005888500c0c60350300c0054480041480801c0401c01407410003805000a0300c440102212900440180c040240b540c5080b0044661140125050000c1c2207030204807030f40c4550603503440c4417060501040c018601141a07041030300380d207161042c2e218a8000400c035a540898441e40081c4150064502d5407003440c100314200c14244038090050b881600240f001550510203050320b144040d0000c195214260f00085114200703e40640310b5a104900f00030a0180b400b01d030a944550640c0c1d146c600384144d80300202100d0000341494080c2d85110b000c20502c4e182040414020301d92117003a22000d40b8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 77739093 1250 77737843 77737853
    0x20d0b0301050f180307080d0905010603120f0801050f030a02011404030b010b0a0e01020c03030a0c050c060d150603022d07050706080a0e011503170d020c01060306140712051b07 78
    0xf4044d61840407803c10825644410480001160034442c1c1114850303040c1411030925001816070004100c0303e654139000000700003918551800b039107138140e449035000844541c10040c1a00d105a004a00c5105e40300451880c44d240030134070322452602842c0c62440c880b80b1003060380161059a00052480240c3c1c80005054180c0f84c0c040c181070a0140d4038600600101c4004903aa0712142c040a50316410400025a070b079030007003107081d5815124500f40c48082e41c01d00d000480c25009400b1105500f51107094040e0400c03101000300d00035140303500b01103003081ca002c084180d2006020f100c801006d03900c99102d08508402c03209031051564040112071480307803604002001183d0543d85600c43c681030800817800448103010310140c5071800d444030b5421516603100d07041c5101c00c0c81041c101003c0c04200900040100d40010302d2540c81c484000b007a4140341d450210201c55140404504601e001c0741481140c991254106010004100c00428203072600c1440074540c0c120100350081050780000d050342044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 77740343 1250 77739093 77739121
    0xa050408100b100c02220b190603140405060121020607110f04060305063c010f0501050a050901080c041d01090e0a0b071101060f180e030f040603020d0b030105 70
    0x1c030182e40030450114000016103240004910086d8041004050f805070b61340d541148410f503000040700407070440340c40c0c008159041d9965a1210005440c10028400c40da0103014114a40c202c03103100d441c0b90700d416140d00d0348544041c043d210f0341760758444d0300e03d042c10440144500915002041d403a603460003440d1000705038042070889405101045200c51203450988036180403603800c8000340040e40c1c1c5100075596800c140c148855655503000950b1000216041d48401c107440864040070015410090581c03402103142c0c0c062810041c00704422180302c1d910800341d41c03120000f030820201c6a100c071418040c0c68000e9030010329000c2c1d40c0c0d4444490030f84200e12018100c8804140c00c1104505a800203500e0b1401101c015041420a0001c605c0c100d10403c009a0182e1100300001000d90321a01e038024950400ea0180f107996038410b00d000814034103442071003101c0b1201001580342c805541d000300c84a002d24440c240900d503002c1900580e0380e100c1c1d0429081188020003c2007a8540414031003100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 77741593 1250 77740343 77740361
    0x60609030818210f06160e0f04020d0227090705040611070b1306080c070302060c03040c050409080714070602190515090d02070906060503040b0606190203091305010513020a05040810 80
    0x391051802054500c2c0c840b01b040e00b115509940d440c07001d081036000b809005144403418540043d400c10142507007411610280200c0180111200134100106a04448800d41180b43d617101b516440e0504c444260050101e40488410382030413031001408030001400d018041e40305990119000840710140081c2c4c2e40c0b003405403413094441c80700301d4503a107013000064010080f0003400342c0d000201184401c0c42d24005194090f01c2501646c07840c6468038045070a803403259404035880140421047d00704a40190303e490482141c40081151510b08503009544041020700b00b001c051441c0d4504c030a004091004100130401c038002851039080c01414240d0b1000c0c64181075005000e5940d005c100100705006400485805907103890035610b407600ca54400c7d2710f002d00002c0c1e11460801441e06981190841050300700d08540195483e00125001d102c00c1e403680c0d40c4603c450518140040c040c40c2e0394082c0c038504400c400400141c5890b10600e090316144600e40101070cc074400e0b1003440300c0d80d052a410540d01e13 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 77742843 1250 77741593 77741623
    0x4050c030105010f17011a13080709050c1606050621070e010e0c090108130210090302090c090310090303020c070f05030d08060d02010c0204060f03140106060903081821 74
    0x22850038400440300300c1c8005c00c130301504034081d1004000710380a0b03030441c4c00d442142c4844545000400368004000138080c0e0b004e00b82c503410010003001400001e104142d0f02200d030440e954a8580700056070280142060002064a80d860000c0780050300c4030714101e842241140d114000039185109010780e55010361040c80b4844103d90001700e0401203440c103040c0611006040b0a040480240c015580c5100003481266205502002c1001507510840080e0310283c280c2c441c592003504600610078000d8001300f0f0645005000c1102e070700c01d6280062140c007203141000000415402030f180c206e001c4c0c07054141e16440d42c4642c40d00460002c1101d0241340c22100f0440445c1e103031407400542543e07800d500302c036041d900040c08001c200155000d442a1000c4030310041000030415210710039900300c00c15503001038844000308034805180c03560910440d00940010709209181074550f44d594100c0d842121400c400c210b4000c2a410740b207440740318045034071070030243d429400340e4000d5088540e190148d88079008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 77744093 1250 77742843 77742857
    0x9092001021603030c020d060c030510150c0204020f16050303220b01060503060d0503030a0207060e0a02030613141b011209080d0c0203040e160f05030106170c0904050c03010501 78
    0x1280e6000085480c202240c01070603801052031502c0545004001c1c010076600003c480c400751001134120711810142c0c10864400080c5810020700f6000740b44001c3d0813a49180c40c4451820010980108818001c10790407240540d0314680510310300d149005564454003d102410568010024040059031181d4405020750990038510240d24144503410300014140140c504014844640300d03d00965120402134a02d20312a0b4655403003620716802242c960034056404107400e0100000303405240c510f0219200202101e0713145030006a224580034180d412002700c48141e90b0b0400202d080d0b880039201c032550030780b81c8075a0180ca10031585c42622060600150462a40c05240c2080e03109000005400060321410b000c0c1c044030800007031149552100640c44140000645426035203001032042d00d000340b100c1740226080310094541c000c180c0006007800030510061100542c03010b800c6000c03104840240030742c0c0c0c50700700340100c0314425503849540041c00c00c0e040010340301038a070046040714020ba032410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 77745343 1250 77744093 77744153
    0x12080c03040c0501030c0e09040b1501020312010510140c01020a11011803110709110a02011b14090a03052e0908030a0e1204082512031101060909 64
    0x1a51510003220300401075403050350305000e194400d42c0200c200540a00300300c0310040c000f100040003003900303d800726a01710b406810003240030341a44114540740802c1c001142009862005010001e40c14064240600c02454505071810b1190300341450000d40c20211031380d513485000c003140c00303540020080000300351a0310300c801900805106044c0002c4201014110504a5940842d0709010808100c0041d100e848008a013005051103424400107900c60425941c140402019094503d4180307000700c8811000580101c080d004543c025540c4000015180e440103440001401c040c4541c01c090054410321026008502e4a9010381060490740d440c40700040301c55031074003415120000d00c010300070340040c400b05a01c1c0031150025403187c10300034140c0e105d0a4000d40c4144094105500814080d400b8140e400085058045007440b050b40e885c0c0601c5182d030504649005800041c4002410444026255025024294440005082074500030700c020340503810850341c5040b180030b06207042c0c01440104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 77746593 1250 77745343 77745361
    0xc0103050709060e0108040201030b150403020f010e010206040312060e010e041506181505041e0b03070308030c03091c030c021014040b090a050613061a0303190e0d1208 74
    0x64030458155550704c03038120400c4801119031802c007034402c80c1855150400380540b0395403000040f4520704498101c40e100c0c2d24500401c00c4004019070307014140122079001500c640d0b80031908650003501400c00340001013007852000024400ca912403040c440c0f03044008285da200114405000300d0080c11003019100c81d00d800101128010b2055441c040d521140c0c070030070b20030540c110300c0c0d41000c079489050402c0ea45a02003401c1d194005492041a0519095079031710344110b05c070301002903070300b64010f10301542150342e0943c1600c406004815102004800146458030422255148032510071060341d4401e10417030040c000d030604025002c090300840c10b101503074030380d1b0340b049104141d040405503446072215101c42003d034030040d01c11415801150801004120300300806800351035001d04809404600e41072101c11601c01050200844084460b465429580002503602a0440030400d02000b42000d0040d240c1b00500100141c00c0f041250182050114003a502c5049407101c0d250341078155a01814 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 77747843 1250 77746593 77746607
    0xa0617010e0c01030e07080a030302040501110a050304050603040807020a03030503060a0e0903030411151201090e0319050a0207050a030f140a0f06020d0b090906061017061e0d050c01030507 83
    0x1640e4140c2c081d11082d4450344c80703504001c080c17111850540d12019240c0042d503003031401400b0281d02080d00013230700300a0f95a2007810800c000b291003024125001d029514951240f10320301c00c00303216070340c0800444c0034400c030303a0200c0c0e008507402040c2015031560703890003400036007088035030601c80c0009220010b41039810002540c4070b051a58059855607841c0e55a0250044055a0b40358000c60301e08071141031021054000e000e400c200340d08141d4150300d411081003c0e1481a0f070346190640042c0a140c000c40d5071f9400080c80a4042e0514079161b100505089203000c1d540d40c003059000000600000a01038100700206a00d030140d680503c0c9240d410714000e0b078401300014010a41e80c040c50703501d4082401507003e014507111050000c9000e00030140003a55082060320a000e003074118209101e010710304588042881c4000307003400c540480290311516000d030001890f050181c042d84103462100c0154100758141007000030700c001000541810100d42e14502e41c0f4440307010a15140114034440d01440e8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 77749093 1250 77747843 77747861
    0x30b0d03140a0519050408070605160b0a0b03010c032913230103080903100b01050f0306060405060a09060305010506190f02070302031014060402040f0e090a020402030a061701 77
    0x71611807006015070030440c0c0390b100b1802002041801d00c801c601d1320340c040001c01c1c181c1d45155140b41d100c50030107941c1402c16450354410010701c00100b0606241aa501010030600b0707800c5a1960380030340c0c98040300006016240c1103540c3c1946071070180320b5650303011f42c481403035100594541c00344000302d07900e2000c644161000180d4001030803a100000c0c001c0581115407604c2d080034046c54180810601030503288802e800880c0c441d40c020a4079880c41c02e08218108690420050600400f030b07000300041e1040c4103051841c006c080b030010014590f42c640381c0455004120150200c0d559045240d0011b2804095010f0308001070309050000030035203801401d803038820700c1e60b2428020000303408000f6500c0406c40f0880f10300b5030003142c00c000302580d01070101c10828148d004001c102007014a007152011040104068402d502c140400d011002c007503d250030907200c41e813400c84000d4507031210541c0740400030b0710000c0d4080c1c0000704015000455070400001c031401d0003c038400120003001403d083c1e03440c04c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 77750343 1250 77749093 77749097
    0x105010b040b070503120f040308240103020901030e030f130905060f010e030a1401051009020408030417030f070804050f0d150b1804060605240a0c020f12010c030b0d03 74
    0x200040c08882c05240c001c2c0b01451040040b60b241110313407072180c41c050b81d0481d24444151210402c2205141e005a80c2d00e40c88180c82d40010240e01e62408945d03241103c0c200300c103040507404039108010781d00903406102c800303c07210704903915007000e1468003030640c0c801c60500005040341400003d00182030b01515008000041454280c001d074040111003c403040210554903218130030100003c52481c1c441c8218811501e000400c5c51303d0504604c1d40950901e07804808160310401081049050100a071800d440750328844110800346da0300340358510b000308816015540000600b24080010000c02441201c00075241c0840d08024041049014030b804c560240a24203078801c106a940503036807150710010002401000c2c2034003030581714510400129011540f16a40303660900c000c0c0341201002584041900102e1507400040441941358028502d940c0d09201120700700c841190385600b0340100c0b040c2d01601010b8010100a101d41c080c2c048403401d000441d01d40344089085080c03488070743c5800c98040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 77751593 1250 77750343 77750347
    0x40b1207030213020702040515030613081207031113030302070609180518010c030509011803170a0609090305130e160c1704030f03080603010c080a050a090c08030403060605030105010b 81
    0x50b020b20003c405040f02115a5a81c20070001c0300594882c8151401003c15440056510350182d050615103000944110388136015411030400041844044403041c1c002c4001413210381d226840198040c00440f034481d0813103034000c00c0042d08440c80d0020541128001e500300c9a880c1e40d90b82d401d541c215568010717010008926000d0313560303040f11034004a80040c0060b81720409400c00c1070406084907003010548002980381d00c20b100c00c4290034002d254901c0d0020304803c180c124155000303032055a04400c214036000309040005c0030004264811801404003c00c10310441c50545001449940106064400c400d00701c1c50114000d80301040d080e1080850040c0544900c01410080d90500701080c0704440d00c0c10604103a03401d10007180c000d00002e521500f80e003102c0e442c643c5009411f100000700440d00a81c5400e28014030b5582c03007001c1980280e0f00030800140ca4a40b00d0055000d006001c201424007030844030b00060051000008000b01c0740112010040e454981e41003609884007845444c00242003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 77752843 1250 77751593 77751599
    0xe01050a2303060a090507090c0e09091c09060f0207050102100b04060b04031b081c11160b0307090f0302130c051e04031103010203040b0114060408010f0b040b1207 72
    0x158111610803200c1c10001c15610303682080000c0c500031044070b40544450300c0f440c0308800c2003810805c1c000688a90700003406014810b5200a29182c10803004911074220340f80401c00588007032158222001d2032100c0400e82d680c503032402030480a090b01c0341b440011542240c1c669028400b0034000d054500507405000c9910042c2500c8001d0f2a00400e13003544140d40b0fa0b00085c44038103003c010002144154496210058265183ca401c2c018592100c1095000384400f405440c2200c04c0710b10b001c601d141802800640c41c2443c00707142c201610000c2c040404209804980140d441025501c40c0f12160340b0a050a91030b2031500c0c8044040e407100940103410142c0703141c01422035030030420b526603803072270424282480b10220300030061511292030b071402c200103030510502c28980590411004190000d41c958102596142030758a41403240e06840e980707140034a03c01c0d40d5103804490003080c80d07030003e2010440400d501e000416030020041c0c4190700e801d80807801401c0c441c034180364004501010700b0f2880c3c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 77754093 1250 77752843 77752859
    0x280801090c1e03061113080a140d080a090816030801031101140f0a0516080301031502030412030c030b0307060201050906060904120809010f050a020d0e1f02070c0510020a03090e01050a 81
    0x241ca90344040307a4410131b00000c011002c0b9860501c00503e00100101000c1200381802001000c07a1a06103016400c18010a80b0403504110400c1d041840c2100004015a0a040c80d01c0f1071f000c0c0c400a41600b40d08007400348281588560480d05072801480c4107404a0320040042d1071501e5000c0700f6800281c000d02503e07442d4200742014000e00115818032900c1c00705c006d0b01c06013041182c21004c95414001200500a202190a41280c8412040c40862650030240c554a001007458982101010b45484d5a240054820382250b00345040c09011601866116000603029100071600501c0912648c000526185001c0140d04c0c0100d800c1803441441d480c21040446001d040144000c05a42d2945a03003041d103015071103098401d410300d000040e00e81003094120340c241e460f00c2c0400810755000890a21422503c0141e1920f001004540140e84213050b24094407185a241e0140e07074000c118286419603541c0108406941034803075034a640316180c4509581e00308000a0003038039040018200d007071000c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 77755343 1250 77754093 77754101
    0x110907081902090a08070308120601020106030c050d060f060b1e1303032a0309060e31060f090209090c04150e030a0b09100c0e03030702280801090c1e0306 68
    0x8000070b05009104c985507103c1c0313441d00300c03141e108071080c1c071001440103607504043d06201d030407201c00d00c003c1c0703c0c1518603281c0da41a00d024ac01000d202d10742e4001c0750010449142d02000d88400100418090299980c06005042c1c0044e6108140c480803124180219080302084600700803403070390315140041c1980c90480e03001800e81040c540990808041100007840340c14812503561080da1800c0c00c01f03040c000014804070a0340b40182c0a82c40c1c0340c4c40440b5883d01038002007139a90500c484070750f20320002e4940c43c010705035650144820000d000804200d400541c1c006183d0711000b6102c0345903d031180048070203607100d00d2058208002800903010710380381c800e0411a1443d0b00007012075524400980720103840c01c101b56242e1415074848603045210352450300403000c1d40c03c1c40303041030500d0111300000f0039180d1140d401c0c0280718451880389545030551b441c0d420501c24120391041c0d2180c82c0c0b925100740c002c0046250039500b0441d1500d000482d0510744940c8414008e5000141e0102417450791290098 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 77756593 1250 77755343 77755357
    0x61802030910051005010e0f030703060b030c1e09060603150103020f0906120708060415120203070803030901050109050c0306010c030c062301050a1a1602010c020a03110907081902 79
    0x34010b5800d1485101c4240c01400e00940040364003040b841d1a01001600303100c400200079000b4401810410440d58000c1581d10450b900702a010400b6605000000d09022262582580c01000c110b0380c0d103411a440709a040315001309643d02461910f804081004500007150b0910f8036040f0764000c980b495209402600c800c1801c5070340e441c03c1c081c4560014809170414050000d0307490f180401c1160942d400001207400503402ea07000c0140109110000341015040e000d003000c0340120861510454504104240040ca0000c060f00d4513810401002c5001e00020b00c01c4480c0b860070308001c41c0121405a081780c0c0100c038140c448030140304050b134080c0c4141805ca40180d42242c0c0d94a4111065224071840440340501072105440710345c180010000070102a030441090301803004090b05010b0940b40449440441e181010721036518544012240e094201c2c0c002500102c401c3d500200300510401c000d10040c900b2202e01d125660365600c01c982c2c03aa401c5608240e410300e9809500300420081d4020050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 77757843 1250 77756593 77756611
    0x11a060f130b0c0a0501051b091c0f050708010b03011104260d0e04290108100305031224030705010e03010e010c0f090e16030e1c0504080d0306180203 66
    0x20310341c1e0b07030746550081e0003254418107160004032020080010030304c142a800380d502c4c201c441d0035076044084034200340190661203029510750340300c2400c06111114525071581c1e0080045d6490b01851900c01d4a0b00a584254400b075805c000504050b4a418043d8020006810400e14100b03843d001e01070155841d0000c0780f094055400c00e04020040c42405500143c94081c0c840202003200b44080c48229007110b00000440d944111120000d4490001e211184035424a0400c01507201e00c1090301020754641d000400d41c0c440014105060005d27085c101d0b20404003000d107400302c0200b4a04040c054002586c80c3c03a0b05400c540c0c81803100d50700912090f003406801400000780d1442c45c100c040e085940542801d004108409540350706941d10900321005041840707020006810040303030219108903850400f00034981c85801c010481c1c1e008110f442200c543c40180a4074015181c1c6d4040c0040d40507009403c154051078510f0703511213010303000301e600f11031800c0381e8070b0708282415481c03034000e40010b0f003980c079 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 77759093 1250 77757843 77757877
    0x9070e0a1e0e0d0e011805040902180a090311060f0109050907050a030606030c0b040b0703140d051512010c0c1401061206140604050f07031d030d020c011a060f 70
    0xd44000602c106640615036070020708041e804640e001e003891144050060400071900d041510b9001d07404000e0040314015a000f10740f461440c40020240b20080e0b03031007112090384904000d804809900070702c47e014043c0c1c0304d00c5507150280020a8450b41c0482c1d1240c144140c4800401c88000145e06c034a0f807266003002620710b00c5031a90f0018088030800c0d8000d0b02d41d15203030300301407041c45a000707401001428541c2440d441c0c90300e024142c00050040003009814050044d4000c0780702c0f40039104407044984404010080e42c82e0006400100300d440b1000540590030b02070071858490f4051154050a60003615148400c0c9119034408564a850b165466034a548815000030200308044200001d40d108980c0804d40c803480c10147c0001c1c1c100140740c1449181400280b141c40703080c0500141c5c000c0384900c0d000c0f03101420503480340b4200944800d169164031001620b030320781c0040c60740581821446070000348040390403648940c540e2142d02d00c8140c1d01000c03c01c8040d01b200344035030044c0881e01c5840c100c44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 77760343 1250 77759093 77759141
    0x130302030720030d030e0c0402040f0603020304030c0204061203080f010503250e0117011803080c1b120903010e06040206040e07110a0305070302011b230c03030a0b030609070e0a 78
    0x80d00300013001c00030101180e1203655214040809106c10401d030758040e6811418030f0318001032042c41c41250710030441450ba000004c0703818113114076030300381189801810034006155a0011680103506005041e00018008408a580d5850030b042207070484600400410110f008170b001c030050b85400900003003151220010005d45c403154200390900a08401003803406a2140c075040c81d007034074286803d180e6041c0c0130020f0940060342020149420110324040b59880780c500000b40a00f02900681d1240741d8032484181c3e07400301780803200420301c0004c20381c024048050090040390b40c07164141c41c020740c0075105000902528644100e21680109280b40621703020100b82101070600300c0d1600f05400240001502d0024581c09004e100400021300380400c030024403c28006201442c48034008d99032074082104030a0004643c2e05451404101c6c074140c980da0309041444000a10026480c14020b01942c4000ba08250b0049507420803a415500c200714246c6d5030910b03841c006e1803204404010701203882c0180f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 77761593 1250 77760343 77760349
    0xe061b120103030206010f080a031409010c0203010504230a050a020405070c0615090c080601090b0c0c040203100812030106020c01030203060a030f05010c090909020d0210030207140a0308130302030720 88
    0xc00c0c02103001c1d40142c0140c2d41440d100c009494401d41040c9600d5000c16100030001e940441c005000300c1c1c4496003142c841442c240102c848440b8036001035410b40c20032080c4020701c0405041031039454001641e10015160302d6445503154049014050202e4111041590141c1016003207254081080d14020324090b9a59840c94111500c180e003030703841000e00110a10420150b84210042090340341800c0318103283c01790000303122001b5400b8020780380801007008810105c0070400b100c1000340050096489280c14104441e0181061149001d2485203d9550115004190480e4140e0f07200e030340946280001c100041d0080e500280000f0741010070340f08000007184651301803c001c90321034400820380d4440c0c200f00810030006ca030410414603190928490050b5503c0720010b281580c1503c3e000c00807101c0d000d090380203009000c030180820751100019500c0c11b0022034101e2500b44030307480e201101c0d117410260000854100000801590081010304e011070040d42c030303070708501e9001100800605025004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 77762843 1250 77761593 77761627
    0x2090406020a1d0915060d0204180b0603010e0103030c0203030d05010b09010806040605010203070f061407020f0d180302040e011b0512010512030f0c010f090c15030e061b 75
    0x150345060380070510001441c1d10480d042040c0c4050032030488a01040340009182c07a6010300048103d00b1800802d00c066101d28080d5442c808200c1070864607182e80d030245040484048072003801d414030b07111100034140361407802e59040c4c9105101c03020140e801c65030260b910925861040e68180b1003400401c406070060301030b0070702130320450b021180ca820250002422034500504882d11550034800103028a9034000141c88520790854081c0b00b0003110340c02d150b030040151001044c00c41448000f0844a20380026500c04140c2c0030038221000c0800752041181c1d8030721020090868100d030048104003600e00354111252075030b8841d00020b42e69070003580c540250a0480303504404503c0c04243c50410550400c0700c180100700030344040950b074030340c0b0b0f503065100e10410704890b05024000c09d0500707001e03100b580442a000003e5504215000c002d05140c429036017184170792104110002d040b650114401c3c00344220007001080100300c1c54480c1c4203c943c0d80400b0f40204180500c2c01d11420a03101b1035070318 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 77764093 1250 77762843 77762851
    0xc05030a09090f090213090c120c0305100209030303070c050102270f040203130b100b030f01090e010209150d0b060301170d02030708090f0a08010504140d09050d0602160209 76
    0x48041d96207241480c1801034442c4034000b0406146019101030143e100c100401c0d81002030400002040c0f9040c1ca802d2a8881c0650132000b034031180812030000300542c42c841981901e002d0000c940d01200715450540a900c101210f04d90150000d0000c900080d006402c416003140c8504d00141c102505801c1170840c0032066440203081d004602c4210800d0700b004406958480e4064406520f0f51030b200903240380900003000014a2003005d64000303240ca409441610001e818140329159a80c144100c40311180720702809902201ca240c540c440115a005100b10b1309200c0001c2c00e9400311201300041c144641d0031640015104980319071412a240c0e46500003540030b410058400c940300340000d06414900a1000440010b40d403003003051171701040ea0300c015604903c0b0112003440b2030203260404180b51003070b01c0d8403400556003440140004c20800300394000083e8544811a83e408100d050f04942c807001d41d00c0350350b030401c1d61610040003140140d0000c00b80700b603558101401454450b4081412400112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 77765343 1250 77764093 77764097
    0x20c090c2101031b121401020403080a030f23040209190903020f0d0f140702040902120c0102120310180603050d0903060b0d021e030f07420f0c05030a 66
    0x10051080108118011500104c44450f801556003400c3c02a40b4402070f02d4806840c42c1311074882c4004c125825011034003d1548510007640b10007060b040078028040303518828000c0350030700144150001c03002038400e10b506000711003c03d60341c40742e8084c010911070180900c40140441d014003600d0305094041c1c18a09886580105a8039a5842d00e441c1400240d4440c041080030000c8000501d076404414440096921001290f641d529880003400034410006e009412aa1880a86010b800c020500d00c08001d403c2e001e4030f80c040c1e026800080b4600c4100d0340e00c1580d281001d800d0064040c01c0f10000103c03003030440d00160f1243c6035220310f4603018840c80d0160000c2c01e83d070400d10812405000c2d04103101d00a1310030744100d41050340011501548480b17440c01c0d556840c4002c004658040280512510019054805843c0c1300c015202c4180b2182030800219003081030748130304000c104407507401214030f51010560074803d00355023110108640580c001c1042031100c540b80c0464024070041092501035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 77766593 1250 77765343 77765407
    0x50403020103050906010e0402010f110a11120a0b190603170a0f0302130501050a020c090c04050f0f0f010c02060717040603050915010308130305010e0309030616020c090c 75
    0x140c0300040540d40c00801c2111180c01410042241d07069100009400c00d509003842504080c68072001c4a1400004a801105200b421441418455014807007080d24105441c600e21986c0c241d440d241e500c000701c1e18010b0001c2035100005580444c0702d14420809022140045409662500c400340212000b4101000181c2c0010704280c1d0315410800300e10001d0f0841c01c055007411982f150a41412640d80300741810701c00f0000d4900150742c400c2c415149070020061018180c0d0800c5028111141c005004c0e5a0290200052410080ca02601a000c00e2080103180150f4000d030304004442003980fa91040fa0802d06c14800e03080003c41858081ca802e000007500b5640f15403078203800500740ca00c05400e41d09680c000004503014180c2c0c00d818030b810b40f41c1000c441603559890840060981c1804e5101a04a5203061090416020702000504402c2d404604442c10394031600003007580041d044c10b54101690180144003050305014055aa01120003031500b405c11507070f080e105442c0385c28503071450741401070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 77767843 1250 77766593 77766599
    0x905040813080a08041802090603090a0506090c0a0302300f0d0504030f03030b0a0b0f270303030f041a0f0f0106080712020c0102070507120b06030c010f030902031006060504 76
    0x811030144002d2880b94003c0943e201281c0303a03201c00344218007860780c0c082100c0c24005500e03070340b50301155804031010b421140d8a181070407580d9100c0d42c076048100c426003daa804913058000c00104a107041c80014542c0346118035590170003071880065801040d082c048040008403035903079240c030702500d041805c001e0140c684603100a241013101001185040c0b000600090010849002126108a905090016101d03044a000030704800041c1d108110303030f200002d050500d903d00030307029000c001104800c00446c88400c000441002200e424280d404d640240b000030141170b80c2c90f2340c10f41c11a0103002502d0141288400c1c01341161000c555944101182c6c1e41444400f01003c0c94032030050800d8640000c583c20b0a15008111817075040d0a113036495000300d00d664500c0030079811030740d860350300a0480d40031541c0c07015064102201e40d003041c0c1d511200c0400007142424042070b86812040165243c0c5d01d26107181506030000c00b01d000d0240e816102d414035140242000c1d01c41c0d10050011a01c41684840c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 77769093 1250 77767843 77767867
    0xd1407050309070f060503060f0a0308030c040816142209060501051011030415140a0f0f0c0305090607031e030b030d030e0c120f0d120b0907020a0303021309050408 72
    0x6958000301e13910400010400450360f010055981090040312840c15468480c00022b01d055100c2d040a06800b40000900059042e240f00a2003121801c070300b03840c40c203030381202e220b0155038252003030306540c00c034080e4900c443e80780c9010021100d4221710308400b50b02018591010880c0c41025045450369030390401480702e4544000c003850800300350301d03100b8598560311160980703a0241c1d10541005620340b241027015580200c60f13480c00c0e641011003041c1ca03480c825000600440b402014140071503079138a010307280e4520580040d5070054150300d850b4603240b000420710190303500007001681082180c04070562802034181c0401554500e649d40031910040160406050000001d50b070700602d8900003101d80404404500b407004040c040b10169501381c141c1d6540d0742802d10613480d218090050703038092080e040e00246640018118240e0401c0700662131000d2040c004420344140016900003c004e0300000e110350002d00c3e00d56a040e0100501d55610b01c46482510420380d400c03a002940032614901d422 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 77770343 1250 77769093 77769103
    0x30b0c0c070b0a0912030c0204020f090319020103060506040806010b031302190302040f1404020d0203010207080a02010501060807030509031b0f07030501090b0a02030403050a030b040207140609010c030e0705060d1407050309 98
    0x2114078204000502d0b031701c1d60064040000020005c0c029070300480c2c82c000d80c2a12105803007807040054195800c3d50020000d05098100f039003012404245468000f02d46070408100782d13416100004d00403c12070b42024500080741e04000c01a210108141c1007540040e19054082a07804003880340794104030b4254810001a42e04014000c003010789486032640c4024042c440490f0841d405490f40c241c0002e0a001090181c4182c034000f07000004000340f0314808a034150f0006040b208a0b1f80c6003800c0d40c80344070048055038000e545010960384140440b01006040394400344032107080808491101002c12807440c02c2071050b92050759240d40d2400c442c0c0a0200a0703003980d03440070790010114a54074281d54003600f20f00810040404059451240c80d12540300c0e50b04072001290854102d20104500c050380c00e41d16603049030042d406500745444010400d02a0181100d0200c1d0740c8003070209207003094148190354002c40f4588002c41d440d0504141d01000d825541c500071445607035616502c1c6072502c6d10a144c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 77771593 1250 77770343 77770349
    0xc180d0f110f010c0611120408030a0c140406030c020c090a0225020a0e0a0902130e0c010801150c0201180f06020f06010509010911120a0b0f0316030b0c0c070b0a09 72
    0x3500200d80400c60341c0c0e4044c50800d50140c1c80701000680302d07110140888130703000d1140005141000c14091005100c581c40185102d500c200009100300c2a000d40103c9000e02d0041040c3e41c034080034081440f183c0d009401c5011040018030403590211903610003d00d6061043c1c0e10480b080d80d00150340303d42d000d16085600c0b040622004281c4810405074049a0141d005104541100200b840402c02d000105c2d0018580c503500140b55559081c901100c06004015844c003151079446030003400308a55020309100e03412100200101c0c4200358154030191501c1ea0b103020201c0c1002048907e410703202165038a24000740900c8400f5485040c03e040c1c0103440d01501c007006002c01d03402800100480e54411003002d0654a11807030100340c0000e4261541424007411441215802d5010304000c0c0010742a0b200a401602c210341ca00c20b126051402d15443d9420b031350380c0342542c181800c030500104101000c80758000c600003000c280b138120705100c1d01e41403012580003181c0e8018002404120f081c1c0c03040d0303040d000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 77772843 1250 77771593 77771599
    0x106030c0509030307060203101d0f06011e030b04020f0304050c18040b06100905040e010506090a060e0103080304021f0804030f0801050319031b060905010609140c180d0f11 76
    0x1400b0780010010350b0368010404000c0440b07400000203581046090201c800916401044424100c0c083c00214980c0c44112902d400021004d400500f146d07206903602c4000000f5aa0b1001c01103507a00f501305e001c1c001d2084001d401580030007008400c1111400214840d40c0294050000c03060030400b00014a0300071031540e9544550303541403001282008a0700c5800c15011521a07444114810090382c846040b54841d0b83d106103450720014100b0010741040303221300d408880840d01d40d650380c074804049507500e00601501c00c1d9180018070000b45410000c580080c00240980c181c1c0e800c12038861450043c402c403200c00182c0d6901800200341d0050780c0301c2841e403e242481c10156041c18042940c50440005902038600c002c8079880c1490b000d0032110b03010784401d60303070740f03199036010700303154019280101080303800b50700e0314400050350f0a0b00e114245c1030850754140c1c8541601c0b40c100c44411034200c0f8003c594090042e4030041010350710100c032051110302c550303840c140840c21410101e200901c22486980 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 77774093 1250 77772843 77772847
    0xd05070f080a05150402030a06020f0c010c11030f030613110c010e0613021315060914030703020f06032508070e010815010c05070807031a100b0301050909190602030106030c05 77
    0x1800104106413514441c110094840e42c42d400040d29103d0401400342145200044100c180014080280303142e203495002404031240c03408040300c502d90510004c0f1031030780050003010f020f018a00300442c4c0190005141e0390110840301c0005c000c0f40d0302c0054045184400250700400e41c070081c06811030750203580d0003030a01c924081e00300844101007c07000074420950b103929100e00c40d1040e8440443c1d2800f0604031030000340c49410150000700705000d000c0000c0d42e04602c00685150005001041e2a400f0340490030008020301032003015000985002800e4402c0e4450f407540074401c48414400b100150354040e1541031003d03001d4a250000c2d40346604202400303040098150760950804610402860b05460102c0c01d420924240700d005e03085800c10707004030b400010901c031000d60048484032580318103038800d0300e0326107490700d100320b0030712403500d54007403e000401442c6407100c102a0300c60720382e00c2515501701c0c41d030720241c521300010b02341200c010b40d0100050258070307410700c05c07002034040da1304100e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 77775343 1250 77774093 77774113
    0x4120c0f08031606020d1508100e030910091212030b030a021e032409120a0905040f09121d010528030e120406120b0112050a0204050d05070f08 63
    0x1d0b44078841c504120101c25a2051840200b00b00c030382c100d50300500c9044080200c1c03152101d5000a691942c4070300c41c0c0c64411042c0403100e1000610a400d4076050070f200a62070008000c00344000100140000c80501005102c000344011038419003600d4144980c0314a10081c03803442024003283c4c00151038a000b940000e0300c1c3d80c01a202c00840c2c40750541441401018140740c8000203251036030040010401840d100610b01ca00d4561410b0103005245901c203441c0c1c0c004150040413203e0040d80004400584071210070401da04041e484180c490341000320110300c2c9101600c0348152b194a481d80140010024450550300e05840c00034404408001d1034043d1403c4e100d00b4050f154003065007035420301d100c0d1424202c4429400780d407042810324145400d0300c0c0d1014000d68001c03a140c016204020119031a143c50290401c018840d0742800303d016103816000b4818000f12400500e401010001c280341e003004042000d03034402d003c1059451142e0000c010450402c40ca160440104e0341c03003240c180c1d114003111 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 77776593 1250 77775343 77775359
    0x150b0703030f060b0a080105090a020c060c090303040b0a08070f0e13020c0a050105070c060609052203170c0901020106140a120317131103060403080a0f0605030304120c0f 75
    0x11105140c251601286031094031036140c00400041e4001c3c0303240d0800203410480f440d00324403032034101c81d8100c5150469960b080c07005400e92082500740500c5070015030000303240007040e60281c041010050300f1a41001d4884509440b00e901c8540b40c0b03008100650100041c080c1c0c0070b82440c100e24183e1401a0051540d800885c04409440f914280480c0c0c0104070300301341030410420b522056400c81e00a2040b428004409001c03079442d204190f540c18100900070800c0340250185138000c1020f0440011888203121141d003141c1100d110840801402d065403090003004482958002d41e0080070a0b80d032413a03002c0019084807603c0c1e00402c07400c0c1e416a42d0742c1c0981c0e28503c009080399a000381800c1298402c3c0740455581c903007484c80d022a042d904060021009030800080c0502d4414170030000341120a00c2056a80c80c1304440080000d4002c2c0c0c00550300510f16009200340c2080c95a000c681c007901e45002a040d904503407c2440309400003002c11080c02141d240d0300000300042c6601c040054144a24 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 77777843 1250 77776593 77776597
    0x290906030106240215070e0a17030405010503060102010e1501050a090e0a080f190309060c080f0c0a1709030a1806090302061602040e070f0b0a020a020405040c030b0403050904150b 79
    0xe2154810321007041203c207507000380300181e04080d18009103512441c0181c03024091266a05c01d00b40200219040840d01c3c17488090854000b0348403000860078645842d0045500c0d61005045504554a4a07007141da1100204007544403c408551025090360400301848440800c0380c0c00300b0070136409d0044803c20381c400420385548140e088801c01d59114814034130720740b0502c80c3c2b6203130200080341b0607600c881180e4182e001c01030003403040c1c0f028002080550411140460192050142d40302d520020402801e401d1008081030300b030900f40000d420b01c072064404d444401c2101e10205c00d80002941c80c61240d4810303290202241d0301f41d40e04019078100f80b4007d0841815000c02400380d50009040e8154842401c0f542c10b00300c1c3d00602c28414407420098980d1120a50710801c1c01800c0d03040d1001c00c050042c8d0013610061803843c0c1c02410402915000c010203003502800940328010310f50800b1000c5540c0c0c1c0c00707141c0306500988400395a27680000901007241d1400030525442c0141c12014004000c1e0102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 77779093 1250 77777843 77777879
    0xc020a18020c07060309061a0f010c14010606020c090a0903020a06050a02040b070f020108010e011413240608090a02060d0c1e0e0a0b0c0303010605030406290906030106 74
    0x1900000c000050440500a11600445418030320901e0800a03e0944c150400e1201034410041402100c40e602003642c45200e68181d2280c1c000320b184c400001c6544a206500691401040d9901c2e04141c091059804c5038400e4000400580100c1d03855101800c1c81c1ca007003504000340c41010002c50081d03440082d210101c85030300030561910f03400071074604441030301500c011300741403046260303941c4052400e5180001420300c00c90100f0a203000000e00200c04841081c12140407548803481e11a0100c02c00443c0c0054081c843d10841d55820141400890154510206441c4c658220515401c1c50000f903d4000700400c03048595000030451401610740000b5105590a22a004039030611100c2080e140d408000e4607031418103603110b00544406900074258415420183c0d011070202c1e0f00c4404110182c403801c4110001c0380d0007040100100d0348501c0040d64040e006000000700c6814542e0328041c6d80038400c402c40b801508071400c0b8007991902110395504400210000c1240d5450901144e01e4508002c3c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 77780343 1250 77779093 77779109
    0x2030306090c07021005120f011406070807060c0305100b0705100209031c0f090e0417090316080a0209180606040b0d14100501170303010b0a0c0605250c020a 69
    0x41c082100000c000042d5000c02d94010400e080700c00790142d008041e03410518130100c00c2910140420005024612554142c03540700d240004071050400910a09a000e040211100300042040d08042013031482160603282c526a0003240d60f06010014840c10a166041840410700410112001450016040c03410030b51819015854040c1040085e003440e40141d0102105000880741d503000c16408030204001080a4441705000c5172030340c00110400c1000c96005010f49080c1c105040100c40070005010242d10081c1140c140c620305d1001460846c060364061800e581c007a103074040071490121500e51788254082c021404404450b407260340d40d600040c6c000c038004c41da02c3c1c0c40405141c50b0300403000c0100342c00c45200161381e0600004240d9505410003810300640c42c220002c28211710780031004420504260085040d0f0f400c043c81d583c4564886594881400b55540007680056082c0c00f94901c40c90345503d410525200f24403503030054140c18640c6008000304e01c92a2030044c3d0764480781c1d800b41d41c044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 77781593 1250 77780343 77780359
    0x5030f040b04020f0607060e01060611100509010b030327010302070201050d050601091203110105070806010909050601050d060608070f050c0d0c061107050607021603031202090d1b030209061002030306 88
    0x341c0045000f404100034443c0d044100011b03004240202600030f41d0541078004001c222065881300111801e5107d18404407207500440d1544410142d250070a42c2c10200704400042c0c00c0c02d40c1000130f4603552003206c01c201c030300640049011104201001d903010074802820b096240c0820f80d400280715120b4114038802c0c1c10b54450214946902c28003504000d45010140300412800c2420098505100342c0341c0c1388103560800c0d0003e04000c3c4200c2d02c1030301458060b1500745402d401c0064000207808010001410090103000300200c4000c0340c010040142181c0d1105210740c18040c5000f4541700b0015040700500c042041203003000c00000920b20000903840c9404171034410180b4003280581492954040d44000c0440d180092142c00300301d25000c0d90035a000c941c160b079120301c0d0400a0300301c035110280100d4901d01c0c0000061485800a00c4409070042c003e00c0134044030394900700e03503511241120503000b081038000e1003181041e11041c0d401c24421142400c4299102c5002950380c0b1008080900484103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 77782843 1250 77781593 77781601
    0x40201050d090804060c050c030102161511040b0c0c0108060109150c200109150206040201030e0c090108011b021612020607061103041109060f090c041a03060307050105030f040b 78
    0x101e07500c030758012035005502556a542d9900014580e21700b01d00c042c1e0350381c051205210348500d414402c0300e07158504080a250801220389601507031424245103840c503543ca900c2c2c41c440c2440c20310028000f0340035100180740c59242c40c1d014245018000b40005043c01003410621500d40e1704044190300b2140200d00e10503102002203021901c07500d007800000c0200c40c8409081074207401c88a100ca1740c03c0801e90b54000c16564a6020704c1803120020155400340c1c03c010089405035101e0b400132240040e407035044846601d106004a61039050903403080901b40d54038203144a0032640c080d2264041c4500303200400025400c50303500307115840d00b803003803280c80c1c143d541c000740841d200d01d8181c90742c0341d40010f400c11102031083c4200d4290f41c0116801c031803136806d4910440766450a0a5a24000c1c1070190084202031000000e001d0400c4018008464021080c4030018401a203031000800700743c4000d01c01501c80c02c03c3d00a1510307042c0c041c1c0110741400028010070400356020740300b0980c0903412810200141e01c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 77784093 1250 77782843 77782867
    0x10b010903021212042306040e010306180219050301050903041802180d03080a0b15030703110c250e1603180804080a0b010f0b040b0912010501080d02010e0309060304020105 76
    0x42c00d00c0c1340c051404030210700012504d20075200a5400c2d444080f00741d14038082d2200708021441180503001d8422600c030011300124483d940608504940d004260b010f40c3d1150700015100c01004040d1080019111030500035820300b03016140d005100ce0008508240c10105041000c10003540d003541040d41c04607001c541c02c17640750b2061840c9800980320603c05102c508005000c404d08640b070000840c1000b20312580c0e0b00300011205940788a40c8a0b450445d00c400c40c084000c1d080b8084540c504075420710041c466080c061098200340e8403041d10b4014210b03c5413040119080007580a07005051180d0100000c400404000032000d0707a00f454002000407040ca480c00c001c620301c40010304030341004200414006800140c0d510356030301510f80508560b90744d00c2c040c18040d00070300405620032418401000032900c11005444a400014044020140e00d03000c0a400c58209038071011241c1d0003c1c0f2106c02044d0280b01d101c818514810103113281a51720004140d0503c00584020b0410900103100c80d005a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 77785343 1250 77784093 77784103
    0x203130605100b0307020d0201050601140904020307020a0204180605060324070513060306232211030708040b0f0402010c030f12050c0301091802030714061e1b010b0109030212 77
    0x807407060502504e0341003000009541e030700080d078880050742c07070180070074825030181c030090385040003d204240c6405584c0e0184400787d00040c0140303056100c0d01144000598980c01400300e6030040601b00345448909007008025200c1c09002140250080010040d100710aa6408980c41c98094001004ca88544000301d030144515162803110350130088001c075409505130460b404a480e8401c21011a03011047c1c080c104420a10380b06601c1600344040ca16800d00107444102113281014000500c4941b807504d070007403903008940241c0050f41d003802300002c101048601da604030060080145881c43d041d03002800c0103100c0c034009010f02401000792000c0600c10701768444200c480890034003850500441d503a40ba80c04c28001c9803406030400c1e00c80c40b11500409400c1c904140c00070014407200703140140c181a0395001c0c90b182c2d030300300c1c10400800155618644503a1000c4801e0b00740142e495034818505134491101c05074502c000d17414031207580c203644e070702c04050001e89404842204180e80390030043e500d41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 77786593 1250 77785343 77785349
    0x150304020a0b0a050415020d090e0702120c06041205030103080702060304060216030c0512070804051e100807081602060412030b041401240801030f060209061209010c03020313060510 80
    0x200b0000b034501c0d2041d80035014104640240b001c10703c0d00149038805a8560b2420320b521400103000c2141004045005c549154015150780140d516800038000e00c82c01503806544120b049a200001340070030400f044620240c044100c1c5132190455040d50b641102501c0341103c040d100d000c020000c241480400d0b0f04903103a42501c02d044002800282c58081e00c81c0c120f10106070b07000c1c0205020504805038902c1119061540a649940340a04080401c0554101d0780d203019102401440114980e44406d0141c000342c400d943c45074401880c0c0f81d01c000f05503030070050451030b0700031440080204485c4c000441c0d94100f980030502c101e00c01007502e8220010105440140d6005041c260000110f02ca40c080c02c5058901500801c01040b041c2d0039020030409400c00c0c4180016400720040021480090b40104402d03c1142d001d890101c1e40c1000034170940110840301003000c184805c0c840004001d00c1174000b60300301c0781810340c00c0d4502a41031060364210540007410268944001416841d0020100000307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 77787843 1250 77786593 77786609
    0xc0b0a140301090905070e100314030f120a0f14040308070c020a140414090a021212030a0209011d010e2101050405010b030f01060b040306020d0b030a080c100209150304020a 76
    0x280e40e554188003000d0130100c182a5060701405c103005c0381103044540e04034403500e41c0c00381ca24042da14642d100c00304c8000e844030080041c0000d000a1101003612001009105440400401d450801446200072298140404000c1d03500d000654042c0d007116030241640207400d400c10351031aa990708000c0d03610407900030001350711403c031890110300d0803241c02842c081c24009940401c1040d03030400841e44503090a40da0501268400180c1e40d00515144840144082d0481c041d01d0242050010740794460700140c0b2598001900455282403559000c0310140740c0b1244904880c616101c00e100181008110b0081180528002c05860310340f070007207100224003415804001c00040c41c0c581041360013064400200ea10078010300c00c070130310144c1c01405000151244617080526003417640d51403034025807180c0314800f20661103d0120032903907011301c03201003018003c100140e91501c1400010303040c8460280003002c4c081c4180103501c0103031558464108000c026002d00c41d80c0f81c4803400000e9103074070150301c8040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 77789093 1250 77787843 77787847
    0x60307140d02030708070f0501110a060b3c030114010b03060319050106060305100806070503060a1d06010f0f020703020f0102010207021314010f060e1e0604030807050f0a0c0b0a14 79
    0x5445200180c8a0101c60510a1000f002c54a2341c0c01100c0a00000004030590340c4103804c5500800e915030301c0010703540c800a0031807259110640080501014000d81a00b05e03015005a44c0341a00400e849441040c130300b10020846c5541601f801170b00c40d60103000b4540c1c1140044002211601c0821080469200a41440502da40305140040c0601100d025401c0000c1c1001c0100b04002d1155541d8400c1e00d818002034100b564415a08452070740000300216448003820700c00203140904088071a80114403103618003e50300e00030001400c420b0702010404200030040b40c2c100741c81d66001c0383c0300d010740b507048550401000c0401c1c0100c0c0a40111440030794455000070119101d1422584104c500c1400c41c203503500103070f03a90f180c210815144c91013034102150001280f0500e030324010b01007881080d01d000c2d0001010340c40070041444ca400507001200e80280000308072040c0042040769900c20040d0100070300100c4803640d140424402d16105507802d01d440441d010f400540150602881070403440e2020b6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 77790343 1250 77789093 77789099
    0x12070801050105130902060301030b07140a03050609250c051006080f010605010206130803040f060501080f011b0e010f05040803030717330607300503060307140d020307 74
    0xe0081c0030038440c480c071a201c0c11030f0b0300d156400280220750030039400414a030b003142e107151200480c0c02c10080450003000822004610b5410300d1001034405803003540d46c0028249000c5042c444e1446003d8654510b03210920400341c03d0890b0000104401c1c041c52601c22000c0842e850031a1401d41c3c44802c1b4802941041b20109041d10001440c4650708903060082c00b20340d554a0040e40c8a4106460004400550081000c0820214002107030071900c0f0b4051010100c1440d10784404650f0f080e084802141c010b0044c1c00385442d42402400c0b00b261003030101c00003490a01c0350262002184010071814402c082031503120f50750089060303600130103840b801da951301d00c1e040b00b0081200301c90343da0700b4402081010100300c4203510001d4900c80d2120002c1c0e400c0d80c00c00ca521720402d44540d0504400e0b8007000c1044900d00003103004c2100c80c01c400c0200c3d90810030150b10b1009802c41d0301c1c0a4100001c01105200f0022280d0700000c40320221004d40a020285041c05804208a150000340203505445080000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 77791593 1250 77790343 77790359
    0x10603050a02100c031b030c06050c0a090e0f04030e0d0507180606110c01141c0203060f1503040b10171b0a0302060405040506040621021305090316021207 68
    0xa0240034803c480c071480741400c01d0403d43c3c001091300c6001e030000f0401c800208621482c0c082c000346143c080d052800d00003059603140b00c151841260086282400031440c84445501305c001607000e000d0489112034940341c10303114070105500007031001d0108000c0100c4494541c5400c0c3c50307085400d40000c1540c03c85c1e911110300000d000140800b11050510b059000100a0302c9524009811510798000e001c42c1080d400045440342c0ca20036800c003020004101804418280d80d0000d080035421003c09a00d070300d003035801c00c4001e0703002010301c070f01504441c0303070800c204204002203a81c0030743e220b80f250000d038503420703485a0550710b1900300403460111210b580da200c079070000320740074048074801140c401c0c45468401c1c00b003603402501c0000d40110042c04184000d01d06074000560002e409400040c40741d59524000d2a0300110f480025204049980e0010a43c1890700c80b030184008150b400f0b000c45d091105c01c080d44c4c6d100d80e00041440e1048280300c6400c65a40d03001c0c1098080c80b42e81201c000d0798407050742d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 77792843 1250 77791593 77791603
    0x3070602060a02030a0b060d051f080a021002120a021b040608070e100b1c0c02010b0307030b041104020f0a033b0a0203060709080106150206180f030409020c0105130c170c0301060305 80
    0x164030550001039000c201c0842c20302c40303800190bc3d000c1d0080d00208959509000007101c0910f455410350207900041d41182c60000042c05154041d540208000b40c046110161000c0c420080507000c0c1c1d0508809010080d00001d083e000c45581070310041c00c2d59200881d411041640345c005000111707000800d00340c9414030703007240351004581c80010011b04ca441d1304168201c84002c100345400d60007260302003000c200348858240c2e01c1409000d20700f550ba40020009012a03012600510980c0c0c2e002c00c5140e40d00d81e245c41804410f40941c01d81d0f6118501000400364405981c2c00d0700f5180011540300401140c1050082260041d401b400b100c1c0e0505140300c3c040e1101c0c04a005603203564bc46d0080c00514240341141c3e82584180c0c6401816094030751740000040000c20710300000302489003094a4030341070b07010002040180380b848001602e40c10b540c100076095800191526196280b000300180c00b00e481801040121010a074150111000310406e05092a150100445e03155103008000400d1100c08170f1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 77794093 1250 77792843 77792851
    0x40e1b070305070b100302092202040608070e070e0102030702120102190e1306031a07180603050a06050603190216060204030c05040e0d020309090403120509100b03070602060a02030a0b060d05 84
    0x411003100c0c0c1d45182d078102504c0b17003511002e90722003a8207001c501ea00482c3c3c90340c201041c01c801c0042c0c00c0c1000355004201990f0803a40040c0d40341e40540000c000a0400d80c040c0d13600302c216483c15807a01294440000d55a009100000e07100302c1900c0c0d02032261400940c12034000302c00c003085a10703c030024510701a0500f0b0041690034003c848141d1401000841c1e032050300c050300d03400300540040d081c20b1491088520001400d0109018041e40c0303c1c001070100006840c02855650f401045900e010800c1c1802d460070f55100c070303000300c5040c014040241d40440c01d41003c004d01c0100140c03070342d440b209005000c9200d4100a05507610005000c01071180c040445000d032502640e0502c10245e8400d952a6201c1c030700c0d43e409005801c18454005941390291036990058000e152088801a000180504a450548481d040345d1700807107600d0504081800b40003030180040f4080e04505242800181d240e03c0020320240c0450b0780000018a010340f10ba00070b1442c006c026203404e0301c5000c504044401064103403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 77795343 1250 77794093 77794103
    0xc011805100213030803060301061d09010b0d0b06010c060f110c120304020915010504091b0806031207030305130512041a16030c0203100203090106060e0411040e1b07030507 76
    0x1500500a81402e000701c90002c2d50391185515440d2554460350025003025107240e80c55504c450001449204a90010b208201740c001d48010b241070020325503003150304124030749020b50340c3c4c021094003007000e448a55620150070b090141c110304107031504100405c0d0502180d45014607103a024045140c402026001c40d611180460b100e82c404a09100c01c20300048500070b600040e00030015190081c00c003134000c001501070402034201a02c58064405440a083ea039407074064840601084640e4040b40c1a5046213060303020300380b00358029102c240c4900c01c841025007850745403804610b102c99023881c51084641c000e000c5c1c58282d4803414400006501601c500d40b00a101d10a018800304130650840d80340442422a11120780d01c2c91b0340c00d6852003031a85090340d050003400c1520710300718074038002503205000c44400042c55a08128010740010b91000c83c0b030b13018030700c1d040c07401d114044c407070086a0584c1c3d5448580c9190b0f03075407608080c1803503100c0c404540700d08001240b12130806404c5030190900e94030803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 77796593 1250 77795343 77795353
    0x90708070e010806061003060b030c1c09020102120a021606020102031b25020112050a0203010f0803131707090911092802130b0c0606030105090613020112020c011805 73
    0x2418800d401ea40280a40d1105811480c0800c01619046512481000b0030781000b1400c81c1d41c0c2c00d1400d5180c0c101b1103402d0f4440c17100103010054541c3c004010450124400303000c124078111130700000c3d545c143c17001080d441800006200c0101600030003100d40c18182c0304862940b02c98950000a010b5082612485170300310084250035400b6201c3c50940c4e6900ca13203052450f00f00d0482031030f0321120500c84181a814043e5110a83c0e00304d6400380950751250488200c00f50392945845826001d40c44554403113500c503041442041d031320f4010102000c00b00c50a0084a0803003007180020181442c0080e840880541d1812120008000c00800320642d683c1080764a0307040c59072100d82e804541c40040c62a503285201c3d0b1031030110b40c09101e50141074900c100c1444070011548405501009a10407520401954064000c210241c0350901502d035102c110302c4013411207810001c085c40f2400d811014001d041c809114020803070031b51180c0c1655401c0c800c00c0024400c08105149020440c650140d090b10386000d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 77797843 1250 77796593 77796599
    0xb0c01060503071410031404030c0c06090b03060d080c0a0f0b010e01030201170a060506040e06031207051207050a06050a1a03070f0e0604090624090c090603090c08010509070807 78
    0x114144044800c1c44412440c0003031134804000717220310b032034101c4418541e64415980c04a41014003003031040d44a601d070308640400b6410080c0406005030b200c0360420a403c03209102d1021580c1c10347c0d070400400c0d50584000c1c8040d142000c0580540518054644542c00c04030b01441f0005210a14003405a0050885a601e41c440c81040ca002400042d001c0f5543e241c80f0107008922245050340009180c20000790541c8510004100d980964080c200340c02400050142d81d14080c80703001030140384800f00e00c0ca000c030942c0d9115103a2000002c1c100d043d0401003500000c0c1300e801c0c41030b03041071503002104203e5481d00d00f200c2001081d01101c0c02c910914030042042681c10f0000e002e1058403045c1180c06a00307446d02c42070080f801401000c0d0764000d41c4550741440001c046001d001d010f140701001c104000b805801c0c000345202e240b070340b20024850610400c1e4003a150410003000c2030306d040345030200d00030310b5038248400043e03040da0000420398a40820044500310114414043e100c0b40015a00e0300b0769 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 77799093 1250 77797843 77797849
    0xa091805031c0c030209090c071103071502010e0a02010e1504051309050f0c0f040902030a0206070305040e0a0b09070c020f0a03080d150f0509040309030b0a05010302040c051c0f060f0b0c010605 85
    0x107142c6da82500401404d01040b03403070380c0c060050040103104605400c1101041404242003454a900c1501545c500d40789100c004c54080c01351020f02910708008060f28580d0750002403240e800d0503281e074011032040002040c488a0724044402600002d0a0b442100041c0740f6a00300074107003401c0903103030380c0120700e135040c0416800700d400e40c0785480c010101403895441c0000c200003030030943e80407139061141101038401a00c52601800c001d40c0a502c400d900c452814003495075490006100401c40351170500f19441d180d454618803074200c4550b2505d5410108680b011603860140e1a031450791103e07410340c1c000100f018090080190106086041c0807101c1c400694100508060040c0340741c040d084107023803100b4141131031001c2d0702602a203410700b4056640c0e00c401c0c0d0201c0064440d4080036864a0042c4158106409006003001e00c03450914582101404802070f035030303861000b001116464000b190320480c180d03040103000d00b95002c074100a266407040e445000d68814042ca41c0c03036508090300041d10340303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 77800343 1250 77799093 77799097
    0xf021002060f011503061205030a0908030415080c090d0b0118060305060c09030a080c01050702060c25020a0503100b0a0902030609070804150c0c050601140a091805031c0c0302 77
    0x2214602e41602a90911012003060009020b07078004050369010002143c100020148054a00078000303580e0340d0b821417100802e140100d401903259035000700805c000c02401405034a08005d100d1170400c08540303403041042c600d4030a0034042d5603c8441c60b100c64040c0040d40d0801c80c100c0340c181200303104030b64071004010180e403001d10000e05960024000a000041c0b500c00807c82c44000809a8000025541da405c41c3c81c2c0164528805a0790b559080001e020380400090340c10080313010110303050403942060b0750024400301081050f100c2615027104219200c000d043c00c00340c580101070f5809050300e20011801480c0082030503200d4031b88118001501c00e02c52003124001d00024004078170300e40d10303100180e510039000303001144c40c45405a001c46100e0750611030090390440300c5d070b0380c100c1e9060141440e51410348103810012201c481814028030076a40c10014508840f0b0041c40869000c2c0084001c0f20360000f0510302804600000801c2054000403061310b10030594004420010204071202c110224 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 77801593 1250 77800343 77800351
    0x51509010f030206030406021303051b0f0a03030e19090c120b240403050703030c051c08070f030906020c07180506010c0201080a091208060f04050606030a050c0408030301030f02100206 81
    0x70381c0e4880d024009410000d00456105004080241c0b80100d1003018005101d07a82d8001d58498028a8000340031607001e000410001404031003020702e84881c1c40c001101c1520714030000301448003264011109841d11000505000400c9400d807148580d41ca0109003d03295040a42d0005045002c2c082c500d041390f403007180c0c202078000d84280c400d40741c444842080c4089001035079035142c0c014480040001d0741041900043d42c42940c80c5c411541c250b1402528240d411b0300c0d00610444941541ca212a50080b9804d5002c01680b421401895800c803041e40100301e00800a4820390000680889201c0700162940844203071900100707901400340d541004444041c0d84841c00250300990307002c09036118941a40d04402161000140c0144603503442d0602c242011281012680352010842d16207028919450f0b410300640b0f0501003882e2140014550b40702c02411080c280d03503244041801c007520281a1805045400e040f2656561241032008280c080c80804a215100101072481500d03c046451405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 77802843 1250 77801593 77801609
    0xf0d23030c03060303040b0c010902270601051b010612020108060d08090d080906070b0103020a080a0203060a05040f0218090115150c0302010b03030a030e0d02010e030304030503070e090a05150901 86
    0x1591152441140340d0b0340003400c03003076141c030080c0404540c0003078800081241000c5000006a140e0203481401004100850b5401107401d400a18040071214000290b0380071070309182c001d41e1f8003041404a54182480e42c2564603542ca004c1000c680b1a440c0c0300d001040394000d80320320403150703543e40c1000b070322000e404002082c98034280700d0700140d030400f805000c6c40140714503000c44c185800c0c0404906286c2000c1000c8d9005c50342c000040056040c80d03401400508203003c040e000300030540d000f00381d8480f0040d2041d04816683c0b07000070300f80301003400c05090a56004001e210344d0003191052003840001070750040220f510382402c41001c0c0c50140007505c221100050b40c40301c403610840003540c00d030f0035000c0706505554a54440c01c07515a03050000b805841a15107000902e40c030b0a803255072030302c14072960050541e0314042040804071400025240c0c400da0501d02184d03250b0341d4010440e02c19505035a8540c00004a6051282402040c0c00080c0300d0002c0300b2608010b505032208000c1c2030070f000c1c416010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 77804093 1250 77802843 77802847
    0x30105151c0804030209070503062e1d040513030305150d020112110c030a030b0d170d090b0a021207030b090601140c060901090c080a020915120f0d23 66
    0x1c0c6001a5104035a00240900c40341c07800e065030394001c0750280070200c0764000001c1d000001c00485192120140c6005480750003895081886051000b80c40351002e4500401d0101c04250030400d090030701d1911038984001f5100348050300300141011084030010300c0c2240030034104400a2158103946242c2d4900d0700c80103000480e01200ba0b001510a00d4401c5103e0020a40381c00c8241900c5642c0b40080c03132036811007402180d654a50301c070300030200c902d00d1a60324800d108030030f80040407406444011020010201c01581d80e1050341a10f00007c0080f808010f143c2c0d0503040401ca0000320b07a9024181e50700b900404c0004c10365825000710f08076592400381ca540208040081000303540701c0d079074082000f080f000043d445c0c0f105007403800e0328240c41201d9665103691641c03914030412420301d40c4000204840ca0041030f02d85802d90000f60008802001101501d16084400085940f071440c079481c01c14122080d01d1220029200d656159038410f41d00c4030100f40e103004014030072282000c3c00400784121240b454 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 77805343 1250 77804093 77804119
    0x30203161d04051011070f05060105270114190306020417031306050a0504030507030c030507170307021e0d0b010312050406140c0a0b070203040f06090815060301062303010515 77
    0xc40101700c21031800c00f81180900c9050b00107601c5801c6100518066402840d40d5850b0500300000781d4448a410210310200109040c4890740d0600c4c8941543c00281da05242484080e0210b100941c003a0108014102d9841f400020b0194075030081054480741d0013202600c0c020300c50b80c640d90f481200d41c004d8240e80d549104100d428841d5000e04808401482e0481c40c0580d280c079282e02d803200c150000d03035415000000c2002003101c2040701e0401030101308900c0219589030703400e440d26402500806805204022000040d21175400320b007031240e480c0140048202041c1e42814401400240811a00110b5403103247c6101c9000700d0a550454a143c2e03030707803546e6040440c04119542c1104069009034424164000002018024103074810b0342180e00545c1c8031403926500100380e49096001ca014000095000d002c01c0078013040d005104d44030b501000d10540c4403000031900400855126a52110030790440c0102c3c000e040e0141103103642c00318003d2010ba26a01c0d59040500d2100c00d031b060707100032898811 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 77806593 1250 77805343 77805373
    0x40503030d0f020c010c03060801050702012d020f0316120b06070204020708070206030c1c06120303020a0908070602010b091e060d060906022116080705090307030203161d0405 77
    0x1054620500302c0503040072528203000303003552040e040c0e2401080c2c43c1d142c24062404240300700b40c1c0c06080d40c4000d000d0b50070504c4000b08050b1404210f4041c200449404103000d40c0c8075011201c4015031210180c0c1e991a000c018907101051442c0081c00084145001c000001d40c9409400d904e00f6000340b80901d0003055a08100c001c1d070001c3c004450a00007403092002607580c10001d58070904100d440c50346d89800f90b0103020410600301d043c142000d4a460010b2020303040c3c080d1100c6400764942001652142d083c00199001d90140d48541001d100c0c0080116606a041d0070508420600790b5000030f040c0c46401c03003220141d46a02000c07410032803800c0081c0c280d160418400c540180a40e20000e016812611a00b0603039215806540e101d803007a00c5120886101181c049a000091161000900d546d0800080003505e0280c12141003141c04501030865a6050003214003e690080c115038000140403a0051180568481c040f102c00400e44003805049021111740d20455100c405044004041520 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 77807843 1250 77806593 77806601
    0x9030302120c0a020406060309030908070609030809130c110111030c030a0903050c0a030e0a0b0712050307111510051504060c0305040504230603010b06160201020307020d0311070506040503030d 85
    0x1201840c3c41659500c8000da220392003030074050152a50007203004a40e60501a00c41b0004c3d602001e045d600c00c1d902082001d03400711902d4240c980c0400299942d9002600183c0345010001408120314544040180d0a03500300003100b0041c080c010003030148251803001280c06001c202c40300030309140208002690151541d105441c4280700703080035428805442070700391411516540450210380d1054100344146404106c22005014030512545861059070b54111524203045c0301200380400440400c210901070b145513060140c03120102c52804441c2c0c003500c0b600c0d61040d01d60366010041040081224141210529080344088205a01d041c3c9003000444074014040e00c2039040103010f01001c0740b580d41d5401100102c03100c00301101078158074000b140303200c0c80010340468400ea150004544683c0c45a0042d1078a10940d1160020200c5140c00140d08503c1031110007580524000300c070100701900060302c1d41d6500311070300c122008240c41d4424883e20384100d0242d254158018401c01c0d41602490704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 77809093 1250 77807843 77807857
    0xe0d09031401091401150b03011811160f150c05030c031506030705090f190b0c07090903050301060e0108040b190e0f0708151308030414030a1e0903030212 68
    0x70002515201c141c071080240701101000e107030180d440f1856074a40d4056420098060242e118200745907514002083c11255564112045090703101e0b50340d100b02c89191000d4503c1c81c3c001841c6110205140c1c501440c010201642c1280e016091074100a0100300e644120580500329841d007518584a101c141c4c54540c1008041d0410241d60405400782038448102170340c069000c43e2607140e200d41080c42080060112030f40320501680c841300d0340840c2d0a00d03040b010b000315910340c24040d55400e60900503d04001c03c0d80c00220286060000d03c004040c0c1c072030021812a1210342d00d2500750b00d940401196000003d94019002e8614a8082100398510310001418000c001c000081c2c140d0071000500d0074628022400b486541204000b00000201440268982a1501401313002498110480c9441c8518500041d142d55400b0000404000c0c0c3c0584100720308080508590b04ca240408000f007070040028200c1460080e00320a044080b801480648207680d41500540b00300c40e8030428814013608088 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 77810343 1250 77809093 77809133
    0x6060907120b030a08030402040c0305060f060d0608070b040305100605030a06050901090b010602071401080402100804020d0c030804030309060c0f2a03050303150a080d05030c09220e0d0903 83
    0x2d4254985075820001310900038800d1090075181d00d0207004020403640d08088900c1407609000800a47c1c0e650b1010303840d6140c008513941e903100d1030f1004a44008140340d8100400a1051440101c3c68808803c094821203205400312007061940d40d01038000c0c1d801ea440360a415078414500c80b0300042c03440c0c100070b60215903c0c1c00042c0e03681060b00c40d500815020f03840342000d6000400c00b484824003a401344840c020003820b00491314101a8041214036003404a15410000b80c0000b00d070842d03031001e007a075407625042025000c030140c0340d05018420398058402280455010500081c800b40103640101e0074a403c02041001c400c00c0744c54100206000c0f4040c56095000c074180c003d0155501e650f41c0015501a038000d54403441c002c0c655420306408090010b1107406103000400011800003150304600489192443d180d40700e0f19034210080c01000c0e0400c0d40300440011b4030b82003694100c8100e40a031074055051004105c4215402c1e2528080002c040005040d42c0060001c10240600912003060300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 77811593 1250 77810343 77810351
    0x70f080f0c060a0b030f010e07050607060608060711010528090201030e01090f11010926070f120605010e062d18070e06030f01050d0204060306150905090606090712 72
    0xc607501800c144044860035070340383c0c0c0c07005150291705081215000640840000f001141a540c09180d510300b9280b0440f8401c20f030004603041006030b07070b4014038001d02c0e18108035016420400d00191224510240103145980380a000071408460103036041c04c1c05044404a001010b02102840b0103011440404e905050700e4082e00c4500403024403d02c503000c2c2c0900402c0044038154a01078040890a980c554100328002e4020f000342a51010503065604a070316508022100a07200b4601341702a0b60b1014002a01420307000461200c402c4086940c1880307404104126038903a02e000c0f40c02441079600d15080071101c9401c100c006100d02c0d80240301000c4000154052603800002010074101d618515055440b040c184070506420008002e8183c03000c5808504615010b011003001c100c05208645c071410500031200d00303645583d030155014541200050100540d0075441400400c002c0c403a0f041c0c0c940c50700c0700103103440b0000b113100c9024000060803e519501c544200321200700800c0718104d112556 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 77812843 1250 77811593 77811607
    0xb0901020a170c07080102090114070f080703030c180305121c05160210090b040209040f060903050301050f01020a05070e061306092a0c080a05070803190b06070f080f 73
    0x701c000e241001c800000d0300755480300728040f01400c20409078030500aaa006002c0810310382c0c0c204c2c001c0d511540d02000d031291602c5250410a00e0781c9840c9102130856100050712009156154000c10596101522078030485260141c000c140500c01d0b103c05800c0b5040911800d0318401c01d20001c095105540407008845d0400f5401c21086590540b861780c1d0669200e0310303800503581c0511130081c0d80448003800700305010142d01d61804017032004200034462000c200016041142441060340b101c0d410403020813580145103805041c5038400c0c010a0b02c2422910380041c0c2542c4002401840ca80d4000042d0440c00d1401c1480c281466014003096880a0b8031240340b50600c60a03c24000104000c800c003240c10252400401c0b2000d420307400540d03060b034074070805507030302d40c1c0149110b00703140e83c8082c0700c0341d4032250943d0460340780c060b247c0024032200c80041480b200c1800024490302589416400700003c1d4800e0081001c144a59140145400229603c24001c15a1f000282c50b0315005090403925200c0c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 77814093 1250 77812843 77812853
    0x402180306010f0905061509040b0103090803090d030b0d080f030901022205150c060403082203020610060503090706030b04020409050103121808070b0f1204050d0206150108010b0901020a 82
    0xc0240c0100754104483c0c002040309071254002c55400610944141c0c041c07207070040005000348510248107010320385420701d80c04036034408d501030050301d5003040b5070355180d042031041aa120707494404003000007400c01008150030710300501680d0b503142d88811560301c0c00d881c918080b04260001050010155030038440101c44040c2c0900031060a468425820016800c0104210002e80300f0104040070001c24030000050081c006106904140c042c106401c03160759019941540d4031681070300341100000c0421520805800040550040c0701c1d120505249a0311041300310340e680000c0b180b03d0000e40c400d8801b0044640264048070b07940b080a040985066183c900c00c0064440a9004580c05440342c103200c1c0940c1c1d07111091080d05600e480b100e058491402c52420780d550011300440505c41c900007001e000e0383c003000003100c41c0c80514059425080c5001d00b0410380ba4234654443c034016001d40c50006000040c144c9680b0400e5405848014569003451b045118540040070900d042d48960354030240464 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 77815343 1250 77814093 77814103
    0x7060f0b0603041a0f060109030f0213061409090d09170a020306150910060e041a0405010303020304030302120403050607050c0f1e0106050402030103080909130c08060402010807080702060604021803 87
    0x44c0601513050b03c1410b41030b14074180b42401003050b100700f440c01041c40380503a0700005a40842c1e811061140e2481058000202c4070803901c290840510f01e405000a070280c0c0341030580c0004c802c11110b28000d0f5542100e800e840303810381101c890000b9080320382030002040c49003001c04815078100031a2519006075011034605071080d1004034401e200c40b02864031501d010a000ca82c0a0700107a14030302018941000540301c1060300003424400c64aa41d04016102c44045011200a400030020300c429607407030078040d4603540240800d80c014013078100b02c4030307202d001c241c201d6007142d60141c0140b45569502c80c0480d10740e0001003080d4850300405101140c1004104102000d142181040c21070103c0782071003481c21a402540007070b00582c018801040460304e400c09031100104142c90320241d60766003030000c1c820701c6200c95006051403882100481d90640c0000c0c2240300360b10030f03211405561122182a5407400c0c00703e64482c01680620005022400c054018202a0440324038041c0040a2200064109 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 77816593 1250 77815343 77815351
    0x40e18030a0c0b06100f030f091a1e0c0f1b0f15010501020a1a09030403020a062609060a0e0c04060b0705011b092c0a02090f04050c07060f0b0603 64
    0x65403612400b01444000b009264204208581440e2041c80310305d000b41a1a0900c60300c1001d15a40d00300c2c0e062200842e0f0000c4030000d51207110031582c0240c4245440c40f54200b42e42c44000020702e28254482c04031100172150007100d505020504091075a42800943d50001e40808440311485080d140c944c2e000b009000c6100718001c0c0070301800301d1000700c40c0e00c48400507809241154010501c600c00b241001c800340030111101c030001d20055480040781403a500c9194002504070300024070010315141e200400001c18540f00c00b103460285400c409100708a0401d4074503008075041140455003040d2558091901c200a00c0d0544034081c1c4414000b41c00c4400950224a210f4000115413040100038403c0b030300d80802184558031000b8030140000d18188450048418100c0303051086a5110341180108505d103007080750150700c510303041c10040080d4004446c11809001e83c1c07502080107127007600449102d0410082c0d02c5003481801d458107070291409031a0400e42c0355940400c000300d500d40a00851207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 77817843 1250 77816593 77816597
    0x705220f0915050a0c0f0c030e03071e080609011a0f011103030a0603050f061308030a090803100305010e3004030f0b040302070e04080d020a021c030f0c0201020f040e18030a 76
    0x10b40c80c055441314180e4800c44014800c001101b038180da41150030544040d0304a41500e00282ca008889002c81d1502d149030300503008490447c85080d603040314001160341560429029100c1e20344600c8807403801d80e034020310321a81480e00a02e004044c2e00b040c84e04401411030502d404141c4090180c112415a402a10f498a0750b84d04c440c03040c000e00c00100511820304200000425007890514200c2c0d1b004024480018036000000001c030b40d0100698100515450f00004025564180700305800c0001d0664071044506500301300890544038004916041d0030b450400d40007060340300074145e5501494403400b9000c0c04645c24400480441c08107280c210805100d51150506c1c1e007498140070785401d00702d500500c8000c0861041000245426003a50038601208002585421507580c081c0c1c102030254035192801c013135080c4100c40301a49908950100c02e034504040040c008000c004070300b40e210308403900300d0201c810401001140300f08515540d018900405046e02c40d020f0004450031507001280c0040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 77819093 1250 77817843 77817851
    0x31308010527030f09010203121317030f0109050702030c0115050909060103030905010e18070e0a0f0506031911030a091e120c061104080303090705220f0915 69
    0x107002c4029040200d030050700d0001480300701a0b4070761241d54034403c4c88420b501c289008180d0602d5a4000c03c1515441c1c0340b2080f0381c0310103180c0f4000c0450640b01d54401580c841d440f505028805c243c04008880c0a400d9984060741c4a80c04d010b61031024110107402a03003140700070003011900100070300c142d80c0340d40302d000c10101e0024078100070446801c0f070103000300c650b0b90400f00041001a8205200c071007280d8003800c003a0240c264200004040e401035111030710b00586500100301c041a80980204c1c00640200c90104286485001144231350b03d10380039080d00140104003017150030041c660100385002c0007040104500070410b00224480d0020303505400044e44407461081044410035100b0b41c0203100041a220303e00040e102c1c1c0c40a20849501d200510040540d020b0034804c3c2a040700920002c603440345545c07190740d0701040380d0b20f070300c100c41703801850107480f8000c985890a5241d8881d5000c05468590b692403041e00c0d944001c017a844c581c400a1541c584c7d14800144400035451034030245400001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 77820343 1250 77819093 77819101
    0xd0b01110714040606050906040e0a150e090105072307020621041505070906081302031c081006050f0f0c011503030f030902090a0f140f0417070201020a060b030313080105 75
    0x3c0300780c40b07040d041002844028400040e50303840342406e031000c48080141d9000d4a8071813890030300041680d03001d409801a4924004101c0c10030201040303000b00c407018001c001558034141c1c115144c0800c56590b94108445188800400100401a19855000516241c646001c80400b800b90880801d9090b08001c0768104000901180407290304001c079042400b40282e00d031602d001000c010480c0204d50a010320040464003030140c1c0300407403103803036405000ca403500e003003000c440600c10f8401e100391400648900300161041916003d0708003101d00701c1d110f460910b60b910100a480d600860540004074006100e40c6c06101400d00900d01060440b8042030101415403e0040586020307840c0d0100b4903042c5611000180c440030b502962000002038009035640da10901c00c0e000c5d04141c016488150308490a0107c0e4130640000c482c05103204000c0030700d202d0a00800305a0f80e000d01e42010303001d81c2101204101041c071940003003041110042c10381c3c3c0b1f0403100060450740d41906400c28100b07a9580d40802c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 77821593 1250 77820343 77820349
    0x40516080106032105070f050303150301060b04050f030f07060903030809010531060f0203010905180d0e0103110d0f0b01020c0607080705010603080d0902030705090c0d0b01110714 79
    0x1800340c044200284021030035a1104600b06074100d01146103204240030b03060b40307103102d002510303103855120444980800550421369520340082e580c600380c00ba07602222007601e18051082108030765808941c41c0c10300307107000b04008014003001142c6030503015005039000803560600998018183d10388645909608500740140000300003020b9000701c0c0e24150a00109400806020100700b07074030300c0040b4210150131102405e100682c0c0b802440c29041c032241d994184e0303aa4010314141c2d581900300300111340e00d4103141d80c40b803000d184600c0c0883d080f20f0309220055108a28024080c403042c18082003441501421902e60751241c03181d1310b40f80c5c1e41c0e0203d4401c42d640380d010302d00c9100030920040c03071560300680000340c15100355207000384800c500003200d004101c02074002400454100c07100589501c8601344450107042c00e41d204070311901400b8800b040c9441d00181081c01307488820581030500d4050904c0000410072046049e043c050700f0032448112680401402006d005003941220146e03c460f070034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 77822843 1250 77821593 77821633
    0x3060a0f0608070318030818120a0305060f0a0b180303090d05030910301104030515070201020310050d030903020603090c0301050105060301030803190204030c060504060e09040210050d140405 84
    0x1244c0300c8064521700b0100480e40c003051241e040000c1e00140000700400381c141c1c51030410409000110f0900100318140d100d90140e020911800c02610300c500b00b4011041049002e59090141e031610084c00e0090a20391034501000341e07503995020307044900d0f140381040002c0000c5100307982150554000655100182004d901a00310880c2d941044242c0c0e0300c020701800a010445903808040d2803684d540d8451183c3d141d040007681c0840c90114a03500c5031642445901c40720f0700410722540d128000007061019105100b240d100301e010608001072141400108140690f0680d015000c0009051020016030740d002e005501406111000703000030201c040074142034400580c41607100307400c14001000410100340840360701c0590f1552848c6c0803422418240c00078051034002400342c20211401007956604400103005945840c0ca0319420700c442c10f410481100e404440094029200c142040482402035000d03120401d600741000c02c40c05060b00901c03641c00030485017503415600405818440319050aa = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 77824093 1250 77822843 77822861
    0x70b060f120c041a0406030308101a0a030b06120a0617030403050a022110020307110102161101090b070602190c0f0219031407050906010f080a0203060a0f06080703 72
    0x69122844801c00a81c151a285070703004507405903898a1401c80310b450111000c0418410040c010080c203512030400414004044400b8480119040404120684040e01c1100350061441c0807a10349540c541e002c8010b002c041070b145030070510601018040c0301c100c21150f846007481da600011150b01d0308a04a80c0032042002c134142035081000188042030001c90010340d0035070141d030400700c1d0707040713004800e505d5007800d00d18850640a201c20107241d2040c560010340c0101c3c15030303840686c41c1d20640e40c075500b01c0c840c000300031510180512110001880c1943c2040c1000014141052100d9980822050b554816030007200d00b283e002540e401c03c01811080046800300313902d0001d061600307958807180310070703014807001c2c1c841c1000d0000900303282802e03e040005903620a41d4046c550403504000d6a960860340911841440c42d00c0000b03000354801c001c0802c09003003d950320340319078440803d1100294030151a90b03030401c0c03010b00017141d0071b0071075083c0c40c00030301c010b80e909095490000401401c0f250040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 77825343 1250 77824093 77824099
    0xc0a09020901090b03090a210e09221e0804090c080402130f0b1201090309050f0303070308060a031208040b01060801050d0210020a0501051e06040204060512100803070b060f 76
    0x201180030740c1d076031100180003599121444e0a980c3d03180c910305140303014280c0c2d800421002c00c1d680941c440480200000d140c502181d100c0900d80440001001000001140e42800c1d0800d80410102d030f1448200140c40c5160060070703044070540d8581220004217210213015607110f500083c081103080d2043c07151920311500c42c03400714584d0502d940020304000d0110b00050809880701103008440319103910102c0960401020507001a04c0b4240003030182035004020360200d00c1100d070020301414a00844a406d040003400740d840c01003607980940d8411401b420075504103045a001000140500038810f02031034068560803602d15103032a09100d04001600110100001040104496150015641034141c1c2c100ca141d22640c500b914100c0c500340d02c00d1005801c1e90b0034641407080682440c076006482c103e00503d2440e43d5642d440c28842a48a00e00c5190005041009003140281c5d41e00300071030300100041802a0001e1317980880503c0c50b000210191410002c003018070401c6c1c0b9088451442015040d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 77826593 1250 77825343 77825347
    0x120d0c1502040501020604021318031106060a050f040f270c08011b1b20100503040b18030d050c13060201090b04080d18050109020108070921030306170c0a0902 70
    0x710f00001d46501c00900001e00408100c45007c01c0d1170103603004544044c1441c2c11320401d42c600740c24020001000c0b00088480c03070060310042002c03414103050110650360040d285541d120450010302c001424658000704405580d4010646440c0400402c05200e102580300400445250b051003804064580c2c82040e060303140c198451815031000240d404600841d050420000322260700d8448492001c1800420400e0070490080b8801700c401c0d94a2034200f81074884420090b0940000d503024413060f40c0140241504800261101000e01c4078103800d950340009507804c001441540d00280c801c10b640d032a09103000440c400c10b44610f000302080042038144020311026a442e02d0f01e0b00b290001820150101200103808010b01c2000c0e00000d00e0324280700801c14541a1070b04000d4001c210b5400228001b82200c0040744e00141700e20279600954984241044a401c450068911001c020702021000c2c941c0300c501c00102041d0701c45241a2142d00131025105816184040110b41c20490304103003e0b407481 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 77827843 1250 77826593 77826599
    0x260a09060605120a061d190c09020a0e0f0a080d0906030c0c02010f0806040b03030c0c0a060e09070305040303140a0b03060a020a0f050c0c030727060308030601030209120d0c150204 79
    0x100040c00c4d100b0a070001000210050300d460b0921651154001501d014415059100b005204814480014038004da0450641c10344554000c0140c0c4a500740210019050420780009407805019802e00390078010301c11406c19540d49000d0b4240580d0100c10404104008810000c19405001e40350a503180e070324203070071b080c030090f80041c000d041c44454a00400c03c2c2c100001c4c8040d1980c1d401081744020003004c50352526001d00c4d8440d41d031000002d819000b001d04c5100050340500904110b050070354028288049540d603044110020301c4010005e40825840700034880c00000082922405000c4d04000401d500e0106014145042c0000d043c1080c0544100300036281b00394401040c405000c4907180483e641c28828046a252400180034135615004103140002d070303000c0200e01c0c59440620440300b28490014445603200b296114030000d0400d400810019055603c03a82c0200001c01d030040c110ec04900c400c030080ba14000c0307000300b0b20001c6520419008140b1595048007000c20362426025441d09007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 77829093 1250 77827843 77827879
    0xf050607030603201801090f0e030c0c0d0f0c0b040501020d02151305070504152c06010302070201180b032205070314120f09010f0e030a03260a09060605 67
    0x510b607800041c90030355411142445d9690404008500e040c642d0050344c1940c44084140c0113003d15098046242d1514940c1d94004401106584e409075048025140b501501d1050001840803c40202c0b01d50700e10300a8000040d035a07442040240c0b0510808503120390800001a1a00c00540b03035480555004000440c040341c0240480c691007400c06032560031070001444e10300d06d8040a5044154003e003401c000c3c10a0009006044007226010400b0500d03ca890100c0c11401e50207280c159803441c901c2400049655000b80c00074113545106243c021180b50f080d6071f89504a40300340d08140403d01001003841440d00115100079030080340901e1041030f6840d26520942d23602e84a100080001224901500b20a03009200806907400060103142ea9400e425648000d540c1c41000740602044122520b044681d1140c00301c10700f40030025000701001009a14262240c41c0b29569081c0c030101d2003000c1c850300c6114840712a000310341e1010089014555817a0074820355030300d46c200c0f6008100001c50700030030072 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 77830343 1250 77829093 77829113
    0x31e1b030c0c0f02100c050a06020a031805071a040510080105030601060302040803040302040b010c0b0703140a051515040b0a0815060f070b07170705030a05070503010b07110a0306090f050607030603 87
    0x107036048540620100081c8811b48034044040000381280c040c4003044001e12965400a0060142958080115142060022000581e800c0000d001d40d8004c0030240012061000c0e041d0340600840031807410a5620701c0014012900d00341c410780010010001040582800c001140c090440341c1000c2d400d06040880040d9a40070320b1201034030842c0c40e0419885243d018003400804650441a030414038641000050f001c2c02462540013000c100e003400049000c0e80724865039000c1d8500304003e1032920b02c090208211040b00450010f10032008100000d18030381c813040203124041d03594803086003526183d010012401da40c00f8686004000c10800d0404246060040f02e00303107580164134103016210a203088980300c0c1c0c546000d80e0101c1000092081c843d4000015510403201c0328020710180d602c10f030702141c0c82d010030311500c524007000380700180002e400d5448920040310041c1c00804000c1e0f03a51580300c261902a0415144047d8421500b000d10105100943e4000ca0706d04083c0151840c60780d40c00240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 77831593 1250 77830343 77830373
    0xa080a0201052d0a09090c0c0b040317010f0504062301050d02040e0a020301180911010e0612011509080a02010e060c0a0c060e0a0905040b07031e1b030c0c 68
    0x1800140a0000c404501c0f08806000322040c1c004a485007030f0040c035031260f01c240a1400407510300c0c2c0000400108500a405013103035296903000c43c0320b240742d44001e4a114080d10803424016200102100760228aa10a0003040342c0e1200b94036541c90801804100c464a40040750071051748980d88080c4041e00d84060341c808001c7c41c7c01c998030070300621000003d02071508050a07001490052005030745940d006941614440c0e401c030003009520186803011103160705e100400f0200940040300360b071741c001d0204a2884502400b22460503081200c1071040c100b0907044a0184c0688a0182200652005103040035100860041040c41051b40018106040350640c1a03c00d450000d180155410244104030081740c2c0f15004200c00707604c4040c00b404420781111401d016410640d000543e013400740c041d950041c0d1300654450a26151141c00320080c083c019031100308040780b881c441402155900c074034035954424a0042002d0328002c140201910032603201c1004114100c6440400704054000030014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 77832843 1250 77831593 77831597
    0x60206010f17070b0708071502091e0f030109050105011406130e0705040305010507020c130c0c0206090a03050f100f02030f130201020c040f0603060501050103180f0c0512030a0e0a080a0201 83
    0x10903009038455482c3c01084d40100004840104601d020032440001070003000c0d00c540200400ea00d0019074100407030180f0074000740d00941d0b0f04035101903580d55507e180d18005014048081700c88904002c6400d40da601d40084603960355800040181c0781d058044102c440c4411111140351188040085803140300d18000c04480308040008162000d0040e002c1b50001c40d8844020b00c0305140a040203501c071400104540e01500301400320801000c928440e07510350700300e151104061a0b95680034090540c120302d035800c2d0800c028607408800b144042002c4049507941d9002824041440d4841c0c0090303400c0b09020024060052003480310f0701211045043d4007521080c22030001840360300040349000d5980c0c10164000307140c0304000844c080c0940142054a000b000180b110b40d036598011400c942010604260b002003807400000010303c816041d4806c14000c0ca0307254035864480d40024000d262543c0d07258025480059034501d20354005101c51101d00c011607090000926010304291503030005507000341 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 77834093 1250 77832843 77832869
    0x30c04061404031208092521140d020d030b1e03011d0708011b08041e0c090203040209060a03150e011401031103120f0906030402060c0f0610060206010f 67
    0x380d0280c88281c0c2e0056812501300f1403500c0300c81c030000c0c1c010981925410918007070306020300303091201d0400fa049062070440500305442d02d0114680420100e8035200e080e02c000d6129186d011840a130700c12240c1540900c00742850780983c0c0c0c0043d1030403400000b49018903061148215150356403030f0f0030080381c08a5044070880c40710340340c0019005024141c03100b08401581400b01c49420f1001509a05030703404200204055201208200446a400c0f10200c001510010008000444290000014503001036041c244620180e0315001445040d400030440a0345c08001c000039403502501c001c0d00510241c81c03142085007942c4444a0f50a170009864850355110240000754034030035408560b64140700000a125035869280051851078001c8250f803192160242c181d510500000844041c1c12800302c50a141c00c00036401d1101355000240166444001489042c07003070340c401d00280100703144c004090500c918004441c5030351040707207802413011580807000602c1602c1c0c441c0d012000307541e001405c0107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 77835343 1250 77834093 77834117
    0x90d03050a0b10020f070603060b030612070807030f020f040209090c03220f02090108120319090813030c0801092a05030d02030a030501061b060b041805030706060506030c0406 77
    0x405011000001508002040003c207031950707000c00d60b2107610201d04241c44c600340d0344510032020345180d4003503c0d030744400400c007250081c64003034542c800314001041501c4a40c0e507681000307810010310f6401955150b03480851142145020300d0540e4101e03108541c210300b0014528045641800001d02840d21560004080341c00c122001c030440b01d600074094406401d40d0528541007000d5452840704a020380305e035200200d2451400f2445950007542144954210380d0740c074030500c3c040c29405160049075a1342e44048808500c0810060260b0400c0d40840e1381c40f42c1c5185000305071800b5540c800a916454600c0da8000200225030b00c0c1c40c5d030040c1d100013580104000c1070003603c5071520760160ba494030403242200d000640100103031100481585013000140e0f6583c50a68000e4403034035200240c00c5c42c10340b285c00040d0b0035078015040500041c1000a26094400708965100c0c10a4001c1d5000d500214280c01003040c84c2c0a039070043c12060303950b1415030401c140d001040f03000d01e000e4902030181d01501d903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 77836593 1250 77835343 77835361
    0x30402010807030f0f1e020307020a080307031b0e030708030f040302040209130c120b01080402100503041103060c0408061302090f04030212031303080609010b0301090b0301061706010815090d0305 86
    0xc041096000c401700008039a044842000b0600e40d40c45511550120b12180d44510180c401d40340720380501e03000b41a100b0520340d90000c50f40d01c001d001c803081c1940d911210080307000c03041240101104076100c0e0401c03160a40700309450a401d40d84003179990340c02040915251007105066604803030341510056218080c61002842e4540000020303280302d45004924551540c3c42802d00c854105191001c0042541e810011a01311004a501075086410202592506032242008650180c001e03040900513031007201c0041d00300b42054a0718103024501103005d000e050000c0c01703800e40041d41c03e418602c2000403035001c075661007401842e400f5180d181c080001d040c14028803d10b41034010015110366a0f00e000d038020001c00d448124103a0004106100040e0035042401c000d41c180c80140c02981d045070f2078040128094015413909a0b0155202c11001542c009401f06800001101c2030107041c03158140060203281c0101001c5100480d01c050040c003540d49400b28684440d080701d45008203044c2c0d54030030b20b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 77837843 1250 77836593 77836601
    0x7060c051f05010618031a0604090c06050309010e07080d05070305040806100e07020c0d0209060a050909010e010b0102120a050f070f140601052e270f051503040201080703 75
    0x11054031008521455403035040d4000d43c16100b054981080d11240030740003540503440c0b030100802031940a0554092000e401000950061009001095281090390f03040c6850296504c8040441c40c0402070000403042030140352040500a07000b0601e592501e035005a0390551000080203101e00000c00d141498451011030340a4050182200c0e40341c1884044200d54000c0c034403994688804075000300c0d030000e201145030302020500922140d0440e90540801c0301209008d000c82c1d910210b004000074854803006d40e201d1240700f105000140780c40480c80d0780703420f49268503003140c1150401022003541444100948410003042d240443c2c40310115141925980308041e000340400503100700700c4041200300302d01c3e00d6044c020181501c00ca81d99990500c8400c402003900003422054502d003500c0e10034644d26413040601540d181c00d52034041c1554103004c0105400407400d544070012700d01030003c2407017508000000c00381903502c0d01d91030411014204203404080c00090401541c00c0c003003107015101c2c0d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 77839093 1250 77837843 77837863
    0x130b0c0102120f19020903150603030408010905030304050d020a08030406020a030605060711010e0105030c1b0307020603070207090522060b0301110a050403031709070b07060e03030103140c1207060c05 88
    0xc0210000d0400011051400f8002c84401c40310002c120840f15100c2d80500035501071070070140052503200c50380041030b1082c000051505803d40310910000510000074028608000d0248001c0d664a0034541415410281c0071070420084d50b116030042000a0040300c201c1c0d51141d0480030040e02d0303e41c244011805890680d12040e482030340426504140103e5003004480d070361098903000700d2100694015540f070301048840352020b520a1102c400710f5800c5800c104060840c400542c0e00d0080594009507064009039080c00050784482c80070b02c9840564460207420100c0c1d51840442e115408899052808614100428090b2182140d10300c684094100d450f40705c076000380f05074039691040c00062090308035200a80004c0c60080300000541d421008450103042100d01411149040014445095100c10350450310716568218044010006101071406181b15914400040d0422242d00345400401d00f9254030a00c00c900307101c54401c10004800341101e00740d007440e10643e40c560170f1060130b0102e80780d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 77840343 1250 77839093 77839117
    0x7111c0f0303060f141e01020318010201020d0207060212090c1e0103140106080702010f0209130b010c151a03010e0606040c0e0301020c151e04020d020a0801020c010507030f02130b0c0102 82
    0x11408a145c040c000d09082c2e0a89090700c4000c02d070074082041440001c00b020210f40542c1040103090703400503050358402d554400600015280446014140c0c00304c0e840103000b65002603000c514030b0b009200441055400101890080c8424a8140000781801070b00e0f10081500303030b84000406800d0f034020b8100c2020905c2030b940c01c426940c4d4800300589602c400311032803401075180c441e0322030a03001030b03200b030340c4030300d800038000010894100b0030030b07801800444002814000c0d0b9204400008800d4840f1510b000c2501c0d1000c2140441282c294a0303000081070441d100c0d1f4103010000120b070300c0c00211325070f00910440d4081041c00002e0019241c4856800c4c00316059400041c420400d030b10300103451401140c602c0d181c0103995581d20f48140b0581034000e0b0b20030040010b000468054506280c89103a02400144500c0d815640c0361000e50032030b4031140800320265110380812034581e4052090001c1c04901c2d103419841c20806003403140c480c05440c01004007200000c00d14024041d025170507211914440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 77841593 1250 77840343 77840369
    0x1005060a211b061b1106030109060513060b071b1517091603140c0d03030c0212090303092403070206041101020313051c0b0a0207111c0f030306 63
    0x10040305600c08401e520140c40150b007038400c00c280e180d0b1180060086030740668601d00140c00e0a40d64548011040d0001c0c2c0f5a03001e0b004540c03016503902d400442c001c0004410004059160005105d00c0d09401004130440c289000c2042002e04d080c103080315101c9511031260802c2103184d507030480c619000d075044001c0250018500c210340d1a00b0101505500c51004100b60960b076610348169661026000da613800c22180701010000150003021418114600e00155040119075002040c80500369203019030003c1d884183d02c0b1913498041c001c0d46602c2c42440d010500c0c10050a011a58034440c0c065824000c1c2140c2029810b1390040c0c4401c200985041030031260b0741d0410a40c0256103000558050703c0511041c01102c140790300000c1142c120111b48507014007d0740c508403c0008200440f0081c0141c2c800705691078000603004100a4840d410804006859202314100620541a404165805080600c982055504440d141484010740c8003240704c62031046485c040340079160503800a084007441d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 77842843 1250 77841593 77841629
    0x10602070614071b12020a09270303060305062401020a020105041e0909240212070e0f0307092c070306091a0f070e010203091f02120f04080f0d021005060a 68
    0x10040030b501c2c001d4001c58204007201c8d103901d0f0020440780d00034008010413090b800702d8841140035040301c00740345019080004225070f03240c5400e428504d0032102c60000e051040ea070400d08080f05104148811000e20051508541950020f0702c3ca1040740181d01226105071103110100910071048000380c200d000c801d10609560f450080c0c941840007a1900806681d00c0c890821001c951090f1603510701a85080801921400b00c01d0b5030040c100d141040d0441c8102c2070781540e03078600b045600d0003425040c01c0060031000c402d00000114841401541400b00c2c41c0800350956040001c030b200a598002900190071029132030910074504848030f03203019501d4400c003001038040004400d0f62080c0f8003600d60100500f5408012600ca104180300d15600440c040805819490114050001507003240111400c0400503c500b03185500054450610790400080901c0b0594041c46110b0035440018014030910f4400b08000c0c1d200c01349450002d002c41d40d542c00040b0700f9a21516900020800c4403007203c1707403000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 77844093 1250 77842843 77842859
    0x809011e050a0e030f0a09060c1703040f06150806070e010c20030a050c0306010b070b1801110714070b030c0d09020d1203050604060e1009090602040302040501080d0305010602070614071b 82
    0x404e08404204009400550702717000d41056003002c0e0b03210521442c070b9031181a0000e000d8001a0007902c8002169181000282c41441800466085000c02c0f08080d49000d9105240c000024800702c10084ea04803c000c6a980062400d00b03410f603c1540c200c0902901000802400d0f080640707a54103200e1034001100340329010401c40911041a002d9944682c2c0764040c0202c10f2003a20b00c010880032034207000464211002c0d1005009980035000428440b0407440040340540000300c0588528003401641d40d00e02c64100300801c01400d03240025070440c5416825110f00c0d01903403000c0025a625904000110356496440012150744a00c40071140001440018001d003421035803140074928050f400f140c460000805913200d40c40c4581940622070412007054043c21660000b140c1494003400044016039840c05081d02030040d00c1c00400c0e9141e00001c00805941041c3e01040c25908030301814002c640c2c2c88501805201c00d261003040e50b802891400780510507203c0800800e4010649010036900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 77845343 1250 77844093 77844097
    0x2a021c060501080c0a030b061503100603050f10062106060f022b05070c09090b06030d0512010b0c1f0203090c0406080c04091a090a030809011e050a0e030f 68
    0x24003400081215070303220002143d49840503600c880d0b018901c840100002452180c0f5a0b5100501034150300c150414080b04009a41050360003040d8010b01c00e40a00416501d0b00c24283e01c05000100380b01d030340c02c2c0355003100c201614900035282040403a10005840000d0301c03d144242c4030f42c1490800507141e40e43d0004003c00303000c2d0b020f000140580040094500b8542c6849441800501c5c0c480f440035900c090305641c142e0082d5070856030f03690341072000110707a0a188148490f0b14010640f0b00703650700c2c0c59000c050400382e0300403800d002e10000340103501041413070318030b0241915920a9411f40d511440760419184c0840521120b042c03481040d80e0400c0b0310080d0b0059405001034004490a00d4002030400c000c0d640107000b0244541d105840031006450942c2207440221300403c0482e501003613110728000c3c2808119111411a4800d803111010103074081d42c01540644c03420001c00c1008581940c0700c11580c00e42562040302c903140d00c04945005220723408407200e84050030803281c4d00c1c4901451a615a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 77846593 1250 77845343 77845399
    0x80a03020a020a05100f0302091302190306051c020f0d060c0201060311060a081603110a0804020f0d02030a0303090c0504060609080105011a07060c050f1605060105102a02 75
    0x1503007481d0340001d00303403c01d85c0385405245d01c00d0f00d4501c42c10403405012402500440d05a9900c00080b4202e00c02006651005140c07c1e001045000020400210043c1c103403075103640200d000d100140800148281d405e0001c1c01500d604841503d040c1c0c804e500002e1500c007505c40080d044510b403816540b01107405500003800c981c800c0103a84a504200300c1000000e00600010001180305030000403200c00700044161244440d80c100026041c15250240910b038228007541d00c003082c82c080c180420751038000300251003c84102c1e0000f19048442d40840c2c4c45440800e402030500d61a040c103c3c1c204105404036001a240145c410020141d507400c004007250343c10320488d81c00794079010011880444c0b85884115006d0540a051700e0400d43d0340d9010010300c1c200400170708000041c814820109280c00c001c090180e04c0300c0f04250484450700380582004010b03440329200301409405030020300c0e0055007401207001e000c40f10f400000c0c0d503100d145c8441014003000940c8960f419040c1c244000c0d12450303071654 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 77847843 1250 77846593 77846599
    0x21021215150913020f09030d020c1003180602120f0a060b160c0b0310050f090f0609041406010902030105011803110d0f0503070b040519020102060c0d0b0d080a02010c0203030f0c0a0504080a03020a02 87
    0x400b0f0313235100040e85c4945211103040e0304952075403101d0742400d000b90003d000925010021010001490721014100d1304100071400b81114428140702da05401000016004410b1180402c0010b1400d003003a00c451081481c00701c2440160740c808020302c07508001b108000c2541040782c036500c0c074050810036220051805460f108070008150003c0034144100d00922078500c00450303100700d464850410000043c0100211081040c031076140000070418800c56000f0b126420001d81c40354100000540940b459100e85d0080050b80c0e542040410000c05c0e83c07409101051300e004035240300030f00b440b480201124034040e000b8400002c00750200b00039292030900c118041c0d001d550306541c8042c0b0b240407071407180c1d10190050740800c0100b000151070000500b841050442c000034055406008034100e400b102d41d0627100100c02140e03c0394072640a00075082c03890a140b002e1440c0d07107414040010741a5016108444c5c041c0045101d54820303004404860182040408559a140003031034002d43e2021604803c82c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 77849093 1250 77847843 77847853
    0x3070e01090c0c050601030b040f0804120c0e040c0501030c02070b0c0d0e0a08120a030b09040b0702100b150a0c0c03080304170408031921021215150913020f0903 71
    0x41e1544503c1c18000619808030185c010b6901c4d640b2082038440000c1c03c26101c000e00302003039400098800d001030000344582c1c418400212a1030070700000c40b08099003d01d501540351000c000c00100c400103000e090b00d1090900280442c0302c104120325019180c0c01c601281c03d40002e6034800010002011051043c89990301d8241c045030101307110030f030041c612031100c450703110038189000d07902d020018200e140c0640c80c0015200031202c000440c403590070f071400e54001c9144130a100c503080c3d040c41a84443c410b6050b0521030031302d0300d002050303102124901d401405d1001180001c4610701c50010b00d001c568100c1d811032a09078403030030024010b500507141110380e1908001094a4440c006003650704480c01034000c0d504010302c45607035420a0710052050410440340308000c81c51701c0c4448101a2012045904c01078860351810144680c100c005450104400f840300c9405c4d040d655600c1041031043c0710405680d480300140c002083c050141c0d9803034507070254004580013800900880c0501050081141258 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 77850343 1250 77849093 77849111
    0xc0102090301150501170c0d0903120b0103051506030405011508030a0e0301090f06091103010501060309030201150b07030f020c0d03050a02060f0408040519090f021902060702031e070203070e0109 86
    0x3030f2209902c3c450140030840aa03d5040c54441045c00198040e60380d018141c6440f0361001400202e80882c0800c8001c10b940300d9018480d8411803081d0000d103282800c04002d81d040040031441030b0710304508424030444000001a0411600390044113005030102000e0344510344a01140341c480d00000880c80008111140c200c074246014051411300d02d40140c2c130007c0c0003881d41c807208090160008141d8658100303c2240c249503d0904c1094020b1050fa0307000941283c542c5002420342d100200c500000c0e80740a1005d00c24003491400b1942401da040c01c180c000f070386030100d06905002207032000640c41400c0070300c03400506811070024004000c8507402d40d20f090f550711500070180c40c0107940207040c0b00e000348024041814080c00c0002c11810211200c40241d95550214090350603000220581d1a004100d001d102c094100c43e80080ba006c5002074a00c600d001d4000a59a014030010904c03089503455180c160004003400700ca00040d0094182c0392200c1e1901000d00b6511020310480c8a4286040084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 77851593 1250 77850343 77850371
    0xd0903080402120a080a0e03010b1207170c030601140a08010e1509010e0601090c02011104030c050907050a050d1d0a060e070605040b07020f030c0d110a0b0703020c240c0102090301 79
    0x11081117544100501e04100500104541c03621040058030b816650f00e00c46407403195500002e21214511000c010000340d418549922220004101e0030b406c16031205100703008907a408078500d4196907480c101249000c0c00d07000010421166580f10049552801091150682000c1f81002260707a00350119038440c0c440c2c5103014207e81d241c48060000e0b411110062200e400e41340c01000c5000702034030001c5651980c5a00c0400c8071350051380302311a00c00217040c041106090165905601a065041c07086c200782c01c00e41c0180080c40342180101040b65034012140340000221b13080211110ba510883c4c0000196141140041c001c0b0072070140780344034140c03001030164440c408030b4041c0d88413147e440d81070800342d9013400380c641c0018a42d60f502d8091414080aa0384443d481c100314140201d0030480e0200310b520510034000d64036080142040c20400c01000840e17000202c0d1003103040c0a5a0f1000b03050007000072540e203c0c1300c15240661480001580281031081500074103580070040380200403441c101802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 77852843 1250 77851593 77851603
    0x2150c0d0503160e01030204080d0309060b011b030302091503070e0306060907020307030c05070e04050d0305160905091302040e0114010e010e0c0d0216030305071b150b03030d090308040212 83
    0x703da90407103a28076400300501c94032451480c84810b05003d0b060079164003440c0d04001a945001e80003d550f510541c00788406400b0380c3d0004402070070000d103d0b460519003903415000c0502c0c00b078203264000410390010f41724084010101500ca0100a44a0030446801491180c410524501c82d100e01070200340140b44c00005180100c115400031071901c032039580d0a4590046064060b40c9602444030300041075084504802c0c403a901c200090803010071881d60140458102034410ba0001c407031030400d2101240c00c00001070903102e0840d880c0015030f50762031300d08251401210000390400c0c10b00790240c94500054022030941c1701c02146503801a030300d60b0310241e1200424810b4000c440c0c00100400c4490310010010000c4243c081d0000d4580111611b43c0c514203001404200d0010b17903158100040a507004905080402040ca048a000013854482c0c0e419a030060102840441d502d0403104059035041044900c400c12002d41441800d14500b40981065404c4400781c1c055264081c00b105030b5240415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 77854093 1250 77852843 77852851
    0x80a150602030409110c0d020304030c09060e01050103020c010f110903010b011b030309020a030b0906010e061f050901090513020d061a040306050606040915050114120a050c0702150c0d0503 83
    0x10045060030328101c0c01304041c006401440110060800121b1019801400064448040f607001150346515500c2c0144504006600c04840720f4a4808144a070310301002e07025046810034a40961200e040d00345540c0149240324440403041c0c030341507403600450380d004007070031100c102240200042d500c01001901e5070083e580c1d140f0464450311900000003030003984509016400a4a04202142c481d034498000603001e44c2c4448095214000401ca0300c00c80b143d0307041e03012105543c1c0030070381c01c030004070782000e000c9a026003824041c022506045030303446003080400800c0300400c0c08010501030b0070241d00130741c440d018000380d19007410300200c0c0c0f042c600c41038848400d9410400e6840d10749503880d068028000074240d240d101d00108000101340949000d00605c40488040700e9106600d000b0015110043c140c44a403a81c9a05010606c0d4004800c03a80c0c6921407949200807a5580d03560111200340e1240400003075100456805884e0f00b22003c40107400e07607a01180840e4542c0786c00c28030585060004807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 77855343 1250 77854093 77854097
    0x5030102120105090c1303030c051b09071d04020d1d0705090f070516030206090d020c060d0209030703290a06030209010306020919090b030709050106080f07020f01020703080a1506 79
    0x100040000c1e00701480c40d20f91040301e410f095801d10750036020346c10320b40d10194410b80000d030f0141300c0c1e642400401c1c0203451540001600460701d1400b0b98011a0612100070800f00c00d1140d80185c1c5208d580302e226180054507001401150781d8007940180e80018000d10114407035403941406070310760700000024080281d4000401c8403850f507079000780d681150707040203000400300f250501800c0d10b21180f40d041c1001c0144680c0103030060b403800240d00c0b031501445c05003810440d8400034000a0a4481604442102d0306e042d41c0966515044808a498015281d20060000e0f013600c1c4410703a004c8400f2681d5000b0403203da04001e958607684000f00035144140401380d070010324200104002541c0f64001e000c1030102400b420b840f580041d103c00b890b03003450f52101c8444d98544003089181d20b014400c980250550b0318041041c5d504240000308903103402040c3d0200b0040c0711000c9900c403402004079032600c22031040250b564064520780244043c50581d024445503040030b20152b00b9224400d443c1c0e080c2e581075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 77856593 1250 77855343 77855377
    0x121b011406131407030e0606010905090c070201170403090f06051c020901020c180601030b19050108182508030717090112060f080c060403240e030c0a030905030102 72
    0x101009812203980392011000c0341e603154031143e070112680c5114410101624001401c42250b80c40300e0420400900c1070741006082042403010381d454482260300500111106a1126034038401641d00e4102d0117500c100c511a98001c00c010960701c00c0441060721000c400c46504941d0750201039880d40102a4500c00740c0a800c880c2e1904100f00b0b5010f44002a014411904002d0307440c80420031504024585034841e103680c40402200d540c040c001c07044560400c1c0d9000480003401c0b01c0c00c1c908146240101c0381000004004036080c0c1407518541c598004215054569481c0e00d0502e41420001014100540700035441002908980202c00d803941940c020441695080980145450940c04040f2481c14007802c1c0c05840c00500861040c1c0e800344c00140c001000090030100801e05d0079102402a40c4214810007051000800c44079034281d00516250f041090130701070901c000c000e840b0007001d104c1c840c031000c03c02c407100c404000307402c484044c001e441d040340e5103441d281807500380d1240c40c0703504a0700014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 77857843 1250 77856593 77856601
    0x3050304030308100512010903020c011b0602030601030b090a0203010501090e010303021c300b0609030d032d14090d090b0705010e01060e01030b060f0a0509070c05121b0114 76
    0x30080a80e10604106401807400c5d19000003440a581d4a9000c03603080c0c0d900d039050f008158040020802c02c42c000d003040c1120040003c080b001e400b890840080c4000d0300070020955a90081e040600644401054083d05107881c03281030340250024030440f4000340c0700325000a107541c0c5c1c15218506903500350b400b07408040c2151b0201115a501c0c40850010000031802d0b0165891010b50b1060030304070425142d60189120300d0405048d1260016600d204001c10000b400240c0d078002034402c98020141008121a058482d5804500301400c1400004882403150500c00024551024140c181083c1880041b40c070340044440e6900c0d91545000042a8820001e0204a08a4029214041c0704000100b40c1d45540c84d41c050070f50b840d40d8400c825900c0b1181c01442005040000f9543c04082a0740c009010f030030f941300140702c4c4a40c9116280c007400003003000c503494510030a5440703850f9402c081141d1400f01460003624195010204402c025030082071928103c3c98180110010070801038481004c54a07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 77859093 1250 77857843 77857847
    0x4020f040902010903080c0a03080a020a0509120c130227010e0d02031009050c01022107150e010504051c0e0a2601050106030b0a050f03100203090a080301030b091501030503040303 79
    0x74032480141d050241902001000404980c01401500c0201000d44014040e5103001ba2800301c028041401d42c50041c003100308000d42c00401d642d000c003021140412854040c0e400c541c00c109414040580003111540c3c816614080c540040580500880b0308075aa80d20b041c45803131400180c510080d0004640804400702861f090b40320410b8140001d0548819410100e03401044481d0344608603910b40200e904a5099130301840a11540d2540341c00c07491010031040500700300c52090700402800c1030740500421001c41103640c004461049100000c00140c182810000d40c2d80d17080280503100256018480401c40380705030507009000d40003a01c0301e6040ca0620650000b00b1100c0d6249000c07540b801758802c003000e003003405454004d0500c0d440000c1d1044a810621030b2401c1b081d00440d000d166515420707480e58034001004000300b4008100107803a40c4480701103d0601c1c3d000c0e000a004140007000110500085401030f03402800750030119040000d030750280106540c0244006800360b04240010000300e8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 77860343 1250 77859093 77859101
    0x4020901170f03070b0105040e0601080304030b180d020f01060603060e040807020102030c07060804031e050a030c0e0d0809040e06070207150203040f030b040314090d060b0607050a080705070b0304020f04 89
    0x14001c0c156040312016001161540d0081c100544020b00e9000c01000305040038403841c0700145108001d0000d541c1032444655980c881c40c032009003a4041ca01c000b400c1c1401401d00c0e010306d50a010203403400c4203e0248002d548000148103c160b9510700740300040d12901074840d4030101c404058020340303151340f04d4888505642045200f40d05500042090175262035040c0044c0300685602e0f01d4550a030705107800c00030b02d103081811000680303458154440c008030350080d064440988040c83d0114000d0030381d5800f22200c500078480789402c401110f4002080112903009021800800c0d2410860710385030f00354a5035200c2081d118071016030003898052000300c0c0c0d019081501204580126440c0c0365550300d1a03070391484190f2064403403800480c01e003c20964000419101000c00c400018213000d0380c50006100350a03c0000101501e84c0c0c2c4070459415280c0106591a50b904602602d601c1c0c4c0c41414683c1c0250302900044441d4010711a020842c960030409070fa0103141c0240c050343c0c2c00200e00003840024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 77861593 1250 77860343 77860379
    0x1290c0a020d0b16020102070f2a0620070515030a0605090106030507020c0a081e1006060503090706020703050a020105090d0606080c010306060e090a020a12051e07050304020901 78
    0x500415055001603102c5403003a040c1948141e40414107490140d41e1110001e414008000c02c5900400103080400c1c010080d01c1485034008041c00c0d0301c01828003600c00300d141c0c068090000e0104442c400520035810140b100001c880c04000310030401810301000d601c441c035038090b096003e6a1110540c50801103100503550122904000180e9141c81d400000c408041c240e0040c00003903251410007118036414402040341d02401e8a40840581c10070390555110f5a40d40107066034200740b11000c00c181034041102148004110703404100e09a103540303009016034030403500309140b44211500041c1d07680c4005040e0084035005409442c1d90b40da180c0c01103411ba803103418859030003141d040151012950074440c1d034008041803c0205414201c603000502643c4840c1e0240c0f09200000942260944441000030f40c007918200d40140c4d107640080055810714a00810b030030001e45040c00300a022200c20071a111144068450b90826550700c04080319a0301c0304840003504500100010004013402030121600d07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 77862843 1250 77861593 77861617
    0x71403030705010906021806031e0a090c12020a060807122a02010b0103050c04060c0f02030a0c120c0f1212050c0307060510090506101b0c09020309060129 68
    0x15003030007502c401d402e40b4941c4c001619059400075000103c500c0344a110200c180c0d0540b41c2c1d40c2940741c20010607900d108004145c0082840e4180001d24100b03941c4e00050300030354440d480d01d580307e84070780401c90020101202240611066000480c55034001d541161292145e0798501507a200303e800b075840502102000c00c0031810a4082081d05030f90307040d62030300701e104040d8000510821014001000d450025106003031300a02000306024555200c2c6c110b109041e04943c0e5051020814400f00c0e203026680710010300320442e00c0700f0201d4040d01d51024540e5150203409518032280e2500580c052151a500c100c00300d55101a001030700040980350a0011807411342401c0d41480d81c1c2c501d89070f0940d8000c030011a10b44d42d1711010000100c2402d0141d00c00341148180402081c603040011402c00d02b100b040c03180503c02c0c8280c00d98811090030300c6030305000d644811908003051703544000d113000e9081941c003c1342030b0003080000302d601d000c24000b40130350020700100610310488406062a90707510506150305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 77864093 1250 77862843 77862847
    0x30406110906040618061d0405100b122d0103140a051603020a0b03090a0f050c0a030f0201020607020d0e0d210903050607050405010504090509010b0d081b0a020307140303 75
    0x1225524003010f0320003041e05496a0988083e40d0032402c042c4191500a01d00f48422803503200302d2400000c1d039640301504280d0f0000b8090326044aa452103550350303070020f4100701c00051800f80c01d1103055520f074044c0844e07000c20240c0050b1180f8009907020303031582c4601600e140800410100e0420f0744c1199904480324180d5804200c180c50b140d00740300c004440c40640205041c1c0800c03c50070483c00c14030050503403040d054290300b88000e16a0702c800d82c050700a03082c010000000800d0140c180141c00c003803040140b07440c2c1380940c1da00e892050210564401c0e40580200700006442c2c500110f8002c9040f1416544d00030341c189140c0800c00e2203c018207007030303e4500300e00500d00d1041c1c50b40d410400003402c1d152a80112035207545081d034500341004200c041005801d104c100101c0e41c001040c8c50a803110321a01140658491021a004100c0c2d80602075024120001d0682840f43d008014521000d5007c8007001d44a8049407440d81c440a100e0000c1d0145e106440c100900000381c9030120300d0840003000d8034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 77865343 1250 77864093 77864107
    0x1109040206130e090706030204080705060903030f0a2309010e010f1709031209031312080706090b0402040c0e03060a0203130803250305060d1103010f06030c18020304020603040611 79
    0x150000110781c020b000d0f0044074106010000c0010000400104134070b140a52801d810503035000d44070300e52442803500602000c0341d00d14096400b44151034603104911640c0b41c49100d880401804540301410801f00006013802002c1600d203c4012548448c106854850b00004d03103500440d0710305e03244007407142084a0b03098104850b05071544082e0085428034025520f400b81c4d81c3c842c95881d40050008445540104003500381700400d9a0580c2c01c1321b848070762200700040c00c0d00301140b8612a03540c00038105841e21a0103404c000503000814019802500d0070088000515010b13074081d40f10380d000551680c001c4000401210302c0f50002c56100801a16a41421203039030303680391503500140e50282c0c02141680c20030b40c0380701040100c207070b41c0601840c0903c40360500102042840300d042d0700181040d082243c40d8480d40d2402d41106070080040c0508002c0035540707040102c02d0341c030b0b180600d080070100c880541032102032a0003941e025640081400345585c45d0b07640c4800040c4050090780b540c101d4203100c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 77866593 1250 77865343 77865367
    0x909110d080f0a031b080412050304050a081605010b03060106051206040906021606050601080705040b0310050a06030b0f0301090c0b030a1103070503040b0702071a0f0415050703090609031109040206 87
    0x98501d0459a13100414519140c54802c0711003040300d81d0764000c01c41c46000700404940c0c0004001d02280160800b5607582c0c849040c90340c1003410148014105080010320300d54040301d401070810382c56028500030031544541200301030f01c610007845180c00051040c0b00903c2544168001560442c0e00100001445103e50380c81c04142d8008500b104144010154280c05021640c090300c1c3c2d11200174a012032207840c000101802c01e00890180f0f200050006c400201c40011019603c0060403005005c0c0352019500d10703004014041c0051014040c1c3c400d9511052503040501070802803561080d00c14051a003002d0b0060000e17000241000c410a884025a18a60b0043d4000314000ca907150303a0a0303074910f00342c24400d0306c601c0c02030800011980640c1c01008000d10041e9041c0c1c50150020300d1565400706da20300b040440c06203400c0010200b0b0000b010014103900100103000281c03098403000c40c0507030755210030756581020f84806017000003034000034220340c9421501315071700600c000c081d1400c2c60426285 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 77867843 1250 77866593 77866597
    0x70e06130312120b03060106050a02150f01060210140103030309210903020a05011b020f01171006140316121409010603030206280902120d05130909110d080f 69
    0xc1070700c180c0c0090b8040c1c00402c0c0c1c840761250045031000c0d03061140f10414404a507440030305110703030700c2044000701e1001013943c828460040b021150b418a4640d40c10000e402e803044150071710407000588912681c0501010b4907000d05800c2c88510200c01035660700e076850076400390010040481300340010051248a40320071041d07124620003a0b95235000441e007144180149203005800150512010740c0c5814100543e5031980300003151305682644100004c0380040c0c44240c41c0300c5101d09002031107410400c2e49506900d03804200e44150f0344454500f0100d05030405a84015140d1034000c1c05010707a01c00704240158000c40a8240d410b10000301d0000309101404130307450a45006100b81d4444004100340350b41002000c1d044428108209105d070150220700443e100c07041740c4032007050f0721040400190340d40d043d40e03007a1801803541603900d055005034000f8500c6e80a00c040d00c02901507a807011921501c03e10415442c20344c801c4012481803800b104000c10903500c2038084802c407a00b0003054110201c8880 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 77869093 1250 77867843 77867849
    0xf030a111801060c051b0603070e030c03010c0203070b0106090303020d1103040b040b09011707091202040e0303070f02010c0c020d0618060e0a02040b0f03070b03070507020a0f05031c08070e0613 85
    0x61400c403010010f20703040c1d00b010001104030503004100d5405c05c0303447c0e0782c0404032a0460000c0c1001d59032a46103402007410491400c038a0707a0305520b411500140e094000c070061205521496003180c0c4c5a807100000e8418408a010180c016804000007140d51806059003007000004c0b0002c41e8102503460012016580c0301d5003100c010842c01140c01609560000e0000c52915172210048019140ca017030001c4c42c68015202d22810b032140e20080e481903445550110500a00603001e80360b4038a80f4420141c03640c07010040c002c1c015840c000c42c0150840c415008072003640d0b8001c4c55241c140031607444035005040200050b00c3c40ea40862401c1d00050d040d0301c603804e055484100540362503445030041008507102180443d0052500002020042d80c0200790041602d640903540d03a282d07214088222028014400025000300c2c075113501144800c40c2800d19006c88200f00c0c1140c2d8407217280c43da01d640f03c20300450903a01040410011a01d454041d400c2014948006841c141c00e0060045142c8203000840d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 77870343 1250 77869093 77869097
    0xc030d050c071b050619031e02070b0c03010501020607120b0a0905180106050f091315020304020406080d1e021005010306020c06090a0f0312110d06140f030a11180106 73
    0x82ca607070070450410301501014182d41c0220948602d0600482e00301e1059030f500e490b03080c00c01156000d809020781d021610310040800014410000100010002d5020403000d44400c81808006003000b1412030480c1d050b19410781c045c08c0581c494043c15100e1000b2020b0896003152501d0504c06903803034000480004001c1d42d034020501d82400642144811880d1400d4000e0340d0420380240031070f844010304110012000d45280c580d5940b4040300328912159000001e00103226882040d525021a80103507001700e008480800c0340507510144980e903030f0544e0440c1408124802a010801090f41c5990b0100b0544d03030052303c400c10035045011040f51400d8108860982c1c0c0400d03080240b0104001c0c20354021310b400d00400e4128040d44810071196043c1d000201000b448030920f407811500f940210401401c041c1d069902d070400009088050308031400741380e004401000207080e461a00001565401d580500501519519510340001400440c0000360b0041a842d1050f103000100c41e140c83d00821180d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 77871593 1250 77870343 77870347
    0x4121106030717060d0b061e0604030c050405010b03190f1e060f08060606190201090206120f060604150309020f030703030f0f03110a030c0207080706031d0a050309060c030d050c 78
    0x902c01070f490720001c0c1c03079503010302c00b06501500080c07a8000c40303a40260b401c54681d0203003150011015200852150041d0300110041070000801414032a59012346104032000d04c00ca07030721803560300c1044c0011110380341201c010000455003030a041d03020340c840c1c4101c48408100d80030341c0c03d4180030281090201c14100c540d500010880c100120034640b016285802c060b043c0e50818000007003403801407042000b698035905103140ca0a900075417181288a40c003800e100e07200c111410048151aa0031504100c40c8282c0c000000c1031890a035040768165800d01500d000e8808e000b0b44120010101c3c060201d800400c881e41c00301c0c40e40c0d020801c0d903004610a558241c003200314010000c0030700a4070781000c4149800c0403000c103c2c4030b0102c0d050395074040c510302e0001041d050003071080340740400503405202140507011000c201030b41d05400405441c16a940918203850040000542da0307d03880e07401801d1600709202406071480c1c1400100f40070b150b00000ca900304060440403004403101074408813011500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 77872843 1250 77871593 77871617
    0xf020f0a1220070b010b0901050702060a02150c1801020c101b08131d0f0a180f080408070f050607020d2609090601020303130209070309050102030a020c0c030f03041211060307 77
    0x8203284c81c05440d400315030f1414074000340000307401405070010080c4246d40200c0c1688103d40300300090f07100e8203400030f0b00d5001c908062807404400d50004145003003034001c0041040c0c103035000003000e4050b004007400f10031916952401c1110610300b80f000b04a10140b0b01e60034132000c80c03a40d0f806403000c040c44411590780f29141c94001c21602070b14800750400410a0740810400c0307900c8000702984500496004258100f2001030004124280203000b0860070543c011041840300401c094070584904c90b049840468850619aa21440c280b1407964000d00c100520b80c0107007040710295911510445580041002144e66920b0081581001c0030340700700040749052503490001c480c0e6400400a001462550911480513001d02c02500e4004e40240a101c000c1041c4034807a6218180c0b0341d40001c0210340300c0c1880c000030406940280b1030704455105480b105c0e5400c0ca0046040140014984001d41c5400e20341822800b11000d8100c080d1540d0040e052000e0f0b00752035030402135106078130669030a0030b80d4207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 77874093 1250 77872843 77872853
    0xf020c03071203052d0408070f0b0907050604050a0b09120f0307050c0109050f0409080f070c1409010f15030b040e0105040b09011a041a0301090c06030f020f0a122007 73
    0x2001440100c10101010580040031408400300003c5d41201049100d943c0da02d0420307026034400c540000301510680054042030002a40c48a40a4280807081e1030708a0358840c02c00071030340220f0240f1b0398822140b070010040d2440103001412520320140c8003040e64000d5184882c1080f4100a00d51000e800000364136040000a02004130742007024280300c10f64034101070120b00c2d40c800156589000315560708030082070155010985000d008502007c581d070f001281f400c00d107180c40c230f07100c3d540b1004480000c9800e0b0f4902038040ca41039521080200c1200751800c94881d040e40d0002c40075109042d0340712032801c0c194596001e07014858224070004165802d040c80c20541c40400200b11900a0345001c51b502c24450350b00069451221040b5004aa100408590f03041400d240031704195141d0f28005c00c813070800174111090300455000c1d480410855001d40084000ea118401030004035030f5003009020090380c054145000c0c580150040080c01d0300c4803001d041c080000703039501c190b4038900106040003008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 77875343 1250 77874093 77874101
    0x21906050d0c1809050a06050613030501060b03070f080c0f03010f140114030a0b0a080706032909070c14010c022d1b060d050114040f0b0a06030f020c03071203 70
    0x301c0c07815810885008000e4075002046001341484251600b01090180c0c10a8201c1d5015010080c1002d55822040e1120200240d903440308582a500f062070006060714000241c80c880c040d9610b811840325004030b4101d50000c40145032803255031040c4244451583c1e20300245004e00150ba040c0a0540c2c10300b00301901244601907190b040248650440c140c0c80340c108180d80d00007548500210b0040d004000049440345260012910f61088440010b0441e5141d08a2a4030114a483c03141e4071114055a0340d00302e44a00d09003e411500200100c0c440502c19509a1500b40c0951018040807584851290a403071031081484c006070b000060b030205c0210a0300c10343d1400c62444000203801251451995112101c039801d00500b51440304203001c082d2105400c031020980b41420802066840d001c5109041c5a00d0703141a0080d4600048081440e105109045074804014100300100341ba00d00c040340075045c42d0401110440d000c0c8182080481c0400260004031320820343c40e80083d81781c2c00d00804403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 77876593 1250 77875343 77875361
    0x301140603070f030e010b041503120504030f0210030e060403020618010903080a0506011b0515130f0605060105042714010501050703180f0306090203010b030d0e040207021906050d 79
    0x40c50041062100d03582d0010203001ca0700710741d410003040802c124034146004100f5128001d4006083c900c5615070601c50030088810b4902c1a084042001c048400803600390046000047c01c0766020341e021009468090707490300041000d85404503c08800c803448a0412a045e00e0850240c0c3c00101406108442c0c21842c0516081c1c040c02000030747c0385a1401003094602826945a40b1baa900c003088007a4070076000761032509091115000410b400307144c015515840804044048500e0101103400441d0f444002c0034515040b0b22a524103a00d1500e4aa000309800340c1514140b0200b00000100b070282c000f104c3c01106208250200a000044420300a8503c0c50b4121001108454014001c580e00704040c1c550075a01894030315904210704910080b80c104582200040a003031050000801510780c02441400d07100f68000e0010003108028140ea5110b029428400b00b030038040e41c0c07180380c20540d000d0901f00c3e0000f070884403900b00c200103000442c2c0c91900100001000001d04129440c918001c101403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 77877699 1106 77876593 77876599
    0x203031201091a06090105090a090c0905040506060703140307050408011a0f030607091413020a030b1f0c03030203040302010b0316080d05070c0e060607140102030114 73
    0x2800030900c5140c0301c00341045180403c0841c000424030b02c000f000351580c0d003468141d07801590030b500306888803030700842d8a402c00602031b0083d00400c840e00304a51102000300c0e04080500c030a4400013809980102c1c02000302c000005d074030178036440c1c454240d510749036160703203c1e030384c0c216203520441d800b2144c1582820b001004810211401a258020403078144115100340d0f001d154440d03a0841d0520007050000c1000c104042c2080403101a41a006012003900701024002c83d04a0300604c070500e0009544100640c12030a21014074403820001c1c01020000f4003d8000041034003200100c02010541c000c0045010103000b500580c1030f0740d00040c04c5d10300002c1d80600c00c0700340d0030440c8600480781c440c0d0000e07030302c0d5a40104100c1d02c200e508940307400e05080c2800031482c2001d0000e045c05400280070401c1c100441c8542040b085616130180c0056070301e51408412456082c401079035184 = true := by decide +kernel

theorem cover : BRFrame.Cov 77697843 77877699 := by
  have h0 := BRFrame.cov_init 77697843
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77697843 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 77697843 ≤ n) (h2 : n < 77877699) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
