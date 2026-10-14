-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0312
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:08:06.904926+00:00
-- url     : https://prove2.me/submissions/894f7003-0870-4a5c-bf58-9b7215adec2f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 55935255 ≤ n < 56115111 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 55936505 1250 55935255 55935263
    0x503041a0a050601020c120601061404092405030115091d0307060b12070e010501140c010e0a17040b070b100308070b042105031f08190b0c0f03010605090409 69
    0x1040180c1c48016a0240b4025002a400c40e100c0350241d0007400100b80022a44a0032a805200100800c0748610098001c51408020003810140c2d6210040700351003c0300b030145d42040c50036007100040301c0785801a60081c90114001c1c0070080441885c0c00303500099000d140c000e591142c801c1c2801456a1820718000d050382e400301c913510503140c1004001482181c4440384906094200e249100f4400200c03141611a00c2c000300e17645900c0c1c08010b48541401d2480c8507034220061000c4041d100081c400c8040301003e220182500d140141b6141c908000c131107090410020b0309000c00c2c04415814800c0e10511a40a011400c0740d8036800c490400c0300078a980010110704c00060030b00104202c2c81505c9026902c03c468400800b42240c0806140900e14408480086e00038000540d03c0307071405049072a003800c03981c1950099601c8071511820000780050b901010080d94504000708030a03529260341c4080d4010980b42002e24006a001d043c1c40184941d800700b00c00407804a04030394590b0b2104488580c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 55937755 1250 55936505 55936553
    0x1e020103060f0e060a0b090901060302070501060e0f0412090605180f04020310090c0306050d020f040b10180b03060f1003021606050402010806030609030301050409050708030a03151a0703050304 85
    0xc0d0300c500d4040100c0413140c103806021050000507003a04918241c40c1003040003855203615030309040c03044000b07420403501a542c070f640340c40c400202e02c00d2410701c890040c0640100221180780c182021500c541c1130100803020072020342004c000d142e52040584600a01030040600321804540010f21009120a0b0031136100e440003080c00007a0031404c43c2ca00484e26100341c14041c0030161801601180c3d040d01c112508a9a9040c0542c0146415801418802c0000b440040c0c51540b2402080454490b46030b040e0215950403030b81c038004040101030b0401060000441851464000042000103544a00c0ca5000e81904448003c41e41c0c02901500c41c0d01c1c41c8504945c040d251a030802002802d01568283c4c045080344000c190142808500c82d4840e081d014000c0d40741d41d203000309210040111000554190281c0a80802c00e1041800181003104072503601042d2800c07202c084001301d0b600c0790300080c1d49010115a660707840c0a104203032002d107600b60a0aa84942e618242a00100c80440e559140080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 55939005 1250 55937755 55937759
    0x1030317101502070f0b0910051201030209040503120103060f0b0d0c03060e1c020106050f10080c090609040213050a060503130314070203150f0c0c0303150411210a06031e020103060f 80
    0x203d0f40001d0088000200c8030416018030723100c802e80d900d10450a03001140a90f040c0144050304000d20f0b6582c00c0381c41681224609075807003034000b10054003030300704807081e0fa151144403c2c4051903010309940080d0494034060004860707588c05610203054071004000c80d843c0c400740c5695100911150408041c5400b00140f0056a034100900800c420700415110745907409620b078450030a071000d040300e50754545403001c0b580c69840d01c80a95400600d210366214804125010450719140080d1062840081040c0050790a080c00c104021005030005003c008003481005007111010307040d5202c854145c02e024a010905920200c000d114201e0013039050b00c50844046201100d072240517125012402000d44142c54060400005202d0405000007640c014808070341280004002400c40c184014000600c0c11150f0001074400d0700040110b08085128009038406e45000403911035118a0801041041a00355515900e4110740c080100b02d1201428219030116400b90348102c0c0900704959800204070303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 55940255 1250 55939005 55939019
    0x14030a0c0311091501020a06150b0a21050f0411010c02210c010203030705070b1905100303090b03190c020c12010b030c0a030314030a0908040303050301030317101502070f 75
    0x2000b044102405580d1000016160821500403108140b0050b40030b049070750768948030400502a400e403141360841d5030450008041861000600d01130030581ca48a22003501c0b0800140f90100007403003c2201070600e01089a15020740304002c1e40300e984032603100412500d05004807040712a08900a4011130101284800e000b24803910350ba180b0411400c03140503d428400480c3c40e07010030b540107008a0f40c24011300c00003446d02c1c81c1159116900f81c0110645a00318800070742600c03003d07100e424041909000038020f160340040c0741c40103000c50240c03d6180d414510030303003c443c40307640c006819455511400307031070124070900880381440401084201414103000310301e402054565401c900c244548a50140c4c20f050100c80360f42101c0d0141c403a0383c2000c0c015100030103294001003c050301340366501c0c1e05100040340c21000c1e0001e035000ba91583e45942c110310b0040c003464540d02c0081500303901d10301041000901c15a20509882c07500c8852002d0340584002070b0b1510105800c001c1510005620208480d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 55941505 1250 55940255 55940273
    0x120b040b151c06020f18031002030601080a0c02030d1a0406080609060403050f161110180b0c010b031504110a0b030a0b060405060c0d080c0c060114030a0c03 69
    0x9502036401003055460350910198990540042180c000340180200e0004428415815030454001d070805441c01e0f041c0d4400100301d601030240940b0250902c641003140f805c08012402503c5521081140345080010010f4807200008111850341c80d242d02428402034030034401e440e10314041103000d05c0f091459010b00ba08184800c1c02143c0150310740400020b00c0301c1e0018086014a4440d805403a40e91180e803412075003603024464130b28050f80104407003680c440001c003a094a89006d00701310340045a0400030031102800d260f8101080115041101400d44048a1500c0841d95040c004654031000050450301605a450078298140030b425070400c56495816000740c0702c0c0c1c1c41050340c006482030b64401c02922021a02841c0c100c04024000501c400c07400703078003500c0c0b100001050f050805984000043c480c0d4000011140107030000c0d1a9012015080b407011a00404041c40d0503060208840e149030303540805124001c001c140a06041040d61000c3c408400e12a4000403a0407030a0380360705140b440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 55942755 1250 55941505 55941511
    0x30706050405010b03010c050d020307110706090303080a06060e01111626030a1205070c0b07021509010b01050a080604020403081b1204140904061e0b120607080402060310120b 77
    0x515420b00c800001c00e40b03010307c1201c010301461784a0360304000d90382041038001e400c01003003982440701a00e21068811010000240141415920481d40390300318600200088000344c1400300040c14090180300c10398000200024017402841c00109064000180514003500220040e42c4c3d1b0281c0400495180c03011b950380101203840310840300c800c0d520507100036038a00c540c184036030006040e5040e07413522400c00d0b004160459400e05e099480100c20f40c85e601064070701035603c072000d680b1046078500710040c0c51885640c42014040200005c094490020304a40300e8070100000300144880050312660b550360582d400b03140c00020864480b84c8807c041c002000c2d40d00c6600c000303441003540c04407d80e0351324400c0750140e52004a06800c034a40d520309000c00200701420841d88143c40d5107621001c1502d11480c012100d285400c0072441e40d00d0b580600c244180c40038461a180c0e0400c204118485d500040e4042d00150b041e03d00c1a41d81daa1051440c1140b141500800a0611950170400c1400440000180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 55944005 1250 55942755 55942763
    0x30605130605040e06010b03010b0a03060302061c05070905060d021608160c0e150906040902030105040c140d05070b03091005090c010311130902030c0d060b0a08010e010e0c09040e0307060504 84
    0x21280c0384c01c1489a650200740f095821140d010001803090f585000301505126826040201d1090380726030009650350000903900041c40e621000c095900095401143d8005c0140d040c00e10000f41000c010030f8061080b81d1f41e01c4000d03900000d24065a00000724004805030f00481101d403103e54031480b40c41500b0f0001d0081d940c0da120b003d07011404000564080340514440e03082e82d0a4900b401084c0840c85c40c0040c0819481940e43d4401409038a00b80550351146105842c3ca04e003e9040407040b6040c000100300031802070045a170010f0004000192041c1900d40440ca0310391607a54044466150a0b1401d0038111814180070901003824030004003c556540c09803814408000010f4640481d405080700e2550402900704007006040d445900030340e080100202c01514002c006001841655116801a80745180001c0c2583c2410303440030180c4d0141c05100003500703403545007209a241000014101c0006440001200c08403940c8941c08400e51050314000d503a250001400c005e40100302c00c4a0541e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 55945255 1250 55944005 55944011
    0x3050114070f0509010c020f04021c1a010203040504051b0703080910020c06070c080d060807090e0a02011e180b0901030b04051b070203010204080f0f0706020c0105070b0703060513060504 82
    0x150700503002d681c0c0c040d003180140c2c1d201400c000c20180112803000a04205980005159543d056162250b00081c100e589459414869211000b4070403000c1ba0003001100e404c910f0480e0358214241c4c0e000c0704442c2200c40440d00408c041c2c42e03038038580340c1e01560100c40b14008070700050310804040e04061014826034220040d100f1103071035407104000380c3c07254000000c52078001400042100d4007032a102d048403400341081c6814a050050404102da55582000b40c4660100f001040741e1081402815076003400070000c0e00c0c520b1055400a001c856103151040020006200b01244091041d602a004109003c0483c03102d2070784e403407209103141c1c8080000d82c00070342030100075020350601e4015035016802d2481c2408400104840c0c901194114070000c0768155000c000c0017610140421036280c450300c0100207800c0c60708401007520314084031030344104295004650450510b0780c00074185d4003091b404c4107450902d40d039100e200324000d0103d070708110b07031141000540504940003a4000015103105642c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 55946505 1250 55945255 55945261
    0x100c0f211101060e070c060c031113180216020108041104050103030804020102100504030e0f03010b060403060203060108010f0e0c0c15041211070b030c09060c01090807170c060f090c030703050114 86
    0x10f4603d403000c8031505c002c504514040320010300607500c801d0030740e00f41c0c2ca4001244000300189619540c80400740c2c2d6000900d401c001c1c425244c040000094041c104107045240040200c4103840e111aa03000213414011140005424011100b10040b0314103002001008207603124940501102c20554050f8014030610f4968081c070049403040600440e096166031142c00075403410080040c81b64007800b0703015500c0c1d00b4440220740300c240240014520810002d40c40b46800c01c0018031b0f8440503485003151020001c0d04100c4805011081034002c290644510fa880030b40f410340924160581103000858420f0324204401d025400b0307201d104014055941c60480d4131041042030fa5540a40900780030240c08002040610030b40800070b040010b0040c0440303080c44482c00e15982140d035500402c1e100480d0014030803040101006000100407071542e210380c10402038000b07166480c540201080c4a80741c60324081005400100080070181000804403118240c40303281181c0680881c038171a240480c031807004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 55947755 1250 55946505 55946519
    0x14030409060e04050a1704121203150f05060d0902030a0302010f0f0209030712020a230f0409050316020406090207140105150330030106050c0705100c0f21110106 71
    0x40f03014603084001040c1070f4111383c8030f4445036452411900030001003044001041a8510a03e4490074003d1000030f9882c1800303030001d802e490505000e44d201004a003c140b000c540d04415480030303070300240d80c8261141c620040117402491a1040070350b1510602c04441c04050f41500700c0d5811560b200700900070614031b80d03060016406041e40031981034200c0c68052054403001e1011030b5040740000e0002c0502551810768940c50403007680c1c140a100b2281800710800d0030698500582c400f025101084a074102d40c40d15612805180d52644150000780c114205560f02e84d00418013414403070f41704541e200e031640b5185030003103110040300c1502e50a100000e050020044100505a10007502030110761960004480711004070300d00c50401c0304612160010801e50020283d40a040b840d21a00d41d01c07010181d500386410900e610640c801e5050700704803041d41b988409580c000c01e520099450f0440c40c2440d0102494100f981c2e0701c14032100a4405440e02503000759080d5200c01d03484c000300815034035544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 55949005 1250 55947755 55947779
    0x6030605031f020f121b18060310090501060201021218060c0304030c0c0f0302010221040b0a0201020d15030b0f010602031206030c0d120e0306061e010504031403040906 74
    0x40340341d60540010710241c4041c0c44886502120b91038030200103103081c0c00e4855182e22034016812010070000c030700c010003c804030038650310440c1c44012910b00f401d11400b110040c903041c61640d103042c040e1502201013041440003130130000150234802e030288203540e102c1d00b0081c000d4002c8c00c032070400d013a030000104650f42c2502120508081c8180302900c40c80c1e03982080e0f840f82d030384003030b10490411003044c01c00404240d520f849000541400c0c2c8482c6096442e50000902d0210045404495080144103118841c1d040104441c101d4140f00b1030680c54158903802640280124001b501d0b200782007045c0c02c40042e00c04a9540140c0344034980c0010280c49055260b44c40c00000d0203500c001d6132042064058034001802d0f12588084018111000610041c011610045c204001241c0c003003041050104031741c0e0000c81014100d4000d80040c0440d2030100002011044080d890100122890341c900c0c1d06079104104640107140c0280c1140c0e642c420244485603203a00900c18518000d06d0108003042d4008440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 55950255 1250 55949005 55949009
    0xb01051206010305130803070906030e030918070c060f0506010212040b0406030207082109010f14040b04060b060a0c02010e0a03020108180304120c0302030712080301150e0604080105060a060306 85
    0x205a00d0407907803640010340040c0000380581030a4800d0f4510714002540c00b800451066072190b80305560f103850000c019041d904070102c0c0d543c40b50810311082c0c6164860407502c801c0c03140c400084810940701e07010141d43c0c42c808882c0c007a1265040c9907420303e07144a982c200d01d003d41020390884035129100f16050203a406180074030709498000300400c00c01c040c8a500078041079030041042d1403608032050303001c030a0720a000c801800303003070706007010040103040c00e1191030b802850840c0b0600100c000141c0303107281428000e00003402c01807400040f60a001c0715610034641480050070613541c410354140003520a8842c1c030346c12030020b40c0705c0e40c0011132401c0c103568407401c030f9078180c4030a0686d440d1800c0c5c0210842c0240c5801c00180f205204c00144111003240c00d410081c000c6001e4440e083c114010306041541e1358000c0d0501d628100850f40000e5007071000c5a044910180070303e02d0403246400100d83e4071412955950b8800004600460030701c0341984140d001d40412101607501c2da41c0c8002c10740c160b80041c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 55951505 1250 55950255 55950277
    0x131401051c0b13020a0206071d01020d3e2e0e0109080d0b0a0803190c03020c0603010e0106030506040b03120c0307020405010b091e10030905150a020c010b0105 70
    0x904040c010074421600b01c940d1068004100e012040040c0d2004000c0b81c01c04e600c0e40300103912500c00e01806c55040400c0c0d0000742d11a400208901d44c080002035501c840c02da00d82c40401200094141c02a4002034100c3d1103044510828844000c1e02c070805a8000f07850702500a280c00350700968000300b0f100d00b401d446030009043c2c00040f031030600c003031076401002d03400102245552a51080c10009202b20700500744e10010050005802403000140701c8050740307541060140740e0042149521401d20407020800c2c4107518600100c41010030b2134100d0602001e2003a0641004011001146221501110078180e611596041103a55030320001c00042c0c80600c56195010780011040010141349000204210310810302260f203003070070550200d400c072002640500103507100481d400403d031070072038103480f018648412205039031801c01000407501d03034202e2200024107580758184800c200b0240410b01c80c0111049205e0003d1070015080790207940201c1103054107519102450010798040c2050320011114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 55952755 1250 55951505 55951537
    0x15090a0201080403120c03020301140a0302030a17070804081005130b0c0a0318150509340e0702010c110d051209010603021c0501060b04120b04020402090613140105 72
    0x185400660780c0d1200070708140c0030003d80160b5002d922046000b04d800280207540c0c010307070702c1d0324000000706902e201054003031203110b80600820160768009924403401e6000305c0c54582c0c1e02c000c040c0d114918455680000e0083e000410006441030000c00c0c0c1c1240910443c40500c4596641c04228400c4e80c0c484400411000050002c9600d101c2544c1c09803030140c01c9414000303078000312044005090041c01d00115107002c90280c00c1c0c6507480f842e000780c98110703950f80700402c0079034410200e54020303240401004020401543e50200100c0740890b401006005007619496541031420000303000e411001000008600c5544a02d60303100e9000895030031500c000c0d581c450404100715541c040e00035000d003102d084c564032032402101607600c0003214100c03041206504050704a491400c1400d4a840307030f12480d2041d001b8072041040159000f01a100c07254400f441146541d150710008000340205000c1a4102d0f0020481346282080f0a000030240d4034059200550b81c1400d00045515101c4c3d03034205459008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 55954005 1250 55952755 55952773
    0xf110a1704020303040f0b03160906081504020909010e040606051c0201030e1e030c0c010f0e0118090e0a050f0a030917120f04050907020a11011b0b0108030c1509 71
    0x103503560150424402401c1da80350a42da99544d8512039881d82220044880c00002e000b0441200110088041d1081c00c0042050386080c0000d040d030b880c0101004484122103d488280d6505c6904551a4400041c90184503503120480203001190484040b80c14910300341c3e020942d03280c1400d100e5034040c240500703403a04103600d07801140900301c0813032850b0b041c1c40340b4212a0003a085401c00040c4142d01c0100079a00c40e00c0840c0c41c1440c108040010b070341403090038044204d60b25440a01c0318005882802c000200206c054049034800840fa44040c0407107140440013034503c1c10109520000c131340240201ca03200d0346124100307926450103990040205200304001c01c16407440c50581c0b00c50400d0482a038103000360002d07150280da07000e082c0c600140031000400307110030714113034440c103400407618402002c00403600c0e500c0b108031981c22000720b8140101c07403c006120b00d05080e01c281ca601d921800001d501d503591360440d40d030f0b0b0f0000d0800d07071301c0c0b070007110b4001c001c2508200e001c03441140b00c5401403004070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 55955255 1250 55954005 55954037
    0x50307030c14030a1805060108061f060503160e03010e1011040e011e090203040f1a0f01060e0f0415031112070311040e0a05060f0105060f030105061b07090f110a 71
    0x1519018405c0c00f02046030480085071003404039134001c1c9241070150060f45002e409204411030034014072907003a0305044050003490707403103015a5402080740e010034030f40b014180c800b5a11202d280c0d1803164950f081c501c070742c20b040340040b800307035186114890148601c0043c0c5403407803418012401451205c0f000040100900d1b01e1504030090110b0004071401c1c01551101c0850050340e00480e415910070760175440000800c06d03404084c1022400c09269040c240c10140e144054866040c4a10020405100740c1e80307036159140109014010382c001c10401c58828900c40d5a001ca0780e2510080d101428102c044806904043c1d2038082d03403042c060040c01e002410740e6100c0100f0003680347c159030400d5880c207101c1c1c42e9100802050300650301601c01010b940c5080781031861344070416000a030003410107200c07442c1f0504101056a040d03036800c55403280c941e041c850600b51710210520305400b085c42034690004001a0a500c484003550201c4418031407418020071100c0300d4800d8802c9880080c0044000034103513 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 55956505 1250 55955255 55955261
    0x140102060402041812080103050607030e0c13061203080406150501050f030a06050402030a0b03011a010c1e0602030718050105210711100c02010e0c0306010b0309010615050307030c14030a 82
    0x104218401044590400c1c1d01c905c403030500380d055550086801440140203203c3c04004141d400388403450f00707012051030142e1258554411024640c000d4001c001c031083e1000302c54000d031b000340002c40320300c3d9100303019810002c2c0303581e5007520155500d40c5000e010401002c0290078079000d0f1030041e12014601061203003407008941c402841c02100b1a0343d141d011507260b49500046002e1140e80b140411040303186810142107441c02200c4103440120070507240d00698000780d00694103508110075041d2500c034807495030b03a01c0b60040c500030600e40c130000401084d10b811603021400d41028440071080709403500c0042d2128810414080000c1040b441072009810107241800c1e441030151500d1002074015841c00c40c60301ca07440308004d40e050744400550b080150709200d00c1c41c3e0712354008028005020418082500c65906008002c0500300000000d024401c0940000d4000c211600c401044828003040051164006882e40d100080c1811142103603a44a003401d00080111811520b24544030ba075041c03002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 55957755 1250 55956505 55956521
    0x1602030412030e0a0311120607210b120303041209030507030b180d03020a020c0a0b030a0b030307050a05060105100309030207090c170108010f0b030a080301060309020f09071814010206040204 84
    0x10000c00b2100700c3d403142c540201c0381005500c900310384559905040c08200640800d0120384116501220421442540c000b020911450f102c0c1000c1038640150518200034080d0290325640040e920400c05680d500c0c00001184268000c8031001100304140c98100c5002d407281c07101411070b501040040c0301107142040c55940000d815120042c417400460079190409103080b00c0c1c078011a03400b1482c007003c10f805008004141108862039a81d0034100138a0751051300014100765a503958031455401240c8080046484603508002150486142d5160145d940ca074240607550007288000e02030300d4a14040e000d0b840c1d0b0f0980c1178010303240032400c2000210041614611071820401c0d82c04501000e1482180524042c10766600041020349000a915041e0380b0b001b01ca00e070099000c44001c00214582009a07415100b1618002c510601035000050603810414030b0141d00004102c02d00c00540e410502c066220003c0e00b480403003580d584e03100c0c040221840645980540c00140002d001844c3c180e001a034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 55959005 1250 55957755 55957757
    0x604050c130e0d0807030c091a0c150c0d0c0309030206041101020309060a03050a0605032b030219020a050606010815010c0c080d02030406020f010506010903080904110c15160203041203 81
    0x82d0600e00c460341186070501c01c0d100c0f5400b040700c0300180b10306560f043c0241d500000441c10003030755051802d2041c40c0c0100010f01c40b1200c424010461242d90401806110250308640201640d00e00b020b1124a066030b00040e170590100740b80074215001c0500074025001d50384d8254010300300c55956078655034084190b00e94242e04600040003c0c91071039031075002070060303040c2c01c1e41e00107428903140002d00c049800035001248240e21040b80800c0c0381d0707604840c0c0c0c02442c400b2212a2061248454150040c1c004c41d40d0424850504150f09070200e41c2c0000c07501c84079030080046801c9610780300015101c0e14025500c1030710944905052440d9540140400c520030303407090980395034083c0d45150b400d08000744902e2907c0142c00000b4200000d580c1000f0083c0106a200c000300700703d06181c00083c000765014400103041e42c001280c80d2200350b483c1d510600040380800a00c03503856405800c01c41e01c1e0710740c0189074200440880d0103c0d0311800026040010360506030011071070507040001c088a0a003034200228 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 55960255 1250 55959005 55959011
    0xb0a0206060a0e0f06220209121204150201110d0911090417090d0f0c0f0e010e0f091005090c180603030315121b04110a020c2b15060501020604050c13 66
    0x44c04480590207141900310615001610b407423180e410000079404814802c1c5141e4032601c88004218020000c80d000c580111002000a04002c8826409001800504c50400d000442c2d0040540f810390094810785105182c0380090b16681e00400100c490143e030040c0020134621140682d224040e4002c040c1054014407107000e450060b91561092002c080044803502d440740c20402540f152907280c58060500300b0507800981d07040444606503d030b030007000d1044c8402c54034040b0342895000d2044002c06000328070140000d24040010f50394440340d0040d511702454071044800041030700202c60034080c0900401561454844a6503000c610102c04030180e480341d01c40441c0800344808005140c80030403250a06d040c8180018104400c41d82c1c41901a0301c1001c00700b00001c01694017140030401864111080d07140c11011448160352091442581a001d440d441e00d560107000418070617440d5000f40b020180030850303d07040120380b07846041e01e0040c4183d01c00d06840d5058500004215444074a0318400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 55961505 1250 55960255 55960279
    0x16031404030b040c03020a08060c0a081302101809020708090d0201030e0a120806100e100201020c030c0307020307080106030b071d060406050d06050102010c05072a0b0a0206060a0e0f06 81
    0x3504901a03d04449400c030300c0e1400c104500340303070600d2801052540054403a600d01615488010b20510042804000380c00780001c040314400d00c0c0300381c2e01e0398002e04070012600d2074503009413009014001c0003004005801001440b2034840c001c445c03005078001e400e54248102d075414000300380701c1c0c130004038140341d12800c24116411040041c084118000c2002444800411030090000403002c0c02c80c0c0d018a80784028104182e0700115403d41512098076100701045045404038028007404241e2104c82c000040e000050443c00409000340d903000302d0985040c48c0c2d444014500f00c405c00d00c8028032003640348001070b4100707008090413400d248a6075404403100c25100000b035032070b5020360410804107c020410740040459403140201520081c00204101d208440002e4624014094000c00f2000a01c0c440f4203c01c4c4039003954401c20500480030031001e07465000f0070000790031048520005100d0407000444d00d1411894110845900400c0e000041e02c0342100c0400307020f40100030365080104010301e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 55962755 1250 55961505 55961513
    0xa080906330d1b0e06060a0804050f0706020706080f01030506070f030204080303040c03030e10050f0f07050f030a080a1505040c050c060f0105030f010902030c0607030908071d010b1603140403 84
    0x3110b804203105000c541003803070500c040c112020303215030015080c00c5000300030408961a24001c66a404034242424412540c507481c11614011488076240701070301480500196054002950310151a45c913264103590799a04401e031340c580b003001d2202810300c2c0d0205001c101014058070448840352400d2030007528050311104064603540c410f80e01201d0b141c0138a8000c00605030300c10064401d980048070b88410346807207914024228020403c40641034000060f070304602c0c0121404540c140755110003519221884125800c5e209d800c0b0400c8040801c6012000901840c06841841c015000a15401e0001410102403000900000342058140641081840c0000c4820040305100e414164014400c1e0342c1440141402c090100201607290b0b0f043c021500700503500070030000b01681041ea4140e03115080c43c24101c4030303141c0e694801100d134007a140c8081000c9103680240c90b150085e603503045880b07907a980c05c5543c4030300c80c0c5051000700020040208002a1051217055004c0600500030b80c100754407178071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 55964005 1250 55962755 55962769
    0xd150f0311010f0c020102060403050306041d010c020d020304030308040308060105250309080d05090405060406030803040f0b060121090302070801111e1201170a14030a08090633 78
    0x1900d10008044250304290f03030101d060030301800070f0b00d88090f600c401580041d50b244006080141404004000a2802e0700d45a010080c031110742030541030003520221a0034000d207d0320700c241e801409003034540411540000126001c4a40c5552035080e030b56181c6c2c07400c0394681c2002d4042c60421000300641030b280c01c034920507440c0c81000d4611454500c0130600d0302520085123580a1000c64005002515071a038100d01034455415080c1c2e408691691000009001481d20341c00041294070040144424091102d040d1070813544501d2040d01c06480e1640151291036241c40441c01e800c0d00b94101154841c203d130000f04409110780101c4601a45900c0020309507030240c028000300c0540450354502c08102400060b040c810003040183c0340c031070b5400b540c10468205002d80c070b08916000f081001c44c0001009416441c0742c011002030a5062a80c4042d6102e0748540c90410001d108040400c02400010604500504d40c2e44580c1c040d6030031400001d150644c8007155401c0300c9466814a501c15100c1300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 55965255 1250 55964005 55964009
    0x30f020f040311030d210905030702060a02070603050c030f040201050c160621060b220801110306040506030609061306090803010303020102040f0e10180906090506011502030f0d150f 80
    0x180100c84181089000e0520b400950030807071701048084100c1d840c4121500183e40140350844801184e12003503410211b107988100400203420010004034010307610750110b0200306543c041d039003e0000e40c4945050a00c50b000540703045801c081b4500100700150301510080c450a603851090311a000f1080041d41c41c080070590111012601c0f03038900303c0c2410312414503000c507580c0c0d81600300300c03c50170050f4200c03090045030048144c80c9000707443c4007008400007843e00001d06200000f07016442d000c014502c1c481d041a68081d0045003044d001c10000d18020400328440d100b1a0000d10007a035640c190013040e0f2022001c241c0320107a03685031040c04a025003000303602031801398002613950b901c0c1240b82c80303900c7c4161f400200100c0c00b220901c44422902c00c1440c0c101d40e211b01d8122026050042103074020b084c0340348010801842c0042d11810403001003142c904a0710868400000d8040c0464140c1e180c0c031404c29140800e10040044e10140011a8008201c08400e0081d084606454001701d111950140d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 55966505 1250 55965255 55965263
    0x150d0c08010e011116082802030403031707170a060305010203090606030d0c0b0408070822050109050a03080d1119030e060106090302060d0b060c0a0c0e010501030b0d03030f020f0403 80
    0x1541c06014802c02400340000100e0021005842e02c442c03500380e0b1104102004000f40009000140355070500008600701c07403403034182061200c0c00e40403468065666402444101c0c00304920414500081066103000d5124004545642da01003440e0300d051004035000502007883c0a0795104003001199091020394465020350009104e0b0b420248205032914440c1810602000741d00b100f02c00000b108a172800d80c2140c3d00c0410113880712907903d4040c0781c07401880005c01320040295183c07500c17a5422440030088802c2070700c4d0010043d448400780901603000d4000580031031070400a8038610050f607030200340c40c000100c05170360030100034419a110726800b00b01c1c134400081c1c0701c001c0038170000014481280140320a05010820b41c1c60750340810101e015107099448050750301d580c48502919500216030110401c801540c2c49108245400c1d11101003e02410383d00c00074441c0003241d1135010b44100813100c2002060400c0e1903025550132005050000d812448540d002c0c812003500c1221100580091441 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 55967755 1250 55966505 55966511
    0x16030303091a0103030504150903060509030304030f0905030d050705010b191e0e0415151d0a090f08070f02040906050a0f050411100513060306050114090108150d0c0801 74
    0xd00d04104030030040b0810200051007048004000080d0400229403c03100d50f031a01c3c60307211b034841400f0f03103503900305500160159040108014640c0c1c000300055129602c81c0e00c071584851882c2408907802500e9001e150b4142d4031403020342a01d640118045d01402d4030910010580100503808103155011214841c00820007401007130001ba04100e000c144140c602125010929150050a960000d009840a40b0034449601140380c0708046401c40c00041c0000c005030208a5a030360b281034601e032010130846045903035650105000b902c031070151300b801e00e8218441ca000c3c401642c82d804403a9200074000c4419000d4203507003c005850307a0141101030341c0070f01d03400615840c000464001fa2110400090340f064038103801c2100240000e4089141c260301600c0240d8038141080041d031719407181d130741100e000e801c103614002100c80d0316030410011b9841c2a130f99642c0d10200c1202000c3d0074029804906d000c81c00d44000117009414403421100c0514008010200b58040c5807241c2c460308503903411508450351 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 55969005 1250 55967755 55967771
    0x30a12180b0304080703031a0901080c01020106050a0f09050702031207030911030a02011202030a0f110405030c030703051b040209060703020616090f090e1203070c0302160b180316030303 82
    0x8403030510200205000801c4034614502580c484165128101740241450fa9815044401450104440e207100d20050000c0c1d042d5612084204d54450702c0e0510540198240480451f05041100c0c0c0942286e520300704c040c85440c2001b421a024200041505085100c103021303900c8040440c0c9881c6003d80c00c9038900245d40001400c100031030300101d1603800d001c1e500071040c3e640140d90191041c17107076801e40f8000580f00e4a400001d0b00240c4507000c0a02115800d181d082c500c0f82051a00900c122a021000c903240d0b8200042815103456171880701408607008000000f0300d0101c8035610351460240100010701d0500038000048041d0403d20054005a00007c100500604203101e442410702d82d500381400c542c0d107421140514000c01e4000d10103015100c0e103040307120b41820030011004150303545d800c948a00d040e00c07000706450386101c0c0503001031007120601c1b00881c0d0400e4040703080c0c4408d110b0841c03034540c0c0300c60f8004542044900180d0140326010351058a92100303009400510b22980d00498101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 55970255 1250 55969005 55969037
    0x30b03060f07090b090904021909020403080d05010f08030f03151309030f23180d080307030b01051204030c03090504050a060f080705090123090c0c060f10050f030a12 73
    0xf80349410502c1d00c0030003040002c0080c0c6ea0300001300d07172080d4102c80d08412211030110f40c5040c0901c551240d03c4090000c2004010011203201401e420342c0940820030003682d071081c0b2405986800d10803820b098100b084100030713041d00e4100460b072040d51103185001414040d0b0208908004008100c1100742d6107060020400da0b014861044080840c5058412280700c036041180110b8505540702d10200300184490605441502c2d041034030000600d20f0140750a0ba00348401981c1c000c540540c0004c2c9000040b2040c0e40c003a00980340201e0007a0504c40003565169800e40300409419401d5050018030100001d1303aa0b69800750741d10900c001d00020801a2038110041408001d1360040c000742c0d04000414455500d0390140641150081e04010012224100500800c80d4005810540115008003042185031062004080c884240b4003124042c3e07594a40c003110300316040c1c65a80c03400441040400c407a16000d8110340c0360020040c2a6010b80c40c4503510300c940c0c138408128200c040f403015000010030b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 55971505 1250 55970255 55970267
    0xe06040312140601090902070c0801020a03061503150509060303190909110304050a0605060d1403041404020903070b0c0f0703060e0c090915040305070b0405010b090109020405030601050d03030b03060f07 89
    0x2600d00509402c03260408a00280000c640c90151580c1d455001c1890001d10541c42e210800818101c4021036a40c503805c1c1c401009052540100303040340306070310b906400d468481d00c0f0320120545045090359400e0f05140c100214204042d003180d80c584401d00045250301c1900401c070f051200c4680341d1154207468142c00e442030703071910450100030650510420020840125400000540c07051001a031581c8001c005100308000c4076028100e240907485074805020000010810303594501c11044140b445c08003000140d104590801ea00340e0403214041100d0b449070405000c1950321002981d001415503800680b40801c1641300340c0e0165120403811501c001c052014116400054410182d6880c14140303051351212242c0b003000496688200140505100d0b6040e1240035a002e1040012802e040c00e007a0301070540c00010074822000d20000186006d0f40d84219012180d024002e052a82c1c07a1004001000d004448140c05040d01c40d054940b0f1540c081c04858460b07058070340720108a08000ea002003038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 55972755 1250 55971505 55971521
    0xc0f02131a010e09040605040c03170d27020906040204051512070203030702070611030403020a03050f07090b010c0308060d0803190506010302090d0209100801110403140d080117010e06040312 84
    0x10b00552400418036612100d0041c0d521540150f1b000c989902c0741d1a1021005039280d002505070072000259484200721200200201e005845050010541301010522000442c880c03010030402a5501c080c014141010041c6d4441c02c0240011b0138555aa0701048041417071414584401100042c040580780084080c0713600318a00e44010740c2540b805100195641c4001c0c06410144038050101c0c1c04418070030800c860281d076003e02544001603892170855510000b014030503400e40184480841e5103045440b03120501e24050f920404458901d480643d0071080c0a0482500310548a4050700802c0c504c000840c05014039110400c0c03014800c0b030078142101d401034041c9040600400c003082c01030340c596460b12052501124680643e8036000006401400c15a202c1c0d001d9500b015000c040c1c115408015200300ca00402135405003e14007440543c45000c094480d90204580340014400e06410150140618a880000103805030103a0300b0b103458041c00300c4d801c6000820740100c0c2c0256000d14010781072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 55974005 1250 55972755 55972757
    0x190504021c1404230109050a111e09070f230901080c03010e0408030c0d05090714010801030c12050f0703110a0b09011205071b050706030c0203031005010c0f02131a01 73
    0x2205080503074a4400c80024000340840c9103000792000b80d080c0da000e502c03686d0981d505c031007141e44c03603226441e201c003240b440b860049120304000c0700d10400c000d007041041488030070010859171f131a984050040d03d1401101c0da50404201d2212106104440c0782400c01d580c582c882c3c4241600c2e00380c824001403c18000400210f01004144010040365110038100c40d00103074403403070b0552070365900030144489015103461043c072581004144140d404000c42c1100c00d840d01002c3c00c0c06200340b03506c01551111000c0c030000b44194003c40c030801514210007030603102c035441141900d900072110300c80b0501d0610f1a0300166421826040c510300c01d40740580c52035004001c0314500c81c1c14003030250300291140740700c085e0301c1c040701d620380002a805034850400d501214645001c07445101d40030703040042d0740e81014011040880e14007801603810700d0000007501d210350030840084c2c1a06050500441d41d10454003000c8a55085000c020001a5030350787d201205101407480000d030540f03082e088840b0002604004e24 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 55975255 1250 55974005 55974041
    0xc070306060b070c030209070c061802030c040b06030604090503070f0507061803030206070804020a0f090902040b010305090a08070f0b090303060102011b0518060d0603080a0915080105190504021c 86
    0x43c0000303907888140403c0b0f03501125000115540c0302400c0c0c94208888100a06032440d00703030440300b074260394441180748500a0b401c0b10100c003008014407049600b1507049070351140e800c0c000124680b6081e00030103641c1e0300c1041030300c0c10300b6840e0f40c9064842002e801d0890762078118034401c0c0001c0b81d2203d60a0320f991841000720580c581341d5280079458800240c86c8200b041900000607003591110441072004002c9420310080c0b441c1c0d1b580105008080c0d901c1c0032482282000707034080441d0302c00c4c00b40500600b03551010f4101c9405a58483d407440c0d020000071542140c1040650012507610a0550301c10f440c031502456481c03034a44002801c40c1c0310f0340c1030384540c092069210a040d0340c0c80401c0c1e03900203c03088a940c21440d03110000503214018000031012040c149040030042150039009482c00e0103884d22020640d640b0741c0088001c1c0a9400805030010f42442c00401692401c1010350001c40c1c413101c6040141c1e0340340d00115090f607010034500100350714200d5590703845507810f01c42d2840d494001d41a503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 55976505 1250 55975255 55975267
    0x204020f0712090e1801110a05131208030f04050f03070c08190804090e0304051003060e16080406050402040209100f0f14041401021606030504060b0906010c06020a140c070306060b 79
    0xa2001c40016003108045040242c0d103051929003540103814030314600075501d441c1c01c156040280070340c1c013090302c60014422480d80010001c031500f03400049194000645401c690302c41c007506200e40c4005206803451e11948a24040e002c0080c001040598001e840503a000740c00e04420600d13140198100340c00c9003206000c02e03004a0746d1030342601d041e51268072012030568940800f1a195002e20303001294003160101c1446202038255100c0421500030708046400b503680c0c60070100b00000a601800c1c042a4040e00190000d00c0e0380c4d102540c01071000f4401820140000082414005900e0981c000b0a041c0b108489034103402001c1c20034403e4051500e000610350480c038480b414042d6210300468440c00c264490b003181e00900c5400d03108002c18108041c3c840e034cd15001400742c03205480684010b440c240340d04016007801d00e105480b801042e1210300309118560364101c02580200100010407034052046004014900004c00a84921900800b0b00904500b040021a25103500c941541d0008003c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 55977755 1250 55976505 55976519
    0x80106051f0e0103051503010e0606031903050301090b01030e01020309010c11070602150406062412050603030304150e0a08030406063302010b06030403020a050706020c060d020c01090204020f071209 87
    0x400c1c2101d4400f80f81c00710301d07900c1b40c0c0c0340895044000d46403a80c1c15400d19090305200d0200203052441208101e0480380c6061502d0400d40c03802da4040d10203000100200700600c940c9407150022009500c0615000801c2c45071443d1403422030f01300341e824044594480011031807555014010500e4010044d010340151490100082e542c0c2c00a5a0407440d02107800c00024240304060340908024035000608110507554449941d8100401c4020303100481c1194201860781c07070b1240700c0e103407084d0009001145152140d440303603c0026004880c0490894072003180d4081c1810900a40c40c0c2984110481d98503820140b40920580312035420a002c4800030b1a50555004640c0b00f10a1014401009201c400f61074500d00f02c0c0580b40968180e504610004244020140c2c00510701c00f005009800769100300781c840d241241c80b03200303292500c0e600600910010544911039801000b00c2c0c204130000243d0070700a640820183d80149465801d10000450404244002c059482903041214917200c203580d07040c41c2ca = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 55979005 1250 55977755 55977767
    0xd0f030e0a21022b14070803040f0909060e0304090c030501050303191409030d0903060e010e0705040e0c0406030f1505060d33061503060302060a0e150301080106051f 73
    0x2801074800c00401c0d0444441d540c0c40d0010181060006100c4c8080720380e203003401d015860402e8195066880f0340c07a0009118440481524245c0309007081c04100340d854030200001520501074284c512559a41041294560800c003c0005103200d69000c02d8166200c0340103422100141d106c01c1c0240c008100d08080702d401002c80d00b21200c110708207000070311202502c2c0c08641c0034001070310740c141c03044c0b81116203900c0d00080b9150459100300010310002c15002e20103400e980ba00c0081e05840d9010328818051403919400202c00c07a030301c030401c80701c00480220000381a1500b5500a0300c641c034244085005100b00c4c0b0085409640c104d00c0c0910281c00c241c4040f44080c80489030150070f803240380507074a6004d460901b03003d0000300060b12542c1050b0603140707140010041d910078503c41d0b00d024603211492034001c0c0684000c5070340081069051840254040c1c9032920b2070b0408580c00b08040c441d08000350b11038400796010340544800090740741c0c241414403081041400c145480308862040c901030a0f030b800b117 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 55980255 1250 55979005 55979069
    0xc050c060601141c02030402040e01090c0302060c03070b01090911010c0503092209060f0c0212070f0303020c07060201060503070603050f0411010207050d26070c0b090d0f030e0a 78
    0x720380583c4021580e0f15541e403a00034088400002c4a00340b044c0019090789070065030045000300d0302003120b0300368000820300321160f2200051104c0d505420420151030310720081c1040c1c03102c1c001500e191001980d200c920040c4240c000c000c425540b180d041043c090480300f5146202803e091005c2c0308556915141e580340910200e25120301c0c0004919000f0502c0b40113a0a190741d03144400340502180ca10b8804003a10060005442051030320418000f05480060007504007442c25030402e02c2e1120a4841030041d0000000c1a1b00b0715400700000b155084040003104020300c0554000100395041400f0941401d143d640001b040500704403e0000348090303098407540007544550840c1041e401800183d003407007010303441036610080001c5400c060144185c41c5c11082d094070200752200020800114101d4028040090b20f0749624040c14000d15240328003c20840341c00a002c4030f00c2c02c8207555404e910680c1d41d90201c000a1041d907034240d003800d08054a01c0035285503019204201540c401d0004074514103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 55981505 1250 55980255 55980257
    0x10c0308010b0a0203070606091d010c050a110a0c080304032a060e0130050901020703021903090302090c0a0e0f0f040b0a0b0c0717010b01050307030c300c050c060601 73
    0x40d4414050b4020003c1b2010140d0100042c06030b50351f41c40ca11401030100c09215a0304107600c072204c0c034040506116129014407681c561a00300a0440c1041713402010b0000d1004841c0308404010300441c00c0151490000c06400008541c5d071411864030707185100080c10800c90412403000d55440c512091100c00c4281e0342585408861510078000480f501d00450000c4200202c10382c46031488541c1b101c804101c0010080014085c6440707600c2070760300b03c1c0b150030005401604100744007024aa42c0d0a00da0324024083d01d00321000e1501d0750005441c2500940c0d4070341a15400140e45c102c195000348400011a200322140c850701c00d8540e01080a5501903030030244147c3d602c0c44004000c0e940c5035940c001501c0c501201c1500c404604151644da59164000c84c154002c05005092403480140140002410107a503218155100c0a03000d9028120010b10704060008420488207005006d042400882030300c004070302c60034402141d400003200c4800e45500d0401204111291040900090390fa41162007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 55982755 1250 55981505 55981507
    0x3060408090612010f060201110301050a14060c06070201021b0604030f030f18050f07120f060b01091508010e16020703080c0309030a050303040210030902130e100f1a010c0308010b 79
    0x44000540e94403c050703010141a044500206110f590740d03e40e1340039135016030020045004d5404800181e0b00092007090b60242d0411014081b180700c11020003e022405081c01e418a00c00d207282a0610342c00301c91110050b0341c04114248074140580580314074040b000d000c1c00403030429840041100342c8017000d40c010305495548904004949a00504a060100324804107107440e510709030352224030400c0d107040035108100d0003092840045101b0f140c1c05174401c11500c00028181c1d9084080c0100710500e42c140110701d0342c00111b000c1c041103913440d24546541d80035490b40c1880c201a1011502920400d1124000942c20651680004119003070fa50000401c540ba0710240075094a103101d050000c41e0540606d1f201c450801c10000081c0d40218821620201d4504044800314103d604004001e540300309610720b0381c9070080c0698001c450b10b481000594840a04401d146002d90f81a0300000100030380c2d40c40081e0300d541d80078022a40c80e03102403922440410041d14010000718041c0504044514 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 55984005 1250 55982755 55982767
    0xf110f010e1908010606110d050a020d03200d02120c03090309041503020604060504140613030311010603080c030717090d1211010c05040801050604060506030c0927090d03020903060408 81
    0x468001481c004103c41c200030300c6203640b5501d0050803101280007010700351054050804045000e4070036602286030a80c0103041c2d80c8011031044015045240006504a000d840d110514258280c0104541e610007240943d031040700342c2a842144a00519441c0e45400030300900456941c0402202c4030702d68105c0f008078000000c500e800c120b8107140c1c1e10003540500c001a0005400e900f060103082164507004d0301030341c2e0061600a0146611403100015002c448650b23062001a00400f03145a801d080c81c0c0002612980f01e40e648100f40d8440d4240c48150390021904000f000300c2d030102040085052202c050802907c8004640b02c140c1c035040c0102440c0002e810000c0b40d034071400f0101444284507000b8483c01c1c00000c00504141e11078099148503500700000a003607801c041c05840c0c21207001400862450391190841941608038040d0f0729070003000f9418140020307416042c4450341035181501c2e15950f052840300e1302d01d0a864800d441c010b05005200c800c80b2580c0c040b4100d0390090704402c1181d60b03030b8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 55985255 1250 55984005 55984039
    0x30301060c06021306020d02060a0903020703060c1e05041401030b06040306020a02190b010504060617010308030a061e0e0f011a090f060d0504110a0305061308090307030f110f010e 79
    0x8090101c18080f81c84c1c520400246040d4001543e12400710755400380d841030703181c09400809640554802030056031203c1c04c204006240c90f800228003030319600e0040d02e01000f6640c50b21440d0b1804128600003400480d00340b152030f1000b1480c140007042401c0400c40c00001801042040c0114071000e05070035400300d07030b0200d894020721a803d0030070b841d40e4140300d42c1051031401c104512000e0050340d0040e85040c20110b8014000e000c0c40c049405012910022a032075641c40d0800c55000030440345150342c40b06000140070300105004061440034542152880741029042001a00001c2210300c2500c407600040020b8501c070b0511050070840c545c4c0640c2d4401c482c3d00030030480404200362a4003c3c00000f640d5280103c5a8032060085104808401244a2410070400c07600d4041c000900140c110380003103018007071041c03c8a83d01500c9041054100307890b40d03000a09210855109070f03000075980503d0b01c20462502c5041d20306c0581203451402074041080001c00c18000340c014580a100042e0a007140d070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 55986505 1250 55985255 55985257
    0x60905030909010e010f141e0103110a0804050c060a0f0804060204050603010306090515090c09060312040803041802040e220c0909060b03070e06150705070b09010e03010905030301060c0602 83
    0x1001000d04000301d6969070380d1340c4500441e0b00b4403e003298681e080c02c2c04500c2001e1031220076900da00041071a403070011186480d2005100d090b0703299042c5650745110304000703140c0c800941026003194690206074540342c14035900b0915000b00040c8500d20401240300000d0300030554001021140c84d10407400d54543ca4042d0082c03049401c066407119003c4000010070031541c0160003800c3c400c4040e514414940c1c0c0c1c00240c12101515000039035085282d001d660741c101205800d0b40080c00404944030f00d1078140204103d40d01036003042000703410004051142d0180003609003041c400c0d04908504d4a03140582629450700c0150803c4c012211001c2442860700b0a040440c00103904a5500c0c80d106690710750710001444c1a9a046a80505000e000c10461070b02040010445011783d200407042d90303440c01000100040750300c840d05190003e02401c404100c0401103800a0030450301e48640e6404280000350544a075000158032907810a0b8540d000a480801503e04644080c2000b44200c0c4071482c07c01e000e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 55987755 1250 55986505 55986517
    0x12120d0b030102041715010e060d03020a061404050708070b0a0e010e1203031009020f03070c0215040f0e06090403120b01020102070213020a08061206040206070c0e04120210150306090503 82
    0x12643c00403c0c04503480e10f5140c044200030502004a80d03001000c0340250f10310b48070920850040044d02800070741c841c00d10008a102c3c041c8a481601d8070340c007103076803200f04407181031101c0031095130008200400c00100f041007101500c8190b0040400c0e07171030701c0746103800c0d0701c166106030040000c030250380060359004180e0138120140c01402d00400302804424150b0ba50400c41e010860703142c80701c000085c1e01005108451501e481040c0700c0c0e1440d40c030900c05071240704035488201d07080001071000d0300c0c10800705006040500940300c14549a00d00d1710352028100c800240500c0d02c10814002444002a0400c050b00c7c1c034805a12030118060001c400184d009000e8200080d4001401802c1011040d10f90390040181c9482d90301c540f202601e601090013182d5400b080c1c00781155001c980410094505131000d010034034480c6500e648040c0d181c541c84a2002401c0c5c1d001c503146e40400200803a02901403104603258a1003044c10822400a012403041c910b2144c4406041c4965820782d44007400320620480328 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 55989005 1250 55987755 55987759
    0x2150a1d061306050c040503030d110909090a03030c03110304060c1e080f01080705060a1b080c01020309010c0302030709030f080409020c030301081603020a0302010513080d021b12120d0b 82
    0x280c0c514000e08042c104040003541203558926020010340c0c2021070405582c255480607000f10308200e2208110f000605100702446d1964000b40002c03041d60b5070710005944103034107103009006040204e00e405425a82e00d502500141410100d00113095503005040e207901c56000b00010418030b015240c1510100713803a00a0500100000c8560807111f608109030074010000e07454401c3c1c05a90302d080540d03c6092501a02d980880100101042c00d442450240c801c1e070b20003585401507050700e5503900e039141e006080c82580c0740d401004000c2800307028820044c8180c85820203502c1c40c9082c440c0104614a1400014070305c6100707800341000c0c4002041070780c019200c250000c5540f120140710166681d0024410018a441641c254204041e500c840403000c4030b42c0074000040503800d40d4015a030340d80044508080300d038640b1800044051080103400205100394001d003850182c80103000e802c1e07071036842146021340f9076031545c0d5170041d00000c0d1620301c82320382d403400d82d44a4000202d0280900b00c03402c1c84a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 55990255 1250 55989005 55989013
    0xf190503100204050a05030d080c0f09030d0804050d0309020f1c050303010f030b0106050f0d0e0118060c18030c050f0607060e070612050609150a0513020d050702150a1d 74
    0x4601c0d00890781c014070650350101d542c1d03410181d07a10101a40ca0744202020f10004001c0008155036000860182051a0f401d200d03860826103c540800d2030a40755200c0d41d400603420700207000500034188100e8400e80014a000d003c40360507074002c035140301160b44841d40942030070001030241003494010b159180c1e43c01030a40b5601d581d00c1d06820701070080f0340815602542c0041c00042c1d220b0140c41150010304030213108030304103175040700d0400003414881403041140d5210340318110380d2903840c48064861031142800003160b01030303500e0041c0b11144070614060304141c5803006001190031884001c00b16002215002034100200000c21020300825800070840d50420981d0780d040c5001082c00c034169152030361004d42c07000044510f07106840050ba10183c02000231800720b1003550364109ca40c01207440103050310240595810109001e884008814800f4035404254041610183e000e070036007141c0300340f00919600049a503944903810014142c4455260b481c4028020000c03501489181000804155 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 55991505 1250 55990255 55990273
    0x60a0315030f030e03030a08160903060207060608010f02090603010519030c0315050c07020108060d02011412060a0509010612020c0a020406150e0102070b0403060509030d05040302030c01050105040b0f190503 91
    0xc074004040010803000300c0c141d540044e41c10304001007130b1510020075943e003c11030340726500054891140004032000708009008040041001400201915803040d40700050081c0740034415821142d0303a5070b0400311a8010440d210b0169528001e690540b00c040703940c050031850f915034800300030f010b9500041050424840000501001c0c0d5020701107000c5010382400b40795038413840c0807082c0c440c069009010500ca803021500b00d003042291105418810304160303c80003960442d2007981c1c1c002005a07140d00d004101044058284144a00d000300400e50300d00000c3d50402401900a4940c840c0c840c941c10740c0483c90350ba50b03100c204940b1002c04c4c0c01420400410361070b11450302024040e290740d4000700c1c030043c115030030951000030f0001c00c03200724140c00d81c10030b07056a841c500503001c06840c110080c4030500801024001d00d20503680070718402d030010350780c4241c0102c016003907602c164845807285c1e00d8480f4926403070302d41091000700494201c0c0e600d4541500609000a83e003801d411068052040b4081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 55992755 1250 55991505 55991513
    0x5180c090d12020606090c07030309050f0715020c100e0613030b040804060e03070b09060c01020c011a1206010f03030f030f05010f080c0d081204030c05060405060a062102060a031503 80
    0xb581c030140480d03a0981e041980e4480500540e04400e4911018155040003d800032070311942c09209140d02c0b83c0e040d104da42900505a070301e011040e42001c440c8156901c9400c0038107030100109401504c0a4510791035074400c0c0d05014042c2c00841c550303627014400000c1e00c401e0115521086a01459010683d02114189424801895041401810041044547c106400c3d1400080a6040b07590f00203090303280c128641c0911482ea04046220005590240b101d103400385401e0180c08103e50480e842c0c0241115190100521180c4008034042e803038101000500850385161b502e8070949401d820310703120231303400e51808600405d501035812200300e00d03100002c03034244440c41244040310b40c1c81c01199450348102d02004010315100750300508550080000071020701c2688403165209002c0d042c16411817081d520b0321801c01c01d088804a489412010030450740510328400d441c080e000b0b00403d000b4501c1211381003042044200c5001c0d11032100442c6944582e8400c2d00700d0805c1c181c203d04001850340d92490 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 55994005 1250 55992755 55992773
    0xf07080901030509010209100509010c0804080a02090717130f050f010f061d0a0902030309100305090706091202090901021e070b0f040c0e0405191a0c0405180c090d 72
    0x1840380e0000b4104404903441c0b90050095a8424074014400c1d046c802d000081510954090f101c21410b10030a074005102058216010708001c104a801070085400c02d4410845040c600405005c02e1010019002014070658030484e030b40101c0700303803d040301c2907010306000c10380150342280180280704080640391407180640000d030381e983d0004024000303161a0a02c0030b840d0241000801d110610410008100c010f060300302e91521400503094034600020040480e03420121005c1d6900882d44035002d004010f0001c000078402082e240c68801061800e2918940012491441c007034800c3c01680041141c2041c294116081400c1260985c041c802c00c0c900c001c052500104c04c291035484a90300010051031034440070511903a4403512602c2505e080c090307401040070780588141c1321071090350305412503401e403400a00000c6005450001521070340800400b088200100010104000dd00c02003005440c0c0d0307200703014810405403c082c2243c2c1c428400955a001c0c200742c85902c041c03a91005024068a85 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 55995255 1250 55994005 55994017
    0x150b0304020d0b0a0c18080309010509040e01050f0f060d15020307030e0706120e031306140c03030112051009030f0f14030103060606090806190c020c090a0f0605010806030309010f050f0708 83
    0xd01c41e0b00c0400f004211b82d0651a1030340c440d0400303a400400c540c02d280c3d88984010540b8000041c40018010804aa124210b4504480628101c4c1809042c403094017030301c00300c10b40c0c0004201c88284085201b9582c1c01a0441c400d0200f4003941d40100100702d2160007500081c6064520300300303ea038030b41e599000007449500d0751500034030110314110445550035000310403142c04e015001d08010704185488400ca035445080c00404a640f0028001c5c23101004c82032005500030039000180c01c0b05235500e41092420061b4802c20401c02c149061498000030741c000b010380d18000204d050030035141400f64001c0d174000120007005542c60720000700100811800d540a5070903519227513208020b030354072048146e50b202070070f5903050100000c00840701c00700c10032034111100004003403042d56541041500416481e241c00c1d915203a10a84a424070340b8169460310a4200800003407078654005e003010b5000c0b986a2284614035810004c8610030b400105008004880b036102c41000c14540c0e5100f5030602e0f60713180c9c0143e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 55996505 1250 55995255 55995257
    0x309020306070f030f0501120f020307030c060305040201030b040207121803021c05151b030a1107050a030f030b06040302060906280215070f030f0f06060507060b04150b0304020d0b0a0c 81
    0x4e442c0b5651170b5440c454203050b42c940426251034010107407500b105044c884074089915100b00d072408030000341c401584c00010400760305c0214950825100141c00e070741c940d00d40e141c0540d1051111b040490100003c0074a5030b281d03814680c9640c081d000a4203c0410141c0000e03400c0340302008480d0810965046d00f0b202203000310140c03080c1d4031917500c29807148141a280c0c0115082c0c0c0340c0200d54a10000c03001190401009900044c0507001c0082100b041d80250781c050b501500310305658024560480e003c060010718514003003101c5911140014440e0155000207800352030081042c03000e58a4280840b005000c00300140d1482c0c05990000403c440c40103902c1c000140196490300c1b101034801080365004150f10740b0380000211882c801240181000440011881c1d2511444054821a0312590001c1c0090b640c960b59507555a003018002c3c4c80010300010f0180b80f0703009184903040a0000041c080e111540340302c40d85d0780c80c0c0740005a00165840d0000e05200707a041c2c2072107460201a84007541c0380001e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 55997755 1250 55996505 55996511
    0xe031c09020303040e060105040e042102071503020c030403020303070f0c0806060117060307150f0206090604020d12020a0b0a0203010e06031b010f1106010306020405090c130303050a0309020306070f03 88
    0x100040202660910380c8000e406500520050182084800c0c0c8543c1c40f12041c5002802e0036a160843e81401c042a18151040309104040b9080c89008540345442810356000402e2064608410060f524035525005010581d0229000200c2c5c0003d0040320021500101140c1d255a1141410241c02d0760400341101c1560452400040000002c00e030a48aa00161901c000c117840d12102c0c01c185500003051164140109480800ca80400d8941020b1003403c555403ca202c813100d08020f80707001e001a0801c900c0d54400c0c400c200040c3c2e601a007100c0070076482088000a00c04c5205c06038500094500001c094112040801808241c0c1b07a02071412201d250f0a1191036413035150038181ca6a62910780300303e001d1000c00450f61154002c4004070400c43e082d1800d0351000c0c050494a5040207401e800807924160001000c0006251101c4282d03003109050744841d1900c4001e80030100c60969500c0700406108020400224050290344989400ca40180644d0818640700000278240f9000502100100f45 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 55999005 1250 55997755 55997797
    0x1c1b0f020115081c080c030112021201060905060102070e09060c0c0f070605180639150103020a050a06050a0f05040803070c03052a0f06070c0305010506241c0e010e03 73
    0xc072035604103001e84a406c070303418034603400c0440b01000c280f0340b41c0c2c090740c01042e1080c20300c0b803440c2c007441104018100000c0020780ca00b030104c002401d01d48558014029a110b004c144070b1000c2000c52425006091440546c0e910740100404a041c00c815029030401ca01481000080315034001c5c1c014140a44450844655603610808011050003038000c44400c1101e442e0b2075152811940340506114010349201102c1c1e440c0c40c50000d454584603980e18604030354100010802c60400c0c5000001601c021500107031001d04003003000300036000d500074500810400130700402181e8014000c403005401c1001c290795661819060000708020603110071a45886500000c004050210804006400b0815000410032120204220808550302061076100504010350b01c001380040d40c07103100440c0300380b002281c589400010406102c00c1c94082240c00014a002503240d07150040c112400c02c0c18080d0102ca40704913050444004084241e07448046610f01220710848080c000040d00070a414240c801307407002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 56000255 1250 55999005 55999007
    0x31407060801060804110f030a06020702090603030301050d0303020904180f030e0109080304030303021c0e07080105070212070303051905100f17060105011b06050a021c1b0f020115081c 81
    0x70024411074000130042e00200e0f00180501e03603042501400101122003924130a00000d081040902d030489840e42d000505100f142000004154003007400c0300a0342c259803410020400c443c102e1000201003590024070b566070769482c0d500c460001d5501da111001900d0007854510300180301144c094020800038004040c0c19131086001c4010703900440c0c0914200791850b54264065040b031900e1010905d01d00c1090780e4040d4a6211308000c00400e24002c25102d450010310500b120b101410603030441d0807442d11051401d44074004c5445442d0305140c0020396a49444c95101480d104a861360349041c03c0000f84450540e0760b95404050b210b400301c100031881d50301d41c164011105030750300700015500800300402080d03014600c081601c00c0c1a245102c0104000d6948004451086640d0140c031a80405c60786400140c540303034040c02001040c1c003080740d811a0000d030508518800d5080c8100000052600142031007904020309110010038101d1009496010f00d5885141008440911188849080c9010703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 56001505 1250 56000255 56000267
    0x12060d02010906050c010f020a02070f15090512150903040819152403060204060e0405090a140f030409050103031710090c05220303110c150306180103140706 69
    0x480c0e4161140142d441c40c0400544050b04104040200740d580c0301d5024508100c2030009001c03100d1a0f5024001880c03c3c002d00e90082800350704207109842e00c0e1509070103155000300da508161901100c11800000c0e0340300e40146040081021482e48200000c188400b1f80f00000152040e00d6800040e0f43300d203424591680d883c0c070300e91100906030b4032001c141d1000c131031100c1e4841c502c0112506907a00c40450480076036040c298031a4400c907410343d40000c0030000c05910038542c03520b04d0000c903810310290520540320b030764481c0c0c2090003034800916481c0001500c0c904119040e0300c6014041a280ca807036490381c03100b004080c02d10051f00855803151402113414455080d00344144c82e03c110b081b100b141000040300050940040300700520404004d04101d0920b880d014125035840f07550742d00e03410303801e41c540148280d201c0900d01005912141100d400d03a5503510181700c80440d81008035490b80d9690b00020b0045918965007000c0d003001e075001005104c101d56101010402c00c0c404c45040542d100001c81340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 56002755 1250 56001505 56001529
    0x42315040b01140306120303010e09010c080105030d08090c3102090a0311150403080c010c02030c07090b0a030f03090603110304031e02011424060702091305010f050c1206 75
    0x11000c0720f08032054040140615000f450191079040c680700d0302d298141c60344c1d00c00e80161005110180800005440034000c00c413401c082450702ca8540c1d4135220100b40e40f001210801c109009003403001414103082002004202d907001441910307245059540402001b00c0c1040041c0e5048106c44031801410441c0200c640c041c101400c0300c160f042c030b1511041d003e8510044410303803081035000a103001d5420180944040c602030a00320343e507400051161821111030021180554005106401e51020085002000c55a80c1c140110f04120308400040d043c1c041604020004010078103604141940b00c52100246c1e00ca68a04000c00c000c4407100000d240000c41e0000d0020fa50b01c90b150012100d10568a16400c801d4000820f003901040e20300903440804440903490303070380382c04c6a2241490300c805190000d404199140751070207440343c0104501c3c00001385a0702950940c4c0d81030781c003001001d502c0f001d001e8491010411490030040400400796000302c003032043c2c080403503010400ca4500000410b107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 56004005 1250 56002755 56002757
    0xf0906060b0708040e091c030b011b030807030b01030207060606050a18031104020a0e1f021005091203090a0501050c0301090b120705090604090c0807080601081b040b042315040b01 79
    0x20038585041000010b107000149842c15a00482c108000060a03c1c45084003801d01500d001c5481d4444100040001c0d070743c003494bc5003007420040d034a008642c0100c1200d802240c2d520300451031089940045c1d000e8410310030010281881c4c210001001984000604080107644d61a14041d84641e0130700701808003c1d000180540400345802c19052400b580240500d04071410070700da004444d0400100603001c00301c80f800201031030382e0002500c1c59040c0030742c0002c02c01100c070800007801d1640e41d041c2c2d034502e100d803884132615002020410b140c400b0402a050b851b03000000703100910300710032040c007290801e200c0d1080e8182084807011040c40c103020003112140010000b0603171a1300c0c0004001c121030000d03000d290041d035034042e92004100038145440c0a0902c4000a1500a162050f4546880b0b4142e014500f99004003164403100c0c0040c00d8084180001200d010810ba220240000c004284284819031442900e018a050329040154014422206101d1911301c42c034a01c0280800c3e5000c4a0203a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 56005255 1250 56004005 56004007
    0x1a010303021203100e15210a02040b0f09010b042603070303110f070302010b12010203012105030d0f0e01060603060501020307140a0804061220040b030405100f0906060b0708 76
    0x80d0510b080202541d031010b1410242d000b03245c0c0c0d841e118810b010003503c0301004145441e4030107409060280f451003d180706000782d03072000300c0320020003500c40d401090001d01c0303191500ca060200c0d94800c0c1c0c0110410350000c1940005581d59000007829612a01c9695110050012500c1d10091242c5030301c070704400c8400c0903520340740c11540d0440007498003044051810380309011041041d80200d01a0008034420b070000540280c200003041007413000e406212081ea0b0040005001030700c04140107102400243c195180e001940e8030f01541140035620b01070303440030300c3c100110f00100704a400150780140740c0e00081040c1a1566811001d0794524000d80e805030f8403c02103440025000e00040c0b008180c458147c030000140340e600c6038004e6005038070903000601290b41100030070a0750b12032403803242148030600c0c1400c8070701d001140c3d542c0200d100d014000316000c40002d0034850103002080c01c91203180c00412283d01040c40440040c508404180e42031b03403a1100c0482c0c13403c116402c81d4030050b0000029 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 56006505 1250 56005255 56005273
    0x14040c0b1201061809180209060409021c030e13050103151505010c0f060207030e09010f0303080606030703140c0d2009060703050706050a020d181109220503071a01030302 75
    0x1350f800740f903030b4070a03502c900303c00c588001604003952080c5034241c040000382e01419942801000400d45d405010584182d140031030f1040169905034000314450a40114025600c01ca81030075900740710805941a00100000003115400da140d500c514140c0c0d118858020080d91440030100c203c0fa0320504407901003000f02414410b66000380d1518200501c600c90410f00050540c0d501c1017030360404c3c0403c0b1701041800048241c607107880d903005030241c44c0014251038400d1943e14000c0c41c010340078040c0b900610002021450701c0c0c1c46600030f1008130308001c401000c07500384421040366944c0310660000360240782c050f404a000c6440a116144615903030511803d20f0b0902040285a50190a0441c20b1010804c00b1000060340390064a00c80c0741041c00058035001200b55070400d4820b090980480710403c0d41031100041c52140c070a8012040540340000e080d6559411940b102094892294a40c10681059000c2000020041040900c00e4a2150704400d903466203528082d0213010050250300000c1341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 56007755 1250 56006505 56006507
    0xb1512040314040f0b030702011803020a02210105040302060103030f050414060c1c02030c070b04050918030f04080307020a0812121018020903060708070e09040c030614040c0b120106 80
    0x202c590403404a070100c52410380d6600500c111121694882c2001c1907003c400c10080a03028400c10810a06c400203c802c11010781d80d0080d11500c0c5200c00a03c5140700140b0100c0d40051004e020101d0001007000300f02c0d6090a040107036456609110840001c1d000481100c03070309101c0c03401e0350304417a0100c4214080c030b0504010460190080702c0400700901c9540404120b801c1d074203811804201c0903401455460321820b541c14104038040e001040004010002041240c0395141002c0c0d0140d9804105c075540025910994118412001900e1003c64003103404201054040010700f52240300300c03840070459a80d020302580300d04810a101422a40500940003c42401c56031250300a03607000d074401502b82c44042100c0611030285070820940d501040148450404100b80e503040340301750a02e04010725003403e0051601c01a1840180144110f502140400c040e0440400286038000805d108044403000d0003e0083c004503029030f8403203180d0000080009940c41100d4070340c0c0d41078070020300a80c00c000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 56009005 1250 56007755 56007767
    0xb030304060305130503041d060a030812090f060a0b040e150403050d0e060106050a11060906060d02060f03130b18060f04050c0a08030408010f0e07210b0a0b15120403 73
    0x20014203500c1401348800001401030004101410b43c0144d40f854003a0b8010318000c4451340242150700502c0f1501040c800b00b101e02058600350340000c80200300070b5450b03020305401d1100c0484403808501c02c0c03005010200d00c06030883c1420ba4030545080000420751131a890390307030340302032a4580740118100201c0c0120388941c000381803103241e01801103240d1805502591a15000364494000500f02083c00e50160b1350040c500d9190341107000c014a12801d03e1110b203915031201410b4a031180402801d1802103407101c10a54444400348101240c0b82d1606021140c084034401904850802c210b200041c080301d0485e8480740030b507a1007001017803142d0300e401300101d241c080644291900e20403000e00000c681e1740c10f228003000e07010382c4000d151034900d80329805003940c5621926100359414a0340c030304034203640081c0740012140d08c00e034002c004205038003e1064607200300201421049240040003103002c00381d000a0254881070340c012502c0c200c401d1800142d07015911072094000070000c00304010074031500b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 56010255 1250 56009005 56009011
    0x60507020a0b070803010509070519050a0c05011a100908030403020103020d020c060a0f0605010e030c0907030b09012705040b130309051e0901081908031909080d0b01030b030304060305 81
    0x64144022152509100b28040c0c000e81c2046420b4200040103104a042201415401c01801c0c20024107041c1000c0701100d4005000242004010000c601e000c4c40340d1103100d185c101a43c1040080001640d0344080001c1000038203c1c4030f000361004920341100b180300d81c201104885060001e14181811580114082c0d8400c11441d611541c003402030001050003440344502844070008002102d60171480ca08056558a61140c1c0c1400b1751450032552035200451400b0110702d0882d0012419942c031803040c0c00500c16240703140d400c59800780001ca104d0440c2145e80642c03100d0038003040b40c8206481d030240c040d6042140d00400c91075802c4080b81e0f200c0400d100d0850814031904101004a488101107041047c1580400e144100078681c03030502410249207441c00b4000301c201403c600d40000703921301c28450080d82c006111547c0040010410f1034582c00c042d0520420b20800d21000040d0304002d48a41c200c1e00c44e0b410141d152074800c1400e58002e200f8070524030b1001d0083c60400b0f203080e200303030000c010007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 56011505 1250 56010255 56010259
    0x60509010c120c02041103061804020d061805010624050901110318090105060a0804230a0804090f0507090b0c0102090d06020a0f050a0207030b0c07060c02010501050f030c090106050702 81
    0x701e0392a00090b0540780300c01c0e8154103d0760366104240560042000703031418200300c0311200000700244100c3e5120060441038544011905100c00d0711544045005c2c0d0034501c2d000b50000b4600134801d0009121401c8510040740100d0080c01100c1d1034000052000e40c506d00c0f41401005030352a40781c04203001301d000e006030850505151201d071702c215101c24290380c410b5861310900ba952003500032036482c20f41406400f421082c1c440d2030a0100078500a400140c1c090000b5140182682e504403044d0a101000240000580282c1c1c03050152460121b03050f400c02d0007010310440c103002c48420500780910980e80f0400e10740e41c80429aa1a121841400b60710030b01c1410b6155408104443d04c5407a00000800f015101780c1e4010ba960080e088000c06c81d48502c00700f402000320802c42038580342e50001340704040c0c0781c104c858080705e9101d003a14615248034100c80207020a081203c00100141c042d40442d04903241078500245100c80b24007007607240c02000b10300c0c40c2d01c8090f0000502c000c6102e0405002c2ca1440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 56012755 1250 56011505 56011517
    0x1111506092a040f0603020408060109050907210c0e041a19020711040c0203041208130302040e07080606060a0c1704030203031c0b0d05100b19060314060a0803030106050901 76
    0xb1980e515105104000240350084001908104000703a00d60007100610203840c046060038108100c19031980310610915a12030b0b11603002c603076002028006100105090000f4408130107500643c140ca2401140e0140d600540764080041d00001d00c2e8401403040d035203c980302e030030031742c804009040401019004140e6142503003e03840c41c244551004113203ca004004103010542c81c2400c1205541d84110740e2011904140020043c450000080440d1668005021521010940d8000c401a032840d40081e42c003c1c100454414000c80100303601c1d003980c2240c0e09441a568a0b4402d00c1014442e207a0342e0400030f4080b080315408144a1603164900505110402c2d151607070f640c0009103103411150880c15401c1e110b0716032502c2e1031100d10030740704085410f803803a500300c2803203882e010780f6031303002004c5000050746400340d114081e40e8442e50b030071515140510f101c00c81c1e03440c0d080080040010720152001c000800b800303d0090710308100e20f001100c0403c0d00071460341c1c1c01c2460458040e04504021070500c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 56014005 1250 56012755 56012791
    0xc061509090a20040c0e041b020607030b130204030f050c040b030d080604090b1e01050301050402010507060e010b0406140f0d020306130f0606061205100311010e010c080703030504020111150609 85
    0x9107034000c3c4812080e00380c0d60700d041c03031b400c007000c00044903420206106400801d1566068103900400c20a520211074100011a080702a01080501002440c440b040300d04c00100402002011901e44c02040e01a5003140e46114200051008070b404a1900719450342c001580050014425a0707855440300e03014002281d91070f4a0707500c0100403d421342c0c4034010f0305000404050740c54082568140101000c80c0240818106900060b0291041d0302001c0c01682d110b03080f100c02d91800750007001e140c00e0085c10800c022540d40403844841855440301900c140d0722904028178502d0883d0804600b01c0c0c004001d0800358890b0780c420b000650600d2070403035030661841000004a20a07100d44c0300102129180c142c003143c42c0c50780003412074000501801500341600400d00115400905944d1020403c1c2451403403a280e820068840e0304004400420340b03040010000d00301581034103c0f9021728806e032116500941c0e41021561181d540303212102144980b000014050318041e43c2442d00300c3c9400c2909e00f8607407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 56015255 1250 56014005 56014009
    0x150b0303030117070308072a0b0f07061410060f020109150e10091109010512070326040b0406030c0c05120f090d0609020a05060403030e1509060c061509090a20 70
    0x5000301006480109640e0851458801c510941e052508004140380002d642002751400b03050080b4060f0941d0008041030090030032020f07500080d892806440807171554940035814030030441c1d241c02144002008083c1001031300f4014054a81015803110b8070780580794026250b14001c00132007000d040d8034490004a9424402c95101d03181c031007402043d0507080840460140b040c40103041c2c1c000c0e406042c440c2140309080b2008500d12095903484180c0803005401201095225400083d000c000030b1000100083d41c548101d008001b0be07040c0e0b03101171080094000707050b15800203100c1d000c0c0890704048070b0300c09d803080c10000810f0804000c40000d41058a14404074481c0c1115410485e0304960300c1035100207501c0c103803001100400003241c11518190455400806400003420042d0180d807400001c5d0041500b00e0007541c0b0582405800c50780c0ba400700140183d07561030156030100003c1e51051503040d190500c1540144140d100800601c422a41a5102016525004c9150640301e10400b080c144075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 56016505 1250 56015255 56015257
    0x10210110906131d06030d080103050303041203110d020408010c020303100b0a14070807020306010b0306180c04030206190311090603150d02030f010603110d050c1908030d0504150b0303030117070308 87
    0x61384980d00300321441c0c5000707014945009080c8040106004524004000040340001165803099200350b91030303000e003d4000c01750040d0441e02c1c80601031200c0071031000c1c2000899806031048901c584002d10664418203816a224882a98600f0600c1d4038a1010f210306100c50307004000416061170f04000f0600da07002c1c01c00e0f8540005200300c682503000100042076180801c8034a000d030602c2c028845c50342c10f10500103100607071911b0b4880c03802c040c1500020500c00c00041030b10700440d0003910301560b5400342900d40f1110b5107964442d0011034a03000e002a004040c80c4181c4512010280085241d61150516038200f003844c0e114465001016010b442c00580302405003511180000001060f01411172404030904007105184c54042c904907841781d4045240002c02c1c1c0b808800a4078440310711142150303011407801c0350f034020102c2c3d80b1001038850310f120007541c0058800d50103248611080848003941c901562800058240d06510510060104c100034000d01e40400b502601101c1d543c80d035030b47d25145c0d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 56017755 1250 56016505 56016539
    0x30c070f031202070b092e020a140706080a0f0f060806010501091d010504050606070f0507030209010e040308150303131409010b070305071b0503150601021011090613 73
    0xc0384240650070410001c0e02c014158030b1103103a00203000c00c5402c01d072040c1810300915401d244030340110745481c102c82485da5075614520201c00b0804405054409010303540e103080050840300c0c01c0303500110001242010a03018203840c8180c1d1080722586a24a40001403c2d190054411a95503001d0303000d031900340d520441c0000c0c03014101600a6601d010005011681b81d80d011111070907410308002c032a10208a1030f6411f4420480300000c030340d155000840c03018042e00c500180b040c007200c8158801e003c0c0c0010740c041200e200701d07480084c580c0c039180f41d04843d24058400a02141e51240803550742544089803a00c1a03101908903400c12507010400c0c5801001d03039001199221401d0322400d00380c00c04100710783c05803943c0d180407403400242c0d960040c40c601c66a00d000c3e01e610003440701d4030324180d1540f400c00e004050003011120010409600e100d10461b00b80c803424058481c401c00005d0304034a5002c0c140c1e03854948147c00e81031810308001c1c40340c6070780420640c181d41d02c0b4903d4080351041c845c06520701307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 56019005 1250 56017755 56017769
    0x9100e070c0302070f0f0312020102040515190f0804030e0102121305040e0102130303030207020105040f0303030506030f0601050a0303230c03070c060503240d020301180209130b01030b09030c07 85
    0x100804160501030b04002585e04082e02001418005000003480221900101c1c0c3e44042a44090f52440ea001c90090280717820150b13001c001d55250134900c5e891350340135046083c02c0f03905c9103441001085040d1660303c0781c0043e10300810f9100c0001804a80981c007031041c1c4800600560b811108280e07086006a880341c002810b078040003040030f2040d800e25109a12107200550021454242104c5100c1c0c5522140c2c80300400b01a0002562011644202d00340c0380280644050b912010f6100d14015000d440c040312124000d00c51980c0c00016000002000e90407982e0140000840303504540f81101c04a0310f000d0401e500118400443c035006002100503c08400684060350300c40050b4604251040b155070700c41c80c100401407060001d0030300581c250b0000a01d004246008416848000c0740c0083e03940c0d08041d615520340207000c86e0810b101c5015464851007158080c8050395407070180caa81c403c81c01c0700078080e242000300510010385840403158004441008a0781802c8280e44d80130324008241d00004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 56020255 1250 56019005 56019017
    0x50c0a0302011d011202190908060c2b0603030806130510090c05090603070c02030d0306060f080403020a0501060e10050d0b07030b060d050c0405040c030b0d0813051504030c0b030c03040209100e07 86
    0x145030560710100c0000986009c002a0000d4148007000aa40740a80303400003003902000d41c85000480b001c41300360160005200000c0c48a59540d050160140604803180c600494110400242e0547c01e4843c1b40d01c0b80044002c0b20300e003641002d402070010030303d116070360f001d211040264800d02e5031844003540c03103030001b9503840303c0202082c8145420500c0280442080c103003411028045c9a42098200034800c0843c5000350309596903003412858800d04110260055180580c0807038108601c8420900c42d140041030103001540d07460601540a0380004050f0181d000c800104185074443d82041e107207440000c00403401d00c04000c0340c02d0304981081c0c8004050f40c0e80024200318505140c0526401c0303581d02d0030701300412440300010038103c414800000b0203c00d000140c00f00d142c1c3e0b8682d49100640340140040201e0b030741c80f0b809403d040d40030b0b000c251070070241140001039181001d011a48542c007800304690450f101d079428041c1449004c7c014051140c2d0094000c00d0201d16407101d1440380d01d8564400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 56021505 1250 56020255 56020297
    0x10308030a06080610030609080f0c0c010e061204020607080705100e10050919021504140a140109030615030f030c02010e0f0f010818010509030403050c0a0302011d011202 75
    0x81c90888190382d03c07411103a00881c04100c00c05117000c0401c4122038024002054480480c0382c44640d034851842455207400c004107c51100100c0000c00c9200400300f0703200e504a0210020811043c0e00887c00c208100804a10000d0018184800034000151186250310304003c40303503a52b50f00b0008000030501d5803c2e600c103040221608100440e0701100030b0684100036070b05281d07941c2e5407100c851a1580d8500c9400300d1a813011034a8042c24003070140d0814248580f070750b841c0c2020800c01030740400801d04c6903400d0301001c900c4000c00d840d0f00c1c20f0030f60140c403443c0c1c9480c5181c3d2610060103100e03088401c0100141400000305402400c4484624800e070f84a1499804134400507224562900710741d4001d200300c09020a15464903294440e6960302420001c005c0e0352003081341c8008000b4190720131400d509040030702448050020240007030701d100700c0954811a101d0400d100070380400340701c06400505030141da010600700000521714a00c40600d0301c5800d5144a440c00401d0781e101000c89401820f54906d8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 56022755 1250 56021505 56021521
    0x1b0319030c05091f210606020606060421030c020a0306091b0e0c071103150108060a0506100309031b14010f0e0a081b0604060507030606050a0914030a0b01030803 71
    0x50004070402070502600305100c40020902c401e9650207204883c4d0360000c40d1112050141490b40c800ca21161504200c562600c00b013203001c0c008901c2002d0151103a440030841a10303040c000e50301680d080c4c004070804101c8062801c1004991210190f0070b10818104000c05611080c10203406140500e80c0410300001ca440c00810302c0c035107003500e4200c42c44404801d200b03680d0854403080d00b0103080e03004151500301038240130355040c0ca0b51003650f504d40b1401800c161942034800441c1d04803410203080e11407aa0390502204103031041181c83c00c0e80301c846206944138a602035480440060b0003881c000d69000c85810202080c524410400e450301503c14049601942c0c01340507c158200b207802c0140b000c21721440003181d6074902d008004040120106502000d000e014420306600c550f00000c8885034102410810000e000035620344000a0070108007158580c0650215001d00d049560303200740c080c1c60540c00114444609040e203a250084101300c2c008641011049806907000300b0714141d42e07081804e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 56024005 1250 56022755 56022761
    0x50307030e0a1502070501050a051b010506011107030c05060a031d0a110f030303040209060609090403030b03070e010602030a0c0303061e08010f06030b0f040c03060509030904061a0409021b031903 86
    0x407000200340c05030049410f01507400704010040304c00a09281d42c9908400c00309032124050000400315010303590050310300d183c005422090040300c00780c0700e00703160340d85203003080d51205514007026040c860030754010001810984000c01080d860751500184250394080c003034030146207504442016600c40055075040c460b100400c10f803252821030741941100240c10110391603010040000e0700c600c07401400207481d83c40d004221074110310014a9112a07103068500500288103c100c12070180c070401c00301155001051015605071405a001541001d000c0d01c81103e484154040890401d501e0304400108944101c0d0100c2c440c8a0b200700d035000280c00d02c0300c4c86084400c0c40303045850036818818104042580720705940d401c0301a00030b090816507030b1030421090004a90340700030306080c071300810003840c032002002501507450110b40034020b2903540e040c0d800f20004031000598a045c4200810024bd008542c000c02c88a002c1d0101651414601d034412419034110003800503280e82821001030120f81e140c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 56025255 1250 56024005 56024009
    0x702060f07020303160e0607050102070516150504050405090c041b170f01030305070311060a02030a0506010c11060904060b04060801080d0c1a090109140304141215070c050307030e0a 80
    0x12000f1801c0d483d001080e51024400241e0f40c0e000d01c003180002c04490b8031510101e40d2201e80040003550f4600c500c3c0f03085035449a0134078803c034000e92503c0700072460140c60000414402044d658441c1007900b40310401006140c080c01c0004540f0a000e5603011a0311280500c4410882c0225000480b440e8804042c0212801e009000c1c041e46808080080200210703080d01d0550390180b9000e03440301d00600e004d454648503000044114483c1804004000805400a6200f041c05d0b0b4000c0c4400d403100ca0040d9105000c0010040549413640703095035a034100403001d420000b00040001c951199140d00d1251070ba48250807003000505030f00010310101c00c040103081c1c800f0035585400402e0254a854500c240c43c1120b41d182900000c44000c6598104250440703a100c640262000013204c810b1031416a0b26801440303010401000c585250310145070607424082c0c0b07040ca80020f081c40000743d0300700481990004003c01e044c400215081400300300c0c20006402d00c281300e0707102c0c00440b1444104020984480d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 56026505 1250 56025255 56025257
    0x90c03060222030506010b090a09020309030301030309120f021e040e011406030604050606010f0905041a04051605030c0901050408100905010506060703050a11030405030a0f0605130206071502120702060f07 90
    0x2d50400001e10009149030444203105500340e150240d610000f1800c4105174480c085d2503001006003e13000034040020741c1220300c20f07182d03800e10981d00e41c3c1c2d0000c4404140740140101056a90304000760502c00c0901c00404520740b04081c444d030000340010101c0d130304646c29010311ba6545104210482c24600f580f508490304800410462074aa40c4103036680400900003030401c4405410a48001e00900d50300c000b03040010002e1006010500c00442564000440b40344207030306040100d1102440603040801440c8a581e030702d4a90b036600110704041343d002c2c031100c2e41040010840000c409005000b0303456980a4034030040742d49000b50826601b902c60180c14548294400c00c000c4e00000d403c0412502c91100700e0030849001d0f002007a1440c29401164400394050045030a800e0401a045090005552080740c0410581e118842c0414100105250080d00140d0401844002c2041e104082c900801098000b615244000f081030200c40b070142c2d003000250b4032507414005074240041c4095801002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 56027755 1250 56026505 56026567
    0x3010e01020414090f0c0a0c030c0b07180b040803070f02030a08040f090c030204050d020d0c05120a06050a05040302070302090408040b0403080702100c05060a0c0513030515090309030d080604090c030602 89
    0x803002003000d8511880d103040c0b081c01248d040410802d8046c07840e0710800e03600240780900030314018602800b42c0000c034080c40014040e034030003c542c0000c001c1c00d40d82a180d58000840c101070f06581d03401c24000d081c101c183d07854420031824034006080c2c000104060942480021000e03071510b0704010a66a80c1501c80e014140180014006900c4404030300b15040d1f0100c84400d810401401e100c4030380e9000d0b0300010b8212896184420a8100029502807502c0c23185d50104126510100300c03000710350080e0790040c01604510010400342c940018220340140c01a15070900d02983c0e50034200381988079510442d01d40301c000c030301a415450b00500010030700046040402035110f00740e55031500c4000052034049e40b155214810741d60207100c4c0054500e20b14402c00543c40540d101c0c04c000e50b4410070400300d112021000000980b8106003c016201661405001000d070041d401c3c00c1681e1000c8006c0100e034001c5d5a0b0200c00011903002d900b0030f4001c500511005070345800d4000d510806d42c01d4210400d5581c1a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 56029005 1250 56027755 56027761
    0x4150305160804060f11090f0d0c030206031e01090606080112022101090204020f2208060a0216120908060711072102090702011406010c080901080603010e01020414090f 74
    0x121207101c8104041c80303140072001a65540380c020024114940781000c25490104a40351156101c001010721184c2110940001111a801c04c81c44000e607102c024a0f003c00c5410070070040c2085005076400001c13040c000d0303441d5a10322480400d002c1d000d81c0a401e17260303100c000421003141c01450306409485140014801d1030020f40100d4024001c1d600401c0d440b0314146403a00c074903030303003036000111980c4d00a20556950a83c9000380b101d50b0003041c0360380300e07051200d005450f8034030416403d04102c425030303806004250340b5a0003400003500320b44044810f20f4100d42c00500041c002260491811300c10f0703112a0303c203505110440f49407000050180c4280544122841c0103c400001c4460494841480c4400410155601c54111300802c10300290042113001c24001542d4064204102d076080141e44101140c2d02c48004541d1803143c43c002400e504001c02400e840d552007901101c2e4010806000822090440b5034010b00b243e002c0d80c003641e100e0344125a541003c0c035001c00b20740d4000d040e583c20105581 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 56030255 1250 56029005 56029021
    0x8010518150d05070f1404050702010c0f180f12030809010204120f080d110a020f1605040504030e0306071206090b28080a0c0503061f0b0f040e070504150305 69
    0x848030948040c802c100005052040000c1005064080d14280700c440c01c0c81907841503004111852642d046116a040c0b20000d004144144110891030f000b680e50845020300100055440e43d502002990240070300b1240440c40e100082290070040008299008100340d05040080043e070000d010340d409079004200030410040070041900611384c02c040c001e00c09260380c2c50003c0103446110060304800c0e09041408248141c940051311400440d0307000d1711007001400c450306450340d070500c104016880707580e40140302c41d050590120703500600c40d04021220714800c1d0b0002e131500808880b101c2c0012890001a2042607403801000c005090416040c070041401c20001504076810882080b0184a4150403c01403000440c050000b8500f0005580c1c0c222100d050880c2d5101d40d1340200b9010380b01c1c0401003000407071050b040702d0324040002b11614a00b82040c400d980d003640304440400480307909020128054106084480c0152015241e01e590303145031052800d400002d21804c84241450b202c00c1042031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 56031505 1250 56030255 56030281
    0x105090d02210c0607030c020d0e0616061415310b01090b07080a09140d150b040e010c08070216092a09050a0503031c0e0c09040308010518 61
    0x7150710b01206070500011001c451240d00410345840300301e01c149820b00400c0e54056104165000283d4280c4040003456802038484004074001a508a01d04014542488a10b1507000070050300c5044007040222400711441803541d01610184480760145a240b4140e10304038510325411081c80c20003002d00260402c54182c502c40400b19000745988848180459a01c60801240a8000d02d026141c07950b0550030050010f4001c081004081002904040b5420f42c400300841c0c3d54510040c0b10780d030421046c2d6641c5040e0404080340d085456154002880c00317030307618024440f0106801d40000b07500e01105500074420280508154159004010b5400080d05c40d48028006e50b4100d180210b03200c3c1c418980b20030016042910200300b4420100c1d03a01e44254085070000031560304950301c441c81078640042644a102e0b500000c1003c8040345a0660b40f0030f10758100c1c0d029418004140c651060782c0801007102c40f00c0172035080f0001011326005000501e04815100c9204103c00c43d201c0440c54940818444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 56032755 1250 56031505 56031523
    0x2010c02060a09111003020c01060b09031f0b150c0105060904030f030c02030d02181f0c0213020408120304050616090302010809070f080109060e010c230f0a0c03020105090d02 77
    0xb0310b9484007601002c0c44018850700d6000d10300505078882d40c800d156002002500701a03082040b81d4204480050101000819103044002c0240a4002c003004407100b40200c0e0900d00040040781e03100c1d604c0055a9952401d03440d8102010303c000d990741c40c0e0301e83c489804c580000f030016108050240c1404007133503200e40210380c1c4000c1814009041da01551041c0c1c9940100103001d440a0f0000505071200d444034540d11110300e0090b1841c41c0030120164800a081c0015485030002464486d038241c003605e040d4488010b035181c5107038010724050b03d44c1d000728104081c10801741480c90000061004010b070402c00c3c41c0d40a00c0040710940c0500e0f0300c0f10300a00d0039450b0b01c400ba041220303880108060170030600108008100d14030308501c05a5440b010503010f030400032002d0310302c146055159090040103003d101c080510f150b5070001390388610b0000314404d1503800c0b191010207000f030101010b140e0f8403e00401d007680b5075485204100c1c0703661800900b5668010100c8900307810160052a8141d000144125 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 56034005 1250 56032755 56032771
    0xb01020c03030f04210501181b180b0f0312070b01120206030a0b01050d1b091d060d15020a03022a07060806040902030703080703022404030c0614101502010c0206 71
    0x1005804411040c11071700042400078110f5440c1004043c542c440c43d490742d0740c1583c410000300d903603078082d0424005d442d0164806c00c40008000ca1111080c00d5159003c010401c0000b480c840c3c001748200b000c24078104e028a10314614080006a580a002000b902240107000e0444900c10207050356002ca159808042d114035001a15070305512920381c0102c00ba59268141113a0801c80711840035585034103050b00856a60114048140108a05001c2030054101a461031400550343d2641c0c4240310740381f100440c1c15102c00c0c01d01810100366586900081600c0129030380c001d611510082c0801031014140b000c1c0c42c240b18804c0e014141100b901050a108036400fa0510030119500c03280410701812030540001e51500a0490101c1044031210207400f17441c0c025801c0b202d403002030a00c08083c600505003101c04000603500040e0000e0321034151000818031a0902140b20305600000402c508001e9800f0801208031900501c00c41107020340200c55122544004c1c00110301d10b02010b5118440a09991 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 56035255 1250 56034005 56034029
    0x3040308030a0f020c06010509070e010206010e07020f06090303070e010905030606090a060504020a110115031e1b141504050604060810030503030c070b0114010806061e04090b01020c03030f04 84
    0x50b00c0e80b0746540580c020781e01c0810150343d1551940386a549458007401081d108003034030804202c0c6240318070616401d290041e00200800c0e404d2031081c44619600604c0e000851240028a1720306c4c50041c4540c1d4050301c1488011a1281820391025141d410100b68460420404c1072082000382e034001150354000c54240c0d201845600d42140c0031000e0802750f0801e0350080e00000d030104049a0040e030002c2c0294190700200101c0c0d06410b82d0141104191001030700a1500003131050340200403808040103c2d105524150020002d08a03414002107654007050f045028824044d0340c40c103100c5014120000c4001e20649020704100c0003400500440c00340c1000c0100a000040c4100c06804800c0007560300001101d41364a004000d00c0c101c1e40c45100129020800c0030b000085042d805020140c0031174058584950b03964900c5c2c00e0110701d4010b841801c0d50080c0604d0000e42c0303c0304100092024011002d00880e042c850400060705e0212880c00b4a4000d910804c10050482e040b1001d490549800840315 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 56036505 1250 56035255 56035261
    0x6090c0d09050304080d022a10021903090519080d050a030f020d15120210050f07020405040c080f0303060907030903180b030411010c110603060d0c03061d0706020304030803 76
    0x2000501001e00c0050851000040202c1d40a2000400c20b0403020309508030f509403d4194290301c4d6080b160b040300c49500c8159075402e0118901344e4001520011a481102c10441c035900070141e0396103910300160b01003141c9940c280b09605001d42001601c0301c100d01200e54a91405050030360300d010180c45081046004107600041034441d4004a5000401c0a01992502c502c440000024481c1c1110451101e501020010307101d0b0900582000c1c0c50340041c00e02c00c00360302da24402c0e98207600c0b0313903001d8030031400c1004100c005076107522456000f03d0203800e4a41c003180c14035607038907e400010000d01c10f86500030b208000c02d6594242c1d240d54070061a10b00440c07100880d19060b1110400040140400c1c050680c01040c224040d001461041c0e00070100e84100010380801502d9402c100000030300540c0340c106811510303062540080d50018030150031b03007240c00d40d1a1110156100d564208854150f1200c000890306103003082c0380048200244040c2c13a402c1d00e0518040c0d81c0388118480245041e20105c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 56037755 1250 56036505 56036527
    0xa0207140a080a0501060906150807030207080c06070c0203010b0117060f01030e1c0e090c0703030914030c010905060109060503030406030c140a0e0a0b0405060702120102090607050a140606090c 85
    0x7030003040c503041110186225480d1440c0a44800d00804d40e00303910305040041c02a09290040d40301c0700d85a202c08219448201007200654084d40b02516044400c11650f802104100034840c4541425510443c10308650b2040509603001d03201000d040100310b070103910504e032420780c60030b400c40f004071a10a8903d525400613000740141414594a90003030310202a10781945040c60000c00c10749548a04a0703203445c60400c8030344c6c98155035010440b1802e02c04600042d02980c00a22a44e00900902a00109043d056032550784038155034640c503510307030101c0e10800508000241c0035101078841840b001c1e0030030300801d540c1d0003244150410075848166503007070325018050340719000381080700007a074600030300340d001e001a00100842e6000d810440c0e00002c1d048038640954090b00e100610447c68500302d502000441041200d4640303c035542041419001c6d91200e006094072841100a8a18217403642403070307079032645070b50307146401030b00603904018a542d03601e0381c101e6019001805490701c0d0201912 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 56039005 1250 56037755 56037769
    0x190b090d0203151e06030331090204180e0a111315030b07170609150312030709080601090506030a0303020a020f0f0715030209030d08040201122f0a020714 68
    0x558400c0094481803212204500060a8400c05501040351080d1600804d140d81c91050000c448d003008010410f01e110f60f195860b0309034280d80241d402c105025291040c1a08aa22582c0590503c1c99910186a01202c40b4007841d5a903207201743c040d1a000b070440d20303900004460059100d1044401000d040300081683d405130001c060007408800040b9201d140002a154007600d0000c0843c0306c611082c007608038000e24062113500094003001c00ea80364040c01180700b10210b01d0b5203625004089001c11845441800f03144200c1ca40d6442d11030303241c81c1ca4681d17420700038180c00c07107491241010104200c41d00c0c0001c03140881c40c1e05103030050b91582c80034800c9041c144200c110038054001c520180c110444001066000e032030030341c84590919040020150100d1191803ea03e4040c4c20803850016214003403d41d4607032060041c100940d011502c0d01c0f07180c040310b0aa00c80320a03910750035400020400403660003001094076400b6280c2c074120b05004003a580d110180704900c0134600705814030369603488082c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 56040255 1250 56039005 56039023
    0x60906160f03030b0f041b0e0d15150501050f07030810090f0b0405071803061d0303010b0a031103060904120201022a1216030509031903020102030402190b090d0203 72
    0x40c1c03001040403080d25005019101340b601891040102c801641818649407003101a003862040f20751454820303e9030191000361004000d01d50000700034545a0101d20f43c500c2e0242e0881c0805000106862441d07451800c0c8001d036040141000801d0040729142c031441390449910b103816091800c0141e64094440c140803038690071070f40000303041420504003004182c100610900c402c0310140803580e50040304580c40a05280e600540785401c03a02000461071950025002d00d600f05610502d4094690140746154030a0748402d1603510005a80040580d040c800d100107148000c020f181345040000004030302c004090400b402c101055038545003003900035030444a917041c80344030f00100ca100b035120115105004054056050107048800d2603605491002c403180e0595518142d501284142c4040324590041200c0640520680220060595503a82000b030003a101e40d002503500e103007501c14425803a1010143e4404254101f206124450008003514490141981e03001040707011400003903c0c1c85002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 56041505 1250 56040255 56040263
    0x30b0f04022b0606050906061804060305070609240e060c0109120c060f0501031a090a02090a050a0b030a03021e070b0301090204030506010806061008090307140102040f060e06090616 80
    0x4040070300c420826240704030b0445000b03070000c002c0c250fa284144100d1700e200b01c0d440b6a0000041151110300d0418541202030380e0301c083d10016801e5201d5071858600062074028030041a5280d80801160728400300701d042c10040400c0c4062141424200600380c0f0026441c180e201d25000b1a08144040b0700b5407008201e15004152007134001800407000d400746805890036501c2500b000c0342c0b241409014024241201d600c8502541009459094034030801400341140e9418058011105d0269451502050044800d4103001415041c80c120703590445140d58102402604882c01d0300c00460b40228a1080703070304444410210050302d2904850504146410008541030040008180c15406501401c1941d00c543d040b20060798940009076038885044880c658003100b8a0a04084240b042c104a40c00c0180392007128140003ca54541c02c0a02400c4c98114441e0b5010a040086d22402020080241a00e0a00c8600200c2560105003580708020240707004a900291410140100011000b105900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 56042755 1250 56041505 56041549
    0x90705011b03050d1a040f0501030c05010e130501061706010807020d08100e0c07110d08030115140d05040c05011b12180305010b04051506090f010201020d0f0608060c04030b0f0402 79
    0x40c80c1d40041c1700b116100800313010714500b5a0381ca2500f0f085214440c1680e402c5036028604a10b420011201c2d40300005245802082d681740d4014152180d00440d4040c010649030802c2e41079191300001002c0000410490412007807000f44a05207402050404500c452460108041d07a03c0b580010f17451201c0344e20803a150030405c0200711440b007c11000d041650300c5039104503c1c00a44404001e880100c180b006840114100700401c082d0041d81c3ea06c104a5101c0d04041d1003440c202004521700790001c1e10021002c2d0744600400041021281000d009440c0074200080382c11003440c01c50115890022000304441002481c00005a00404a0300c001c545403030354514666880380342450281400f9104d44d4042c904140203d5101030a4401c501300034074024100324200120901000301425210082a040d55803c010240b9090f00c14000c4e0380700e4003103030500455110b00c1c050b00540342c400000c000551044051000f07100082c0c6038103141d504040350b003242c46550788880c00000c14200c10302090040c3c07005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 56044005 1250 56042755 56042771
    0x3150904111507060c11030a0e030705041a030c0901060c030503040203120c0a0506010b0324040b04050a150b0a05070219080604060b090709030c0603020a050c06010f0e090705011b03050d 82
    0x1804000f00790191150340c00b8000d00c1c00d0804d06550102c22286513225540007440511070181c4113003032070740355400001c08684003150b0703880204044a0241c410070700c080038040307074220705800c0402401024400640b48414a989810f030000c100e040c0c8107200030104078000020806640c3c0401503e00c03052101001559540b0714400500d0352200650740407502d500a0400003c2d004483e282602e120300c3c1d12946c400c1a0600d400542c080c440003031004990302c641e07218031900d0903848a110b154402c0782103400000d40c5034100c524070800d5805075803113205814401c0080340d1078103610a05071209107605a5508001c1c0c60740c407122140c101001d400c4000d5600c0340c041040144003441d0022060100103a540e00c2841d1510407003180c000d2a9408050003030420000c003000982e11a1b8020314a80d41c2524003107040042e50851541044402c1c0e1102d4010481c50409010042d0074541194209903400d00a02d00e580c41d03c0c001a1196481800000241d170340b8900344000e00d8000d40844e4081d20b0403803c1084001c6c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 56045255 1250 56044005 56044039
    0x10e03070e010605130905010305030a0809010e060103060c18050d0b1306090b010614031b0c070b0708070605071d01120209040e0604120906120905160e19020315090411 74
    0x2801c17070485100400609100007a4a102e14402c06041c0da4000000c0c40c03610010780340642d41000d0103403190200c1d41d42c4168004081790b00b4004180070358494400450601c8031001d009124503400c6500b0790a11800342020010340d03446000c42440341d030340b154041e00555940d00140040c4143e4500c06014941040244810001c5038201b00341a60f9041d10f507a40e0907a803001821600d80821a4001c405041c0b5210074810306c0c2c00000505040790600382100e40d441d40381c20080b100c907000030310115144035022900c90100141e41c05080e030702c1569031901340c45044c0b07011501d80507040d07841c42c000c3c10b01040d07034011b86112504d17404603881184050800d01181b000e06c4d100582e00c00e0121030640300000301c000707540b038414828070b009011120195100c05051801c0f82e940001014108000c40d41845811010390100b8410101c500090500840c043d1162030011500000d0015040b0b40c500300c91310400810682601000f42d84c000b001003528102040d83d150710b01001c070800b6840c42c49500c01c00c10350356101c83c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 56046505 1250 56045255 56045257
    0x1110301030606090609020708122814010b0c0d05130e040803070806060c0d0305060d0b0c0c1002040605030411010c06021303031e0801050607030c15050405010b0d03050405010e03070e010605 84
    0x40700c03a080c04000d03036560b1b1440b1008030f0148a074000c01104042110040e0215220115908484c1002c100c003c00d2604c0840214044414141c908105840361080141044c0060a080c010060204001d14024803003a0207a1203c0302c429501090140c00301d12000c8164031101030703e001d003400109a01c894101410001001d410843d030340c60006042000068490411806a80120038108000c0c403031145200019005400e00401140d040026104a031002c41c0700c60b240746005040524695540b400c042d0b030341e541046d1a0302e88901501d07004100402650342d0090450740d02c05c3d04501691030320104040129152090104060b001ea23002041407030040000c420300f075085901c81d480701140402c1003610a102200d0b05450307013012440200040010b401c0400017004880d109141029000e5400d940b46d0545d00b04413200190000d82d00c03c1044200407092080c0003889100300d5200444c81c059680050040c4035600644c2c1c100031200c1a130280c1c1d600c00b008840302504d442c114014481d0f840d004000c0403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 56047755 1250 56046505 56046509
    0x120225031103120315120105040602030906010b030c041502010906090302030a09060915030b01140a0201091208040c170708030315180709030f0c15020c1e030a1401110301030606 78
    0x1003030350320750500d26190004040d2840c03120381c82041e007160f8815680e2440c1458188040d500418a8444080d00a000b0711034288101c0c410100140c482c200340c1c01c3e080c07400c817050300a4050704d5010001d20030020610026142260b803482103903014914000c0003240542007001c40140f4207070414000604054000c005009084d12580c2d504000300d944d490111452443c80c40b860f42c903016403e0040202504c02d4100c02805079040c1026034140e2003100a00c58070b94400603003c40180d54071a810420000d00b20070a244020b0603207400b10550500303840e00444045a031161504405501c1d0802021440500c8040f000f02888000c2d6901c07071a11100c8103c046822a02540c400c884608111095107060a031080c0601c1356907590700301c2c2c5400c568804520814402c410b44060303060010000301d40801c50803049001c21294054100a818132040c0031640e1a4801840b4a100500c004480240c0300024411f0183d6080a0540740404820700d0050041c10080c0000303209a00000020091002caa000041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 56049005 1250 56047755 56047763
    0x608030a110c06090a030b04230309100302071e03110d02030d06120f06020a030209040507020c131b120906020f07030e0306040308070509120601080a0614040f12022503 74
    0x950703245441c100f001c0c500c600e0101942c03085a5000500104816551459100d8407400c0754000c1c0c01550310156001e02c91a0302c4651031a4400501c03407140303041951180d08080c1040c2825030070700721641e03181d0421941101c820004052a10301e554241845843d4501d40018080241e0b034034803400d40c1e0020346940c07140c4400300511381000d000058074058108418132a58201102c107490a80655905001e9400f403a01c81003015003d1119580541d500d11400340109d050743c0081003445030f034400f407010448205500b0305070b641c501100c2c515014110f003030201042c40c883c0340009038841104583c81c024120b0440240c05a4404595a076411607080300034061307540240c5070b10051003440c3c810180c1e195021200100051800c41c080f501c00c1340107601600c000344cc0248149880b1110001c7d00d46450026841040307540e00c110031100500c070891141d400b004001e14001882c03403a080c1c81d0143c03840c00c41480101440c4070f070001005003520a0200001d210b515140d034105001d03040310300c110f6103081408151 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 56050255 1250 56049005 56049013
    0x30b010b0403020d03270b0307030f0912050f070c03050109020310060b0f0901210501050415050a05010c08040e07020607120209010906110106030503040b031611060a0207060608030a11 81
    0x4a00303100e10314203450880f0340c002e108459440060b41c003116000d000c0141d1b4054481c0c65140142910745214a0340003030b003c0c0008141d01c030b24117450300506a400640d01c1c480740c2413925a0660200da01451242e0906101342001030341c42c082d00c0e00c1c03205244035408018048429004011003001010f4105071012402101101e1034021142c0500044a11034030070302d1030070f401c20008401240b88482c0601266941418615482101401d00103024140d500440e05840c0d0b4840040c04645850b20030103112801c20300741e06000f41c1c10400400c0d401d80450160905000340c14050404108440007180c010344640038241480c1d0502010280d92a50203480c4070011444d00100403e11041a10075603981180c1651610305283c500a41510040522411629a5500d48402002094040000f08001c0c002d401d02c86d81c0da441e1140000704203550084800041008804090821303610004044d500401c00c8080103a03141d0312403400030018000c5a101c0e03655130001007040324055030421a00706152451340151 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 56051505 1250 56050255 56050259
    0x607150b09090c0d020d020301140a0606020c2b080a0f031116030806030124080708010c0801170106030c090b0306070305060310091104020412030905090123030c19030b01 75
    0x8481800302d40c104015404920030722407900d80805241c180364006010060341c80050380100742035070f804000d02c2d000d03110040107001d208861441620300922240c400303001c00304044030020740e500b0489842101c8954482054201005111070303160001c13980b110381242d0342e55030100301508210948141c840031914101e00003d402e040071040340c400804044c149281541c071035500380c40b59080517050b60742540da02c41000c41c203640319845890466030103100350b490742032401c802c0d1880c29125400c2540280d04060034003018640101000341903a600c0c0440300941c2c087c100c1164010140b5520107048002c030414002040070745070b4060f442500091f41507400555906030140c0944001b540c3c0690554402c8040d058000403a81c04030500700d20074050103d90450704000542a0b0300b268000b03106004200350002c00305600500d01400608044d55481c040e0341c5008203107100b600c1d41f0101900c082d01c848591700f000f544d090000c3d107081d200040c0801100004080c081c2040e903130070700044690a03502d42c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 56052755 1250 56051505 56051509
    0x103060b040902030a09050304080c090109140f0a021e0306120f0d0e04090f050f0d0801080304050607020f0301090308011502010204030510020a110601030539040213050607150b 78
    0x1410098940c0500d0061a091500b8144402903100038900807017940e4030520b130700001d80244020001440814010300d0070b04112010000765150603480941004c3c0f40807c0034a24500c10541300b588105c00c110f8441140e40c40d00740010107445030340640d8000815500100f40810b08000240d1701a002c00e88940c0b00381c00603020115035a1440041c3c040031988484c0e2204c2401e44100c3d50401202001307000403500032515070340c4075030081141c0822540c80d000b0b544d03c601c0c10340741080824101c2c4004e1511201a514101101d41c0728400c034002c150082c43c00051040542d1203801402c0c1c030003600034008021015072400c00a01d60708081c040d1005001518040003d154814000d84e0156a00400a0101000021070700b000a40c0300038180020f010700d054040032443e00500c00c180c000c5000c5c04c040d180345c1c004804059070890074114054a80c104c2070099102c0041035441c451000c42e4151401aa1020f400c10204440746e0740750b00c181d40c071100000d4402c00700101580d868160b4072040307000780000032813442 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 56054005 1250 56052755 56052761
    0x12010819080d061214010509150c0a210603030207080304031505090a0f0803070806010306031527030509130b060706020f04090e010c0207080d02150c160c140103 71
    0x4620140250340e00000c15210340051a54004030100080c400343e07542001d1605184495003035822030010440d102c08030790203000345030740300070440c000e02940107a642000d404c106014002941e0404040341d012200c50007818403003a18450409401e04240303c0700e004602405840c001103005020b044000102654004196000c0d00c5d0b00c081810710381801d48960500801c2e0041c43d2a810340704210001c40403d12906800c3e840c140101d062982d2441c000c02c01901c4008058070031410907280070010804900425414494010380147c0030aa00c0c1e4030440180c89444801810030041c02128100c00c01c0582003c001c0c10320640940d10107603400112007903441200c0e090b0000c41e420801c200000c0700040c41c264003c001d03c11203500001e0500f500c03070081d0000c9580d441007a4245a540d4000e400315940c0400c550310041c034403980201948000c0020003500d0303000c10400b0080680b10710740800d07074010b0000e0503a0410050035900b0800d003074040c1003008003808984a00b006407024a1010015940300340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 56055255 1250 56054005 56054023
    0xc09161106010b09010309050114041a0f070903030302070203010e0d120e010c020319021f0203060301140108190203010b0306040602070b1b040b07030203070b1006140c06070c03120501060302120108 87
    0x200f503040c201080c0000541c0603210129089410f9540d070004810040703681d0280900490256140071840c00205ca28440700e86006099000360361100020040ca0380d40c0100b040082e6076040c038025071104100e20110f80074000050600c0214007031020642c0026522101c0d072084030034080010301c004038035600001d0807500000441350040c1c000308800c0d840303816104030340d844c1c6490078411a50255841c1071600742c6401401e401208980d00041400b84a00e005d018880c41c0c40094a048401c80d458842c105540d100090328654000307140580c801d043d0340d8290b0103c5913901000d000c0d504c451520380f81100c001d511804084803042039080c041002c41682141c0341440800440b482440e040c207090780e4060036001070790120210302c800c0100000040419560340d014144421010b0111410080003411001008440240c800d100780502c1013074941c00036030140c001c800b41c01e001a807020b45003030407204403040f061383c8800b8a041c41d00000704c040c1c0c55802041c03210401c0070907007102e9889011131034a4910385 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 56056505 1250 56055255 56055269
    0x1204030f020f03030403050f0a0312051513060905011d1b0f1c0f0b0301050109020721020703020d0f060b090403020a1104060503390604170c0916110601 67
    0x200300d44600500385071407032920030340c40202180d061a07502d40d2154a000481720400b507694001390170000c02c0540024024642458540b000d100c80c0ca08540860309441070321518a20489048001200302a500d41c80b001c05451010010300c641d43c1c441981d0070401d54040001c6000a0881002401c58100e1461400c00c0840c00303100d16103001810580000380303811070030003103802603c6d03103000a21509662107850000031180c40049010b400d03510805003100e03416802503120b140100a2840015404407441e1602c0e641428581d600b994010301c102d1420500c2d800c02900f06c680020000c061003c0c0e401c040000351310804013400150f01c18030a101d0130801c00c2c0c034000c0250344114007180008071203503080400c10304080c000041640c2d030350780045e286c40c50055440503540380c4c459035800c0c0343d04005203c13070071003000c00049070560b054500860380d580304a114125006c44011010601508207208140343d008006241c907000b0b04082908620002504420101103040001c03061050800803070a64122404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 56057755 1250 56056505 56056523
    0x6010207030303020705011512140c01020705150c010507051207090e0408070525030b1006050703080c0403080403290403080a0c020c0901090219031b050706090c140102120403 77
    0x2642e5400d401a40250350100d8655482d10b0101c10503903a0540020000c28400008409001503801c0c01c4848441076800d0b00364a401110000c0b43c9641c002401d03804031401550500101030841500c0200307401070310751440300740d401c0c0010f0025855000e4080e040400c00035401180ca51510740782900c2c036001c3c0d882114503424078000041c0c0030458803005040458041d5040d552500000c4a001054001403e048a0112038105050050005091184ea44501d9182404e000242040c10183c0f441c002c0301c00081c1080040320000741c0344100101520000d41c7d024180a440320340f640344c4000e002c901580d01004024510b10345c1159201d805500c14021381d059240c001444d1108401c81028088001d9a1411352281c8104855951901c01810740204100e40f401030300c41c24007404448401854040c00f10416081c2003801d0107c5a00c4940800d150280341042c5a4071461440c2c02c0014014021014006c0d10301104000b4480f21301c09001c140b201800da0a4803a16080b5041010741400345010182214071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 56059005 1250 56057755 56057759
    0x20d060c0c1a0105181f0303020d090501030b0d0807150e15060306070c1101020106030203060c0a020f030c0303010905060111100c020106120c0308090609060a1106060105030903031902160302010506090a0506010207 94
    0x380c1640c1175410071400b140f08491041690748280036412554007c40c01a4000705142c000198001c2e0300c04c3c082e103024603060140d040c103c80002c0070070b4189500500109030000e401c80070091008000300784240e002c0800c4c800c0f50000506503485541c0c80c42094410340660000a07194500032400e070348039603401c0d25126440b294540700d07580b03402054042d4074190340d40e0340400320159a0400c0514840c4103130501a56036038662020090801d0350154044000d44d0060051b05264440072083e28150707034880200046950728003004a44008240090b0207981c02840840c0e440e150309600b20b682e1540241d0007e0110315a102c44440e607045c01c205014048400f960b038203000151355140280286a0020442801d122042e4005203180e40941d40c0380021810300001a04021414828a40c0c440000d080c05810f502d45136162948a01c801030188c881f90791210420000d40e5040c0d4184c40c0640004894814030071500d00c1d0290007084107981c90b500c40d107402c000040d9000c0c0f0314003c05100d4003040e4007901e2038034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 56060255 1250 56059005 56059039
    0x3120f070f11120d090204060906061d01031401091d2a0f0a18230103060507120510080115050102030f031003050303070806130b01021207020d060c0c1a0105 69
    0x1401200c264800c50090318600400f894515001e0480000c80364000034200c491841000308880c20b079403040c400c440c200081080b0081d004195040034840c41030340a50380440890040b0014803030340c40000800501c6200200c0e6014840d442040c4403d0301d502c5144004102e100040eaa03060700004403245a007415000c000b40800c0075607441d1032210050003841d04851100000348507500c141d040303003020036a50140684004618090044100112100e03500c0c0135141984510a01d0414000603091030b4552020502540c03003424650200f1140c01401c12860414580c4000783c8031003071042140660915040c00c2d108512000280c0032260140c004503c2c0c40c4804110b030090743c10042c0380d0388035851a030b140080442c1e018002035118841c2036603003c0d141d01e05481040b005a415a84644074540782444443c001d9800040f5030b050990036682d640e07211411031000844600b441e000042049061032101d25103941c100001c0703440144501c8000e410b0705004e8001210551091003511703440a03101901400030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 56061505 1250 56060255 56060267
    0x20705090c0a0302090a03050a0201090603090209010b0a1b0b07020d140a080c0d0603030c03090b0304050d1d190302090105100f0305040609050a030206010e0c0f07020f010905030601060203120f070f 87
    0x2050050401609200260f40041c2180c0361ba41c2c030a13541501301c1d0070560b003190b030b004100401600761403d0801031800190007141900d070301400707004280600002c03c03109203401410725909140156040081e422000d1402045001080e154180035110705603103042c0c00c40c00303459415030204100c2002402d0a0a00c2d5088070b601101900011803004c081240220340e03400c600030700c806140242c44443c0002c62600d8000c10311210b82e40420501c00061003130000182010405c4205c800d0b507454101042c48440c00814003409200542580c86400b81c5180c0011410b4084002d044034004c598942c1580e80c2e880500151143c84604803002800c8401d6000b03041d8040c2c0e01071500903008a00c0050800116500d01d890410201c00640250b80800c0c0100600c010a00001e42c0c004044200c0c181010f02c82c0b195011f041c0610980240b040300c50740055103880c1d10500b0080020480202114550b50b5a032101a49a500111550788450f9100c0300241040d019036610718001c080c9951002c7c0f900700840411250 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 56062755 1250 56061505 56061517
    0x60512040609170a030c0f030e0c0405070302092809091e031209150b0a050f01051804021b0d020a0f030c030314090721110904060b0a03060e060601020705090c 70
    0x110003d6240c1210360080e2003002d000e014030507490000300d50280346000b030301d8070f030050050404060074058003218000b004980019403140a07600440e2584072003805802a000e582c00c00307034000803030110b802e0412014603401071041f82842034601d28540c5904081c001d484611001620100314110007201558003444200d140038002c1c0b07070000b0304c1502a01200155040311400303036001000f4110184000c0d082d886520200d442c00c4803200784a600d08004621502d03010300001381030040202c0c0402010799004140e50000710001d00840d0b449a441034042c00d40e080d11044040b05100e102d0281001d103000291281e0f445400091000d1828403607641203c500f1840c00f4100c08042c2c590175182049403445405500903c24000940901400c1c0460450106082d65812081050b200000804200f802c006c074200040300741c4a0380132564a606100014060303140000390407e42d4041c3c00418049180d0040c4070303120885040c0c800580b510401241da4010302c1c05001e620070301041c08542d14001c1c3e5401461 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 56064005 1250 56062755 56062763
    0xe100519050d050a0209040506010905010906030e030f070501050121051209060c010606020d0e0108010b0a03150305060901020301030606050609010f0e03010e061509160509010f0c050d1107060512040609 89
    0x842c10a032080d0740002e64409944000c0050340204250b046403400740100d1342e0090f02032078402c45461800c0e00007482410107210b20424140e40b080d50708860201070048a40c00254503e100d0381d41c103503918040380289024800c0b850041c2d0f03d0a09103a240030040c5503804000e4010000703003803000d042e04903c40f86074088000158008810400060701c90002e00034540182100d4024010454524001425090f560400541003080c000010301c481a0301000b540c188221034500010122006403105411406c6d80d08050110f110b05420841072400540040d416684200020300c2010750707070802d00401e40031701d000841c0400c0500000003180c91254190000304e0b50300030004940d1070401c00300941001c10541e150940781904400600285c07c100c1c40407a009400c0d081c160301b00059428008045024031840b680c104100038030a0410540f052080a8403a5002030681d0011428003002030304000464041d0205030103901000034600d40550f0a450300c025880c4101d65441c0d50b50340e1003a00030040420111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 56065255 1250 56064005 56064007
    0x11206030b090106030309090e071a04180605010207060e060702090a110d0203010317070314030903120703090201090605160b090109081909080106120b1b0d0c0e10051905 75
    0x700d503000040d0703800707551100d000182d0503007141402410107595030041610b03d42400800580060000f03044400c8480c4506190704044001400e9607032446103502c01103d1002030a180f494100895100d841103450907000c50b44d460742d66020079900716511070115503000b94184407070009410300c2c680e06580700c61444800162106460696250340d080280350440007a400700044c005c00182d41380c4100110718030401981481c980f40e80c010a0100002040904200c0c0880401d08001c01041a03034401102d81c0c210304014581450000e00070420900141d0002e01515400141e0500400440c0c60000881c0d114948000954450071540700b0041e0284559668441554002c40c1020b00502407255180d030a12030302807401e40c0c0042800c155600a1600b03a454034104000e80004030915014460740041101c0c0541d40e06008900c001003d6003508145682c00607200c542d000e002c3c2c3c0101c00141c80b588a2060501000c82845503580b0442281404110200303d1b0500740d02288100c40c4001a241c0747c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 56066505 1250 56065255 56065259
    0x10605060f0a02060a020310030f0f0c090b01180303080a1a03010e030405011103030c03060d02010507050604081c06050a06050702060d11030a05060f031f140f090705010c0c05011206 80
    0x1040e1180d00032424282541070100b0700303070310700e642c1032101c00d4001803950340942c02c0d810401140f00c208609480b0044c50301c40325040b8001000b09090070621030b01d0300b00012010203507540300c400d4040c02440a0f4180081d200415000b105c8108025a000360b80d051340d078130002da0791844c3c21007000703010210300c464500d42e9004031039055507002d014501d0451312003409141c49030714200c009080c0c40e0b11100c003134003550406d004200c0c2c140c680005603039004808945c180055206400145d07554421400f0182c502e0203400c0401050103040b41c0102003000c3d10600012021035a000355504840e070500509600800c024001c100e4030344110b0281c4072560004103185e00c1c0c030742140303030080884a00c500c0d484808031000c01004845002407049581c04801a21040000034400000030340355603800d82c0460000020b203d9417010b0303580380d51112100c1904044204070509040e01c0c1c02e41c92400860301040284540b040110b010b506c10000203510315070003140e00019500b07010064460401c1c04003003890565943d000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 56067755 1250 56066505 56066509
    0x2070302040e010608210904090f0204090f120207030203190203030f03070806030c01090803030708180d030e07090e060a0203190903050d050c0a0905090c0910020304080d0f0f11010605 81
    0x1040b88680c20b01e0300006210340b034981c8003410305134204424200c80081d10550b050b0000e079101191400c8204640000e07000c02c1030320307100e9503030201c0702c00284d08030f0702d02140d940400c0740c9144652829030050542150034409048120f96076030300f50200941507046596060300700c2070a4a0b6440d04036100506407801c01010400800454204580107000140c0600620200303040510007602a14000e2a100580c5810601842e80c2c0740320140940040090320000074000198400004c00c2500c00e130020380340314400d0340c00028040d180e451010707459030150480c000b485403068482e0515041148000d06059a03510810034005e400c01000c00c0e50f00080c0320710b10507100c01103220300481755100c1e803038942c0c0302c540070361a050844038001d150200c00e4000b00585180d26401c400b481088030300c115000d0031031b541c4840e80841c240c0144e2a4490f0030011a44072070031099000320103401500d003500120b0b1303198495004100c0300030b407800c10400c0c0810220000c3c00c0c800c501c10040c0c000d100700d00780004903a045d65140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 56069005 1250 56067755 56067761
    0x150a0b091318030f0f02010203100501210c020309040b03010204080604080703020a02180f0a0506090a020c030706050f1911090f011704060c030b01020604170a120e010501030c0503010903120c0207030204 89
    0x34040f80050090001c2d19a19600943c600071003001a00c000c50941c90180220034020441d80141d5051003400c6a8200d66054504055260300714450707002e00444501d400040e550f6045019030610a6003094210005824140309440803640c8a600800701c1d51110f407210b000d590f11140c0140c00314015100c041d40540c5420b04410211422100700e03030b80310700d0311001917141c04201070070a40f01c2500384014130446503958905135410100c04c032001641d50848440e041c0c81d520510b10f0007840030707007060208040d11050020039842580100880d00d128076080c60183c049408801020500c94010300ad000c0c3c0e1404c15011018500da01814401e29000035820115100c02003103038100d0304070340c44030655030301c01d5858050701401c600e00b80020640e6080c01e9441043e4260202c070040003034100402c02400c01e51040483d02603002d0382c0e0b40c040184c100001d1181d400717894240400d446c1a650302c000002c15040501c40c03201d86075003542c0c0d80000742502c00000400b800b041da62100031440350180c08405a50382d44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 56070255 1250 56069005 56069051
    0x70c0c0e0615031014040e1203070e010206070903060b0609030102030a330e0405030909041101020606101d0a1a1e030403080c090a0906060206150a0b0913 68
    0xa03084034840c07a20004101180e0366071a0181c81c01c00c414014048458101040101a82d1009200f000b1038400b94000c50700500103c100c5007014400c0601c05803a540b101002103014a0813551070000410004005a03996035003135039800001100f203a010000b00300c3d0713036128009688008194518100182c40002d007681c000307841084449984a40701115900f03061800500303800680e0498a02d1034041c610054003013114420100c0783d4801d403001400b0801c00f8404c961103450001d182c0e107491300b490f041c01004400543d00150140c4201c0000c01c806103008203071206d00d03056a5035410411541450701c6c2290b12000c40c00c4607088941c9d4200400e001143c10703500030255140710303035054031400c0040c881c032003228100300a14505a000c2041c4008694080c00060b8002c0c1d52002490761141a000483d003030154940c49010307c1c501e031210219101e0783c04543d82c0d000d800c40c40c8003403000760400310070415815494402c41010390401c1091a140d42410000300d03400c1414a03d0024051020552443c1010094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 56071505 1250 56070255 56070269
    0xa02030d11032e0509060f03010618060605040b030103080702130f0f0506040608030703111212090115060905040c090b071a0901140106030e031e0d240905070c0c 71
    0x10040014850355100c3c000d0a82c14182d84614070040b41150300181c064003401031a000c0c40000c0000f50840d11542c0c1c07444000301001d0000c0020359a105042c0441c0c10382311440d20031542c10440c0024045200d4429a01581e950b1580d0611f140d19503920354071280e0100404903040072180880c4e03200f0b010b00d4071070b01e10104000760000c61003409820301c1904607100100765a205034070b0608148002e5100106407a40280d05080083c051905180a00c4c6800d41d01468480c178502d002a0240c448aa031b25140750041d51044001e02c10510344041918016005004802c000303a2a043c08021500d856000000507240f603082029405403520152580d07640319000c10764070705407406118100c81900201183d80480741c080208003440c452404241c0c5034030103104420805498085108080c1e07002d00c21280240c0c1640d4030640d0400441d13035080709a422100d0046600d500c7d080041c0c00a20240c1680c0040b0b81d6194540240c16042c0300b04c103002000090100320400003141036a0001076600d580c244040c03c99 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 56072755 1250 56071505 56071507
    0x1c031101050702030d270303050907150201020a0905031b01050307050d020301090b0109082404021f020a0201020613051c030615030203090c0a031a1f0321020601060909020a02030d11 80
    0x801c0400400f40c5240d8412019200d2a200f100c890f07849040603d1b0098581c9403030046a0f035120307007842510708240f43d08181c00c07040045000c1c1c1d45a5030154020700c402c4072540c0360060140d0340c60f0f040544841c00d04440c0340e01c2440c108641040342d881600195445810781c2031990a01c00300d00f0305070040380c001742c200c4040030380e13a41b07170940c09980c00070382e000005d050300310051203c13601d500030942451005001c51072039101160041011561101409515410340000c402801c00b00c1c9034000b542d07034124000581c05400b41038080351418a40c0b901c3e1052490b001001131107040041803083da001c1c1082c02c0e2450030142d5880001c1060700303509505550003101580c0142e104e04101d1103850802248a41191040c10380200800c000340c0d2030720100003000c00b02c1c030120240c2e1355080001c8001d07403200188480719804440c00442002644081103c005059081d25600b0b00126034040e0fa95150038042c0c0400700310819400c1100311003a400404031101b8a2055a00b000c111100e00c10590700c51002414031444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 56074005 1250 56072755 56072767
    0x106060215180a030309020d02060d02030609010e01050105160f050609030c010507020106050f0d150f09030905030109030801050d050703081b06060102010603030f03090f05060901021209030301051c03110105070203 94
    0xc00311034060341001c0d502e0942100a448200015521400a5001010f154075841d42d0320a55540a24050503241c01503c0903544120080c0881e00940c4104d83c079600c01c51901001143d00c000c0860204e0580d031040e180c2520f00040150207803184c0d00d6644c81140c1c0800d1035218840010010f010040c01400e20700e004507214281c0740c03c11400e41e10014840021685407040401096131801001200c000042d5000171070500c59062a03150089680501c11203641018000e00302d0503013551004489500a03900c00d282c0a441c1d004150903101030381400303000127a480c00180024a00748003200f165030711403000c03142199500d03134484000e60840d07207141c040c24980c000f001200500c1030100303a5004909100800c003903410f582d40584111440c240c10800c16036160f1007001006159030404032001d805c5001c440b10703444e040007214041d60190500002a1710140b000c80c43c0c0309400401d40c2c0c180c5e4070062a0106100d5410300c032a07101c03154503c060f01040549a80405001000e202d504d0191600e613014580e10b038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 56075255 1250 56074005 56074033
    0x304090504020315090c0103090302010f05090d03140606030a1104081204050103050108061306021602180105040c05040f03030305060f0d030f020705061c020307090b04060306030c1d16020f01060602 87
    0x41084400d040110010041103515075001c1146c808604003402c00042c070500a0130200d0041c491281102c0c801850b0500340002801d002440100380350741580c1c00e004200e0b2031603046680c54010303a10740740c0000051000c00e450380303829081150514280d80400307040c070785d58407040c40c036128030481e45464440000400f8021541e240c095140500050070080615007004641c0220b80010441c0c040d11090380812140c0c05140b5030080c031039085400130300c240c100d2440205812082202840b8480c030030b91828a030b0601d000d0081c0d080c1c4040307440c18409100d00d14910b480c20b40140c64020301c2940d01110318890a05503949217000c405c08507002c3c0c0c4d11520b044405100180c51320215400891140000348802540024000000440c04901c65000750304c1e500c40040035580b00080750000245c500c0c0104000c10820751580c4018112402030501691983c1e88102c01030880a11942640e00034689034006124151500c044205d41c01c451304c1210070403441c04103100d00b102d1440d0040f0700180c11013105d00c8a40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 56076505 1250 56075255 56075263
    0xb010509010b0f030703090302120a030617010b1c020319060e0106060206090a110303040803030106020f1006050109140a0b0d0b041407170403020102040e0a1b0e0604140406050303040905040203 85
    0x141c005051124034183e00055403585500008100300101512446010105407003803041170711050751881d620303444540529010b0083d00c0d040c00340541500d2481c1c441700c0c4070381050043d05100280581110034001d01c4a013002c01417a5502000e0360541304008000d650442d4008429170b100f8014100080d0860411111609490460f44180e08540c406010f0008400001c5a41081240c2c040c0e0001415403264000c20b0940c0200c3d40495284d01011000194150700814140d41203140c120075180c00d11488000c0d00100e503d80d01500e070014003070480a020b9040024044100b482004081c914959503480d00c00d01260f014411021415440702d4038003405042c070780184056007030f03070a80001041c90b165100070b0500c910846107506650f043c04c0460300780750003035048901610b4104611091481c0802049003c2c1442840041c0542c107900c4045e000d83d0b100e9a0603200034180109414506032070701c41107020409450401c9980030f540c441d00014140c2d001c0008000900050401013440c0c50140101400c1c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 56077755 1250 56076505 56076509
    0x50c030307200a110402070609061404020a0f0609060503070516060b010f0302071a04030c200a0e1005040510090501080705010905030d020d080a271b0614070303020f070b01050901 79
    0xc26840400c50f08006043d1850000000c0d0007620016154001400c2c12800380401d884064000c81c5008401420004401c540d984180d00130303034410300266507c01d240030350311089100d400005407008905101e403a1280c00255004289840c10700d05144800d0360301c030100c940c0020103c5403da66000220415604051600f42e0540181000c509103006c6881e030701b0440601020003c000410b50300040c041601a0140c0c9807015041450140e81c0e02c0141842d44000c840c1d108914800c2e00429800603c03d201c02000364030a45052502b5a06186044180006010080c00f800500300d403015003c100f281851003100e00802000300100b4009190400140201e80c1d00c0c0c03c00d81c060342200904548035138000518401818842c43c10200070307600c0350741540081c4003500c10082100940d10424000d403422032118480d4038000d044614405001048000c030321100da200e407001250708142400c03481d801900203041005e01906015240240c1c3c86423048a95100900c1181d46c240500010f11481c2861a46280 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 56079005 1250 56077755 56077817
    0x8040302011808070b0a020f0301141f020c0d02030c04020a02061009150e06010c2102060f0907030803040c0f080a1704030b0a0218060f09010806100915050c030307 72
    0x301142e2181c03201d0041d4440d403034019002108000c04108840c82c0ea40c1112000341090725034640341d58603510320200d04006002e015204020313001c071a00000da043c80c00c0c0800408513400515000101500b40580200610400d9034580621401c003940358840b0300040c00782ca9805da010b026546030a008010701d28169402104c02545020781c0200200c0c443d03110308081d556107489012003550b41c05e0041320358000c00e07140203050195800058400c0744203100111003a0a0f15001e07240705684548100100e641c1c2203c0d02d003456448001d04001241403240119002404bd10341c41c800709864180d00f01c02c140c429801560203501002412040c845400d11010203d810b000c601882c0c54a1a00d648250b40c50140c08a96010750000b036980d800360141c0342d03c1d00000d02c003400c1d40c2d80b0341c0200c07400c40140d6000900e0040c007040c14800040e040b0f19200c035089650b5540d40e00e0301800907003131005062034500e91034800803d000041202d6958418100061403040030165504507810b08500c44000045488410134a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 56080255 1250 56079005 56079041
    0x40801050f070503190b040f06060f030e030a0c0609050105070c12031a010f0507050f06180106050303121009090f03030e03090901060f02030f07060e07080d0203160f020603070804030201 82
    0x104002d0342c001d040703a0f0030281d807010383c2640720811500840148070304280c240d486482d04682030464281500014222a41ca4540758500740c0019000d0b800d0300c2101d00608216041000100c0d81301780200c650f00030542c054500018602035a81da95421940c06a405102040f1644280005c0110540c1448000c400c10b1405010350411503140603503034502c82007036505001e01c101280446911034803c3c1c031241500001110f00300c1c440b09050a44683d07064590140490b0f0782e2001c6580f13141c05014580032154054011460002900c000715407025002c0c00304030025034245800114111130f4003480501c1d0f800745c0704140c0005047e15020342110103050408065030000d01140340300d0303900c244c10941100c0030342c10044200704207114100d0461140c3c800041c0218404954802800380540c004c0a00180c01c6040742c51064035142800d5403a100508440010f0f0710070400e030400f0724008500000755610401b03442007608540e500048882d00700722044000248058100000d041e82401002c00d4074280c00c8200f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 56081505 1250 56080255 56080261
    0xa0b03060f0d0c060311210603060a060605040b030402060f040303020102180906030c0d080d0c0e0415081b04090f05030a0305070809100207080c07080706030b01051305040c09050312040801050f 85
    0xf031100c1040361145200303042d07544007032014031014541210141955448194842c528002c004040e540003030f01e515000303109007000902455014407800b026607410362207680c280340c54100104460341c40240102e030482c1e03050009a00074003a2102a001a40c8250009600d1b065180c0c2c40d00761003204100038601c94203002c014014203480201d14400820029030f181520410380c1e0a10507030920418505292240c039000d0982001030b03210a01c040d81d01703130031181444034152030303450300a94807003034001c01d00c0a400031000300414000400640814000c050800f007a04c0c18030303031a1048580c0311000262015000051082d001e0340d03042c07044940c040d4250801c08040c0c00c02002031075452030340d940750f5042d1a40c009800c3c0148a131220986548801401c11580d0f00d1f52a9064591900d03020b12030000441d0818103150b4496000f0011b0321440c90b414280401c40e5450002044054951002800c0034081030314000700e1103840c01d1100303031009458107111542e55480c2c0038074182103c60007001008565031003414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 56082755 1250 56081505 56081513
    0xb0409020d0b060409150b01020705060408070b130801050403090512060121020d050f03040e091f0207110307030605011406031b07140712031b030f110307020a0b03060f0d 75
    0x14565458101c1d142c2c808a55440002c20010040104040c14421202c1c1040e1048800c9400440d40f0310350a07800e48511a65540034043d26000310b00032030a00340c125220600c02c4d00142006001400b08480c0c4020390107030f580c0f10680c01c5074801d403029400103012446c140301500b010b007508180c0100c05801000b1640c944030140c4400280c1e90303030250b1210b4811804809540d900d134504044035410000380c5210100041c030790f56480d4064441e804080a4607000558040c0e004a265513921034450000c0315901c03903c4c0c40b40c000961000100b15040c807400d14076176106441c2000ba00300998030a880001d02541130500342d00d4005007188002d44110f0341003007000740c1d40094440040740c60780455540d6403201d8251800d80d070162003820420010307110f0000c0002e40d411605115070b603120300944902600010501801508450022000d0080b80707084540d41c44580c4680800ca40c50300004040e00c2c10310f0311980c0056206010740c4e0040c0031458000c002e200700c0b454a108100c0030351000300e8224640c001e103075403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 56084005 1250 56082755 56082769
    0x11130f09061232010203010f08010b10230c03031302010e04020901051b03040305030c060403080601080c070f0c18060504060902030f040605041505130b010b04051e030715120b040902 80
    0x10198601d000100303c4a001802083e02d0890181003000a40d281e60b104d011410320b450030b5200d0b0f0300c095801c14400c50842d05051440851103d80c1d0703505c43c074030485034000c01540d041c54142002e0403a4410401a0720701c50040c00914016025100724106480b150f000040002d1059884140b107544104240300c0c0c1e036030f0444101d81020292070700c24003c450910200e02d056018a900c0038042e4000010000c90400011404500c1b95100c2d4642d00381c02e072604001169981c004903499240e41200700300030400b141c40701000c01d486500c9907003100c00c040d4841c045050392b04040815440070076140e080c28042d901c2c25004e60320140803076040444c19494105503102e405840174002070726255440c4046810b1104603a98141341d02d558800500950a1242c0b42e54402080342e4016a04000c90f0000070400e802000101d40480c2c1c4001c1001540c04001312403e0314192140020b07a42c14441c0e0744000540210001850000b00c1268a580600e41540c441c18010703280070360111442140740030704e8140141c0e5024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 56085255 1250 56084005 56084033
    0x10510050d2603010303091a0301140a1a120901050709061209050d090e06090c0306012a0303060806070305090d0804030e130c0320070611130f090612 66
    0xd0308203401840c0c0303040c20b40c9980b002c1d52004a44540c52803080d5407500c031220045049074425501c0130303415661618a0213503088800c0c01c8442d640001c200401030301e03460701c0b4404191000180243d11440d43e604056484840d0b00c04400351240c00801d510134508060a840c60b400800b04000703015900c0d00440c000c087c003103180288010300c422005403041d00d0796158001c251350341d03018007141c044081d101005031480340c0510604034602d01070000218241000c000761401103900c14841801d507240c8038010344003c0c00010002021051b5801125400001800303000c114078020346000071883e0420030411704207a00100b0301c000703041c1400c0074000740a03400211101062401d140030700560700e691800312403c52980c1001d541c0301e155814a441c2681a56004001e028403d440400c2180d8001a0104000b4425204040651030521210340401ca980d0080b1190182d40c2c07505074a8607002c102303070b82c04600c5035400240704629280c0d0144104d01240c4521000b1b4052294001480c4a903603a0303c0390207402c24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 56086505 1250 56085255 56085259
    0x9010315090609150509010e0c0408060a0b040e03070b0a05060d061109030f06010602100c0e0603041209050d020d080304080705030c010209031b0d060b0301020d09050f1615030b010203090d0f02030606010201051005 94
    0x10000190270a862502910090b08002007507403da4102444110058085200c069114a2600f082071140c001d0002c1191002a13100d10030340d140e550750075118001000e008200f940c01c140d0890b60007001036510f2190301c2c818180400101d846419210606240c018581801c51840d4000c90040c80a50380004140100c664501404100c00010b45003c80d01101e515613015000040031003800100481501c264003941501d945405000d0382d24001c22001c01d1a289003c1d4001c6a54200c0c203000c115584001d41e40305009032042d0b8541800c070383d0303403a145600110005010740d6022a4443c804d207802e04c040100784015038166002504901c1c0000c2d14201e90303100080402d91f0f45c440750307522602e080d0151481c40c0540341040080b0341036414516101d201c00c01600d021400380310314a11901c0300344c2200d6800d6800710000208038400c4d210064005203103140c01c443c10351100303008030600c9603280d01211505c1c40c481d01d000403170300307905105140c078003070f000340032541564100704c100151103a2680101c8111070007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 56087755 1250 56086505 56086529
    0x80d020a090f030524060f010516050a03080103050706021515040b03100614032d0709050c04080105070305091c110303040c050a060c0503030109020901031509060915050901 76
    0x10019060324944915071020840450b5100c0000a1042c0481d103480d41c0d4040c00905220415510300c80d1000074000c8030f080f0780c06a411403810031503510a001030f000d949401c01e4084030408164886614068202108074001510703140103104001090041e08001c10441c0014150541007500130b1400300b0001f0044400c020b02c0800c00205070396a60840b03048010054192400c00c6400041007003c1c003824040c800500c4001e041c40e1140d8100025a19490190b9001e8240003400d0803100c01d5408030066480620740c41807010120307000001c3d03ca6280a80142c04906542d245000101c509484008280e5028540390034200000200d000c205000d40780e0480c1d0040c00d103203071040c509480d040c8040e12512030900c80801040b0410110a01c003805940d0100d8002503a2a540e641c21942c0101d20440101150030510041014410703e40140440c681c05040c0828023841040741070a0041007a4000240141c0b1900100110311a62041161401052132501c080798204800b04181c130070f040c4242103680b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 56089005 1250 56087755 56087767
    0x203030f060f040504030509031b030303010909150513020405010b0901090306020a0203120f100f0807030b0601030603120306031104180206030a111207020d08041a041b09020d1404080d02 82
    0x20700c030060b0074942a4003c0c0100510305260400401c035403c440d485a0092280c2100c9420340f030f2a054890450600042c0214a184c1c00c0c80c152001030300030b04900b15010840d0a030b00e074040c07900304d01449100340031004500319170b0441401000140c51040c1c1c04004603c10070429100c142c0d1340aa1284241c903000a4096528940303d04201e1a52150708840d842240811092000340c1070711901450091006203010041e03103849102042800205114403910350b40214410400078008851082e44a001410000b4206aa94990700c10302c00181c04c401c40002e41e50081270040002c4c6c11548103019806403010012004042d03800d01c0e0480e5048006071043c640807000580501d40c9400070f00c80b6911801c0b126444d100c10f000201c01d403d0041d12020054010304609a10482c4138000e4944125000840850b092040d0490000151405401135542c00e0705030030708d08050744403d2511001041918001039556144011000444203012070810b614404802400301007220201a00c040f0340d4103210042c0c1d562 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 56090255 1250 56089005 56089009
    0x31415060f040b071502030610030905190b0901050115020703080d110f031b07080d0518010e15090705030d1202090a060509010206060316060c15020c030406020f0d0203030f06 77
    0x10007110300c0c0c4078061100041c04252122490003800005224441004010312140c0c1c118061b0301003100c2080d000700d08070f00009583e920a4000e130a15500131700070707215024856200610030b4010703034506459034117a03082403100c2900309224a60040c0103500e0f9440c220180c01c1d1009448402d50b10010b060000c02051303007010110329501c604941c0f46601480d5580c1c1042c90340c40e07002c0c2c0e00111a403112548949440c2e01c410300c030300011030300319941c0105460b2401203c0704c8403100402c40500240b10342410210481000b4900b40701ea0110b0b0a0b00c200107226134900407103c8940480c00500d411080d03001820f04000780c0d100051000c1003503a09050180c10700c1c50710000c000c024000d0382d40450380821018000141329400c2802080305420a9081e03580715502c840605a68074000c3c103426000420100c4200701440c4240c1c10104014410411a80460501c526000a0360400e036007801030740c0c100290070001c0580411072004c0290145d030103005503c0c26600003030746030f0000404c950600d05a18000407015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 56091505 1250 56090255 56090257
    0x81f050109151e180609030308040f060902030a0615061e030e120f040f0501050319020901120204150f020601081b04110c07060e0a12020f030106030f0807020a0603141506 75
    0x99540800c00f810803010b0759009205103c846005aa80194160302084040c45224010b041e81d4140e11445500e880d1030340c860100c01411007040c6c07100c2d0355482d01c41006035024003ca5081d80c1c0112404920324604803200d8001c001c95500c02003e01c5031602e207204005240b504050107000c0305050014000448a50003030410210050a0b08105000202c01035445d5410300a44265005071030907121860301e920040d1594031043d100c4101c0760b103904031072440600c006d400400c44910107250040c40780511342d41a501743d800c59000400c0030032400e42c9400099600807001c0d10b050300f03103100810165150060301511440c40f0200040c100c2c21b101c40d60303005a1555000340c01040100a4a203030b80b000349200d200c5c0c484100303000d644005554403025082e80e01e08070b56080150340140c03020f004070428a908100c00d40b50031031003964240d501c9920010118101504040c1124080c00c50075555007030500c10441040a0742d0007103000d0616098200343c50707400080020f503220302e00a40c00011140c00000140e42 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 56092755 1250 56091505 56091527
    0x405010e0f0105190501030f0b0c16050304080c0603240604180b0907020106050609040506043b0114060904050709020f040305070e01140108180706081f05010915 71
    0x45449900c0420180201c154021440303200400001c0b2250800c071a400d41c2601d01c00e101c003900308442203050f00701052000c214285c0104101000c0c5140c40c81c003600c94000150407100541c0e1640002c076040043c100c1c00d02501040e480201d41d00b62440c503007210159264041c2c2190007100541820740d20a5a0b2155821a0007038020440d038007200400ca05090005043c40c54a4540541c480d1008a16180d00501407030b001c1c2d5400a080078205456041030100403d801004203602070f0b2950005086400304604211820b141c0e20400c1e000c1040d04001c001c400a1201d805003405d0785411030b4441d0320034410341301c103030824421900340b100354856060251074030340b09070001c002c00d9200243d00721200d40408014421031b07100390300b0340720003030360756000362101d40424405d58204091030301c4440b10f5580315505880c3c1c800d17603100301c44540510030b03203800f0302d080e9403038011401180c04481400045a82d101c1c031007900c0782c1c0300b011405e4141c0c100400280b04190714807641e45110700508510034a68054420904d0f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 56094005 1250 56092755 56092781
    0x20c011503020f0316091104050d030201060303141e1602030601080106080705061201050d0f050a06050411030303070c080c0c030a0b0f100608010506160203030307180902120609040501 81
    0x2110000518003940d0210a100c224402c028440c0008814100800c041d030640c0c4003500300e01812071421400f00d028104d46490359070501c078204008103495079441102da880d6801307680005822410340c6006071140c0034441612085120900c01c152905090011001c060001d6000f1141c80b038100d072030602c55101ca0080025858052040042007265056001000300c1e28070404858000e9603c0e010701c10244500824401d456055030300600c940e041c000c1c00008140d00c1900403503c42c00b15601d0300c3d81008000c61049660540f11b03000d01050100c418481c910006044010b9440c500385018040e02c2000211030003010194003041c0140780e94002e1101d0700701d100016091b545030302c41610b401d518401c801c503040042101410082500501100c164506842c029240c0d0b400f40d900382002c00c1084e8000721004106010884603040040c0c03010f001070f50060f80c9540b50f441c25030446120120050b106030b08060f000d07034410b0101a11030340c0c100707000a42242c070580c0d192065031940e080071030140800c00500700e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 56095255 1250 56094005 56094011
    0x70305070206030906330f0f0d06050f0a060602030d09020103060801110309010e070303140c160b130e0601020c061308011404030822030302181f03270f06020c01 71
    0x101c0d1040100300c9510810301c54121034000c00402400c0381143c2100d0b9010201401c00721103900315414030f000d45031347c40c00300180604503004042000400c1d030500d10380c00302c8550b926101400364081000414503004043c031601808403e050100003940d0340500c9100c40e143d107031074404600030369012703901840c054181880248502103500f180002540d2064440c9010343d0701e81510142164008039203842075a43c50b40e140c1ba08110f0710540c090843d0031610102040d0b00440006104205400410200906030107030190b403510b103400716000c503283e85070b03000e07401051074001006103583e40454807480e40d1000304c0d042511024040b6100d40c1c0420541c1000702590310b05a1350041c102d0348441d070f96208500c40e654006550340c076820f030300380d07011041800017443c00000b10f54800000d02030f8010704144905606518419440c0d0000510b500307220b000d07202e041d04040140d84080740c4e818000c080340c1c20303001904d040100810320609248150343c1807000c3c00400099103008200592038045422012080c4000c2c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 56096505 1250 56095255 56095261
    0x3070909020a090204030b0601050307030f15180509060a0c050904061d090d02030301050f03010b0907080a20091002151005090a0506090f070c0b011e0b070f060207030507020603 78
    0x81002031681800c182c0c0b190509480014400129000329400d070f03980141003948039241c9a0066801d0f07003001e0b09201c24162940d402811f5101c291003220010052503507003401c11460649590130000c40720110303a03541781c14002007040310240012280d403c2a0050f07000500c501c0c59440c01c070f409020f0011500c1d071003810014000340340c03081c10040e02c14908111001d103000d911145015031780d6401d10030654015070001d10041009103090038104c7d16100e80580081141a00c400003c1c050180455448003c2208003040c49090704051240304400f041c0d0144079008440c100302c8501c42d5005021101c1c0c800c0c508101c500304514400c1c4800c0d1b00049200d20002c1007418070b4003004114403200e0013001d00924480c400143c51100750300805001d100080c02603900c6803106494148801e1009060606114050300c0182c0043e0100c6c070110b00807c9641c010511402c030344005d0400b25981640160701e8032906000800114051f001e03512206684080016a2510f80d1f160944990158a602035407008000c410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 56097755 1250 56096505 56096519
    0x2010c330e060c0403030f03090201090902070b01170a0506010b030603011508010c0f0504060c03030e0f100510050d03050a05031b030c07021002070609030b060616030f030c021c0f030b0307 83
    0x300080e0750346080180c0300d05503540540903059016611000d00001d184242c4200704501950045902138018504694050b03103d0b15200c0580c0c3c400309049a00c0b0018030010072895903114801d03405050210090301045101e911621755944042c044d1a20300368000000c254144d9003548583d80340303030420324640c1407107a8400380300d03009041c0d400e403880100e041c41c40110070080c070445c01c5a05403015a140c1076941d41c0c0780e4078114020f1041404140462187c42e021140381e00003007001034044200300314041054a00320702101240407441e03010380c0c050098920510002500101958245000740ca0015140c0c0d490b4580c0c1c0025108000d44e120700f4110010501c48568007040041c81030500075030346400d841d900500e040745d03228018400d6000080460006200040500300d51a07002074006000e00e0400460f2204903007025403807001140451100041c41c20115014020000411003500107010040000c1d1b0f0494502e180301601e010130005002006030321640a03907c1b41c41d01c44000b60450340c000c0e8503108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 56099005 1250 56097755 56097761
    0xb0306040914150105090717190203091e070b0f0a02011803110d020f0c04020901050903060f0115030e030a030c170906010602150c0d0b03030d050405010902150702010c33 75
    0x45120322061000205c0c450a1049101c2d01500482e92802c11100f071034401c4911605010b00944803001d240c440300c081040c0c4a002460003a000c00000d84404000c0500c0e60888980000c4405111380041008101c0150351b5000d03100003510303a809130342d60307044145400c0380181b82c2d924132859410803c20740d40040c581c3c40b41c202d50300d0300c03022000c0701e003102e08400007a039a8203144101c4034044e6203c04e5400d0040d04090300507100c1038806050003403c03c030802c4002400d011045484104101c40800100100e4400030b14a0801d6000e0303040c1084140e210200207a120712601c1c4060092584402c00485220703c00c01d0f40c41d440300301d13110134510641010b15011307072160030a210303003c01407169115101500c040c00c2c2500d4000d03071122850b145002400d4982c04080e001614116070715010a11640302d162025024071031150f03206800000e04e00c0b18a02c1009841130342201c0d408240041030001e100142d8000290a10080d04080d500f500243c0002145610301211042c0100042c904030000c120441560 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 56100255 1250 56099005 56099023
    0x60206010312021b1c060e0102030a2007030810030203100b19060e1207050d03020c0103050a0203070509041104050d0b04050106050609030d050901020304030c06020c0117100b0306040914 82
    0xd06500220000c003001203a5800d1440b8403214106080300b02e070813880c40c1401c04a03201051100e40f650740f589082d240e2030210b5020071a4001c40742d400004014601e0300e18400da000c1501c610b55070a1281e503550a441005e4000c2c00402028440c241d00440c00000c400440f040c0207542c000c08498121400c50041c8019000e0800014000c0540d40f0729119038481c20018001600d005549550000314003504014620340940f211490a009018001c2403685481220316132090003a001094101c030004001000c07140014180340d8035602c10320510030701035403040841e00e08120407140403076010006418480c061050303501655210310b8907403035032082002c6a00110b00c218083c10080002c1c0741d03a84240038542c42200b40f1694190403a40e402c80300d043c02000505000341040c03040724141900c1c3e5541c1294031301281c0081c400b5a0003480ca084566a0000519180100e903070154491424443e28220503caa14041c0720314110000c00001d080d611558040700946421070461a0360034203411149459241030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 56101505 1250 56100255 56100263
    0x210111e1207050a06060902040b090d0804150f080c0906090d05150a141509180f0601030c031b050109060309050a020d0c0302011403070804060c170703020301080106051203040302010302070314040602060103 91
    0x41b400981c182007132003078904030b03561115007601c2c1840e142c2c104065071001d040100c03040c80080c040401c401d841d89030807070310002207500c8900c000d40e00702c200035000c20350050100404000820020340b07152a039030243c554260040d140398103000198500325080c18611109045a001190100709201001340c11801c090000c80f20708481544a9034a018004250025020342140751580800c0200c428000c2e203415072020300d4141c410f0840b99081403404e2540c203a000b40c803400300390380f018030034840e01071283d81441e489030401000c003e1030140081c081c0c074854403c60040c140e5400c485810311200f8000c00c2e1015038010080c01880c061490b20102520a80c0002d82c0020500002e02c04440461021280900c8035501c80c6100da42d22a915040600901058002044842ca066691242c2413207134031030140d0700c0d40d100980c6a60420030303018210344140d40194806c2c0310700200350728660f2000c41110140c0ba020300c0e000d03036a03805600701585d1090b02c2d054445081140050001411a03010481c0c0781660301c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 56102755 1250 56101505 56101511
    0x20c0f0717010501030b011e0314031305090402030606010f050405030304090c0305010e07140a0c06020d1a0d020a090b0a080d090302030d050f0909041b0609030210111e1207050a06 79
    0x403900701c0c200e860900001b080c8014506c0140400c1e07900901c0d164000050381000c044140c0c4982e14006004410304840d001c95001180b40300b10b090039041005d014110070755581c842072038140c00196890318042c3c00e45041c40028100d040503244581c08440c00703040003a00f02c95882d83d036001c4590040c01900700d4000028030b420008030711405c420000728080c0b200e41e0380d10018104540003403403c2e98000e81c0c01a0900102c49081d400054041c005010701284c5094001219401100c1c84501d842003020694403031401101140010303541c14a001e003c3d1850804005041042007020034403c4076950440b014a1003140b00d40100c10b5403103140300d07003500d10a40944113017131100502901d050041a66140008005100e903568504181c10840e41c0103000301e00c10807407005002001304125017160041c2001a044143c11300035410040007031160107030380b481c1c80c1c0d010114094a03940c6074490310508100c00c2a1140c1340030310340d0204000e02410f10440c1d43c880c658544161800e6075680307806400071208282 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 56104005 1250 56102755 56102789
    0x20907020d020304030809010201020904110c01050105011e081305070f03051603030509060307030f180302010612081b0c030105070504050f0102120a0e150d0e06221401020c0f07 78
    0xc404640d520318114682c00840c10300d400c40d507588040307400850300a411994240054129551035024004068541c1c0c0a100c0d0741d01c02e2421110b0a441c8160003c9040c05000c020090f8030802403003461550003118034142c012900d400001480c01e1642c510090b00a03c241440071560703142e0103243d441145c5c41003045030006038050310746002100d40b910000d000700c3d80910030031740369084c4140115880f0b442c601e000141401000c40b0780c01103400903812502c0c6c071202007088208054091003035001070211001e942e541186130355a404110310800b00d141002045c0d006c0383c0032048000b040354054085009000707002a02e454240105107070014410306104100001c0150303d01c1d40040390140f41e02c01842e0240707103089180710b010354014070038452a6411076480e11982645010035000f4020104900002050340380520302e00914118010304000461501403420300103001025810444941d44240741c54031544c003201c0758078028020841180c00300d01404250042192010841800392860301c0301c9088620 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 56105255 1250 56104005 56104007
    0x3100609060c03030908090306160e0103060b0702040b0315090d030b01050c06070e01020c04021305151602040c030212090109050708150a05040507051806090604180f0302071a07020907 81
    0x41244034150219008118240103e0700c25000024954050240340380780800728004203141c180219500c0f108001070f69110606268001400e03c0b20400902e020f202c160f0420000b0350f6a07100301803009100c1d50380c8400700031194800780400c00020210000b8808a45040507400d0f403110080386001c00024503007200000e003513001c1c0003a241001307042c90003890150350784403003a5603103c4071001c224194030074000d80f81d07007a41d00e50004106c2e00711000c0c0380c0c40350a4908410b00003121090640c00d26821000d1049080010a803203903604119012100843c1030f08000406400a03c1409804089200035000700604910305400c1038406603c5042203558290341c810600340c442e62924100601250440b0100740101c072540c02c065000340c040c00541c2d001e169110f0000c1c0a541085a0304004402c0140030000d41c0e18120100c0c0394420800c0d601880645060380b540414171440c50780c000c00c00c5c4e03804c0750001e0a01d4400c000102c05007507038022103600000c0c1400c0705200c581081078100e1148084800190f030303507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 56106505 1250 56105255 56105267
    0x1f08100902040806041401060f09020c0610030203150402180c03191e110f03040302060f1b04050d0c03051207020310091a0a02070b0a050a1802060a11070806010605031006 75
    0x643d0100c02a00207074a0760360b15103240b0f030600b1030b00207425926103201150712584188010000d143d01c1300700695981104417807a042403c020114030992040d40401c10250300c1c04107504c89000784c00d600c5d00c21325079035920004090f0400750070030a580070070420401c14207041c11002580034001e50a00c90040a044492000c01d9a00300d402d680995003100b000c000c096282500003079039000381400d010b41880a64400010740781c0040305c0660060f8020828810b000c1440d01c0303516007011564404c0c22000c0241f4001c800c0610603449035034010700c2074a91000907c200c0107040c10166922030169220000d8261301540c41c2e40100f07105074464066034801881e03041c4a0322981148a6026000110f03003c1980241482000000e051031841070b020002c0100040c0c401c155644240c0e00d0003000641c5040405038001202c400c98040c09000e01e0b0320f441c41026a40d82419074160180926044100c4c1108a45642c24101c0e00d03403090714144680400070410176001009184900029100000200e50b40d900032641 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 56107755 1250 56106505 56106509
    0x60e010e06040215090f061306140c070b030703021606060609050612010302010c08211801150e0601020a150507080c040f0308030606040e071205090309060906091f0810090204 77
    0x444031500e05010707100e80700d00b00030340049000107100d0581786c6003440c045851640f14000f2209070341c00e110010301405402001c0c000503043c0600c0c45500701011005155903461a602808903012404000506150b20a03011140405000300e4082d41c4851645401c40c0a4505c41c0581c002090340c1d0700010400781040320a842c43d054a404038080f043c0d00e581c0041d10280f01d84581a038050001300400d050300015548600756401c0b075100001c071031345031900d04400742403801903041000d641890344038034912a0307001c088001e85426090b801120344031500140d02d03082c000e5100804588900e0701c2d00c108108203612041c0b181d015a01c41d1800396590880800b2944118010b80c0b04600b41c841c2e05001055443e4080e541c8110060042841d003078070740243c0c4030f60090894800000405030800500c07400024055640c01081e05030056090140b420300249050103081c2e181ca0240d4030108080301503564210541e00c11250300d84040d98011101c48004050100c05c46451702000342079035000910750910301c01c60b02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 56109005 1250 56107755 56107759
    0x901020c1203070f080a0306051507140f070b040504050105010e10050f040e010b0d0f05090a0b040c0b0a02030a0327020105090a03020405130218010e01030b0702010216060e010e060402 81
    0x10030340003450100500440844038601d41480207010410010b20b20203200c0004078003a1035241d44810210340b0040980706141c00080c0266000310301e91081c42010b80c184d8540552003400209007481d10007000d440d0268446141c4818071440c1e000044549842004005032001614140074503a2258019602015118040d40c3c02c00002d840303100880c1e2045001e052100148010700c0e15143d590403030302c0403403542071300700300b015603000940030760102000e20a15002841d00101441030303103804136105454000107032024103494a00c0001400308401c6502100c050818ac1d074007261036840c0108025a6500000d84a07400300c3d02d40b00d111845004820f035007035107030408104884e0141c0015030045a480c0c0016030026081070f4031410110050f503d0303004181c07040f42c013039410440417020343c01007203815800500d000b00310302d2040380148000003400c14084d06594120714001000e0b10b0394042240244180400c44400030344920084e41040401d4204822410b55007009001610302500e02c0c90300c1e42d100340d600035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 56110255 1250 56109005 56109013
    0x80f0403090b03130221100605150d110408070503060112080a050f071401020d1d0601090504021c050705100f020607121503060203060307060504031109060a0b0a0807020d0203090102 80
    0x100000c2803000441e4400000e00c20b0080031580c075404610400101c05001284888400c100740d40c0606c10019003102254402c8140622441c2c400403808001041001e0700c01f010700001c0d010420803440c2c02100600681c5821251744568500c8115100d500b02e00407107120740550800020b05c0000c0c08101910304d5084950185404020401510103902c921945601c0050920500e40800c1c1c070041c03000841c1b442e10300050f90390401440403504a40c030038951004581c1203520b0840452500280050544550320300008645d140c500009000e00c0c580103c48812000d00c0036420100040410760703000310741f01514464165000c42c5030540d4050202640032006a000d600025200b500c25807018141d84903a40000824000940c42e0525501d0190800c0c3d070880d0700001800301ca403e017004000c006095619104e4201402e41c1e403009000304500c0c42c103601c10012180851465603071403811070014000000025074415585c000503041c10003c0311070b04098007408040410715400130003201c1c5d070010305074054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 56111505 1250 56110255 56110259
    0x411130314011d0d0f0c08070308100501020d021005060d050a0c14042703030f110705070e040b0411040f0509060702010f0605061e0c010903090f08010c0801090b120d0f080f040309 79
    0x485d4218802c01c05482040960114000442c48013002820428003e6581c40750314900152648404545607100c241103510000d90803140079804290900513602a0350003040d1501e0ba0400207031074601102001e041401290425001c00142403200d5003100e00b80c0c240e00e1a020f040c0790820084078081d5107a0110300c03a507501511080209100143c1c3d03d18824140050601000d1444000700e810078004290704500000c0e040c014400c04128640081c5a00348200703900345000d954035101030401a04c01080c2c614544201134040d616a0071450f51540c3e032040411141c500402e0305961a03c06644445c0503529040228601290710f00650707080d5480030b48520300d07003039401c8110040c210100007da2a880f00a100904030400300380135000031366000342d90302d100c1e2500700041c41c00300003115803000b00359a1601004140190300a5919411035180c040005400c4192102080200d480040c0b100043c2c090950a80807c0350801002c0500118650310302d0000c2d07642c103035075461103042070324050302007524002c0c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 56112755 1250 56111505 56111507
    0x3020405061f0c170c12070804031a06040e0705030c010f03020702150a0801060905030624220605010207030b0f060a0b0307050403060b0d0c050411130314011d0d 71
    0x503801c200080c02c09600710440e980c406081401590b01c6000280c1035060407011302a518030f10940c05101910103502d001c280110b156500c01c4850382680c0310070700c003040103011702c10705c0b8080e41e00030f54201e00040c031450f10141c0300c02980c1c1e000304c4040d1300c164540005012142d1000400318240c2e14007400420412141d140196028540001c03231004242c3c00700a00310042e10b854403500102c000701d044d05910b07107180c0b480c00303130082c20160024801c00c0102c000c20001130340c00060700d0f5000a800130301c1d415205041e08600c83c85a11039401150050442c50306400d00b1802d492101030fa140d00504108015a02c0b4001241ca81d0410301c8064904000072002c10b8007400d40743c1d10207070045001019010441ea4a51324480d85400444003500444d2011808105003c494000c1d2000d18000721a00450b0700b003079903200c040e00046406070306d00503982c5198080042d516802291000d00d5001d2100c0029aa00d25107100903410706443c2200a508042c645054208000040c00305514010043c0816030f5000704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 56114005 1250 56112755 56112761
    0x70c06050f040f0f0314060405061b220911040807031b0f080102070201080a0b09070c03030e010905010b040605010309021302071703070206070f080108030a050306130219080105010509060301030204 87
    0x103032070140d01c41c10800010380d43c20b00b00d610b4004180001d0b540e941645181042100f200d00d41e296080c00e07410180810000076004285a0b60203100d41040301d0b010948880010780700e029000d50070000403c60302c0c800341440080c9140a08072542d0171018030a0780344481c0600d80c1402a0f00c58140241c1c40080c007400005e41c40c2e01c900d041250740501c08410155103040c1d02c400c0080035805240c150b54005203c00955034090305040d4000625002849940118004036000100c0145400200aa02d060701810984a40c2000c0c82100d41c0200904c010000c1e41401402403440e80d131510b206602c2c00f14009900e50080c007030f10700c0a44c0c008109104a400005c402000303540500b4084501202032206021303c009460003450203007940c2c0d8018081ea2414142c00360025050000c20414040f2a4004108440000084621070f503005d142981d160348948000c07444000d0304801e48203200e4004104080344050840310b900d80000203070340e4a1001e981c0c2d18010340302445505101604500c0030001030026003000c0d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 56115111 1106 56114005 56114017
    0xf030605040209010c060c11060702101a010903150207120e0906030606030309060d15060201050f010b030403020d0e0303071506090e1f050903041503060911070c0605 73
    0x110001c5c0a9007400da100501d6140c5401e0365580d510b01c104441d4070320281d040c0403603044d414130715400303500ca10070300c061400c000340740800c56602c21540d84844401c44006031985d20800d81591100c4181040341c04c004044903808104000001c0c01b100a040980c1941760b8540b0204d44800b4100044040b02500842c800da100c6802e01030155808000c40c0c40e540c0003191250380e104034103403135400500144003c00b0304030070040c41c00045094040d0822071007080e600340385401c0c582e250003050340180804e54000e401603025080301c02c0080d00800072004120001012203045c28010360742c4010880c80d000ea000340068952004101061960181e015410182805841c1d8190440074140c4191204d001141e1035540360350101c0c01e003034030510885010b0044044114480048007a001d0041c0501d44101e0440901e443c0d12250262161020348590541c4800c03200c50040c03800ca0f045906e60480 = true := by decide +kernel

theorem cover : BRFrame.Cov 55935255 56115111 := by
  have h0 := BRFrame.cov_init 55935255
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55935255 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 55935255 ≤ n) (h2 : n < 56115111) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
