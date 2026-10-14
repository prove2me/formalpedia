-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1824
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:48:35.138187+00:00
-- url     : https://prove2.me/submissions/ed45f4f0-bb1c-41c0-b614-063adf2935f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 327877697 ≤ n < 328057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 327878947 1250 327877697 327877703
    0xc03020d060b0a02010f02031006050304210206040b0601030203041511040e040b060f0312070204020a050c0d09060f0f0c1506030f0c18050108030d0b0f06070507080c06032809 77
    0x78140007207039002c9590014800d81502e0350003080007034141c1031801c040b800300341d5081c076000b0182141044814072900c0590703002400381012020491001400c0040c451070506c5a0000d0303000f450801c01032000c00500254454000e00301517185150541c0c550100d8103000c046048400e50701c0011000803440c14080d10068026003021240ca400c25043c4206a8101115007030f110303603034500d0026070350704003c60394090100c0850503031800d1400300c0e400c01c0060741041d050b1904010b8140300030a03d000f810410170031040715a03150004100d0401c00300811502c034a4401100380a00c0348007030b600580e488141041c540e40c1081299a24620016126000c2e011652001e01b410515000040a00034500c0101044402401c500004945803240401c260b81e4244620716072500148030741d10012a09422041d000d1500501d50880524140d0014900e03800054040e80c650b03202400505c80307040c0811107003080090840c1c0b8a81149802990202107224036131a025445120000286c10040982c1006030720700d074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 327880197 1250 327878947 327878951
    0x302071203030506040507020a030f0e0613090c270b0c01020403120f11010b0604060e13330b0304020d0507080615010206130b011401020c130905150702030d0c03020d 73
    0x40319080040150006640c1c29218620f00004034030814000902500007560644804001c44510801540c000440900f404e070842c404204e41703060654450418009014080c00001c1e640601d03035001000d0400c1180c445003d4000c03555012401074000e1103404c22100d07040c076101e555503071a0007110302a020310f500081121140e02c5420700c415400c4241070120b0740c41c0741c0d5140c3c598034465410600b230714054005142c001e00d0400082c002184607411084102c040501410742d80d00b4104c400c1c8040354800440004260083c40d007070201062100b0400c0b0783c04442029144039a0b00b03043e11b4104503c03000d07000900c03400a00312901c0401c8024061003000b404850185ca030b40c3e03c2c00400b0142d468940c869064018011180021001c416020800b841c1da40c0040c0b22501aa01f09041c904d00c4115524081d4154468000e0381442a658807000c0c0044d038498400104400d44180b4000b403501d0031803d842c40303591312105c04101c0700c0c0750700000765002d013001d144001c100499500380640091251907201c4010b14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 327881447 1250 327880197 327880229
    0x80903040510050c0708010c27170f1c0306080a0b0a0e10050f01050406090507020c040209220204080f03070b0f150d030f0810060c080708041d040c0501052104030207 73
    0x8819845062306040c542c80d0369074401c042ca102d495521100003070035207400c11206000e000000120f01c4040c8010420310880700c802404000300c0c0d1a00244c00b980b4100410707003006039480c5541c14007900380144113400045c41a01e04035a43c50040da88010b0042981d04e5540d10100c001c06410071110b00c19144000c401c000070f003400c1044440500d8240078080c080da040248c0040c5000d224410107204c4c20a550103400310401c01c0c0200f1010398049150564400b42004220520300b03482c0344d800e228008100c10059513a445e0411603420aa807080325903695400600c4020003080d1f40046890340281c4402d041800c0c0e81d81d2540c14550003014015140c0c02c201f0340c0418100309500300c0c81001101545c3d84480d019943d5481d85110101c40134010280092240045100020780000140c0800c0b031050000c541082d490f5507029015800803410500110810010f00013030294000b1900058030080c41d04c01d04d00507207244444a001c0324148440000c0200100240a040c42406400058615400c14060031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 327882697 1250 327881447 327881459
    0x5060408010b0306061e0f060d020d06150c02031e03040b040b07050622020118050d05210301050f0f01030b060309010603061d210c0328080903040510050c07 69
    0x70702d08420030314007902c50783d00484d41c649090740707920304820704501620403610300400600514180ca980d2041e0460790500241c0e02d9400640017078a200030404a0014013a0f00c4c01e0305080019401481200502c13003900503079805a1800b264100c00791401040c8011220150700c81035103148210f030311509441001190104852003040001c101c0c1c01d000d8002ca4400c0e1f22450b00000d5891000140760303041c039649540313010065001d9400c907403114102403802c0c007a641da100c0c003040e03d020b00b10314100c0e080c1c0c001d401c81100019a03d42d00300403051002490324103660404001c03030004004020200d1148043d465003055a81c800d07009100d482001410840d00c0e828001c00890103820350707000450380c46090401c00c285007100c2c08140050b03c410480200b51110740c0180810121202d4080081080410403c84040318400c100926414201054402078007090b0030300e42940209120606081014000c18070401080000503502540d40c1110605004024080140c8103841142076141c054000d00500081d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 327883947 1250 327882697 327882701
    0x4060b09010e10021b0a03050d02030a110102361005030a060504020903060f100e040b041e05070e0606070b0a0504020405011508040f020d1a0a0f020403030206130204060506040801 79
    0x103042400e8a0300c0c5075100c55141045481c41c100503a042c0140d110b2074000300c02040100c54102e048038040c0101c607044c2e440e500da0b01e0078603013204824405a8400074862101c40c2e0b01004282c0540c0808000710309100004100282100b0489200e813050442034a012314159800d042200b000503004240410880040401803e50b07002102c10590151406500280c0c0d41018005c46100c010000c0c086c01c01659036141c841d0310144064003911400c1e08420020415082c00c1a88601030741c002e06e00030b0781c90f16141c42d042d0f03803180141804143c0c3c0000524450009040043d004090f0342e410781480d480c2d07076076520104109000d20318001d0a0007501c40248484100164802805103009803410300044c0c3e240c001240c80e038400c07070000100040c12040004d000c92101d102c0705500301e10003820311500c030103152101c1c10038070000407000c0c0803050030200f405100025807140b140c1c402155031042d03007040d103151030107500c5000c01043c00d40307420488604401195900e0b40282d0180800810803501c941e114800d01d80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 327885197 1250 327883947 327883957
    0xa0801050109050d02030304090e03040806072114270d09051c0305120c0f0f0307031a0112111b0a060c090e13060b040f0b01021002211504060b 63
    0x40482c2c5000d0011900381000d0340903113101a000740043d0324080c582100000140041180d50305240024840410441824801c0340d00401182d034904d040d60b2091f040c401d6400b011001e1065102c0d181861302185001000d503407540c002881030031105281d680a5580c80480003c1111008030701035040070003e1503410007091001e0302c0c410742c1c0340c4d11040d1050420300d41d005200940030b0041041805540d076440c0c3c003a800a41c3c1308480300319190a100700c0c4181000c03250840351010301c42100101c100140150301d031084520000d02042c1501d0000058000a4400040505041000d588403142c130070300034034140701721074404000031800b1141c09500c2a50a84604d0801c4084a00c0360034072030100a03440c890b14030030b02a40c010854082071500c1e080c000c4c5440c28100c0f00102da0598503001282c0c001d648910400a03130032031201c40030855074021400203040503640301d044c82449106000c2035107801c070442c0701a10001d8140740543d5190b02c480c201d41385807031903451020340d01604102010540f0030101c3c0c080c0c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 327886447 1250 327885197 327885199
    0x30d0906120c0c080705010e010c20060c09130b060a02070f0801050114010507050c0904080307091d07080402030307050a0813091a040c0e04020f1b15010521030a080105 74
    0x300c0444041c540707000035245400c604100040c110348a540204003440d006219051207640001040460307a1100c40c2075038400301a241c01f140300c80e800440648090320741070f02c00700000070140403035162041101103107014240106020300032102c50140200c03810790010000b040001c04080e180c0c4a02d190003561a600b03030040465030029201c001035400e605000701c606840034a002082828048001150542c000100175185403080740414025501c03852030440c091400340d00404d60760b141161001d131202a06600144640d1480b0405140101c180c01203950091800d142074409a10743c3d00000340b0310302035000064010300503c3c8a41c82001110303401800d414030f9030604054890794034240b040031200c051010103140d4030055400a4240781c03e500844903007030f480c00c010303180c041254046012030300310340350307820f510100082c1040b8140c0f400b402e091440c41c585030042010480c003143c036004030403040c4207060040b40075007980f44840321081c84103010a001402142d48404801400070480310080c4202 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 327887697 1250 327886447 327886457
    0x20c03180f150301091a041a0405070f0503040803070c12020d02060f09150901020d0c090e1321120509010b09180d111c09140a05010903021e030d0906 66
    0x86102030502c01c00c0405070b00300b0040380608582c0b801120710064120300341c0e508008442c42c03122207800d590780e100b485c10000d0380120000c064071410045c4021280050b0026017031250281d444010a0350210869034402e6100b20400c0e1280c881c000250303124a8140801040782c0c0b0ba41280c0320049038000b40030705240c4400d46c212340305510b82a103400c1e0258821703102d16030b984c2c0010b541c40e4040c008101013a0707009120007000514003000c0d40544811101d80201d4203000ad500d0710745c2000140c0400101c560001e002c00000440d8240c0c581d00c180845451002d0440103e220540410300d03140a254031241d000440308080c060381c81c24080050003001c6a12555105240d100701041704030348100361608903015a0070007032004110f216004c0d9070380c518021185110303100381205403001164441d140100070031641c55044c0f4450800c0c14041036900b54400d20380c02440945030410407681c1c010554000c50f034068031031506003074914051102d5590804c0102ea00b51040540311490258014908001c580460340c86c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 327888947 1250 327887697 327887719
    0xc070501060b0403020d030e180a020c07081204030210050906040b04030308250311270a060203070512090d020d03120b041b2f0d0906050a021b04020c0318 68
    0xb5014140207030300010350000750040603040001d0140701058024540201401c01c4e0704041010801c0c15441264082003880c0c0200700580c070184c0c104203003c050602c00019003109c91030310b80801040d018501c030291290314050401a41030b03005130708032a43e9250151200d5602c0b41c40c0c9000c0c040d10361051004500080d030a100003a210b0740c4042c1c02070020070307005038003580b10281100e00700d0240c003602c004d61409c40420030171100e0302e44910b41101c030051240344202a0600c101c1c4108808081c04d0b60000b01550010483c1000007803002c1921001030701c48180041c0c6a000c0440400ca10070717500d07075001750003040403003100051603009080340e03000d001e15481c00c1c803c2d0304400061109945c9801d00d80404104001c8450300720902941e041c56888024410100c0ca2400a440ca40901e041c42003c940098003c0700a488240703900c4005000a42558180381c0c1c40c1c0410381c40d0007941c40c0a1107098000f592031600084425546903012201300da10420200c0c0d0300e481001c940401c0440034200360912407548219 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 327890197 1250 327888947 327888959
    0x51b060c19050a1d151308150f0403181d0a0506040204030c0b0d0207080301030f03090b070503090d030e030102070b0f060306011212030f05010b0a0305010905060319020f04050c07050106 82
    0x82140d55004283da200c4550f1612190a41340028511900d04c0c0e10041c004118070507111004c000e410310039082840340e8403452070800010b041072101001352611403058000c000d61445182c0c40b86800c00d07494641410480c0314091400c04011043d0801d4010303903400c1c0104140100c8071904107005a0380754004000310344603c03007041f08912039488002c00c20441c1402c208582c143c1ca801500d5003410590015140c07070f01d036942d001003a038401d810032218212052010000d040c0c0c0404035001408045c018136103040000c5c0c590903039034000c298020340301f003640d00060003c2510038202100d03003500180096480340345529010790030f0b260031502d0461000c030a00010b41c1c14500014982e0488800700c2104452409940f1020b801a0380600781600741034075a0644c034901c0e0500d10420780242405a04540c0382c1494100c0101607403011303449214101d0a000c2800304c55070f000b05115107142d0b8105151160096988041504070701200c0109a1103840c00c01006840390760032000381030b914419002000f0a0703031600c5c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 327891447 1250 327890197 327890207
    0x70c061104121e0c182004050405040c08070b0c010b150901050307090e24010206011a1c06060201092109030602030a1404050d170402090601051b060c19 67
    0x11080d40c1101145411507408110495421983c5041154078405602c110340c807103408140c2d041e8403400b40703d8001c11030050b90822912900c42408440341022044018000c40803c583c083e80c0110b41c400c41e41c90740440d0070400007003050300052040030281ccc0c191903554010459240c00c034034034451039942004150030091400c450908038290082c3c11180c10040d0180046401d60001869202800404080410511814681140b180502d001d010b10800940d690007415584040000b070f05551100005009900c07030324905000b0508a00d0f465a1107000340800541402d4480f00c442005910301003001c120b181d41900300000041c050b15010680a00e075007030b031141c442400300050380041c103007403801d2001455a4004503048140d200700807640e0f10748210b5030840c00e00165000c0b1002da206410140185800420000b04144808241045840c0c0390700400c002d16802411203040250008000c0400603030035801e2408041e0030400c68040b4070f0b0648030030540d64040c1d590034030403075000e06c07039407003807034854 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 327892697 1250 327891447 327891449
    0xe030f030307030216051009030f030b0a150c080304060e06010807080705060901091701090308060418080c03040f082a030307020f150a0309060c0201020c0a0f03031103070c061104 79
    0x148004500d9a6a000360440081d08200990100f96100c1d45514000c80e2041121402c0140000d034009810407643c0b0b000f9003025601081c0310249401e060000390940d90b5460503000304d541411aa08440c074034100122a80300f00403600a0142c80302005001c14000b090380304550b0880c462003141c100e6600c2c1c0e1900c540e1000340e44601c003103641c004001880b040c2801c0018000d140818140291015160580461642640078624542c0d0b0756510004041c9540544195000740c0300791000c00181c12032420303042d00050800c001615145000450a000d40010230403100109032f4010f0485a46840f00340c070342e40311800c5610340d1a1881c80c061042d0a400d8442c018002c1a000c000d00443c031b45070841e0300340b024441d200000315a2100700d0b483da4245150f0b51000030104120301d950005491051481c00c181140c9001d0502c904680c41404110007005001417551295a00100045035a06241c41d084020344204520b4981940c400b10901000907001030071401c210b84a0070060001140000c0400030354000d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 327893947 1250 327892697 327892723
    0x12a2010110a0f030806040f020408030403030818070b0301090c0e011707140d0b03010e0303010303023a0305090f0c0a0909030905030105070e010828110c100203070e03 74
    0xe06001055016404090981c240c04007a80c58102e5940c03074540140d20001810303404076103000100503c618081c4159260820013070400c600341400c0030241503490149010040c00e20080001180e0f8002c5520311040c6203959200c122070100e512640020140c3e0403e00c85c06007003a0411340d43c01100c50080a54441d603c0701a501c5801d511441141c0c40400c00c0301414000920564015181034844100000e0800c5111400302041455004042c1402c44850b25642c0c20603810610040c40001c2e804200c1d02c000303090f05010009442d09801e4054000385001d90340d003d40c0780302d50010400503505504901c0c807424424090720740100e1250074942d00c40784e41c20010755203d8a03000007400002040d81c4900d55030347c000d00c0e010800c5a101c074042402c5950942d45480840e591178005241c560b0700481b080d82c0160420200d0810303c0c40340c02120700c03003070003610382d02e004544441d07040f9030609480c015030f5000c0169208542140381c01410050080d8400da44000000c0da14610307010f01d03400c0004a40f003032014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 327895197 1250 327893947 327893959
    0x20c0a020f0111010c09060215090606010804020312030f04020f0402031501081515030105040c02120901030b0f03011a0301050907030803190b0d03032f090f012a20 72
    0x168200041c1000d22541141402030140305591807034000d200b0b0700443d441c285c880c0c1074240d0401c0c10180c900703891595228001c0d0b1183e0200310500c107010400a400001c00c0c204503126848610019084c076001e440c603000d84100100030003a600c4032101905000360b00a503a1102030201d02828130099102c00c0b10200e4071746a0b9000040c005510802e0030552001c00e2050b80303400400001d000070b145040c80ca210252070480800140100d1916201d200d911080f14001000c3c01407003080c01200034018056203605142d60785214503800e40340c0c11048502c1d0780005000700440a0301c00e014149900d20010024000d600c1d00000650141d0001201400d82c0d401c01540da042d5a507190301c1c04490700d01c1c0d400c120b443d0f6440b0040402140c6641098081c2c90b0300c6a10045901c01542aa540510f040e04280c0c060140c1c8160b0f1090400e0b082d80106c075134481041c0e80103d10b01a40e50300685503545484004400c412200b240341281e5000440d00d04400e520401e15442110b09414007246080c10540125034094 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 327896447 1250 327895197 327895213
    0x70c050910061b080f0c0601031202030c06010612060906090504030f05160212010603080f0a020d0206010e040312110a05120a020310180e06040c03060c0f020d0f020106031b18020c 79
    0x400b010200c02c1c3c628410000c66190449600314464242c2161001107002c0d40301000520030000e4035002102c40c000380f44015402c2c9094420f0050740d4030f60600ca2042840009480b01c0041c0d945a08100d0140a84140030f00080e56a4035080d0010070017284c0a8000603280605019131b244924221501b290018995401146c125000c01a403031110780302c0058559071341c902c000006103810000d0079820841d480b03415110b110030000a41003448041500c803c5421407401032083c1810088010b4000d905850251034208512002c40000d03c07603002d0700400e4120120b65070a100340c3c030400402c9441c411200c6401644c6810340b00e401603000030788204100e81d0905038180081444031081d1024a2081c900100d0001a804000f5082000959003900c490329a020113100703005507801050015441c0e40b4069100320b40012000b51a000e01800103420041c45c1c9040d811160700c00d410081c003654010311080703006240184080010806031281c1c805040150250301c4465043c0c1c82030b10160b072088800381640b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 327897697 1250 327896447 327896477
    0x71d0411030a0b27010f0801090503030a0e0307020301060314070603020c06060609031005010608180303090a2006030a021806180d03090b0c0c1309030207050d080708070c05091006 79
    0x1500300c0d800401e07005034078003c2482d0180030200d01304040410084466100c1e5040060280e1001a10380103404180e05162100001540000403254001407842e00081c01902d010304150a41c40b135018080d52540c00d0600102c18000301d01c002c80c01d211100c0086075581d075692442030b81640207030022045260824000601c00741007a40c010002c0c840c00406542400c207983c10814201e40c800c1e0807100000d40002e082100c0c044030441d081c2420070008004504510704a545103a80e01700412000341000301005a942c1210401200c468241c24010111074503450b1880d62a002500003c00c004011080402400f143d4100700341102d001402404070440005a01030500c49000c0c6240411401c002d0030303c0c0001078001400b40030b401c602402001410704ca01c0410304001642e002c082800da1814036218803440029000184481110360541e8203100300070483c14100200d0107040390290a0700b500280e800d003040104813540c010748004075414451500d440c40300144901da42d0043e000810001080e0341c400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 327898947 1250 327897697 327897701
    0xf090c15070812070905030114040f0f0519030203090f0901030c17030d0507020109060b040522050703080a020601080d08010e01031b09060f081b100503091005071d0411030a 76
    0x8014014034540340380c88180c40001e507200c841101c4200011701120010300c2585002e00a144030001c0c076014040850a098480b01141c08141400070003070501c001c1d00c28100700082c0728003121800c80000c0322640300e180e801d0281d2a40e0210400310700c078101e034400910b201d00c1c0003880c00741038903001901c04108506102d140c55018030300a034044081e20081c0254100301c260f0b4000c0c6882200581d0001c03941c101c10f4074100c0c00384c5101c010030034441d1742490208005221258078002860403075405003000c80c082800c106007041507a8102034802d40c40005c08082d01c5400280384c07412201c042c001c4a50700080304008840b0f41d03100380140c1d030054a0843c01040032410303200325540180b07030400310070304013036a90140d01040701c801e0380c89040509054041000740300e200f84419001c4c680010200c03c40c903001c0d0b10000c0c0d007140c4a040591306008010002ca0001351041003240d00940030390f2010041801d00107405001031801c010855400c0c0e040c440b40c01c00758100350040c0800f6420900d00c090030b6888074402840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 327900197 1250 327898947 327898957
    0x1091205071103120c010e2b030605060d14090105040f0303090614091605030102130303111e0319180510022b0305011706070c0222050f090c15 63
    0x152440c1d142490741400d54050052500c08259880c01d280e941c42c4403842c5c03a0950356000525401a040180003880c40348800c1e4841004002c1350000d0b201000b90300e00709500500407900003580280e07002c21203242520307507640081d031036410030009840307255030361440d440c00d039803040320010985040c2c110b40300c001a0190f00007454103481600c01040908401c005c0044650b0102c40750000c950040688040c211410041c0c507001d01411b4009515025a24444c0754030004a8071005007002229407440c80354100921071110700c0d1090a108428450590910359500d420541c03001da00110844001d4001c18050550a043d003180c0240304403895141104020303801c1c0302082c1c4281940180c00391454403440c1020641c1c10042034030380642540b603406000604a0b00140c104100302c1002c89041c8a0041e0002032844c2d22070135500c1c0c01d20304141c2510200d078611800d4001369800b0f070090341e40740d219900207400191107445543c0d08101c42d135607007502c4150b071200c144141c207030450013400d0100040800100141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 327901447 1250 327900197 327900203
    0x50403020f04021c0506010e040c141b060c070302150105130b030f010c05030f10030b04060b01181d250509180103030c03021915020a0e0402040b0a030b030109120507 73
    0x500341606003900500c544c248920700c101456840303040040640c1c000307185c4400204150742c100a030000024014105601203c2c0040390b001010461a030f41c4510a168240350400820590720142000344092845410030300c800c401500600c1041540c00c4010749421341201c000a088100503101800d1503801850b180da0941d07014010219403c11020090192005c0c09819550b0745d5541d00c1c1100c441003071b036240079214aa032110a60b6042005c14040503280c3c0d045034003c0070000f980c0300c002d4010303189601c0503103002613240c1c1c1d081c50001d050418100700d240c2c00e818090040792030741e0368611460744d0b40c1881000e07101000c0c264a0110010741c4540d01500d00c001019140607002104410043c0128100740c0c021800615250080310405a061040c21000c41c82000000c01c14180c3e6079030801800031482a100c0c80740c0d80400c0420443e80329080400c003c400c042d10440d80c481e1a2011803100ea4405207500000c282001c1d2101814141486009199600444440010082810704640b81c2d44070007025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 327902697 1250 327901447 327901451
    0x4060909050c0a110115061d04020a051c0912030c08070e010f030b0303040512011d0d0206060d020f1003020c24010302090711010e10050c030f06101709030705120703050403020f04 79
    0x40c11b8191960040c0c0c050310450700c0d104610911424400c00d12100990210b02a070300500c50841c0326034014061300e000c6041d40300759a5115090f110500000c000702c05001d0008898a9604d0184c11380551003807020b03441c10360302c10050360f80e00f000035a10444c004542a000809a09421020034820307071002d071154400800740c0303150944c0e500000e484240c0542201e0216551075880b404000d1508415003004d0804202500410315504000380d01d2300401002c0c0e5008940e040011011076031020403504070203400501c3c15241c811507201c010001e4108850328446403041a00076510000c60001c04d0707a1999402a80200030784c2158244440403038080e010724240210007940b54020340382805541d050049000040c2008100320b40c01e042500e501506d0062840c204005020110070b08070700c40c41e80880c3c161100280f1401d81c1108540d00402c02e109480070450b00018003459182c080010035895028a007200c00030401241c80305014400c500009002c510308010400050800400140c00a04000c0c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 327903947 1250 327902697 327902711
    0x1030504030e100306080a3005120c0403050d090816030203030304060c05360a030b0414250305060601050309031605010209040218040f0e0a0308090c0d030504060909050c0a1101 78
    0x12041c47c21580b40c20881d0760060b005111020001c0c3e41800048419410800104540404101800300d124078685c3c8200031803503c0020300ea41c000d00302140c0003181d0020441d20811a500f40051401d40f8a000c3c228850003800380355024550166030380c0f000c0d0390300200551b01d952a5503841c0002801ea030b613005000d018081c8005440d091034401c080c01c6c0210744280425840321124003a0483c5520f5401d29482484c0c061400d02c0030a40c01c81a5aa0140d80410329100744003401d02c060345030241d0313013404800100e94210650700340f10b4a03500c40d40450740315030200c8409403036040040d5064001160030400c48d07401840f40800065102034294252406031000500e011000000316040c0d0744070707600c10492444c489022125508240c4100c43c0380c00443e840800411109030b6215403240c4600b10080d04111410000c10791198050118a0400100078805035801099280c090426001131041e04041b0b800544009400c001c1402031a118440700d01c80d45140121160066400e2900401c6440c4150740e1520 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 327905197 1250 327903947 327903959
    0x20a0302030d08010e0603010507050412150f020903011a030d2102030f012c01090b01030209030a05070503160e040f1a0f09100615051b07030305070204060501030504030e100306 78
    0xc1d951182c030003030795240581d40c103250124000600c040c0125020340e14020402c40a2a0301c0710555042d01c0d01061041c01000441c10031800e43c0c8141d0f00c004c05060703d020000c00c03900300180d009000104007500288850f2100d0004036941c1030090107025055000100c02d200041d12a401508100e540c0c01f00490042007200101408c0703030400c0315103440942e800401485000c6001040900c000038000d600000118507400800317a035030062040a00d901c0e121081c1d2110bd81c06070301612141038010302210002003850808584c2d444a52040038042d0081c1940c01d10182140b030400000e44220708800121030b26a0f641340c212507421201d05440040900c0d0294000104402503980120302c0d136403019801d41041d806240c28031601d554440340d040e107050f50402c100129038035a0417070341ca41c40c100342d07032540c4402c0c0c1c10031401e4280c0c86024103640500301c404400c041c0c022001d03144460003a2410090b054a580c015806c0300c0c02134030003a001c42c000020410492504031031130307040d103000b914001c6103141d0390f51 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 327906447 1250 327905197 327905203
    0x8070b220606060e060319050a3306110c0d020607080703080610210c17070503040303060509071704060e010603030908060f06060d02090301061a130e0702100207020a030203 76
    0x160301110240d4441504111440d400310102c110030310100e03512461410180410210015140c951003815a11500020001c017034a07400040c03842c10007990b10844500c4080d403015007030004140e07032540583c00b40d00031601c140300c0c045080c101003c9038002d0500107100700070064022078070017080360300160170003031000001c1a040184c404144aa00c403040c0ca42002c4040200395140b5500720020400044402c1011080242226000040285000583c07554101c0112500781000c03803d070784000048028015800c1d444001035116038065034082281d03545950030040c1050040e10b00800044035580302110079821200181d800c02d01c180e00008002100e00714242c20f44280d43c0c01540803801d13800c0e04011800003488040e910600142149865240130340010b0040d0003825030640c510b55001c81c141941d52000d50040000d00105444000c1512000c0c4030300d5002d61241c2c45001c0078810408002810151804240f4080ca01c82e40103001c500c11440c1c1444000d4000100503a4040b01c103810000241c1c03424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 327907697 1250 327906447 327906511
    0x8041104020c0d0908010e032b020403080406180501172e0303030f0501050d030f0c05070e0712050606030a1e060b19090303020d0c11030d030204051003050408070b 72
    0x3034006803002040f2200007401c0c035a8a9070000086904155a8010520003c02210003000c445107050700d00c01d010911040010340d00b14010942184000b802206101810700503104440c269070b10f5142d0ba000c40c170400d50a0b4a0548100c6010403070810071100300a0790114600e5011420714580b001d250408481c02184402d0081481c2c1c9950711040140709065142c000e1a55110700c0070350510580d4900404616480298440a010031044d1607000040620584514202d20340010448070101e0301e9110b040c90300081a1114008540c0d2005e0940041445001c0c042c440c003c020012401c4d81ea800307003400064068842841707011521003100c1c0f07501044920900c0040d10712020f41d0364440e07020032a80c2c1c4682c03901a070700c1c0301403203031365802080003a9000461900d80100c91604400c056994a800e00358180248501d5a15000341301184a00c3d40d8543d01802c100d032811644103060303407000c240941c101c0c1c0040d1005002c43c001003041d0404100201d00f115000303030200e854881c4d02842d8040c10f840c15081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 327908947 1250 327907697 327907717
    0x22030503060a090501081b0102150709150206070801050f040207060204090903031d0318010c0515091e1c05092211041202010c02040e07081f020702100804110402 71
    0x2005101c96030a00c015010b01922494400704400d50510000a50300d180003d100703131a03a24840d140e071107180d10030b00c1124007021070417058810328103000c0005481c080542c043d00791004000c482c1175051074030020f135050040366641c07901806a400c100034000e17503403040d241564003c0d4082141d0030000d41c10388003c0c00104448400002d10403a070b0b2500070f041c3d50089903440000141040e032018040b0020040715080b0200400c882e94002d0800c0c0161a8040f64404c00340c070902484d80754419208468006078030a40c12041500e04903400140d45d10001142d40c03440e074003580c0c0940b80c1c4600140058042e0b094100705802e1031401c0039031050016040b03052401c0d84002c025010071803401d03010540c0c050003840c40c286280d070300c2c10a070400700c1d0500030900109020b810460009000020f6403111703800301c80080c0d001000e8910349611840d0b59991089000c240c1c0d03d04025801906811081510940381c05950040c0060030a41c01d1000480f516580900251940420b000e440280c079504c030b02c010043c80340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 327910197 1250 327908947 327908957
    0xa2c03030108010b0d0210030b0a0906030f030e120a140114070c05120304030c061503061a01091401020c1005040909060c08090d0e0d1104050c072d08032203 69
    0x204190ba143d080d111200c2019001d201c80c000e50314016540c1d0310060060150368034000074280104000100341e1041c0340c0c04420250318002002c0141304410f40c0c072000c2d85021351501d2030004002c4c428401030142146032101c040d007080c000e80700002d4901000001d01ca0450b0000702b000e40c0707040d8240740c80b80401d071003080109001d02000002c100c0280500000c50120703200041c214a000e8801130120180d0303e00c01010b46030f850003400043c895500015002d0340d04044204a12213600c0103480051224198003400706585120005200382d0340d006060f001d450680c0030b0444020b00105004059095a4805040c010148404100e088640c443d0310b20640c010a004104001c4104001c0c1c1942005424901c4a03000503886030318080e0001081c0324a601e003a10001101110760501690122108848a038401d08000a020050f41000c025020190180b074201107520010000c01c01030000c800c0007254003c0b5170105e0314022807280c101a69010740e0740310f91406044000c0c8840401201d5144044000c10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 327911447 1250 327910197 327910199
    0xb09091608010207080405010827030918010b0d0207030c050111030105100206060906061303020603040804090b01020601140126040c1a04050120011517100b090a2c030301 75
    0x14859000c0000200341c41d03002145403031555181c45509100394003132a0305000c903402c08261a02c1d0269201c04440120400501455580b91260341c1c8a0740070350540c9108015903604040000365198060341241c07a410021480d280c0c200141001039048107000742c041c0480452a0700c0072035000e00840c55104007501c00c0c65903139810f010800c9100810300400c0340840d44101c0c00c00405e03803a051000e94001c40d04503034450f26980000602e010034200382c0c0000b900440301005110070001001301910940341613402c1448005811001280e03070f450244100400141110124002e550081c04002d141c200c8142d2009914070b0404e60402122a01b664100d84d1128240d0082041c2e041c1c2000100030000d84141c902e103014a0070b80028403140ba00c4001d0042240c842d090050441d8007544004411301414140382540b56988000c0819072050103441c480038010500040e5007080c1c948124020108020035110882e1a00e10f040c0b070080070000c049480d00450100c2000c0c813100c2d141600c0c181c40784420020750f03981d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 327912697 1250 327911447 327911473
    0x402120405010c031103061c0221030309100903020a030e0a030606080c01110c0a09050901151706090102160b0a06091805070806040c0e0903190c0203010507080f0105040c02010b0909 80
    0x40b914540782c0e003100300c014010f110b140d035182644d0445500401524070201c111600012b4001c0034041c3d40030800c82c9030a603070354001c8100440a0361059407003c0940300010448070040047e500159002401030700216881c1000a02070302c140158860060940402c264407543c820080f40c0445c0c101f50303c103900200c0c0804056a010180d0180742100d0b101400e007103c004004135142c404503002c0d401ca216121400500410400d5000c171070b020149140003220144c0d58486d0102042e030300e400400b414082c03200026141c1704c050084038811164840706003484145038a804407602c0c00a019514455156100094400020300071106036202c1e075100080504c035180390a5280041642c04410250080404c220115861030071140403140d04420b40c50350350f038607480785501754800d41d1030040c1006032529800028681c042d20b410b00484c4264000c10054581c82e13804d4405160403580c2da13240e0210480140982c0c10560881110000700d80000714100342076000081240b1703800c403100c00f5140d21120f520800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 327913947 1250 327912697 327912701
    0x705100302120c03250503011502010902031903090b09030a02010f050d1508010b1206040609050717011b0201020705100e010209280501050708040608150402070c0503060114030601090b0402120405010c03 89
    0x18640c015003030b01d81807803c00704046c1c198007051054a03401011040d038440307158001c1d00880c040680c02000c0d40c00564458050744003100701c60005400191109001003180c101c5d1000300d41c100e00000307005000450303581d801154162098118041000000d2108034100031540c0103840742030781e425000c01d10382e81c10310700b2060845140c491450f2090814141240d03006501060140d0403d80010340483d002e0803d00700300d443d0080b240d100901100305485982200241035001007101000340d44c85500c2e018007070504a0a0b40100440944243c200c1840d078200038a041d4000c035414680c03840050f0600c3d04010005031f11003081e00010383c1503400280c4510380e0b102c0c43c04003100036003403d0070300324140038443d00c0301c2d03460b40641c3c01280305011034017000c101008042080400e039040010030640d59810b00f0318050301145410300c523642c02442800c0002c1034140d402e012224901a01070001e1129030301e080406009860714003d01781d0490b5007000362800c000c0120b240c5a1041d40250004103070107071034801c0102 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 327915197 1250 327913947 327913981
    0xf0f13031e02061c090209010602010506100e01020d0c03140f0d0b01020d081b09040504080d0e031c0f0608031b1504020607060915150e0610020705100302120c03 71
    0x50000c56101d80310005a54550544911181140800708084850450000180360900001e540180500700006070250705402062250340103582c0e00c561a0301c044810303151400000344c00c5025820907078042801520440701d40d031246010b0702d011088100f0754104a484c50b4030040c0030761a82400002c1d440c1280941e801132100690080c0f000f0a509405c54000030002c000c080c00c580180e0114034500d00c0105800780c25503d0081d4014001c00a60601d0701e40743c440c0707030700c9513855414030350400d00340c04101362001c000c0d148104c000b841a100304031540c840050041444c440d11990040e40d43c900850340360320030405084c4101c64107685116240d07401c0d10706ca24160043d003501c042042d0100400005844100658107041d0f400382001c42d9810061401402d5111181074841419240a02419100451400d660101d404110741c0c008952180780c140400700b5181d580c41d90150748030f03120801103030400c0910311381c0607501c0349030060410782002074a0b080c01005462410715800c0100511440404c001d141c49 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 327916447 1250 327915197 327915233
    0x60d290c04030b0f1308160203031305090901202503050309060108010603080403080703051c021804090809010c0f0f0c0f060f0c0b060409050a060204060807020f070b0f0f1303 77
    0x10340c4e4035001c2440508102d52000003004401e010521000000c046184500c1d810350050a4030b440b5510031400d030409202d107201d0076218980c51030209951230418492400c4032421350700642400c000350184241c07a40d104280750034103880c0f0641e1142110318503c461080c0c46100340e079150390b2820a201054507003038068100d1107003649000d500300b0004548a003242c0440380d010300707001d446441c00d04040e01c56004140c280c0d8045203402d00c07001c0c0d00e82c24581c002c0c5031362482c410302281485c0c0c100003848121a11848021308040080100c01401e600494054101510400d1045a014419503c40300c000144020866480303c4001781404007007140080c02e00648200d2900d88c500c04c0340d00c1d00003002c00080850142c04541540003003600e5454681120704035541090880385c4c145d00300e19001c8000c1d4440d2181c500050408400310f080300b8404502c41d4418114040100602c2e410001c01c01419806480101d141c50f074200448030052404001604a0444800e0f80c12815441c1d800d0828205a12281070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 327917697 1250 327916447 327916471
    0x31e010207030e19271b0f0314010e15060a020c090f2707090914010606050c03030403030c051902010b1228020406050405011e0509060d290c04030b 65
    0x10190303000c035a80354008891401d8486007102d401c000c41502c0c9171912400070140b89003031221103080c424004041c0c0c4041481c5039100c140c110404c0904804540c011307020000300f10b1710400100141401a00b00e50703000f00d4081040351090382c00d5400a0002c0d44440000d44c0560005a030100207440c01c25041075008007108200c0e915454030b24694103801110b440310801c1a03021809600d5510020040d880140c050448100b04000007400c040c42400707548500f02031a52700304030011030001e00c5a07003030300d241282c2c0c0c000450039607c2c4c0d0b40e000d038003030031901481d4410440d013407040d0500d0349002200f21a10030840d40000a65945180502c0000a200340318400d1507446201c1c0c0242e80320241a10035851400102c2c1585946a82d100113406407030540d0000c1c1d44581800004103a100d41c6000c0d07440d141d1180c0c0c1d0b242030029602e005129540ca01140c14591140020081401003641c40e01121091910700303100c0070300c1600d00344807007030301d02c20590781c5100d07411000ca014020084010320b0039421205862403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 327918947 1250 327917697 327917719
    0x209060d14041b060f050c070f080a170c07050108150a0308040e07020c100e01110703030807110f031206040b03060f18070e0601050f0403060204080a12050a0e0906031e010207030e 79
    0x107004140d905c02c0303250030000d0000d866651034800b8007200c805070070240c00450b030740c030340d20074810b992045000350544171400041500004041241d007112030b0a8154800740c2075040c60840103503140e50006104c00e4006085440758452031713907030300c0d404c1000d10b100392042d41d1100d080c21000f40c1d0303040d4005c046400f59480001801007a030fa6125203000003c0e1146441d01c1c442940c0f4004892914500a24104500c50000e001c1704040d00b06142601c60301c4030350340341c1c03c041540011243e6680402007003d1160b8104104100c08010a003240701d0b4803100c050000b0505410120100340380c12401c41d00505842001c40c14485080c0825131009120b4641c14000c1071524140108a106010040c01050611000040960420004200b91001035400c101c0841d201c5540740303160303030320b0b0f0721903580486407003801c104080002030144060f03502c005440e0ba41c80b08030306c1504080c0184400003a1403507906105050b83c05198025446130628810060800561507411914019252100004030700c0d12072104d40d10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 327920197 1250 327918947 327918959
    0x6041202160909060534020102040509160e10080f2e03051002070c18150303021c11060601030923010605040b0603160c0813030b040c06030218040209060d14041b 71
    0x41c44906e00200440c00400e4002010f042e030080c071540c4d01440d00032281004000f2602e00214803552046120703292044029807130070800c08400884070340700010501d19000715541010401906034010301d28060580380082c400c00940d82c0c05124228900c0500f0789400900802a0902c0512803c0d4002c1000f542030030203a6503290010402400340d042440411101c002030f1075865001039103222114080c80680039143e040094a07001c6030818403811410928200484511030940414410501d0740a08155214640110040c08480d2400e03034107041c10721140c42c03442c128549007161140c0184000564103240c03600780026030344442ea600d03105900030304c10400350080d2450480a800f0540c9401c1810000c2d615110701c2340d000340d02402060510903100881000301e20f040c124002ca00030003510f41441d5032807200b02d081e4840ca0701d001c5500781e138807030f05090f5908154010b0034200100130007840c1400d00da0b241c0542124411040b108041007900c2c281300620640c0e030099600903c0c429140161641080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 327921447 1250 327920197 327920251
    0x12100b1005030408120702070e0f0406110a0507241415030a02130c0e0306010b040e0603010b09011a040b0d02210126010e01020d090c060f080f13120206060406060c05060412021609090605 82
    0x10050b0070b003d08011444a092104d476260600700003804020403540c8144e03000b079208a002103560121807944003002d511503250010700c108020b40e005102c9d10720b00400d81e05c0500a4680c07485500f00b031203020f02040d2901e03502442002d0190000c2240903407902d02e4541181108000500f0f00d0313001c0d0340341a4446040743c640201c0b19064a0980c0d402c02c4035052501080000f070b101c0c980c41170b1180d0300042120300d0280c403a40c0003051514941002d400c4082024020444020428450603880c0702c400081c004a48101026110003100b00c0f02c00060740d0010000c201d42640c0c848072417000426513a41300c000400c00507100387c00c050300e007a160144200800301c4000d09041e0001e025501242420800540114091440320b540e02d42d02c43c1908070207485940019613140030a940c202d10941c104107010844500c100356450310b0940020003044241c8464880020801152400d041107015002c0201e4100002c892044018104004002507140c407504008080700c0300505499149190440c1d0307141441044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 327922697 1250 327921447 327921457
    0x9061b02070618150210230a0e0705041e0203040b1b0403080a080c040513290603010b0703021513030f080601021b12100b1005030408120702070e0f0406110a05 70
    0x70403a00d134091500c0f1603040e0310b0591094429900603042206c90040342d0850840707903080303e034000403d940c0c548803000900141d8107500c0e41d561040d0300150040041d483d00d40c00c50005042c0329000d8013030b030b1602502c10701c00340e9100329030a07100d01005005000c1c401c80d071900d2801501c2000c6100074100744c1140e0715100b10f40f0484441804102c800d0002c290541c4003403003240e0040000601000c040d0703441104d1030300900506080080c0140f00090065144089055908000c0000500d00f83c6580e0a0952070086904170450070b4007144a0b25000c0700080700a0441d9502032400c4071006002d0800d04d1400504604500c0000f00800540100380030940c2d070005150345104c81002096008440d400c004a94240e0084d03550741c24510803080c0c1000032041c164486904c442c0142c6e050101c11249960aa0700c07840280d030f006181034410400780c120406074010a0b500103010b44161035405903610310140d0800400e907003440303140c0b200750f00744001c0006921485017001c007a5100383c0e09003c2c2e10000035240c0e002e2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 327923947 1250 327922697 327922709
    0x91003060c1407030f0e041806051504050c0c0c010c0209130212010c0e01030b03031e0705030906043510020a090504050a0c17060f0d050109061b02070618 68
    0x101e401c0500558069002041200c40c0c551445859440c03a040041070400c16401800100b0080701d40d41c0f1060400c0d01807040c0b9001c000340c0700c1d002c110690395050000d04004002100b03900a03131800401c103590b2409100e020b016118009900c070010204020f040901c85d000d8581881804848440180c4501c05410f0b444400d0a91407120302105001090882c540801001381a5180c035041e000342a8100448443c0d040003a40e00b00800003600d030034182d492180d00001b1016400040e6255034542c0703110000d0211600c03c0007585c0c04c110849021801541182c0c00851031000101c20300540d801c1e1240307103402c241111821240c10036030b100850b541c40d408c01440100807580c0021300010158001c00101c0002d0202a004011500d450301402009001c080e850b403000910042d41c45403220a8100030a024010041040316081701c4a010010101c1d10307010112015502d07101d0080101d502c2e0b01c141c0200035904d10b911260018100300080c206503907600080b060062680e12040b00c555100503401c16110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 327925197 1250 327923947 327923951
    0xf04020c0307020315010f06140f0c030d1a0117060907030e07051807140315010e0406050612040c17060406020705010e19260d0504320c09100306 64
    0xc02028040c110301c28a00301a42501c5080709100c10b440c080181c05040b1812589240c0c0d00ca92551800c844000001580c0c0039030840500c071b60f205070b00780c81000303000c1002990100c0b850620a28008010348442060340407811038070011704285960481c0c000d1400c85059801120585042e00000e00901b01c003400200070103954501c0c00340f40050030810780018100040072414003081107005810401c90840f02540001c011009200c00c04a865082e24003803c68121840303050001c0100460700c2d200c030300b400254042d440b81e41c0081e803503c078000104001e036001702c040440ea14050502c900208182e5001300b02c1907200c2803e840309503001150f550b400c10781c0442c0240c0d0b101086d0400c2c41c0907005556400d0800e020ba9070740d04505031484040704000e20b210705040300c111540e4604020252070b03124030119a1a2080106902c90251a44642d038414403e0401d1100f00343c9405c0030459000b09044800b4401e8280b4414080000d0104202c01070f51408070b612845c680780c40d0b0fa507805001020301c0020a030b25 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 327926447 1250 327925197 327925207
    0x160516031206050613031203140117070b0a0503100509010810020c030d05010803071203060b090103020a140309030405151819090c080403081501020615010318030302130609050f0402 80
    0x4207080e0010401060010a00c68603110300c20001441400307a8442150604281401c5022031030007801242c00645d50030303102c580281c0c03074512110b26466001c070902200c6c4c0600900490600c403454040c00d090505a07880d01d03240d01d0040c000b94909080ca41229204c0c40c0070303500400c886038001400342c501c868086401b50308c82c568100b0f814558001d09419a018600307000000c140e040c00000a03110181c020000341c1c0300b50742d402105030101c40c0c05004400d07051800b00007541565010b50010011500c462425040c6401040400701c655002550103000c59040001e0400281c070b02444000c6180348020304e124501a042c038441c0c0c900443c2c94001c24050200aa003851004040d84100002020382040500c903054452000901c0c0303080448080b0085510040030800201c0c484043c008005c80c103800409154a90a0b2460700501030224002c1c10583c0340e140319101c40c1501a91075490a200391005611540c12042661915089821000400030410010009507890036150f00c42540d0580f001603841c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 327927697 1250 327926447 327926477
    0x8060109020d090507031101120507080105010807180b0a030e01020316031d060f0609070e0915040b03070b030a06150507080702040209120a0b060d032a140616051603 73
    0x81c000f0305401902074000d042001003880040350201ca01940300741c1c0d60a2060060070000022510195804400540f4000052006500520141c1d400c450316040200c6c0e8a203041d2403d40d500b209c55080f031407050304040380211005801d801146a04130030600298110320308228200c0c0e8084959400104060300c95081342d01040115108111328003840f8144c41c118900742e41403c016210507038489008902c18000100701601c21394008c046084001c086809644448500c04103444800c41115802a030b01d80c2204841e03642040102d0041541441e602c1d241c0c0b0b80405550300703d4500f035100002c040b03204c280081300564460700300c8410382d5103c0c00850f1034000f5400802d000b4080c588030150030150103240c041210074000f596255042c0304201d4040245d64070b4041c4041040012801000310720311900c2c0c02000c50400c0d00001901c11918031071640031307619889522400300542c1a0700d80c1500404217100c0c012500900440021145080c05413800c0f101e100c2101c0f01c002c030f01e5800780401041c410480d00d6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 327928947 1250 327927697 327927701
    0x3030a1403041b090c120615140d090f120e090408070c120812010b0406051b0309030129150414030106080d02010e011a09130f080304030c0b090708060109020d 70
    0x700c02c150a02510780c0b00c4d1242c500344000c0c200400e480000c00c2203403819428a491500514058650012030500450f4054034280c130940c002420600741c28009101121040c20240306140604e03009100a5607020214240304422410155008040246902c0f14403915154850b071250001c1d0700c181d0725990b814940c00c0000d00b000b16600444d45011402c0b070103205200401c0c024204a6082e00342c4003401d40d0b03807604040c03642e210781e1283c100801c800780522150344061495442500543c00196445c4c2a42c2400090842c0d00303060841a03941c01d2100307a40707100e0300c0c491000c4085840039600e0050001980b2408000c0340114403c44c04503420255251607552000c0d0884c2c0010b04070320701252030030303040d458020740a49085008112150310b02800c102004204207040024000c003d400c1d54100e84076480c5142036500009800e035482452154480e0000e04000011446a070095440034040c0c0b0040c03814214480001d802c00d0b000d6070100f41c050203002e0011541a04484030784200680e0354414690b0540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 327930197 1250 327928947 327928973
    0xf0403020a0b0304031d0f040b04090204051f0602030c1f1b0305090c0405040f020f0d200906040207200a080f010b0a0f030b01061d040c0e03010b03030a140304 70
    0x141100d940440002c02c4245040514025803084e100c040c0f0361000003805100180385444900e50004500344450350300e040c0b0358010b410441010b0400311b4220b0759a000700c0e064a030280e85e80c0180790154518002c0e41c1091801e038074040c0c90b07940301861401c0c0110000d16650340304090440b1440071080c1c2c402c0301850955110004120301d60601b1594007588400c00b400034081100c481545018034190b6018a1510348a42c41c400d6610a12080745030680b43c091241c210f10109585821940c405060004103c0e200340860044001101580341212608107101400c031020f00b40c940250f0050002c10001140d0b080c0d4442d400c0801010b201e2109200c10000308074241590141da4580200855280c00c0031041d000344104a00540c3c1030b030340d0301e07a0341c60203448001120f10028000f00320340401480032030700c01c03813000000d00080800050096090000142100e545035003042c085422f089400090381401e006801c01510100e014504018003124098102a00e00002c100710399000400142000206401c281e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 327931447 1250 327930197 327930199
    0x1030b1b0c0d030c0e030706090332011b08060d0f03051908060906090103030c1502090a0b030a0606050310030308061206100e0903040b0406051309020a021e0105010b0307050f040302 80
    0x103041d01c40c0341d0b070090300520b10300000704006452400e03145100e040025082045540d5607035041040c80c51510b981100003404c903803154585900c4004068006200341c40c0b074007080d406070300002e01c4002040c0c0c80c002001d00008030406011042041107500c0d0348000e162030405030030408481100807540b40454030383c80381c1e00c11804918510142e91110f5580b0600c2c280c801c1009446d1241e5503201c1004000008109100c000c0c00103100040d0b05000411002507691000401c840240c10058204000f03160800560042c181b00700c000f0042103a00c031814095540104224103140c0d20314240300c00c0b4500c060748640805400d00aa0002080c4180c030f4004078007001c140c0d12003e407107280c00d003400304101c18503042c03055014851015000c00c4215001101304d40c01c98600d03544840c94146020b00c00c0d11030345c000170b160a544000280001410070304500003080d04220a501401924141c50414580e40074590742c0e1020301d0389020f005020304240c01003141d4124405090039a2100e80b1820405480d21031a0802 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 327932697 1250 327931447 327931453
    0x7090c03140604090b0415090503191e0212161416140f040504081c020a030e01060f0302010e1201020a0203070b0601020615010809030403140703060b01020601030b1b0c 74
    0x111005500d03034000c048100464040c0601c0762510003c01c016220500406411014058003040020301c0b11034400b210200a090041007003540c94440a085030001c800f49401c00340e03650503100682d940900c65109901100102c0e00e5411940700b4000d6a400c0e64140b0091401d0700060306c4007010380c56540d811502c1d58001e10f00320602001001094440d400000c444007010356521010402407132010700d040301250080d02011040381a4000c0101500f4094401c0c2c5a0400c1041540c10000080321044203404610402580d5450707501e800604551507110800701d00e9240400a100819000b020082280e0702407801348a542040d070000340308031115168400c2507601c00916200c1d400c2d0044080d200aa000791250307031481d83c82000690711403004841500c810404054905419801005010740090402c000c80741003544a0f5104441c881207405208040e51000e03500f08200501400b40801c0301d142880641540e5141d6900c40c0300500018121000d0303102c0745488112000209015110080200d00031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 327933947 1250 327932697 327932711
    0xa0f23030d0c0f091409130b0f011406040803040b090a120c0608280e100c030b0909010e071202150304030e0a0e13080c03070c0e01061e0e0d050709 65
    0x491801050800c0c00d0300701043c83c0c2e040301903000340940708402c12503a5903045030519900c03100400180b00c400900340342890724000c0d5003c0c042400c804d00148100e890f4404900154180b0b9480c0055102c00110719225080801c800d20880d2004001d032411903041c40070654654034000d0020304054895001403c0001200340d402c03007407005420070182110115220303031340f20740c559141110803218040389002c0005003c0c1c840d090701d0022507105e01244004081582c518070304030015801030b903d0340e900b03d20000742ca9101500062420020660700300395110000c020030244011455204d41c468490b10306003c191303100307090039510741081c801541c03000308203007a0f41e91816190180c07004104482050142c42054808241084101041c4e4014104840d0444155081d030b0303a0100150701034010082580024822a0000f07464006410080d060181c00d0f02003643c107122006000c450294070603000e4421002409032207640203200360005200594049500074003030b0800a01c3c00307105a0204040a10f0034003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 327935197 1250 327933947 327933967
    0x5090c060f03010906090207110105070213020310050405010504140f0903090607060c02011d060127090b0103020306240f0316090506030c12071226070b090a0f2303 72
    0x214141d41946601704825511111480700300d00501000401080300c0c8416209150f01031405070603818070007400e5160400030701013000282d0300140c6100507010007022090003d0b1502c0d014241c0504800d0341c2c00c101080c1495000b91003c0000360034100b076903049502040c80034909004455a0680c0584400d50710a000e1401d00c00402d215440e42d80154a0031018140300c042c40030601c218010a5802840d469003045c0c001c02740c030601c00702e01c0381d14042405404408101c182c000c1d02c000a0150482d5000340d855801072505010f00146518034410140500e04002d007413014190040c050180d0307540e003c00f801040881e1800c0303000018002c1b10752241c01c0016907401c2c5074108912501c000e8054692a6030005c0506c00044484040446140c00c44041881080504000017171039501840110410f45172610103002203414200700c0703030128940000c8010a010344c0e100030351742080d9204e000700014803a9441d502c90714110340000502491001690100304028142c4200d00701e00c00b501965a42c14a0304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 327936447 1250 327935197 327935227
    0x9063906010e071107140406230108010506040e0f070e12010902030d05042105010b090108071d221103190c15020303012904091a04020f070605090c06 66
    0x4841c8502c04491031001690321403184407600354402c103901c0101032590505503401c11151056a0301c03a081a9140c02c0045c0160282d1442c4800c0d03080500d80c100450300c0364000410442e0140c1085001e080d0070042000f00400001c906944080d04074030341c80075500c038580704032044540c5a0050394814411580c0c2d0340b2602c019400b240d01c0f80d200314211100d9609507401590030340600e1050304844003400d844064020300c0a24901e00041c80740000241890b40d000c0010b0070340748280c20440c00c0d039000314800c0c07140726894807103200c0340702029182400340e01d40507401403184070408000d05203000e10f85000d90704000110310364a07005040207098482144459014010b44030380c0c80d00070395221307034040340014482e2100c13401601ea1103015800b6510b103a0801001c20341c080303c1c1c003041506042c0074401c0780d0750001c11070f00a0170142c40302500210b250980d01032a04800b81080755060300c0790f4410400c1c1004409454200d4100942c032510114055560554a0781015030b8202c155030080c000041460111401c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 327937697 1250 327936447 327936449
    0x80402040b2107091e05040212010222060c200a03020a0b0a17060901030b09120d020301050f0a0501080106031e140f01080d09030303020715110c0706050906390601 72
    0x10400f00e840080d0750f0b54860003942c9000443c5040381511103d8400b660714150802d41e40103002410710140780101c0c2c22035500320791010348030400200c1045c1c0b01d00c9042803245000c9000304414680143c4c1410700c3c0d182d00c0c219152041c8000400a0411082c062503107400e1811002107800401200f01c0030b0f0340f460200800e50082c2e10035000994581c1403444039001d480039a0f80500000b400c078203116070843d965440801d00c0941007005502c40c03210b007218920540001094105c056560250300e035454101031042d0824180680d40c03081c00b50007014060750368000c003001d0440e1500d2902180000003404104924000b001d484a0b800d400e0006540e81d0880c09002c1034019485042203180d241c3c0c0c0d403d05a511110900028030020702450410004644079030082d003075081c098200172103004079142065088401c02210f0070b804000c007181010310b800061103620000e000900303005107028580c200040b1070f845400142c061550b1249944c40301030a14217aa003010110204003800e44e4500900c645a4603002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 327938947 1250 327937697 327937759
    0x60e07020c0103061d06010507080703020a0209010e16050d06030615140307060c030305071119020310020c0606060a05191d0604180c030b030a0308150102030306030d080402040b 78
    0x510740420200d51191203188202c8034001401071101030403a5440b4007803c00a000b040c1000401d01041c00428070034401001194865001031600c0740040c41800700c4514143e06c042c020041600400600401d40c8403880d11030180d92030084d0359000d500d02607800800329a000540003e1a00c1283c00d600b4460042d0841510000501c6089204041003050364a06090103020700040c9440c5583d400039019400c01900422142080340540501c1d02c400b626080d0380d07481d86150030b2000b00c40541903080a0284501c4a81041815403400020f84190780d43e94030040c0c5450700808000031141619440384040c1c900300140f41c0000854800d01e5240244008494041da0360307104990b039519050751512100301c03421989904048100f201810b50454000c01c9131603200c40600d81c85032195082650b081c0320098000780b181d10b1b1003075182800e0f0b401000c803030180c00305181590700800c1030060f41c0d0b0300000e80344807021b00c81c6890201981c0303078408a03005e40302410a454100e88179040500c4000000541440d0500e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 327940197 1250 327938947 327938953
    0xa0501020d0516021510120308070f08010f03020909071a0a12020301051305132117040206091e040207120f030603030e0d0816050618060105060a120906060e0702 71
    0x101e4101c0203100b0000e000040c00940d00c4017514404a50709030808580c800c0501d00040c08250380c0da0407520003102c102c102240050610f00810500c01d4100c04c4980080d54140b4080c1242d40c101101440b00050707a0101a110b280e81c000003903840b5504002007400b510400e40c5c210f0030894960702d01302d8160440c12844001c1032154002c01d18401d16031003503174100c9030300400f460601061029030100034000074103010342c100311851170040481c2a62412450b18250503032020412091140000c00d00314903c45a40e81c9003400300240800360b42c5040c01da9010000848a0f003081040000e41e5a95096503c4940b54100c0c3c00494141c060001c4021806801480764599501032300980300d04404549460000501007040c042445080c1c1c100502d00f00f52040c0300740c0009140800310004250700e02c0da1020103c1d0f455202c042045641ca400b0000c2c00c4240c40190010b1125504110000e00d0500450711114100701542940d40c101a83c40d8000140303013600a00c7c10402035442e512413441c0d07560f00301c58501c0544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 327941447 1250 327940197 327940201
    0xc010606090510081005040203040203010906110414030a110f030f07030b180613080a05120a02030402032a01032309070825050f0103060315291f110a0501020d05 71
    0x1805000264810400303185c0140603e402d050800000303400150080c2d0705996128000f200003144c82c030031440020150a401625545800782c500500b41d40250018003031b40002d050070000514104800c10840d00c1181d02c0d283ca03092100101e46401080f0b46102c0c02d40c81100000018010318250f200d000e080000b00000b103026241d44c80e03541d41c00040d22480310300d41400c131215000c01e10020281504030058505a072400705071524110084009603040b06070700c0e41c004180800c41c03800700140b08030301954482281c2c2c0464224604860112241085410706440d101403941c2c450610301e4000700d15046844140d441c2c1084040e2540c0c0f07041a0154030701521410710025011125411800209002c0d403500121890600040c001404a00b00c83d0758141350329042c002c030000708040712000902c44c0c504070015421071140d041411415254110f419010a0b01140080c0ea46501050b07100b017030203001c44440195000001143c2c7d514210071040e8407401444201030400206400920400f441d5400600c0b9507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 327942697 1250 327941447 327941479
    0x209090c0a0c0f03021c0818010e07090e070308030901050a0f0501050d020103110c060412020106050a050a090207032001200a0f1b05030703030e060f060a0b0c030c0106060905 77
    0x81e20401000d5000328074038008401c0042c44212807240014031034419106a01081d05000510202d001c02480104002c1810090520086440c040c0302d48400d40090000c2c0003086030458451403540a080091501c421111044903000c100780e0b402903034031101c2140c0d2440c0040486000b084142d460710003282c189040403100204070b000315810303900004d0400c1e503400e210717030300640041040404850000340d0601c03440411007018002c1a104034003802050000c0490a80006c8c212506508044d04c100b52015051246413525040f2605a52040348011707610740c0706040c00d882c0305483e141d420010006c145051480d0304411340000c208081c17003502650002401c40c0f40c0d5031281c051010319500050040e481500d001c2e100e180c900b0180b41407403590012021880c0c90742815644052010b4002c00e480b141030140025041003002d5100014020794182e6040c01000508056610b11602110401c01300742821a044107200702c070108680c510082011650b11340f00501440010701c211031080200b5425035101c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 327943947 1250 327942697 327942721
    0x50604030c020f04090314090f0a12230307110d02030105010f1d040206180d0c03081309090203210f040305070f060c0b1609150206090f0708060406020d0b13020909 72
    0x80d50640321242a1011401d0100d075a401c1023071110b90028004007400400e490303004034070010740186c14181d00311107060700f4445622004541380342091002c40d82c0003800d0381808410b44030b229621408203800c120032440010600c648078000a5415442c00000091030039600702518110380c0081c2110b40d1025008200080e01542124040c0d040001004408c0c034402c0080041488503030014140c2a8062040c0c4800e032050507d5001201c0854000500c440024140401d020080c458a0002d000910296000c2521100007250040c03002498041040c800c81080003512481c89180038000c0d113542d60703400c0041d55400c0600c05d151848548460209405100e00b030024181c03600b040788510b2030b0321001d084c2c001c07083e0b0003100c1d0003c02100007408207440c443c1c10b076500b003554015801861a8280700c1c01c45030401d01800e00705041c5500c20b003c10403100c0000310f04280d000d5002003005840700c10000702040548544400740b030b8003481c41c403201c1c5203010a503406418200c0080d6004016540e0360010341070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 327945197 1250 327943947 327943961
    0x4060801090f060203041e0303050406060f051f0210090c030204050f04020105040b090418030305070e490f06050c0f0306060304020424081908040b0d0207050604030c020f04 76
    0x1200710000110304001c90444d400030740e046481088030102c0ca03c40c48031603207251960500200c0c0001d44500c103000038041d09000b1400541008010303400e80c03a146c0800a50124101c80a2448181600c0d840b000140e000f07002c8141400d074000000d0181d45228645a540045a13002c200e01c03e07490302c0c02286100112450142c0b007260306849003032415003424400e992031380005500c164003a40b20485840795044045080702600d2298902103904d00340710402428a00301010258050400400e081d440440c01c1c102020840d02100703100940e072110941e046118811403000034038000c0b4907090340e00404c0468003440c400c0600805c410403540c0c6412846800303d1203400310390620310707400380041262031a043c801550800c1c8002c000080c4504100d0740140341355488801e90112040120007046008414003031101c0c0540d066002c81505240b41e5034020040c007403806510105440452150840016641154841500141220354503d0300345001004120720800c200d002d024034030750091381820704d401108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 327946447 1250 327945197 327945203
    0x108030412140102040504182625080a0801030515010f0e0601030207061506030b04051006030b120319030c0f090608072006060f0d0c14061908060406080109 69
    0x141c91081a45401074040c00000040e00c00b55401c003c0000c15542c0c03841400c1c1c1c403100300302c400c6c01d112000b414010340c108081c075039582c10b01c00d0000322070b1b195060400858079032800b00d0203103411b21062031172440e510700b0407114000c110f600c002540c03480168020741003a040b2880350040780c2c000a5100750b92107480800b03211308031100704640e50510000d003142c49031a5006506160050600d12661605003c0e00d51003401d0140800e00200c2c10300480d50725011382401c0d100d00341d0301070040e0f003042940403c003020148503910416070303603c2036912203a680c281791105142080003220f860324400501200384e1307808050041c0c046454010609040d42c0589010100b024550b11817203000c074a4110140c401e903000421080800a40796030410352403a4602002840b5a40b14000f40722600c2d1030010b104034050740e08140c41c4288101110704000074010304082c2c06403034103400c8000e01001501c001c112280200112a01e1b401000074104081e2136110307078410b2040c10704460501401d17a50724696400c0310503005d805 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 327947697 1250 327946447 327946469
    0x180a0306021b19061e0903090f08150406050702031c02030a0605010e010221090d031107060504152106061e14091c0209095514030702030601080304 65
    0x580208000750721000c20140780f406170f4a54182085041022500781c84030880214921030011300123940400d21b101d0241c41544002c0c24006500e000e0b9919610340100010000c5403a6000210308500c01d1003a503503d100603140035444290340610040107034104843d101003083c0341540000e000d61240005039101d20040e0054240c105c410400203440900c9008002d5600500300055902c648500c51414400b5010350758810507140c942c203074903041900b16840081001000d04c410310000442c0403401c0702c3c841440c2003541e0180c00c48008944103006190031050b055141c680b000800079000300390402c0c580c040a40e144480b17014082c080d80d208022a4909003502802e100c0000513041544d942803a0801e6499a0f090b5a8a10350014200d103004580c41d10081c1c00c9004070341d101004a1116180c100070221030340c0c899030080040c481800c40314107010b0814900c0450b0400e001c641c82403c820101d07400c844240b88852440c1c12190707a0b80d21002c1c0c124003034811080005101a0040301742c1d001d071103d003510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 327948947 1250 327947697 327947743
    0xb13080307180305030f0d0501050a0302010519030b0d0c0302040e1501050f0120070810180204050c0d060305071401090807060804020a0f150311090904020402180a0306021b 76
    0x800c603940404110b030039550302ea0181c0040b0114408001420f5018a9000003a41e5070318210b4000c41030314410780c03000d402182170b24024070050ba001401c0d216016801c0500a50410a5403011009400c001203e9504162080e08040034400c14006440507130307000740c40500414030304040541d070700e500d003104030a80c40a0420041c0454585140303804040a0140340000070740c2ca80d150024030018103c013004d541980614405c00406c0320920131001d4043c1007490400822580b0174000c2c1d20708880840c021310440c0d075900000c0c808a1107005035002400c07464010017059840780303885a43e070b519500034002c032050382c809484500d42c41140400141c0c0d40c03a0001e08501441d0200a0302d1005001c0d0040341e0200002c1800328480146200100050100700201c0e0010340f800700000c0e080b604036104a0401c15001c10000540d80c0b502e82e00c1d5900a41e059900680d02c43c03180090038080c40050100390b5000e10400000014401190090700c0c6490714402181028940d44581a641c1c101c46066032014040c1414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 327950197 1250 327948947 327948961
    0x3070209010e2d0f07080403081b0d0f060303030f060819050114100f0e040b070e040e12030604060905060913020f1002160b0c0703080903030403021801030b130803 72
    0x300150f00040c031110340ea40d09500d043c144881c0c3d030002c4091100e54100c644100700403a9a2185155040403850400c0d9201d41881d4400400007400100700c980030f83d02c000fa0000010340071038102d5050f094843c0c0308000300459110000050144c0c0d10042d00081c5c00c01c0703003140080d40c180c440e0100300c50440703004000200004008044d010880781c0300740c8140d56961984c0c0c10010b0303050b00c1184103240f0244e100c0420b908148500151540d55000020084003280400c0001012510405d402800d00d0030a00786000032440010f014211040c00315a060107942c198407600101c48000d580540c604440a001171626009404100c902c21650305034480d4284010640c480036649000d046e80b40058042d45164900e400410019402c0d0b800c0c030030050780708410200040c401480c032075028050310b0001c0c501d0602e0240c40c0541d2100c181c000030342082d20014840900e590100b04030340046601401120b00000d0892800f000c03003100344000c0d1081038a4500080c9038140e00d17141e481031075502480b00380c25611500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 327951447 1250 327950197 327950219
    0x3030a08041b0803030a050c071a10080f07061d09130f020924011d13061d06011107030302060f040203101113050103060308090405070504240e030307020901 69
    0x60800d60300407041d0400050b0741c24003000d545019224080c000c50b03807802d260000004441d401000d031030012600740104000140d6011151959180c106000c030401d4a4580601c20550752a42c1f02403124450716842c80454100429240b04541c40d68903034068080a51000005010106100d6a4042080d50005d1000705020b41d07416001c5018501c27850384842d1550200f0250002594560b00381211110300708080c810101d8421100c2c5801c0c078040c24186e405802040c0e03252042d800071807242810030105045001d859214500030000300000c0740c8807040d00b04d0f03032224000c02901d41c1800104103c1c071813020010b00241d000d0441c0d905600400c1c190b964850b140840300c2003c4c000b281c0c5406069000741034041f0300c0c00741d00c000d0308544404542c3c0f20403088014500d0b4886074070803418542007980400c0451032000555101d501c0c10b0b075001c43c650703558401c1150180700d0394000449200d100c05800d401c5882600401d042e04109458207d10b4210315401c1541d40c2c01005c100950103034550f00148100b41d518 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 327952697 1250 327951447 327951451
    0x21090d080a0908030403060f05060d02030c01050901050903070e04030f1814010e060712080112050709020a03150e040605010f290408030403080705060c03240d0b0a02120601030b03030a08 82
    0x180b80404005031254129401e40d403180c0d000340e400300d4a0b421400700e640460b10403190031031030442d00c85403080750725400701e5120f106e82505241030040214400701d0341d9004d40c084900c00751009064400142e00c480700788015510a950560015690001c410712850081c40e884810f818000f070100240751510454956031000c581c45181003041d00c031151406a04d500c0042c1c81031510925070300d140c1c00c00e5614001c28105050f44643d54011050322810b000c10004981d02c1c05650106101580d241c0803000150058000340c0900b000031042c01200207000b0700c80c00074a1f40210700c00c031410b01040e603031030b51500300c69507980c040c84d58106191319100f01400e607006c85400d040705124404070b040640c1c40d82c1c41030654100d41d02c00e440c541400110743c410413205100703896100941817101815414495004480c0b206025005c0144031400090b05090350b503180c2c0100c100a80c44400d00500303180500d0f01d40080d40001001104869410b000b080c03141d0f00038007401401c80000340040d418669801030859141d840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 327953947 1250 327952697 327952717
    0x7120510050c04031202010b03010f0b060a082509060311030402090f0601032d1401060e0d05030903031c0b0405040201020d120f0f0603030f09181a04090521090d08 72
    0x400c00000010484803521710165229000001c2c0b030710303843d024142511074261960b80c0c0d1070710b040111056542c0d94170980e000c10480c0c0c17610313074060b661303011a055001e01040038086001d4804080d05000c140c0c844030700d030143c0f041641c0622400b010003046d01d40900060310000e5001c044500002c5540f0030510f0f4043e03200f20b0501d40802c092030080e05605002062030071802002c0d036400807403840f00302c00c1c1c004c420080044140088040d0b02d00f410040020180340c2e01ca83c811500c00c0d4280d0305001041081c3d904882c030041c00d80f1b98403101b0b50030000300300644510001c0c205003001901c480a1405103c0c1d24421501a0060f103174501101004880c64217041c1c4007a28225540c0071a41100c1c140703441047c0c41d6909141c0009081c5082d4100540401040301c030420400501080c10312549600102d204039107480b040c800318100c20706404140420300c0d8030b52840c0d0402c0c5010100400d0210000e03940284450201540b044051100c0009610b40326034003500b070704420410b50107000246508010005159 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 327955197 1250 327953947 327953971
    0x50a0f0816050d0216030b0a0b0a0b03010e040605281806090507050306010f27090203030d150b0a1d120703060c020616021507030b130e0712051005 65
    0x1d024024140440424242600c25512011007140602c0d010031107404041149104040460726651703441401010041104c10010744074180f003101503d5420549001d0a661384c80e513a240d68507100d403005c11010071542038400c2400c080200f0b02081003401303000c0c21188541c104441c203038141c0c000382c0058a00f47c0c603450001007699500d200841c820384a4060154440c0c00a44100e500e003d080510301841a00000c54198802d001004203485055a00d021104500b0200070400742618a000081401d054040d400d40000039000d21000410792105c02040841540e43c00790680303d4000ca0460301405030040b02080080050104180001040c139454000c020070500511040382002814060254400c5840b541c9501c0015007064041c098540c6c44140150421801829008000d641d8221042840d08120205010074081e505c280c0004444000240c444000705030b00710030683c0107011080c9011000d0140e4080450100000b00007280a60b070804014150448103192020041402800100b10a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 327956447 1250 327955197 327955207
    0xc0201050d110c010509010b0a14040617160b09010215040204090501060b030708010608070516060b1c0b06030c0918011808040501021b1e1903050309130207050a0f08 73
    0x14100c1d00640032011071841c4650386803034030309203010b00303403417018266a40d264182044840951154403110b011a25583c01c0e4180b040f600b040424000c211a0304940c1d0032094442c07100954840004490030400e2040302280b00d44d55070b4604e0070101d80141c100250068000d0030100320003110204050342c0090004100107036112484d902c1c035007140e00c00d078401300c00d42c0310200030407424640000c100d90040007681081c10070f80c9010f002c02000c92158100301e029001003003201c0d070180511640000c41d04480a004003411011000c81e0120075180940110f5201e407504002070342c039080c042405107800780098540c0061362160602c002d20303184035000340711301c0d50359586c4c00a41726000e5800000301c4a000d403030709a9407503041c2000281002000d0400d1aa404254115000f43d9215103e0904100788070940d80000d180c21000050742480b00c0441c40c4002c003c0301003000c400c1c090b000c8000e001c03d0300201c48408100c0e040003146d08c1640600c81024045410841d16000031405020340946000e100781e44a6181c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 327957697 1250 327956447 327956467
    0x12020d022b0606050901051305030f0a0b100e1923100605040f0506070f1a0a06090203060f01030209012303180a0f030302090a03080c0a0506280b01020304151d041404030c020105 78
    0x4012500c04bc0c4007903001055560a0200c401c80340f035048540c3c002079590890038440b0300007680602508060741c1005035030048203271804960094201c8041d41156448044c0d204100301020715007603d4407103081c82440c0000030205c1c010f4041b142120740d812128211180f60030304000c0c103900103038001c0c0c9a8211203008200061100c0302d10342034500aa1304880001e050001c43d013011266150040d134805c0d881001400340b0341c0d95248603804400800d01e40580d451a6440040302c085a034034034515441901446140c4909190b030001d50301c14003000c201d200544615060840c0e98000c4d4107400b8003540c4183c569100400d03c00c0c0c0041095034406045913200302d6495841200640c4100d901d82d419801c004213800c2000300c02d21601d80c00281111701c030640c016040400b00000b0f072000c4282c0c1d02c641c1c0d40d03840d64074041e40248295001031411000c07184480e4120302c000340180d081030030020f40080c46000d0380d403501d180a21540340c0042d0f203101040d0003035681d80d030146c80c0c1803282d82c01a0305103c01403101e0454 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 327958947 1250 327957697 327957703
    0xa02071e2a03110d030c02040504020f040603080306030c01020a030f05030901110403060e0c0307061709190309140102061306020307210609050606040b0a12020d022b060605090105130503 82
    0x300c01100a6608140b03036040580800d20042d1405100d1600350703003aa40404d6002640c4c9100319011200010651214800926003d0400c003489401c00d007040030001c184030001002c2c1d481001c043d8161440c81804100498171902441c00003808120a503685410b101c3c440c0000d035601c11402d400008061042d415045155002036004a503501d40351000501030b44405d10444240c020180c00034000c0c54108600a040c6d445285800c814100744c0c1d07000554129010882c40e00815208405103140000c5400c000b0302130b903414040c0035800302000c10b4020140d48000b42d900d10a50302c0401d09040e034078540ea240c0d0041d600c041c2c03410081100040b03d80b4040d44810b07a0f0303010384000006c400620b0f580b80040031410744030700804c001c0c451034090208000300740e5201d0803980e07206076902d092203060300311880a0b030090180a5802c9040c0b031021440f69080700081a01041e4010f1010003034445403030150f110000d646880c0a4240040c4052140c408203500401c0940396551500300032207800c0d91142d0200745 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 327960197 1250 327958947 327959003
    0xb10030b160e031c11420403030209033c0f0f0706020c010c080a050f0409110702120105090709110d020309010b040c02150112030c0b16080a02071e 65
    0x1c460600481c0c2d40a5003600b1081240901280c17a000d005d016040407200d2185090302c16840150910303c0c803130404450690020311464103c000e0240c04030b4107240c20014000e400108415000b4410116842e40340c010340040e40b0020300390020130044c020038010340810000c6914016800510820340c038035890740c4040c0a4542c030104400018a042e61900ba0000c0c5400001d01c0d2050602003103290a10129003603d003210082581c13800c00641d0345103008682c0b000c84c4078582c0414030207494840f100350000300040090156500880320750348440050100307a400c03200f054494032896400f0540411000e02e254000021581d6030350030003800d005070494054140e138070031035546e452a591912004004e10b0144034002404020344018103400d540c2211880e111101802144441d141080004080500c1101001c0900340c0c00080c1d0101411f10f45814941c000a030180c0401051413900029021249442134a081a030030004030354076290180007003111080c090310140c0301000702d400e08c10001d0300c001c2e003405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 327961447 1250 327960197 327960223
    0x2070c0b0a020c0901090e070506130b040b0a0207050604060c2301020a030504050f030a080f091006080a050114090a02060f0d180c0909110105090d0b090a0b10030b160e03 75
    0x440c1900c040e601304110740005030040c030056440c01d1425850820006550019142d0030349003a0b5840207144c540d0440e61205c0c0e0321003500c50000041c045074450041015109411190b0200c6845940352000c2000c1d500903405040006410401d0303040c0441c0b101c580c2001c40c0d045116021480c152115201c609917440300a0410206c0e8440041c40700b04601001442c0703140380103102450030000c21070fa000b008c2030300103003040329204011004920000002e02440c900c80c6001e030800c101ca1680e4020158440283c030380b041c2d40702d51a1803c281076132410b03c400c0a100308242c0019002d9030410782c2c201700c1c5c65008030500c1e0134128401c1c07001504240203071203114054030301e448910350380030110f10740300c00a0221030700103d85140c10700d0460740c002801401820310003482401c009444002c0768010a80481c480c21000c0c004546940a111414101080240f440ba01518510886542d2404030841c060200e210003499130051900003504206141e91034041c816a62400ad00c031800d01000003854429690304003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 327962697 1250 327961447 327961453
    0x60f2a060c090311100c0206070c1d0405060703051b3001080f0a03121e0c050307020c0303040f031b03060204060503060f030115030210120f02030901110c0a030302070c0b0a02 77
    0x240244040c054000d4001300044618080c0664108002800108070540c02030061001140c40c208001802c510074000e00380c1d106030f14900e000c1748840072421110030303075064503207010b19400f04910900c2401100d1299402007603010500c80c002c654840d8542c072001c00c0c50403084000090403440c0c074990500c24007081d0704e085000d02c0f65050111603410412469030310284c40d8400381480c000a500118003010700d094201d00007400e03250308a5407521200040010400d0b40b032922405410040e0010091400340a01c0e03822500d1030380600052664078883c2d80500300081c1100c61080000903c2980000c0590480034606141e065480e0364410503a00207801c80c0d00414001310801500d07091404d403088909004800900030ba8040f40c0b90400009020700001c3d015241c10147c1312401400340c0c03001517140c05054420400c0003104d540c140300a4000307481020b0154201074006441c43c40c890155038402005034043e00030000c141e901680254003034241110392070142c2c800002c560f40d2000142400f02060b4020b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 327963947 1250 327962697 327962699
    0x1020903100e06060a0f05040f02070b04060608061302030709021305030f0307060c090b0706052d01140103020a1403130b04080304060e01290315070903030207060f2a060c09 76
    0x1a4500b403c2009090718014540710b5410030000500c201c0b1681100da003510000341c40d88c10208001c000e489403507006400c070f080035010b0104100d07155000900f1100000259110b50305d4049000c20341440c5844060340c1607000403000c8c041030f00710758000c001030343e50083d00f14000c6586101107420b001c112956000c05130000300d240801c4c00755600410722035030f88a141c1600351031300300310050381d55014800018000035500c034002980404800300200500c4111002c16a110320f06000d0364404403c00d015611111600200f02101135010780290f42010041c3e880300050f0b00e14810308000d03250402010704418081c11525407011400402e12a40200d01070315030541c0c1c2e407a0078201202078540400c0036a00c02d030b2526050126540075030354031803030310350b1994803004105501c18000f07454403414210078110312224506010070b11b03401548900c100c4e03102c0e409843c910f540d500d80503560450104241400306003a40c0d0354a1928a0f82550a214441800440e200c51b140b030b070312003200305c40ca52480300020a5104c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 327965197 1250 327963947 327963971
    0x150916061d0621090a02091f0801020a08071815200c151e04060206240108061507051b0102010f020f0906090604170303070815150a020102090310 64
    0x103080e07141180181c0c0c0c039503e802d040c0d00d07610424221610b001c402e510030090201d2031540050000c208541e0b00146400003d08043d01d0609030f4108035145003400d0b10f0507402c006400324041c020303610594050f0300c40d40c16950780c03404243c84280c45400ea8203030b507500c042c1700450003c2e085110054180e0169070f030078000d0032203081c0c00060241405800c040741d038048598504c040d6225030035a0140101300c00c0483d140d802c0008100c548018007000c840805902160109945a001650500c141c25951100208003d00e09484074103080c240c104500040c2d601c3d001501070b05000d06440c08a654210107503103425400d440d89414003514092035071000c89005144100382d0380c240503020506103098811440c11702403413248840c1c0c5c4a2041c919009550110303100e1100d41d28001503d000b0f0504000440c803071501481410389075402150640f0204260801251518078036141d07005a103070015184585c4030100880d501c030590040c01b2280708544d001c021940c1240c40a100c0e4039000c1d550b580c07003c20303104121a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 327966447 1250 327965197 327965237
    0x4030b061305070534060e03096d180c0803210403020307020901030302010203060423280c020601050a090e071e0b041212020601050315091606 63
    0x801110200b206241c0e081845c1a140c1c02813045540c0c0c000340008201c103001060a00f50b010b4001400d03803008014800c03d100d40c08007424900100c810030403a034a00c140c41c15000c0840c043c401d0040309000310100c82c83c10315054266148408003a10a01d083c0d02d090703601d54400a81c1c1c0052031300980b100d100c15003d000c1100718901e0310081c0c1500d001840c10a1031041d140051460000444104880184089000d05000b80220380030b003500078109264546e100e09001c1e020b98403e4030054051450502d031150460b51ba44038074610300e0612400302c503a0b502d69015010700321501094032990145a001ca510903001e60f0b06c40d0286110304c0ea00508801d6142104201950b442640400d2402d0305105001090740c001003125410b460f1065807070805240c0ca03049141440565800050b59003400080105520083e03000300c80b089841a00309290060540da4100e894030028811150981c0c840080c00a03a01040641e2943c003a0609080700ca4100440c01c0000340345483c1c0d8002e0000c03c0303494a24100c1c0483c60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 327967697 1250 327966447 327966487
    0xc0b1f080c1e030d0e060d02031008100207080306010e150d0c1115010b07032102181f050d11120906070f02061303031b0504060306120804030b0613050705 68
    0x1c10200a900080000400d4480c2e820206104c208141c0c2c140000240e03445405072010501c0c0c070390045442c5c1c6400c1690410030013041c01034180034805c000c1c1196401d2203500231902002d512100d40340c195141c10300155002034084032001d5204d6540b80c0d0b4500300101d084050421030200702c10108144e11181c10140c4080d014000d200c10316084903403406c0c4042c2001c1d040b03a04540d801103402e40da42d1543d080c110358080110511324080c00c43d85210004951180d00070b00088401c028444824403600420400c051038005800c0800d00d9020404000a6000354083c20414210050128110200411110660f030201d104c0d8154000d4403c1031084c3d1201c00c0140e075502101d02d0400c5548401d0002020b0740d591030040c04058106181c012550070144241c0050898180c00b42061803004641d420141c11900b00703000f86400a4a0258002000d00900544102e05034206400d01e01d0141107466008054200030501a00400115807141c106209407080d4ae00c02e900569840b926020443d01510122841c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 327968947 1250 327967697 327967729
    0x1050c10020a0e010813140307051510050d050601090e100204030605101505220302030105040f030f020705060d09020402040e040c150c02010509010c03020f0d08090606100c0b1f080c 80
    0x10042c00c201c0c155251103260f4440d2504040b00f030840715504500d4924521175148028030740d00541c8071030030007250540308641c06028258014030450f921042404800481104064050e91001004015a09495000000051640d010b03608002c1c4c1c1448100c1c2aa40142c1c41141e00c0e0b9500d50030410514101c0da00b08029014034428080e102008090060072401000d0b50f41d5102d81c03485c107280025100805581005681c0030380280114030301070a20034222a482e000903800310b1120340c05442118408210303075042d510014503143c18101c001e42d03408024481c15030102d82181d4200404a0319168942803613128500c20388031040c819040c04030200c0c188800c940c01c9804e01981c1401d020040c0e0f00001030b120038103020300e0494108840c80c00d00300e04d0a048082891154010007214501d580c0d0300a402c1882081814112034107911032a003031208400d100d180300e40c0041e0380d003462000010311503203800350041100e400320210318045803034841d00c840071039020440650103040090705070b04012172210302c2014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 327970197 1250 327968947 327968957
    0xc2208010b0402040f0603050703020d06060201020304060e030c07030803040203120408060108010b2d0d150212010e0f040f1a1806060406180e0106091a01020f0c030d03020901050c10020a0e01 84
    0xc038090020036004411b0041100b419158400511034074440c0d8155022032010000604c051561f07010041c1c002d40c026035040c1d84040c00c101d022001010004219502040380c1c0000700344083c0703035031105070180c1c0000c0d0007241d05020341c8c41c58010084400008d400505040b40140031554942204035085400c2e820f180c41c0512841d4144003140c4400c400c43c3c90381c564421540400300000400041d4031564a41c0c0700421a0b1814109003107140343c96170280c004003411036a0188541d17200e4101010a090441e010031a403603503180040c00103005096503950040c0b240850441d10f40204000007040304049424840c0380d1155460705054550030024940c202c4000c1d1800c028280c2800d101b04c409681c00c0d81101c90007031f15000703404441c0c0d5096000100600b40c4001c1000f0301d440d901000039020410702151070044c481c4c0c4a45000448002c036058800d801c000707005110228501505801135080b00c40c0c2d090500406200d104940c0e0400d001c51300c3e60301d54907040140c0d00c0c2c20f4020054095002c0d2078100e81000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 327971447 1250 327970197 327970199
    0x90501060206060904020105090a030c061701050913050a0c0e1603150302040c14030a0203060307081c0804170c0106030501201803070f0905010e0f04020105120c2208010b040204 78
    0xd40c0118059401000540b8440c800303699a000513541849088562030f0412202d801c00010300c004d82848005462a070780d1622941d070090040e600c4445420701601e5804840c10f004501102150140e4500c8a445041901c48112203516807042d00103107940404e008894010401101030808003004034000303c0e81c00d08111100d890b1000d020384004600000340101e036038400002006025107258041d005052003e1a6a4030700849400042c5d0415681c41b4040d108080300811081d0020a030307002d01401940e46d1003a0200700380d10071604408042e00590310000300c0400c000d25614450010144205000004103d691542ca007040c02c645070001d84440c0900d0484030300c040310810b8811142c040200c084900f040d1544a0000781c00c106e03050b44500f11030581c0c1e1100080b4840140c010074103c80d14400203003850380d41c0c900700e5280503008a40003400610100108212042c034940d0310751b04a03400340c00180c24010f40480102c24049008071082c2072107132020040103031020034054110003060130f8400354203103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 327972697 1250 327971447 327971459
    0x50a020403120e01050d0c031d0a050a06051510020303041208010b07030518040617010e0706140703031e200a39030e01020c090906060d0f02060414030601090501 71
    0x680280303803049040003118107a030b0b000d0382e01c034009592a14070501003c010b0407d55420150081c48100600340b03c1c000d05000c81c188901b0003140c040c400e2a080070180101444540c1c0d0784000b010020310fa03908980d0b0014107940746407180c4000001030085a00255541d04090910010b4241c2c003401c1c1e0000c10103040c0040c0700c140e600c01d0607140d445616041c01920741c1303500010030061002c118981c0707400c0743c54582d0000e03801c2400c9000291107503000d07000700004480002c000ba10b41c1018020303400820a80101320542800300740082040358000e01d00042c1c40e60625500112619403001e401c204151556030000c03101101c280d030b44401e08032111201d440e0181c80b4101800e4125160b07001d010361013801e40000710090941c4600e01521251482200109015107009020040501011030052113030800c01c080c03605114802900458000c0003c2941f40d850710100300c100c03505507200319400304a141100e401a2180c40160010f031114000a40c24100701100385450b001050f4068002c01d82410010419 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 327973947 1250 327972697 327972713
    0x10e1501030b06030625020c030a0819020d090501110c031002031512060402010804050a05390d110a1a0c01051f03060903110607030b040c020f1203061f030e01050a020403 75
    0x44200702041b0180900034400d908280c00c0c44c034181d41500031b40045504002050300204000c5070b0820800076210b201001c12130341c40420704035503c00f10703d454406000c1c1e5802500306c60380b590780107c22298000c9030600070906002c04050042940350300441072003055040716a88080900007941c003110210703e20050182e40312070242019043c450300c4030200781032000c28032902280b190800c04540305224505004420103040640c008116040c843e000c0034101c0d00d86c00c1070000350308000c1c140005149207885616010700d5500459a10401814002401020540d85140303a500e032420403e0b21428150314050075104014600d9904060382d20002d1130142401c40a2070543c1d40182000440390881c0c902598000e586000042c0180b0550b400c01c111964181c1006600007416a0b0520407034240b000144c0c4e95179410800301c0c2c29604000c1e200200b00c2101d8001d0350b40420300030001c02c8414440780c40b02d48900640550000066125401184940070901540790000c0c504202145060f10315110000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 327975197 1250 327973947 327973981
    0xc030a080703061a030c070804031208040507050d050c0111010f060803071101090e1b0403060e0610050604060221040902070b09060c040311091302090a0911060c06010611010e1501030b060306 84
    0x2e8501c0031841f0390034000c110080c0c2d1f02440e0f0040303e1b03c2110f41d031501c000d0210007085408442e944903103003001c2041e00382258902c4880d80d000c0014031010300d5800045d6000f900e03403840c40c8455943c96040109400690144034000d142d114040c545e1502503080030a045c0d002c080c20f90703050100f8032030200459404503107120340c004c1000c0455089000c070106061010301c61988081c01e058103040745e070a045900440c1031401940c03659400c4102590740ca0602c20030340110710070705001d600610706000d1688124040d07000480441940107140c59200d40c5c171202243c0041406840344000c01007080302e140001c020558200c24607074441800c2c030b851507940004090302100e02a000d103011001240981442e801e0200d8256401480780c0764600d888180c071401024041001c1e0b03500e0045443d442c0c0b49040220844d8083c11002c405025242e0a100065070007641c8259070006c50341d0b0300d041c01801844280401c480c4074501c000900b203554510704007403440c90009080c0074440c0c3c1203803041c00559103403214151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 327976447 1250 327975197 327975211
    0x21b010c0509120c0a18022a010f0b10030c03140c0301081b0f0607020609120303090d08040210030b01110607030b0111191b080109080702091e06090604020c030a080703061a03 77
    0x14043c01800b21001c0702a0080603034403c0c43c0d1445d0002030440c104079002d050348d0003003100700030041c006048486e00150b42140240c15040b1500450b02240c4903c80c0d0010f090050650501144010780a20349012505003101c40c54003940c8048018488407500313100b807000c0311001407040b6800f038486a0015400c281e052010354407404000840c441191240c0c1c0542c2d02c140070082c601040030f1002c0b650562030b944201c562410a001f0706102100d114010101f550185402134044000a5110740041c0d00820040081a0520091001c0e0a408110400049201d03410760355002ca401040030f0005012040910b91969a94101c03010f150344014004225940783c03030300810102070215080d900000c210340d06030805070555003800008800d00c03454000800015200341c502403000c3c1d036640f82c0b001d4540040c002d400c00030b40e0410b01064280c900802403981142004000618003003840041e01e1641e440501901c001c510480100070055030540720343c40050500301c030700302c080481c03210aa0310b50f840000d241c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 327977697 1250 327976447 327976469
    0xf0603051005030a120206010603090b04080703140307050a0e060705032d0a02011b05040f06051e031302240d091b0602060a060503031c021b010c0509120c0a 69
    0x48000040d10300d03a0000b0807010741540c000f55620b08080c503030011810103000243c8507000000410a1080c4507603011180c024100510944555440242c40da10018095041003a02c0308407880380768419004600842032070326115a00c0305040c1019201c1090030303000074440c4905101c401c0204a010007212884100c110359406188442c60031004200141003900c00c041e003001c142128402e4056000309176010b06d00d0484006000040310440740c51195002b2224002d060300c0003004158001c0d17001c0d1000903c005c608070318550401404d02102d410840304258070001c1c0010b41030035410050540d05080101081002c102485071500456500c00d04104511103590381c190700c014070925820107021454010032089590380d580381c0c001d41e1000150384450505180420000d11403900004903880e002a4880c50044040314840c048003d421141c44546806208403091420300801c0c440c0390801d0903140c4032692544601070900182800624654085a200c1440c03070742150798104219080741c5084400b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 327978947 1250 327977697 327977701
    0x41e03030e060705070c051e15071b031e0b150a030606030602040e070c050c0103020a05070203060901050108011104050307120503040b0d05070f08040f0303020309120708130503070f060305 83
    0x42200240707840400001c16000740424407440035840401842440d00491150850f503840b441008904030400b80280001d1882049244a0f4207260000014101c0069a00e41c140500c513210980740b0b440c44034003215011544401401001107800c00041c400c0100d140c3d205100005a580001034031000d08050302c4c2d0001d10103803086036031b6003a8400002c1c65101005104103696440d03c0c1d40a900300c1d02070b841c43d0080034000904640e1060020f002c075a504a0b00409419010f04010360080d40040100c004103e020000d800268404104041c05100391000000d1190314001c855030848004910420802c0c02c1040b0802040d0350000d110f00c00d6038400c1c2003002200350507141c424950312413980403091180c004a5199014401540058032074822a01c8030903440d40c15010480780410226030091502c80381c4805200824440c1d07000c0c5501a601030110b81940c0000c1600f00155044079a0469142030006441002d004d0703e0b45a000c01807400b1380050881d6030501001c04185006c42c000c90b02056581e01c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 327980197 1250 327978947 327978953
    0xe0403080402120c120303010e0c0f040b0d021b060603060a0b092e030506010509010e0f24060c070f090c09150c020a030812100f06051305090c03040b0c03041e 70
    0x41600000c0310010100e64445c4940e6001d151039800074460240c00a007000b000079111802c040881d414000f4400b04a417905007014200034031070304038042c003d0046500740154040742c041100c00783d20461002c40205207500e41402094940400103103800702690414401440c1929100400c0b500071042107000c56403046544881c5803040c050030048094800c0c1c200d40041448004207586060700d0003036070610011707070700d51550500c91002590480014031100c0c001580c4941c2800101040c051040c9507190014507082c0010500e030451140030030260003214081241d92072046800c40100750320301e0b06006c01500020701410419041c4102103107000021741404000e0301c100504103007190b00034004e60a4035200c1c00c0000319a00800a854003c0510201040c0009200b5890303030704507100000c11140b07503800d041040b45c4640080a940044619041d4080354540e01e404d507ca00c50b282088240d602c920b0541400310001c04040d0441e150040f0800601c4049142c41c2c1d44024600841081504e056071149 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 327981447 1250 327980197 327980203
    0x309010c06090c0b0d0e0c010903330605041d0601030f030909060f03061d19051e061e010807170f1203060109050301050c0313080c0a0c06090e040308040212 69
    0x2000030104401480d000c00c0903250760002c0c05d52071724a0a802c000190007070030b505985402c001c4013940400d0720f00c90304100040f00e81c1110100409000240d02c10940c00300060140002e051f19400c0080361604005c0c469410544160310160b1710810507a640c00ca041009152a01c406000191001e504a0381a2040c076004071204001000321242c104125541c0301100c0e443ca0b0748a0104403130003401c00911110b5100c41086018034042c1100107003040d21403500103212032248441040300c150158107840d802020200225a141965910141032545820304103160f0b00ca00200a0b01e02c6c3d1501540140304002000911000b0741d501c4804c01564900d17040009442c0c03188041490106100c3c0440083c1c1801942019501859080e210002130035140c0042500ba04c1d81103d84001c0c800d8240b001500c40c62015004100e094051101145843e9403d01181d0510000030b0f01640c14260410003000030036030240050008080e400680d1001d0705003a034004001e5180a403001e8803c034410640340c00c019000b8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 327982697 1250 327981447 327981461
    0x1e0801060f021507112802010e0402130509061513150f0207060302030c04030803042004090503070f02060405030a0c030b010f081e01060503030a09030c0902160303150b0f1804020405030309010c06 86
    0x214091b281014401510b020340e8000c0d8070220f000403118009a19181041d001b0348014240c101c9428541604000030303c03010940041c40c550303100c02100c4100d541c0e40042c40c001c290100006d075103100c0b11403c0c007a00440400a64519404008d1654004942280d001c91420141e4209184c096035035241d0703a142e03101034065908050320001002040c00300b00701032071180c07210070398103070b0410b600340e031110310070801100c61180c00501240c104000800009040c2c0d0344c4280081e10080047d41059102ca010a103800800c01007110f0303007280c2c210b090081c840c807540302c2401042d1031b4603070303404603402e00c00c2298036034444600300c0182c1d40440784000c4510078290002c030080c1c0805022603807a9801000001e01000451006845442c41380b240450b0303c4d00580211203100e520a4178032203448810342d60840080c481c6154244541900507008030384401c0400c000d103042c900b501d520948414401e00540580b60480b10945d2013144100701c1044a61808425100c14030000d00301181c901009041c000003801ca2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 327983947 1250 327982697 327982723
    0x3090201120c020607020d05040609060302130f2d030c0302131e0207111c0b0a02070f11010818060a020a05120a020c07090b060315011e0801060f02150711 68
    0x144003a00c2c02c45070f4001000c901c41c0303405a00715140c041c02c0032000d4809119a004031000074441190034000c09020740c00400030034036412104920300303540b14601400e40c58540c01c546140c1c800620803811250b80389891022203104070080b200e41915643d102c9000c1d0900d440001e000b01b40341d080720182074106074054003080503d101024900603020540350001c1d84920380485840003840001980350410302d80d45a400c50031210b09200000441d02c81c0200740e40d006014400840c2c007000800006481c220301000b03101d1141451078404038103480003400c2101c005000401f014858000403481850004120350032102445006030b0312141a00c0c201d42c3c80c491009014004805a0140440004039a0007400c1c00c440741030a0300d039060b499aa54805896081c00c083da8001010300209103603440c0071603070012101d4141089403a82140380044000010440085400304444d04010090aa00070178006000304140c405819801b9031041440c8020801a00f10f0f020043c0c1e1507001e00112000300040075070004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 327985197 1250 327983947 327983951
    0x6170606030109112106030d03060e06040518070b09090f0601020a140a0506090706080906070c0204021803100506030c0d0201021002070c0e13230d0f03020f070605090106050f0109060309020112 85
    0x200c8005c81490140302600d51500038800d802031840340900c00d200f480b06994803203500b01400c1c3ca90404201c0500b50180602400700308401e540001094204004402080441142600d9003140e201700000b91000902540329800400b04000b4540e9001c5a101c0b07203039a004e50f00a01030440ea4a01a01c0e010342d0a000414610902051241580e400107a0320125401f07940c0b80540340e955501140e40740c100c1600c1076400300715018850001498140c01600d175029039800311040c2d503214000020700d0501c444540e01803e42e03903802403040e10b08080c45141c4e003584d402c0c1c1d105a108540740c3c0c0000d50354241081c0c01c15503d41d0220b4010104510000700b40300801c3c60780e001c0b8150341409200da41c904d103d20b00717003290700406010485512001e010320454854495201404515925041c16100c80c05903d04d071f00b04040d400c012a0100004e0074001d000d00394003070900010317076181c050b000c2070031500c3c26084030b4824542c502003814260390160000007660100d16011844840e00c1c80142d03a4001101d20000001e8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 327986447 1250 327985197 327985237
    0x6060b0705151305072d2c01180b0d020a03050607090f0b0405010309140609070302040e0102120610110a110108070906091502120408070617060603010911 68
    0x1140c001010141040030310065020340d111801c450038951500f05004040e03400c039070801c00c003c90034241000d0103c1601c0201c406c26040c0702d1900085441150004241001700e017a143e0000101c040c500d6401d11644a96252a54100780c244a800590307031110300542030f00ca20f1801d6003070710340401605165038003800002c20513440e49015030300e0f03020407181203000a180ca0307000100c21040100500440300c4176540c96291505043c011000781c0004502a42c00040500342031580110400c18184100c11042c045c041d082c0c114410001640c85101c02844681e0040c4511000e42c0c10b03220800d50060012503124404e502603400070350303111003280030210312401981a1072080c8003546103c080025400d80c0da2050301d5903400c009944070400ca0103482c00050490318140b2002d80b1022020040801c1ea00481c0d900020034003159070b20ba4040c0d040030000360845103080010030340000c008601c460808410035903a02e03203000860a94007051050480c001c0d01d80c501c56840c0034100b011074030310002e000983c600380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 327987697 1250 327986447 327986453
    0x120810060e041a031b011403060a050405060418030509030d02030f04060e0d150b0906040e0a0209100e041a070504150302031b0c070f08012a020705060403060e1204030503031306060b07 81
    0x800d0140a50720702080126002c880b03c0403587c0103c2c3e22820005080d50344017030030142440010170000f040d0300d4000d42e94100d1213084600400d040200d080c441c1d82c40c113503288229002c2c03509040000c0d8501041d54024002c0722060086041074030300391007091403c900c1503c1e14030005000e1004820f0050321500300c0099802c5080e6140c1c20020407048203441c9580300f51141740620044800f41d1105042540107287d0ba03100518101003541d0b08102c41615014040d0345800d4080c403040010b40e004c80700540202c035010310075800e12581580c42450350038285d0901c0d1815041c0c1a40bc48440501420154000001070b412036000b004e0046100c10300e0100c83d224440040c90f140c3d43c40d0f01340189209042e030340078000f4420005008030940c2c1d0951798031442510144060004401a0484000080d0301410401140648604c1c001d08000c5000e01404a01c900d43c4085c102c0c00c00001e403a1410015508000c28404102c0c004116500604021030350305882040e8101000104a80d8201c1e580c0480001094024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 327988947 1250 327987697 327987733
    0x6071a04110d0302030d0e071a25260d06090207150c091e050909060f090607200a020616020901290d140103120810060e041a03 56
    0x455841034000c286901c00c81c0007044000c801d0010000d005a004210422041282d60480008502018115620507448104002d200c1122a20400d540c2e0f1003c65942c1524910316484246824488220341012030241c591101400c2c1124070044002d882d048451042c21440088484142800b8410460740ea26440a0301c082d43c0201c2e401e4440c6420604440c40c914120310405427800d030b0507200c0c0d140151030101c84440d20f0300200b0806600c140b1319240080e10391142e207261880346200502506951a00c0501e42c6954a030250013020294092000c002025030000c0400350b50480c8000b0b104441c103000500d4a252084110000b500140c000c11501203401c0c610400200d014400c070b070181c0090383c89000080c04454403102c00114030501d42c0071b02e202c0c030841100500b0700401044003c9402c90701001d41d80c960b220280d1013110000e001c100c160320400e50020040350000c460401c1021301c585420801020060741000052141d42d03a2922990748605e050f800200521000e400c4e101c1f0260f006d00d003080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 327990197 1250 327988947 327988951
    0x50c0a0309090c03050f0a090f0b0f01150c0b04020906040b030a12030e16140a0909080304030e010314070f020f0618010518031603050903030c25060e060906071a 71
    0x22500c3c0c10030802d0445240240501c81c803c62034540b280d45699036640950303002c0c29000070300361407000300f4001071008036458211040c41100088264529035140070150414501000d208804114811076018002203044441541003030301102c4a14154a1300030009006280b008850355061061404190402c6640010800322500030f8600300311407292207038019107400a880908520072083c2d40248011114441d4643d030000b00a0300c52001151680b05040c1150b1782c603441602c0001c000f104001c01c00d98130030340c1c02c141003030702f0b1a0a10400c070a0184c80d84d10510041e00d0602403040031907817580510b2007000000c0710004220110340e03040c28125054100b203611740240080d65420200011001c64241d0008116101ca2100441c94603034101d45c0716259903440c10080382044030410282c08030b6a402c0003c1c10700345041201501003000948001c1c8641300000c400306081a4010b02e00304140e5800c45032041c100001500c21590314826440050131074811008010589202c00000788400041002018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 327991447 1250 327990197 327990209
    0x302010c230f0f0d02100c0e03030307171e06120c03030d0902040c020a05100203092d010f0501080a080c0307060c0c050706020a08190909060801140a0b100807050c0a0309 75
    0x15290b0210b030402c43e5107a03d00c0403050009039000001c4041d07800115444a100300400346004d00f91025840c00080c155407060f2a500d00090f503021600c0080d46804000542041d02d0080142e0b02c8035500303201810120000304000d00c6119034552204900b1801d0240381200c003801010349a079405141c0d00103005094103842603010383d107803c0001c0543c0d80001000b1040640101c0203000c090b820102c2000030b90702c014030021950148545031040440030781c044d804050300001d003403211108505501800c55004100d52041d03d03080c44d00400c40c100002c102103c000381c011803a556941c06440d0038030724601c60b500c40109810b207859400043d40354402001e00482e441042540c030a5591b0304400c90341c1e00c0e459640034015071001c02c40004142c160110b4410919074600300305600707903907451060b000c80b8090343c03100183d41d46425070748250b02042a10340c0e501001d102810041a070a00c03010840c4c041001c2250002d1010f00c03804120080d000301c0c1a00c144411804c01c80301c9070451840e00400003d0244902 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 327992697 1250 327991447 327991453
    0x8030418060515030610031512150b011d06120c0909091b10020a06051f06170c0f04081009030e100c080d020c010f09050c010f090302010c230f 63
    0x21480d45003d00c003000c515103460102c1421500c4520800040c14000c2071090107141d9128619602d401011a480005210407148404204d2843c1018490b20381140394036a4042c0ca01022040d072030f07801c044c1e072054a00014414103600443c1d280401c11912802800181c00c0e6940f10070000c21021050050070268402e4800090523202c845545654060110195181070301c00481440c56003802140021582220301c100c540140b0140c0755070048031025182d1f1080d811080d0101402c590000e007018005107090328110f4900d4142d00d1004180b0800900120b110036000940002d008200909642c003030326081041c4e0348014541070048004026000040740450110992042a8a4810031050b40240252200d6140c0d0f20305070b9507800c1d15401049450384180c1e0a22048030b90040034410404440310910f40010903040c1814090700d07000707807440a01d04001d400120170801c0c0e5030002106040342d0342828100b05140300c501c0c00d101c0d010302d01c000c00c030600781f00103003c6071540c0d200041c3e040da402030390010f07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 327993947 1250 327992697 327992699
    0xc0f0f03071b06050418110a09030c0f050306010b0307111507021b0d03120e191103060709090b1309030206060415050a0b070812010b0309121c0b0a0803041806 70
    0x201d100c5882c0d52041801241d01408104843c070b94175034550508900d02800090005000114060150004c1c0c00000005005020501c00c00c020541444003400f99280c802009038640b0002030fa5a280500465150b00340c08008908124051070811115248400c11340c0d904d07072500c0b0250001d00b00121858401449260301807980500b401c002c401030054058945d04407440251410340340303811140031941165654944104600e10107216030309200d0705c00e0240c03a20001c007508040e03c4004544280c1403081e08030f1030902c041c1c0c6822400510031100c82100c0881d00060210000320811210b043c0464006c1c100f18441c0704040c0e020030241e104480459042010000b41c003a540341e03c000c640101e5401000002040c8402c900520203000011b1003a040301d0b180011030380d540f516000b800c0e401140b900d4008002d224a180003231080703040359102e1030b04c41810300000c020202c00c0400789a038080f010b15615582c0c1c5201d920f803000c4560240040d641125901d40c1d4500c10100b680a103601e084d1295460118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 327995197 1250 327993947 327993983
    0x50a0f0905130507020c1c030305010e061f020a06110306120106051c0f08070503041a0c0c0105091f02030910020105060604030212031c05071d030607050c0f0f0307 72
    0x80c8040c2a9540505603842081c6104140e2009003400741501055101e0384020640c0e95840d1a4050342c1003155412820307007024640b8002d030503a1010b03084a40c406d07522404004498603006010807541ca64440600307031501305d6000980c2400d200c18801f0b804542015010305024010500643c00745109a0310390395030540e074242040c02c82c0e0310740c050280d0240291802d003180346c43c008545c40c25a40140801e0040c45016503810b01d0b42e03070008a04503000d82021400300140f801844807009580d100d00c0300c087c9841f0501c2c1c60300d038445da40e0092240c18090081408052030302e4a044d440e4144a404103d50381400d014107002e962504582035242c4140012091a101305206000d880d01894014151504080c110b500700082c6203852b030100341c01884184165a42810728003503035032aa41d0707036a4000601c0e05180000902c1e8205c1c070320000d0008480310b21101581d440000b10304d94850004d1a02c0b9484140854403181865131802005580d403040404401846102100400ba80392082e0000003010744d142e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 327996447 1250 327995197 327995207
    0x5040b071d01140f0c0f070626010312030b090a1506020114010510020f10050714120f06192705160302130f06120e010b030325050a03050a0f 62
    0x1e030041c0d0003e050740030a003000d140900080d1002c0d803c4420324904015440c1076140c6042d01032450102168460a420080b2640001d1007494000e1007184005003030f405d00c185500900818400200124082401c0313410091180d0301044903a03000800403a410701b0a0040800906680443c40d03840140502000601500511864907030680302c840303203419a840c0804200b4240501c0002a056010b49101a40000e1090010745071081c4120000916030410f00d074000d15403159a000404241070400c64142014040081540e02140e4119152015503d40c404148001b04040c1c40708103404e130402c404140075840108005c040c88045a101c0c0a07018102c1400e13041d00e000307a4015207000301c070f28002e10700036209800500c1c081d05468448829030f9580c00030718010041c0c0741c1c860f40004e86a500040b12042182c00b68550f0b40780010000d06c180714128002945038850042c0010406034102c02a400c00a1145180c0001380d8004082c0c070744010503410050100c0d0700c10366880c000101d1a0f000310b11401c1c011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 327997697 1250 327996447 327996497
    0x1e190204090506040606032c0703050f030301061e0801090504021f050903010f05010e0c0d0213060306090f0603021c060b06030705120109090302191a0c0418020403020609041104080105040b07 84
    0x1500780c001c510740c9a0701d00031461234201c0300300501074022402c01002103441003001c40d80c0124040000c6607290f26203040106401c440e24185125420244c110303140f82603100c15014195084080b0003d0243c0303ca100042c0c1103418040030742d00030f440c14800b461200b82c0140150840600580080c40a00d080034400c01c22113109018000b03003ca40394001c1520b032244000900784524060500520703080079001c45281c00345c034641c016000661a82801c1c0002046401548910007100070144001400c40e80060b400c480c150142803110608a100300d8244074140d00012449140548459600d04007210300500652186504070914451000000703020b06441c0302d0302035078a0b007517400741c00c21038401c07800e5007011081401c0541c4c103100b100c041d41107000b07468a12240101c0c800032241d69110316081c07108803240541b44000203807600c140001c0000da1110402c0f0b0340b84490032180000c1e03082c4c588030404424000e54201000700d610b40340c1084104034071603d8041c050226600d40d042c01900c07000f0250444070130 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 327998947 1250 327997697 327997721
    0xc070218070917070306020306060705010204140a05030f12090402131e150c0b0c090306100509090705060417070807030f06110301060e01080702070512031e031e19020409050604060603 81
    0x105007000410341c687e0145421410040c081450f0034500d441300c9099070410740100505070b45015020304103142020100d0000d080907006000c031403e004120646420b0340c0e02035030b07154120000b90440b0f10b40d5290304880350740d13002c02d05d00d443c2d464848000109541d045225001e42c2216840041071403040c0780e100d4109511240d44124140249a4400419280c09400d40255881c1031040f509507580501070316104a45c44580f9000d001d2611003009601c00d80509925500d82280c40103000f10b4840300100c41c02e492101d28004a4003114403c114036040041e440b000d9a802050320110400c00d88601c100015030040d1010b0014510895840f0103c1c402071060030045a4980710511055000326820b81d8801c403a4015542282e03034070408a020750003826241110742e000060f10010360040403490380854035429003442c3c1145031110780340c4000c103480003070814400007101c0001d001e01a00d058007004034052a01c02d6445960f04c1c0c01c664050501501c00602c10740c1411808110365200f8810040c9a81c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 328000197 1250 327998947 327998953
    0x80c0319080f0711180402010f090501140304050a0501240b03070e01180b030c210402102115140108040b0109110c01051e10050a0603050c070218070917 67
    0x2007080c1d03502e0303607101242c100c8601001400900a583e20b130200300c0d0a500c5024040340a91130140300042511812005030414428040014041079a108001264405107030794540c0d6213840d281003507441c1c08000c1100a20542c00c10b0a01e42c48002c0c41d19040b944210b1060100101d95191000440340f404101d40c030300300046819004200943c400c2c0c00c03040e40300441c0c2d0440c14885440742109200c40d802290701245503540020340c180d03c40725584090a410740c402000c2c165a040541c001a031651079810300b0b02c1003050380c698034602c0e169802065040c91000e0001045141c4846180c1d015000c02480340070703040b01004030081059401040801d101d66407119410800d6800c0409000050000840380071050806100000400c08240305150140b42e503e6000180810a00c00011400da001088040300c800a01410059a01c03121102800e6480074103010520340d07680902c520050256801c0070b9440002c07050490200308099011038010b45496641d4801180c44403501ca444005444d8881ca95034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 328001447 1250 328000197 328000207
    0x1b0315010b0307080c130303271d071215170105070e061c0f0b090714070807030c240f0204060e0d02030c060f030603010b010c03020c0d110a080c031908 67
    0x26201d4008140d1188100c2c2d17105042c02c1c81700b0340400e410045504200c02054141c42583d402d1502081d0540305024109031299409060403841860506030300d10700c1c00e541c24440c0c0410301f4603000350710030800510807980400241c0d440304121384103807244c0e01c10707007181d540102e1050700100d03018003d00344100010b40301c420854003d10203001c05a440b141101d0660110b4100d21800d00102d40500d010342c0a084001042d030900d220100900c02d0805004c1c5030a200d48000400042003003001a1401d4640110041d500c038611030070195403807198001c004100d0004682c07103140410303891014503000c11166004001041d00c01c5628802c034407484c0908004140341407000d82041c038103956814605403020382540e00b22004807000c2030654000e1031034501c40030f1001c010412242000d21540c40f80e41d50906e0042014555502e000e5100c2c22a180c009001d030310285034131420b012202c4441061040090207141c40c0175070310000c50f929000046102c41c072a004038408503000e07080c0c036081c1c10300b09030708454014900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 328002697 1250 328001447 328001461
    0x2010618050105030a0f020118060305040c1508010303050d02070b0c1b0706020a06020309010e060403110d050313140a050d0903030201150605030708090109150f1514010f111b0315010b03 82
    0x906c56410403410030082c0000d00000080c103948250061905417070111301420245070901098402da081052080401e01c0c004a41c650700180c2207045a4260074201c0d901d851a040000183c03145800c0501080a017800f072101061202005000040801501005103825103c880d5140c0413184680c2c0010b91145140e2801300300c02d58001c0d03070840361440000440b0100c01d51604d06010084406034003050f090b0f04200d003402010700000c070402400f49030040c51850014601c5007401ca4400e070150014810f0000200c2c2c09808000041109401a003181c00e810a0014010002207150104034019400c01035650551291042c10a0940c1e4240c2c6404d82599280e41c07040b110038500402c011403035903e88071200c01044040c0b04601a0722440c010115500440c04007080565600c1004d04042900f0bc1c80100146804200580c1032440d007407a10100c1d13500100c1c0c0807500355a903017042071002e011b00030a5109459002c2c414100c006010b0f0103643c00d0548013408049086403d114234085180100002540703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 328003947 1250 328002697 328002713
    0x5060a060905190f1509060503163b0f0109030b06010e150d0228021011090a0905010303030617030706180b07092909060711090702010618050105030a 66
    0x1041d60002502616541c0c84040c04e00c02d212a0740b0000c8403882c02d00181c1c04c01507201801c1000303840c980c1007052950516107141c42c69403130408040410802e141d0f00f81c403031a070040c4c0351080c140500107203d010314010008000503280c106488030340c8900104000140d40c1d501507540e01e0126500188002543e6540000660b007070741d8201541503105200c6140d01c0429213819003c0e1000001c0ca00c030040c0c1310440c0407002800c1e20b101e4074030381c807821134906280a03203154000341c2500010100b01012071301140c61303010b01031107000c2c0d441c80d03a901222140001c60496915400030307040f28000d540034007403541d071582c00c09480c0300c070b26081c0420f54104001c400c010441c90b401c040c01d4481440c0e09101035403502c0e143c0c2440171006507020000100810000c00560168803541c1410300100b0340c4a08900c1c4015040820a210f58066203000e00008594002400305c2110b02148111001d41450742515007403500070b000380b405019940c40292182d10b442d811309040d104a5042e244040d00030400c0411396254142 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 328005197 1250 328003947 328003969
    0x20603090304121401050a09150f020904090305091c0f060e0a0f0f02032e0e010b0411120f0609060f12010e010b090a09030503011517010b0d05060a060905 68
    0x85500c400c100024411483c0700035400310134016000e06040c0e0000c0d500071030940c0c1d0040c1182a20604101c02040407030340a007603210008140c0000020380350b1605414038040d0148403070745980245080313200b4050582145c010300210314129526800365420500040700400d90042c0600882a15a00070b4000b80c8503510484004140d00f04642c03000e070300f990b2400401e00038560202c2e004801000c082e0304500381000544a01041d85510321b030b00303081e0003484544801020301441107140d203540b5410601f103030a50002c00e980002800c00d0181c0f80107144108100d034841c68088017400c0f0f0110024480d81c500080307050091900820750117683c0c659004010299002d65541079100c022f03c05078400c480003d210300344d070111048002182c9610518200715030500000d180341e0304242040c0c13518000981c440100d81c1134440e54a0700d1444250fa052048400300e4180d49902c0b0b40f40200c500108500c080d55026103441081d10030240500e1703903441e003407000d50b4405104150110751018014805072400c1e4070752803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 328006447 1250 328005197 328005211
    0x80a081606020403081207080702100c0e090106030603150b030309060304060f060f090b01081509042a0f0618030303180f081e07031d121b130612020603 67
    0xc0364503040e900e40c14102c2c0d220f9401100c0c2d1000c0043c1740001403065585030b6501401d1414420344603e403c020207901c80780d2411024042559414606001ca4040c6140300a04500500305200540e16402d018004000d640410394a960094405001380365450003200080c0720702070701071810701e1400b0007070007025040580225003882d00c0e41005007194402d40300714001082502c800301501442d0902c8042180c0d40e9034125410042c2010070043c039051807540c4c40300340c0700007034500d840507603100d0034482c1a904140c0f60701800b60540030b888103101200c40d031485c02608c1000503400e5400b60b603500240d80307104080000140c0c00070300700c0b81000424080d601820391085040107080c44142c0541c0d501400100b070200c01c80b80703804c0c04100590340c031060401e40300008004000441c40c10303d254402a01400142c2c0903d000b101c10a103030a007050300c40f04084904540d901c4210740352902c1500403038028000700c0c1255400703501d151680e4503034030b4103c1c01148112002e6840903030701800e850f000d01c0752944c0010b11030307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 328007697 1250 328006447 328006477
    0x1090506031501360f09120201061a130b0309010b010f0e0102060a0e030c0a030c06060509011a0a020309090112030e09010b0f090a030c0b0301030c05100815010e15041e080a08 77
    0xf0135105003502500c24111490305001800305006c0c540341502039610f07840481103a1502e8000d0040404c0d8220264048140e10009921400c013031402401d80038058001040480d0080140610100d05401c040511203003600c50104601c443d280803206080b001c070409006074414004520b4607801030380301f02a010969002c0d41d203813610f1034514620344a0aa0411400288030110309000d210107071240d40094801220031010b10352424100038403461800c034102180280024201c1145c50007042142c60784403014218010721b41e559038142c0b050713440203038060300858042210480286007241045041e6448040301c0b6062000e0254401e5240d004206070030b80020344200044042100611000b004010752491355a0b02d42c1185800c2c080804668000750043c41011b08210710307030b50010170383c5501c0b01011051f5040d04100000481d0384d03a94640660b90000011203041180804000052013650040060140d92800403400c4440e0805644030b8104c45801140c803036000a0504d00041c5075002c02c003502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 328008947 1250 328007697 328007789
    0x3050403022b0210090c0b0307050d051006081f140a0b0310080708010b03031e19080610020609060c0a020f01240b0c0c0108100e01090506031501 64
    0x540000c6100009410040440c03a030000b540e4294100b080c040d0440f0001c50030f0107601c0040da034141e84c00704280035030741c101c9070003000043c603440c807520581da08200744100a10007420207817042042d501850040c03000280c102800100030440340003040c02d103224003000500069282520019841c41d400d0510340e80040c2264000070407511150156000d0302c042c0003020000303440d10384507902d001d40c5030340018000d904082d10080c184d503005c016580a0011b620b00703565907180d041c904458034865165074840d2400203c0d107400245600900c894854042554400b091411349901607a8541d0304452040f140d5200e040029406c1c0e0380200076145884140c0122064039442c0d0841c10f094070707000c2c41080d144c0c424513140e11441d001c128010800405c500d00f15a86060112810711b84c6901d51820160b06202513000070401110100c40000000c0985500d082030558541c0070b060040e01060742d00394800d110b225640b038080c0b04811219812500440b14a0f42900391900301a80f50700001c840c24900c0c480d01e01c41c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 328010197 1250 328008947 328008973
    0xe0402180a110705010c031d1f020d090303060312090803030a0b0d020904061b050f0306013204140a0803040311180c0306190f0308090f04020703120b030615010305040302 75
    0xb000c1c0050b00c0c490000402c1c2c184840c42c00800301c480b154003250b0500d61142401c18005400320f400d0104a90420443c003244140001c0c4001030310582c6d0030200d07110300c2c0c02c0840d02070541c07541c849001d89104800501050052000071103800c0040d01a0581e40d8104001041d0180c003e44d000d0802c101002c0c002d10110143c40d00000e0403900226000e5400a4660005494000030301e5051060f2607c2d030b05001c6e040001c042002c030458080106518140b140303602c2170074203446040309020003101e8034052440f8a442c1410000c4400d810034402d640382d003403910714103c0c420700e00003051a064507850360042d82424550b44880321100c40564510b0b4201000700343d0072901e00c1c42c80c100350344203072200000556207040c035505001c04d83d05c00083c03148100300380a0701070140601280d00041100c1d0000710054840301608001000c1051503059140d000e840010304030109500901203040c000d003c1c0c42d0811080d00000c0506444810803949001c041900c09070b184d46560203688440c0d00240a44103c4901c0c03240d0319 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 328011447 1250 328010197 328010231
    0xf060306030a022e0f0c030e030a061b120c080c0d0902030312070e1f05070c090501080c0a090902010e0d0501090b0108161e030f05031e040306060e0402180a 69
    0x422082c030210007620003020881c01440489088912031a0907080215170080080501c1d00e0010300404102040000d1441560b00300009074100d50414802c01c00d80100c241c41d00312010051070081c0100f41e400501441c525054412440540d1154450030199506c043c188600360307100c80403a840d0300d81c0e52105000541c9042028003490300c20303d06c0380e40f554280700c1b170040d201c1201e00a4091007810b0020003a00080f41103006119018002c0c01d180d61500c1c01c07031902801c80c407480d40249141510701000050702c400e000881414161050701c0c816549a12101c2103400d90301c180602034085408078510100c5070501c80802880180100e0001846603038968400008400aa03c01e1100358408603c1c1c851a00c0f900c80c0d50002849901285011045004042e0348103c41c903100190a91481018060a0000620889407440029460f807850b13010400c0c102c1d2442c0d00035020a0b610a0b05d07049020555400d0345210b14011070300140380040b10031036000020100302d0010500c1c100142c440d0044020000701d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 328012697 1250 328011447 328011469
    0x90102030c030c060f0604021e0c1920010f020607050304030c050607020a030305240d0203071208030708070504180e010e0a060b09070305040209071b020d061b0e0f060306030a02 78
    0x41c3c0a03010760300b0305002c003080780740d4040c0c000e41c4128410001900113100035140b4003e260910850651a0400d104840341040021690880854807008207101000491018400c0c040b10f0f080c0002400380f41c500044640c0b610600040000d6400080070912040c050409107921030b100345412100107005607511404c0c01d2054400384096403084003920109501070080350750200c0040003015150000070080016030709100366950050084035a445d041d07460620020000d0600c01c201c0405580c0d052802e040305900460380c078030004286201041440d131040c0304680803280c030500802c00c42014103100b0b9000740180100c4131000d650b580725142200b802880100381486c041c0b000040d407046003030184908528000c043c00d04161500c800c0000584d40d040c682908210a454000d40c528103410310b00d2440040704102a510080c4248164204030240d0012011100001314420300e00f030003031600341d03051048210101d40c4803c0080c038480b040d0030003001450340140300408032100882e031500894003903110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 328013947 1250 328012697 328012717
    0x180703021201151a0409090807020418060b01091a0a120e030a140c190602040803031311121207081306030b100c030c060e010f0c0e0f01081902090102030c03 69
    0x658078040740e207450b01000f0300e00800000314080b51401d030382c0122402c1481076005002da110340c4c03a40c40d5000d0028078410385480302e6010f0000c100c0035020188505040048142c1122841e040c00c99007007903540f1901004040380c0e26008032007000f40d2090030742c04080d00040e00d481d0802030903000901044890b030192088580902d005165140302c40c0900410015010181940b484d07030400c007401e101c640000d900103a03445030f00140e846020051401801a100d140d0041c0c186100110074020300780e00120103454028410214000e00400c05c10a000c034868620081003125008041c402d03503100c10800081280c14466000d691501500312480c039500005a049040061b5079011030f040b40781800840001c42c20a02d042105200d031607660010846c200741c2d5801080d06407500e0070240951000d401c003029070044500180880d1090740c400030301030460110058441c50200f60b9550039540580910b0b07028401c010030303105800310404007080c081d520981455045110410206c3c00c807180c248064003c10301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 328015197 1250 328013947 328013951
    0x31506091a030f0612030c0708010204170114040b06010908071502012007060b040f022205120312100302061c0f0501081b0301060506130e0c0f03180703021201 70
    0x104101d9071115422101800000c0640100248484005800700841c2c0c010001c1741c4180711446043c2c0180d0031406080b40142c020312800c1c83c04242000190042c06c2a241004104007144001940046c20389040074401403444003442c0220b808181560952540088181040b20019aa80c0010b030302c5c100581e07015048104140c104001c1c026420f01a03c80c0f40f402c11202e035140d0081e0725035907510f644504140280f10b941d8588010115403500e4126807280c20f0407220440d01c1c0d950110b94042c54070608405944d10a030000800310345403070034104c1030111b014440011420f10483c060804910b05e00038100446031440c0d400300000680e00d2070003c240540700b000031000d0940c815402c030000d55188540e0403204074101030060005685c00a41001f10409120503c8000a264070109004114170f030042a0415400241c09007201504101101201c0c8101d400803400c0d610003140d0700507405400203000222204201007143c500c0700951400121020314280c952842e40c940c00520000140030107503440c1c1e5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 328016447 1250 328015197 328015199
    0x605131b0e01091a0c15041709040f0509010203100902030c0d0f150b0c06060d17220b07050613020906062107031d0f030d020f0f0a020c030610050603010303080703150609 75
    0x5a000c0c45080d00f101d00b0003405186c941003581c0d4400304031540f9030b00850417403000b0030401e80f1036a03990040e082940700004200f0103810104030240c0070b54000c40e13240c56100c1070104005690201d41c03003200d01c1802d041d81681d04000c03030240c0110150500500e010b40d030b20345900714800c20300703100f4030100300038240c21421710760361026183d141b42080401080750380b0072001d0140c2c8001207203164039800e484081e103000d100c0d40c03200082d601c503584a40d1513900d2a6407078110740002c1802070b202c1e0020507146000b881111074958a101140300500c0743ca1900a40000b00380d408a000e505001d4041c09072400204802d43c8a00a80c0740034102201d0201c0e5000000703a141d030b000f00107401e1024a403140110201c4040c000c1c51814801e2103940388280d600e0810811340c00a8840d81c1e40000f00c055403000c001c00000c0596481c00005c00a550b80b22200d0070343c0c482e00942011400015440d00500b044a0000d800035007180e2039a1002e6440d4071001344050207164440c240c12102031015482040504101e48442d2503503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 328017697 1250 328016447 328016467
    0x60f0b01110303070c0221010e030408011d0705010e0105070609150e060402090c03090a080d1407081905070905061303110f0a12110a090605131b0e01091a 68
    0x604070341e0305034050b0010070600c10000e611a40c06600160140c0782580c2800500112202c503510300d07441e40c166546400629082c0304400f00040045540460085c414001a031104440303000806c03c001236583d00c030000c01c10655001c2c001d1006103090505003682002c940b600c464041d1001454111a6a07040306602e0f080310086208038100c0007001c8001344028605a03001c02c0d80304101400e0125203110120005a9000d8204036481c65250302040b482d4450a075000400044d0000c2400850560107140c000b13600b20b48100b907968450040030200c5070802c2020030645000b0600034050500300080d80c207001c90191079060041604402a0490b56003962840c00c0c24008803080220fa0340c402c1151600e09499652152003040542d68021995201b0000c035103000d0348000311244a8030b41002640d8400500401d07503134030050880e43c5c203a40c00c59030404c481400804456969002c41060f00740d074251003d80610070107448440f8001818041c0f68161101e0a071254481010100c81c4135510000d80340c648 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 328018947 1250 328017697 328017707
    0x610090b0a030915180b0a0608030a08040605060d02010c060c0302130b090a08010507050702060309010e060f04121845150302090121020a06091502120a0f0903060f0b01 74
    0x1e45540118100f10600320800c84094030310b0a080b0241c03102c2c0014001c00c1c190400e0f548001c1c020b00c10027003160340d5103958203400341040b441205e081c2c07a002e140600141d441e041c5401b00c0106280e050b903c3d02c658002e25581c65004140c03080644040550a100b034410184c059010350001c0d09411a04540301d900400401084000680010500da41480d090041c4542c01800381e500b00780d170451b203541e1a41e0714400002d005140c0c0c0403518245101c2c1e074023440b41040030310460798013480c000d1750644040080315409a410440741c66513104a00224041007060021201c03154840c2e0750003000c5280303440d00d500308000051000d41420780300d100c081003d40583c00781c1c0c0e105071403402c2450142411f28034596000602e1321401440780325a080d0305103103403201d102d8241450003243e40c1e008150111168407000010300f140d8260140d5802d00c1050070740c03107460314000251403003445031201c0c4a07803034000a000c08881040c1020800000d001c50b155012001911a00802c2c8428800b8840003032100103074400144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 328020197 1250 328018947 328018973
    0x140c0d0c1e11030f07060504060c030314040605060312040e07050d0b03060108011a0f0d0206030403020a06090602090a1212030e15010305012a0207030209040f06051e1501080610090b0a0309 83
    0xb070140d110005c2001400c0c1c220055504a459a0916440c006094101030340039000c00a400b0200c1189101000200606e552206006103070a904550840390301e5a07041d551403041d4001c5900203040500090b848030b100700000c1141d060b40a0300402d1003190000031914145080e001485540d4591280b8481104544d4102080000454851945090034004150050034104020f4004c000000c006000c0c14000c1000d64403817503000d202040301c50310038141b0710002c1d041040058411041f9140020b4080f030008070341c0d8078540d0081902c40c070002100d403041c2d000b01071211b01a02d00f401a41c106d0034a00c000d4641e074600941c015030001c00da01c40b10036070905c1a269450140c040401c41004042d607256800156041940d505542c1640c440d1503a0514400d01c203602000104a207003044100500100c1d1040560003500d0036840c184816180d0080090541171002140d0380041c2209000a10314a4041d001c501c811007182014000c0548440550417907074000010f0307002007a00c44c40014200b004401c0c3e200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 328021447 1250 328020197 328020223
    0x38031504020a110c011b0f080f0c070303030f02030f06220e03181903061127010e040204080d05031302190602060603070614070309050603070f140c0d0c1e1103 70
    0x1c6d04240c00b07600700c1c40107542071003000c1c100c1e124410030201009040f0003180c44c0d18007689090742d00c0c0e40055031040d654240f1804110b00013802c02405203c000a94001d6071f00400c85c030440c51003550f4544083c8040c03070342603c000d07907641c086041d43d25000350781c40e21480250319660006180d88421814480e0f000500e80044280988125007041312101c244c0ca4032941501c5d444003012812400d00e0350346942074002c0606a9000c0e03000c102c010b02d010740c004910b43c1d032806801e803070340f030445c1990300201f004900540c801c4100340d81025006007101e40c86003008560080031408500803142068000c641da07241480904400e44140c86c6044c86010b404100156103c0403c070002c1a001e41001001001e03000d02040003007819402060000c20940518943c034098070015004070b07284d1400c000c0c000d2400450001c2c440101d80c0c07030b4501507240d403158822200e095040d0b20080406540c803040840d010000010199600c54613910a11b0850400c03030f140505080c0500c402c24000c8100c50704250030320400400e24 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 328022697 1250 328021447 328021457
    0x9020c0c0f060f03090106030c09090b09072402070905010311130b010507020103180203010924110403020108060a17030304140f060f0a09060204080738031504020a110c01 75
    0x880c40707691030a04076042045042461900c94540d402002d02511440d00003c0004008081c045184038003940100ca0180c09510403104544510b90903d46411580c00786204440c0000030f55007101c0482c81c110780e2802c000c0e20403030341015907170400f1004884e400e802c120ba032541a0101300d0320b1490305581e010154220301400b0050b070854200064083d01c95400c1c000e05142d00d4980e001056049100248a440d402034000e101c841ca131480e0941e03060752203084190a20f010000c5000351020307a0b1142c81084168a15094075050468005584004009040d03d0348503204480c00b08050104003411050500400011a00c9081070300e040060030340d4000003100c040e401444107098002d800540e054010028106601c050f07121001500054104150003500141c00000c0026440100041c02011a003240f2409400d5000c0c80000820324201c40308100203e6211050915414006200654011340844001c0d8804043c52010405a030425401c450109140031072041c4004014058100c0e0b0308002d20381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 328023947 1250 328022697 328022719
    0x503010c181802072015162a0f0f05010813030e21150109140a0c23120108070b1e0403170301060201150e13050a02040609020c0c 57
    0xa4003507003901403246050200008003100326030201c80d81120200c40c0c2001c180124404d002591070a03000401a185004102e0510048001004001030303901c1c041080c08a100d5480081e241c0c0751410040003c0122807071407240c0c442c102d111803140403400414916048000c1a890009a100b210301a54085410f1056002c1007222001901940881c09036150a0001e0188042400b0444040c4030a10a40b590840407150703c00c1d200c800078030050b1440c1c100031024110380c0c944004900380c44180655064072030703c10010514011451308504144441843d03c01c07803001d0b9000f0ba103446c0e0081640f81c02007000c8006200070721440002042c07030141ca402d40c01028924903004048130680300d07000507003106800b01618000c01c40491422500150f0b0406010718441c0315420415805038001e11400c1e01540c40c00144140c024494101581180c1c10b1b00d1143c01556103a1101e42090021010122503074003c6001c5080140e4a500c24800035140b208001a113502e0310310320052402e04a1380c100c0b849940400c40c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 328025197 1250 328023947 328023977
    0x1b0313031209061707090b1803070527090f0106030b07180302032d03121f0608043203030712020306060421060e010f050f0615031b130503010c 63
    0x821a42c450244e90040e0f59640d43d0070700440d0784400d03e40180110800004800c2909080f078050801c00304011019a5840350b030328810018406441c541c00400d504a809480751007580c45220140c0c800801e0040e101c1c40001d031546182100d9554004a420100e0b440602402c982c0c004000800f42c0e07907c01d501d80301b07941540c001030b03034030070100c0c10a580702d07514900e0305101c0300f00d0402c01d044091900b40031a625544403a5051001000c2198440ba0501c01625803256a0115400710011582c0c140c45080c15a2595101ca0712958103844208a419841108400c0030481d510001c150851506024544034144510011300c1e825a84080d03004017070040c403d00881d0b0340d8413030480b411a40c0b440c505030208904149811601c40d0110300140407985000328010135140c064006802c1800c0d8a58104503681d0390fa4114080c9020030341d1041e80140d40ea511620501c0c41000c01140c1001009040c0304440401c0780380e5079803a80c8940c1c55040380c7c0e050910b0400140c01c1c03d0080501c2103a42d403d06500c1048044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 328026447 1250 328025197 328025207
    0x9180617150c1312050a050111160816150b01020d0201140c070302120c010f061203020606090c040807081c020d0206070509040f11031f0503030904021b031303120906 73
    0xa01202c1c0d0724003001a10810f200020004080100075848080103a00b600d0f04110b5100c803030f06d0074150380035400d05181c1a03824444004903198901c110960071541d010a0301c0d9070f2140d8200402c910102c5400e110386030b001c0760507103860b525017a000000120741f03030040100080c10520500901800e5a0410a4544e201c2141c1a110765000e8509001c090325410f40342812481d04c0c06d400c80d030034200c07140001c80500001c41034011805045034a041401815a240b034404000c60502201400580002003c00c03d5443c00c01c2030301d5005024089520f0405441d1a03549003001016803140007668460215045800804217528900700c1150010341a8074402d0072000e5242e03600104031030100480043c070108603544aa0109852041c030000421480b8040003003114254015101e000394103c40122554403441c0e410f40e02400d0750009000796003400c0700c4400b444080c3d00082c00200000e180e08628480c04a0304002404050250602d5a100203155041068448160101010801030f0107038041c0031040d080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 328027697 1250 328026447 328026451
    0x4060b03220c030c0e0108071508040f061506030b120303070c020d032c180403141b06040305090909060c071202100e0708010b2407030918061715 64
    0x540618400c20314501d03001e10b600c001ca40008242c28009100401c211740081200e9050722900740031106007580740d6142107204041805105d0001c1c030840006000100b00b000b50080c03851150b4000310f11440070f52901450741805402c10030000c0d82d0790030400c80300d19110281c0e40415503128040c43c23450034140300c01000c0f104505070203805104c84031004410148110210410440016011a12100707807580303d101540701d54900324407a00000c40c00304400380b04c0410490080e0380c55207603400b86000b000401081508400360074008400303018145400740c2c0701408072034855446070380c1d0556070f0009103007003044054000d0103204043d0b100404000e03054288804070398006401843c1200d90310b41107041203242620300a12a100241070202e19099614001807030400d440744c0300000e210900c2c2c2c19060126602e030586140d42c030b8508141c41105500f03c0c800007860614000d15101c014542c0301c0d60301800c54158400072802c890741c0d0741e0040003000c07034450b4a109071003100030240c550441c01041c501568600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 328028947 1250 328027697 328027741
    0xe0703080d1404110f060c0703031d01020114011a0906180406080d0206040f15140f070f09090c0e060a08040b070c0201080a0b120a080d0b01020f1c090306050406020904060b03 77
    0x10315085c54110345d181003d60b0101c8109408460395076440e40740080c00a13001c52021030170099180e5410103198010f014440700039150502d00c1e0190303031030034812140080300241c022130315900c204001d99a5444804c000c01000e090b0005000d0103005420600c001c4581c264002d0708140c20180340804003aa01144507508142c015a203403885080324102101c114405280d003084072445d00a001100c1d003e45043e552007689183c011031440c1d03462380000d6031000c605e040c0920002d05680c1d810701c040e0750254854998801d4610f4500212607144020580c1a401000760310081805842080200140c5203902c1e64004014a0900b01000459002070100d00c00a406001e60742d864402c1040d558854041c40d2021640b05c40c11100b4283c1309092410301d540c80b0510044102d400c0040c9541c443d400050400c02000e1004020074010040032035841c0102c203003050100802403a10320000204405004490056014480042e43c0f00d4031101080b0444110b54000d082c0d01c4000d00030042500e0440d000c40503180a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 328030197 1250 328028947 328028959
    0xa0303122301120506090c010c02060705070e090a200d0305030603010e06070c0c140102030403080304060e0a080d050a061412010603050a120906081b0d0e0703080d140411 75
    0x191000100041c0007151181001d181c50100000034044015640e8480c0340d40504140c58064403020140e40e12045032501c6c0358080348011001c100142040002044918091800c1d5036007079480d05415120f41ca41034a054009500086840041c40780c503902620340d15000d1912008450300e0500401c01e00e60045401505020002c000581561029040140f80d006d5420545040d03143c0258080c0070b180800030b003074444d66001c540100b04105200020300c0c1c2c4600c1600210704080ca50f40d90300030786910042c021140240c4540c3d48031a01c22040040d003180520804003542c507445030080400072079500400c2c0319295402c0200400401c0c1d0028440604454291200107103940c081210358050a03083e48001e1192041180c20420700407614030700e07056144c0541d5042e44056443c07030210390050090312011811200120b2001240242400410210107821008200f240c0840e0907541031005030f500a50301610b00164050640e070203446407020310b081c0b0349040c1d4014241030f141c0381500482e1070a0103020751 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 328031447 1250 328030197 328030211
    0x5070509040f0615060306080102040b03150d20090a02030708042603010b12060a0b0f0702120d0206090607021f09020607150b1512040b0c090406060801050f0a030312 73
    0x442e1004100304426000401803000d9200a0040b1001c80d5051140d800001d28143c80420b04040c18000c03501181c0386800340c0e50440e26040c070f12170901e07160f4000d50743e48078a064031601d000516000c1800340c1124030412030302d036299542060014050008040851142c410020880500e81100c1060380207a005003100d001102c0403c66590b01d14007810014001e010080000030703045d0400030003020105501401e565194a03107a040c010148224050700c401414203100444c5c3c42c00780c138006040321900003482d0a5080003071801603030424000740101c200507002501082200807041006c240c000d00180f0003041a4540003041c0f0104e202e810500d40d1030700c2d49544440c0203640e591420f0303032003c68002a241c1110640c01081200a100c00d04409001c0c040480c0005a4000d4040035030b5040c006107403e5055a6880b40e5070710424420007031941208880034800910b840d181c920544001d400d0940b2404d41d6035040c1001c005900266215a502c5071038200300074800a94001d110722014080754001017224 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 328032697 1250 328031447 328031453
    0x806180711010f020309010e0316060b150a0c02030c101b170a050408060a020405060706020304050703080c01021216090b0a1e08070305060d110d050a080a0305010509090a0507050904 80
    0x40700c6260707004521907003410b05080748000281d00450149402c04000c02c0191940e4600c0fa449006a03020542040c0101d4a220040346243d001483c520000801c0c0301c106e443d80c007003c00480d40281006000080c2c00c1e445000450a00700035065030b9560443d06d20506940c0084000c10081d0a000d0303025403081200700c4d034801c100d190100214403031600106262503016820005085400c14418003040d441450082030380340e1807a20845056940281c0b440340b0313100c0142c403000041d52029204850031b2050072000400300f135418016080c140610f800150756540e10003910800303001c014085d0b40d10400e03044090001c0c0364200c03888808a4000c1c42a198070781d03c00c00b0080d24184840743c1c00d80504000744401c3e2144a82c803d5800303114400d203071010051600d6400500c80c02040e1440001e1140003120511071291610310f4410341400c0c4107400700c881c424190381d90300b0b01680200000c034010a813294018006498000201a4052101801090083c01d59182c00748d850029110343c2d8044c5010201240074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 328033947 1250 328032697 328032707
    0xf0a21050705040603050609120406050a14070210030524060d2304060623010c0303020d061e081e03180a17151e0f060a050d1203050708061807 63
    0x40400a10404c0b855507a070030300030307101d480469401e1403600401e05078140c188202c0055500b40e4089a80d60360030119050020341c2c0701c40c268864118210401e1150b00b00581c0d9600c66503005020a0341c000c122400c2a00d0480065080100100c2c103282a005d04244180c03100744c00c0e90343e02c1102213800314510340000340307a180c840c100184d05030341d01c0b01c4c4008010920a964001504552070303180825001c80c0100a000502140c008149000414444620012a05c03c0d00900009048024001200340c1c0d1054a000895441d800c44e9030343c1c1841240c20009400d05000000d41e105030004460485000841721070384174803404060a240007011203003c051500c5000414001c0d1040394a291030340e07101c1c400010360780c442e00d148210440e108480090b440c0790901c0e141018150311116114156200c10036850a0000000c2501e50041d004080004190ba6080d010030540c1c2e002d003442d20694001d030280142602c0c3c0c020809000d106a1000348043e0761204491070800c0ba2030030030190070907200d501085036 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 328035197 1250 328033947 328033949
    0x2041109030303150a0905040209060d030201110408010e06070203090901030b0a020918092e0b0f0a06050a18141315060201150e07020c24030f0103020f0a210507 71
    0x3030075201c040308201509400c0d0b0700035800344030101d803019009079075150040103860089400940140840d00818101c0c00e02c00300c14a034880c460300011a90040c481030103e9690401c0e84091003070382d100e62454801003070a00c44540c110b442d40c03000c0c51509500b18007007014481c0610008101340201d00010b11a9040c90381035030300500000385040c0068591103105c0e40c50320000c1d51031042e240106045039608890088207004900c6544059040c903103441000d80e8010841100c42540002c0301844861082daa5025244e010708025207465458008005005205510700008419071050358002804160204030f0004000c81c0d084440f00407480f082800c410183c0100c4804001b512403c180110301070703070103410244c00700d9100030000e190b43e603940c00046007040303080e2286170240c1c003d42440036542c1840c1ca07442e546006000c0441c3c02c440305501c5a40c400d0350044031a62190041d10300140110302e84560302582e1660308483c0080c0792402c0c940401c0d021420405060041c0311803203000420000d062140720 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 328036447 1250 328035197 328035199
    0xb0a110c0901090203010503012a0e011107290a1b0305130308030108240a050c040807030b0708012c13021c030806010206100612021b0f0f0307020d02041109 69
    0x1c1010b50790340310200042c0d0000c2c0185403003542880d4900100c60442c440c0b403880801c00c1c03d503800d0000c509140030388812501c080c20a0400c000c030121417a15080400004000f003070712511100665110901a80031a038020341d9464041c0002c014203c410b41e0f010b20000d10301c41c81d440c01425181c1007460291340354410100d803042160040b10001041c801917402442c1240c94400c02d6401c1d0148290745818064140d0355006203c1c0c07110710210b510712086500c0254040b0321a9800c2c0c0ca40350319421030740e28124007039004990307000580b010010f81d1a0301005090040c8008540c90562840d40c1d00e081e903262504805045215840b08001103248403160451610950003504244103407035140074145400c00302c5202a03010480150100301d1130751002403078600c10309069043e111050700f400c4048070003201d03039402070031901d400b48112041840c0104922118241d031800514210b0f1000c6102810154091409049a0024400500580c07643c0301d0712a2959030444001541d140b8400b08800341d800345d03216603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 328037697 1250 328036447 328036459
    0xe060d02090904060e010f11040308071103100f0b01080c072d03020601030b07050301081513150b150c0706080a0933050402100309030c0b091011040b0a110c 69
    0x200c010300c100790317000ca10402c803418000d005000b2010400c00c01e44001e07515040c1c040c4801c000400104aa01001d822640d10410032000f8100207907000a00e480c2411006c03002065072142c00783c0502368039102d044080d40080c00d081c0540d15041180d000c8a0055840151000302090301c0001d04003d9a900030000080454000d2601c03d11801c0c001d40e10348090000712006d01010740410030090040303083d24106c03051400105070844109490401110015204526012241c000c40c000590960081c11260b4680c100c0002e40c0d80c2c0f5602005004180030f00314180500042003c0c0c031204501141101c16500e00c1e080181c003075160290988020070350114098940c0b880c2ca4803e80c0d60180042e10b22640d1542c20606d600703009134080411048820a8400a40c400b91906100031514040c0c0c0252414070300908150720b070b905950300c40d003503102c1c07081325400b0743c42d00f0181200d00c1c00b291318402e00c2440f05007500468285418031200307110742d01c203801c42d29050110601c0d8031489004108200340c803203d000303004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 328038947 1250 328037697 328037701
    0x6050310020a11010924060302090c030910090b06010c02030a060c17010602191205090a0e0109140402030c01210f09030e0603040c09051b0304080a030513030e060d020909 75
    0x10300000e4101c80c0344640014a8103400c110010030500541355800d07000340010390001500c0042e1400703008446021400a612203000001582e640da03195403140c1c1e114403407640d50786405800682002c1c098005100f9807441c01080b00c000c90308440000380e01502c00c0c20308496a0742580002481d000c0881d400900c468180055801c01c654070200c00e08000000442060190345c84a100342d031518820841c07401c061400012240100715421144d070320140c1e050400f41d240071601c001240c10a4072941042070541d1400740108105942445582000d584000080800781420b900003600d0b02e4101555904201d0458a402d94240040204100e0150300306410400440960703042800360040312800d40115102c10341013540e50400c10210ad114644c8200c0718030180e030070500f40c1002401e01902110749001401c4100060054031070040d80900c2c06502c8007500c807102c1c6a80107007501d400902d20203606144240180c000b0f0b40203e03030b0b120280d9080b1482c640741d101003a4060001d0207100540f5500c11000d1003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 328040197 1250 328038947 328038973
    0x2090f04020c0c10080403210902030f07260319031e0c171e0411061303020a090c0512040f0b0c0706050f060f010c14010908031009060605030403030c03060503 70
    0x7070242d588030b000352109510409150015205c085c800c641c060081540e8030f10f8028010300200891810b1100e03c1d030000344e95807541e00400d151014008110317103142c3c8444402c3c000e81900e0101035030b44001280070101c00c00d041c041950780302e000b0103001060742440d0440c850060303406508000e090041d003070000c0d6100c4104642c503001410101d4101000704401000d42c246a42e9483c0c1e0241c454540590075035041c407041e20544404400052041d04c81c11a4180c01080ca070303842d80001c2c20794107004c00a40008600b54010402c240606034131007442c0f0b514202003640c102c1d4019050707034500d1050344980521a603590912255120300381b40700514411020081180000f6400050214180145000c100da95560340e03602d011440705070f498907400032003411041d03403540c400c01000850f90b102e1a404a01405221401402d590080340c0c00c444003030020040041d207003104070b0355100500740000180400307450914054428440908040d04054580680344c184a02a80148004000c007508881070405814 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 328041447 1250 328040197 328040203
    0x705120d08010e04020d0b1e011509080c010804020d0c1203050c0d09030b061908010f020301030201120504120804110a030818030c03100213090906020a09121502090f04020c 76
    0x80c15560100c0d407140008601c80d058010710502c210350141c1075101c1c1c00d110303403610203e81d0801040c00100c440380240b00c551031008591070a000304409da903000d40300c20314000007800031170305030300450060b61040095401580c1c0c45200c40b50040c5d0141d41c02c0d5413290050920300d90742207840d0095550f44e13501152010800d82e0040080040c8000b0000741d61022022050440c2c0e03843c43d03840003800c5d1011020106006142020f00400924101d10091064030f540320505421f440684000e090000c0d400720040066517080741200403810611601003100d4a0942c0c1d51004c609050807544080245200000e0208182c0d0b11005825030350080000c00d900381d032880d005800c0c4c0d125100c600d00031706203a0401c10642c100000c07140000700c03000300030304082c0d851501301000941148001c09181c00c02e041c0300155020a900c01c84001f54010344000d60b950004c1a00541140b00c2d07944500e202c0100f9003035180118450034206140c1e0907441c070b405030b0346076200b0000442c010b141034644e66010f8400628000080400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 328042697 1250 328041447 328041463
    0xa080c120c03040510212d06060e0d410a1112070308090103150312170601360609031707020607030323040f05010e0c030d03020c070512 60
    0x440e509902e1070741c030f00002c0b20340041c90142c103111b800601040780c003150301c3d50300700c000c018032110000c4c00424005000b500e019402920307500d07103070b40e507a90050011581c8151a1302031003506450400c401e4a842c0d0b103a0b0074000c5030001500302071b010740c1d02030207911540001c401c1d858428940d040d940e01006286040d110404c00c00308491800880380e44001c40d08100e00d203105441c81c2140600000ba01d0360711002c0721584003c410a04155031027121080c13644a01d40c4100145000303128290400d054084050410b50303442e00c0b0023b04c0e414490400c04140c0e80442c15941e009005a2010010b4020b01e0b08812550044d805a0805c0b02e200c1c8000310300d2642c80f41c0d500d1304890150345105810210100d017080d40d4429a0806034002200300480030209010f0742003d505015400c80641500c80e4909007203004180585040b03800403a09030358070042c01001d001d48420a200d101c00340070f10724104c00000b0b54a05418400c1c0e001d00da00860300b17a03100d500600401e80100310142032100054030b00c40c0c7e103548130820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 328043947 1250 328042697 328042699
    0xb0108010c08091b0904080c0109030809060a05010e0103081b0709020a170c030c1e0d0c110106050a1203120509030714030f090d060902030d0e011106090a080c120c030405 75
    0x3110019800c110001081d001074052150a4110301c40345201740048884000d0041c1d554800c10021004600000d10405020b41c0c005d54500c50b081c100000c2c00341c1081c0303024114130030540c1803100500894020307040660440343c3c0050b03213590720f0069a40700014203d1409000100d0f000b81040024201a41c0d001012140c08581e00c4841c0c410b4080c506001c103602c182d48d2226146028000144110b800b10010000030005151512505000d0101c504580e4400c14000d18016101e0241085143d007182c001e4403081c011400030701500c1c0c01c003408100c11440610030010b03000e01e44403100090500074130004000000c20f2000340a24584160075603603941c1319203821100c0e000f40d98242c4074590004401c0e50001c22a00b40014688509001004072428890205448c900d50b94800c120060f9020817585003903000c16128008200c4070107001410044241c10003282a070040010032848a00100d29141c00d02d901420007900c0744030f003003245c0d45006c1c0078400d661200c3d140040c12500011001000e0021500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 328045197 1250 328043947 328043957
    0x20112052805010f0b0f040f2c0402100509060903120405031203160e0109120c050a090c02030906071109040c03120302070f0204050a020d060f030506090d081b04030b0108010c 77
    0x1c892a1a407007110000d1103031a000c01d890740d60612207110408010429180d10341d20160605132120481000700010350321043e4502c480360403454000b1840140b1030240590107503d04801c0c6056004a440010594240c00c1001000215000d8995900b400d80c0d80184e0043c00f21243c41c80405e10844c404e501500400e4460710139503054894030038804040724440c1f030034120f08184003079113140c0940710303010101010390501420400124030050b0852580c4e0440340140c14500c4450314000500c03011010b160404031019050214002c55a0303000422107400880903181103550300e00ca0b080049001d1450303081c06601c00345035414001441b080b8161442501c0c00b65100c0300020500c504140c00700d20640500030300c40d900c0b0a11030f0001d450160321039503002c80d140c10302502d0540c0c5080c3c603904461403074011a5010030107038014403d12004125007507020405100a10740c0014220300a040781c10001d0000b071504400d094440c4c1120840e901b47d40040d0341c883c82c14026540c4131000c19018044058070040003038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 328046447 1250 328045197 328045261
    0x90f040615060806151e0901020a080f03160e060406051b010509060405010f140609091e240103020d1214030a0603020f010e0109060f020109050f0109030f031a060702011205 76
    0x8019500703e608941d41882406d20402d050051001550441c0910b241540500c411a40202c3c000c05e0060000142c0942c15076500d19103030320420024008001c010042029103444c01c1080d4590303100b11000d4503103604003107858202c81080c100305034007a04605882e0354240303014010350020008882e030140d44990000c1c001c1225806820040304c081d10056065940e01f000460040d0500b8647d0700e4202030718a0030780311214000d88419422020310101301d12540d00a00103a10641e035004030300c03038642103818641d01c10781d491b50700014081680d105020304403110700007810303440c2c5000f4104420300c2868140c003151a0710700300074204000c2c80d4a102c2603004601d280c40341e02d00d561090380c8800c46528140c44007000d1a0a0501c21180d41c240312503072030107644d40c800705440403c1e01040324071484402e200001c240d03030303c4614000300f01c08a4020014141400c00004040e006142c500485c80d03800281c40b00ca488804600040301c140481c041c0801170107103000f0a020040e50400314203184031040c548582e00341 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 328047697 1250 328046447 328046479
    0xa020d230c06090103020325080907090b210f0109030c0210170403030b010c300914011b0f11210705040b1503010611100b090f040615060806 62
    0x40c94241021070b4054802c00a41001e58066806945c1082c40c82e515084000e44050180481c130508034140e10109d01c0d581c0c108401480200000c00141804100900c041c1a554002c50141114200c410210b4184582240c0078a80108510f106441c00d42d0000d00403c1c5131810050b14089000409070b000d019120040b080c1d8a000303620802c001566103100782c129540700d032400c800800351540e00d00d042141540924000c164041084140d4054031641552140321902514020340c21109440060107101d4a08000c443c04030501c140c001c0c1020300300803407445448121503140c4038458400070812050b90403100103202c038264140044003000e843d8414802c2c500030b0203055081110342c1171806648207280034419814550803003060038070068840002c403403170300c10300500c290000d0304007000040e0030300a0760343e4024003000030b5200460a07060800509070403001240c4640300080c2083d101403c180042810000c856000283c1100c000da11180d640c0c2d142c45006050400c1698500d2288003041c05103510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 328048947 1250 328047697 328047703
    0x111201050f040c17060301020f0d0f140603121c1803110601050a050d08160b04061b080420030304080102121e010302010809030903060f0601020d0f050301170a020d23 73
    0x3d202842d10345140c00801c90440d003c68034401000f4540554091299046111205014284a454980010602c441c2c960014800c071a14800d0794244060500103002d4aa100400e030f40c5100c100541c5030594648003411807050b0503400034101c40065140034400407140013040d841083da20b10030303581c12040e01441090036586010030301413985c0c04040103008001d03d00d0905100c4500341e1041c8641c5080802015071403500c0809400b040e96a0b2104800b08030030020380380700385240166207081e4856035248440e0024115180100020002144604030740110f001385030b0310242c1c0b46401000c80313645a48030204a8040c1d00403140c401118444407001c180c0e0303060324a04c1c001840d40301440c01251030b8615001143c5062010313200450070f0104010a000b951810b001c41f903c1a401c1c51400322282c1041400240b425540b03c1084003080300b041d4082640340d038001c0440e81120301801c0c5854550301c1c070038042410480d409030025408506089a042005030b030f0252078140d0791420400d0244201501d0740251 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 328050197 1250 328048947 328048961
    0x1121208010609050415150e0312040315051321030608070308070807291008060906270313060206061c02010f1403090f010b01050a0c0f0204111201050f04 68
    0x2021504851040c0700504091b030011210080340342c1c20071800e1303036107c50b612158181014140005064040c01180c141410406031400c0d43d02007100301e10b0946507440380c4100420f00c8004a100603140c2c408200d203503a881e009020107917040042c0101108028085010001c200c2da1070034080b078184900001c82d0140030485e5011242c00c1015686040400c1d99103500c41d5100c42c0c01120102c28024090070340c05041521720318410722403209010f04c0e080004065502400c1503106010586c004000c028000e08040345594003c00c07031031004040342c2e035415001131980c5200d2600c4422840301050909c00928160002c41c11038810740c00b07880741d503242d01d403d00580b1103199000c2d9401c520410002ca006500c1a40c5244079801e651404a0b1078a103240820f03c025803042c1ca007440306a0240c5814001c4010070300c540203a4060909109180c2201410007608040d80004003402c08840c6000c0e0b01c0035511142c01c0001201d00c0c04003100c0d038401c00b032603003c4e14044080c01f80301d0040001400302100360500e881004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 328051447 1250 328050197 328050209
    0xf0406060507060525090501020c040c051209030c2413030c080d09150207050d0302030613020309030c061e01080105220312020301150311040e06060706060e0112120801 74
    0x81c1c503040141d2960f00140c5805800c0100704000c210108250518056041c0c4000c01d00e50340b0048101e1820000a00c0d00d801d001c5028400d5241101c45100d06030020110703000341002c2c000c034824a69419240c50300f5405101d1070002c41740500e02d036008001010a40c48851160750503074000302900ca003031081040341035040340140450740030124803021660300d01c09030410a080c041d010480b640780e56190410300dc00886844e80d455008684203003000f50601c017582c484203580c90304504610303100000848135494400044451a070005c00302d01060301c240125003010707030804101c42050900441e00d40c003100d00710702a40044c643d21000440c003a4010301559028144241d03d0112010b1503441003820400b210070100c0a000030300b01d15014410b110300185000b8400f1440380b0300e030030a070010050282c1d0340001c25a00031000030403003844104068480b603030708044203581c07140c0c4809491a1100c001d1160b81c1180f68440b886000004441001d03461002c000781c86010f029091a07680c1805550102c002c1c0101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 328052697 1250 328051447 328051457
    0x20f031305070b04060306030b06040903050405191e03020916050a0e0609040501090b0a0b130306110d02030c18040219050a020a140d09080a0309063b0f040606 70
    0x1140c00c0301031030050403680d203009000741d42c5010b580f03044210f0030307074416401580880d8545800300300340050020400e80c0301c43e09650500c0384000341e580080003845140907081c0b140c0c0104000102d0019003038a40302c0904400040000340714640b80c0078003200e110b03030f20040b441203107410002008059010104089403480d80c5986080030048a8281c80c2e4030514940660000070038001c103d126501c03030084d98000c0031401d10005402000c08140700c20401d550b0020030f8080c10411441810035000040001100d0300030200041070030300301c01d00340081d12136034580c80c001c503001000b4040c0c003c1c010300007045402c29448000c0085102c450500c020b0f80075000b802480c0c41402c0f000d00001c80c0c018401480442020f10641d01030039401e41c5e40c0d44030518101d07160035481e0b22540c0d04440c0b0580000450025144190041c2580000f0369001400c042e020700070342c420080f1040d40700010234401e01142c0041030328a1114104030310301120350000b9030a4103000302d02c41c10b010307414115581840e116010503542c8a1b07460b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 328053947 1250 328052697 328052701
    0x100e04020f010c020904031107050102030a1e030209030307030e03010b0901050f01030903030b03030d050f0604021219021b030a1259010606020c1e01140d0207060f020f03 75
    0x2006011001e0a510794144000450000e0060342c401c0f03450ba11440c800d8030348190f00880c1c1e5969030701d40b80c02d580100c0d0555008000c2c0380440c1d50080c0b9020714803000d030720000b0345c1c040f40c855040307020b80200d018981d050b10020659504154001640d0208290241c0080286c3d10514007000712040302885101c0e08048110206a2507520035001400140c2c080c0c1000329007100c6500102e85513a0202110050300307640c039001e00c18a038200707002a0b500108100c0e030650070b1000d24292042d41c0400a0008100101c81240700c000c100f1507034041d03e27841120100140e4181007070075003498a0381e004580c40d00004041200140a00b222403103401c00f4002c20803001140326801c232500c0300c041d62406080c8076051204005604c058651081c002d51009005c420341c003103001d40a0a5142901d000e50003110540d04003100c220850b480340c81d0140c00008031812800ca0400c15a130040c0d5000b1100c07a41101c00a0300001d00e40300c129090b40003800d5051144404100403843c52200400700e0103a0521001e4407902000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 328055197 1250 328053947 328053949
    0x5033f04050a02190e0610020d0c0c03120333090b0a03050708030702180402091929130e060117101a04060909030e100908011d06100e0402 61
    0x950154424440c508542c00c802c8150001030f000070500c40a40d041e0f2224000c21710283c440440301582000059400000302100c41340301035141c00c5500c40200402c509145600244404004141d0003142c00403012000390211441c0240580031403290200c02d000d0300040c030b5010b060500e10301c1d00303c1d00d00c0070007140390303582440d0120703024110052005500000f07d00021000c51000d00001e4002c0c6540310095a0b290003501c10300011034a104290030340807040310f08000158940b004200d6000c5400070b4001d00c0c81e0f0507410340340020b2200907240581d80c4010030700200640d49a1000d102200e400305c070050301480c0800c1111059440b013144190940d00510010403500c080b04200c00c40d100c15000a0300c81924012a6000c103c131b1305444a07101da26040b2982180c2401e02d8420680948220b280c140700001440d20042c01c0d481040e4081402140c006140d60f005604c9040306101502854000344020151840c007080290118822018036004607004140c9400b4848491011101001c1242d0082e5545070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 328056447 1250 328055197 328055317
    0x309090424020c0d0f05030c030f0a0921231818040f0c0504020703021504030e040c08100b04060801120305130617240607060b0d0503 59
    0xe00580c2040109101e00c0d4145200380003515101c6050740c0205140c40c4803280c01440d400f100114801441303c20403d020515040d401283c1d400705801341c0c1407070140c071012a0720005003200352004e001400d030046140c2010a241c0d00f0405100c105136941c100e4002070503d01400f070701c1c0c28200030f855480200409900d442080540722040c920040c14078414140281d0b8100f036060301140c044858403003140042e002c20510b085268050003080e5811410b02d40306030fa0181d50303001e4082c0ca0074440e0001c00d0018041501c1000305c1d1010704405002400b52412030003014240c9276040d41c1d410010b07003180b400842c4443d882c20543d0115010365403540c0d5a6464081c0160282141c03000540400000700f04201c0e141201507112070041c0429034640d104051071804121290034040d1048010380000301494006404801c89103140400403944a581c8200da807501c900100314481c005a00004e0f040507620620130080044c1902d0b0501e5000051004140d48005451911200342d0110a04404402d001001118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 328057553 1106 328056447 328056473
    0x108040c081f111c0207060902060a020d030f0207020a0b030c0d06140102010f05010806060f0409052b030e1207110a090c0e0103050f040b0417070807031103090904 72
    0x5001220895003c50f41c4d081c0e4002c6512010300c0080d5115041e070b20307030007040c1659443d450b9001a45030081c8000400c0880e00d4032807000e4044606008a0702400e40c002d107500d003d242000c240780099000a0310b00c494022060001c081c89982612919014007400d0710480c0d02c1003854800242958500403c00d142d0506010040110745000110b403034119030308030390881803681400c0228008149600c40075003140300d20b0486800c00d148034440e4000c000059103040c9c255401c00c11041c3c0a0f0f60801c507400a0b1940300940041040621501404000344162480601220341c0300015103005000d8100c0c3c030a45075603c484141d400e0704001145412030081c2014046482c0c00b0ba10000440750062024116808610009003048110052000044612030b003480d294561410200d0103a000000d007140860245000c251084000000303030741000b070008120881607620756441440300285 = true := by decide +kernel

theorem cover : BRFrame.Cov 327877697 328057553 := by
  have h0 := BRFrame.cov_init 327877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 327877697 ≤ n) (h2 : n < 328057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
