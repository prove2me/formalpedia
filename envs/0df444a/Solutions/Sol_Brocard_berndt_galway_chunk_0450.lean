-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0450
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:52:36.027641+00:00
-- url     : https://prove2.me/submissions/fbd74950-80f8-4a15-b8ec-6c583f5e22f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 80755397 ≤ n < 80935253 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 80756647 1250 80755397 80755417
    0x501021f0b0a0306020a0e060304020d0f03260103292806080606040e010c050d1a030f030304140607080103030f0212030a090b01080c100807110d0507060506010306030c0902 76
    0x828a6900d07000a20320400c80d88122202074001c0340000c4010b4005449000081c000e5403560316500e007560003e08581d81003000180880c034181c00310030034544181040d5000e165160545454000b03030406a884801d000d100484202c00055003542800e00d11030b82d040d99842800007041101c2d220f0208240c0d03814090f8607004035907200e0684030789142c4180e0007240e0040581e1000380810b42001300030300c81a119604c41c043c06d04d0303060110181085a00504541c13401861050004081c0c0c11203030b030041101201140e02d640762040003e00d6044c20310210040d40101c4c865440d924402c0d80d900500c9031204001c5403030a010401840042000c680500c021941ca0f40b03592046c1c0302000703804c0d41010034a80042c0c40c8001190f03134a0213000200158449068050042c3c3c10042644945500001d1003519851804e041006440c0300410001405480380100440103170b01980e0095000c03a000610030740060405882c3c090900020591550203440380d001a241c01c803980c44601406d20b05540003a500c100449 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 80757897 1250 80756647 80756651
    0x150a0f050f041d160503060105090a05030d0f0f0c020d020f18070f020106050f0a0b0913020309010203040c050405070804171201030507030606050a270603050307120201150501021f 79
    0x20058455425000380003420b00301c0701d4405845000102e19040310f0380101000c111440100ca1101141d0304803043c2c0c0c0e4014802d19000750ba0b4101c44021841d00c0c0b03603e901507a00b51060541d01d0400980143c0c5072810000680d444078070b07600e003c003400c41e40100c100d01c019411a820010481c09828240440c15850078050710030342c003001600c040e1003006841101c1450014100d100710015566081c0a000002d0804072007072103440d840c4100090b41030310030b4400d5440c08603000500030b1850712074010794004010195011500d0b40303007002c0001c6c0031350710803501180c032035100300c0011610703240602c00d845c09601d02e943d51000907a00e903950200000300c0d22112102c002c4d020b010646015907403107900741c0614400c40284c0009450742ca048810fa40c4e00f0f40160b803081e02c65103410311130308068400d49015419801d1075203500416128164000308615000074056000024100051041442c4540340602903035008100360103105400b9540c442c4140076860050300321000403c11075500100e421030342ca84d64000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 80759147 1250 80757897 80757907
    0x40f0203030315010801060306031505040201030e03070f11040212040f08090a03230c06160303020403150203040c09110913060e0115030605010207120807050a1403070c05150a0f05 79
    0xa461600112620320034009903d0034141c0310350b8801c040900510071401d0500085003190703101e0300e500b01021003003512550340340005015603105c0d82065569901d4001540e5654090307040c10140d540500e00155040710412007000054207152003198048290641526041d8030303940c1da00e10f0440031210054403542000d018840d40d664664201500440c030403441840c81080748864050302c4250f031441e82106811141210000b6285c21013202e0000d40703444030040d4050402d140a40080c02140c001500240564806a1030607403c1e0340114001d40c0140d00011040f0341e41d01e1004140c0b444003610051120003800204518284011740c050344844000d40440c49030f45807842010410002d9101451451700c5000024581e6094070032100a0320080c07020340345681c180214125483c0c4a040028000003000441c50103101d4140107000360342c1d80c0840003040502d546005c0640d079030040390003a20b107031440c59000901072610300703004900c101d03003c1061410400c05002c25a0019000d940400c140300e42044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 80760397 1250 80759147 80759149
    0x31107120c03031b02090901021b0c0d030f030e07090506040b030111090d0c050409060504030914090f040302010b090103140f0a02130b010210050a09030f020a0c0b0c0c030304080609060606130e040f02 88
    0xc0300507c40c4201c0c070001a1a04110300000b0302c038121110710845241c1000d207904d03c0304c0d154482000203054160070805455403021301c04400801d5580c0b0260111700070000b011480c40608d81009000b4030003103070140159002401010f003290045d882100c44e890041000e8951400c4c5900d03040300b03141c000e04c4001d00b11551240402c05440403980100c8182d56200c0401040540203403ca01c080c0c04200490010f00f580500440c0c0126006082e03890802802400101014800d4100034071042d4080c11040031540e40b03141c0b201105845562001d594020704002030100f00000039940b900304d80062800e101d000000c44820010b00b602c2e641c0f0780c11801110104929400d150040601a0031000000190b80d030840c1402032803076210181d4007003150800c243c40310215404284040907542c3c4100599070310031343c0f104498070b058600e25190350180008038000446c16408110b0500c1561124140c1d01c080d07a035001000514459121402009000c0e0f14050268604034030b1910340c010f200d04018128000c41760 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 80761647 1250 80760397 80760409
    0x60705071d0f070f030207150e0a03021e0601050d050a020d0f0209061203030601030b0a270c02010c050706180609110a05030c1c080405090103031107120c03031b02 72
    0x50085403410500102101c400c010001c4450740c0710074020707400050307810f100c40e0003010742c103400d2054400c042e0007080050600c82042210400c01000510400c042c8209280080d115005040d003a8054002d00002e501c0b09140700302e080348104840005020141e00b00020007035048079043c3d09403900d1065004400041e02c0e00003000903007034021080251002418410000d10f954001c0c1018001c607100b2100000585001042c0e076002102400d020881007a0f10700458187c180c0b0782e10a082113000d681030700d6104003c0c00c0900250705d07503410040c02a090107071802c0c2d098541d41070090001440c200801310100d21150301014080301c110868402d03035141c6031152000d8a100c00021358854100015803441450030040301070092105601425002e1503050001d1220035644610785256040b990340039040000c18800c071009440020009003c079612828002c0c9044443d490400081c49003110105604020403940110a1380c082c61790000350382156001c846551840c1d240c10010480300c1150030040e80c6807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 80762897 1250 80761647 80761649
    0x1b010e01230c011e0606020c010906081308160212060609040b04060608070b0c010510051e03150405160602060c1804090c060302090f010801050a050405071107060c2f090606070507 79
    0x1a61421321456a543c12080700c1d515880f50055600c0400d0b030041d0703660401101002c40f002c0c1d061003e19503680c80700102d101103080e03000400d41800010329091000051220302c84a46c02507801c07100e4800c40643c00c6a4501007520340f5a88401080000f50001e04541022640310380318501c0411341b80e030b407050b07600e10b014000d40110340454400304003100c1c2c001092089543c003080f42c0642c08102850103010410b070403004440041070000f8a41180d0003510100b0240301c0b04001000415618902418803e4507030600c070001621150f4015400602c2510000f8070134040c0c0c3c0000503980c90080d03000c101c0759031a0340d20f000c19a00503481d1000345c8041100d0400e060010442a02c0241c4e83d810510104441e991001d120a41441101c0c4014070890f00c0d841c4413202a0346081d0f80c00203141d00c502d00c060b90080c009102e404802d00c54144040341055000c0c1903200306038840c0207080400c0003404100c51840711271041d01003a141254100007460311703144aa1640004001d0803552500302c0a446d0300d820003ea07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 80764147 1250 80762897 80762921
    0x90507090c0e042a0302090d080d020d0606020f06070c020a0b0309061909050c0402030c12090d09120206090d23030301080d090b030c030a0f020c1b010e01230c01 71
    0x35007080b18810f401c1030f0140100c0441103046003c008008084500c0305089001c186a04256001c6403028580e1a40c0003d900c0c0710703070410f4801d82c81d95000035848010358081c000955246090800002d026030000845000100104028003c569502c1d50102c034010407083e02a680061040000299a45880c00175030140c0000b40180800f4030300360310f003000d00060075121601200c1c41c1440d1000412800b0800458580d030885000d42d881d19520b041c49020700072000034a84105c0d0b03400a02c141d5250004080345205545c1d02c0b50400250388407045152040310740c0010350000f41c02c000c50704083c544408a00c01c0c4a11075000091840d059003000075403107440031052603256000000500051108024101c2e401d5000d10b01010f56904040409150740009040d00e050200048041400180307a40c110a0350710000c10811504d507002e0080107030f40ca01d45001d02c00b5240c0300e20360b468000c95115959110b400401a1550105548402240e40c0d40e070030a0402d8051004050186902460302030081040c0711b08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 80765397 1250 80764147 80764157
    0x1060507020102010614010c2006030c040602010f0504020901030b0910020a05070512160b0c0d1505010e04062702090405040311070909030f1116060302130f080c04090507090c 77
    0x100c140300180c2140d0031900204006c03030390454000040ea0780000d55001c041d9000c485016800c9031700d000403a080307100400403644020040304000c4412040c0e8003400440781e081d402400300700072501d00b0700d040740c070140ca000c0d420011100050011815080c490350700640c43c18210341d00b400c0c81c0d02d1000b080340c10101a120015030002455418040104203000040480d07510007490200041081c000d5450800070050031114804006000c1c012910155040c075945104280000005041044c9084590780261404101c5c04648200d15007040d2044e50180c8445000c19402c1c0c0d8440508040075030741e200020310704075030200001e0396a81c0350f82c058903000701e02c65200e0045400310250407a04080701500b00c0c8840610f80402030021903405480f00032103400342e08201c0b9011880364144c0b8100300c10510700000801011900040c2c52707a140c0d00418000b20000014803400d03860b05103014002600d4032031405c00d0780c0041030030082807805130f000c80f50301d62141046070031240d0f0300e24062054440300a90400801c7c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 80766647 1250 80765397 80765407
    0x160b0a390803060a06031a04200a020d0f0206240402070602121509040b01060c080d15050a0b0c0a061a09040501050702010b04140708090123040c080706090b0702060d05010605 77
    0x1080064001c1d0140c2080c6c141400400c01e031401640c02010314805c01c40c4602e4494403000065103000030000340302c907081101c00b030740c1e1100c000c0040d5031604100104d00c0021032994803907966070b01c082029400b034600c003d070f594010300d000380d03002410300496281181d205908000140000c1d0b01d6100405903051a140c5d101c81c40c0c40e0600011f0711110811003843c0c0182050420480055144070800d41598082e0410034100d9505003001c40185c0102c0ca01076038200d10742000d41c05401040d040083c2160011244101801d44a03c02c3d035640340501c00d04d0308096032000b0806d0001940c95040540c03c0e10303841c90b584a1060340040000c103501030a40381942c159644406018000340d0a000e01840c81d00291360a001106904025002094000701b8a10802003050041050400c080d0402540f04808100050048021005a031019a410307501191030584108000030a03540120b80d1400701d80d403546540e03880901d02160070641c2d44c0401000c907402401000310b2403074110148200c3c2e02809440d03403541c0d151 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 80767897 1250 80766647 80766649
    0x20c0f0607090302010503010b13090207050f010b0a15080c130b0a030501060c210c0204020c0d090e2211030d090501110609061603020c060108160b0a39080306 70
    0x103100074181408000080200380050b0b6013020842e4111460002841c0c2c0d140c0201c0c581000070510360f00140c10142c000984001407140c00941c81d076a01100000800c0005004010449924075921400f5030504100f4480d505003406001a00e074030803180c00c200c030726200e1803030350554400030b4580009403811004604581c2c40c640c50300c13500707001d40001d0815800d0001c540e11400d016440300300400101600c45500001d07410700c200014009254080c00030364482c4004030046807202c100c595201d00141c1d81c140005080c85007908a24090300344414071180135800f5220789002180f00000913036040c40b0f106503030310054401708110424101103035201d010482c240b00004242c20140031401500394042014040003090110701c0a070051211004040c485001c2c2c10b003034029003d200b052102e00e01034403000085004001c0f8256144d240440700c0c80709001e40380e410100d201d014008405001454807c04035618041c990f5220460000d0b0200c4046032445600742040c8000c010242206c1c1103501105100746 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 80769147 1250 80767897 80767903
    0x405060703063605011401030b030a150507050f072003030702010e1e1801051002030408060c0f04080607020a03030f0902030a260414091503060402041d01020c0f 71
    0x2015003031509224003840e11104481840078204200d030141002001072915001c4003104502d1442490411320066968480741251240f4040d2007a0211b400c1c05510b5255107808076424000315404212504403022600c041002080000d1145046c840e08106241c0f02c501880c0182510b188641740e23103840d0104204081e150384412108140c003d900501c440d90050780c1042040700e0074481a5125807581da6401d0040310399483d0340c901a03400113103010341e00502c0c40515400c5816a0000d954410030300c40c155108a036248114447ca0102e504284040796007110544000d150401e002c0d0074075401e141d101c1e0385071801c01006480c01005640308162503c10181c01d409800e651119820040041c480b041d000300740c070380c11400d43c010090b2415002c45400340c1c9010348044074800c9006a402d46998840e1814041d48214406c05440341c0100e1000518513005040384801035a0007070301510107a12181d0030701003d0580802c0036140b809920011010b4200e091016281c10064040204802c50a08201070f00f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 80770397 1250 80769147 80769151
    0x30904060501090305150a0b12010b090601050f04120204021308061b0c030912010f0207150b06090a05061305150d06150807050d0207050a06050115020105090d050d06030506040b040506 81
    0x1c1440700003001003020a4006c9400040c00350f1000300401e030380d82d0307145030305c002004019880717584051100c55803407810005500801300c3d0340060b030b50b5000c192500d20041d102c6015070721016808a03030402046c010714450384854256944050009410000ba150400c08108004d801c800040c5e03100d0030400c686684035945515202250140c00c3d850915140c6580c1c1c1c892140324030503400b030403c040b07030007807052425400000c03104d10400d01191071b044145017800302d0451000000001c07a040c104442d0b00ca203803ca04544001e00003c003000b02c2039203000c00b0b1107681d8009040b07010803202c5101d000151a16184031000c0e101c11120101380e51200d00103812001c4902302d8000242021003600e04100054100204030b070000b641c0c0c00d0490700d82c0e4021042e0030180c41031000051081c085d180d40717a801c0103042e4001c0f60580740140c61003d4a035221107003c81c00c84400b180c1c18a0a0b50061a100d031010340920010910b59009200114100740c40781c65040c0740180541c2c0032600e0010117001c02003440814401c0c16 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 80771647 1250 80770397 80770399
    0x1b02060d02121803030a0c0203130e0601020d090509060d080d060603020309100e12070f1202030a0908010b0108060f03150405030a0810080a1514180709090209160302040b03090309040605 82
    0x1c1e50b0103c006126949010041c50f0b04c00303e07560b560072001500c0c02003058880c1710040800c40e4030f0003a00c1c0d00c179100c0300c02c0050364404e015108243c50b800b005030040700007030151030020700b5026490b541e56041212008042e001502c0310b5004210414050b1620300803078010f040359450241c7d4030700344806014076102909440442d0245000003192440720080b481909140b800c40c042134a82e069428005401585058003c03d034034407a44518425603000720162039407030442e440303903241155500c540c04e00380c43c84981101d00103002a000642c1e03c2c541640342e0300c0d0113a805401c40b03e1160340c642680f10580e806460555030383d031000c00c1003100d0503030204805501c000840442c406807460820003981c0c3d00424040100702170345c08244440e103801c0c070f644030000c04007130785501c0981401d0010758a94280c1961300400b10b1400382003004610f1400d2406664029540540070880958494285280200b12400c0d540f04041c0c08020008612070240e0246000b0703580440034682c0d03014407204100c100c3d1403550180d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 80772897 1250 80771647 80771671
    0xf0306081614061606020304110a06090602070506070320010b040c0504091a03060a0504020303190f0305010801060605070f0206131e0504110d180203061008190c05011b02060d0212 79
    0xc000a84c6001204c40d40079a103e480540c07251101d1800314020107011842d25001926241e00189055004020380116031880c1c0a481032561140d003071000a00c80d107480074000c1100005082c004900b4040c0d100d821917142c000000310803403120001010b507102003002030005540807409215203081445003140c8000c000113031020860308800441c0e1030750744c0240304040013a5540001015528244100c0d048002c0b188007280c80d1408004001c0c000008402c920130000789804000f040700c01c0d051140c42c09131940c94503124180b03503665a8640d00b0040841d0300326080340c003d00156060301c0d8100c0d03000014000000a9801c1c6000c0c20540c252a00aa07074030591045080c290116101d9040004454010310304510206440b0840801541c8800d2102c00080d09803107075204114a0841010048041d5840c3c6415035469421824080e0b50f41c1e050300d10301402c7e46001c1c0900f00201d6004111482044104d80740d16414408113400240c4680c1000c481c880507030f5000a11304420000d458600d59102c01d2031044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 80774147 1250 80772897 80772907
    0x25051810090501050a09080303010303080f060909250b04091b05030c070f0204020c10022a0c010f11120a0e190306020a02070e1806010b030c03070f030608161406 71
    0x41c41e8484500c181d506102c030002d91512030703521505006000c0c00c00030b0304480d541e503540c0ca002002e910707088403031444591008001c40c9941c90500d003800d000ea40c01200070207500546510903407334664074046012014208076000620382d0b940b6000780c0021308004a0001e96a0100e900442da540c0c100c0e462071003000310800810240d00ca040080e5104036401440da505400024400f00d0020b208d42903800340c0b02d108420480f40140c1d6960020044d082580d8400e51803c00080c003a03500d00d92142401506e5a0000187c02005520030184002128a189810b80010790211011401e10341c920000101d20b042c005107054202d0b4000c2035140e04000c09480100a6024040f0411260100ca00005003616000114964902d200b00f14020181c18038040041e942d080034000350011a04070040751405000e42400081d13289101016607100700c414031a00c619603510703c5401c440c65800860a84181641d5140202e03018900f0400030317940b6041c000e105004241048407182c03028006028562160004200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 80775397 1250 80774147 80774179
    0x1050f04060e04090b040c050f0303071104051e100e01060e01020d031e0c1809050c030406200408150c04050a06120f0203090d09050301050618250518 66
    0x10803103048940307034036104407001410400903026240ba00f4000e0907810030700043c041405040d1520404607242111400300d440d07408414191240114400540420030b881190012400c054001c1a440003d40d94006e00d14108040c812905080030341e07416027000b0036020140b15007240d406002d809440c103810850000c3e810040003c3d43d4100e23084100d000c1603100c154911003943c2d41d035202024050140f009005c006203041005000010b40440014203070300d50400041d02d080e25209260040c00d08901161030343e80d50352030b400701a0100e04000c200e04460b4213041c4847d1804200600058078841d40501459854429040110300c0c02621784412020100020080307503444250740402c40d8618180f504844024907086002080e0400042c00c40ca4000002c01802c4140801d180c2c842d5281a01d5151b5200c3e120418942205c80803240681c01100307002803220b000d2440380c40554040e042d02c44043c40a884181d40001101c0800d00341000f00340d010405000c102204070801e00819015121204c003560001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 80776647 1250 80775397 80775427
    0x80d1227110307080715030f020c0607050f04030503030106080402041a0a050d140105090f07120b0408070602070f03030501051215070509010c17040510030e12090d0501061203020c0105 81
    0x50005058101006411105450503c070030b80003004541c05880007260f0b1071000079502c4081c0d04080300064580180a007103480a8400d4410b001c007104020315440c0c0e200201a0723002c1c1d0010210004004041c80b00000190702000110301034000c6646d003e901d0308141c4113010640b601c0440c04844215002d1400440b5214220f00000701d407c11a02d0070608a00390034211341d10010881e110342554200002c011303505600080d4800d0b4024102e00f2544040c0d0f440c401032024001c0100010207103181c1030085004665041702601c0e01c14020300c4010b00d031114a64030301c08406010b5800b180400e441c1c4004118905d00207440100001c0c1c3c500c003400440c0c44804045103d040e0090051080c088045940021648100170400c071362036000c94441c4000f035180310a56115009807040d54800c114455030801a28468041d0440c5410020020208109091449803081d001620b030150403c003440803000114200340079402c000c240766062039148400b075080090401070744400786d605101041200315841c00600e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 80777897 1250 80776647 80776721
    0x402030c04020d06030b1816060203030106120b21011b080a0207260304150c02100b22091101030213061b060c08060102060703060803070b060406080d12 67
    0x8407001a07441c039900441800400e03d64001a00c11603401040000240320a140050311040410403200300465081204200340e1040c090200142c1084c401004810b0003200c0103c0e1603080c01d4070124204c82c1c1d0901003001c104104c1071103c1544880a43c940148000b881101d009840f007a440d0b10403203000b40303c064448480580120202daa000032048103111103180390450400588520040d0350b207160744445180d81003598252030281c1c0f111b0039130741400541d200e0307580402c0480e006400404111900b1000402c61400416000082c001d940b10000b200c14480b1059030515074400100d440c0c0e5420408004926516200d044c10720400c1019100318100c1607400441d04c01d4a012a00c000314105035118801c145c8034001c01442c01c051645100d5600182c80a200b003100b80e007240d58550b40e49204800f51899442422890341082103040c0200c3c49045003079910590203080401d1080d5103c880c107103802c800c0241d400008050603509a03564116010b05098071003940c07003e01100880c85800a10480d40e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 80779147 1250 80777897 80777899
    0x30f050c0d0e060409051603050f01060923090126010603020105040302090702030705030a0504150e0a0902130f09050618040809010f120615020d08010305030307051c05010305100e060402030c 84
    0xc0c0c070081030410f980707090480b0080c0001040500281c1403014203404000d0260b580c030804641084005111504c1c4200034034129001a80d54614007407070111102003121100304051024410741c0d44008107500c035105114001c00e840c666410070b86c0510201918513504180d62080c0a07410302d00100007503070740b10f415036041c0c80c0c0485c1d600c1c80c280c0300c8020a034a98495024020800d000106e5031003901350308180a0301c00c444142080320200c40d02c40c0c10880c0d02c54400c00d084c43d03200c581e1490920950b1020b601804034001800c82d4a407002e40c40e00080300000e00507501204600c3d850320108040342c106804001e4401b4111030b00ca84041c1460b581e44080c50052002c2d007410081910f2000e43c600703104d659451042c10384c03c1000c011035902c03003070340c0540f01c5400440c0c0c4002d8800c3c6446501414803d0340b403a41229041030145080d80c0b28030324200c42c2540524040075005161005810708031030644929030085200350010200a441c254041d81540c03d141300b440da01381c205400300701c0580c0f00401c40c03e442e004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 80780397 1250 80779147 80779157
    0x7060203131502030c160302090a14070f020111070507030c0501020a05120904090206160210051c09141002090306010501050405030d0e121002070528080903011b030207030f050c0d 79
    0x3141031412803a41c0218042e105c1030303224100d4000c8603000b050940c40d080d00e00903504202c059980d00b01c03000945013035582002d14010908001025076106060b80d10310141c030341c80082004a0f0003e500d4580381c100d9141650b150300301401c20410020041701050080800780040c00d0801901e45815403500c0d49403c1d00c01840100051030000d5540799884521070550040216496014603150303240300d480e06210803400740c2030222514111500440c02c0e04c6200b003022902c2501144600d004c1c401411203400d085407941400800c0d1019444140001341003404030280043c0c83e42401310406241c020706034000f0b41440010030051045490218804955a03202d00b040c50344804c45201148000f50610600b85681c05134880110a1180d56002014200e009000b2250070240d0003802d02c030450441c1358640d41501036145003000280d814030150940c50300050000a0f04020310108902c01c035a250100070010381e00192440815401100740d56086086180c02c90030905004210f50740d0356200141407040c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 80781647 1250 80780397 80780429
    0xb0304030201110307020d0305010e33030a03020f01060b030106140309070b0a050d051b0313050a061803111204050409050c03030d1d0312060907020f01050f01080706020313 76
    0x14001d40004039a1003d00c031040f5900e1801e4a0001c1d100c44580a2050020f418503000081e101c200303900040c040c5104403460340891040300c1141c0019481c680103120fa103845c1c45800b848540d41480500c10f10360294000d804500300d1000602e003150811341101403d60340c01c2c00140003007a40100010580a16407400980d242c844c2e095880c036080300c85e880f4a410300000188840c01a6000025110382d80301c0c0b01c8140701c117844180d100700159815403400307130091005000055a01c410149604d2280703000f54256142c6944540305c0200361800340202c881c0e403441c903210841c01c140d40301150007034500d074900150030303269401069183c10b40b007648901e511440c1c40d07916400c1400414402682c140200a040b0303580c5403491b01c030490103492003644c0503a810892581a02c001440401144c01c0304a008101c18079654645e01048040d0358003422140c118814003c10341103161091240070300844021030304806940c50482d842e80340200c141c100c441150002c0c03008900a000c944200c3d400d50700205406900c80c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 80782897 1250 80781647 80781653
    0x8070b0405010e0d050414010230070b010306020415020309030601090510050a090b01020d090308030a0c03090609030801030b06030a20180c090f0609010c060506030304080307050c030d080603070b0304 88
    0x240c846841501a14040e644c1c03404400c9410200800071182c1c2400307102410b080007001a80c555134100780c603804d44a0040442c40003c5010f201d14a158580008104d0420031140c071a4070114601741c000f1a2079942c0000c0c00d018021525040078840c512070b100a618002032600400e8861506103d0404c0254039030340400e54a00b803403120711001d408060402107102c0c1e5601142ca010306580310a280c0540201292015401d11400140703040d281c01200d031a02e0758656070300c200007c010200c6014205a6109801e100141e1240910803005010b5903910009504500741410041800341406e40320f40d11a00520000803a100601101d5043c3c0499203402e40000401042c1c481024181b000e05010099082101d130214843c040d01c4907450a41ea600c00c0e8946400501a50384103108a0344d012808250300c01001500c40d0704030580c01140a01683e0909075120700240c55600440d01c01c4415405c41199100b040c1410800d00707a51410782e19200c06031b82440408240c807080300340151400d50342e00000107414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 80784147 1250 80782897 80782901
    0x30c091e030f0303010f08120301031101030612050a03020d2303040215070c0627050f030f0607050a0e030604020f10110a110325050f0f0907030b03061308070b040501 73
    0x100203014007901d0040760400800e40d2254401d016580c0034000c00200480e510b44001a1400b030080500c8040b45142d00315202c03001c458441198607410907440d038002144049140704403480f510310a038010281c40c82d8505d40130f03040c25880d0300305008002845000684e0203950310300c1441801584d1413075665031b407150300214403608800b00703030101815000201e010401004207901000c807000e66031410680300107032400815040c055030341c54501f031540301c0003404186410094000792141c0201200c0f4641c00c9030103070300c2c2011300480d0f4020108030b01186100700a60000b484102000d004c402801c41762034213a00203410804000a0140544000c1c0341042d41c02c1d00030b20b65540da2520342c2048444521b803524007444076030000003030300340607001d6042244c0d00c05030301c0324165036599070341e080004034203080400f800300e940b5a0f481c2c09548056801c82803070658840c00c00c46ca010341da00346d401045015841c41410f14040000c0d1150544050014080000c02e0b41e041c01c0e601919800710408005440318148140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 80785397 1250 80784147 80784199
    0x1b030a0605010803031605090a0302010f1e05180a030b0406090212060f15090f010b13170d11060906040204110408190309050109030b0c07080f04061205010506030c09 73
    0x209461030079001080007070000010394411062680c200c0c3da0304001c0d1000716814007900d170f58940c0002c002e210500040d030064001a10b40d09043c40d2201440288811110000d540e411000c808607500190b59150070304658840c18000380c0c01c0d200004250700d5662000107090380144007500540c0e440303840d081195a40c0356030203420407600003114034504000e00e01e000350340015100d01d038400440001c242e205091101c4d01078842d642288141c40031381c1c60000c4a00480d40710030307409000c4030103003840400c562104d0440000307400a1f01c070042003070116600c805807029503000c60302c0950b58800c0e01003000d50100002c4096105070b043d0340210b0500c2a041510b0340c113000300d8221400e40d0280d44000b440c11060b00e6040100c0600a6136285075160f600c0005480d1a54940006041030f000100007404682c0c1ca00002c0000e02d104a05072442d01c100070b011009190001d401000002c1c41c040346040c0d042074940500790252a04482240c07940c00d0031740308103105106003041c0c240502441a043c0c2180f29403400005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 80786647 1250 80785397 80785403
    0xb0315030d030b01030501120f030804020f030f06040c0611030d020a0207030b0a05060f060a090e0903040e041a071d190806010609080f070501021e0f16030506070e01021b030a 77
    0x80c0341d4180390200680a0b2003490312580c006854800005104644801103034100e5410070f0402100700240d0304c044400507030040050303030861140d1000003001d4804000c40d1100c0745019000d031400e03083c145864407803e4283d0344400d0800402050a00e9207180200403240a030a10030001a980c8203001816400c00d821a07101900d070518940070440d14000039084907100740c600300c942c0540d0b00c485400300322070342c0210100b600014000041c2409044681840030340c200302d40500300c070b0425649000c0c4020580c0f0803102116403107401c035290704507009419203498010b0841c1c204501c2c1030401c50700c0e02640b0071203018071038072421140d00740d0913021505110350809440900c0036103485613114440605890404e1103180d49a1040203c915250724002c680300054490582c0540440c0100d4601d08a5050949d168440caa0241e4024440f082004000c402999455084102012495810081d081103001480c0000744018413103009003030303a1f02140c20206807c05c0700f904128611150b001c6403924100903001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 80787897 1250 80786647 80786653
    0x302030601062a050c0d0201090504090c030b0a141909050d020d0e04140a020310080304140f01080708040b09012012071d090403030f020d0507030615090b031503 71
    0x12600c40c1c0d00840b000b0003008208490803905002c801e00303500d43c80b00510040c0c0303030750001002d02000340707411410412220b0051611303d0282c1d031180000b40031184074400890b410072541000300100700610641d55800000f4035010042c1510709121342404450041074000340300400d07440611340742980d600c100d00654029088842c9041e003404003a41d1500d86034841c4003c03072403405102c81c032072400380030f80380c2c040d00480301c00b44113501da012149010390400b4010302c1480300000c0c00841c2d1064100b0180004010360102c1c5840354407440284641c1c0851481002d0410161070200032450341c010384070b5500250b01007000d0031103950f4908010700508132003d0001c914944520313030305406602e40002d40400300c42d64141540948464500b503914048000c4051440c00d000701c048009840c0180045900c64003905007c1f81c1c1c0d00500b00c16004070303032100f410b030f00c43c1c03655a5040c898180e62510070000649400e85a0114420841d08080c10840d1a482030340c0000d0000070001e101030103840031a0707480c0f04002c0d0403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 80789147 1250 80787897 80787899
    0x8010b0315040f05280c0203090409020a15020c0a0e0402061b0f07030312060b030f0a0b0409120c0c05010302040b12040c1502060106171504020a27030201090503010203060907180302030601 83
    0x81c034120803603079406180351803907001c0c0340b05038040d184038122584481f40c000b18684500308051101a007480392050381d005480c0c00c00050340c0e90f11804a100c10868541c0503100dc000f404041080c0120260003034038103040c2c40c0d0304110046e210607007142c1e60018004e00280c1c0c0700710b800103424a09241c82d00f83c28a180650384000080540040c003100d588004882d090111a071142036002550004495020054950001140d50303503101d6032000003c110080c0c80404e8140c515140c507151a41000b15400001e110505240180b0100303c1c482c0c4080d1500346070940c80e00340f40c16440d0816001e031001088250140c8c401240810420022460003050101d83c141c00070002907070040e45843d024400c5030b01180101071003014050303840000c00c4c030500b045480c0113007460701c200c144402034005609003002e04c0351120080100700d00092041d030311808502403400da8507086100040141465900c554000ea0041c8103010041c4e64245480d6400303c140d1422071a00483d1003c0010b51264651010b90140207000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 80790397 1250 80789147 80789161
    0x30417070b041211130f060323151b0313031e0e061b0d17091c260405010f0e06010b1602030a12170105010f020a14011e0507090608010b0315040f05 65
    0x707c02c040b80c1c002c9805102c1c4841180c0d03650100e05000baa50a8980c2140ba01e2101da0010056440d8000c190070310410200c4002d0201101c40390300564880242c000120400e104050744800e07044040101c3c10000f5aa144c203200f409814a41c45c9840b580c411640864101902d0425030170300c800203920402242c021840c0300c54080c1111216004500e14814044000707a40903000040c07078240400480c0e6000125190954101d8103d840c4403a4801500580a542c100090744c4070240350049004000010304411609140c00031513070800d4101100e13401c14001001102c51220581e00c5c0c400d02d41c502100702c15110f200013401c2001c00035008003042c11240c0014009a03018182001c0b000502d0008021a621070b0010f40700300380c080c4030281c0160320214408001034400603814903181c0300c05d000458000e40e00f50411801c0c00da89800112107030f40c0c8030100460140e0141c401d00040c0590300300810305505040403841c1c140300003070101031003480b00c0c441c0700d000c2c0d1100d601414841000c1c20f000c0200c1e0400c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 80791647 1250 80790397 80790401
    0x3010204090917040303020709090305310801060e01090b011b0f02090a050c0313110a03060e0706050301060f030c051209010c0e030105070207090908040503030417070b041211130f 79
    0x342c425901d500c40040403032540c9009030200c40c15030360150003d0a1701440c100601c2e014081400040702000410302140020001c558a0240303442c50b40008a0117071240c4561720a0050300c1507000f41e02c1603050080c2000301201e582a20f40c19603101c80c0020032100060703030040e2424021550030b0030107598004011024804102e02c1e842c01c0c83d00c01c40b2140103035212682c2a8082da24140d50400c60424100081800054012680d40f0018803840c510104050700c0c40000d4a22040303640207031201901c4500002c0c0705442070213020058505410b04c0c0d411541804001461b5a00c50341104041c142e035401d086a00d80d01417000d50750f07081c1e40440e500903036107881d00242c1e01802d44580304102050320211000386034a818090140b290340d03158000c0280500d403816000c09005411020b9072140c50400c40422151424030080c0040c0010065840b817030404442e20310f20b440c08030303804840c104500384801d0119096500d05012a40c0d005400c4001a04107280019601886400200c882c1803502c000c0141040b80b917 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 80792897 1250 80791647 80791661
    0x30406020f1204090902030705060408010b030106050406081203090c0a0603060608090111180f040203040320070602030304080f09120106050f0904081e0705010614151c0f0b0301020409 81
    0xe03825904410a54000140d0300c4581d180254210102800300380064100c40e440301e031209000030121a4900c0d51200400d0303581d030158208440c0c60751511180f03a0103003001d004000c01007905507010011340f46446002502c2e030300460300e01e840c0cc04000011a80308034080007581e012900c0200000011561090003a000f0a41882110042000100081c0c0c6804040c4203440344100f56403070081c034002084070010b0410404044580d0b0001952002c51040e480328405148518426207a10340341c2e4000b443c01e411a54040801504140e002c40c6040c850998040103403508107600c04e203500c2c3c5403048141100882c0c0980d041d59508039030740207500d002107401504004102c3c0e500740c0780b02c0c1c0032286403400c4c440388100894000c0d000e104200010b5041d0f071041e00716a0720030070841c1d45d90b90a1845a40e20759080d51004d510039012a41c401510f00840d28140c241c07084c0c3d00d02c0404050345464081103c4461340300030200c010112690354a80d82c40c03d0386230341d0403440c140b030001030086684640301c085e1a0014480303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 80794147 1250 80792897 80792909
    0x9230103050c0a1409011101060f0e010b03090c06160f03020106140303070c0e1050010c08040801092001020102120f04020f060c0309010824011b0c080304 68
    0xc00011841001032842121915a20342d550f51200c113414044114280e80800525810049561040781d00381c0020310851010740103980000c0901450182e030b84092003410f03040032070071090400c1031049030040020800002c00d030545860f5220603d00c09a450f00c00012180601159000c170310300030800d6410b600c980251030b850fa0710080c2903040704080c10b9680c00b6a050082c00106141018000a04102005540030003d01032020001c2d4480804000106207040b03001c203003000c02c0e100640c0c3c000c1d07034061144054448005512210301100b070061541145200c8003814001102280b000b84081c8004503009425094000d0041c40140d1810340380a0582c0080004140407450700002550700c18000c417003001c118000040d0054860f00c905841c420400341c070490f8400d088443d140920b17103481c0301401805082c1c0001e1030b26850384400240c60444010042c441841d090481900c01c1046000d40840c00302080c41d00480c0b81d51144a03500e1510881180a00300c030207c4d100c000380f4008004000c1003a901 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 80795397 1250 80794147 80794151
    0x30c060507080c07020105031801020708070b07020c0604030204020d0603020303030702030d2301030b1315060e0601030b0a0b0708090a030507030201020f1606030e01021308010b180c0d02090109230103 88
    0x15a009040b00d60b4401074681031010881000482e0141d0702c43d80c05580c00200300000c10110b10000125542203910810048070742d40c0010640f0f01c2030240d02104c140c0c0c48582d60001d81021030714140007a94911943c0002882290301040c001800401c9920503400385d6809011030760303030b8109024041d40ea500700501642c1d0540c100725000315503104000a00f06c3d0403045401040d0542d003076036070780c9152060040c4941031007180540300c0ca0100300304000d4070448007440040025411f040041c40b25110400078412814181004014070075500c60307041003c03c403440c01c021140c40748a10300c4c10303180d1403080710326460f40011454008030038083c0c04030703440c03044034400d8003110301041008000d1a11210204519845542043c0f8104101c2c0d001c2c0c0c2000500f4440900010314100004400030b80c8071450341c105226034bc1d518420311103035041c44141080b100c0902e440c100034a1404424544552140c0d040c40d224940c3c02040c9001c00764041c00100d4040c100004030401840881002da0310203160a40c89240068 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 80796647 1250 80795397 80795401
    0xf05040c1704021c0f03170f040507090c0e06030c0904051f03030c0c0e090120070503030103120e0306010306020703020616080f071101110706110c071e0f03030c0605 73
    0x74001c041c20009000c1a40d0380c048965180d400700403443d0102180c118640104081200014802c00c41c110803192094482d04c50400190b01c1c00848108014916000d1840c85024800812000650041202c00465011595074126102161031460088c1a5904050f021003800351001c10701d406001c81c0b240640f4100400d5036081c01e4a003100380749101840480400110034804640304851208005002c0c110610100341e0310892800c0744081160310503400e0355076554110440101c01a01c6020954604c14581040c1080c1c44290320ba120602c40105075651903040004414024180042040c60003425a46c540da928101032020b58001c032000c900602640700010140c405454003200310b01a07585e198401959900081032403501d01801840501211504034001d0f0b80702401001d4002c0c0a5440241d114403591906c07006440070350180492164041c0940054504002201e0007151803402444030800941d8520031942c941581151f5071007204a10080705164001c100f00102c94802c036800c010b95 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 80797897 1250 80796647 80796671
    0x60903120c0804170307020904110405070806030d0302030a0608010903050a02070e1603020702010e03060702010605030c04020307050f070c0810021c05070f0509031c021e03120c1606060f0504 84
    0x310038a400007001c82c003092009020f24040001c10a40c4480c3c15021030f850311641e1340009210050440d001c8620000188003402642858066203030070054500f0011840d0605500003602c0303500c0744450710201603021000800805864018100070011305008221a0b080c50600400c41e501403d80c0c0c10140c4902c08002815041c4002214420b1042d00304419460a450b04d0447c041c1d0320860f020b90401260380d66905807681c042c0704040c060407042d00006011441c00b4145405c0c6443c07441403901c12407040c800c0042282c0c00200312443c401c008001e440c3d4030b905616016420903000d400c1302c00b140c8545164810f00b40660ba004002c8250400011644d03c921a0301a4090303500840f000c0c800980c81c030106085140c014000b4100a0070000d0a9502c80500d00d5040d00c2c40c2030b4179801d41d0300181e010b030400c41040e2201040c0084a11002d601851422039540300d045100c01000c2c0a268003407800244800400403000644401c4e1980001d0138408c0390350b60242404044898000c1310701c078614000d0410b0b10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 80799147 1250 80797897 80797907
    0x6020303180d051b1501080708010c0503040b040b040201050f041401030506031f0f020702031c08070504030c0302010810030b130303060f0315020306040b0907020f0607141606020f0406090312 84
    0x14401c0d4550301d46251842e10803500641441d1340352800f541c3e00c00c2001464031043c118403514081c0c012a030003030010394603007242c00742551814194035090206c10010300001c64203c10b40302e4bd0082e00a00003142c076032124070040b1a244601c400d04050140007041c04540c100d483d2a1801d03120900340d0b0180030342d4892a0815488444000240c1e00d8001e12600e9042005066002611100100740c40103003060002d4020a003401750180b01b10b50800b06244141854580243c90550404814645141494110340d240620740c000e9001c003034144904a8000b030441c254294031140516400080e9040a04101c0c0191062441c441e0b4100c000c203080003070129110807a02c84540071240c1200240d00403000340540200254070180c0b08581094903400e8041042d2189160729008078155401000b810410454903814150007400c2e100403c154480041c00440002c2c06854442001d00907402e83c104d120320b410002441280480c44031480b0101d00012001d8000250400310381c0121080f0950f20700303113081112 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 80800397 1250 80799147 80799163
    0xc02010c0e030a030e0a050a120b1503100f181103060106181a1b06040c09020405060304031209021f030f0c02190f0204110702030d141801030b09010602030318 70
    0x1405074801900f000110740700e19081804581c0252101703000316142e07004110f001d0255041100e1130b0041151090401c40755103409030b071001c04904590000080c481c0001d45a000e880c64410900d5250000358501c025542d20050521030214565441000d880c94405031003810005114801c2c050140000340d8940507020500c85840d490b04941011800c04022030540340c0740300508003405405111800e40d54017900314800301c0c5201d4800030700c400d10b8140b82ca40362540403600310360412401480100b126444031003d03aa003051307050901260340c64216001c90b0007018512000b80d0f2102089900c16075108800235042e04420710790b9002d0001010440400701981e524118010040e40260702c114810030400c2040716041d803084800d007070303d41c0c001e800240988041c0300000000c2800040c000c41145010007200360715407810b09040c40722142c0c802081006000b01680c91305844e20002d80490217a21a40c010718510380d004044210300c2d610768400075a42d41044544202010303107441491902100050444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 80801647 1250 80800397 80800399
    0x2718110405060616140d02150903090906130e0706030b0310050108150402030f12031509040b0103080306060f030c03040618151d01020d14060a03030e19180c02010c0e 73
    0x586880a05121142684507900041e1004a845e1500300d05e8070200f4405101214401c0e801404c0034290140243c5480c0006421380209600800907071030030f621001c140c40e0b800a0220b68000c402c0c40c498402d000a060030001d121543e006d00d540c045507042d00340c0e01020b581c2005a01f00c0c1c1b20082040c08041c2110700c20f000e1517150307078004012411000004918030b640302c4d1010701a2941c0201c0007076a02e140c0790001103800314282010041200c2c0c80a000c8403c0d240003c211104803540c14684c41d8440d00c0c1c1c006000141800f0400400502a510790808548010307614040c1c2d9a0740749803c1c0c800810581068a0032501c82d070401002043c0a9070001e19540f00784d4011909100024142c2410f400078502004800708070101988807041740c180c00e01c00303003001c210808230200d815500e003610030318181da004244078840c100c13400c0c003800400e82c00903114807043e4050300c01c005e041d00c16448942d840c2903941e01c2681c51144001000d095641150010001201c05800a101881d41140107403480c011a810381 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 80802897 1250 80801647 80801659
    0x5010314060409060b060304201e1306050d050c0a05060301050306070503070207090608061611030a0c061116150911100e0909031c02090307271811040506 68
    0x403070403601c1c055000c0380d100351040c50000b81c440c4000c400309a540d0802c42e42940c265050a440042800140b03002c220002003c0711554000d460400700d01d00c2030700400451030b000380c5080401820240711a40304d940504002844c05c581441070745030907aa00c00b1201106402141809000205402c1c26020389041e00c5004018000c00c2e03840c0c120031200d5800007040c51045100e14030300012840410310500740035081741006050b282c646030f042c2083c01044003000701d040000e0520103401d1070b41c0100075200010388a15050010324190304010002e041c1034030600e801141d00198800c00a4005c0012140711407040c5040500e01c1c04c007050030800ca0315090300291000c0d411140400c40307840c1003c04244515074504201000341504004074903585401c485402c055400050780404400c0200154020303420048010740c60100d01402003070310b4610034418600928050300ac420008d2070980b0401681038a9040d0030809440313051001110090f108109403100d2030b184a01509604050244520404000d40740d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 80804147 1250 80802897 80802901
    0x30d0f06080a050601150e1504050f030c0319020d06020a020106180b030703080c0a05102906092e020a0218130b06010c080c01050708070c030c030e13090302011505010314 75
    0x6c1d00380e4179160400440400200014402d8250748041000300d0b09030050700c0150700c0f641018180300c400d03040460303034501c00c0c2c0c0301c80c81c1d4042d296070002d2501c064901081480091303451030303c041149501440030041c100c50021901042441e41548050b00b01c7e00000341e805141e41418000703008031040b000c08036406400c1504140086007441005040d1511140704540d00b400b01500c030325003020342c03201d518080d80d6240d0309420b400102000c8071070310941c0c503a0340c0c00400031005400200c0e0741c400e065040d40030301b0400e4500d501c0d6503080c3c15424051901e101c1c0d030400001d91581c000392200424007003280310311003c0400c00c00700b404543c041845604006000048003a080e1500381c010100100f01604100d01c0c804d07048005012000640b03000f4600400100e02410704540251200e00300520400130091140040c1000c69401041124955018103003203481c00c280c100483c90302c210b024aa40700b0b4900704541242090b505511440e414032140e58031003030141d143e2004509940420600355180649000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 80805397 1250 80804147 80804159
    0xe15070206010f0b09101205070c020f0303040b0409051302030a05070806010b0f090112020c190b07051e030402031e0607020c060c0703060b030a1704090614010503130507030203030d0f06080a050601 87
    0x2000d1b44044407500b081d07450550f1503007250007952002c44c0c1c0e030800074402160010031810100441080f940e0120055400d1500b880702059507409039200707013413215071a200032580c51404840340c54802600902a03946c3c42d604c0e8200160f40e200a84900c4115124030b6000080c00081001502c80404001106078a810510001100e4000c49810100c014650070000424020310411181c0d902c01c0c2c0040340c040c01c1c882c0c1420014000040105810305200b000c201a602006c400b100a509600003540610740700c0d101e50012a10300084500340134516071a144c105498104000b0725103100e05c49940c00c582c0d240401506008103402045000788440c0e01c080710520026013140c1248044101c00707000c0710001c00b00c0b078076030110541207100b540c541c1030400141800010128010351000d41741e00d401c4d03a5601c01c0b12a000800380d200007400c1101d4074000ca45c0500c00c1000030300c4107c0046800404590b2510704103c2c8c050003c045600c040e11034240f404030300254007180481c0851034241c118020384040c2e8a020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 80806647 1250 80805397 80805409
    0xf0c25060801060f022a0f04050f01032a090506030c030c100f020c101707030c1d131103010f050102120a0e06040315060303080601051810030e15070206010f0b09 71
    0x1074400065010b021b5890749044a00a10840307040c1e454202054124040c0c81803045501443c0c8807039000e01c0c103050030492aa1034407082d550459500c810789a00d00701d43c40c0c070305002c5e0403038000d080f00f008410343d000000c078114503400c124000c01017241500c86955880d010559560002003103541c0026450034280301c024000c840e1840c000203a03005640c2c3c60700f0f00100080031003004070440800310750760680302103484c14043c541541c0221681400c1042c0c0c20b1108014101c5904140b003a000c980c8c0030382242d0101d889860303c440b04c03414800000d0024400c001c1d03110320103030002d000f8103121215108001034a5840000c021145903008009246090003240c4226000035510f011030ba0445000c1200000140a00e400a40100180d007000500c4600b1498010006075002d40b0450402c4402c1c0110380003018a0402c00007a410210f030400a074006422080e00a00641483c1241c01d001d0381084001e03540015510705d1003000940c0c00d44900eaa201d480e04500305520380542440c85c4418000c06440e07040031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 80807897 1250 80806647 80806667
    0x306010c12111203011a2706070501090b041209140402031e07030906110901120c0201110705010914010c0203040911040e0103051b010e030c01080a020f0c2506080106 73
    0x60310704200e50200911071207140244100c445503c2e504000010001031445c400c1303000241c071410840901d003400b40903c040051091060100e080c000340800e40002e640c60808548905d0340c08002440110014103084d00ba080089905503858a188000e00b42c1c00b0b80b0407a02181a524601101b00920106606000c020340005005803c040b00105009210740302c40051241303c0c4e26507a0f404581100d4034035100090b00d44c40c2c1d0b026480d41000b4800740c001681c00640900c0d804202100000d42200c2c6003c00f02c0c054941c0491600040300e0000300c0206005040d000070b103126015025920003d82c442801a081303915280d50400160428803051200c2846130300a8140f070522030030000e06107620340c403881000000a0b40f003181c041c1e001d0103100807904054089850440003d080c07010050741ca6502094580341700c108418100814080002c100c0310701355042d580304200c81c2c400f0580b0341d034204a120307030780303141020202104038402c6001140074110346642c4400c1d24031660300e0080e982d00e8540213032000651 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 80809147 1250 80807897 80807933
    0x7030804020a03050a050607030c091505031015090509060f0108040f080405130e010b0102060f1f030c06080402090a110f07050f0105040b180304080c0f0112060806010501080105060306010c 83
    0x1101000020030070070000881c005009601900c0d1f50b0401d84005012a060f82e0124014068800700400912007510500c08440c0c0301420070703554035600e030f1020610800c400d801180007018031010b0810b0003a80006403d007501e4056070300040c140c0f01c080800005801105003140040c2101c000200000c0c0c044901d2080c9501c900c0f4564240360b04c900005403100c03282d00d01c1083e0255141c06154001000340190418040280050603041c2480340c0f07030000d45280145504503010f04105e061290051341200b03079004681001c001c807004e03a19117100030810201503a059101700c52007800708041000d1482078807031409078110307094540085101c031103c49800881007602d160007200c2c0d480490b0b40c0203000d09803007180708000404003440c042015418207007800c00c1e480803c0d031081c81300707000c10000068408122607048640300c001100120040b44c40d118424025201b05050010018502c1c00009416040c1d4200340c0f01e00c400343ea00d503410700c0742501080701d503140080c090b2010000400c603211503110301604 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 80810397 1250 80809147 80809159
    0xf020304030507180c170402011d06030c0705070503070803040e04030522051e01022512030906080a0b010f0e0a0504110304110303190f210e0c0108010b0703080402 72
    0x40d0741d440d0701c1d0502c0001c0d4800700141c0000c2c150b04040c04240d126400250100341070501800c000c0d500c10341500e441c001c000074140569180300a03031451b64100751b0840304000400041d902d00d0500b4a00131960024882210700d0312941d0750218885c03a02045035829100d540d001581060300d0802840104500904207500f4020100050f0311000f01c000c0c64426940d00072169841200e103442c0034401000d00361003a404224107640070600c000da03804100941d440c07c4501aa0301c140f4080c03003c10380900d2041d44801d5401421703141842c01c054000711100c1c01c41c0c4480d2500d01c1c0780d640310f503084411385100305c6080e4000b485200d500c521443c0100d010606801010b0401e134482074903038003c50101d0b0404103540c2031010021003007000300248107503041c68142c020f0f0301440c00c140c1c042420045552400301da00040c07040d00c0b003c540300c2c0380c411140300d20982a00c90700000482d460380c8155000f0060f460300440940180344002e001940540000d904030b5212191051600c41207031000c0390050320281049074050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 80811647 1250 80810397 80810399
    0x504060212010b070506151810051017010501020a03050d05070905150c060a020403020306010303050705031903060806060d03080106030b03030d0603060203060a0909030e01050309010e0f0c03121206010f020304 92
    0xa1440003500d80070b0303e40d2040c0306940e90000d051180c5040c4005081e01d00d16011403c0f101d425850b00c19500004034043c055109079500e40128050510645410040c0c2051000d1401c036601072744004014000d00002600c1c0030740c1d0b600c1c1c0004a80302e02c0307000780160204004100d40443d000c1c41e80d004591090301c41c58020300c4152103a001170070703a83d0007600055819002144c03d8102031001d12425800c0840e4010461920303241d40e01080c0c4441341484007409200021500c002801400d004981c104801c0312008101c0009010700580108400d0040d600148036100010709103040c80c0700c9207802035401d07072500080f90f86044030403405802101000c4c0d0700760209200f94118200c0b10b0140e80302035449400e0240e01d078a00710701845140d40140c0e2000602d94208901da001080d04034003100c031400c2080c030306680d40e6692071298502520304031600c4601071040d0301c1316038000c41002c2010107140f08214152400001c03180c140e021540a40d00c417000d0080c0d081004500150f0040500c0119040d90780140c908107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 80812897 1250 80811647 80811667
    0x30402061b151009060501050c07090b061b010c0801080303040c03201509040b0a120f020607140606090c0702010219020a0b03130501060506070f0209060a0f03030e03191505040602 79
    0x4001903d520188405004040c0184801809650040c0c00c0170328201c0d040c0103140410301c0d660a11032181c07a489658a41210740303141c03079442c00ca81401480d0200015005921041c0a0080218600110018414800100d1070b900d003c022280260f0f04030103070b0901c1d14215200c1e81b003064108006802502480c005001c0582c55520130300718420801c2080302d446440d2b00c01800260340c00c01c26181c0c445c101c8014140500b6115494056100d03400c80b15150504609101045843c844c1442c060410aa401c00301c0c0000c14000a0700c03441002c00351402000c9450310f03841c603942805141c50003400340c0c020020015000400d4402d25641700d0009240c6800e41f55114100d2015070700a5507880e00d40c0c0f10006000c030500074240204001080169021803a01c0d01c00d460f002c880314101c0740000e02c1882d005010407055500d540d13489011b80f040381070350101c4c903581e0724010703043d0603400006902900815036005106100d05491100d01a04840c000b44400f0f4041c0d4403100918004008580580e801d00100310b032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 80814147 1250 80812897 80812933
    0x140f040f0c0206041106041a030705040315021306050405060f0c010f0603050d0806150418092f0a150503090304031e0614090c101106042105030402061b 67
    0x10204864015082605080c10711700c030010f902c15003142c05890108020070148440034031100f9030314080408039440352503204e0222400d100e00c2d031000d807001865080d80184042284e0041c40e906410302c2c206901155a408151007a010324444c640e0b00c6081481010054030a010040282c50603041c00040e025103001401c004a510940083c1c4e445d500000000b0341107034100800070b802c41c1003100d04a820b0921800c0e078030858415805850320b20742e43d42c40000340c1d900040e00300080260b84290402500080740784078158603002152104090f404a60300c8400b24140342c15150142c030790b07000e404002e00c0c004400945060b40051700e00d1500d44402c00002002c11031000680321071107a2002054a40380185c00c080c0152580c000c9036003000c100300c2060107205200011079503625001622070044249a00800f07851011281c92010103038000ca0b41048100312003e602000003000c9122100f083e0082490112241d00040f0f9000390401020490247c0c4440d1100317441500c540002c0031141d140110010b4044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 80815397 1250 80814147 80814161
    0xe01030605060a06210c0e04050403050901020c060f030609060a180903030e030c0d0819050108071502150103060f0603020d03210b06220b0c0d0206010609140f040f 72
    0x28525075039000344000362528014800091025103448281d005d07810320301c0341080010b0081e280006545004d07500003140541806043c0303460080041020f4903140c10041c1840d4040d042040c0180500c0700d90403076030f1a0640580b078955600340a00e509569402060043c03225025240b917610056000001032050064a00c10b03407018610b46001c2800c04840c9006000d99072a154180500c4d002407200c900e000740000b48401d002075051502d00e07901c0d00c0305a4040d101400e00c6020030941c0f07050000109007440300046407030403030b9035803810180c00450002d004c9882d124450071003240d041400b401007010407005e800031141000c0b0710000151035070b45c076400a0450301380000c0c04c0f0701150450500310005140301748500b246009808003445150700043c00109140f059080f44405c5071444070022007207030300c0400ea260207844001c013183d80d20781c8918060741d42c2c0e4a0307211200005105140c00400c04c2807113115010110ba0030210800d80c00003140d0b00f0040224020030110341c020f6910300c403032010b044050040813 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 80816647 1250 80815397 80815403
    0xf03070515060a050915040f060906080d02070e010e0402030705120a0204050c0414010507051005090f01051e010308071b09060305060903030f220b0c04090b040b15090a0e0103 77
    0x401d40750100390110304507000038001841541d2102040080b510383c038040b0fa5001802040d4036189410500c0010014808034500c00c40581c981100410003c485901c118151034041c0200c3c2d81d10081e05c4000c907983c8015014149482504000402540c010700f00c2007504503100605550b509030701d600c003085e060150b2540541490b401401c05d601075081c54030070300b604810000070702490301c3c0c140f00c0c0d82404410039a9541d81000300010b210f00a11101340194002412034003c20300075428014150350b41c4030031041801c1c0c41d44d40303024081408180f000e60015010741c2011010212603282d038581c403459030443c620607034210b1007070452180108108078000300a01944400025003030301f5130a01030300c4c0c0800103004081f0355104100380034444141c00350242d4000b6140c0300c1401b0010711490004440347d410b05000305005174038401e10408043d101d0141c000c0d940d420008114801d0300c64104002c1d1003c012030141c100d161a10b00001085402000700b0071100e01400721004144e45031100c1d940302e2003d81c019 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 80817897 1250 80816647 80816653
    0xe190b030c03060f010903022209080406030608060a09030219080c010f0e16050901050d0f1502071a100b030714030c090a1505030604020a0c0f11030609071d06030f030705 75
    0xc2554a01402c1c40d03e13081c01d0a05c3c0141309a03040d42d0101d0840d20580e03402c2c203203103041c9260010300c9071116046031192950042c2c1450322150f86500c0500900402c0c040c000c07050140000060b0400c4403441040180ca0b007590003818400c0190b80c0d0f0149019207c0307025a44410100545a001e4209005050101e004c00300001a0f000c00c89401e40d040040c58244402d010380540010800b075074800902c6810758500b29414079081c013880c07400207001104084002c1400f042442801100d0711103902510145010311540c0821074505c1c01020104d04085400d19000d80d40c0610074401411400055a40500b082c144080781400001d02d10a41e03400841d10700180d52000a034046240c10644442e0000309040e4000d90240f140c0c0060142c0380b4003008190a0003590f01040b03400680c0c0c819071280a07815000040500c8002c01c80c1042d100c0560511a983d0080c41403102080300701c800080e0110485000c06901404200c100c030400c0c4060001800d0b181e410b1240105840d0341640900c000d020080c411002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 80819147 1250 80817897 80817901
    0x4061421040309080307240b09090c04150302032d0a05070911030c03011701061802070c050a1d060307050a06050703021903050901050702031f020a1209030e190b030c03 74
    0x2c01092000542c215034020703001848100001203401020408040c580c83d007044105001d40012401003441c0e04020303034401040418005074680100310b55007a9881542e050242d0058031010089080355807200075010703401b40c141d00325500c41d1403074400c1040f075a04961400c8000d500b9121440c0001249003625113400042080042c01c1d028483c505103220301520b4503043d46000d120900c914001442034460240d4008004021580c00303520000103400a034107010790401d4500c400100a40104000711200b5141c007001181502d402d906900440301c001c941c08904041c1401e0b0700b2002403015002a406215444c004202c590700c200c010400392406640b6280c40340703120306000f45031602c500340c481001c105252010002c02d074072000321003406c0000e003801c50317681aa62021a01d0030510100701c02c4064402031149c0c2c4400500e40080031503500d281c1d55400f0528800070018100c900a01004010801d0b13602440c21500b8800c0d81400002c942100d14605aa980c0e02c80080a9000711022100c48a002003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 80820397 1250 80819147 80819153
    0x5031801020a0f08130b041211010f02030114040605150f0d020a0f08070c0201051603121506031a0603060409030c0b04080a200d030e07050a0305010903030612080406142104 76
    0x11001e500c000700d0641ca489168190310750101d440320161018041e1400641c0d0b8500c4a400340701d27807649000310a00200f205108411045001350403e01581441c0e10211034540b401e031820f07008801c1500d00040900040160340f400184144c2e00902880d140c0030070900040c182d02d001e52007d41440c003c84d846540540d46603a03c010002400180b824091080030344507d00580da20030151414086013002ca80341c003c05500b010380d4010005004103203680c4c00c3c038000801d6010303100841070844005860034004100740c22030b4190307404000006a0f421501c20f00c0040d074945020f401c060205800703070600040c1c82c3c0b003a442e4a5220380c801c84044c0c5815000190070b0807039552141001701105020b4000100590160742d4194071000015142020035842e041c20241d1543e003840802c009140c001c0850044550340c0c68200d01030b11002105901081c5000400106021600000715000e544610780380c1c500313420104140d4941740c00101e12410300c8414804203070804130510045c481034070308864500b100d190600e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 80821647 1250 80820397 80820407
    0x302042c030c0303070302030712090507060206090c0102100c140d1a060306060304061d0a03090801050106080402100c0303150b0304020a080c060d050c090303040303050d23060105031801020a0f 85
    0x4044100603401001440b240307040c0401902d401c81550324003d03949072580f0310121341824031014400032a600e400010340030072100044401c1284c2c1542c0070b03a42c1c90b0361181d00302500ca81e4484810b0780035800c01d142c804119042548546044c207507509082c0a0341c00030108044240d000f801c4c50044817503588455003003141d000200594000001c4625514501e00080414030034040036200070410f90302c441d5003200b4800445408200e040710641140c0762403109043c000e1034400b091141c40246c2d468280040f8400d07100e98070851145070003034000300030710540c088100c8032110061410790401d96581c80f000d04040d244620313000107005400302d25032641481d00411008508590010b1000ea00040644080c2d03111001514007040e00c407400020340d55110040d050251090707100e4a54940000100402010b4111020300b440c1880c0900402128801c0070500ca14a1502d800101c01c00008000103a542e41c4507800955200d540c0303100d5140c1c81145c00311040e0aa8004840c120086904081840c604540c08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 80822897 1250 80821647 80821721
    0x91f2c0709050c09040518100903030501080a050705010f17070c050c0121020a02010b040e06010f080d14091c03050a120203010f0b0304020607050d02150603030a020d050310030204 79
    0x41e01e03042240b070524180060562194161080c000c9490790b0001d034a03980c04481e03a44d54003060000740c840d07421820000000800f8044001c5001c02e240100203d0311740000156600c0e40f0354401d00078076809050800648610500000c0102008100d204410100d0404040c0c14015079003915104003003640781c82d005c0c1c28020000032803070400801503a000000c2410310702c0480030904401c00180d9400c191f4804902504403d8915a0014100100d17030305038a50014019040300c0c072540010348015100c01070152590842988400002c410202c42030340b12041c503008202140000300006080070702c5014220300400c05010942c0880c0e80442e0901010760403a0074003404003450740c0c01318510b60501139040d843c240e19004400c81302601000050440d2520b0044030041764000e000c441401c10840402940c8801e18032a0b1881800c1485c00f00781c003410008181ea4079140345401424110108040459080c0c10050848807a0410f001d0004090b85552040e00c1c00320000d1700300d03060314400d00044010b40b43e031b030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 80824147 1250 80822897 80822909
    0x18060606200105060102060a0e011104030b0402040b0907050304020613050904051e010c0c0609050309060409050405070b09010509040b06041a0c070803040506040303050906040f060201140906091f2c07 88
    0x4020401250343c6e804281603038401ca0420340051916203440c0440e00400050702ca000303840800203400b10a000c400002d141c03086100301e9045c80000c09003002c0c080d1000c07050300d17a0400710700140089801490000301074a100c07035005e92406c00207070750340001810001c0142c905540b01d400c455484600c1c0c201c92504211500c5c5400024012403070904002001102081070161140f503440d010300c41004800d0044944802005041c0c986550300c800384c00000348030545046035107100d010000250305002c481600c0c100354058540c68148498841404040c000795031a80382d10280400c404600d000881c011401614410b42c606515510203400007450a0300c190080f540c954402d2004210641d680b90464007625403500d4816182c0b8508130104015000300d4001c20391108403520082a42c0d030b815808480300c030020070b54078a01c9403500e851580d100d010035a0250303490340000403000001071602682c042010030790a03002583c1510b400c1c5041d442c2c0402c0001d40b180880782c0070444040d220401003180034100c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 80825397 1250 80824147 80824151
    0x60601020c06070209150607080a0f02070501050d0e011113032603010b131a0705060708060901090207050c040e0d08010f14091302030a12090e090709180606062001 72
    0x715000000724503000d480e00c000e108600744000100500c9400b541500350440251484d41c40344614500b800a03034001484802c0001c40c0e0f84c501d4190188009006c1085a006843c2c41d8030b0403007042c202c0c03009003011f509621140d42d00d1700300c420500410500100544c80300d48a21060382425454015240c1442c500e41e074500030003905100d801011241d0840381142c40140103607944030081004d59044929903070010841d00700003080c4040f1040e0400040540c140f082d01912400c0e5552201600d01c0b02003070301c14580100c440001481303a4a1b60fa401009071600400c1110111407082c0e002400f07640c045075070f03200e5503000f4000090005801c2110540503204004e15940c0b6141005003c10f80c40c240002031900c81d06211012808001d1216600b042c41034000d401d40340101900c0c20300c0c5000d40462222040018005400001c00c440c0c94041c1c140514845005041080d203052070340c4028100100c11003000462004482000410354451140240003688400320014522000d001030031000b01c10007012380e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 80826647 1250 80825397 80825413
    0x40911040e07080403090803070f06050a0e0d140405040f0209010806100c020405040c0914010501021905070308031807080703021302090d031215080a020f0a06020a0f02031f050906060102 82
    0x210450201c10740c81007040ca000d00880c0d98504048135204807540c0440701d507000000c0d6a50a0102d440000200e09001d90401d100f41d0315600c0380402110b0540101c1c802503000781c0e13010b041c00c034411340b99000418441c3c1d42181c10240c50344002412a609503040341c41003030b40000c21980e556000369a02d03600050854100c0d6000500c0503019002440c200300003445640c2d250000b508004100c10540060a0480c0303040141000c00006120b0281c82801030038054842ca40020850348d5080d50b0500440e075010000d0710b0600d01c1c55030384201680000c2c10a6840808618a060039403100b04218001402540c0041044501c0e600610118411051002c3d403882e004000812158440d0880302c2c50683d49440c1104d4064001c0c613916005104e04520b0b901d009510780e000203040d034000200c0c141c80d00c1c001c0f0303400c60303802141c131040140c3e50300c0511440015802010300e85000c1b410740041c2c50b0905c3d0000c0c080d10b55251a151524600200001a45048075a030740c082c0300c14a0010806a42d0145013800180852 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 80827897 1250 80826647 80826659
    0x1b06091305040303020d050406020304020a0806070f14040302030111031005010e0609010e040b040f150906210503070510060608060d051e031e0a08090303060a150302071704091104 79
    0x34003400391480300c056849201040c1014865412100111041d00d01040f003820300e8944040a50300a9409902c0340e084040045048030700410b07081c1c01342140f900c1d03a4136500c2d802d41060b00c000780e02c0d080b80300111809002c0000036803020700582e200400810f81150f5249482d0100380c00e4403540d0b80120b810001001203d40103a200d200c201c8042560909100c01c480a4102c006000341c264220b51640050508551070440c507010f030131254100841030540c01902d51036092450031100f051140303900c800380c01080c0a100e007118a0700e015000703001b0015640b50040076140c10749040b1044070340c0203980b940e43d1810081d6690102c0000c0e00040120760068810f165910b07000e50380c42c550070b030203803612003c400300b1070b900d14041040b40c135420240c0500745040751000d802c5d103145401c02c855040100d4a048001200c2d0200882164410744005080e44103403070801e1030050201000300100c80505508000748408900303100410382d401c0c860b206003d079032107003000c480d01c060f100010008000140113000c14004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 80829147 1250 80827897 80827909
    0x706050406030e0c150406030f050c0406030e250f05030d09030204020d02160602030f06011106130f080d0902030c1804060504050a0807060e060f060303030718080f1b0609 75
    0x1c840e00c0707140c0031610303031402c4050905282c104058640c0c460041d000741111010010060b1003128902e46082181e10340c1509200182c880895000020b010104000e029041c0264410b8070b5104649048a0303c00045860683c084d106440440980103040b00c0c00b000031501105c0c0030b001800d401d6015025104c50344001400c540b213203010081c4115004118400443d1060b41038998004007200302d4901c1070781a0420200950050740c0c050003600c40b4400140d0194041d4501c40300c50710301c031802498541d848086034101e0351040b0f08111144184000710780c2c0401c2d040e8020340b001807107000303000a01c81000c2c410940b900800c1c022050180c02c0d03071010100c0300c5c5100c0c0282e5900a4204101049954580c600076013051b140b003a0040c0490703400300300482400358030344c80315648081c1c02c0100c50407910303840741e4403a840d0412918558150300070000124054170443da59200350f068000c1503c01152101e40040c186800324081d02d5243d4441c644030388550321114455280e82c90151883c2c0d00e81a203210100369 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 80830397 1250 80829147 80829149
    0x15040503010c26150301060f0f090e060a0b0d0210020618010c0f0804050a02040606120f051302010e030f01180314040f0b0c0c060d05012405030a1a030f061807060504 73
    0x64200014000907003032504c00f80203a40480001030080110b5a01ca03810400c1000480c00740e04000b20240c0d40200705125076100d815404210280189044d54800302030034081c01403403c0e6150401e6241c1400c00040e05d80d50303420b541d840c0c426005003109242412915061080001e900c5281c0e0381442000d131105a080f00404014401515182c00d0503541c509085203011010040290480d203081000a00c8943c060708511002e940c030403003405400000b501c0941030303a80a07990004103501102a0b030700150301800c0920380011029050710710700040c0d400c041e8211041c1e0798651290681c0300d4940e030201640401990a00c0d210f00c0a0a0704142c10410704c032110350039a009440909900045a5540c14020003014440800013809255a403601010040103440c0a2044c041c00c6041c2e15039680b125008010710303c54050040c2e88041c1103680d0300311003501074840b48440c1e00c40e001012005482d65107050245040800801005101038100300210f4503001d60022401d01c40758010680078006582d111040398 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 80831647 1250 80830397 80830457
    0x7031802100c030c3207030b0c16020a14040c080f010b0c0304090c0903020f0108040201020c062209090309120305030a0c030b04021306030e03070c18020915040503010c 74
    0x11040c0c005140c15030b03550000c940064501e200711240d02032031074000419400a40c44d0512400f062031305c04028203946031028000140302403902000110700007144801743c000441102005201c4007459000706500092540060030b6482040c04210140d05242c00382c03414440c03207868070601514011082031581c00040c01050b088d20340004268032412020400d03100640380c4603504000550340248064091000d038030040740144000107007202d103076000304072451060b81c060300609106002881004003a602c00320b604080d011302d200c040c0e11401d8190300d1050117404c030103900040002260402601c8803401c2d600132a11f241d04030340c4640c0003075880015a60408000b0790003080c0c8907050303070381900500324000300903030003e2000c074041c84840c1c04031001d6822035117503803807c03c00302d40d00d001542e40700d210f44940500801c05c1d18004211845a810000d110300348220801810314070a00001400c4405030038082c0c038070b17201c00f00b010b1217145002e11034007065003418181403601025031846411003054201d294 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 80832897 1250 80831647 80831657
    0x2313060f050613120512120412030501030812040302030c0f010506090a0605031002030a0b280b0a020304061b0b010e1503060403200106150504081209061210120b0703180210 76
    0x60303040045c01c10400c4014180b9046654807841880b28400038503800319801d81e0464213480401802a002e0b1103400d042e240c0004140c4e1601d1209003e40f004008003820071811440708000c1245555814804410341c000c4007400886c203414510200300e8110009041e50002a107400d601304540c1da070004110b0003000d05080056140e60319403082d24020300307140a0044e00201c01c20070301c0c0052512894a007100a04c25600c2d445000d03202d9040a0b16402201b0a02000d40e10070003003400158003602d034864840c494400c8a00c0b0740c0207955140b0910000c04c0e4880010b0100135010f011012411000c4440b040000390014a01403829890040a40c648410031403081c240402d400101850290003800103003282200c1000c480048985c000c01c135620610501c821030040b8000411103240b1901201d10b10b420040071142010080d20b001d0400041c060540104049016800100d101400d038050380024001c2035203000d207290042d005000c1ea80001b225030340300c908980b0b144006a4907a0544c2d002c0d01998644 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 80834147 1250 80832897 80832929
    0x1401020303070c0f29070c0c180e030a05070c0803030c07030305061f0206161b0201200a08130b0901090b0f1b0105041208102313060f050613 62
    0x42e0460340c5450190041e4101e034081d0110801d13115980305c40000d1111350b0a5141c2d00c2c164110340800c103003032000381500c803600707010130120114804404440701c01c03807000546001d072448803c0c5150710015089010070030104410061244100610004042c64000b5615625104540b042c992140c0e0000400307040d1b0342e001265007511000c3c03410580321051104003403c00e0345018084d40c7c41c482142c040503081d03040700e04501424480d041010080622100c80340103924a81c1c01501c02e19114041a0200b0304d1006108185003810408a14030f42d00604801da0b071000381c0d141c0c0c058002101c0c2c00440c1c0c50401007225a0b46664002c41150488407118001c90311001c810382c0b021500d2040f40300c1c005c00340c400c204000480341c0f03044d4001030066100d0448104100c080308800e641000c004c4a2160144010b82010000c802e000202d00c241d100701e80d035601c200f100320301000401042c0265920480c580d5121010b00110500214010240401310350307083c140044440b80020851b114000d42e200c080405d2030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 80835397 1250 80834147 80834153
    0xc033010030305090607060b04050411130903050711041b05090102071406070f2406080d080405031207020109240501170c1203040f0e042901050f030f0304080708071401020303070c 79
    0x8c0103000d1f05400410a100310701b1f20782881408500d81d141c0152140301d5104912001030350034802c000b0059455100c5a06201c09610b590609403010b40f41a500240c640e00d02d140c01e4000040c0c0d100c07031480315444a075200c0c0b0034440024035100094001c0345c094100d40d4045041560390f0303019102802d80c49801000c15240c00e00e8032268025000750140141140ea040b040d030600c805410030000d440310702c81181c11103800c5001c11540180281d6002c0c2c0035030820000e403003c0c4c071500101154820344500002c9061180c65a5824220501c032401c00b060395402102c0810140450052070b00501c1441d0030300d50030030307956901580c40700750a008681c4242400e100b403030081d800600503200101414001061220380d00d0551181c43c1208550450305c0c40a080443e5208281d00301c005c1440e819018181007090b03080205000b4040d1072000129414400c0c0c00d2844d108650030402407002d881440c015140d001e20b800e0100d4504480c1c1c1d001800081e44403140d61219982c00019240d10400502d484882200b80341 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 80836647 1250 80835397 80835401
    0x3080702240a0311160f080702060406030903081e070f020c090a02040e0a05010e0402040905031204081308120d180606060503010f0e040c06050c03301003030509060706 74
    0x1c224109a4031444041c020010000040e2070180d156440a0164501c1490782c51072a120300201d030900b503800810000081002070041184045c4139440c19490030519400103a01034004d44c0c00600065256042c0f40c00305507000d0501c54110f0f030282c0100f41e140d100c803580c0a0307a900000f405c0c441040601c00c4030031100c610801071400c2004010f1311030540780c00c0007180d0001951050242009000700000403c500000c00e01c40c040c102d4901507203404081d121a800c00014010404050340c441c0720034400e845d44d0280c1c0b1580240154801c0d10f4003a0741320303603d000b044541c1c0500e6000100c0741e00542824049000742400311080d0b80c000710800903000032400c2c00c40c050582607141c00b8104a1802001107030083d04a00118181c54484c4840300070990381d0b1101c88000041214000c0094034407100c00c02107240a80060800302002d035003500d0822500442d030460030780c41c0552411070100c500e4000c0340300c200c13501e0490b50000c0301250298801c07030030f5031800780c40340c402c0040341ca000c0c1800041b603105001c10343e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 80837897 1250 80836647 80836669
    0x20106030b0f01080f0304121e1b050415142e030f05010e070c110303041805150405070206150a030204020a0e010305070302090d060902130e0601091a0a03080702 71
    0x1c11071121140c1000e00428035110424010245180300d8800901d034500d00010a032000c03140100001c5403414425902da803284404035140740711040700c50300e0b6000081c3c203c18235003a208801112040f110740c0340c5420042070b64506224001c64062044c0288844481110b00159004050b07840c9021619a00954080520000309449501ca405d001c00d4003959071540010708a003461301001d00240c1d8075055407121410301940c2e0000802c440c0c10651000490b80400340264407030050a41c1c0c14190f13903080f561454451410140302e01c603038840400090a030b0400300ca10106170241c03801c02440c40c105d1006035803481c000e4000303051b035440c0c40341d00419aa02c117080f50303001e542e0191065494541c11000540120f440300d02d0140403c0c104000203000c64400c0c0300340c0f03509100040140381451510b0315800020310848805a800000d40903a01c490030520340543c5581c0e008000c0200140e6241010f010111843c1340300111580c607181c04003034403994070003c1000a89420184641d603407400341c40028203010340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 80839147 1250 80837897 80837903
    0x4050a03030810050109050a05010804050c03010f0617060f0609040f02130209041b020619090203030703020a0302120c0c04020c0f060f06030f01060305060c0705030f0d02032e03080a02010603 84
    0x9021808020198040344842c081e460207511801010b881d400103440da1002e5016803034121840c5507007004a03602c107401382c40c0c100d409002039441c081a08400700382503410003802860040e45442c0f041100003542ca00c01c5100720352070005042981008081506a418003401c024400c22411010800744846c81480c80e800f198003d00202140010380c110401a420010f0300921651428280341c0c0c100355071042d6455910500e45c00f40800c1c2e9100d03444800400c5010703105080c034a40d1036441c43d0040e00d00704014404140240c0041000c60814940280740048441c408d400352001400751401240c000980108540b000b1103015884410705501d8070701d40022040000340a102c0c000030310084842c8414000c2c0209415000e8542c000f10480502c0d080c0e03915444002c2440d031111000075000f41c4580c019045051007030098918003400d19208002a40000c0180f280d526800014020081c031a20020712131121a259090070010b13160115030710078040341c8409403c0010015050101d14402e52022025540c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 80840397 1250 80839147 80839159
    0xc050c0109060b09250327261c0b01121803120903021c0e0a060203040e070f05070b0604180b1b090a0b0f040f08061504110a0c080405 59
    0x109062074400780050f1501c490244d22058003240c0a004107811070303480c004084460102c210017001080300204020740b40328080a103e00300744604080c00300300584a03540620b071803001088100c8113a12001c0761105c0c12407039041007040008115141c20105906a241d071000c0000c01070a0303d001a81c0c0181214480031102d0300d000c0284018001c492154952540241d84483d80002c408204500311480c851014000d0390200401c00741038003002e18107940c0c100c81807400800b02650000411207105441c0c0003031001d0307040031405001004540142d40d034040160310305018030b12504032024000d80f24285028020101e0300340043d4558495410000541c80c031001e40c184080f41a00b00310f5814081950206988451080da410031121498181c4001000003070000d004e051815a0b80440c0c0c0e0b0101082c54908070040c400011180340954103c0d004000c0c103005042c203482c0042080b028083d004002922992a00310207003030b81482502035036841001410680185c1c2828200740580b80910f038440c0d42e1140c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 80841647 1250 80840397 80840411
    0x7020703030c170d0f0c0314070e06070204060e13050c03030406120b1f0914060906030112030212030a1b09080303011202040e160f08030a0c02040c050c120301060f05030105030703060c050c01 84
    0x945d03650700022020440d50790420407891114007031a070403001614403c1c0080d88948a0381120701d4582c00501d2403d200820006090303940e14000300550300201c035040c40f04821502d030481805000c0c00200440c041c101d0180d407410342481e801409800e904043c1008007903840010801a407103010404038400a54440040800111040104400164040c0a081d01544511920790741041001e444c9418001000307142503a007010f54007080c51505c12025011403150a00410f602000d00c4002c1d4007035400c0c035102145950b0300f495000c01c43d240714102d010030003600c9001002003000c080281e030f040d82c074801120300501c0344500001d400b0f440c852104040c1c40c060361036803000500c0040d4664040740d103c3d401c4807255a6580203480c2e141d015203508070300071890f196a500018a45a401210005a1401d19a04116181183e85e15215003c803c00003549070010045c40132a400c40c3c2c074660201e003030b0700c3c0941c655810107010a032902894480103041d00c0d01e851060051074041c10a440341c40d0a030b00c00801c412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 80842897 1250 80841647 80841671
    0x60e060f091216060e010806030c0d02010c060519050610020604031b02090a0203070206010b0708121b0d0903021605010e0613180203011d1e100503030703020303090607020703030c170d 81
    0x560312031140841c0c040e1440c84890350041c0300347e500c9420000e0140012440351003d200c40810ba4420407810054510180d500140552243c030780940320344041c60300803001c0e0800000c21128060405445403514070ba40c2070300c007640091b0703032a4419414078084000901518500c4005000e01500a41c0b0810b40d1007007140740c00166024611481c0d45a084030581d0b641c803102d5403103a109440001d890074004000c68400307101c2466083d03802114692003800c0f8210311a912880c290810000074815540740d80720107040c10382c10440c040c1480034484043d00c0080c275003400601091001c08041b801004003007210000640500180c40c014070200ba103000710024441041c4000b94002d010314510758403081d0a007142d16003c0a116031048160014600a600c0c00080e14103003500020207a03940e5070050100410300d038034140064004240301c2d4006580b0780c20412000750034020014100d104644c0001c20030004258403442c5160741c0354214111307982c0c01c0c1108160303441512400b1005206e59007091511500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 80844147 1250 80842897 80842933
    0x1e061e030f06100207030818060f070b07050c0a0b04020d08161406040309090509070f0b04050112092d06050408090316060906030f060906030615060e060f0912 70
    0x1140c441044800201d99802c0200b007002d001c400030f1800180c0c000a01400011003c000a001d0706545d0240064800818030000c3ea09900030394000103c003801048000402c507003951010703009452030405504103500740d0040c1e503594002d0400a0a0b90325088040780542d00e90765904c8401940040da00e60799130984000040c000d0240d44030840703800b804a11000050381000ca80c07140220b506680354001da500d441c0d111409081c02a000c0025800703108000504c40f025088200010700c01e0b0201547ca82c0d250000245c40742c0c0d001108070031a9820505d41d0f0b0300040c0800d03041c10781c108040040c001c01c0c0060300400036191300c1112000340003500d0b100501040c0070611000c1d041c0400220100d8107606408030524914007190703c10b400108403050340504c0f80500076080401111403590f00010842c5c3c1c0c1c0d10980c01602d603240d0040d01c3d81c0756115600010540d00f106188082d24140c00c0418003125544040b90052141302c884c1c1e0310340c80f800724601c440c594174100207134104c00e408001c40d44001e850000302c0c96 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 80845397 1250 80844147 80844151
    0xa14071209080606060a08091905010b0103060501030b0d02010f09030b070201090605060609031518060c0a09060203040b1c020903010c021e0f07150509100c060501060c021e061e03 79
    0x440e41c8000001401c2100046881c45980d02410150a242d580141a200104040d01a21581c040d4480c002d21044040340803421140c0500000700d050341d9550005400c4540d682c00c200c0c1014106851288962610b0000c003019550a1800c42c0000d00442c0301100c41c600e41d500010008000320041c0808254150006100d150041c030041082e41c48100800016100380007809403d604041c0080004030407445925911403200401402080d50185a0030b0400c2c1c82211101002500494044040c940c02224080603104030f00046103400d0030700300c6000d0036011340c0701e4044001c06441d451044407030154054600300c5101030006d20202e50398100c042c1d200c0342c41c1140880c0441080303020080401001422100860340207000d416241e00b41207001c3c04400311120044180300301008107802e107491b00740301c1100d044095541c40b940c10115103401400d944041e8000400c0041c1c41c41c01401503540d00034030302c1040076000c44100420445801259090041c586420015041040c103401300d07480000040d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 80846647 1250 80845397 80845433
    0x80c010605040617062a0a020106030c06020a08030f0601020313060309150b13050402040b090117010f0203010b030c0705070503030406051809010311090a0905030304030f02010b0301060503030f0a1407 88
    0x803002036100c13403100c0341c04401c4e00c0300307030810358855030101d25003140c841c0b000c0c0b10b04245903500ca08240b00c1080f40d40d207554807040c000c00040c0c1d520340c0104244041881500c0160100b440603203404903407526841084c1c003004d010109614001ca011492a03030007041250740c81100b80d030030001d00e42c5d07031440090000c0401e030006892410150001490690b940d00c65041d0600e8028144001403131303078581d841700500c13000b04101e0f00203aa8002172189652580e403907034020032800485402101d00401403500391441c5a000000340d03801440103000d04103043c029030b60f01c030800c41091a104c542c82c0c10301d030b454038034240c4c450780d014000001c1c00705045500c80001c10440380e080060800310341254003404840302007480040c0020355400c130758041c14980240d80365040700040d0004a100700f0036441d4142190b0085ea005c401084000c50080c0003d40c0a0141c540c20402c101c008111291070680801c3d00c0e440b804104a016200020f800c00d1102d004104c2040e2000136035a02603201c0301c241c0b410f4114404811012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 80847897 1250 80846647 80846651
    0x807030b0610030903090612020909011403120702010c02010c051516030b01110c060705160e040209090a03081906090207050a0302070f030305041202060409050405010f0e0706090e0603010207080c01060504 90
    0x824005002e8002c013604a54503644c1c0744055441d20314121506a004844014019000c006000c5680d0301c00341414041c090525081f112100a1b80400d071400e40340f0800304000402c107000360405030b0381103d0009649902820300c414100460310f0312504000d404941070703841160400500c2200070310040d0b4800c00c4620754400b04020b1444500540b54902c0100710055154402c5010550a04104000e030040d03612450403180160740218090484000c160070041b040e40948c02040258500341c10a660020104806405400c50030303140200745080c0280711200c085819116600e900d490b90703001c28010901c040086455030b500e0700c1c040b91506003010055005102c6c02c11701113100d11100650700110380c1e2684030a85454600041c0d0800c1300c40c160070030b90741b2090070b000004000307541340100f0b44618030030800004c01c800c401d440102120040102d61250303a200d0142402a01cad04580c140c0291046000118110340d80c100019002e071107030070002440c4240c00708860309018015004881030300d408a0301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 80849147 1250 80847897 80847919
    0x501020703030c020c2b051203040b060a0b030103021309020111070b03040c0906080a060b01020a120810080607020a021207210b06010305040f031d09130204060e070519090807030b06 80
    0x20000462442040f1920504801b882c000480c442c800e40406450300c500f080c1c840c9001171035446070050300125415292200c004040020340e20345000784401409030f84c030303034a803c0d9411038000c00eaa240c950f8120107c6140c1e80c1010a00f5a13004504003088102c20408543d002621004000c089800035502101c4100c0c80d40b0010800c407080f802504160f968510050100c1d0380301d070716184040c1102c800c0603810b40c0100001c040120340320078602c981001298495000038101143c01c0b480840701c0c0e5004c0d5a40d0340200082c81052540820581d81c800d030103c40e0101d4814001c2043da091000a911044040502d90382c0c8600e0b15195600540c84140120303402074842d982c000064068a404840080214105980d204002130090071000c103d40a910002080301008001198118105499500b07420300851401c40841c03900d40980c01c09000d8070070220300107050105029206010300312480c440880d601d4182c5001ca4403800000000704202c1b011180020380d00c2c10712060718102503940a0103980c15001d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 80850397 1250 80849147 80849149
    0x902070605090c0f06030a14100302011d01050a140f041203020f012a1b060f1a0d06020307020f06040605161e0806030703020409080c0d080907050603060105070501020703030c020c 79
    0x82c2e20307000d0f00c400703400365103008106000c00142e070f0700050020342841d40d070703003400c04a80c000c00d40414881d043d6408000e21581c00d50002408070031440c03058582c030002c190780301070b066640001a29120f80781c80c10091548058050341c0c2045020700c032a01490900c01003400105a000c00d00c50703031070f0507000e0340a440d801c00c280800719007030f9200702084060402d1003c0c1c05200d512002003030150311201500e044441c00d280c2a0303200d004070400501c16900661a02004c540616280c8280800c1c1c402e04c95030189600d08c035001003403181d07410310301c00340440f07501000044080d80248411448542e5100949025141c83c1c0303020001001c065505d0a1528814041011074a018a8030000c8881281082c00b0025400a504841a02008140b99094003e0900000c0140c945001d1042d00b03901c41c2da9401e13151a04816214500040761000320104603900003400550003000c105c050940b0300545245035641e403158016281d078400d010004000e0340c0300041d20820700d0b6041d8040410280d155080c0c44082d80814 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 80851647 1250 80850397 80850403
    0xf0e0906070507020103060816030209011d180712060e060709051c05010e07091a09040c1701140c0c0105060f06040e061207060203120105060f0706020a09050a090207060509 76
    0x9a5208459000d20041181d06000320042c1c81103910514010a40d80d44602d80c0354100030030f1a6101c80a6040e0020034000c5181410342d150140007103503260824840d840c910462013031409002026001031044055042d800d003030200101a00c00c03c501096400301390714111004005c84a4842554043d00001c01c0b24544078081107011200000d040e1040c152200d841c03444c3c842c00d065821903056689a20a079036012080c01804000c05100e000000e0035040c2d0458041d1200f810302c0795503c10000401000001440304c1524829201c904a066002100c1090790078010400040d0508141c1c031010100b0003003083d032500a140c800d51150080c00552506014005080d40200025601c06014402480728035016881150311030002040d02d05a418081c0d109401c050060b00300800503000058440600c03035090501c60f00519060700c0e00791406408804007400d81c0101d4500601c1250000b60802281b0312070103103800a803100034103004c03216549101c00b070000d500c23080d411075400e82840005840800c004c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 80852897 1250 80851647 80851651
    0x705070902180f0a08070803070309080a08030f1801020720030d08130302100f0605180103050d030c051308060106030f05040203030403260c010507200d1404030f0c0f0e 74
    0x488002d03422412030408104001440b80704160304006468000910354404009038002480c003403000d141d54039014100100b002107244c0007802e240c0c0c05407070b0201c00940c0b05400c903a1310401f006602c441c192540c500129000c3c000501c8c20b070447d8002705601d0300b403000c45030b407100014880c80c151450a8110700249525080b6a0304401c000c1480391002850406458010303182d624402e00c191041c00000080c5d410858800044040c1000d40c2d075041404141403600e44409400c80038030101c10f056245585450740c613039003030300c1d040304140d105d44c0380590850040c019600c49101506c5518001502c9410b2199102424420340c0002420040b04482c60802445040e00807134010340554030701421900d4884030010001044411040035024400411055002030f00100038000c00200d03143c1005000100b0030801080301c100c120201c03000170303c20608009102d12080301e441c02d0030010414400300e07406260055500140011585020507810081001c00c548280c40e01080ba0f998401c0d250941d407200340c0b400f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 80854147 1250 80852897 80852917
    0x106060f0f0f0c0311070f0b0315010219151d010e10020702010203070803060613030b0f1501080402040c05091315060507020105070602070f0f03030506100e0d02010e0d0b0c0705070902 81
    0x45425083c08a4440c00443c075007901a0000c992182c6d80e2604400d00f941103650280c412414080305003c1c01010003c11031901100c24070090405490741011003440040e5190010300c2d40c0751512003451190301c03941280300281034546990301c074030b4015140b0030f0281580790b00405041c091000c503420b54541508c00d407042d85406034001c40c180030081d40c400400351b01c00382c41150b1045090252001d0180c0e410580700c0078502c15003802c40c50707062104e002c0808040103055510894061810400c40b642c0c04201d540c0c2c850303011600490341c0c60301810151030601c0791141042d00517800701c2c1100340365100c5401c26040d0009920b486981d49951360340c03c4442e4040c00f00c00034009203007004003d01060b95a005002c510b03005560103290f880032075841041034010454202c020036111010040380b8030380542460146030903410801c6030444408000f90f401b4100c244024148141a503107051103407603400e56500b8803a442640c1070000d00b40b4421480c0030b40c01902c41120648510743c400320701042140251055007807 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 80855397 1250 80854147 80854157
    0x7030e030a0503090705150a030c0e011209030c08160b010e0f0414030d0912080a090c091113030605010f0f0f0b031e01060807030e01020304020904230106060f0f0f 72
    0xc0c000d6402c56290b40040c00c003003900d205442022901d5907c480c843c0111390542c2c1325095440c02d8510000c3d0650b03040110060510030404074014042e40c2040c904056048034010000340c200b0f40d0f02c0c066544038210700d00039001800110b80c50725480c1c04103014403082400780652424682c1d031201a0081a1011240c01d45000050030228000405087c0248151002c0b031007902e050241003500c00c0c0488803c0003085e501c0d40401da00c0c2002c050b800a6003039030001c800d03c0c0c2c14800400c1544500d1114003451142e09002d0769100c500f65030300c418280c290390307520a6101406007810340e01d0a104014080a00803001408035011700082e20100364040380701154668001c4110301ca1621001c614181c0004020601c1c1c600070101091001103180506406041151204105801e210707000a08451a94080406c0c580c410001e001c0569901ca0800b0303846507021904030000208034000009011a905147d000366003030130300c040b4030103410100200c52240140d0b80c0344410340c801e200440e1140d0501c110040414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 80856647 1250 80855397 80855407
    0x10f0605030316020319080d05010509040c0308091503040b0601090e0906070f0908061602010b04020a0210090606050a08010903030506100815040608030408010203180606060a030902150f0a0807030e03 88
    0x100f440403c407081d560004090301d08004448003400c85456098004465896000503001782c600071903c280750240006039401d0259150a03034910a021040780806060410003050500e0b5070791b00d2030a0400400082d20060340c890401e4908130601c1c2078207507175180c042108400003051518a0034001403117034055000030800c9465003d81544ca0038044030b00802002078018010403001001c005190140da82c400040c0da40e086803a50081c00c49030700b0080c2902ca0f900400c2030342e5603240d000605041d601454440011052060700e82070000b8541944510342003c1700072800140c0301410b6002c59002d9010380c60a00030f40d40c464041040314051018058086102c0002146001724040d19079600740d00c001c0c0002603c251a403203505d185400503030001240e40c0d000410001030946003a00040c4882507400182428241040060007a00660362000101540d50f00044295604c11241c4101485000704165607005e4a048031401035201d030a00b640401c0b1960041184648a07126080750b13001000d015500301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 80857897 1250 80856647 80856667
    0x3010e0411060a11070b030702071e030f03080103030e190303050702041103100f08030705030915041a04140915060903010902030f0c0a090c02060109090501020c011d010f06050303 79
    0x1190140c0107581503441c44001d800030341c991030000c06446541351103640d0302c4204400c0207840d05610750020407500509005021031281c00054680944044582800e07070b0000031480040b46064a90001c0c00a54510b9040c5003810b420165190580b4040c0d5030345402a06003009000791048400e1450380d603a00c160200b0030101303201e080a0101030348001e04c003044580200c070000c251600305650812924101c0082007090707591804031300c002042a10003441c180002529407546034003500d68218001c07182d40c1707415074000d280031003284c2c0603001c005c2c06261320744c03400700712030a281d08240545038120419040c0d003902840d060001d240302e46440404034018030304460912443d6048006416050341d212034280e001a41c0030311120461100c8400200348041c0c1c52000c103c03e4001541c08800403a107401e46083d15990302107240c2c1c0c152001c2c490023180c00b0416241031802442141c0c80050a0b5103007055107560018201003400351090280c00901514114950070012507809108443e41517004200e44480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 80859147 1250 80857897 80857919
    0x2224050f0703030c05070209100f05030f0d03091403040801020a08060303091f030908030a0b01030c05070b0402060a0c1e02030c120703020d060e0303010e09150610210608070801050c0f0301 83
    0x14034100b45c43c00d13901b00080c0341c2c00304411010580300c0d10301000680f0010711400a51501b00001488120010000907100080d0f55459800c080380c0c100070103032220385c001c081c400b02c1c044a070138030b42c6001c007103a5689507681d400174000e40044000c20005641000403525a00c0c0010559181c160000c005004841c0341260300402c402c00200800241a15800b01d0008100e4680c0998826031110760042041e111800004040358190342c84c3c1d4050000910514000caa144080c4641c1316505852656580c00c4500003546c004000342c000810a0001000040c1c03080c05840e1241c48071071096044442400ba072404006a00c5140c040200c01c40c1d02040c800c1015240050300010750600070b20700011a540402103040c00d641c026000f10b106c00c05040140301403450108180ca030041c0342c102c82c84219052500000d00305404600720201000710b41040700da0b00d200190740b071b0341034521f032983d040200c10398034011580c44d10300900c00d0071703400c1d4039103000200000200c80846d468400300c454040e256a08000085c40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 80860397 1250 80859147 80859161
    0x607051506010207091e14091902130216020111011e0b060904020301031211010207020609040504061b020a05060901020406050304021302040504060b1b01090302060604022224050f070303 82
    0x411032103003050002c0c3c1040030344907080c0350307500e960b0703030942c080028906a40c00c7c0c82d01d5903441c450103c885010451400320119401e0010307807201c41a0054080d160000070300b401d40362040e102e4030a00c001900c2003400003041c44c46150300c2c0b0030380f03030800c1d0382d008070800d00d088810f007940b041609015141c04680c00702059007d40d400c0c40d0300130510340c1018800c00100d012a0800d030011a90791411940c00007015806c1101190300c000500700a51401d80c0981c00702d6924040e9085490280740c03100082030030031013a03070458000c1040217200b8030600601040d0003940c3c3c000303211040d0303068028400810b100c500306000325803c1c0c03032071a1035032441c0d900c03036500b4480300d00713000301c4030b501250380c2400007090542d03a90203444002d001105025498411900d0200302412818034007100c142e250109100c0025000b00741f00d07501001c00c603001601e40781805164102c917400c0100f001549075400c10b0114400343e428480461490810000304c080c0e460b003a0050322988078220000702807950611400c80005e1281d00420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 80861647 1250 80860397 80860399
    0x5040b030a0602030403031d0102070818040b0d03050d0c110a1106040306060605070201140a0e010e0f090f04061503080708030a0f021b060a090807080a02010b100201050f060607051506 81
    0x28000310150b15204100c1e0016541100001c1c1c943c0180c00b405015601812180046d0f900214070381441666003282510403c54141500314683c0c030169407941d12580000241c00001e011801d0407140d6240041c000d900807249149040e00e08007125504030320502021070440b03848401400c1400c042d8564800216a05820603848003040001100103089401104010415512641d80b501c03088e00c00907200d00001500307c46480803d00c00c1020083e07002503500240300c0c080c00c0042d03255001d00701040d40414500d2103d90032200d0101844a02d25201814500c03e50090004100c55075008008202501c200d1002420491050000001050101c001590004031821b00024a03500d1072003000281d81100450700080b20000c0105500e2400c140107090303100030350003410402e4408559502c0400c2c058400081e00b0098082000e0540c1d034000d50005041680042418000c540700250090107402c0865009004030005000300d0703a239080c55420f84d0202d60b406405450ba500c1389507082e000c1c41e0707002403280e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 80862897 1250 80861647 80861653
    0x7081206281a130603060f0e04030806041109100c150506060304080a0207121b090b03030403140109081605012d050402010309120f0e030708030702010f030605090c03060f010206040c05040b03 84
    0x703c940c4100c2c8440c900070140754030089920b51426009281c1d180165020100e10b0550303030300f00000641d2102c80a540120112740019040c1a02c41209c0700a000b50b400301c94106541e015039229484d080904440401d11900349401b18440800028068030380076100150003003c1030000c500040c1c1020301030030000f1918411604810f07071300c21081444c0c40001c00c0582c1c102c031245140c1e048035007840300c03080007034083c00c0303003e014142c84000481e660740706038400900144c402c3c0f14001046002034005060481c1c0118145840e07041a829904c40e41c05040c004075599031a000040e809074507014039002c0c0c00e8100407a00140030340400001006003c1c0113208904045d51162840e00013001c239105a100ca50450b81c90343c14401d180c000142500d400c5c0e40303101d0701c25480000300b005124000022602c0e1203a0a10b042e118001c2108030580241c02c03079402560348026101d04000c000c1001c48051403081c4001c03200c8003500c3c0840d800590701c4500503a0003601000303542d0428044c508140d0032401a6900141c21 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 80864147 1250 80862897 80862907
    0x18060f0605071505070918050402030706050a05120a020901020f0f06130f050604060506041401050f22050a0209010f17160e040e0303041106030106120b040207081206281a 75
    0x180c0301200c1c2c081780e01d400032600001e82800405c1e4402d0030124140818107041005041540029580c0c0b101c40c892907080040c000383c1c1c0924540304101f9501b030220240700395203560038502000d502a4000780c00781030052080c100c0392034000000103502d80e0400c180301c000d000103803555084403c2558007441d064034130341c40180d4220300151040180c0c621403401000002400e007891000c00050310f04640e00014070540c888018002607513403a2000c24080c10031104024442c403001c034500c06600540c18040c1d811441c04c4100314004101d43c00601109400b41d0314540d48401140c8140d402c01080407115025900300b0313000980f580c00030a90000950b00c28100103c00f04003510005080e01c101030f051900035080802030000f084800a02600500b400316515400c540c1080d01c020a040840d0618000043d11780b03019840b01d450741e81c1225104c5821003100d59455414810100c498102598913502038601010110500d9200c40160f9030401b0034040032801c82ca00c1c01d506504d00c00c00c00f0310040a0014100a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 80865397 1250 80864147 80864183
    0xb03070306051002060f060a05090a0b040905160513060b03040f050709020d140f07080a0902180108030a020c01030203070e1e0a151b0b01091508120418060f060507 72
    0x81e40b2018904182c4c0100301ca0300e8160000c140d0104003410303182c010040c42d0f00901c820b541d600d0002d0360003480094001046001100080c0281c0441a000b4256000e200200ca076820060103106041d03d50642c1c0d075150b40d803c0c01c03603600100d4400d441030b00584170060020030001081e07080032241d030f00e014000711141183c4880703002c1c04030b80c030400d0329140e2959030708030004000821070001da034800c00e1412a03c01515103401d0144c45c40d5401031030305900c182e40b0160300045543d241c500c081507801a0b0a11050703981c40e84100c6940358001e04076140548030384a1303100b403250312a000f202e22a905036692440c0c01c1011b507040c401c0310242c00344440341c0400e0040c071304211612000b103020000c0200401e0a66030105188000d0b054007080c144c91040c5100003200030700880e0408100780e04490b0009400078084040314802d00d002c44880c0c108280c14010203001407008051176000c0e00c103450601c0010030b900704084010744101e80841c804e4415100b180313171081100502170000340c8140e900075558030300390f00c02c42c2c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 80866647 1250 80865397 80865409
    0x903210c060e0309120607020c0d0501020408070b0315030a12030903030b04180b0a06030b04020906010507020d05030406032f0a1e030f0b0405250201020f19020c010203070305040b0307030605 84
    0x2581502c4540c804a4941d40034600843c08076007030601c1e00050070003410700e0b0f80c0003900d503041e00d9001406051240c3e4080c041210950448004040034002d40e41c42d0b0b07841e1600d41c1146e51041e01e1110746903003c4d420031b5002d0b1401154007500d55502c40702004440c402090190b01406c0031400030b4042c541c0e6107601c5400d80d100c5010300b141d2103027004c10f030300c0500d02e051800c0031803400090141390500340b0340041400014480041e031a0095012180040c3da55070f8500101d034548504100203403c203071a100c20b40100080000503000fa07800a4509104030001d0004641d030540147c2c010300d0981c440840b94081883c2410000c0041c03490300d00c1c02d000b4810102c1c03809003c4541c405c00f00070001b40d840c0d0b148903a01c0c5071482800310400d0101d4050001e030814a03604c002000954007004c0142c0ca2602010400ca4001d41c120340d881410024400d03121044600c900b400c80840c0c840341005809424040070356584088101d4001302c0d03068a4550406086c84a41038058200800380018169540740108460f5203038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 80867897 1250 80866647 80866661
    0x6080609030301030c150c020607020a05030a030c050d051e210108030c0d030209030c013b0306090c240409090506071d0609060d020d0507020a05010c0903210c06 71
    0x40310045a8951544ca46090321001c40e83c84a110710440d08a00d00310300b580180300800c42501126040e8484481d0b00004500e035065900c1a61b040c89601041e50130142c020008507495406901a80c0500071000300c00d5074148102c03228003410300000c2d82c45055002244003d0500c10104e03001d1070103100b8180d00d81e085c820500b80c1142d08503a002003094441000c0810400700400842e02d0190709203c01c0b000440d41c0d840006120506001880190462616034030220b00128076003106818025090030102801010390103142500030301983e400100784403000a028481c001d0060320940482c40c207101500700aa1707100c24a0103000c0c004010008240d150746c09005c0141b401800070781020300380750001a1111800d007402e220b00341390440169815a0340c040540d2200751040c0c4030242c0d101039810a0000a01c1a0391040c40c64618000c103001c20158001903d07417441e07120314020020388001000a8079890090b100c01000700c3c02804c260210f1880c8010540500300310b508201c11440c1d0142e440340195014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 80869147 1250 80867897 80867911
    0x1506010507150e070b0d1a060901030c0e040c0c03031506080610021011040e0603060606030a0b06161109011e0306092f030c090103080406050c0307060e0105190b0901050f0103060806 80
    0x1000c100094241d006d0f103d084021000100c103802e6114021011640700c0c00751058007410300d03544421400c00180181500a83c84100030b1007084556008000600300c24418082503000034502030010111000f0900c10380c055510945500c0d031141d5980e8200118500c03a040ea150460182c008161124440d50042c4031344107014001d50b82d183ca060000b020900c11b001040d0508c01d501450501017507480d00780450b90403003030041c0040341d80d6800001082540c070510700d4889480f40707403020201c284801000c080711000000c8900d078005ea640c0b44a504032100780c010214000c62444003040000900720303400040303000c3c40b580404841350004000d50300e00c40300070742d0070401c42458981010030918062080d0503020104580550555040d9154034829000385c0c040c803009e211002594100d03441040060303e151300d91105091000e0281400868080c3c00e00340c640d07105150070806075082555180c043d80c03258500c09040030301241c1c0f800c420044420040103135213040c07503900ca4011443c610184400c07482460 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 80870397 1250 80869147 80869169
    0x40308070309050f0d021302090a031b060f08011406090f04050a0e0d0c05031207020f0303101503020412030815060a03060503100501051503041b060206091506010507150e07 76
    0x200d04420304c88140d815150441c861000b10031a10010703a11110000f1115170b11040040e110300410000c600c5908403a04040c20b2545503800408110065030036a0302a50b45564480c0c0f8812140c00c4242d03101d10080c082c13901500390180390a0a6820007074080e11514a00a00c54400c0d000010b0215045074070035241905020317181c9140c2141a00300300a200003c050505c0c1252903103449807030380c545a00a00340d8501c100450b84002c40d50044c800c0021805007804032007625624100816006501d2906100c0c808402e0100e120030000b11f4003e1003900d0448480c200c049004185568040310300040c010661000440e50680e191081c0d140c503005052140d0701ca407000690141404c00300761500c42c4000c0d43d8405075040c6801481151160604182441400c1494a0b220707104d42c80c01071698903810b0604081c061032401e000400550005410340030b103e02200366001001d04106150343c92904603401404a0310402ca454001060300415800031107a03080001080c100100300d440c10b040c1c00f03a20410240c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 80871647 1250 80870397 80870399
    0x2180a03050309040c1d040f060801020c070f080c130b010c050d180f12020607080712030501061808070611010b09040305070b090303070801050409060e150a0f150504020a05040308070309 82
    0x20a05120700f1101c030f6100d0629181421912031714102000c41200e21b0760046846001e40500311085421410140c00040029900c41c2400e0b80303c40c3c2d695000b40724015400407040f20010348910042800025035a01401c22101c4039081c401c10700151800c2d099040c1008400201c0c4008500207202006105846603201d0100409045120101c10040d80180e2058080d00c142000a8202c13015030b910f0840e4140d980540710b80b49420180c0e407034080d01c2d0002c0e0008040c0d0f80002d0304241c1c035a21a5041c1c1341952140c130802d41a010500b107103044a8040c43d00380364404c207014402c40f4000e08401d20f0801070740380085081c0b803461012034034a035800d540403004540045000800c101c4209481907010310010011811442d1289004090490620841c0d01944c1c1e5512160b0511103e500310800c1d00401000315403900032200008085c2a0084841c086c0346464454016941003060190700240c0c080d845a8001c16401e143c1000000e501481820301072000030040040028903a4029103e018000d4641c45d442e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 80872897 1250 80871647 80871649
    0xf060509010609020910080606130308090103060602011e0b0a080a05030d06080a0b040209060103020d0207030e09100501090308030606040314070519080a060e0c1509030c01020f060103030302180a03050309 90
    0x50b88460b08640c00c524014040d00e04952170701402258800340d10314014807140c0781c90003c01c0962103102210466002c1408010040c04000c50052459100070f03601000309590b9108202d00b203405842c840764100e01c8a0411714018206908090001d00303006000440440c0d075003542d41d2030440c500c00219810f40002c2000210340c4a688580c0004109a10141880207801d07070f211108050003c00080c85001e03420041110f0381d1299040c1c480c0503c550104650300d8005003005030403403003824609845100d031007000030b07041c4404030325800031528184c4404140d182150b584816a410042000c0c0d0031180511000000c1100817003a0215640710b1005048007134106028020303a885542034580105151180410002e04000b814942c1181c00450004641100103415820701c0550b00403140e1103e02c0050811603041e004004140c500d00c101c046881d80000c0790300680c1c0712008100849100d401020042020038001d400416401101d10507001e0300184220014221085681042e070301c661000c02c03503001da = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 80874147 1250 80872897 80872901
    0x106060c030503070f050f0715050a0e0a0b04050c0325080604170a030603050f2406090601110a050105040b010312021c05090103090203010c050c1006080d0e030a0f06050901 76
    0xa8115840c1024420301a610040c0452102400e5101081008032012101a1283c4160b82e01070180c694811381c0d41a50b820b140900000c0301000b00c0c4c1c1c643c5008081054504980f045c8400582c0f4140900380e500c50b5a1a00314035950300030030640d16805110301400159800740491308240c500103060b421120895000b04502d103200e46c2004400782e101c1018800420081151544c0c1d0100040210b0b83d2852461002c501900c400e52004000f44208114846d525001181480505810844a101503030300003294050b100340030381c1d4007900f06000301d01051070740d44201e070f445091080e030b081228103040007640c803a821900119425036400c0050740051041060151a28070285003034401410030b26041d40d0720440ca40e4000c0804004e0100002c0c401d026039001c1c0d0421500d10750020020400c5880c1c07008098826071110b942101203000d0000301c03a500d05114410602a07070f02d050020000c03041180700030b8403003c0c4400c0d0b40b42e0749441a148410000396505485040032442403601240c0c1d41886522642 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 80875397 1250 80874147 80874149
    0x120f01150e01050414130f0b030115030c03020405100f060203040302100e01080708060a031b0807150912020409061b1211030402060d15030305120f0c09041a0616050106 74
    0xc001c0742031651481e503a44441510182e554810b1005215140c400003d108060800c21411080782400d0045504103901c3d80061003641c2c041d8028003004004103840308480c9118000103003c502841003e00241c00c090340159448041d11602514160712001c4e1043e0b48202d0360b10000040e88001014001c500340183d10054404507400c0c000c81c0c0070a1480081d0181d0f1004240300c1c2003165010018645030f42e080004d000650704040306a0026280c1d03032628550418a008075146071140010010b0300e400310311fa1442c0c00c0c800550361450420300b4405a0030141c2c0d00240260b901584801100022031010701c5400d070403103840f01400000c00b1000c80c0241c1440b0380c8198050f010380c50700d4009100d076482c99088070380c0a9412510b03165907904040f00c0714014422101c1020007175010803404010560010010001644184103010b8141e84d80c40d04581840c00841e8000a1b0b0242444130800905154000500c403001513452540707442090804603299030094400b02c1c1c404a402c01009017400001e2041c80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 80876647 1250 80875397 80875439
    0x8071202011409031c05270a05090f0f040501090b0109050a0e030406021203040804090c021011090a2c071701091127180a15081002070305120f01 64
    0x383c1800b40000c006911760b2050542007002c0002c400362014801c0c420b404448000d51292240042e48407090203003150002c0070010350303004d6031418901103510b1030301100252007500181b0181409503070700400710300c2050003e001150712303640346c2088900194204280c4ca0103098a82000189850401c1401c0d040d1011300b0800c41c038542080209220055001c00c0e12281c0c8001120416030720303210b601d0700302c0c0c55100e168000030070135113800811540503a0115181d115540790140603c400c0c1c010281e806400c3c4201c414a40c1c0c0060f04d000b040011744844000d02580000458143c0c030080c0480a0040e04424120380d020001004c03507060b4420000310795000381c05040b8040c0d0800ca89810301d04050380501c183e00d511000000120790f0000c61b210821030a4a4854001d007a0201c00552031046001150f0183c4007010410300f056030f81000394548404a030b0032a171642c40100342105e40e05440700025400844141c0400004000b44a11700c800b44410358065081110151803540c500107014070f1061100d0800c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 80877897 1250 80876647 80876687
    0x9051501090f0b0a0e060a03090212060601090e07030e1b0118050f010c08040305070e1015020715020102040b1b070602031222120c030905120303040b0604060807120201 74
    0x40c007400d00c1142c010020350702c00248090355407243e218240c8031881005d0310540c1c03000c40010302d41c00c4168590006103003140b007070b11041c04080909492944881044070000c0c002035404404001584071035181c5500b12503203080004403e2301d5495000c4c141001801d56540b08120850555103550f440a4000c2007440743d108491460380c01c050018a40c03c1d40070390314130f04001c50b507001c0f04144940781045800031603100d412176064542c2d91540b9840901c007250003440100c02184006107504000b9406402809036502a2240c1418448c0c01d5220408540040741150741c280b1010602401803c01428140d03c5a03100d000804081d00c60f075840c2000b1500300d202150801d000f0540005804414a07800c02e0708091500260b134404810f424513485000c05c003170309014981120f00030040c5c01240c01001a8000c0e41c621060989603021700080041e40c445480b42c1d5401080010041402210010f401c5240200701054103aa42c800c01843d111040c2c200a1f00201c804000108541e0006441c04c10469181e02d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 80879147 1250 80877897 80877899
    0xa0308060402130504150e0403020706120506091902221502030903280602070b06090906071b0501110703211109010e0103090206030a0f0f090203061317040905150109 73
    0x8601403d2416118043c0503c0e15118464641e0540000e60b0014007420030340b40426140c5418020759030a02c0b0304c80c21020456080040d84e50020500906201d05400f90060655480e0f1001c502c4412841d00c02c140d514035402d0061100f5181e8800d408403c170749200564000003804c10760510146480060384c0d10a56004001c2060291030209000048030341240c000e08080038525141940155801700090981c1e100080f0901040b18040d50580940400e036103000d096628141556690503094440c078010624460006a410000d03076414040607110f007001044070702c450150041c058216803002c50209005908a040d0080388001e09100303100d1521092245001100c46002075106510400e1b04000b03140e0b51212159000317401504903294081c3c482641da1628646e03490051026034462480b0302d040c000d02d4480c0789418010284815001030250072141c89940c55948060041c4104030b54840c0c0840e03552015040c4200507000070720f289040441c40e46000c0c0a91b011144454043c42d0612681d000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 80880397 1250 80879147 80879167
    0x9040e03031b030405010e010518010c02060907091d150402011e050405010c050312010609090606020a02060d090218070801030c0605030702070311030a080705010e070506071e1e03020a0308060402 86
    0x603140307210b40d0a01820503500c0d111400d0060143c101181060455800c060902074808540c4110a04400c5d100c4000c101a402007402240c80340f030240c441d4103042d44991001e01207049154004141c1c2034440034080442d001a000c424180355540301151041311401e410007040d0750b000408060381020000c41d04046460141000d000341c0a0382c0503e0781004500511402081010401c4442c050442c0e500c115081d80e45170001042e001d4280182c102c0d80c0c0c00c2020015100340001161003040364000d20b014100180e010700e041c001e0600440a981c0030401c0c051540c90320a040025500603909070741d4440d143c0d0304608100516924661001b41000001c000f0001000d03408103030803003a284c1c050620900f0307100d0b190010f86448080f400140500200051440030014154009058005000261007120f540d4004204041c0512503000e4104c95a0114071301d042c01c2e05002c0520f986108084111050000e01c01c0031541071980c0700300b00c0260b130145140e6400d00d42c0001949a109004640541c035107074a4803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 80881647 1250 80880397 80880421
    0x11040504050f012d09090b071107060806061608030c030a0b010509010f03150506121014031207051009110103050109111602060705120d050604060608060f0d02030f0309040e0303 78
    0x86002d0031400c203207244046410013101d12620003032844040900c04040141170958080c5070580d0072401042054441500e20200031070741c8003c4036107544501050f07030790301d10a121659201d0421a02040500540c0000280c50840070b075001d05600c3c44100e480c0d140040500c811146003103545414040c05000c02540361ba40142002a08a80d61030302040c41030035200340d074594006a81003241c0c000b00102e110380b81814440b01c00c070312039075220540f1942c107503407840907040e050564408240c064001d11620051120540b00503e2000e1140c001c40e4910010750a10408591103440c0031561058bd0002c118200c1d030f494002c0074050044080100640080e40f41909854829140c429244d0142002e4041c250745d100d5003620a96a00b050503984680000400c40d1225417040d05984880c43c602004035006007414407810781900c080c0d0b181c1894540300e01c0104503c00000141d015030209070400d0584c01a1014020001c0c4200346100441d1680104001c0205981c40900100d03000e81c8140700b04446070040d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 80882897 1250 80881647 80881679
    0x30c1002040b0f0d090501110c10050f040b040312090609031706010917030403170408071208030403030216060e0c010e12030306041806020720041a1e0411040504050f01 74
    0x20410655aa1300e020b51004082c14030701501802651030a1900d002003030103440145101402c0d00195448900c0b40c0c03105a00705c0c0e80075560310740c03035100d060b002400051010035880d8100d40642891004201101080801c4c0c0b020340c4d40880760683c1f18a0442d04240d0032200e544c4280d103149411100f0740c50700d40c00017444015070f44100b076081c1e5038a01020107801c90500468020b95013040104901c2ca034580c409104039440351090348120f00c200d0700300140c0d04245031035095400b640b080000f4a1a2103948044019401c039860018200502d0b1200100055152244c14003072450752016104080304000090400711442d0b1209021f1541c841c0200b02510010003282e5014404031030002e0480400800609440b1484d0b000404480c80020140b0901120840c10382d20310000f0700c07500c66401142c00c2030005441d00380c240b0382c070402400d01e1a40304500e000142240c4801000000c19141c280010008082e1190300e0031005030100c000400380700500342070017070f0343c0d22404940294441d07524020130420030801c0c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 80884147 1250 80882897 80882917
    0x1003150c080412050d0f02030103050c030a0f080703030605061c0b030c03150406060b040305070e010605070b040609050c060f040807080706050d02220602032101050d020108040602120702030c1002040b 88
    0x307080c2c00c0e103d481c0030354142c1d450b15141400c1004802500c8030800d00a601c02c1c04151079600c03c01c5404060b9180c005954518a544180d5844c4006000c0c0c0d20300381540c019460031070030305440b224041707040d0b00c81302c007c3c0c02034050090300303010703013669400d5203504450407a00b455000740c00c034020f1480140c50010304808200240403600c81c1d256598140340c4d00920481d0050185241d0020f000000d1010018600003642c00316251a42180d070b8070700007030b5154070800d00f0060202c00c0c1e0b41d0008000c030303a4131f5003c042c2841c0a18150b50240d400440007803c16885500039401481c40880e052010741c0d41040004017031304044008100c01410f19402800500498050480c0c0b907400140700603a00c42c91710003000d800038501b00c4100c2d800c0d4680d240651a600122078524a05409020f001002181070758102d0403200c028026040d001120b03001184d00c01e40027041034480701c3d02046560240b0103245261449401d040d40610380366000314081da420078100c0c107000c0a0041c018801400841b0420f000c031003107000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 80885397 1250 80884147 80884163
    0x222a020705060c01110c0d14040608190906021605010b030601050d1212020a030204030302160b03060103020c0f03040f05010f020724021f06051203190f05070b1003150c0804 76
    0x82c4643c21409012449a078485e4140c0118040340391241c00180da0407250880d407102e18400600b01441c07545401680300d00300c001032031040030540c03170801030540c40449a0f1032000401e050045480301c41c01c0e0f91000402ea0854010480b1020134400c007031150b808001821005450654500f80010326032800d00c0e8000f901c2640e01140c84800030707028038100d03d19080c2c1902c0035900c0f0301e0f030204094021b400901c0180e025000318402c41203246441200c50083d2410740358010700396254800114025084100d41000511030b401042d52501c0040014000030101d45642d00d22803414000010141d0236a8000b4030301395408400184191441984580121a0304100c0d4038120f09110b6170132803418a5400c2181030328090500d1070006a0000d0704180c0c20740f14107441d03c042040c5201300755070380da10840c12421043c40140c00b22621192044c0307c03450001c00a40b81450604025803540e00749403c0980e240c40c1134100408040040001500000031040304025042103031140d81034001d021030400a2001300041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 80886647 1250 80885397 80885407
    0xc0f0907080711062403010203040317070c140105061206040b01050108040f0210170907031109040f1a0403020606060c0c01111c0c02031b0d03030209222a02070506 72
    0x40e1103001e45400001d800400c941d60703400c015070354020030448007601c3c05041d98175843c40b41c000d080500803203020301e0b0300d40c0e00d20110161b100d0a4540000c0007130600300c1000301e103060917404214060120340c04c1c2d1400b0070000440b41089400c0111607420740c0e00b218201d07007080c0100030110b1590448241110701c2800c00c10569511454100003804c0c01110095000e001202010403581e03118044c0141c441071000c00410780e40303500d00010341e01c1115110050502d031a03064010b016041020034503400c588144014124006266180ca0240c0c0d444c0b46406400c0100c07508000c14150304200e640d0308054159011031070022148003141d25030660310385050511240c00e410b188807160400242da1801e4004045c4c0b204510481e9004041031500c0100307900c0b034400c54442500010780d1884900140708005c1c0003407000311403581c094010f5000081c07415404214000580882e1810305080301100004e5800092445c0d00c14074a00c081100038115201484041002d10001c96000a0481c050f01c00496116440d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 80887897 1250 80886647 80886661
    0x2010c1202071703070b06030c060a20030f0c1011070206031506030a0c020c10050406110c030a0609061b05040506160f0803010609090c05040306020714060403110c0f090708 76
    0x80071155120500e000f40b03c00002c01107003000f2001c1d1801c0ca00c6a10101d4558031200c04140d42ea980015105a000d0010048200440d010b03840340354a0390804d101100008208603429420341d0400001010200c1000420460f1084203100100744001d075032600300b1480f1072038840761145005155009010314000070100c1c000c1c40310403e504400c0800205425961b1030407071708000140c01d075024400050300c56440080f0003464180d6000007024003a654140c107003458904204c0c0d0205072201b034545035016211200700340340c80c14061078441600404011814856500d000c804681415580c2081c00790128480b1354155409400c403002c07140201d5000d600c5100b8100e102c0a00e007042000201071502c3c00b4100002c005501028504035091601c40d41d1603d40e9a1440720f0555608103007890001d03400304010300005040ea0b01800541b401804041c2a50000000300b62614074151000d80205003c0d158030000c0301410040c0c0009440c090740c0310300303a0202c5140414410080503007401c0900c66400002032032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 80889147 1250 80887897 80887903
    0x90d081306060305030918060603160c06050f010e010603150b0d0f02071203150e0c0a051b1c02010b0906120109020306070c0201181203031a0a090b090a060302010c1202 74
    0x1503004072042020030358034a0665601d07841071301c50381e003e5260b0560055400d1244030181e0b20440c1d020300001d1441d035611408416014580c3c3c10b800c10710104003120001310382a0f11030540300d00c603055414400365041c8120004210070580c808020181803001103642d60340b000701c440701101c1805500c5a16655050003240240c045039400001e07075440480d241d8103100044030320300500d00c0c1c252410002450f280107071124000150180d09070308403248000c60344880c4488010481100c251a00c00d00701004610b004407a000e41e910030907595440802c2190071643e030580c10340c3d550b00050008002004250010407158000244a54429610f064a4520840b0b0030340001000310b6008094074210710b0700003000740c1400da140405a00003260f840c10700100c04040c0d80c1460a450001100700c0041c070796036404401409035510711403807240806010300c1841d21042c0542e03000e02400140481c070361440000f840f9608800a1024070213a080420401c0541d030010050f465a541019501c500600f030b60b44240d00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 80890397 1250 80889147 80889181
    0x3260d0507031121010605070b240a0602060403090905150114041a030f0c0304030905090702210909240111030f07030e0f011706040b0307030503030c070302060906090d08 75
    0x240b40100040701d00f0014003203050612082604c5226020301e90300c50303a00303c0d8180264400100341c8400803011660903142004c6905140011400c0441c031403400002003526940c05600c204056405003040c4804c254000702c803030010b40f101403010011840c16400604c060184946502c1c144a0b8010b404031400314076408560107480d500a11500c400343d41410300407154011200358522445440201e0421650b8008607401685c2541d10f402080b8100000c00205000241c1420103506c541c408100541d04018260800300b902c002407039458584802c04d100c22003000034a01c000f8007200d211326100c81006c015a4014210080c60b1031446411590025451446240880d00d00031102140490816034021240d80d402c000c00e85003034200720a520010754849000c4022603407480329050006010b41000d0f0f012040c20100102101c0d5a00c0d0340c0d403205070559109a5148826040c002019811725404020417070b0044420001010545083c0d0035071a00c500c204e041e050304000080c1d003c6006008814078443c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 80891647 1250 80890397 80890421
    0x19050409050d0f030e280203010e0d200d0e060409050a05150303091005030a02040302090903070201110609030a2d0c11010203070b01030204050a09050a030903260d050703 75
    0x1001000e039007840e60380c80c00c5072480c900002c0d41481000100d6486802000794040b444c0000b0f040010f0504072141c501100c420f421030072510401c2ca41d83c0982d50034021184e03441c4136440540045492140c0c010090070080350956940300c1c2e002c260b25030280b00018070402c04440e83c40e080050148403000541284107a03070081904a051409202c0c2e040f40581c003407402041d0640d030540f141014030040c941c0764000d82202c1076004a0a80c0c04a07a0240108004d44e40311016031001403400ba1658000307201ca84003503803004902d5001086000440d60000e80501c5a14944402404d4910308000c41031f540307100f40307108001000101c040c1c40e504d030108400011500904c0303503190701084c04605030090100c0301400081c1c807007500e00c4801c68080c0d40040101d60085400026140c0581e080d5000d01c40900005440c0b0103100c0c0c0e036400c1c1c0e000843d100b4842190300e0361090380d912030120300d103040010207a28003030744212854030344008070800480c4910450707044400795480802d6030740c0d45e1070054005000c03c049507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 80892897 1250 80891647 80891651
    0x109080a0305090d0305091902010513030302030304060f020c0304140406090911030106060e0d291e070201020306010c0b1015020f07120206090d1115042111190504 72
    0x40104590560400c1e0f1042d1101c03030032140c4880449200b00c2c160b03003040d5a1041607802840d03a0169401c0c680c1c40b500d21960040c1851403405125071014981c1c1107199200b540160004010f210030041c441c09601e042c0c2180e0b00c01542810704043c810364680c440d611801130364114011540c405c0e504c554001c00c00801860100b048240104e050202d294000c44144500c203520300000811254019621584c40f02c0d4050010a055070050b6540c2d00e50b10060480d14540c4c6a008a8208029018070001481411200801c00440e020303580383d041e22010280018043d0790061007040718a036400100c00c0030312034001041355420b80303c00e5542c400c2e50129800030b90700040701d240d1445445d81c00062a40e50300340013408176415a03a03200e4141d0040915081d00a50060f400c02001c41c5500d01041c04c82c07003050044010a89040d0340400040d00e8500411314180c9612003c0b4080200c5002c003404e00108100074051650001c5480c1e40c1c81030100d284030703542882440b000300d480c4a005840481440600409801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 80894147 1250 80892897 80892907
    0x30c01210216060b04050114100210020a02010c02070824150d0b1e100501050309030d020703030b01030506011d060a050403050a05070e1b07061806090609030306060e0d0803060102010908 82
    0x401c07a402c0c80c0c00403058903c9402c00c030b081105418240706144c100c0e003c1e09400803107455140c08101d03142031101f1504085210310000c1006100541c0b005240300c4881d500005681149040041d040c0840c652140004da080300342c250798921144080d4102480e2512841880303035981c445030031100d000000401d6001013045e8059410043c0005101d4040c8003003015004404441e51904005072b402140c00941c01c9240c04000c011035402417000d0341d00039041c10142c0742449000f5211300b08a800c43c0d0b13019000641c86070440191540c0610806403c00c1c400e2a103d0b070090300c54030f16403521002d400d08150060310000f6224040510403000c1d1005161b100064445d9404141001d1703513102c070240a0050b0110021021820b1040119591842e0200300c0581c00d04141e8113840c0c100050030300720160402d1030f4860f40c2160000300340d486070743c812610504000612003403900f001021140f0b40d4005605000c205503004940d0f42d103602200a0b0b10750312031380c01c41e81c0c0c0d51348000407405020310610052a022003c90 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 80895397 1250 80894147 80894167
    0x40c031406010e09070308180d140d0f0e061605070504060b070c08010605092215020705010b0f0315060d060203090718020a050703030507020726100902030c012102 72
    0x4403581211a5074419042c25102c2e005480c2d16800188001402c061042002c5400041c034552100212100140444007000e03a548070404070030400301d002b1096811035017800c0d101540040c610071074006645003106103541440c0208035148559002c4203061072800b84850f080003000c00080016000150080c0405d03075032032151044503040001e0458030760a88010105507414144115400c48070002c005061360b460340d1640c00088400d901208180400d41c100f0320012462142c1c42c0c5195540c0c07040e00507628106030802508490f50311002e58821010001d131180c5654000032034402070003900c0d40440040d11030000080d8602c45210000b0a000e0001c010840640c4000c6100b008a80400c1c8198180795020400f600c124030580d00d110002c10000e2100e00b01080c82580625844002030040341c4820791100424051301c0c00d08030601c1c09104030a03001d2003c02800b4055034441b0201030b482801b8040003580081c0c2c4810281d10001e0400c1403142c482ca11030541c100c162110350301011011550354400b05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 80896647 1250 80895397 80895403
    0x1030b13150c0c050c06181302040f031416060905060d06050306131704030209040609021c0602090a080a0803010618090c050304020a0e040209010308091201240807030c0905040c0314 80
    0xc43c02d98041c080c2d03030340c0840301c0d00340343d4101d5010403a5070b8902c0f4182a02c0104009030f039811494400200c0c0d60034403000c40c4c03000304138a2500245000322444141e9842c12001340d0310b8544040d40005404001c21020411640c001c084c03001515001c03290ba03034440e100902850020412035014036410320840042c04010b107108503004200b54016400c00350b00311040821601544254400290040310307c00014020030304030350260380711030b00c0142403528030401d0a0091280d101070110039564203a00144042ca41d10342888000e0050507100098101e6111030389484200b408144035810a10010f03000c0700c1c1d00c0280b2205141d01402061108104840340c14500611a030400c0350202d00540d1055000b05000d0001a44c0390301c07590340103042d850300781e013141d5803400d00342c01944d20f081c4c005000907052140c6041c00e003d40d50250200007945958122600052141042c0c0b83d8460803a82c1c008032001d001007a4000b4154080c0e0710038280102e85034503286040f0f1000d0000e548003803c044090b003540c036440007000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 80897897 1250 80896647 80896667
    0x1d060702210d1803020d020103020f03040b01090c0e210106080a0f0506070804051c1b06090b0f060d17040b040308030a2a03180215030415020301030b13150c 69
    0x10314110ba0449030018001e4503640c18602ca510001c0344030f24401c00062510035260015988180b4002d8200102c034800700070207402c240e904491600007180188400d0400d1b10079075454090a03d0400728403012100072518060400228a1b0f00c1104200e80b5903982038250082401810b00c8012280c4904040c00c1070f18240c8403550301110706018030008280c4d00c0c2e11506100340a10782000107040c10b01c4d84103078486198000040503400b44030314512030311400c84000103642061401050702007a40304c450300c1e1046100c88000d0040d60b07501289020301c03110703403564010056026442855101c680c030451104000d42d0091f45d01400c0e00d0400040c0100411001501944c015071462109220103c030302e03038544416a06460080c2e40d0340c2940303050450703014442c4e00200d2071181c54400d00f0b0800316040d00450070030178005c04008802e000c00424070040240c0200500ba0140144000b1070842d4190390b0703004c072103043c050164510030301c100e0b1f4100c0c180218040440c0700c82041c840c0070425029040700c00340124902e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 80899147 1250 80897897 80897959
    0x20a0b0a030e0c01120504150203010f0e090303010617040501110f090103050f0c0a120b040c02010510060903050a02210d030516050319020f0d05010f03020f0f011d060702 75
    0x200030086804000008030700d030343d202058481c0e50a602e41040504001c010050042e6224500d17800c0c5000001228401503002c0c08a64689000d2035080c00c843c081c0124014010302c0603981308200411071a54000840e808801d02c1d1516901c1988035820054050880c00f040704840c480d00007040024004007000400340e010003030301c05100c00d584042c10460052401c84540b0001b1404200c00c022042c46801c0c1c10500c0c0725001c0d4002500d51717480003c18126100c1040c0080503070342d50b20501c10818400a080c40003032045140c2001c1203030941d9941d98440b458040001d010b000707548041c1a5116040c0384816060071440c04588040007250802406450155401383c02602402d1000704400d02c0380003140d203e02d07000825030004280503080d580095021039000701141e013040c0218507940c040e81c004c5d907002745100e43c110348145056004100c8068211400350740f20b00e0010088100c10b0741c02c010890040f42241402d04aa40807020104415108001c4029032092464004581c40c4022108004c5400300c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 80900397 1250 80899147 80899151
    0x7031101110d0e010c0f05090d0c0f090b0d080403030f140c0c0901080c030601031202070b040f0e06010e0d0f03030e01090308180307050a1202010906020301090e0c01050430020a0b0a03 81
    0x81e80c43d0b081400c03100076000b214002220b5041e00881903018000a103030b0104003814107122812680c80e003102520580d08541480c00d02c000c4200062000c034002c507500f10707800716958581c0341007a564003404c9214a102c01800c0c0f21410a10b1030001c0c2c0a12181102c0c45868024140d9807170041ca0210b40f03a00440f050300e845140818004101c5a03000078050000c00ca010f001010107900710789a0030006424040181c0441c800d150012403805141805031004100910304180400e0514840460708180100340e14104014030105001c01e42ea203c034401481600045001c400808509040300908020092002c0d55800c10303a50000701980469440c0c800c0c0e440528800c0c801268030070403900c0303202c1c02c41c000d06140d01c4606102c0209a0400f4090190181170000003070081c2d541e941d1200340d030001da201c1520695030301501e00c0141002e011100c1c4440092820f07074686800c242208c045100500c0440c0407a84042200010120343e244220450a80007404462040c0c0d4a182e8520164452a600c03070006e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 80901647 1250 80900397 80900411
    0x50a0501140c0f03092d21030a02180604230a050312030702010212040b01081e06070c020409080706060618050108070c0501090f05030406260402040207031101110d 72
    0xe10400c07086000d09201d441080c43c00c401c0e0150b05030603800141c05411a801945e484445480d000e0480f10204502c0c2603110b10b440e001d9995407030a00059044a0b48050b640e03e103a042c490700d0180449a204c00c8030040140c540192004084403120015501d03900b09000007004900510214014910104200040d1201d150785400f40444003e0f2485203e400d5800280810006c680310400766a20074034520006080c0703c3c00e02c8480300303004001da4080e200c100200300140001310301030007400e041d11070000c00342d005108450a196540c520041609040203918801c4400315501c40d00080c5500f6045450143c131041d81c3d06114000309810b10800d400300c0d08018455500816880c03d8008850307058503450500d03910100b0903600726a040d0320031599550703030303000c01c10000c0c1e90082640001402580210340320b47c01d0000160000090003800c00464000c030b10340302d56050100038942e600c1681950050303100c2c5510715040d9495070a075881460103508084a400f5500315910180c007018041c40d10a208070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 80902897 1250 80901647 80901671
    0x1b0b0403050324130b190f140102030901231b0c0108070f02030d020d0e030c060a050a06080604080702030703080c0a030906080708070309050705040c02010209040b150301180612050a0501 82
    0x500c0f80040f802d50000341800250400400e90391003841c00c00800b92003048900d00f0b01d82003640042d01030300206458003000340240000050401e020311100b10a000652828030010000703000f458200c03c8503810800c40e00c41c41c400040404080c0d9610f010b2410203c24070200d82c00b1000d44801e80d43d1146400101c030100010030803403055550300c441c543e090300070b1891322110043d1000a03611070082c8030749140e00c0e4200044014420002841d06503049070240900e41407156402041c0c91018107500c80160410b01c00380480701002c502c483e00694488041036495001e803011a04024a9034400381c42ea81001c16201040c51000c942c00903010310a94807840c0c91620b40d0810361381c5003403d80c0d0520010b1030340c400051071280240e00c00c19546015800b1107610666070000103050707a07200240c903c0144d40120711504c19041c14098030085110882d540c1d4008456501d100e42c0f180070512800302c01c0155100704502030f4046a104401521114683c001c50800a00f07260756240d0300d40c0000c0760f40d50310b4410134242d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 80904147 1250 80902897 80902951
    0x5030f0f040b1b0715020903101a0f0f10081602031801030b130203010b0a0801140d080a090503011107051b010f030b060c0a1b06090b0306011b0b04030503 68
    0x481c1c1e50203103000c400c60316002a0445444004264484620010494400030800040004011a030191005aa00c1c610141414205a90480b1020700c4a00b012404009811003d9040403d40380540f021000c58041034001240881c0507100d0540011140700380104165218004034400c000c07800d00c941103d00c8101040340d0700d1141d103440034581343c8100d1003a00c040d031003070704841d580d203c0003030400402028a0420700101d0307200788d00480c4074000004108c240c10760460400c03801000101103a0070f18102402c080380c05a10001402017034110000380c0356038414010782e00c90025200190003000884202c910440440e405a281170750580304030350001200d0b039501b00070030a2500341a5a12224200100e805170b001d4012211416070050050003d000d20b03234020890040a0343c001e020100034690707944a40221b50b10303d6001a0b04003e60100c01b8011058042c04030b0740c011304203280c16400640c5641810300f082003640f05c0106404c1c5908144403d05030b00502541c09082c01c60081000c038881300c000c085e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 80905397 1250 80904147 80904151
    0x7020904050a05060c13030209090307060c051801210213030f0c03031106101403010603051006090b01050304110910080f0c01020d0c020a050d1410020a030b0a0501200c060a05030f0f 80
    0x101b003028841c000e00c01414840020b0b6040708660f0112403c000c0303a6a99a81900d031454840d9000413004207540c2010b13803580000d070440c3c500a08140e100d50408141840f0014010700070509030310340005c0c8640b88040c1c040d800c1c80003140c01a0044c0c54190062411598a801a210a1f000112186448120303a1030205105000d03c11a8000005640c40c084010820044000003540e065681700000808160280020200c0700d4a55400240305030406400900701d88100d4009810480c0520420001035895071021510078401c0f00c002c0c04c1951002d1000d1000b02503908885650b014074841180000400103440301070300400d0f001c3e100361054454040f1480c00140201039400f11b40d1200400c9541054262102030b41e004441401c41601403800842c40c0000216815441070f9002500100c40d9502d4032134060480d00131a2030305c00700d40c40e14000034400580080c071110202c007140e0045140501c100008410f01c00c01402054582c3c0d41d11401822540048805820310000d200014105902c1603021074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 80906647 1250 80905397 80905417
    0x70905010b09010f030b040903020a21021510050d030c03030605040e0d141b070801050702071a2d09040e010203040302030a0c03111219030608101107020904050a05060c 74
    0x250500341c88400440c4c4281e01c1d40030780c0050540c4c5086800d8582c075039019101c400d600a130010403c0d4081c500d480c503606000d214258150202c80c148084d451039000c0396000b401202600c00384640c0d111184200806030143d8400d944c403109443c40c40041640020702050706500944042108903590780038031040d1400d255040304250081010383d02613134080c45100841c49030140003a8108400528422420300315007192440380d84c8014070800150f42d0034001c1e20340c01615031000e04025407038034820305184a11014510091007000c0365540b10b407110004400c03802c004c141030412503142075500285265012181d00c502407810714042441c0c000b414000c0300e000e182e15600841c075080020004540300d00c4066800c60402c5490038a00450480402c01220b0342c640c0c9400f003c1d61100c6458840404812401400042c1410030008000e80c0c0300114907508040280113001c1991001c500821010b4810900c000b07500c42c440909100c1030102c00542c500070548140c040705c0c002d0b00d40b010800c5850181540c0d10b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 80907897 1250 80906647 80906669
    0x6060f090a0f020903120405280b1c060e010501110a0b130213020c0d030501090915111608070c1a070f02010302040b0a0c020a0b0408100e070314010b010207090501 72
    0x1007030090750164440941c1c0d0768075240041c00c001844000a0603c2c2c030510700784895400110f0b041c0082e2030b003e1138410100304d15003e0764049804581842d102c200d0907104174801880085001c1a50740700750f40840700918000e000810885844290300b101c0d4150038010140091114420005004c0001550540396904980140a00d94562229a11501121008907004140ca50f00420001c14a0000c0c0081c070f102c0001600c0300489203d0003d00720703241644440c00ca10706180002006c56030b0b04140d00078012002e480421207600404102200f885215041d116521400140d00305000100c0702414000c0c0c03050400000322552200d1800c0c070b9a18800d40060011410040301c1c000070b402034024510144181000350410742e075507082d0442a0060342500b0089044088090114a1301c44011005010042d802500309820455900d0b40c48598505c04400c507651040310445511041003024011070b8080141c003034500000d010705020b4001c81c24007601600c614400032402518900416042c0c445601c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 80909147 1250 80907897 80907901
    0x50306090705070b0406050601031a09060d0501060503240f010e15010201060b180a061b020d020a0b0403030504090e0109031e090506040b04060207080a03021504050c0307060306060206060f09 84
    0x10004220005080c100511100f0416600003800600040d80f00714000c2e00001018600f0000240c00c1c0c42c2400c0c641030320003001403900031351599617010700c5130008010b85078114120300b28031f062401041c0c990002c90341f43c410441c0d6410925400700c1d04040021900d0020b01035034948000c000c244000a004d02c080e15800080040c62840340c0c9a003206500700144008036030b0540c0d99200c0545a4070441c2d203440e2000d07420141d02000e0030491114402000307a071400003000c035031321150701080d440d503020005d01c2015031203802020343d501c070069080640389665081c1da5480d968940902168440e01c03403540854100400c583d400e540621a030000c0a40503242c00c0910074150035000318420065800109101c0d0803217020510343c41d988040c00180802000703242d44c079801c002010f8500038080d80149034a42c00a10400c1c0001c4c0e0220b100401c121114410500544540c0340044c2006800c0ba6901e8147c030034800000740269140d000780040328420303003d03585ca07903c8a0062110790710804140ea50450700502c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 80910397 1250 80909147 80909149
    0x10091b03030c03050f1306050901020d02060103050624060417190203030d0c170405030406020c030703111210020f0315010c12050f040b0d0507080c070b1b071505010f0503070303050306 81
    0x100a00300710845c101502d15020340000181c0c01504103801c071500141c004070b50700d100d0b035804004a0380e1000d514002020103600d1035441a40d9034070005c212030080c0d08540044460501000d26201c80c05030002c004545540c0c60f10031000304c1c0510b42d000c065203032290107954010b0f4850413004e01040d680181c091450411310848100c05810100b00d0344040012085130b0b030103035070503120b5176500551041c809180d0703030703403070004028903002400c0d41240c03082c0c20000f82000000d004509503683c6800c00d50b20115004280091030b804c0c44070b842050f0302c001d800040c0caa000c0c01ca40c0c2c4003d61284010302c00c000c940c0420302c0d00440b0000300d0052700404034044070b8a11907500d0f00500161080d40c416008245c5403070f07180c5000c40d0281d00031005400403103448030700340301c209600302940c541d001e55440d040b541080182e03200d0402e490320250001c0000c00100280940558200c4125042e1076005010b000c154074070301c800c0000a100034400e11808030341c00c0c2404216480c002c106541201d4150391501d085854140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 80911647 1250 80910397 80910407
    0xa111602040b060705010c08090f07140d031b080306040c0302070506151207060c060b0102010209012001060f03050c12030a020717100c090e06030706120903030b0310091b03030c03 79
    0x80605030380a50241325110024034240034089192000303544a20942c10700400e82d61801c01500d501d00c07607a420148040c4603401c0003e00d4146583d0080310301c90030441483c20290344c08803804040f14048038110f60305c5024401c951000714000c1400307850802040440304012402c03801143d80051440c0c11003404200d1503041265190b50031000281042d14100d164a00d036468104198090000f00e80400398400030302910348507901c01c441080c0000d500e01120b81000070079000803419881402140401d54002c080002d5001e079016052280e0428482512030500d07aa5990403207128900c200180c2d1118411418003200303545041126400900f80c5a040001c0305034280c440c104241d40074854803e90340f00c00d0019004e00a24040c0c1c5403504080c903800c003105c0b50300c0e04074000c0545020358840f810070000a61f010240460540b07080c0d400040c0b04041d03107411005000002040c540c5841211040500d180d09030b486a4410342c400c00c0328440c0708040c2010303901c280074030744000703000304078400d0181010a000e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 80912897 1250 80911647 80911661
    0x6110309060313050c04051905130203060103030c0302010e1e010b01090b1801020f010c1e05090307060f031b08060406140901060f0c050303040c0f090e070611010212010306050a11160204 82
    0x134070540d5010408000402d0454104444c0d080000f9400c4c80b044101c001d035803007200d40060741500c41e6200412242c011965882c0180b100030308011004200364141032007903101050240300c0c4410340d41301d1540e1010254500c14061030881255203030100340c030030540c0101c01003000c0320607030400302c4d05154501c2003d1600460640190303041d40600010840c05040c28421442a803007a030700d0325144102100074503801c01c08009000310601204222401903607030009003030b5040307500710314003110f40035010b440c128054080c1403142002d188101480481c0c1e603411507000b5206034801c3d13500300100f80e5038000c0003010b076000c400c03307907040580b900c0180f008501c1012044a1010141007040180c2d001d691050b1442d0300c2120192140c0300810f100740b01c1021100e042100906003100705100f00854958003907103406c0c041c031600007400816106526400360030b4054074220181c1040240710b56035a42080c4001d820100c1e541114940b034501002c4454a04800b0b0720703c040780d00c540e001000260382c2e00f808000d04030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 80914147 1250 80912897 80912903
    0xc0c07030b01180b151809130b010e040b060409060612031211040f03020f010201090b0f04060f09030e041d0a030e040b030307050706030908120103140d0509030d080a0e06010e0106110309060313 85
    0x41d00140d150306c4d465003000310b8001c0c1d80520103028001c4403420300100517001038001d440704400c00420700c0040f81106d51a260130480c11034000500103402c0ca40f00c0001c1845500560300c2c020312548810a158000091500e2096200d000744012500504040d200f0b1082d8016801c3c4900365080a01c0541064104c01181c4001800005411682902c3c1c0c1c0a40081c11a02316411001c59400c2008100160142c0d40d4089038101c81402010840d030f80250002c8095071550307006070754400745041ca10000c3e1325200880c41503501940d40340040c906000f031031601030081c814090f500345403c90040e0f050000840701c1c901e401501800076a0b0a000d021009410b0900d000e45452106208413405035061460071f90003940304040c44249000ba4560f03450500718a8003101c130603c4014451140745d80c9021890080031040c5140043c1c480d520313103604000403d080481040141f02d01c2d400440e40c02c01401c04141640c481d80c66070701a4482e241e082903038038030621501c20f8020300103001052407841c55040c140d0100348 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 80915397 1250 80914147 80914177
    0x30e030405150c07050612180a0b07030f0509062a041e15090f09021605013308100506040b09100513020c03040302090c0c07030b01180b15 61
    0x29865001500070540c0100b4084090800035040c1004041080303100c0080509070b60560524290002c51a04110014011f05040354a000c520390100c10900401c8105a031000111444e414039550090082040e1145442403070b02c0c00022410142d80064098414910300317943d40c101610045c0c0450409e00c480000f4108010280000f10f180b81c994004100340a0000205452080c58a04510300f86c0f80301c82e00110600c10004d0080c010b81c07100080798001c0c0d90500c48003507528440d216500000a42c82040038001d0351030610307115003c103180f200c2611360804502c0c14510000c00541c100500c0c64140c4580c903080d5100c00c046074040c0c4d2261308007550002005000082810740c09020035942e6008031544241901500c50510179860005c1c0c803551000500300045041181010006a5904c030f54000030f032050702030b0400282160191021602c8082001090740c0320035503285080b9034444402e02030000f400030444400c68000c0c54905c203006482e07030010000000c9220003101c4d440a0350007003e400710541 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 80916647 1250 80915397 80915399
    0x10050136081f0609090203250b0c0105010608010506030f0708040f0203011407020708030906030a09082206080f07020d0c0c080d0c020414130303050606090d030c060510050a0303030e0304 82
    0x25505005190400b90b04551100b400d0300359840e00c01c1194042e4120401e030929060190700541c400150395000c00c041c49810701036a00000070701210f500d00c03680c03044000007400039071851600010340115040702e4240d12143d8a0380d0f2507600f00005404100d03440441071841b580021607a5100e00503c0e508103000e004890006071542d0042825141110b185508041c81c5030144025654100305220007008441c002c0c50504010400080701444064404107081c4c2c4c6400400e018000312004440a1061212028500c502410031150b803009803407140c1c4001c1004000055940191445102e104640e554003a00c5d08403003065003964411200c5105a422026504005c0341030f5004005c4204114815201c2c164402028030404c006e07a080080d03810355010b4500c042c0301001403d1101c03192000d51604001c44c2130350362000400d08074003071101400d034040d107084509018183c1001c0c0f20040d25025510900c200c0c0d0b00c0010321411100288144d40d04400f649104001080c4a540595440f0300700400b03681c581 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 80917897 1250 80916647 80916659
    0xa050d02011e0f0908180a08160303050f1909080d0903111e040c030605030f03181309080a030c180608011503020408150601020d020105091905010902100810050136 72
    0x15084444030501d06000034075006c0c2c1c18a401e811070381c01002e219006016104041c89441c04140d1140700081c140000468880d11221040c4295100203240d00c00c175805214101200400449041c81040c1160141c03130300d02d4086603c00c000000a59070441d005190b4018041d0500648002c11340740100c4d2a00c0c04c130103241303d540e1240100710780d2000d1507030f01041a40c141070415003400021440c10b800e030b03441000f140014514034119682d810400321a9803050703c5a10030b041001e0040540020026907002400c105415010742c0448000d2101d5540d14080e886000d051201e0280c03103004840110b001c0c080100807a5a244800c250400c2c1c00d0320300542407540d01d201c950716001d40018102003403003440003045080e5a04124281c0d00143c188028800b60401140315511403040d02c4080c002d5010a02c484014048250007114007581e0151800710b200010b03420003031083c102907a460400074640c2e100054691f101d0886011044d5200b2100300091481a020300e0342c0c0301030320844480c000100e031800505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 80919147 1250 80917897 80917913
    0x70609060504060506030f060412030c2001050f070e010210110f0304050f1504030c02010c03050f0a02070302040c050f0412050c12030a02060a1109040e0304050a080a050d02011e0f09 80
    0x82d03118000c00301c0c0c1800c00303404050602241c4003407030200342d115808000114290920a00c800c42103810000307481c0c80c0c800c4048400341c6103080c15942410001c04004204e10056200c83e124004120003c0c0311615216000c6507409803040140b40141d01107200b100080720030385c0c4504250603050003070603c1c0c1060204000a1a0002c80d0152a0f40e00003c0305c0805081d13050044031001c103541d100451035440c0c1a9006400e420070708501a040182240c1214101030180f0200c40e25059941500c90301ca400c0003038029918100d50108900660424a4074054107000e001503c00103960150407a0070113041c070103243c081481105040d04c0511458001030b43ca81c958600c840c1c0e503421000d01550361104202000303440d200c070150480084929000201662104000076100c120900300c6000c2500e40c64407603554614095900a41da114000941c00283d00600003041e2200501c2001540c003100010342e020b90807980c2200e8101608510700705d00251141142e0300c40000d010035150000b410340b1494646000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 80920397 1250 80919147 80919151
    0x3031207030e1e0706030204080d050901021906090c0b030c040902070203030d05090a060501050d08030112060b030609030403032003030601050f0c1914010606120b030c0306040c030b01080a03050f0706090605 91
    0x468118148840d100303d00c0502403080070300302c20704043d031038685003016840d80e8800d00b40b410300400002186402e0303668400d0014403005103842011869075001410a00003d1500907401c4840f082c0b04a000601c1842890550380f0441c003004000d41420310700341d00d0501079482140c007242e15020030020080f01034960f2007150f010380600d800801c070003480740ca0074004452040e041103202358105440c190001d1242c0080380c0c1552403114107503842014500d0400064812040f003103a144c0648410004800740004c00341c0700700d80c02030703550941d2450300f00c0c03105100011010501d08141c1003040042e00c194018001089400203c06103146000701d01c0742818203200703640c10741307900e0540d21064110900080d80f05039600e602c0182c00070400d030b518104015103040d4502c11248481c42d100c50b1040940c2c0c2d030900039004100005016958145818a020f90f0000d046000880e602d803039100010030350010020b17244c505203030705407149803130701c44566901500c17a00008011140141c907030710700c4000215140600d42c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 80921647 1250 80920397 80920423
    0x8040302060d0e071202060f0f07060e0c0117010e0c030c0d0c2c030c0411040e0c1908011d181b01030f0b0d0602070c0b030403020703020f06040503031207030e 70
    0x103020460303d030805080042680c001c0924443e810b00700800b50f41c03040c0441c1e070082552581207680e00c03030511440380c10380a444400f8040d00d140c0b60380880d00c0b07040407507c0c1e001c0003801d985250601d28148601d4006000a0052180484c0c9181c00501d08118020003160000106261035041040401c50141621949803405001842404c003600030481003c05080c0c1d000146004c0c403030340d2031140010954a00601d200103200d25141c40446240d2403644007160090501c4a010f60784500d0140d550005a50088030850401a0b52407004081140708110a5050382c1020646503042c06005c107410703110b02d00c080c081c90b156086032a0500504d400401501c00400d00c80348220700d8522840c4c0c005000c852110003040910750810845464640c0c0d140d00c00c00c4c450394040c00058682416040c0300f24140f68542110090401c0001804141500080d9000859202b11035481055800c0028082140501e1050316010b5105100d45a11007505280541c2e204605103400100c0c071080c464400d240140d035800c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 80922897 1250 80921647 80921651
    0x7020a021201060602100e21130308180a0807060c05010209180a05090601060f030e03070b07050c010b0f09070c02030a050d1206050301060317070804030605010e1510020303011208040302060d 84
    0x8014464040c041c100b44e1b018211010002d415115040c20f07111070b41c0300c011201d10208903503000e91801039030b81910710801165440303050b455242e2602c00c01c2d946c04400c2c0400c41c440c400080751003034549110250107907207244002c1d0809a141140c01e07280c40c00c040b0003c4400355003d02c5400082c1d182d020341580e01300d14ac8051030b45c203410084c00e0f420445001034586022034201c20b005100c40c070f0b00020001682c5401c0d203400a20709002070230321415030054650090038514528140b04521f40c2c0140684038452884008108201c21441003284a80481805640003503030400040c40d11400380c0815a81c1d80d0002e402c1c0c9a010000c2e544d074a045c86403101401d40030440e8101c0308880160302d80700c3c5e5009000250002c21000e420354840600c403821008656120010004006080007207030001d4400840d1300c00014807095031101c60540004404403001600f04001c0341b038030b54252400c09215040048550081c501d1a400d080003c86c0410040d94180c850380c80c10080000140c8889000300348000d512500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 80924147 1250 80922897 80922899
    0x20d06091a01051c05030415051c0209010804020d02040b0d081b060f01031218090615020c090402090604020403050a08040302010f02160b0901091511060703150e07020a02120106 78
    0x40540341d1a80041e60748544441d490041c482c2c0d0b1203105403281a990343d80c3c0c18900002c40351800d03500c0c0d0b1045070003100d54031030140781900105411801800189403128180b00300030403101a41c0b0220700601e00c0e005e000860802c04940941018240c205c020350001e80041900c3e100080868048104a8000c442000c00000c0c5a100c0500e80e00c102c5644000c4603001d05591b0400c29014083d002c0c2c10700001d000301080c080c004a405000300f0140e045000110b201e144000e50b80c4031103078020300103841204080e9000c4100040c1880c03010070040080030f001001020151126000c1c004661001030100d03401560800000c0003040040080c816401e206011455503241184001442c6400d041a8034055502c4180400345001400b04040b0599628015007500c40041e0710040715040e00990099800301b044240a0b69030310343c000d60b02c214030040d1508882040d10b0f070650423801c488586010010075103450380e0502030080b40010160b0000d18920489160000a4000404040305c0d1007c5a05036951280 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 80925397 1250 80924147 80924153
    0x71a0c070f200411250c03030c0501110a020604030f03020f0f0c07090c020a060903021f05040c05010f02100509160f06030c0e0105070b06030a060606030c090506090312070609020d0609 81
    0x60394440350328040e20b0901c040c034801424078455000d1100b0303d1070044141d00c8104004001d05c00c0c841c1c0e9190b040405104265500d040c027502c2e503140300105551030b500340300c2d8100191500381c0440d064450642d000308a590f489031000c032100314801d00c007441010b408001600036034031984060821b001035402080e98491441804602d002140d9200039510760815220240b52030700031510304a07642d04207401050700c2d9400c2c80d0032420411014100360400348c2e214502c10354040103600240c420f0b48255100e00c4281d44540040d610091003659520059100055044041e1695048150440d010004442090300c404040740504d4006402a051720303c513010b003c1240582c180503505140e00a4140340c00070784480e60000b0700d18031400c4009040441202c0c0420b42e1a10b081008c9a000d40c1c01200800071107031581d500801801d4070406040010b84c1c070030303008580380c50f085088442c26140100208000c9403251040c1305160407810f01586c9255803560301d2009a10364001407106c0b540700d14000110003205103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 80926647 1250 80925397 80925443
    0x702150c0f10060602071a13180c2115081b0114090f060c10150f08070e160c080a120f090f02010e030c13150803071a0c070f 55
    0x3400040c141c2d03080010070004190085102000d0ba09004040e50342441100510300c1940b0481504044101c40400005240c01030b01c101c10701c039003113001814040c84880c40000c440e4204940d8011095a00c0e00100040030405584000c007089411814000859507a00c610341c1486070728518140031040c0130001140350340c1e105052a60200c1c5050340a418021000c020a88507000105514050040054182400132040000240618040005000b0202b00c1840d059104040b4405c01024003100c0d80041022640070940c0750590b422241c07440c0300741c1d0341e1200301c03007084180035910014090700c00a01c00124001c9001041c081409403100350703032000594400d6040f921552624403842d031038025168001089080302c032007103540920301201411400360009090242241200da070102d41c1c0201e80c0b19441158004501c01640b085400c0c251a0340d035990561207102d10100103100d10850800407802c0050384000c44d0708000168401410422503580314985041005015079a40a0a0200c58500900c00b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 80927897 1250 80926647 80926663
    0x3040506010f0803030c0d0e060709260c1e1207060215070215061302041409060d020303030a1e0c08090c0a060509040504021206130302060a0203040b0103080702150c0f 74
    0x1c0140c0d1400b80c0d240c0002544c4a00002c2c00e81c0d41c1000c40042c44040d001c00b00c0d00b194403004500d00c1034503841e00700048090701c80c4001e84201c40d054152140100034040780071250703109651041000e030902c2160401005410402265a105100c007450104411911150058000400d6034002060040c0c1450006403800020318906850502480200319010303501007209e515580303040110a805440707142c002003035203101030a00940c0ca440407400044660344d00303240c0402c00800f66180100c17600d81400b0300c08405156880650554030409c082540501c80b41c1c07102910805401d180c18040d000c0c008040b040d83d44502c0d03a41c000500078000c1c41a090307020b01068040000448404000c140743c2078024007540501c8041a200301d507500002011340d1652001c1690500c0d50030281d4071585002246c84c0401400d604090f00103104413000508061401d10840c0d000d242c020402c0a240da18680e60f130707455580900800ca800006100050f90007640034000f80a9601d1001c2c003803c4030241e2000e0680ca00144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 80929147 1250 80927897 80927909
    0x305070605250309140105131a0c070b130f030903030f0c120302090301020d1d0607030b0901090c031b0e101806110307081c05010b0909070f020c03120304050601 71
    0x603008101e0408115001c0560380080b107042c0441c140c0b4107030400300c022003a0300e0003004c0e65500b08020001800d905032500c44002c1d00c901c21406840c9142e25035004101d0b01121080201407080048101241500c254550b1080d01c030542100440d0302543c9a104404103c4022400715803084401e0040540000014900400d24980b0350110310554a80b010b982c0d148020080c280344d40000c225016032400e4040b41c000540302c3c0f80c10302480c000007100d0b0382c108001d03441d1030985000310000726400303510900541c800001c0080040005900749150328000b030a40f515060141035946615482c550031460030070f66031419507202c00d10841034030401d00ca014450380c4003150812000b0ba045007040040c1041e103805482440c9401021101022805440c503c160040605800701c04113110103a11009002e41c00c3c21802400240150b990b5040c40b03a140d0700491006a81c000f0a500004483e40d200d8030240e544c40a251040302c0307416010700080390030180f00709204c180c0d010303001003040b0500208000e8a030040c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 80930397 1250 80929147 80929171
    0x20306041406030a150902190602011d071520010504020103050106030908030a0c0e0d08040504060626070e04020403030806030105070905010903170f0c06041a010b090909030c01090305070605 84
    0x90300c04000fa84400400790010040364410f014001400003540c403040c80e107a0302400080424064004103030b0790008a20170701c0019030800c0c6a030300c81000c00c3c4003070949100640e0700821003181400c00b03101c00c140190001101700004d040845101d100c903500d000b000e40300c011303000081d9814140001001e075803058004d003051504000c0c90b40001003400b000c403075010104100c0010358880050701202c00b80304001c40f09034860401b00781310050014850042c403c80c2d20072101000000d031f84d15401e541741c1406100e003032160003a4207030100740030303884a9007191700ca8007626054484c455114001002c9070000c0d003082d400144407504001c8513007024824250080c07114100845801d29004c0020996001c3e40002406503041c0d0308000250801039041d0f401c211880440c0c02d450312900040940d4031181200d094440411844940f000260744440040c140d81e1501c405070711342034000051262083c0080d00f0031126220401c503040a143c0284514031006104c1e0f0703105682e4210500b801d405842000d460707034600d82 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 80931647 1250 80930397 80930401
    0x2071103010c0201050c160f02030a1208070f090308160c09061e0803030c0a02010b31060e0a0207021201020d0b1905010503070e0414100807140a060c021c060203060414 74
    0x1004c040c103542e1141c2c0d124075107c07603115183c80c0003510f1035124107000350148641503e9908025112800b007801c110503950315101a96219400c54008018210034004191820400e0010034080001880401c0ca10341c1c000c8902c1406a5071550505010340c08801c40740e644d480700b441951087d00034100c00c0100ca5a4045a036030501e46056207034400589100c800000000da92402c090007074221810f5150001c100e1703514458220601c80d11000c1602950390399180c1007401011000061290f001036500d1200d003031402c0d0f0340d01d140740c10095111f407100f0baa2003441412604d0310750509000410009546070804641352110710103020324130704030760240d0700b2481001c01c0900c25640e110b010369900998a24003018051801f00c082070042170b06041c0d0382080803180c03041105807040341d01400110741c0e100c000c80700340b50745e034039001c241203002000c000354040c140010800c056886040e12403125030004020040c64805120b40321420783d0403003400c6075800e40100c00c100039450640700c0c005081490490140c164 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 80932897 1250 80931647 80931661
    0x5091e031b01021905090319060501030b010e07020703030e12070b09010e0307060503060603041e05010c110c0102070509090f15010f05040501060c0f0507080706021f06031e110402071103010c020105 87
    0xb104c04010f82001c0060114004603265410080c501c140403403100161240c0009083c10700281200340002d0303607805a002c3c00040d48401c200c00c030078814403550b8041c1c85d50a09555040700e01c202160f440c0b40d40007440000c0d0900010b400d04c5441d0041400c8062691b0b641d81c540005003002050008191083c0c022040c200302041d000310490354407000843c2c009a413641d45103032112180d00d100030b0812115807050100400c000c81540704000301555a01c03011202c0e54200c290903a60341c484e407017403030068002001c100200d0030000e268a8201010702c040d209002c5070848003e15118110741c913945ca801040c40100041d401651005002d0b19007502d09000940c10030364003924401000c0d400402e018034441010382407150500400d00940621416501d0301c65844030000c0d920480602c0f01c0b141d921042208040d0442d99202d0078044a0748604080400c0940c4c43e07490700300b403c5101c0255000000116107140954403480148501c5114071400076003048490140342c01c40307207059801d006681c1b408007031280c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 80934147 1250 80932897 80932927
    0x151503030c100b0d1a0a0b041109040e01020d0203040507030b10060801060f14040609030b01050301020703021c09030501050f01090c030c020316060f02070807120507030e010305091e031b0102 84
    0x340d20741003004500001c0f09400700302d01c3d1107841000b07806819005d000340b1181e5010003100d070081000c0241840070034030340000c20045411280d810311980004001000e41801e15801c5903c0d0511210001410003101985c24400c0e42d20441e01200e06070007050b02803081220350b000710358101e000100e03215205410a48080c01c2480b0600030341051082800b00c0e0741603144104c1b200c440e01140f03d00425122960b81c1006802d00416020071500e412400c0000304242c1014402d580034160546c0c014154145d054100408001d0800340c09400c00c00e07040c0b004008aa824010746005251591125000758075115040c0211503400e8400420141003d5036180a03990001c20b0b100040700c041c035a2042c0388500e04d449001070036542d800801c5d150001c1a500c05000d5003002400c80c1c80d004031080d041c200103031503086410f07100c3d60400030f0106100d05165611b039440381d406560b0010100048481d007001a000e91807208840044044070790740002034407050040110708401060750088029800e0241710001103003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 80935253 1106 80934147 80934163
    0x30a0606050355050c0f0d0209011406070c080d090e0106020d081005030118020a081b10020c060d020405010e0d030806040903030e151503030c 63
    0x2d00c0311041c0d81c96185001d0112001c407940f001d01c0c03c0380350041890030201c0f090014040c640c041151603402106256a014000510f4514a8001000007038541c80c80c0007401740f80100c49140050701c845002c141590410aa100a0b0801c2a00420b5907030043c810081c2115002c0c130800204110085603030612100b06580310400d032521628003069511080c410710f001640440440f8440c107104243c100d401c440c0c0c445800190f1640c03003000a0a45094009a4500d4400350040340114500440c2c0c0c400100380a00241404050480740e40106080086641f4001c404e0b1156144c1500d2003442594151400140540c3c0c543d100319030250001e401601545000c075825103003850303044c0fa000d910903c000d540b41e6aa1031842c5d50f00010301024003c000d03c101c047c543c80e1001c079003d0500900c2854015a040b800d210030300e01e4200040b980b941150310b007444c00303030300300300003030036030f030580410040e07 = true := by decide +kernel

theorem cover : BRFrame.Cov 80755397 80935253 := by
  have h0 := BRFrame.cov_init 80755397
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80755397 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 80755397 ≤ n) (h2 : n < 80935253) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
