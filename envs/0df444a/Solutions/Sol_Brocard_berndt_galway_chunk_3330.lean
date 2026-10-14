-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3330
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:20:53.443591+00:00
-- url     : https://prove2.me/submissions/dad9b969-5ca7-4cc6-8745-dcf90a248d21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 598741007 ≤ n < 598920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 598742257 1250 598741007 598741069
    0x30e06041e05070803180a0311040f0e06040609021e061903060e040c08160518070e040f060509070f05040611074b09050402060d021215 60
    0x1108010801448592a040240002c90420000c2d0307405000b012008598400422050000b40320742103441901c07070f540595040c03001400c403400b13401c40301e070f03081d02c0c003141c0711010204803806001900c40e03000c0c40c1d200d0042008280f154540162064500a45550107406000741c030303c020601010700e0880c0c03c440100036046259661420320100d0840519001071a140c681c03100804520b0251003e40307540800040500000b0401d03c00030541025003158060514034160200740360f0001e490f0303c0313411402c071080018079041c006c181030940402e00800c100b050750002600300c0004c01083c00340340d006559041c000f540c8240518600d01c6216200c4d11014141440c1c00c030b04944400d500342c2c00f45542e000e86040019111082c1079088040000310307040d000300788034401d2800740d42c420000961400e54104240403024501c251035003c1a40c0031842c0206141d030f41c50010400611882c02080c040310301c0000e1113081c0c0d003d1410101c0c02181005528000701054070304110314040e0710f00301001c410b00c0c030046024134 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 598743507 1250 598742257 598742273
    0x506090108180a080703020601080d0905120c0907030603060e0102041a13032301051003111005120114090108010504022d0a0608090c0406030c030305030414120405010f030e0604 78
    0x21101d4622035605000340e0702070b0814100303110040101d032401d801280d075104140d0180001ca01600651000b002030907009840145000258130425018901e10504041c00c003406008840300e4034400b0309282c3e1541800d50008008100d1171100351007080c5480164466000c1c18000c03a0100c5040f050381d041095101c251444440d480f40d0400c00d03c00c8205000080001c1c10000c0c00d854104442c01c0b049482d8441d00d03202400d41d84001c00d0316400d0f1984400500018840701c00303111903c4026507008001c48d00405083c0d41620800c0844403110040d90000a44088a44206c1460b4042910802d80c0780c0d903508031103402e0720825100203521243e1849299903022000e60301ca440d04c00c41102404107100c200011403440380c00c54100000207920071041000c1c810003006114000c03a000d07601044030b0b2b403464407040e00415403800010100000003021806010141e480303182070820000c15107030000580460400c55034020f10906001c18607202038542171500900c07401c10180c28041c098000d950340d503911810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 598744757 1250 598743507 598743511
    0x1801030e0a0501050a09020108011d011505040f03050d1103040b0708070f0b0a0c020715020a110622050a0e09370f020906032a180906070e09010506090108 68
    0x54548100507010700454000d0084c1030195080b042c1c001144107040c0001418420143c0088140c095009010b5141c41d15807030313405044401c4102403004500c0254000c840314412503104214244070403a0100500c140803c00f4020451907480340441d00c103c501000ea140c0c01f07544654400c1c4a014440c2c40003245400004200d101e10804121000e02115503504002940aa904401246d590707440240901c0d01080903038040c00b0803c030102c03e03424461200940d107440408000705120b0003100d40d0440e64440800b903454403507a180381c14a01d00b50202c2164a541480e1003032510030008048001030b080088910180194840c00c007501e41c00c1d00f01d072000c02c80c0206110302c6282c0b401da203000b0044002207c00400e001c59100e41a08140c60505004204000c5405010315200340c101c11111010709040b0140b040715615000c50008e4124070072000030b0369288008040112114402003003000007440810018803a94054803001804145c880034411101424040c40790842c074100038000c1c0d10741c0202da03119 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 598746007 1250 598744757 598744781
    0x504080106270225080c1203091f11030405060406060b0301030f08070f08032a0c1c09150f1206050127050d0605060909030c07050d02131d0c06180103 66
    0x40c0b1079855104c0311840680c080100b82d0707500700e001c0740300e4044080601c4103002249100042c14191b007068402c1603102c8041811101458010b080800c2642c1c00b250819104100c100945684916181c10708030703160401240c00b00e48161400a011550480043c00d076416070b5000013041c54446200d9440300070302d07441040d0640718440001d5540703000900020046200e044a07400c01c00a903542c0343c2c1e000709050312591903440545001d20900013034a800248030080860381c0c0200c0c1c00c0785010400c05a903010b070147c0010384002c40307100b040d16015422004403881410561742d03c83e51510718900315411690079000e01d0f80000c0f1841c0c2c0003605601102185800d400e803038241094010365400004e40e4101c01c045c000c0390117684a504109562408903111503010704400f0180d4640341540003c640c0710000e90089a00c25441c0e0720b417603019900c0b07075407040080342401c4d641048246105108103402c040d50500c000c816100310310313001c2e04608002c01590702c4210013010226400c286400190b010b000345030301c24 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 598747257 1250 598746007 598746037
    0x10020a020c0310020406020f01060b070209040c0305030d0207120f08010e331503010b07080f0918100501090303080a0c0c051506090a06060804060509030d060605040801062702 77
    0x2110581d4060100f5005844882001a40e4a180290103403c1c001c55400321401c591402004122400070b0204803110141d0407a0008641e030703140c1c5482c40c4250075075080a030003032102281e0010706200c198000e20f0410f0158552240b0285034920490b840f07820b00e108100090800ca00401c49510000b178000e41021017070724440d9544403006040300c038038800000381d4241241c0d030b14884680c9040a401207201407a001080f40e01d950b0504031201d18920440500070582e100006444aa5000e44015075036940750007810700d0880545180b00200100b002c0d00c9009c450780030031000040c1c0b503004031580c8080fa98141c88074404e554031080588010095005440140400f044442001602c2804100c4c0c10f920310f00f031039500c1c5080c107a05001280d440180b8503080140380100038401a500101241d40c4141d1020011846544079620b4605600a07030069120303c0c0e08004020078455002000b90081e240d5401c0204442c0b40d940d0480c8001c85240d022002011960001e41005808260002c1001002e500f0030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 598748507 1250 598747257 598747273
    0x50f0f130f111309050601081608040302030708030c030906090f10051504020a1706010f1407210909180224070c0f03150504080d0b040e0616110f10020a02 68
    0x2d555444428030510010b0040000e009280107445441c0e00b2100a11300001546450f02c04841400c2100c04540c092003e80000642014400c101300c50754103600c240119100d090610828141d90000c0d60800885d018070700c006002404006000604042c8000c000c0c18103440c0f58000c43d000700300c00b8140e00041e168410940425490354002010b0440455590002852105c02c00510032100034050070704014480304040c110550042c50a021900920380040d0340704070b140340c0202000b07a0082803401c5c000284981d00c1c0b4170364000c10030314221501a4020302000300c080c2c0c1400f00302d54403110000d500c81601a01030501c048000c1103403600d214540751080c82e14503e51510004504140d028011031341c0d12041c280304001c081c00b0341002d00009010706020600b480d40c0c0c3c40c003c9000c1c4c41e030710111003907171040e1000b5a075490b60000e940415120301614200d050044006d0710888a84045902041d414120480781ca0000600d800a81d03820320082c08811a0410010b000b03544a100104114803030308031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 598749757 1250 598748507 598748531
    0x4090311010c0203041e05010c1e061505030106120203070e060d0b150f09040317130f0623010b040504050408040504180201110d120c03020c16050f0f130f 68
    0x45480d0307800500b074008545940c50000038060341451281b440907010300025040080740d8100034078081c41c55104100c81c020103d0b050f14841c3c4228040c0000c2c0c000c45c1003151364104c207032086840a0588500741d00a00440f0340311041d544030080000e400a405600001040141c10705061030250031260081c03042200300d4a585540200901c1510302400410102000e0081480c050303d520640541c1680c5445d032528282e107003e080c491040c011844a018200d000a040030b81c4282d0305452179601c502d05481d15030046c28036100510185600501240030f070400c418515800c07444a50403240d00c00702d6149000e007040e003800003a0101402c100c81c8203d0504c004520340e640c0d40104410100100080d411040d002c0c000108241d4480204403a0741d0060351a16600550100710b4240c894107010020415920700b140c2280240309074010703081c260080c182559104180d25501404507a8202c0c0c110100395007000401401c21049121a9400795080c0840b0a14901c0da8208840788582c100000840805400d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 598751007 1250 598749757 598749761
    0x607110a1d060108070c050c0d0305130b0405032404060c050904060308030603010b120c2e05030a14130f020a031e020901140d02130213122f0409031101 67
    0x14036641c40340c9403002c01040d543e110020951020040c6030a444141c880e45500d91a10306055400c2d01941708010144181806081242e143c056400040c2da01d555488044110030307001400744920a0081d0b000c003002030448400a804e0300310002003d100c064031b4541c0c07031100a00111030841d0a201c82441200550794984c4103e000850151807042d41c0c3c1d1621b10101801c5030300300e4030f2182c85282148045080c074a400100c1103981d44040d00c1070700c0d1100d102d4500102200d082c12116a4170040a450808896031200141d030040c108900188801d543c48590140001d404540002024100e0940c00c008a9a442c00496505c0e0010f0002c0c01d1094603a1550000c001c0c0305d12200b5024000c807003144045041c101d0305a40113110b0300d80c2d900100e00c120400510200704a02010b40f2880808089207007591050b812110b00561005100803d5903507154a651160b000d1074041c3c441c084011110b048036404985941c40f4403000e460100c0c05c1d01d148004101c020002d8241c150200000c503814070030414824 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 598752257 1250 598751007 598751039
    0x31911040b0d0528020901020c1207081207120804020111060901051806060312211e0a020307201518010c0c120c06091203290607110a 59
    0x906041d610b5080e01c1490381034a00144c0b62244406500c2811282c448062590b000740d2071314500c0c09603841300b1460040f0724100808c16071a50241110108210b0084001100411a0080c409a03600c062280e55909414010a4000307007000003281d8262040612464010f944184141092600c40c8040449a0f02e001001c175200b45290b90740d54107100741034031b580000d20440520740317004250700e140480200c2d4440204640103092240081400c000c94002c503501d18080c241034203900c4d04c00b890004001d00014050a4001d001d100300c50b40400c032004280d0007203038490380a54640c03907031aa00303460400e485e8809681848946000d061440130303900e080e00b60117900a20210507440386000000035510b084802515181e01400f03d40c1441034002400c00300c4026240b01141000c02001045040020207403010b60001000071003003214240d541d0b42c01d80c0c00715a60307115841e04180c013240c0750000c00782c107142c0010344964000010700003c4001801070310030700c4a500010b045199055a03440c4c0a00501d568 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 598753507 1250 598752257 598752269
    0xc0504050c0f030a1401080a020a05040f140a050a050f0105090f0c040803040602160806040201171504061502070e01050109121401020a0507060c17061201090206190201050906090303191104 83
    0x5407802c145c085824001000e000d0010a005040c803425182e00180c940000b510509008544814600b603803c1203d9010803492106194060f45c0c5d03142601c00ca0000300411160b403400d140c948004501c1810b010b884540c181d0b030003c0c01e80301c041d84841e001d401020400800b1100051010840410b02c0342c4140301520080c15207400410610b000260650500110368004500707980c0010100070142c0c0e0321014261200c420070b884c21155498503c414001032819900180d04103091135800940101070301034048000c8480ea0075070b010b064070341400c590f640c0000e2160301e00054240101313010700900900100c501a00c1180c440e000594100d11450030382c1c12206544001c90b10200d10202405002d00404c01d44c40090301c3c143c4a05804813204d20510718010b0003440c090010103031000c205000941c010280250010061034031109849500001c00b1080174090006508050100b18072010024080340100d02c500e0245080d656003224043c43c00322060805440c850b1142040d110760f103000d000600107005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 598754757 1250 598753507 598753511
    0xf1207140306010527090309060a0e011b03091401020307060c08010f080715050c0a020d1b05040203011503090524040303140402031f020706061d010b070c0504050c0f030a 75
    0x4050209420034034141c1c41340340201004034106800e160f40c5001c0b40014106140d0001c420b0311801d074400d2540c01500103140e08050001781000007540c0009208600304426a27507642c481c010400072002c031106140c001000705000300340c02c1c4a089008807407003003d100180304903030500615440310800c0d20a0300f001003022032107800041c0500880403446001500914001341a00351070200e4690100399400e041da81003003070102c1e032035035001001d211884c0441d030010700c0d41c01d140c45942040c200611801000341c103003981c8003100060074101402a64101c0e00101a4040c46542140054016040480044540d4040d9080842d029440d2880380c05091140704030740e03081898a450043e04a40d0b4044103255004100d10411006079400034800c7c03c0c1c20960b81c40590300807500704072080a8022110024485801c1a0307010440303040e1001c49041c20300040141c0d0407030381d9030740c0c042c10180c0c442c4007000307000c0f620030100500040c20140c0206030401c0940580d2450700360040501401d94009480ca402c46513 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 598756007 1250 598754757 598754789
    0x31528091101020609030307140d0e030c01050a0b0a0602030715020702090f0403030c0306080303190b03190b0c07022803080c0f0f120d05130f12080a0212060f1207 72
    0x250f410401303194000c000f54010f40c030314107040b0000740281301000030403d403400001400e18600701d0660880c0895002c0013040380e884804261800f401b9140032206018054075019440095244c007c0038401290701c0780e001356180503000d803210303201c3d205100d550115a0f0b03000c01030440180c03524864948202022410302501d81001d1400505a80f59040c91000705400c203c000c2c0300140011003180c0c1c202009012080b040c1a20303194030006440f0f6911a151b0500603507130014071640008603100480341c4a1031511401d59200103c0c21080d0240400294000400c03c1e00c424070728501c0c600895003034100708454501c107562903480fa07505600149a0001c2038100c100d40341100003042020307070440321100020344140018422140314a02a0b9003c1081440d00c55000c11621440c0a050104850708102e00410407800c80c28668400380d0214150720000394a40e0010b001d03180700b482940c031000251403240000d501d58404000402100b04911a8807142a50b0f0140d18039400304081802000d504041020007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 598757257 1250 598756007 598756009
    0x6030c0815090309010e0f0d0b07050705070f120f0501060f030c240210090314040b031f0b090d0302150a05060a0501030e070905040f0c090501050a050315280911 71
    0x10000340c042c503416407040c810b13022107030b8102420650303640d0203a82001310314042d800010041022450003a04080c3c2d07174005d100c0c0c400d80c030074001c03d08180100100d40725141d668909600d192306070701c03407103042e0350341c041d842c03000625420504165076000380e00106610791902c00e441401c45440c0e00032116132011503070421079113480c9990700740c58801042c0061030890b0001406510381540c0e600c4003078041e035a07070440f2041501802c0c00030703034020441c81c220361a1a00d4424400f080c0d8029200400c44020034841c00605008050501c0c007505d01103290241081080c0f014000e81652480044040d800341d0420301444495154040e449099401c0c0c0c007007410f04100083c01442c082a404c024100f500b8052a030a101000065000444241c1100000c4680e600d003040007001c054641c001f86500c0070507000145084890308141d06a440403030703650f81060307921801c144d5a0b000720003040d5507490305c1c0c40014408102611003101100807841045c3d0b01c0d411300c0980c0800f1600321403821208941e0070003000c012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 598758507 1250 598757257 598757293
    0x1b0b0a020606010e01081302090912030a0f0b030a0f030507230c120304030201230f03090601030302063d05040204030524040803010b07110405180c01030c0509090a06030c08 76
    0x183c40a0030314042c6d508100f0071082d10407403140e00103409140701002003200500c04000380d0200d00000c601640e241d0608000d040701802e403950420800c035050101044a41c07801140d036008850f03025503031108450070b6641c2556603400070700090342e64400aa1300e00380c400983d04000c1903032000342405003c1c000d1005c0100301f040205075082d188140c1c8144000d00050342c101549101c84000186480380c482d4603003100b80b095215603090300a00050110611118140008116040c3c03407198082d2001d56075180807100204d83e103180b2056044601c1c0b502d1800d02c429010414140e001c0100c8820350198490b0080740990344079078401c4032594081d100003400c0200a20201d400c569510b8118840fa0506407181c24503800b040c040e0103091000001e4110402003039000c00000356a010344248064034040c1c074501742a0040d820000c2542c0a01c2400c3c5000c0d61080c4a90842c44405460362400d005030300e4140020400004e040e0507001e580c0341000b10100d0122007844004000750750041010121000e28244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 598759757 1250 598758507 598758527
    0xc060c020f0f061603020f07021c050607050901200c1507060b090402010c1e170307030b0907021c090302041506020d0e0a09050606161127041b0b0a02060601 69
    0x10300d4000f64140040084105410600d80c001d42c60050b0b15084201c035521283d00c9030000095000c1d00702d00e1a40100503c014408145078024025250550f80b190800e640c103200302c448440c001f03940d01d100d0342141903015864003003464003882180c1140d510f04000c91545101c0c14580503504070045402d100b00b21030350051651040e401d4800001c5818941d0000e0503040d40017800074a05011640494a40d0402c601c4d0501680e8000c29034602d401c810311110703101c81e4400d545490009007001321000440c00c0c06490603002d24802d500825049100c0c1c100c110302518968100707030400210a500202507615401420121000300c01c240703007007526140e0040d00e440c08144014040c0200107420010035541c07e00303510111084c1c0c0c0e4001c0360a0341c0e0348002806510940c481901240c3d071402040003031201e51010700025600c2030391121100102c1c1d002c46c0380c41c0e981043e90020741400400000300000d02c0188914000c640208403a1140d94603010b040905810203041031005034088402c00c1015070b404640c040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 598761007 1250 598759757 598759783
    0x9050618010b030c220203010b0d0b040b0a05090703200310050904051c110d11010c050906030402131b03050603150f0f07140d0f1d0a0f02010c060c020f 67
    0x500c201a40465280e24119046038814072501c071540840b80d17407243c54488115201d06003103540390f1310394941202e01c1c0c110260311011a80340c80200e45036400e00344624941404000c00104d0000e14140400548281c000d04003020103454081045480240410000c100030092000f40e440c0d14151b00700108410300395010302d00c40c3e51603c0510011860100351086004584010050980c02800040e41e100318080c440602070310402c00c4036400682e02602c112440c1c6001720083c441d8641000007258140101c1e030200382d01110410102d0018540008803842042a00401240d50b80d0300130303c4040c11440b01440400400d4071101040300d0f51405011406001d00e400074406240d0400716011000498010300424024890202041c5510300034a502080d1040341e003156a5100022001c0c2e1016241007220011410304001e64240d40442c1108100b18280e000da009203210b4416490303c0305401141c51060341481414070048000c55560700a0030b0103000960018204080908002442e00302c01044034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 598762257 1250 598761007 598761011
    0x1306200a0e10091824060210060509061c02031912030e030715091104020d0605040522030c080c1501170a02240c1005060a060206100504020c0c040905061801 69
    0x5110941d2401c0310361912100c0c4403c001204c20030b1071a500c0011141101c84c07001d4440c4c0310170014449a00091030081c0001d10642400f07820f0384e1b0814003411050564007654410744021040c540c10504c40c43c0c20103260b000508860482d004882400e5019080340c41c290b8a03540c031200c14594503509801101e0308201e01000543c6407072480d4458500c03440300500303180486510f0714649010b11044d03121201d0700d0140203004658442c22032100a008003c184601c50007281130200255121005a042290f18196110320440700c080990b0304a40240d0040c2e021558440c0900000031824010002c020384881140c070b140c40c8550615108040c080009216925036500515007100183c69140d428094004c0241030b0b003005100780003500b01c660191807209241480b40241c84045144107400c050300424045e10382c07250080c0c80d5001241c550404442d001000065071004200c103003003d90003415048100c0c000e840d001903c1d48001000d850204074180c130035070b02840910920740000d18074001d20307030990402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 598763507 1250 598762257 598762259
    0x52a03040305160602070b0f01080d050306031c0c06020a0206010501200a230109060c09051207050609150a02060a050c040305062202100f0305010e1306200a0e1009 72
    0x1000b01180b140801108000705440f034014208001d0360140ea6219500030707900c22580c540030080e071031510424030400d0310b24481c00315004400d502070350440340100e0000d0301400081c04112014544031030b00c000c42c002000349241000000c10201e1015207000b09007a409000786500d003100041010314200e110565481c1502d206000000001800341d0207668001d0080f422061325515400324064030100700d03c420750801205600700036a69000d24819170468031108426a165402e11000403003000410900d40d110aa0503c036500e0300350050205074000501d510b6040851b185003000c01e4001600740f5000d03a10400c14424403003400d0113103d0340061414022801d2500d992103040da1440d0180200301011908805800c070703d07540106103030000e070700039004482c60071002c00000c004c3c00295411800080c600400410402201c0c0403450051580c504840410312803501c404c002030a8000814010f60a80c0c00d150000c29280740180403481096265504010203610900401300005000c540800c042814 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 598764757 1250 598763507 598763513
    0x604020c0307060e1e010b040c020d050301060309170c012c0c06090402040314030a1701150509010c12020a0c1d040807140727050601050406120b04052a0304 69
    0x1042e0307034640da0001c0001c140254a042090704160741e00c11042494000901c28042c5030105400c0810380343c0c01520100071103002039404a80b2241c06801000014208000400c0807900c6908071841c10f5004103800307049100703482828541035114041201c840d945400340710600d0400c0011010713004071207044e40e0740c03a5080035540700d440b09894250144035800c0484c03803829584855046e00c01540d80401c0c50642052401c20b090307600e0308544c0480c000036062108020500744484c0d0400c1c100d81c00744450202c140080c41059826070004040315040185020068001c42c00c4006e580303010b2810fa8018000c41c4082d0704000070040100d07003251004101141c4006a910050240168000d420042c0d06840c1c000c103152942c40483e1000305a07109128402c40802c2ca0f401441e4980c21803002c0c010864034806540c0d07945000e0380d40031038000f804034200740001c00503a8010213002441c078041d1400000c1241c110000a421141c094805500c064046001d41020f00a2440940d2001f41c08030120344c21440d0541d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 598766007 1250 598764757 598764763
    0x309030e0f100f091203020304080721031409030a140f010212060f06160c0f090c020705040203090c03010e0303100b130513091a220206030a090f0203070603020408060604020c 77
    0x40300320401c003003820001c00320743c13003800510050b000e43d181881410302e450600075940c4d002400b4179003280c001c10310002080985551804c030098003200e084240d604442d141030f5142100d4035804aa420010070602400761750074410b40c4c03142c507c11000f20301550000d0018a28151903280c41441917803040101640b0382540700001039005500b101c0205420101e400403030a0703801800403000400c0c500f80e030200b04200011444009503815035410001c9540d0b00c07128241543c2c003041c80c0402680250405100c0c0b8180f9030000e42d805101041228000c01c1a0b00c0881d08490300e46003031a0142d0008824031154086461102d802481c4c01c9031aa4100440d031101d196441001c1c0c42205c6c401c2e9808145812028103135000703042c10540003000405031005030507a56588407400c950b0b0780402d070a0a41010344515400803081d0103160003400c840d0641e55000c0046005000700c29098903003242c00f894010060760108241009405c0583e00507807114078005c1e5103451708034003070001031040d03005200c01182d60b1000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 598767257 1250 598766007 598766029
    0x20d020616090b0703021c03110711041808030402031509060106111006080a0302010f0c0e060706060f080d0e0109030321060f060f140306010c0b07110105070309030e0f 74
    0x261100381200c01c080107841880e8964810b0440c80b00105a100c01e250b008606240b2a201c110f011080406140504500b03c0383c0003401401408000d0200201041507039445420454015100058412b01000c00420b40d56201c2000c0341c00c1d0100000700002c508091000c0803070184ee58a0000c210700309210550345506050103907c04000003c500100d03181020484080b0801518804001082c3c0b00c415507a11303148051025400b541c200107440310382081512075804983d00c2980c0c2ca400e0618944200302c0203501040c4151442c0341c6955003c50a5600441c40700014a4160001d12005406402c041c1103414120036250503c000c050381000031940000c9104c80b080480c00150300c150000340d504000030326017600230a0380c0d950104070101d40709030014000500302d810b5843e800c00201c140300c6400c2c2544412a042400200510704140010350010b1a003504680c0a09100030502c1c5042c7e5501c1c00c441081720031340c0001c5d484800900078150040c0360000f000b1001d03641c01014406400209401240e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 598768507 1250 598767257 598767271
    0x30c051203090a140f01110715110105070801170f12030c12010b0d0f0e070b090a08030a0512060d170d110301120b060109030302070618030605040501140106020d0206 73
    0x14811481250024402ca80c8103190041c0703004201612426010220115900ca06004600c5405486a55130080d800206150542c5004048060a10003280d04003030300d40c07580d0418408050803940110b0000e000e4284180d43d5581c419406624201c025100143e84c20191082d03900410014206050082941c0139810800c07038100b641c03601c40303d540142ca44180008241ca03d101d80001048848214000b420fa14041d0b0703905100c840040403104044032158500c0144660000c0c01c2001140e51450240c046190010321203c030a503611421181558040760088000130f0300090300042e4140281081c5800c042c055698a01d440e0581d0b0720340e0650b80b01503503448400000805c10704003945258100341a40310800700d05c240c5a50352400c0304224030000c003e046820f5207400f000100194032611100c01100d800d5402020040c0ca404402c1c6c07100260340303003290f06150782008080003083c69401554001c601c54400002c003090710418105c4400d006170466070842d00003ca03054070b40c03a80064917031381240c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 598769757 1250 598768507 598768519
    0xd02030f010b0c102c060103020310061212020102070503030109060501120204080d0c08160308100e0f012c1509150d02090603100c0c0605010f1d07030e0319090b04030c05 75
    0x100c600310f0b0404030a800300c4440113859171404c01070f5030340000315072181264825021640564001c000c444c0980720b040c0585500070b60040c07400b0000ca424050190b042e00020f0000618101c078585819045900c04d030000112181c48140401c81540d1250800d4440d06035030404605150920300300f180c03240700101900b030420206203241c40900c00d010b011070747c070a09480041c210705002031402a000708012030b00810908000840050b0101107541101e100c0c9510388280605a800c041d40c400328801507c40981c00c64045030080c00c207115910000328090045646507c82d1500d400d0708101b1002c1000700700c950010494801c1ca011900d030395030056082a411914100349a85041c04240380c4891034610310381c00360074000c80b681c001d40c10201c050411406440284016a00d17130740000000e201c18451001d1035141d892440b1080510805800c1c1c01005cac614010403020f0312540314a103580c11401d00d0300384842000040b80c403e00d401c0542c410043c107040340a107080074a5a101c22003144554440c1c60300a01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 598771007 1250 598769757 598769771
    0x11518090e07050919110301062007030b010e0402030d09080303190222081e060c0a0c020904080408010f051b16060906050601080a05060307090c050d020d02030f010b0c10 75
    0x81c410300c49000a03002c0504440c20b1850030800c42e03206020824001c00d0a10300d04210980070240b920708a905848094507031a2010903030b48030498584141031031215050003036500100004102d020082d00a05501c030041303455003050f00425080074615000038051002c80c0d1000c0141401c040281c0360702400394007580d00030780c030348070a0000613103d110001650f61848803040d1103032010f181c01a000b9154000200d0703c000c00440e01714218410768600e6a03409900080c0040c9108603550b00a010f181c0251038200400c401c150b001c45d904445c281ea04070307400700340803406216005092040142c1000b00b200e0038400c500b880112260920100d0213015950310001412407a020f050119a12546600c51001c000303404441c24a440140b1046d81c0361400030305440086480302c4124010180a0315008029242091600d0140c40007041f5065a03581400402e000b02c0a20b0070192020304002a0700410140e42da14088010164240d0160400714100906122410400b207000544010001d40c0c68000203a10b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 598772257 1250 598771007 598771031
    0x6010c020f1002010f021611030604030806040515060d0c0f030c0824030f0a1b2303120d0608120c0a0303020a0903060f020a0f080c090618031501151809 67
    0xb5240440d08110348500001d8081c00e458802000c04200703500031050382041000403010982c81cac039001d89015001840c50000320340d032031800758000b540200818070809506880325000c03480b990081030301d0041403070340c5018584015030082e0744c070350950016180400c14030f403070310502072300248003e00300d040300c80d601150401e8004022211910601c500604072400002e010207000d556641c1c0a50884409045d241046150011000c0a10681d4004500042c0c408407840f00c1c0841c010001c03071021303414031900c04103903168000c00c402001d454101200c049a207a0a1001f0640b80c05901c2c0d43e108601031b003c01414007144404504004129803500c1c0160345c58220000823600d01c3c040c0d420281400380b9010401076522001d50003850b0f1000c0c240c480700003001107a881a1442c0b1400c0b5000c05800e28100304c000302c503180200081a4401c45d10300f980e82c9084104010a20f40740721540c1c6407144414007001404542414240211844020704d001c504840002044044542c40c034840d034011240c460301d1035902 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 598773507 1250 598772257 598772261
    0x60509060717030412020319030b0d1502070b0903071e0507150c03080a06150e0a2d090510060c0503090d0c170307021008100b0a0201020703030506010c020f100201 72
    0x752607005000552030440c034120568180c0e00948045460841d004828981075002005440b0001d600c0341100801c6100c3c8a0140c01404500b40107680c06411425020005a45c0c036500c0145003000c0100162607808030315040b00c10040282c0b450080c1e600900401740001d07201d000d61104825581500e00f10380c2c40c02d207807851070820326401070002404040740c1c124555601004000e6180c0c000c1c1d40d4101a6141c0310350960072030f07805000d00c00d02e07500c000f807a40001601400c3c0c519090100500085800c2d0350312849a075002d00d414010862060386981440303241e00c00c20aa03000540709102c020441c60070070b0050301842124900c114424040500c82002c14860240107075a030305032010301160144819031501e000024164020000705003101c21007004400400816926003950240960705901d01c0c006040d20b120b00000e10301e90366400804c2c40417a0000f01d810180c454100550009a2106010b18000d0107680000300083d0401c2600304004000d40d94080140b50840700c250340c1c42e200c0c410040d2003240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 598774757 1250 598773507 598773517
    0xf1e0c0d080c0d120c08190c121b1412060f040e1009051c020a060b0616050a0636170a0c020f0102010c021c050405090108010504030306080c0a06050906 67
    0x60b4003c10507024000303504800000c0c4040a203100400c94003030307102e0040c0c9181c00c09542c540c01800b8001081003001e4aa0b0340300c100320400c5800c101800c0100c0c40c85000980b00c014a105110401018950030220341080c8440702d0034010000d502c0c101080e580c1c04482d0044003c261034410203403041c200001c0c0c1c4a83c2c0c00342d840c9044a40035158103e180c5140071010344942e00003226140b0034070402c0301004095490310410a21141c0c0904000092519500080c03c0c2ca049800e500c807000304030400e9180f40c01807414403510711a078003809481480d418a07400301c0e031400000f05050b00000441e12400402c1104060070303c010400a1308180b07285041290180d5048101702c0c40410340080c44403c0d0540140c0c94648440c422100c0f409036401d100012402d0f200140b0700c1c5005070744800070510001500d0131085d00381c140d6915000b42042d685030001403141d48203030311101d003d0b59554203000c140740e8180550005000c500d802800800c0e4640c01103500044144548800c2210110ba012001d130f4036030b81158 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 598776007 1250 598774757 598774777
    0x20307060b0418030305090c1f120b09040b011a03190f0b13200f040e190510090b01173c07120c020706050a200f1e0c0d08 54
    0x10f80c4407001441c01900825095641042c280300300c404112582c074000003041444400c040c0300903400010070000765081350b54288010341c611b2300c0703c2410096840c0d4814240c8118010b4160040d154504081c000c0c0300510b01d080501040c10401c10000c0b100007900821180400c001ca000404900d041801c07001040d11401e000e030302c101c1d01e280d8070400c24000e4104000c06411080b2541c00b001c00c1481c5509103206507003903205030200a000c20050400300c40302c110342c00401040c1c203078201180d90b02c0707500c1250781c102c524503401b440404044c050181c4501c0b456805190a082814418181c1030a2540c0480011700000742004101801e80401d80b02826030020003040180f00d0b02c440c0b03208104c5180411040340e01c0c000140c000c00c0c80744e500c8522401800b5600b40950041c14255007821130465590b0301c48408113040c46030340681e1241c0ba400300c40024a0901006000c0c0403207141d165005400d1441842110100d51010341e440030314a4400705010303001d90012036410032007518500e821a12401358800359 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 598777257 1250 598776007 598776041
    0x4080f0c0a0909030503070c15060b250c050f0612100e01050316140d0203100b010e0d0c06230a02011d010608120c01060e07080406140408070b07030b0301110903150601020307060b04 80
    0x240319080e001c0540cd00c10a42c2c83c07004101098011070708203203041140064140d2a1001042081d03081c04414642c410101401d4140303040503061803c1900c810a07510810005000701c000c003c0044074034102809400120090560600003100b6031014200501440ca04c401d1198844212a46e441c01c0100500d40d014041e200c0e44858094540010080c0c1501d84e0b0101d4070302001e1186503c5e24100c2c0000d0340750f105600502c01c505014049076070b440d10f000000c48000c1c04910000900504201810201e01198008034600004012a100300c1101da030813040280e0400d0780500014801040c0880c20b024030400c82c1d41c4a14503c440c85026046690060f03000100f44014441c03030035440300511f40314901650050040700340e01c1c0c0030310000314000c0301c028001c1d1130240110300c002070246035144c0d000262454003080a0302c403c0002402c5031243c900d91a0743d404000341540c05400c090204060075035000140f50500d161040010b5140d10407800e0080145031707120b102075001da039240e00c181e031101229405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 598778507 1250 598777257 598777259
    0x181f0605040f090c14030705090d0605100504050709030b0c09060c0706093221031c051302130e0105130302010f060503030406030f0204080f0c0a0909030503070c1506 73
    0x2000c0c003a5403040c0104002d5401e20b5a012850080d240988940b01d94540d8a04104085030602e8044036000a446801084400c10400f0709a03681d400b001c0202c94006d031000105d504080c415480f068030300707502042c01503007000300704a22203030450010000c0726013004036007290390781744201c42070203114085079070f54418000308000c8105200010000241c800a40300c0c2411203803a505c11400c0031994800d03140078139524007255040032104803041141703680040c0102d034030400e804a1050130188a040d903400c1907840400c0300c4104694244001160a05d591400c005d9400c28100d1403580d44461040a8001c00e400c0030f0b260075004d0035034130030150b0b642601c0080041d41042c060034200500608001c3d4015820404c442d0540f02e10b43c81007a0848200900031440c01d443c1010980143c0300014000c8100ca03424803001600c1841072020403e640e100c2d0340074010001e00042040000741c0c00380c011242141c508004100069000f1040b69008615814101c07003143c01c61a0074403000c0c09500c62070310f0281c18454 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 598779757 1250 598778507 598778519
    0x1704030c240504140d12090f1a04091a0d11040b06031501080415180b01050603190c021603051006230618031606021c08010b130b0a2309181f 62
    0x1f2a000c1d0750503650f101051035680c40340b00c2c02c110418070783d00d509a082040200000c0c50a41d1000010340f02c03a03045100c5407031400000900c401003450301a1101010703090320588620346071041640030407080310b00c5411800c00c101801c609040e80e00b8440e062110035000300d030922411501341c82e075110305c0f40c00510251684035014a03440026100443d10709003410000b04261900e0002c1c0c0748038048241070510181100d68440c03014210a4204100f5406000c800400c04076100c038100f005036003c0d0000303040703205180c008501219202c0d84015003814191001003040a2061214120000110703086615030240081d003040544032030251f564544510345c03000c07200d41501340040702100c01079000d40b0a00d078088226420300000345280b160010f13155200500400c038482018002d01c1039062400401c4540f1141034460a40c4081000c80c04541c042c0c8a0a0301e00e400700084400c52148a07032800c0c146091500400c0381404ea044450f21101b08200006144001c1b0060f01403082d04440d00003404141e940f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 598781007 1250 598779757 598779767
    0x7050d11030601050f010c030311040512010218030309030a060911040204090f0e03460203031f1a030604110316030b0307050d0308041704030c240504140d12 69
    0x2a1030315000b0b0140300000501032800b0300381c80d52003d00607101da8104040b41c1d07a08500030b00c4200544a5a08400e2202007580e840d0b000c4c024007007014402c001030341c5a0200c84039420900000c03000c40e2090b40f0070000030055803070200381d034443d00c4c0e40300f040410310403018a810500d07103035104900c40e0058400708000a110100340c2080c20400d4003248100300d00f070300b854031241d22845412169544151308104040d200c06940300305001c5410b4203041d101d45000c0d040c41c41280890503042d003c0040e032012040c000011030f01a01011890900050121594a130101e0503a0300403000b12100440301001c80010320580b01c940100c1041c4aa0aa80c1075807468414014480d0700c064484c804006450007403d81c182d410001703422419986c0050802c07154035200da80072181718500a1044130b41a8100004e0011043c002c0d0241025600c900120f541c11400c0020a90050760501440025043c44031004840c40c2d80200807501034882c1d9a420a4000047d6004684a2100640e004002401190381c0c00081c583c84 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 598782257 1250 598781007 598781033
    0x3020703033c0e040b060406110313030303050601080a1406061818010f050405040203060a0b0109080a030906111911030a08040308030411060c1c0c140f0709060b0d02070507050d 78
    0xd919220840702c3d4840c1400111035446406540000e001c0009108840c0030b100044001d42c4074400726450500c011410090025444e0700840c00700f61104140801581c00a440a5111920f21410040c88961003085940e8a8001d00b40502a55001550308110038429204100302c09010b000c000e02c2d90030400070700c070f440c0d4000d203c0d40804034208800890b2514290281c00c2c003e0b500240180090384500c1e040a0082164000785414400c004900140c9600c05100b02d0740014069151900b0051070140d018180100c01c42d85042581c01c881c0750001040800451301b018182c1104d030b4010f01c4400000400d2420b0354410001d05203000c0420000100f01580e402944600e10400d1254100e0400e030041c0512401903c01d40d0030560011640319200360b5003102855a40c91040c44c1c50b5030114110b8603500551282d180c40d1100b25017080180c040318038001c101400040041040c02c0103144c0c5090040904c0f80909181007400e10740001c0c0e110140141082001d01134070000300b0031143e845003450301c40840b9100e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 598783507 1250 598782257 598782377
    0x182603071505070c02060708030a090506100303030c05030402100c08041703030a0c020715050913110d05061f05030a020c030a11070b03010b03061207080f0c0102010510030302070303 80
    0x20603000652484c811480c01d81d8150303024004a04001c0165540203c0c2c2c0c00042141980075a02c010041c04074108104084c001c2d110b0882998086040d410028261168001c10b0000d1107010005e110044c2c9601584001c41200c0c0c1c40e000d92104442d107440c003c0d40c07040380d006c481c540220b8131481c400002d01200550045001e06070401642403c650b0030b0780c840c3d84070b200318190004082104041e0502a50060140c035500818a520003400e40840400300c900745518135062800200f080c1d1050b03002845065000703081120520840710902c0344680055980f6171a5200b00f1002002158a040d040d0301540c0c01e040101c000d490300c03a003001400074100c000c5500f203240d0510820b2400075001ca40001100d0598502211251640e50784800388803820003180c4051a443c07040341e41c002400c103010b10100c000741165034007400e0848003070b10009007514000b610b6880280d80039a403c100082d0002121411641d05081c07503079031040441c0090901446594a1403142c1801c0b01c02702c01b64201c058942c0000c110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 598784757 1250 598783507 598783511
    0x4060f0b030f070f05190e07050d0c0507030e030606060307050703030b031b1315090905150a0e070603140402091e0f0f0916050112060f23011826030715 67
    0x15031202080081b0300080c08001e598503842409001400605485c941d10454034103049180c441e40d841a1800c550900e83e0b50360006a0120b051420581c0c8540d469608440803001030500341022070010b0700c0303803001500081c03c1c0540043c50504240c000d03048411801c40007020f075a4501030750819401090301c0241803c2c0b2885110203903801c454007c1c030600e0040500f000c1c0c104426420648008000c2060400564040c850007198500e10440403118512a030041c0c8000f040c1107a0720025940340c0360158202800b450308200d50940010748900c0e0780c6a1060b0100c41c0700e01c1940394900c00d0400c55180102c140040e8105034204042e8400f625400c6004031601a0902c9881e903503100529102e00b030a0140c00540c1000000070401c175031050741c0841400307601040010300b040e581c020400c0f070b00b459580003112503078165003d81c40d0061658422410304400b0f080c0a69400354100f0513010842c0b6500030005001d01ca511181d5212050780682210081c800c02102e40d60107417800e028500081f010b0308030070594 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 598786007 1250 598784757 598784759
    0x105010b0c0c100206010308072a061209020904110418110102060f04120f050c03130801060501031103011223011b0e010c03080924160e0904060f0b030f070f 69
    0x20620f182c406034040c5890b80641856400d607516800315900004080c1e81401407808100410341c05180007c11b80c0e40c107040100c84151800b00050030314114058644801c900e0000c0400150300d401e211160701c99400021b182d0140500c0e80000d0082014080c50741419410f0382c0441e0401030440100c0301000d00907000c440c4030340c2d03580740c100305040c03005c44000f4032031402d02440c104114010300128803002c00a08205090001031101d003440c41e00a004a00441d05130749208001c50305082c4201d4000c0d000038030f014020a100c00c10000f125120620480d0719a01d442c05215040c8042c00c800e1442112000d91500c54000050091502070700c415801e60403c60503071140c890036507009d4241c150a0100c1a12032440080c00d6880c2a02c9400008114050078015111401302d0040b038503c130741003c0307040013045910b1400d18207000c0a1030302c224541d203000e00c01c19450801d0030b503849480155020364028800700f0080e01119022018000c0004d030f032071305403042c51041c404003c0041005000ea9610019080d02c1c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 598787257 1250 598786007 598786009
    0x5010c050a0f0c0303090b1e0a030e060718090e060105060c010f23070c11010e15131d012301020118080409111306080408072001030b03012009120105010b0c0c 70
    0xa4851007403003a0090401c0d1103041b540d2341018025044666103410006200e03040d1004441c1800c0044555030000340702c2501c1d0281d001c6650340c029020f40b00040c1c0130020300b008511250ba4509040c09114803130f00d008607801a2a002c25040041a901d032258148040440d4030220740024034465140300340000900c1c00100a18843c041031841590800090b007040c20005005403402069500002d4210011608072910300040c00024480449030041e40c106062078201c0c403c200041c40215005100b0040f4010081c070078003aa0b51091107980703403100c000074103407010040c1d0041c0314110360094a181c031200c90000b844412400b400848070003120034002ca070181e80c100c0c0039500c0340d0385111005010020b400d2112601c03c8004942c810304c26407815280001549450101103181d03d140ea8040c6940b540b05002c03075906000b00b000b2010242c1c002d000d4061001000002c110360300791244284e000c0802c10309540c1d44c0b8006080d00300100c1c440200080e503100c03000c45029501100008540d403041850208607 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 598788507 1250 598787257 598787279
    0xd0c0c09020a171b0f091809030a031a040c0f020f0109020904060e0705130c0314091b0102070b041d0112050a0308090a0b091b0111030405010c050a0f0c030309 70
    0x10301180b56035400c1c2a1240340b00c01e1415103c0251a520900500180d40400c40c0007407801800301c0e0020281585d105c004150410803442d04a10403402030384880418003511580020a94038489018100401e90760814090040d61040154549a02500740f480500304640c10685243c000701e00c0754261760499224131541402d9071404c1030b000b5000b2001d07100280c0462599804489500002002d4421050303030365000450180000d10000c580782d5464902c00c01d403d800d4422031400c1d843d100c4000301649402004291101041c12610500708145401c0e481d103a0320174801c200c00b8142c0720b1070850300d8944440e101c88089102c0c01546030707501035040000c2601c7c0044080f054030658814014006403916960841e070558001d850111207224464421000480708484180b0440c9002e0040c11040c00c20890342c0e480c41022100c00307040c40031030b21b0780e0101c407a408170444095600031308291224074500d00e491480e000340088090602c0c0c3c1c0c0340040f6030400c006485640b08036402640d8000c25a81c0f141d0881d80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 598789757 1250 598788507 598788517
    0x809030316081201091808070809040c0918050103020d030806210312102912040f2a150504030203030c010506031606051e0c1c02010e0a0203060f13050d0c0c0902 71
    0x20060186c40e480000100c07010018046240f1800c8072070706083c03082010905890890f00c0c00c0d0007041070802d081c03040050700010705040d01030b0448144001e500d0742d00800d98121000b0806000c0162404c0050203580318a20395649054980039104415044400010384a401a241402440608601080d000440400e041d0300740e6000c00741c054401d000701c1c1004140c0c0e103440c0550098981c1c0034170400d0615080715441520540c0124894402c404180c6000701c81041209047d9412909030781c80d640e80c0300810f21080c420388088003800080640c510b1001d80701802a0f900080d070520002642c101640010342041d80101002d40032202c5003050003420f40728108450280500107602408641c0454010358000c1c0d034042caa91084518116807089014181040380f10340c401c543c9000081114182e909105400d00c2180020140180d04000c0d40000d03100c0c60081d115840e070030b14203408501e440607c2507405124952080465815840c00d0030060300350b41c2100e50036144400103000c0082d030401607000f240c2d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 598791007 1250 598789757 598789781
    0x4111009080c0103050403170a1b0513170f0f0c0a0501050309060f07030f0207030f08010603091a041e03031505062d0d090f0c090204030b0103080903031608120109 72
    0x2c58210300e008011002008001c000740d040205180781403005040c800415030088440c0d84010034001c80312003204410381c00c180d140c01700b0000d0422507602d401034403914000a8401101d84810900540c40c281450000312000d610f0032030044002030504504005064050780100350350b0b40e620660380710015109400110780c105515004140050450001c483d5441e074400c00601b00040c081c003000403200c0403070f000f070a000ca020940b200c0780c01d10442c3c1c004002034014900e620301030010050a5032046600d0081e0040016481000800b040c100035441c942a8a00c0901ea60b40d01079110701030034000d015040300c00c1c04000c005005174010400e0b0411200f00c400b1581d81c155102159041c14100400c1c000c451191003035100014018606400c1150085051150180340814100075140c10400c045581d00c0e4409844c07644100410400124a500760604481d00055155240d000c01c2c40421700358811400514140c071188566001000f654030060443c401c0410a00182a80c842d0084022256003201e4a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 598792257 1250 598791007 598791013
    0x13061e0503130b070314011211030c130908041205070311031b09090a122106031101050a05040801090f060e061005130e01050f0403020f0d0f0e0d0b0411100908 70
    0x210003280d0310401c0550001398524001030000b5540540c180320030000e8000200a4610703400f60340c10300002803200c1102e10703c11801390840241807400a01c0c0c6c0d01201c60070450b210384035109841804407807010f4400400c0d007080b0450700644640b41190300c5844500044803420041d0003d40c20500380000d1039000744000b112200c3c1c4482e40705042014030701c001000300500b4454500d4060005142510f42580710b219030310b0755400f054000440302c2000000b01d904d001081d10300303203042012a110b00d000c110100c20a080c42c0d0303a9296500400c403110310845d00000f000b0f41c01d20018108111021042d0780002d40280007c010507101c0c083c006440e000143e51251804140c41c00c1400307039151141504400900811001408032440ca00d020f080d501c0c1229040340000980007040700f40341c3c061280c1c2c1c02c0003090801402c0c0300302007544040e01e8800a513200d07108110603014000720a0720781180961100d5001850b07213030240792038a010440300c2e802207811070241048403140c00d41c0a009200643c01e0310166806 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 598793507 1250 598792257 598792291
    0x2120f030105060705190b01051c0503220321030b0f130b0303071a070801060f090e18012c07261608061006050c030d090813061e0503 59
    0xc10050743c10031013095805019480e00042a00d604003c844003c84c41104503540c4d07589400c08002030120000901019080c5019080001a1020045425040c02c040100c2a5448044021700740d004c01900f0007492203d01901c180c034018040020303d64417100b40d68048c000a54541c0601284d4506c101025030440e41c981540c000034956034000c88a40301c000f800312400d041564840c0c96030319807001c0044803078040070380c2484200c0c1d61100c0400d0242486013010781c404225021f0043c0450444d2050f00c10f104821004180024100d000b858160030319800203200c1c0b911654076414040015500520324421241c6001c41c3d000030105104003150b0b007442c00e00028100703c03403995101030310301e6103004142d020355441c0400f8042c003110110068504400200031515104050740c02c6071416400401c00e11109001c02c00c050b040000840e190b400400304c012030040d101d0300c0c0070105400350a4108950010072803000c540154040c0341c9002210030445100500102500251101d06c81030ba5207018200200c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 598794757 1250 598793507 598793509
    0x20d15030807030e03010f18020a0806040f1101090302040f0209011d15211806090a020907210216030201060504060f0303051b030d05090c01110c100e090103030507020102120f030105 80
    0xc1050304c80b860280010802642070341e00d02044501ca090a11000000d40c0b0200342542419981c2d0800381907100b009108504140d20340a200c088403d0005201928102490b291071344103d40c0c0350700071a03020300140800301c08400b04e64040d40001203004c0c0021010041c0c965034680e2130840e0240004050720000c40c01d0042d00c02c03540c0c254407040c27000c0300800070748050841084031080c1c0f041c441c46440e07004802600042c0700d094104180138002503107a5005400d020050f9403201c10146d0002540c0c01c1c041c0e424402841e405123120903141d60b003402c0a20106080e10110803003050b502d8154420390003000055126010801101c001d401140b4040c43c5020301400083d00540082010850b1100820f0017005d080d22401d2443c2c0c4480036403403007180c4860901c40e10072020006590002801d0900c10042803e00e1501036890303400510682c801d01c01810b000c0c1c4024001c515101c440d0401910700900b660312800c000c1c0c03051340039000417401445003140b21900380700c4e4034080e9280d040009200c03500d9646000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 598796007 1250 598794757 598794767
    0x2030a050a051b19050f0406030e0d05070503030c0304110a060206060f01051c051009090c05042901050d090c030503031602030301080d0f030f051f0b04050619030b060d020d1503080703 81
    0x2c4e034103d05110003000341c02681c2c14940054401401d851381c0214030040da01e080e20307062059056035101400700500c400c03800030f00044141d0358415104c040312034680c0d95508144e0320344c0342c652a00707a4016440c0744c4007141c05070340403520034401d050660769032a2001d612001150b261040071004401e2045c0709500b02e500c5034036600000e40110958410300b0b002c640350002c482c1180c4260300c0032654a440c0c0542041242014007808032000e80d1009040707503507000707820104500a074002c2d2f01410408002000b0500c2c000380d500441030260000e0210040645030f01d0010703a02d078820f8410b1504440711010b8115410720000480c0c1c182d81800b000360007003070300803201524170184005280b81416102c1003c45e0308103046101f150312074042d05a10500500c1d00d140780c009200c4d0103400401d00e4980401c402d01143d20b40c10f00b121072040304000c40c0566080506d10890007000f1401041d54400e0001480181d800e0749900035000b10071001408002a0180045c52030682400b48401051040c040c8501404a8007070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 598797257 1250 598796007 598796047
    0x312070b1308120702030d06050406030305190908030a03060e06090103120e0a030b090a02041b020a02010c0f020d0b0a06090c0f0f02010e0d030204030521070f060f02030a050a051b 79
    0x4900b8681041d4401c10050354064048515500582c008688150194154040c0000038a010f5504009240c19520020154800c1c0c080c0117540e0300006440c034078483d1240c07102000506100041d030380c0700c14204a000f0701074220391244032a1903a518002c50001d18100220a040b84d511403220b0000b105581c50540c0d11441c2000b01039404078000710008086181141d2652207690070002421080c0361030310401040b14070310b00041030b00c091032011484d0711030780000e0008950b5030242090076070700c00306103020000115240e0b40203400010000520003082440d24145000c0c01050100340941d50b2140c4441044815250f0004c00140d410360a119020303002d80c986030303000009480003103120281b07090745a1034031040c9110140007a034002010401e00005104142202da0082449101d460350300201c19800e0203403101c05080c01c80743e65040020400d89601c400008007403406c085d516807800c00300b008010030040311060351140c14280003806011281344e00062009610910030b0074615403800c0c0020744488 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 598798507 1250 598797257 598797263
    0xf0912030f04060f02060a1b0c050309030a030309021c080a0804080c0a030f1d0307140613091515080a1a061210060206070e0402072a050312070b13 65
    0x308040300c0507001840080c000b400c495158100601c6616100a143c483d00030292030110340750120803208140b0030410481070201d5450b0035201400503080841c1544a1081007551502c0b40e2480c0004040d015001107002900881e1001081000301417041032940c48031400920003582023000c59440b40c00361540c290068024417469080c00520040c491402560340801e4020138484000f6006050f440484a103840c00c40512a100d50100c84001c00d81c1c1d50900c0c0203a40f81941e0806242815840d80800c0d83c5881d1040d109078400503948000240050007280b10f542240031400e40081360600110001e0100c00711030341e541711a15610790207204000c0c0f10080058400e03a18400e200b40031941c034040941001120415102210b003801e00a070541e952032940b044c2c003550810340400010941042446589420564000d6034a1541f898041d0851000042801c1100c0380c222542d928401c030040718109454040c0c00311a00310420b051400783c02d0184880007005410502e00085601c00180c1124502d544 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 598799757 1250 598798507 598798513
    0x807080c0d1509030809010c050c0a12020f0607080109140618100503011e0501061b062a030b040b091023041e1109090c03100306020f041a0f0912 64
    0x24815401e4081c1d0f0400c0350184c00140c116400e00121800030b1042410700e4982c9d0905034902100040059140c2c1c4003c07501a01920303103002101d0100b40203010326692040c52074143c50551825400c0549800000e0080e0f009062404080c001003440c0810041c0c0180001001320800942c0382082c1c00b1680c2c03009226010124014400064585007402034030041c1f0701e2204000c114103400c0d4400822600305030b0000d020130030484e07500714100710182c40503440540c0000002c6220401c80402204401001030141802000a0003200e8481d50640c845500c00c44100e07424411038508104000200303805a90000c84015166810800925590401c1d4251101d440282980c032000350000740446002d055043d404d80c442d5860810005294400d100000b646541d103141040000e9012641402000305210000342d030020100302e45000c815505c000455000a06540c1c03240d40c900011201d8100e0322031444107500c84040218003a2550382503c844004089401d81080310740e6007044004540c580020310240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 598801007 1250 598799757 598799783
    0x315060a120e07031709011421040c081605060405011b080d0506190303050a030e0a0c0b0d0e010506030a03081e160f02150601180f030506100807080c0d 67
    0x80090040038807000c0c80b1030140046034650f0902090802c0c06401c034501c110410071100308142e0f00108241c7e00d0385040341c1c120362a20151210030210001d200c110410361340d00c1c1c40800c02005070000c1440300f9510586c0585034000302048119004003150700515520a40034401030080303511032039080745404d0032060289070020740c607101c2d1250366000f000e608124540340d400700050b501300101024044013600081d030300c940c0d25681303008100d0b0013041c0c0507034101601c0e28240c64105004100e1040040d41040001140c2a5240328400785c540c044034103208510700341702c5a122400740604c160307841360001802500c035408050740c04030780c0321000134084c05c0c4103920440c0c82c1101c0442c0450f003d11494400c050444103102c0b48a0103460011b110055a0840d030081d2298007000c0c0703245030245c0e00440c0030700704003886010b9103001040c0d8603040c0c0c10001e081a00c800d000400d00100141c8180112101c02020f40c04a880d5540d460300ea103c40c1c0078400d642d0740110590025424000300c0390480c1401001917800103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 598802257 1250 598801007 598801037
    0xc0f0706050c0307030c02030304030903061505120d091a0403140316030201060801060e240a08011814070e0412021204144b03070e040c060201020315060a 68
    0x2501e0a42d4030b0a0080300110030007000d96010301c16121030030443d000440c10340c50207a4000b4480d034410b00008014036120110095032126640000340548002070440307540301152241e4030381e00c550714a80c0301c00085161500103001410320746180d045100c01c0f46c0040c5020708549545c1000590303444012103030f22080000f41e148144601e810702c01c1310f00c60350002c5540352400700e090b82510026000490000c40f40030902c80d15140403045000d1840b03034101c5540e0301c2600d1a0004201a02035030010019500307050200041140d00c1066400b1107109150907003c8004801e417166807030740c450145269a200407404900440c900d40784201002c0340c01c0c41199043d0003850036164041c0c000c0d5116541d0f58040385014407840c50246410000900c24110003d40320a010703140c420b0344000341e0b01c619000291240c840d6201c0c04285e0640407860070150031690055502c034440114010216030a4900505110012981910600032a4007966500d003a46200000c89410804030381d1000204209000d4114002401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 598803507 1250 598802257 598802261
    0x30527060a0e0a21300c060906020f04031a0103120c06060f090606030c030b1f0e0409050f101103060f010c0b0c030601030b030a08040e0c04090207050615060a080c0f0706 75
    0x1403e0448a900042503d9601e41051099011045040505c0a1418070000680350442554440c410341c134000c945a81581001d0006050001004c0c0256000003074000c1d501002c103008200f100d03c40c04116401001c0c1ca220106507000a010091080704094428055103225107600311030640207203000104a230391403000020f100701e241e0141c201551940c800b0800c01c4d4141c4076608035501c45080c1445100d40003000240e00328040c5071580d120180c040c6c56008014411414203d5840000c1e000304090300682c20101c0d039030011005280140e104e03020b510b4070742500c14014580c03103031300401041d070440e1540c07410040c0458090403007138100400c6208420209194402e41030080f40c0010003140e0b241491000142a50b18400c49640680c3c886070054001032032480450301100c5003282030420075255004841160302c680c0d400b9141090000ca1607030148200451464064060b41c0d0002c2000d1240c24180074560103003170b9802d00440c100500180c1c00c695981c00030314403148074601039407401100d07a0716142 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 598804757 1250 598803507 598803539
    0x408040b030c0c1f0608010c020a17160c0302090c16081e0304060603480302152208030306011d04150e060a031211030f07030527060a0e0a 61
    0x140c0000314913016120485108180107095240c0090003244010b140103540c503e003048005060300241d00f580e41c0712601c02010740b40600b40c0520313404540650360610100700f00560009a100300d5248022495a0441204035010b4030b56103110b40c1c0240007185c803080659008041340072000650380e188000492001c80095100324800d15000501c2c50640c28216490300c103004d0380d504080c4034590805107008036400310056070444140c00e403004040e0035404c1040001d099100030740000d256000e544103c000031001d44081801c2c504000081d800074000d400e02d612080c401d0748000c1d041000814115445515140c407a080c08100d02c1c10170740708000101d4200c0e0035000000484d00038210040c0074800c080505950800c00841e1161056070440e103c840c50403070745030400414041c1d09500710380244400c1c010f94174074a80f080c0407aa2100e003107090240c2107a200e40e00b100504080302c0703e5560304020381c01d40140c060201504982c00c1000c4801d044d100f4031f44150107d83d000000280000d2190121900e0403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 598806007 1250 598804757 598804783
    0x30204051f12020412230a020d290403080c13060c0f021302250201020c0904050f150603010b040905120a030902090703022701141b060f0105030f060408040b030c0c 72
    0x12540b1006082030b104030180d443c0e82c0002d80c0c6c001c10b031441646000145001c0c205404544c405580c050384d04e006101100c035000006420180070205042c940021584144102c0c007a8860003031980c1c0380041007507a032040311400d00d8070080c10007050048620451414003c10321665000399840c5864002038040c3e94000100020150002350f541c1c00c0326a0f0000300a0b40300505600c021380311101c1d500203910348594800da41e011b512a4400203041c032900b0449294115064015100001d030540d5170001082002c41d0322901960801c1515421810684101106650040060311042c0c010144601e0f207584008600f0701096200d44400025944490000740509119180145d41c1d5111070f090403c4407214617141c04040c0003080c0d1209440e6045588140701d0240b0f044441e039680d25030a00180300152131514a2190311485003040050011201c00328140c48048044401c030301d1414501d0f50703403501c00b2100149540002e00041007030031070000145d03801030a4140c8680c00c1c8400b80c43c2d030b9858228001c900d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 598807257 1250 598806007 598806029
    0xf0204090c09050a030602031e090109020109060806030a03031815020c0c090f061003180309180204031e020102071203030c1701140d03110a03050304060c030204051f120204 76
    0x8010400091040070556012070800301480c80c68100011064001403201034081c540000020385134100c0ca401410241803101560b016904000001034000c0055410483c0440d0f040400440c40c10b0142c451284140340040083c990707180150703000c40c00303402025010021589108000400110400894105150030800050303c41d109254100d28140307600780d15078040c481000034445a0325440101d9135000c401900d00321000f09040001710300418844c0306001072800301e03141040c20540d00449400031110000d0000a2150302d20441804270711451100400b001d800a030790b80304c140c40d039100d00307621140140113962080b580d55206120724041140f08400180d07940d9415408160003140c003240c0c460040701d001049604000c3c0e02c0a8110340f40c4d074028030448003c0c414404142c800e020800040314020203484540d552443c014105400549003201d032142000c060f8010248a407003600c04448000300b81100c00c00012a410303401c02070101c07441c030800109449031428205a80010030060201c1051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 598808507 1250 598807257 598807259
    0x307110418031706010806210c0604181d03070209060a050301020a0801090c020c010e04200d0207020f1804030c03031104170f0f1e0708010e0a02090703050c0706020f0d0f0204 77
    0x4110f41c044000c1045041c040210709115041d190b4040c61b1710722102d8014840ba66107066101245809007184004c0c1c0e00c075100060102e5059481e600014080000e40340030310040c52005d0703002002291281c04284140e0051240d1005413420380307c0c031508a44c020f44070008080c1c41e02c0c0802d003640d000340c80c414080362410700100000009071181c03000710192440a8004980303402d0000b0403041c919001e0900c80c42e01d56404c03190040072101080300b2480303c18800780ea074404040307440d0065080b01300c05911070314035101d018500d0f080c403011500703600c2c4141c41009029641c40d601901d08100307a01c0300354201541c030f040c00e03411119080e0091029158017030701102c0740400e085409240118100d00e44581d508856800c200c88032002412424842540320a03c90716910808003e142140036400301a013503003801d10265900d131002c1110050036009545c0d5030311030b40d607a04096054039425201d10b21038090030040e00c0c2c00b103241507002c4d040510144c820780d0701c0c0c840f00003e800207607403040c04810b44403940024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 598809757 1250 598808507 598808537
    0xb030f01050105030d050a1e18060908070f0323100501031a0c0703020c04021b12030703060e011512020706090c0f170a1b03080304210809030711041803 67
    0x2081c0f080311213890194036103031402d240105034014012080c41c104200743c0209500900581020b20035040801600c0b080d00d2b601d8400421150041c030400e48a409070141c0410002e1900d420817050f01d40000b0500d1440b084400e20743e02c16440c000400703e0902510f401e8584841141c0a0280254010783c20b030a00300004620b00d002282026040081d2210200085400241c02048003070301c900c4200c03001620740fa24012188804440c040070618036000e6030f40e0303052654074442c015601504103580c0c20403400f0f0300c400940c441c0302403e01078843c80070000030200c03803850700c20b11a5207481800d016001d41400c2045d507520058540f0305408465100420000380716440c20511410000c040c0b11800740c1d04030050001c0303251034041030040505044510744901c180500c1c41c0c0001c800840c0d00c88001c641d2440c140c145420303681f03d541003c43d504405100c0c01140107100710b40351400340d64204061442c2103042e0b550440f05616965045030000d848201444180c00102c6851800c58000e86a008089144d40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 598811007 1250 598809757 598809763
    0x30402040b060a0c060b03120a050c12040f0e0c040b04060f02060702010b010c0803060a0b0a05180901050f061b061611010504050a0f1b0b0c0c0301090b0c0702040b030f0105010503 79
    0x70401c540900414480d034840740d03070b00410401d1915000080050001d440002090401c01c020f0710326501410002849400250f1040041001701c10003003e0b82c55040300d00e58066584d126510940c0f1000c0d01c02c42e814040200d00709545d540080c003810503540313020744d82c00c001c460f43e8000350300042c007282c0710100d010003440c0c041c48500d0348a14984000c00050030102d002a100c2c101e0500094072207000400010003e0315980c1145d00075000c111f07025512021201401800380d84040603441a103c908510b42815060245e10b0302c2c143c3e43c0c018034180e040300c0c14406204684e080000b1240404101d0000019403040600456004000e95524141900c42050000e8580048440e030055660f14000c1084045000407800c1525141d00c840c8515824109003040e9800c6200c003500c11541440080c000204401200024945401010b0690f504015404101800c85100e8180a403c00700700dd00050088600040200501440200001984c2c00d50b80c0c04685403802d20311140f0241d039942d500621030b0303103810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 598812257 1250 598811007 598811021
    0x3110c040509030a03020c011524020f0d0f020109151a030f0d050714121b0d090303050c0f010f053102010e0f1804111c0b22060203040204 61
    0xaa900744800d041c90205a0340d6407048070007520825034080b84600e581c10b403c1d00808880000c998456115035180c0c0d42440700200780e503040c801c18509103e084508130b400880c5030f0f170710030300840082e00da401030403241070b80c440400000c01d80440d580d80c191540055a0307007010b48403404415400017003144201030401d0a82e08048905071295000344d407403036500d81d400030360110082040d144c41900d8810714600203004541240b0140001e0045800d05c0c07944409160140c000b100c0710b50008409076121810903602c1c0c0303a40f101c01c000040c114400500209000d10001d114112601e011030721103440b000405421555074043c8508501d440c2c406025a01c8103542d5040524008001c900e0b080641c2220b03130850325021124003c2c14021003410001e81d598070f4013286110610081c0002c0460b1401295001c00913004407401c80d200c0c00050308182c26400c01002c061542d00e6120717140702c008007042d2104100c858004150121001040c008045500c0360881c40800183c480c440150300d0b41010f10410041e03a101e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 598813507 1250 598812257 598812259
    0x3020d11090711030708090103111206040b06070506060909032703070609060c03080405030417060402010f0905011b0606090e030a02101104031529090906010f0312110a03110c 77
    0x10410f59042c1101c00801194816644005180da64941003030040c0c1c0a0241002255640e180100d81900c0301640d103c0c105100308412a010051411100104070f418011201d000c1d10992123800021880d04040207500c0d04940c81404030b90030488081c948000881c10319043d100085080da8003030502d0b050802c01e22024040d0750801000b001c2c1088802011030f4040c0c0006410440c80c10007003400d003e418130465025190860f40703994030f00604080b2960302d45042d20308a00289100c0e503e400003d100d5000c2c2d50a40f80705968400501035800c1d00c00090072808001559a0b0ba0b4404000525012a104201c0801c1c2c0303a401450300d80c1e84103140030b803c0c203240040c3c40c0880d44c10310382c1d00700d000c40c0c460b030441e02903d40c000000d11085c05031070310780d0f401084096014640e5683d016040340c500300c03000450f40020001283c6030107440d995100c1d03490b22500d00f07120303043c0711a41550702840000d100108805e80140146072580c01480002c40844c900014000c0580c0031400f40c19020000800500c40740e0359500e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 598814757 1250 598813507 598813517
    0x1030e0d0c0b0c0a05120c04090c0905010809060c0d090503300c09030a030521010e100611030d18122a020a05040c17010b03070f110303040f0c03020d110907 69
    0xf0040c40c017a0062040102604042900c4000240b840024405440c09000031110030499031051000c060107007440e500940e8042002c503000600300d04800108148189681c1c603d45003095204540600503122110b4202c0d41070101740b00c4030555070403258070450300025002041114480c0c0d1040414003000280c00d8120059003000100d000c2e880010396000b100f60300d0b2400303951700d802d07165003c680d00e0004261340c00d240240710300010745804110030190080d4000c05060312220780c0c41c1c0050703403080210341c00c000064100740160310045c507940e40200b8850203841848550146142d503081c0c074004c041c21240c4080b5a040c0004101c9000034900c103401101400081403441010b80c00046032008144641c034400c507201c1444510030340c8100b280d000344800c0c900c1c02010558403201c603514143c004442120014116510703040d1111b205081114030301c001e00b4080c40c03030340d04d450300e2300c4140150081080d640300000f15030010041c1c41c2d10f00b6181d6404d020b500c000b00b01c45400400c20800950107402801044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 598816007 1250 598814757 598814767
    0x91b0c010b1c05060f100e1302010f0f09030f02060403080301090e010c03050403021e03041e031506050d06020a0512160806030705012a0c081b1e010e01030e0d0c0b0c 73
    0x1910010782c1c140c101700c00180ea6100c50366140c2c0c2d0b210005040b500f045591106403410f014450395040c01d0721040c58400d032110030800c3c491900845800c10903480726400200603220070000316100c15100d640107400641130034602500c1c0e46a0480e00c1c0d100380e0280d13102c10b07520340100740c00396828400c0c500035100e02c0c44c040c0142d041070340b130082d40d6190641121400b42c808410803615450704004440041c8510105007056150782e40014441000e1480705031045221203030120b415095522030002512001009540703644029121040250001c80ca8401400b50400200760014048401c0501c111181d80300c07030211004081c070051840038060802402a4498031003070000c0d1ba0441502c030103103200900f15880b810540d104150f43c4003030320070b4050448e4442d50400300d4451000f041c082d20345c0035209284118820740c0001d016200c0040300350a83e8018080c00900c503e5032160542c500044070514000ca0203250701c41c419802d03c0080c0f80391001080001e4100030401051550440e80304019191580c141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 598817257 1250 598816007 598816013
    0xc01081e091e012310051f08011508010b0717030c07050d0305070f050d18030512090325020f0406080105060a05010c05030d090c080d031e09020f091b0c010b1c 70
    0xd10000c031110104c102c0443c00003036101007011180340040c1030082503a201d4050054075245510541d018500005404000202d1103949618481104000fa903450000681c030b8544d03a554079401014049440c02110030381d2040076200c40b005035000e2042c81c0591a43c0c1e89403440e10610304805101e0803021f15082c80300308480c1541060456040c003800b420a556100d41c09140c4400034000d85c42c0319220b0900c5034008805255202000d05403220812404040984407030030000e980c0e01901c031490581c09100211100340d00700030690b0b1201c0c2d0b0300c003801e50180c409200c0700040035103075036401010310b580d951420030038503141986c0d44030300a000038200903100c1c1c0309a0300d5054a911641d04801c2001c3e40b2854480104000c8043d018001e1400c2c0042c0ca01003e890000100541110081401c85100d03280003081851824440c20100d16030042034405104820700612411035802824404130288200d030b2820000d0036240209030703000f00d0900010b035550300718007040350400807100050a40e0708019100800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 598818507 1250 598817257 598817291
    0x170a05030a06090506090a02090d08120601020706110d030213052e0c03140711060c0106050415080a1211010c0302210906130206070c0602010e1e0c01081e091e01 71
    0x85006403008d650f03580340c5808200e512208480061031004001030518640780d0401030240038900981c00e690400ba070b034400c1220900d44071075000d5441d03081200c480c541c49009a0080564804d040300d540003140d81d6a00140710a800760110301c0e0080c0c1c0400c0e00c240b04d003a010905c0b01b8181c01c00c1c240708858034110384000f0610b000080e405054440e00080800a105820040c40490500107145540d034103074910919018103d00e102d414040c2c5e0900a03003e503400b4400c90b071202078490460003040d40348119150500f0301c4c545414800c0c18040503112003100a5020f008005680605032009607880c10342c9507039004118000d10303001c02c00290000034401e59080208140b60042c0303d95510746850840e81c00001c116200380c00c00103100380ba01c0030703000407816019000340044409180980310721460104126441c900d614449038003540204080b00421342c0952009604800c1d086201001c0f11a1384041181c00c00d020303160178801e41d001c001d4803030311010221061094000c1d080000d016015444c145109 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 598819757 1250 598818507 598818511
    0x50406090512010b210f01021e1305030708010e0c0f0a0e04030e13090302061b04330504051905060403060c4a100507170a05030a0609050609 62
    0x4030401c900c002005420b0320940101440318401082d8648103074400e001059103030785006940180c1d000d815a481120001882074802101d40b19400e0003907400f001c82400c0b00d6500c1075858081441c4109400b10310340d00e0410180001d05025000098081c81c6115200c0c5402a07d01a0714030400700740d07044680340c1c1c4070340110208460358080b8042c2d2070f44592800ba10204000c1c0300954120403a441c0e907400c40d100f260400c6005038001d4081c5c40e00d0361140700300c610080e403400e481004d01480c200420003d01c40d0b00c5000341c6105075034141c01e0300040d000011b0124102000d01074480041c00124080c00146480c10041e8140d684c0c07260442a10ba180c4004a0414000d5103c05002d15070b440d001403c82c41d00805088040010140304055000c1e001d450002c030a07005c6040b02040d03c551aa003a03107811b074012a4030080c800c0010700750484008419011142c0783c0c4008400c66140f00000c1d1001a80740001c0c0182512a205844440d104e1400d9041401250036039400700030928100400d0211589a0031220740e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 598821007 1250 598819757 598819759
    0x30a0f061409040c0b0c0102040612020a0c0219030b04260301060929070b04031b080412030311070b060306060402030c0909040501200904050112050d030e01060e0108060708070504060905 82
    0x8850340c1d500d04040c10082c9080c0c5c000c2107094400101e81524403410750090040e604161208407a039a141101a0201c0c040c5c82031802c04100c107d618403015103000744100901c2c0080c2d8050007001500d80c1d40d02c1c0310401c02a0380403561696000031640c0030940200c074507482e01e0542800182075615005000b8002d41c064460342c044291440c601c0381400711060b41c0c54503800c0310044883d90b22191071905c80c40400d01101d054001400c080d000341403280e50380c1001c4a80740d411a5100e800c25080c100d6002540071081804c070281230783c0f2020001c540051101070601c09016810240d46482d04405250404070010401c5109600c1001000050500c06042c1c1c0e0351004191044119540c9070f16103540100a07054006240401f20288038902c81c0c2807000400f05082d055405010300d9981e8481441110030644000f010750300101101c0400912031b0340401c003544000e00010a0f02035840f20582c90b0340c40d013030708154400d402004c10000c25070b801c805103c0c3c02920602c3d000346001d20b0715000502c2c100c0540241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 598822257 1250 598821007 598821019
    0x30c0e06010c0f0303020d151502120316030b0d170304060605060a2c03010608070603110c2104090203070507060c090302010e060c0f03030a020307090f050906010809010905060c030a0f0614 83
    0x400e14040310759000c5a090901d12308501d04103030715140c0b0701d41014540140b143c0180300da400b002c035001c904001528052014801066444c2c01b40003015000703032141c0c0c4074640d00072860f04803c0300840c50007081c070000c1090308951299281001c1c100b25065032400d0b0400c034040c1c1400c218500080364840c1d882d9150341c83c4150142a1003006442e695010002024903580c0b56080802c0070505d2000410494111060b13914200300401c0d0b0354480303044a0040303100358140c41d0000c103051440070b0340c12092001740d01c501842c046c0c98203881d130211504a070000d544000c00114007103030304800c00040b40710349041480142440750764140f81d640000c1c41108041085805007a021038a111080740410a043c0d00390070f110140e940340e03c0c0c03040006000350002c44241d40001c50f0400000386c0c0705404030043c42176800151860229550303280054030021000752100203559695007070100070400070b00105000e010009003031a600e00306202040301f070b114900103a1000c5444d12608101480004070b0078005040c060b83c007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 598823507 1250 598822257 598822267
    0x6090302100c300206090601150207090c03090605060105120402150c100e0c010801060203030c090f03060a0906110a091404020c120c011a010219020316030c0e06010c0f030302 77
    0x30448008a294030300410745140001e00340b031004600804012602520f118401c5541aa090300700e80d00d41040c0d0310905a904400010b20003018040140c00c01c5046a00440f14915a9074850070700300c90310306031544d0019a44a210104000550003050b81050702460881d0134136800c00c420401c140c1000d40000c0c801c0036481c0c0c1030155542000251006600894190f030f6034403200300403901c00b800345d03180d803048240205550820b8644c09602003138140c070042d600940c190368428403c0c0c1c02e6544080500d81e4410702050000016036820401144624241349001c90800c102d403030094195130340090240c0d0246030512520340c51581c0403104030b040701c2e401c0705c0080c10031610b080403400910070352240030524042e4249181c00385100d440203150028258000708242c0188080c5400031110710900107005810184504091a060060300d255080c0003c060324821800c50740700700000c0341241d00031500c03030064010801c00202900301403079010401f820a40c803401d2059136840061031315503c00a040c50b40c040340f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 598824757 1250 598823507 598823539
    0x203150405070902040801150617011a09060d0c18050d0201050315030d0f1803021c0201030f06060306050102010e30040302060f0c0c0307030803060d03033b030406090302 75
    0x441e0000604a440c0115512506c1d045c0b00350291214010b042c07131056100d0000610701d486400c004100000d603c0404849900302003119402c1820340000d08041801403060000300d82d110f10040840342d089060003e183c850f0411301030030b26492081080031403544030b40100019241ea07100031808950910b49565203603290030440038070944010381c40303400d4800e026040e040c01c1d07086070500d21107000588130400305038400803da5040000c103001c0290001d201e1513084442916202e5a00003141c1305040100d007100040158600315055944084002515140204159602849800340414104010f020704d0300da0b4000c105400303510310300103031f041621400303164a0340480c5c40151000b866004011580e1110760074031072140ca400c02c449007041030181c3e18039100c0514002030194100e940c088002402c640d01c88040002d0212032110507828186c0b5140c03031100e40b41d482200c0c010228012a00001c1c1400d95070940b80010084d40344a02d02544200070503c03040740c03c03500714811240e0440340003100e020010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 598826007 1250 598824757 598824763
    0x60109051005091306030501020403030212090a05040b010210241a0915040b041431180618050607140f1312030309022b06180b07080405060a06030203150405 69
    0x5a1400c00c0c05c0c0f4119021081140c10b40042044074000c2d421100606945a0700300c840b480703803810940d441040701004100b14200782d00400da80c2c40d8140103413079082d00241e40c0c4505035004d510400a1840901c2c1c1ca8503140320004070b10038040c24001c0c1c2c03603400d412410b10400e8520302c00c800d6060b01c100100261f51482014410464005d00528002c060f1103556403421000151081c09200348120800000d86940c610425800000c0000c003c09050160f800c501c84040109498a803a0310840e49c20144000462518000d0038603001c03100d190701d04803241030308015080c01d0010f0551000c00080c0356908543c01941e0742941c144410501d416942c0c2d4244204140030b88955501845098840c000b2400c00d154140c1d000c030034920300998584c0b0401400d0341d09011108844841c52100b010066010380c04214560300580303003001040c02c0314000d074a80f9103036602188000c0b104103000440480c2004108941840302a03080a11b03100e0034001c0034107540c00641c542400803110300c140501d48000805010f010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 598827257 1250 598826007 598826029
    0x703020c0a060b120a050709110c0c01031e290603060307140a03061103090c0415031b08030c0a150c05123303010e0d080c0c011b0c0b06010905100509 66
    0x3850481e03510174218500a6101d00f8240318410440340b40c0032241040280c030328111070100d10200e010304000d840300c07001940142200761541250301002819126070414610840031060510a42240315003804814244098091108180a05014000d0140030b840000d0b046042d18140d69895403404240c201244100074598009040282001000d00b0304000700d6004600400500742600c1414940405000075601c000002880101c0740110800c08500c07903c01080700c8503495440d08005555032005a45581c010f204642150340000541e10104581d2080384610030324800000d0041c0281214050314074040d4804000395051701500260107140c206460040b06032001c0801540394000100d503d501301c60203603596000c1d40c68040c127400c89080010348925421001c3e42c4240342a030b00c1c2c290181c0b160308103061742c40c0c4541d00c0b2a1a002c8044d1008503c2d5280056680e844c0d0b00c88038141807d0840810207031602d030501400b00360500c61034076101e90261111405091556171500d01c000420410b03d48 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 598828507 1250 598827257 598827289
    0x150f0c0c090603120201060305060a0906020906040806062713140d091d0c0702010c05100c21021620120703050d05030106020304151403090607080703020c0a060b 71
    0x80c8803020036008503942c010820340780507540703c55400c003418809908030340c01408090700d15840640003c45680705604402503181c840c0340d0142c08d2428410219145030807075000000c684e08400c080060a0401d40c0c40c185080e803503043c60000905c4802990f10007840e0107804071400312000720b8040140f1011120300906c0307141807021120207004070360f4000d1050005006203610080c1c1c0c50b0300d0084440c0c148500c50302600300c0c101c1039441e00056074015541c03100c61a07002c03580c80c02030303110781d0540907aa44a00c0311018601c0e2034060311f1400e00c1c070382411025094405490701900c113101c2086002e1080007641e189590081940d80b080c0c1c100340b02c54141c00300d03c500f80e0790b000d80c502120060084c808140745044074401c03811290a000515804d844c2400240110300c016403092004020082c2038100000030b43c81642490b051b104020140200359074400c4441c40041e42c041030601c080d0580c07100425600024910f411420882e0785014141c481c00e851130041c002c561181209081ca40d02c00300c3d10141450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 598829757 1250 598828507 598828523
    0x1051e0603041401050703091106032d0601090b0c06070e03030f18132003102303070b0f09040207080409090c0303110307080a050d0b040e070905060a150f0c 69
    0x10302858400030383e5002c074816142550901c4041849540280610f61500394405080066001501c6c2841216000285140c41d14030030416081c801c001c10404804400c400041d003040c0c1841d200c0009040d0704101d034030940d01082c0401030494000030102d0fa250300715880c0d152042c1d01e03e500000091541c0659003010301c00403000100720551010798180c0b58525001911758040320030803446180d045852510070190040306144c007940c90148031000440c0e110060592401020f500c0306014a84040c151a48011700043e0400c0031200b840e04201581c000c26404c00114034003d15020340ca0510300604c1105401b40740c002c90714004214102081c1e80c09450b120f101008008646d080016036200706110540100e41000000740400c100402140c0d440d036007101800745070130100e0008a4880d4085d4036030742e60380355680c0d20400f0b540c4c0d642c4c060550f00d1542500100001c07801c2042807411200d0181c9110311a800380354040050101c50700021104403041d0420300c020340c003c0d07801030b9000c0050460051000c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 598831007 1250 598829757 598829761
    0x10503040c0e0702030706150602030a052508041d0603030f0705100c0507150c0206060d11030a060c020c0a05030d050a1b06020a090b030910051509041202010b150301051e0603 77
    0x3e43c1c0000a0019076000b800c05001461814943d1000c0300040d00031440141c00820008070030314000d100034190b104415159000c81e00071040005506100c4240855400c0c100090400110382c5200c400160710a2a650781c54072400c0510000381d0740d200d65950035142e401c01184102c24440b05103c4000488210a824052044103140003072a07640254022107100aa0a045020140c09840750040383c1b62507800800c0c0f280c64040030004c141c0f00303050f000c40b00d02c82c0c1040300240644092054904051254030007107002c0b890448080e0400918400c100d0065100c100200001c0c0d41c0041c81070401190382c180651703600a0204200c5105c001381840406685004201c0801c20a03142d0007003841164031382d030b070300a81c9440d4030407140340384029109145194031079071388c0380c0d0204c1044e80515004803c80b148000c03020280b00120307414050480341554000111011844e0703403a020b00401d03101c03d20807514108076040400c40e1407a03e001c10b0150070b01800240080c4e401e00151043c52141d09200140019128 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 598832257 1250 598831007 598831021
    0x918150902040303090b161b1d0f13030507080a0302090d0503040510030212040b073608030712050d27120513030b04080d050103050d0905010815010503040c0e 70
    0xe0b52092004500042d0480b0700041d04422038015140c1900000745070a880d0302803070301c0b001c1000c03032680006040010519030005541c1c00007900c03131a291110b0751801c003851a01c890b0072170034410002c1c08010115081841140003e60090490303404540c04204591554207070002100240541220b0540290030040e182050280000280080302e404503105184901c9104c812011390141801004150700d561000c240021010500c460f40412649084d03070900605000c421004580f240c0c00004584200c9608540041c0248502002c0c2c18200c00131882c0283d10303138072440b03c103002140c5001000800b0a4101c1d401004d600318051401c010308030004041000d01c480f4400d850890700403030380d02c00e43c081c810b4580c50040f4240c1d102400d07075403000324441d0f10f55180c2c507103001c03c0204212040541040b01d1001d4506512a540c043c600500083c642c10f840441c014051440541007203061192800801080c1450007580f03c090400c00e04e051a05da455610f4a02108812600581c010500310010484a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 598833507 1250 598832257 598832261
    0x10c0803182b140a1b020a32151b060406050702010c020a02010f0c020607170c25030201032d0b032a2206080706080a050709181509 58
    0x98000002200b00c504001c0c900152480540000c404075642810f001000c4241e002c1d018a04450040090f121916410755000422413442500b01c0038041144a541c51a50300194400b10300c400000d0600c0b1000501c5d0200158207000b4050307114094801c00100b040c540c1e004414400f60f031340c103030500301d03002401c2c24a006005031008444110041d0301c2c214482070410302c0007900a8506030181c4512a55695200342110410744400c2c0598002804006910000b16401c090440c403140c044141d0751101e8003009481e003032820000c1091107a28501042551100301031840e80102c1c0d6090800195171125a010701031504403522741c8484544d130401ca141d108100c150069440c40c10103c094500d00e403400d108542412035216002c52080c07400320309210300c50410605880b460003a203c1041c03e0000d0181e101020f4035101d8202c168550451441005515004081950080c03409501840149444c150040c080c0c3c403d44500780e05c010034421900ba180c0d0b9240d004a074850b50b047d03510040c0c0741e101c4542c030340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 598834757 1250 598833507 598833553
    0x101103011d251d040c08011a1324210f1805010b0901050d051b06041a1c1413150f051816060e0f0604060e010305010e06010c080318 58
    0x12800d22000f10590f41c901d0b01d0f201d000c810100329110504241d003881004804096100100d0402040411448004a09012140c0000c00380360381070b00b0248040250751103100401003100414801505000740d075840d19447c02d03404c095001200050541810305508001c1c102060f4040703c02168500c5603424007006420101551005803031004141c0d0383c4006119545d12082005001d94000f801e00030105064100d42c8145400010b025a08064584580c085006048042e0545400002440703c02200d003800404515407a5604100041004020074002110004000f10030440b94100350320708100c0b2104242e83c64000c240000c0088407034107051140241010344501c000b0b8090109900072250000611a0302089000b03140002e061804406485041c003403c1c10a600c125081039840040c1c031100b0240000304801c3d0b643c8051241c400340054122881030f000b29043c1054002005016600f102141c1d6a07258401c00050380c0b941c51001c0200800611065032030180a005c402070118040070902c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 598836007 1250 598834757 598834787
    0x5090109050f0f1306090515090a060b0d03051813020c03070b010e0403050405120705041a0f0d031b0305040e16020d020304060c08090d06060602101103011d25 70
    0x1100c81e4440c44049050b5643c12a400d0324241d800e0b5040e400061a0307904900c5140d8440d50440799000301d44080d0240500c01140c519446a01ca4038100050007008c3c0180e04514070182e44003030741d0540310b0314018041c2c03046903011440c0540b0825440091b0b00e0f4100415040480e100086444200d10032590f0f4807644292002d4400010610002c64401500150f050007260305031603044c80c03d0315100901c02c4c400055040c0350690f01401500040f507132507501a210b1603006801860300c03c18036182c01c000d4400d50200f0510300030b01400c40780c400080d4004c1c5c0340300c96020750685102041503c07490212024420b1f40c00c82c0d0712492120382484400043d032071107120403d00036021382d11030b480449005c03645d0b03000354426080010003008100000c101f5201c024180030001802c1d8030000ca42c1522114151103c2d540880016030100440b8481030074103200f0f045000d0340c01c2c22907501d95494544804c12000003440e00c80046c1300c00c0d40100362070070380160340701c1200c0d102903d1101110900140141501d2401e00c0d0706 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 598837257 1250 598836007 598836031
    0x1020106050a0506190519030504030809030a0906050f0403050109110307051203090904060b040207030906021e2a0901060f031b051603022a18090709020703090509010905 75
    0xc40d042c0762018080301583d001501441c1020060400d48803800a802c4a100c01e0080c1000070503441c0c518103085c0c0100d80080d8a010840d818249130081414800a140242c03a40007808a900d4160380161b600c412541c90385443e5442e2094100306408508c116800181039610748002002089512201d05000c084102c0a171a5801e80e14070a00032044004e42880fa06a04100100901454440c40c9070340c1140c011803000681401d0b40340402c0481c3c1c421041503000c54040407080124035810010140f128140707401e6080c040407858840b03035175203c3d40001140c04500302041b003001064160a0024203000c020503c03000b07569a000040e210303000c8981c018000a04000c5c0781c41080e664441d030755030307080728540c0d55500e0031044c14a100c50036032101c0822000c5010b1701040342c2c80610300722440d00200c140c040b2014840c54504080080039000e1410720350300001420100481c088000c1840d0084542805015945800c1881e08a030f80542e942c00156006103510008222600c40341d2001e40f28000350009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 598838507 1250 598837257 598837259
    0x2c07050a0315020a0e2206050102031804090f06090b0f16080a02031003060f2705070b0c1005010b0406030c02011a150f0f070302060708060303030403110f0f03040501020106 76
    0x500030010440d000241903900103030b2089690381e50650050004500e1440c0250004260740c00040c3d089800045480203117820038214910340b0f0040c4200001441c0034001545031810b03a508c2d0303942682010710a13a22072640c0d00244801d01c010341c0300c20014646d215000700f2020004c5c0c80c03c00180c04e004c1d9800110280301c1d60010340703911542c000441ca4a407003a04d68080e165203035141600a0744c402048400240c60001000002a1389805440c140d040d2100001c20312204100740d009000102004100c00d01c0c8400c807000001c00d0010400d00262445001032581d196440b042d15403400380814400c420305403070300c40000b50034075206014000751001030381d05000007540c0c110101d00362080100000c0b40199011140211458034200301c0c01c01c640b24044c6181040003440c003c51840d002030040c001030140001d801420550306016003a4442c601e0b0401092600708000820b540e404000e100030244205080b003d0a038103001c00040700d840c2600001c46110500b100c000c144c0300e41003407044078003660a03d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 598839757 1250 598838507 598838509
    0x32040c180f0e012114060a0b19061b080a030501060e0409050606060c0708060c03101a03041b050409141225020d02190f06030203040221012c0705 64
    0x840311442624011030342006004113022045102801d4002d5440218200141a03003000c00c9240c8820005081a450103078440781c1902c09144101e0f200b801600190041520a5200c0104ad55481c1c44c0c086081100d01d840c15820080c450005090b410012500f42005503258000302e040e07818035640c104804080c0b0060100f0b98030380d2b40c1d008241c1e4000000007005800d01c1c0026113044055002155841f55803100700900300748040c0c0713030141030304000410410358016010040e00240301030380902c0b0300362141140d400103501016000070703c43e060031102c0c07042c1e00c140101c0120140400034010064600117240c9000c400c5208079060307290b802410145403040b880081a104803c10004603403507040c40405420003441d40c1820100c0e4802c40407001da0340940c4500151800702000c00305401c0c061070403ca410201d07175089601c042c1c10940100308000c0162a400420301103e680046104100b20f40031003814007600804a50002c02d041c06900c0c11840000b0803a0713180c41c00b21410503912441d846030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 598841007 1250 598839757 598839779
    0x1020913020708160305131e0816061803020a06020a060e06100314010212010b1804050105010f031a031014091c050c0f07090e0c0a32040c18 62
    0x1800290250b4018000001c00b50400860524043e00c06e1030210700d01a100303d5a07138041c400b5504907100d13040601e103101240c40d618141100140012100800101c0c0c0401a00381c40d0b02180e019803020040207017445050700600c000d08001941d0b0041c00e5950003501c4a070029654420010103680d86400c20441000444000c141503000310242d441a501160440d143c0c4048002e003808820140c2d94204081e15040c0048454140a891000041c81c1d4440c02d01c3c0354886000b03ca011b0381445546040c004000d16a0481d00412056885040101c0c3da004405e098800206548000d69054003400502500c102c10f1944100400d0320324146869046d240ca12002d50360740d40460302e10803c0d1080e001c0703050045000c0c20240030030703041e220103d801402010b8000e906010040d0721041441d5220001c900242005101140b410081601c074141c41d00e01d80180c0f108940032400000300c2c0c001c1042240f188141150000c1d511b444001b81051000780300c0520002c005403007440c194440e40f0880103011403511025 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 598842257 1250 598841007 598841017
    0x1202100e07050607031202042603030108100b4e0607030e070815010e01080120091c0803041211030304060b121c0e030102042912090102091302 63
    0x3000606490b410442030015541c0a4074090742800801081410296594001480901041d52400d44640108013040884142c0c050000a80b43c00a00040c0079490001800d40c10f01d1180d44000311b034405204e8082004840c0403000b43ca4014440c1808107a80846001118803008842076030104d1000814100325400e03101c4000034201340c00c0035000c504503c2c4242c1040080d013504605032510640c1d1181241e00d08200ca00100080a01c1a001009102000b041c3c2c0e038010100d0b08002d02c082a80b0712407112800c00035000c0c02950200100d800c003010345074180780406d14280c114030b03403880005504100b81c0300e1b001218201c60681c4006002c4040900c50280da04090803007c00960442d03c0c1c507902c91024051030401c46c3d8100c1c40f1101040440081000101c10b244044009501103c4001800a288441990000703002c1d0f03004200c100400d01050301c401c202d0004141c0e000c0084000440011450700c99405500c0079881982c05018010006600a0005110884141080c81c00c03010a03079041c2d0143d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 598843507 1250 598842257 598842281
    0xc0c0a0503030a17070504051002010519050f0601181e23030307030309050a02040c0e030f011a011206090504080c1014010b0706060915030209060604121e0204020403120210 76
    0x604e40c103498403400400c80d158100781e541c20520701701501c03003000c26075188030042c8000051b9100c100f4484145c03070707454400e0569107624805000629182000c2c1c00c4148001d80380720b04000600c284040200d5103040303e200502400b0128040c4104200b4494078071030700900603000c41201602e1032240d01490000100340866000e0051800d08610380c070160001c102c20501a40d03103006034420640182d403070703100d2040c0746c1000351140d0890240e60400d162409060751541030f8103a1522401e07964440d0b90124690490b10b00f407a00710101810185100f02420b074503440814000e082000780010800b1480241c4440329507441190042d05280f050030050791701d0081401b40c102c058000501800208000500105010b40070104000e039446109c901101c1071907000c0400e8904024040c4114a010802c03160803030001c81c0e4207070810b030410b0246565444049001010f41b4004042d410124140505080705030390024011901d80781c2e81c0c10401f8070359202000d8580180201c06490380800b0040c4204410400d07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 598844757 1250 598843507 598843517
    0xf0303112404060e01020d0903080a050408040510031d07061e050a1d130501050301060e1b07240204030b0a090f11060d0608010606031803020a02011d03030c0c0a0503030a 75
    0x320020000900c58028100f0740300c0c56154100e82d0410b41c4240001c18603824041c1c1c00045848907030a0061006601803d0b40e0706c1d09081c0818000803a540009803005e6940807288452800340c00c8000380e0090003903454000a40c0c81c50602c400e02c00d000407514000700c82d4070303454141e440720b00b10800c8041c1130340a081c050301003001031201c0e43c11940b113a032456008030104403203403440d14101000a409021001018030701c1702d441e480103108030f00b428042c0b04000c04110072070b1802d40c00d00324003280c4181d102155004000c90041040018400c14001c0340103004400000107102c210826aa080039500c2804280c4800351f41c17502050040d07145104005200383c0101d40f21801c1b64040e61174504040048105550110b414090304280c404544501c4000f050888000601117103001c07000b0b4190754800c01d44000da03c10071001e00020a40100b4072212966091a180c981d034080701c1e44140c0c03100d140820050b050300c00840c80c003240313210014203003980300e0044801c02e585690b6103003007595030321035403e024000803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 598846007 1250 598844757 598844803
    0xf07020a1e05160503070f1a21010e04230a12030b030d0c060c0201021c020d02121e060330040504181b050f0112090c0f030311 56
    0x682100d100685644400c1d2001880e80d8640c071140e00d04180386100b006a01000e503000c100030b180410807000180004c1c242525690b240c00d004030504548101041125000000d403103846030b402050b000308640c51010140d0300340d40c4038040c41d01090000c45c4c0448081200d519178403142d4107141c04e88201484444014140d4031901e0b03580b4640418008039401c20300d611501204c2c5103035014401d62007611810341d980003000c9094180401aa4212900141564070402140911055a00061000628a81016030754803100c4102130024864003202040381800e040030b02414803076615070841210b041181080301c40e11150f04264a8800a58040009060703404240751311855018240d0905205001d43c01e060075680e038085400e8900194400b00070100894040c1c0804c11048000c40c1034003c0c80f00d0a03000c0300d05041c04110001c1c1170107002d6041c01480b800c0300e039040d01c00b50040d6889a40c490107448916645da140b488031005140011000706810083c0080e01400014580040200a0325000e41030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 598847257 1250 598846007 598846013
    0x61309030f080916060e2e021b010c021002070b042c0c09012f06040b0a090f020d02040f0905060a0b01020102090306220503071109070e030d0f030209030709140f07020a 74
    0x101c1034014001c2d4000c2150f8003120411541f8681c002c84212010140c520f1110222a000b030400d2003e04000000d04220000081c0d40e0b680416104101030b1f06440d944e0b440c401c11002070317140000e1940010440c110000c0c0c0800c680960481c20484907041c0c082c541c0d040c2d00380802e0840e183d80e08a412880c003c1041c060300c07155600c620710007204881010750041900040e0f000c0441d50001c0c0d1040703120264000e0f030500040001e180380039a484218440d04106038103182c0d42c2c1d00200350b005100a40b0840c5000050010340d81d03242e000080c242c1c42d5800c00c104000c1145052901c441040b14140159032808044401a50060088502502d0010b000e0011039444072005084070f05d0151074134184042c10350384540016004c00c01000c03424080c10074598006050010014070020091800b01003042c0c2300c1418645407800030b0040b2400900b81040340041600c90402c42c000e0190861190707062080d010000b407076070200e84c000b045e68410071446071416074800140081c2610245c0300c030001039015001d21004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 598848507 1250 598847257 598847267
    0x15040f0513110f09010b120105010c0c090f020412050f010507031406041508100e0d0905060a2a030c1101030225050c04020d0b0907020708070b03061309030f08091606 73
    0x4802c0c4018480700d40d060320500811203201090b0002c0884110018804880e18021040d50703004040901e0b00fa0103880703140c0e8410075211460310030240b40588031019041440703443e8050300c0240080d600404061045400c00342d5031040900c0d0f4252265180401044100380f1a0003120030351026101006c401d0386903030b0240001070001c0c130100940c03020390000108400a06004801c1401c51082011074240d00902d030050410b8001c00b07a050a10640402c20001038403036030103464511907103042c4180300c82d07410200900d401c0519000c80d0007050ba4041007000b011380254001030214054540542c29510510040d000c074030450364080d40f82d50810060500318194401546a100e1142040d03664540400b408201030f41c00c1501c1184000f522081d008151f400c0c20740e42c4583c0820184024140c0d03500c0d0001c0203403034000394040e2402202000001883d25111441c101c050f1403140c180070801c00c0e5480c10b005149146001c803a40009200708045040790400003100c0180080d118910718071640f5000c02901c2e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 598849757 1250 598848507 598848533
    0x60e03010b100507050c01081e04030c0b01090e0f0d1b0c270e0d0504140109080a060b0a1215090f0f0507060210020301080a0206070503040e15040f0513 67
    0x5815922640800c40075100d0744446507001c0c6403910340b641c664490345001414168071290407410009400104001d070040380b0540341c0d00c144c540d640031501da111801d0849070821140070140c0300715418000010f880f002e542c000791015030500103403100345c4a5180c001c1c4c0c0f80d501110070303c0e000406101700c6681220550602101d150700c1503c1c4202410381d42c01e443e00541d0406408141c642005120760030b01115103000746100a003804000e480300404e0754501a0450083c1c0c090b42c184103140030504851039014111560142c100b50041303c20ba0049441c0007030140c011000850b01500b00084001200c002c803806183c21540d20a043c0d0305030850220800307000741001c1405680b80c0c00000c4605000c58046010602c003280560f014103805410903070064a0030150003401034015104000402040b880400ca0041301d990447e040340e540c0d4468108645507000c0c40c0c200100620241c0d0a12080f0307040e119031244003980a0350b040c4030380580e20383d101c0c088480071990a908070b44005e07183c400184004001c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 598851007 1250 598849757 598849759
    0x18030a0f080c150a02071205160b07020c03060a06050102010b0901031a071b1101200705040506030f0d02010b100914090402031627060803040b03062b1b060504060e 72
    0x400e1a01e0600303c60070400825140003c0c4154002010400c0c0447d0032404001d0301c4071410003901e0051180070460740d0344009030f0b010b09030f5136248022504203442030140c110580001030841c0c10500b00019020000c1407284a21405503103818040a02420300708241c504813034203c2d94006255040104052840700001e0002082002d0800200300085021540c00c001a0003400041c0c00310a14070005002045c00c00200f020b10b102d00322003c03640310740c0020450146d98003541c02151945030f24010911300802460861035502540c2103500d030301581503000700c124031412103400c1070040c42084182d130082054054024112103c0640c110641048010140c0151000e01152013040312194181d40c40700c03664109500d0b032503250450350181609400c0066983e00400400c200c0a45130140c00c680c0c1c0c2c4907520a02140090100003e0a00c0e80c82d0126090300c1c5825030401e2303441c0f0240840c0d496002094480450b08101c1c8042d9082609104480c2c50b025502c041d00d07860300d0941090350540b50804051720007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 598852257 1250 598851007 598851013
    0xf0f140108132409110109180207050a0204050c0c060604050f160212031801050c0c0a030807030b06040b04150806031e071d09100203090601120602091518030a0f080c 73
    0x40325000e0986004841030102d1440080c0d102101c1c40e2800d0306142026400c6d040244800007401001c070007000528590700111801651034a03a0700d416802e0110200c00070f5031041c40c20003005480508140245039144865054651039510002003008454080e50100204912140000c9586c0b441c00171681c4000818012145c4c801003402c008070031a40100e80c1e202145040c0f4840c2c012509003400307103030307040101621803d0625111140041c5e803110064000313000c115a200110304814000c0e40a8032002102500713060f42c442d1036029103c0140c4c0948580c10743c0d080ba18035031041d5184203109280c000c10000340039000b2002082080d10640700b41c2c4102141d140610300c0300003049918003142110010f625419881c151410b1503141e07003064200c03004103981031b00410412a0b1903d001c1099410748003a1000c0005100250803c2c400a0184500458001da4500c0c10340c480949207034058603580044402e481200c0307010005168a50504807001003146610024880010302c0c2d49e030207400d40001c0e040071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 598853507 1250 598852257 598852283
    0x30323030411130c03230c0a0509011107120b06010c1203020c010b03070312110d1e170906150a03020306010e040f21021b0306070c03180f0f14010813 66
    0x65021580031101301008681d40e0b003d084000c0c43d2007145032801540d45107102d1820303d009600100b151050b40d5284081140c0000d100c1d009030302640755066104201c100b100c071a142c4810940380e1640c800b9209650394200100000c007290310901070100c0305a88010000352024100c1800c3e0040d401c80c1802d016a0b54071880c8910441e10100f10440c01913001d02800c5d02c4a5a0301403000e401001100f820103071766000070250030086904201101c0403814103090360b200c0fa002c201d804443c1c0c0180f80580d01400301c560800d201d459900010035034042c2c44007a9020741c4032038003030041080d03c540a200094040d000600100400e401e002c180c1d9a03c50b0041e544c0440f424080e9a5031940c400e09000d4080d02039101800c28280694104419800b82c03e00107200c1007240149000641e4601c0014015010007490404a80c1098481c2d141d0120a99003614044074203030b260b50010500750800e016280105404600000b10640c3d41d9101880c000301c1070b12080c0c0d440c0c172805100d00400802c244156411840401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 598854757 1250 598853507 598853539
    0xa03091502070c090f09260f041e050609030c0d060e030c10180309120303090501020d0e0f0703031403040f0c0b07050105090c0102060705180402030a06030323030411 73
    0x500903944640100c3c10f22504001d100c10860b85070481c1203070810300e000504000901c459007031004407101d00c14120040154410b01e004207206005040c01c0200c0045000a8480080320040c1c0c0c4040443c030818058a440f20280045800b40b0b1164582c19805500200d5040c00e100f40380100042c041c620100c0e40e210644941c2e0315580c0000e2030081540e0040e0458804010345109a2164499142040720b0a032516140140710714014054071004903801d400641c00c2500035071002403105da00c0340003036490f00b0400e03d1100003003001c075882d101300740210401080c0103840402d981e016a80c0c940c0382c0c0303c0c02000300954803045d500010001c440180c200c40c010404aa10104804010114101c050382d41d90a0b618110382500c10240180b980d41c1c0c402c100c05c08481c2e801060b00740e0f02c1829460311036181c101c0c1c038411440e8088440304041d0030902c00070030310218040540011055a010346c40e00d50103a00181c071b12024949043c8407010304414180007040005440c1c0703800300c3c0281c2c0c00429074003449074504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 598856007 1250 598854757 598854761
    0x2103030106110c030f070e01170309060c03070b09160504060b0307052b1a030613150609090b01030218010b07120309050102030a0f050c0406051602040912021b040b060a030915 77
    0x45c201100300d0740105e01c01c0043d107100c0600140036040f00540040001c07114445a9564001c1022641c41110080b443c981c40040402c151a032480d00b0840000141c1049680c17162126844a0642030344070a014001c0380034101743c0291000c550610601d2403550781e482100310741d2034121840600d44100c018000458040b01107a0201d02400c01c40800900900304041171449800c00c0380100c0d020790081c07410451405038003810803600e65003240013001c90122401101000744603070b070400842949420308031018048010200b606030f0740b0035500070340044940c040d80c240c0c0c464244a401581d40b0100728203000501c525000110202d1791341008100c0b0582c60344c42c1c5080e0381086400c140f0741c655500c2400e100340c0803400784d40e421442402c44c02d0f2420b4140745d4001e00520642e11820707203091521045070210340300c07544501000c64002c1400b00046071001c10080d168541d1b004622034a100790010590540f800f03100d101010100146000d1400c03192a0050300500100c420503580380844000c2203841c81258 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 598857257 1250 598856007 598856023
    0x1031e020a1d1501080a0b0a080f01020c0d03050402090403050904110a030b13060b07020103020705070302040615030c080c070b0403122c0a0209060d110d0606052103030106110c03 79
    0x1c50800300b031003010450a00742c0d007070010030b00c1c0101c9031070001c2c441007030740c00000eaa6001080c03018085070352022a000309500380840c1d4001b807954420310340f4880780340740b040d4050480c00554105503101e50204603421000c1e80c00548019602c010003001280c0060b001c0c8000b04081c110240001c9400902055980c0f582c1c1c100c40160000720b40c0300c80400080c1c0c40c10300c0c030001d02c0350311b100000c01c1000d060460400c0c5034003610754001e05140e0b0000e000303001c1c0042088141d004580c010400d00102c0c0d26400c181d040540d00c40291030100741800d00d9140d00a014802c0648140710005115041c1a0103403640303e0100c0c0003801c1130b409c0c85484c901c00340c503072025806821012282d40034407841da80034282c03003000c1d500402404c4680c140c1103403a00e90016515201c02035049802112084182c8886040040b0500b10608910fa80032841a451034104115604244100c1d00221282c000d42058501b040d200c00c2215003800020b500104014050300c1c1c015002c0b2005030f0700003002c440b00c0c00da0100110f440c00500e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 598858507 1250 598857257 598857269
    0x11040e01181424010c110609010e030a03201903120e010c0e1801080d050705190309181a10020f12030901110a0c0b0717130308091501031e020a 63
    0x640101e10380038003003c0c56008129020b20f0000301c0101692102c80c42c0013030180744940328032800982610311ba846440300c000c4541000701603411a0640b0310f4068205900142460404608000c0d442d01804010442d071036012038520740705185072036664007280c0c8101d003a0301004940da81c034140000780620900c5604480d40158480049003409601088030140030501403500c02c2c0194001031008101c0444c0c0c0c03a40140711420125215801480c01506010800c0c1d0010407402c043d480c0c40c0d003031661102a60048400801e0100e0301c10080b6607454003a141d00000014000d82000060300da1818441203820320000703580b06513946541601c449900b01100702160003503c850100134040301110a101d985c0c0c0c0b142c40c62410b03505c3d0456010b0080c00f40c00000c4000b4001d607451200081c0c2d03250203a20304950346050001004d0751464840311f605088081a8002d40c0000c3e200f2000900350b10340011b01fa940d18020701c0d61a2020382c03039580ca6030602c000396180720251919219865005840d50301085000e409 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 598859757 1250 598858507 598858531
    0x924130803070e1201060602120a02011d0703060f02032811070b060405090105040309090e0c220b0312250803090304090b0102031c2f040911040e011814 67
    0xc40c03008000765046011060291130741b40c0a010484280c000841c48003e000343d00c07116403183c03103003007007a4010001ca003079103c030684180c03405c0d40f1400c0b0007103102c9096a1060f00300b000102d442251700001c1307000456000c0b030300c40012404042c92107202d5002035000c0d601001c000c6208c90b10a100220150481d9404607070380c13a0303543d0910410b4940f03401855484071040c0020001880e050310003c015200e94807500345219562110340c030302280c0901880d00d040d00040c08150810400e1580380f0307092070004190071030280c5050a680e88600d008118081803141c18074100c2e00300764280c001d03096110800c0c0c20304480c1d50385914030b02001404000255204412403006940c07500d1800c8104410380d0b02d6502c0c200c0c1150410058103000d900c0400e5182c604501044000415006d40555040030150f41c1b001008580c110000003410902404d0040c0180d848000b800d10030181420311001d0325004034040c000e808a400001400261031805089001c40c0d4803040100d0780302c15540045102003025104441040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 598861007 1250 598859757 598859777
    0x708100b1302030408040b03041a0f0f070905090721090c0e0708062220041401080c0702010f02071706060418021e01090e1905092413080307 62
    0x880c10600c00d4207003075041e031010341c5180b4207503950500c541710354018180103440200118042c42005054084201800f6040359068140b540701501e814070103c55a565039840b400000e4010382c403038085081200d0000e07046541503240e4960a403040c40b16000342c201e83d4400c110400d41440d07400d00908540750f000d0b8010501c1d903424401401c58a1900a204100340b11a0310140070284d114520074a0100403c040c00b050314000101c0c401c809041e0b401c03031200c90408540b40212200000800030f200f00e036000c50b0180d2032401904019a032105d0110f40354a80480244441c0d80554000da00c80203240d0014416110071507181d2920442510780d84518400c00d84c084401c00c541800d01d0303c5001070140312540301c00c41407082d586c0011108000056141c00e005016014040143d028202c024060646080480c1661904001a05100c08901124034401e414500428a18100401d42d024611407900400d40003040c44641028200e40282034018403400c05001c00c004503d800e00550700450f56541c4001e414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 598862257 1250 598861007 598861009
    0x18121b2b020304060804110a051011060112050729030106031406040204050d02130f0e0a0c0b090d03030225050c0102070e100e060303161a0a0207031409030708100b 72
    0x803629800365815540100418001d007a000f00882e035003c0d60100480140060920214030000b55a81c411038001d030143e101c01d042943c0000b4101e4400000808850b0580c0e619040c1114104102101a040340c00601061015884074282e0aa200c0d400e00b0400d03221050014100111b41c1c007d0b40240300180d5100c0701c510b1540d150b0741c0002d40055081300e095080c03900b4080011900c07444180001c0c031402c142c502218452880d50030070b44500c9101a0100201e850040240d5214503d0308021913504c1d00a01e0b01007400d60365001030f160140800b801c40000e03052185d50540095004034005074951008001c044515206421301c448650b10500140c80c00442e40c0002900d0150340e90019544480c00c501041380d01c03504822000c00700c0791300c3c2c48080e00507121100440e0551203104c01c426640900318000d03905001032085101100261000d12120668075010b00000f00d00410000a00043d070580d90300340003003115009440e14050060549030603e40c2c4614840c03500c20700351204101584ca565080c032a03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 598863507 1250 598862257 598862323
    0x120d0206160810090c030b0a09060512010204031101120905070b19230906040506030108030304020a0b0a020604030e0f120714040213031e14060a0518121b 68
    0x200da900300b00140d8145007100280c1080c0ca4000d142d2004d6494481c008610f20a030801c10201002030010b001250322035694801511541c080c16006082e42c80141c02100014800c6504503500440c02c81c0b035034544c0744011159844111084412142c03103089040218000303001200041c01c908504650362058140703061841c00c4601f100109100d01401120310a03e9040d00c030f070032140ca0035008580c2d2240c0c132030b00080c0540690f8000e20b0304403002000200d00c0c0c1c0c00001c0114043c40c0212030350030300380c0d81c6d6541c5480684101d00540c00140c0020001c500041c2c080c242c0410b0b404001012000c42540040206115009030741c0300340c17182c0d8406441007040351544145820014010b590551800c3c4c40303038180050300441480001c084008010f41581d01e40d4080c81d503e561294400340d0034039030101ca06007195407010183e4201c030b40c4e2880c10020601031050780e4101e001e000e1000c0c0c0030f0f001d0b54451000344c0503aa00070f45207046520180078a401c18060782401050041d441410380300c0c030055a03908007404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 598864757 1250 598863507 598863541
    0x130e0d0e010c0c050114120a0209040513110d0f1401090c15020a15020708071121101a06120f0604060e0a0b010507020d05010b0909010606050a0e120d0206 68
    0x105000002e980d03400843c8140c1010b006403403084c03c08103200007042d030600c10070b8811103042c5c0416120f10310502c00f20b02c1381c0d9001003500500454080c00181c4036107411080d6810840c0000f06242140d9180242d10f00b483c0032818401c3d8051010721810b80c0090325200c0485000b0310400300980d661381020020130810449040241205601c0b0458140d21544003941e201e00d07598006e401d400341109040104a810f4045440c1c4c0d56012101c2034464810385064441c40381c82601042c807a035130214190381500050800090290007440c0140b4000c2c0c6010f90010090000f0024a00c080d412148000d81d2900e80000500e81000310004a20f21442c0041c169802080003800d100d20840c1006070420920842203452600302c40f9201c00050a408030702d005803560f11690300029044510016030a041c01010f41c003000303440741d081e03407518819500c0341440e070700f215942d0050300003050007070240380e1401d8800c41c861428104041c001d40071592030080041d181142001c09507005a02c02c000b0001e03d402400c8040b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 598866007 1250 598864757 598864759
    0x30204090b1605190309020a0305030a0f0e0f060f0c01060b0c0d0e09060108060108100807090c08090c101409030601091b0e030712020612190e031206060702130e0d0e 73
    0x240c1841d071409114013056158420701c0c410181c690100509551300c02d4860002035510200700c81d9902c2d07841102401004801003008017184580490904178185460048030041e40204020b01d0400d00b001c00f445282c2161b601da0342c80390350303401007c0342540100c1c0050824400c42c038020b08002030940030040c0000902040540100340741d00a102c10b0303981081205820140c2401c1c284910b60301c1951265045482d94441c84080c882c43d0400140d5441030b6003c281e03024040c0c0d5403480702d0390324144c0044c1d54502021808d03070440d900c400c1010009108040e07903901c00d890340305803515020001700082d203042d20a8101741c8070b0a40d2041081d402c08040760500b0707080c0656041c19400e00003600000b0703459003050705c01c0c120100140a43c7d0402c540d502c4007201d4034103a641400c40314504000e4126080342010052005507035103030499410318201c00000756580303c83c0740402006940e4903001801082d800010041b600070004003503564000c1d145004403401c210201008202100008100401d001002403550b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 598867257 1250 598866007 598866017
    0xf010c0504050901030209061215161803260417010b01090b030f130605040f0309090608030d020c0106030f08070312060311040c1806080a0f02120a15030204090b16 72
    0x2003049440b03290fa100e0440c2d4046400868580d120004590f20041d03880da2040c190081c45540580800101d00050050051000e8049400701c680c2d000d4903404d66800c042405101c049100b000040c0c80ca400c142e1100030411406071165410110034087d5402a4204807410000364880c0400101c3c01d21840c8054102481c004c8020f501d4242c0d4183c9900c0701502c20301560265100180300c1c00250711050361840e41c003240c108500d04c1c0ca0305041d42441e810300412000544004800034841c0002c0c080c500540d040381d00a1440d01031642540c1c0002e620071004401507540322134001020508400f6480d00803400785241564400b024074008000b180503045001d0100c2c1f4082051002c500b43d05810185040c0940d00000da403280da03081600c800d00c01b03624110750380b2151103022078800c1c0d00140050196101c4902805000d02c42500da500340c4c011030843d421442c11240020703000141d44d0700a803103c1c190b0aa40307400d000e80c4a030040340035605558802e80320001c40c42c05011060300402c461101d550118030381 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 598868507 1250 598867257 598867259
    0x50903031608040f020d15050601050a17090a1a090d0c080304030509150d0905011d060f070306030c06080403110a0b0105061c06030302060f0f070507060f020c0601080f010c0504 78
    0x80c50000306007a195280070040090001000c0103040000c900c041d07a00101400142801403401c00038222165240d403204038106800306a265008900b41d80b044081c6e0745900c02c1d051100505400e110000400980c9140b06015220001c5010140c07959660a04208080e107a0728001c4411441c00f00c400510104002d0900280070200c4c4c3d00706d040d290003e40c58501390f642d403d4400002056405104050903103a00006880c4031096031590110070154407440c024032405245401e60001038180c001c280c541c0b0f0300f16000041016035405011a0310000c075090000303040c0d45075241c038040400550000070200300e00c041441f0071704d50010040007603c801d035030040001c02040e40e01c2c1c0389982c10622403a40a5040400c183c1059890443d41010303120b0000c0d0100001c07552418000e42e205020340741c481101411501048200e1182b41100e4400c81c82c4e9294146400b03426a41c100045c00844001a011075082c801140e00c2c000901c5064001d0001000420001c0b044448040c216010200c0041c280041000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 598869757 1250 598868507 598868521
    0x4170c03100f1e020901030606080f0a051f090b121c030b010201021204050105010321090e0a0e2b0302090f060705010b030a0c0815010521010e0d050d05090303 70
    0x340040486401850115103014072405682c00303000d11203848286001400d00c00340003201107034040c0c40c142c5002d07078091000543e5032005540d9060103442c80c0a42c078504000181c9035150680101d43c00441c0001100c0c000c4109143d200350b00880c94000349812900d03090031040700e19011058032004072411019004070f082d5000021640c140c086403010500da254060807415038001c0d0306980000011200b120907500d407a00d0942d000700000d0100f02c494500c1c4044110b80403a0b0105002d120008a4075544100d07810301134081a01c1074001d207044686a00c54220901480e400c1c0842d8841006c0f0803024842c03a208940400385e100c03941c2c2c40c8402014418071005095695900880e000c541007640c40a603541254200703c0d016019407e0480e40502c100600d8100300018070840030115031448013a100ca0400c51000004203030020300c01c0d41d600c501b810101c000b2440b03150f0300552042007000c000040c280788644110381819140c80c4000c0100740c01080410340308205006055101203c6c901440c51860610 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 598871007 1250 598869757 598869763
    0x6010e060703140d0c0503010812040510050304061b0e0405070f020a02210d020601030302010c021f240621050609072001020f1809060a0b0a090312030204170c03 71
    0x41e01408100c05010441d19001030348003220080f580300c1605004140b0b100390007604a81c801e00c10b43c6924845c0a02401810001005960540d08001c0101d5141a8800ca089501e80c0008d401030324050307699100720403940f000900c40c5042583c035449414071143c40004000071204020004028403112031140784e8071701e60204a503101c5c0f5034110b80701112000c10402d40c231901c0380c00c110034411500c511104109026000161103040380c1c8242e00a000030142070700100d1700c0e10306502c07100500300c0c55100120485249070f0401481c4541c03a040000050700d016254045c5185a0b03841600802c02e030810744140302d0212010407803800c400c46428045402d0910200300b4800005110000300320340c5900d13050300781c01d20304040152600040300035034884940c20345011055000360b0035402c00c85001e2041401a0030b1106000e4480c2c0c000070407111000e031520381c200611340c0c0000a480100004020048001a45e00090000c0007603d65001030300d413410f02c1070300321020240c0880d660199108448282c02d0313035400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 598872257 1250 598871007 598871017
    0x20409270203100906091406040c08160902070201020f070603050a32040317010602030901030c02151503010902130e0c06040311060936100f0504230a0203040b06010e06 74
    0x108000158290031800c02100410702d05800501e0941010405d26829000180d614011400703020840c07441c90717880d102c859881e101441145010700c0781180400dc01a125406008035500600582c5c10740840701803c1c84c01c1281982094010941e03800902100303c03501d20172035a6041540c008010300c8821007041e451103001824040c5503c4141c08001010948150007905244801301000d14182d41c440c14040d44980000b124180024030b0001180c0b280d03032000450155209101a042d14262640c0f03c0000c40e100244015580664840c519840107840d820b8481d040950010800104a00e900c40658284410340d1020752081c2c0091200f40041039240a5003013202c02c0884076950f640e14058003040303051501c0682e107600c03000c000710030255000c82e01c2d22001c110501d0050b000000d59640303494041c0c070700150150a05222800c40e0610a41c205031780311104101d00300c002c0f00841820446810054201190800b2146030088103110400007202c9900750494002d003400395180502c0000f290342c1d4050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 598873507 1250 598872257 598872283
    0x80a022704022206080f040308070e03070b0c0a170c07090218040c1805041b110316140706050313021306030501020a110c0603041214090301020409270203 68
    0x1191280d40803551a641141d0075200002250101c0b03084002280700410030604c03403071003c41c0810300001c0050002034040f52241d0340c1501d0720605502c842174201e071038420600b9402c0e05885000d00103d4031040c0d0b040500810039030103005240b805150b14000b55030824198880b004020300b4818005a46002316034082614a02c4100586a1943e003214002a80b01c401442d07402c81d280245000f0140d41c81a50100c10409110314404550780e90030501046402e80703100e41e15804d1040317501a0000740b149082600c480704040840e41409804003915680aa80b0101140e0646100c80c10300c240080a0086030010007170307428242d0031407401013048011810464402442104552848880501280c0c002009580c02000842d01c030140c2080107000400595443d0046102da20140071076860008100e03441580e122840810007a0f0107801660030503e030f21025141c50b04180281e001c40d0700c0034400f03480109401080420018205900210340315101003481ca00014500e4011002d80c5001036401050b051f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 598874757 1250 598873507 598873567
    0x20a0e0106082a0703050324061902030d0c02030c07150503130303091703090721120c0f06060f050d050706180e090f2803030b06040b07050706080a02 66
    0xc81e030294004540922204220303070f100410100281540308010b036101d1000c0c071101030003400c110003000c030f1400b00c002c2031a507212500f080303403190088005000080303440540c0100c0f07060014685500b41501c101d0180e041c010391012808141d811400c0002400410b1100140500c2c4102c1600041592000400150304803402e0156030003007610a03801140898bc000035604a815a10210007919610689850b8043d1140490110344100450b1484c5180c5034881d1078650b83c1185659070303444018000c4031403000e0010703528101c00031400040406041600c10344000521608100c0c581c06403c003140c003c0c80c0079a5119804d14006100051008240d40300380c1429002881c01181500261445401010905151005001c0090070010b61401000507a805540d4103654105039605615032541e04441b00851520310007001c030380680d2041811010241500b45000d4892001c254198031400f0200c07070035404032030f0420103158000780b0260442c50307a1200354908440e0070301080382c0e840c1040040d0300480c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 598876007 1250 598874757 598874791
    0x403030b092406040e07030b0109080c0f13091203020a0219030e130b150403140d051b03070b1603140702030d0e010b18041b030b15130216020a0e010608 67
    0x5651030342944c0003020040507110b01450708220040181048240083c081010f0580100d000d803030201e0281c40000014000d040e6400b00c01e0308000c01c02851600e1450300b60740c0c0e156480007040504c0c4241c0745101e11904d0250792502102d0f0002d02d0410008501c1006028450b04d4030000b0717911030340780540048110355003070b841c0040361039074401090704444c0716502c02800c440001c160340070300e400f5204580c01400728010310384d8104004c80e101d034000812400059003c1080b00f08154458042000c40d00c2c041007141d003803400030740d1000144401075410308032200e020141d0300419681806001c2d210901080800c0c1d007410310b510b02035920702456484041c03864856051082040003580304119564000340150045811000101c42d042815201501d098040ca402c22804040c2c0ca1861400c8a034066030700306031a941e01400310281101e03209004d0b4410002088040c00320010b0020f8403030b10703055803076044121050740304028404c0782aa2000c540005400300400c105508112220751247c00904113030048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 598877257 1250 598876007 598876009
    0x40209060f0307080c04050903040b0306011b02100512070921050a02030319110a020d02040e0a0605090d0f2604020607080406021006090b032a060706050403030b0924 73
    0x44480c03454031a0984506000001c1011340001c2e000c051000640d0200030545a41400a0301c1c2d03c500e0060115161082003c10701d01e5109070381d140010030615503c03401900103a400104020303040c15045001402c08908581905503041001c0d8000710503003403406003d0328198140d4201c0c0005035140e800551002c4840b0280a418020341c01d01c240e008003943e80c0e41040c208003403821410107034a20001a45140d10304800310300000c04140d101e400412039014000b40303508000141000d41c445d50f45501408221800042c81405150300070f2405070301411086800080050282c20500e05400030040301c41c00c40d42d034100d076503001c41d6050b51019420740c4440e951800400e025220b4100010304812000400003450f1f45d0201e0404c040c0c035001c1000f031225503a80c10340b07001030381c809448103645034200c0a1a5601307441801c1c40c065218180c00283e841080d00180000d8464009103401c3c0c40051700c420400040660602c200c3d000c9980488454006040c100602180c0040401c060341c42c01c01c03441100d600c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 598878507 1250 598877257 598877269
    0x9090a11120c280c1203240915030b01090203071e080108241f0f09050a1401080304030611251109160804081308031209060f04020906 59
    0x903004000040e10000d081c0030011000551188080410300d40c0082c60342034501d44201c07902c2680f41070f10b941d030184526003622803001030300400c40e411041c181c4e2080d036850608050091401604800e40c0c242d110b880c60f20940006507044843c00c017030041340c1d020082c40014803203c4450306441d1503840060f201d9035102d40036144407c4140881040d2502c400311017220701d5002203a03d0581c0c841034261038031003102c219009a024442c04201445000140004080201d513111008584c40150440e0910568032922200b054090f500205a2a41c60310100318803120705001d0b40e83d0740c1d41d04440a05c119890000416142d000342d000090001d51500801c02e01d02e2031503029200d40003110084001d1246403610128005001e48400b190014500700b28134030646814441e01d44128500c03100b40c850b2426039a01280c0c0311200a0088940100500c2260308103001c440b4004064042d040003141c3d521201070b0b510184a03001400b10842c3e922040030045e43d000402d10700740d085641683c40d83c03016100c04000400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 598879757 1250 598878507 598878517
    0x70309140606133c090803010306140c0f03040302011104180b030f0a03050307211d06061011031308010e0f070609030803190507020607120b0a05091e0a0203071409090a11 75
    0x215841c14680170b24240406000294100e9100b610200031080b04c00b09146d41880c070484030390400110600c948140140400025503006200e48000104501302c0c008c071400305c0d0400e400c01d8221044581c8181e40c02215442040b0078417a049000b48a2031108503801d9982d02081c50700181080b10210220320440c1c050701280b81040307404110303a03070040c1c208244000200f5200fa8040700100e01020321000b04000460000d01500300600712003140e00201e0301c15640c00c012061070703544d0743c8000c1014041100900c00004c01801c88600086003020b101c1480d589400304e13020000a40c0e40040008001a03500b03e00244c0869500c4684c1c16242e50310b042e0072024400e1481012a03489003040204500c007503012418622440b400d48480c00503952b81d042e0760080715000040d80d504442d00003800d10040c602100c4207a8061200700e254451109411100300c0000d10940b0340040f03194001c000e01041d682c000010f00000c4c1040c0541c2d07414600001d00182074280064040c02c0010340d1100c8131a1603040130812aa = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 598881007 1250 598879757 598879871
    0xb0c0f011b200109030e0108150d02040b0312070f140607020a030e0a0b161205040803120a1d0c10141c0b0303040605070c0801020405060703050307030914060613 71
    0x10142c2141000707406c030030091007894000f61040002038245504143d8111000f60050503003603903c41190300b840004c0c0274480d0561341c58840c20951414440c0c4410091403840e118050ba40a41c0c0e8030341c9000c9013207980f440c6020211342c015004000c0f4a540c00580500c4594052410070f06802040002c41c114481c0380c3c010b001c0002000075404007281c60044100c000300d20400d0141c0c511074201c43c08980d5801603020b0108030b0f400401285180c280300d160519002218035000281920400c1d41c1c03104101c81c080031441c03040d00b062039002c81c40d151140d01c0001056150030250f40804040d41401c1045c456010000c0c04210304600210b20340100e0b0b8086104a0b0014084a0351261240c001415a41010004958044100c000881c0c901410700a482c200c03030016014506202c1107607415905504000c040504044d6075000300300c003050001035007460000d003c0015010700d05001d4280f2804031522100c3d6200241080d11600700000d104a5044a003201f0440ca000001c020440c0362100f401003e00304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 598882257 1250 598881007 598881011
    0x606030212010219030b030a080d0f1401030302060109052205070504020f0d050c07020108010510030f020307030501061e0e210609061e0c07020607020f04060b0c0f011b2001 76
    0x50740380c0001503000b403150f00c0ea180b180380c4181c100013500714240c9107100c10064143d00003961543c00520b40e400940350380d04010f0000705c0c522001500340c1c81125402c12503c00ca041d8606c00400c2410b4041c486a80500281c240912491410140008070307a0481440305690b0185038454001788242841280081d100c01001550b54403414040c55100e6040454901903083c517100c04986000f06000071144019410303158000c00740e280504200000082e03002c500b06168079440000760075110751000b140706d68090384000400b541421b4000300600198480070520f400341e2040c07085440d07089105203401d80400c4880800d14021181d0300c198482800d8500511840354100b40321307a20001084092140d08040090311103480804a20f001100080d540301094010410480c0007505080000302401070001e071200c0814008030300840c00702c03112680b04580320000464003031030000c410700030103141c4e06080b03000340481c86a5200e80303d9650b9901c160030b0705004200365442403800c802001d0700c410100701c10003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 598883507 1250 598882257 598882279
    0x2003060a0506030c0d0510020307110d030c0338030f01020d060e100303120207020f030d0309020a291308150f2212090f1d151c06060302 60
    0x4400545016180c0b40e00c20300030051550910b0401e40c1c2491003040c2c00000a03e81500000322013402035001a00c0c0c81c080103078420000070240800c02c4031585030780c0356030340000b000b507110300c40242240d07025100d00204c5c0f213003080712102580c03840d0503200440441c1c10300841e04104081c00680703030080f1100941503075400441e0464440409601a0b02210703001081694030742e45100c181044414980030060202c5c40a40c820511b0740c00941c050501c852001c0c0070004a88200c40c00245400401c14540f00000c0c2c83d03507450011801c3c554449401007180ba644070109004034120380300070381c822086a1200b00408900b0559540200300c00f80004c1103c0c4007680d002c1c3c0305503075450300b00c2d41c81168407540f0300c4500c101007080400000150700d040d0321010100c641500f174507683c070088850700d44400c604106800c900450703001d65040714040200740e00c0c2e0005107035107500c0c060007001600082001124140e0095007000b903031500740c0c01d001c948415608841c0350a80c0d03460004001c0005400c007a4009488650b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 598884757 1250 598883507 598883521
    0x3070f0305191a1e0a080c03030a110a0b1f080d0e040b0d021210050702071208070f05030301170c0d080909090307051b03062a0f120c0a11031303200306 67
    0x1207000c1001c20203440c0c1a00e0301d5100c0701b0580e65100c1d0424550b030150700c10040c2903803151040302e00700c1d6421941c000b540c1e408446a11580d45080c0c055401c10709040d00c15011307194072040461600d00405030702d40034042810f200540900825009c0c0c60441c05280c0340c0510b0721180d80d442030030f1000380f030b801440c0c880790400079440c9a6031425000725a18513103180034045850a0b000041140407218034004030103540100e60740b14581c58100d04c2e012038001c26410000720018400340080d6003c1c0c00d50f103040c4201c452150410034030f4945a00c210f50301034a41564140d0129400b81c048581c19802070f9440c11042e00c485080d10314510600001501034014107005000402000c4940688844102c00320790464070f603881070300c10002c469030044460b0364030f4466034030401a00e03c015140e450002020141000302080c0c102c3c960b17a800700c030310800405002a0720400141c01c0b50160041c8809000114140040350b103882103000c40601000e00a00e1024a0a62102180c8980300180b1200075007612401c0c20441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 598886007 1250 598884757 598884799
    0x5030115060207091802191508010806131a01030308100b190e12010603050c0f040b0306060108070302070b0408210705090103150b0d05091903020c09060a03140303070f0305191a 78
    0x200a810001d20034140c50710310f842c41a0a00c0781603410405c0549a6a124112108001d280e925406c5410b440f11942e001c0c01001c2c0d0702c40b83b50096010341c0b81d680c000d00d0540849400f0200c1c6400071000d0182c203001c041944a0004070546200016082c5010300040c28000102c0b88652281400c105601300a030200801a0200d40d03400b0b00c040513200300d00c4100c000e034200410b0394541b800c0c01d9003541c4198005100e42d0f00c034011058104400d400d00615000441e1144001d0b0f25080310180e40c0780310001592240c440c01280f07124624603010010034000d040884006245d0300c038206445041585900c07000801c841c2c802c000e5801410342494469443c240c0d00740c18005080301b103d460109001d40f50483d2005456104084d14596040c0d01800d004900e0008200540340c0c00340070700b41c11031704170340700407000402400c0c68844a5050354000c0d6100c4c540068010140000d804052040600b003d060005001d102410b4100c0d01500810124940e48180e0502c005411004d8046030301c02d1115000d070080d84046 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 598887257 1250 598886007 598886009
    0x3021602040b120a050f01231603110a021c020d08010b0a120203010e1005060f0a2a0503280f0309051c05090406050607031e021002070c0503011506020709180219 71
    0x5c00c00034005580b440540301012238485403105001150040021280945800001d2055001e400c0001d0801d8014522402e140c0040c910a00981d00c04c1140040c1680c1c0310314200345041240c030040280400350100101104410302c00d0f0b00010340b000c520048014081c018141070b43c914603004549031340e962006030308100130503074400d01c021540c920041542e00305a0200c484015584480c00e00d8400a21412240c52111120081e040c1c3c001c00030a1151001d000002015980503000941d00d99401c082820310994030034410038115040e06641030720440d0082190b00403e240c40c100000c42401c281001030a0404440c0b010300e54600c1100d01c8080b6540110207020024001c3e0b8041148548440901c0b02030b108003a40500840c50a01c0311604000360b180241600c60103501c103030344840c40c03e040c0040a80c0c0283d03904640200420070f0620040c1403d2061002501c107100950f100a40787c00c502a4039a40907001d03c8070800c2c0c50b00712418500c0008509204030070340c090848000003000480c0346800c1c01d42 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 598888507 1250 598887257 598887283
    0x91e1c060b042a090b031303270303090803090901060503070e03070f0603060801050c030a0e03071707021e010e280f0f0b03041a040c090f150603021602040b120a05 72
    0x101518112500f44141c0d04c80f8240d0710843c117103074550348aa442602560001d00011000c100c0c048a0600710940095200f031800010341c142d6118090031842d0182a140a980100500760320902c413a04040d0341c2c08944d07504441c5581400d594941ba0300400311755a202d80c0070030759003601c912000080e09184101614044415554003048881d03101c501d1242605c0054170b003004c1040082c004514000250340c4100c54800c20201102d04d40001d658545005500c5460380500b1414045143c5043d81031410404007540c1394080491101e4003200000b0f03009450b1212043d003d44080c1c1d485035003812080324202c0003041c440da0051398140d5600d5045000c1400382c0542416450843c50001d140e10004c8152400b07640d12070b20245010b600305654585851004100341d03a0301381b442c2c0c1c00080b00d6240e441851404d5810316004101211801c2c8620820745c1144e000c8410513104001031003211806034003070303003009078101ca021503082d10f0300001407580b04441c240408036004001c100420490b00190001031111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 598889757 1250 598888507 598888571
    0x801090506090c0301150b1b150402010e420d0203060a06020a08030a020d020f030a0209090105031f0f02071e052503110406090c05091e1c060b04 64
    0x43d000e00f072500342c602009107000f00ca0658a02400080d00a9014009103ca011300ca40400e0220b214030514192007040040c541c0c4024000b40400d65070b0049862061180c02c0e00c810030b080024409a00745000300c0b080080e003d51032908150560700400c0810000c0100401c4060303161520310300e900e4000e50069503001d00c41d00e00032a0003d019400030400000c0aa004405181169202146c00c2d019600000b01d000800303030f00708026900e8a408034003950044524043c01030b10382071002c052011000040e045540b00303a01c26540180c182c1d21a1640301e404859a0002280702d82042140c034005c0c0c001c400b801004000070518104000e5030503505988164040c000302c400e092903c4664211120383c00d8049001e40016040038000720300324290000340e07650040d000080950361070b81c078001111140040c1d080010070001d0f151340a4645034082200f00f080b40c0e402480b030f9047e510300081e0100c1c11442d0350325001030010b62403402d104455200025481018100b409807250010440300e000c0f10365400e23003103252 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 598891007 1250 598889757 598889773
    0x10c020910060e0307030c05010c080903060709090c0201200c0c030a0614180c060306030f0a03050414010e0a030f02060f07060f05180a170705160603060803190f0504080109050609 79
    0x200d40082c5c1c10048a41226103000da0307505000044801e2115900140d540d40c000b003001200c952401c01503648103400c00d6841400f140c2c281074071407090b03503070441001086a0614460380001c508100343c810a070174013603925513a1580b00d00c0b403032030a02c0b00212007154140558060b01e010b101042c2c21041d034a42c0f0030080301d1a80d6a0300c0c50092219060602131002c00c1d404030a0307090150401e28000c40d0000300040485907085941d50045207090003000085001410110313042010300400300280007141c1003401e06101c51020207000c501c1c44c407420300c0060030100700320000c0025500ca039022541c05904001c1702a130f4035281307401c1c82c4015100019510019915140004034041d4640c0500b035650050314024201c190400e0700c440000c10074407841602080c004202c04070005408001040c10501840554207410303150141c0a412200d00e6030003c491030b0810041d5a01d0300400c4905607001ea2200e0030325004182040c5000c4845d0b004540001c5113275807074610081c0c144440095554491403507a01190300e03007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 598892257 1250 598891007 598891009
    0xe01201015150c08031510030c030b030106080c04050403170901151406390f0105010e0106172809020a06180303050c01020f12071e09060c02010c020910060e 69
    0x2030300c6502c10300d200050380700c6180070000356030b100110f40007001400103084902c813a13800240d0f1000074645c1c02d00801ea59200c00c0e082213805002d20103219900310000c1007418030300a01142c4030070b010391540d4480c6580344001820940121901090307250714a809412a18002c0300c20782c02000c00400c484420340006a0008450904d140103000300100a0292803c02d042d1400480350346184006500e0f114820358a0008100a00c110401c2e5061260004003011444a024a805c445041c0c000c1e16071444090014450f903900a03802803103074900c42a48051680c1c078806a20300705a84801070603000505801d143d2100030140d000302c40703034900031505002d429545650507500c000c4564019803040000d08000c20100340514064010f482281001500d86540c851a0020a80c40f00e240392a650030500107100707000d0740c085a580170b10f1900900400c6196062600588400214415982002032807044801164401c03d081030300c0e01c0d80031300342c4845400d00805920080000c0d00400e0009100380c1d898000c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 598893507 1250 598892257 598892279
    0x1401170606010909021b010c18090c020606010f0918020304140a11120a0b010b0c071d01030209060619030209030d02070f0504110f0301140405070f0e01201015 70
    0x1e04816110102c0b41440d1455400107500002d00b80442a9507404640c1d01e1a04280103e800c2d50020750758861205012001d4024115004c1c0c00c01c0745c58500e010184c104032030300025045c2d0044400d0821820b84d11105d00116465802a0403134202c204010380300c4001c13148103401541c0a0b0344140144800c40790300f10401580c41b500050301420401034402d0310355a034140005000055848482901c81025064543c164080001e0307100d01d00c8120001040d0780341e50401c0c0b110b400500044142203c00c1007502410b8070800c101804007034400c461100c04039800d90b542c8821100703c444a144200820002c80c040980290040c0d11076502900690003203001180c80480c00509544181040c2c4c0c0d80541040c0501008001d0300d03540d085910750030003164139200f4816001e036000b0f00305084000c3c4418a49404c1c842550701c06040801406129441015203582042d40c00700d1602007031800001c01c84008804400004505a0b00c0509001c0d072941511070600b9500003242c000c4032403140d00c01260703640840c285 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 598894757 1250 598893507 598893511
    0x7140606090414100203040804030c06090e011a0c011b0e1903080c0106030c080f070902160303111303030306030b01050105030c160c150e0108150a062114011706 71
    0x9032200c03070303840041c001a03800c0c40c07003404100e580c4044a24000d0f200a40070101e80c001d8509454004010070704100304490801d925005d00103038030700425001d203004900c0000075018012070742107141c005415024140c40d072041d40d8000c5980f0f0001e0020340c0c40c40c5180c00340f600180c14580c0018250148903401e82c18414505030054210452241d00780f0315540b80e5400d6600320504100e859502da80d000008507005100d0750014041900182c407402c1512101103240c005964804403001d401800007151610040c010680703000c0d094240031458980c0c840703040c180d0340f268007002054005200c002006047e8564810400e0764415001440c05980b80c0005541c81e01007104d101103c0a810030038211803e01c182c40b0808403910903801d40c4522170b03c0d44e00340c603814841517141c207000500303a0b420318100790b81c400410381c0c2000d4140002c041424403480402c80542460207800144015004100ca0a0280399101101c140d44038030104100c00240c002d8a0a88001b84642c02070075540c122404405103000c14414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 598896007 1250 598894757 598894759
    0xe0d0e0607021c021807030e0d0507080702130e010c0801050922030504080d0302030619080c1c0f0c050111010e0c0108090a060e0709140c0301050103111e07140606 72
    0x1d09101540d420858008042445580c540d12004848030040e15900c411035445011540348459038070340560020101c8486808544040c1e01c140c0c001d05000e5041001c486207030342c01030111a9665068004125032803013030003104143d18580401760f1080c00040d40705003076500b416a24450247d0385e42c003c010b485c110580c0d001401a002c400104800000b00107200c0b1524828280141405e946080903402c0502c08101000401d40002c10003401d407404030401041c50b80c4001e40e11200504080b0003654455804070100c0c00390b4140a00b013001c481c01501ca84e02c542e503000c10800d41c00c2d0b84910b8114040e04403480b075203020400540004605401c180100d00035290b142005010020085004450419014148401c1d900410603a100412003500a0101c8150b02c0c80c01401c5940c64480c000048648099800e8170720036910302442501c0c508202220304451007441e01280d8000028015007041c8203d010b403918004101c0080b04c040018000038000d000e00600406541c0d8000744401921030404031036503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 598897257 1250 598896007 598896019
    0x50c10060609062d020a06022106031609050c0409060909021005030411060304030c1514061504050d050124030c0911030a1e060e010f0602010b0a15021204090e0d0e 72
    0x20b03540e000c812110319139941280e0f00c101c40c01c0e4007131503c508080707074040901e40619000310b4059000c0401942c00d0640c00420590043c9604501d0440b00078000c4242c1c000d0502803a1500c1c0400d8900c03181340140c0740035045100782005116a501c000c40010071515204078000e4000f80280002d00740106c080c4c80c8610703007040c00c070703210109841c00300f047da82c1c0020800c40c07e00c18021000008074001c60303c1228602011280011200c031000b405411945009014610410341c0d00540808a2107100a4508542c020751b00c2130840703c924a4201e0240c0410440d100c058401e83c040041c021504200c2ca1040300c0c060340d2003014450311f5104000a5850116081c0750468007000841c00000c0c0c1580411345032034051040e010b20340740c2084548262146070f0300000c030030099500140103035004a2030b540010b01050008024003998003000c100111450b210700c01d84400a80d007418215030081c4007000303007848100e842d9544c4039120901d6200603c02852850000c2c403500c0024909940140706802980c4001404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 598898507 1250 598897257 598897307
    0x20a17030d18030c0f0510110d0e300c0a0804090506030a0b190915060e0a06050904120c051501090b0d02030606130f050f04140c0604060807050c1006060906 69
    0x90300380c00045c4210454280c882d1864105040344680b082e60003083c60781100e55980c000c00101c0d80c0940749580b01150607074010072003038103442d40142400c55001c10800051030484c610348950f203201d8090407107850701502444000c40c081080c1540100243c1c1d03003541040010341c5030700042c140d03030703101c810001040072007580007240846460344d480200007240c4a00114101c00c107030f500d000c5801004101c0140d016196201440044008110564031903034034642080036500d801d00003100802c014001034903030340281c140ca00300e403840ba0034924800d5401c0400c5038202800d0841c0d03601100d20134407440c2075041c41d020102a07146403c1c495203d10f60740060040c1402e4a1341801c2211581d030307200340711000716650034008603560880d0203464800c000c00784110322107103444d0030601c104200750340d80a251900300c03928040440c1d4620082d20291012803a2140440d604e69105540074491000513122622490079284071801080c1c0100c019904140d48030701d103040d41c9200649149601030342c003811408643e02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 598899757 1250 598898507 598898513
    0x9140d0f09052209151e0e0a02010f050d0510050901090c0f0e0109050d050a02041404030203030103080714060412091e05060c0a020d0309080c100206060d020a17030d18030c 76
    0x280c014550f081c03050001c1da10340306507107203001140884a00e10074030f034541c0000207221515519a01903c540d85e1014000240003602954039444050002814400042241305845100b002601c202c0d070030844041005090045d86c40012089604c81e00303208401c07000012481e00054000c500e8002c2d80e548540700e80c80d01c2000d090b01c500c1c0401000c1d90410030408000585a61440c201141c074074024009000e16402c0c90040c402038a81140c9030000b803002090030301c00000c1d0b00000726030440f5004600c894a46225150202045456080c17400462280c0001e0006120b07404480c0131030f9002070b0b02c404000b1903860550030740d00d4940600349605520805030421041c00c1000092425004140646a03821040d60000b12216800c01080c0c001610607017051204c60000c01034106100d4040750980d440030301485000390f44210081136503000c0c642c8500c500045440342d079801c0002d040101c9004403004510140c0950b2900918201c025403403c0514644480b64003403d1121a150140d40d803001c03c801c42d403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 598901007 1250 598899757 598899799
    0x12030219030e0309041d0705010e090408030703020d0504080901171b0c07030c080a03020106050105070c141212070204050f06010806012d20010b2209140d0f0905 71
    0x40e602030301d00042000521590b00e80c030a01c11b000ea1002130f00e02c080203034070b50368502e8140d0725004641401400041c040d015aa0342e100d0740c2d8020750001c002030752951001021030103801b409a14480440c100000c0c0420014801c1c050a010102070b611501461f03004462000129026aa05c0e0011888000c80002440d0900001c140e900211021a0f0b1101d070389503100c1441802a90007602540c0000306003004065083c0a008000d200918041d070920080e030300c0f00380c0f09103424450104140341011042c04c5035120b54003030203c0c04840300d007035800a5100c00030b4030403164071480e4101c8c0300d14680320014a2056892003140d01408060755056040d9441c003005468258410403001c03140144020344d0250a0301040c01e4407800341c1c1c140d035100c0c80501ca44004400c6183c407400e004803664103001d130151480d155206070300c0d030181285011003049000261b50300010320349800054190141c009429245d00d02c002211406600b90351f03038503a910700000004585090760350007801d84c0041c49002c1824200f56903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 598902257 1250 598901007 598901021
    0x10e1509060a0c080c0606010f0201020c100e010b0a0608150d0804140307170a0c091406040c030e030d021b030f0d0f0e060f0702010e030a0909051b0301121203021903 73
    0x40c00c1601150045442c4d02c0303c41d8008040740581a842030b410082c0650784074400c07030b207030321302030f0009500300006c05800503120748544064010140c0e44035542140c402c001d420103140b0400151131500f84549524004044500458444514070f2490741c8115003410600700b040d5000e60064040f074207240c249008c1e2a0b0004400300803035814864140c1c0413402500000d2008400401800203281480c1c1e58070b04004954040d620810400f0f1510b01400038101042880960140c411280002d030701900460540003069261840c10700d600c804200940e00008507401002a100c8200440100c0400180120340d28843c00d403809000310310a1104c1c202003241608240701c81c2d01b070010081040c0401c0d034403580ca0808106d980480b0f20800006101d49950284186208020b080001c0c52400c3c07200d41c40039084400a1068400712a50f400c005841c840ca06000c04041c10240d2180701d0f6203503036403004005200e0300a042540c0f19500500030701e14441c020f100315030440c1c410343c0d072801e45450b10901c15030040c804 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 598903507 1250 598902257 598902277
    0xf0604031202070e06090105220f020d050402040f02130909111513080601060212030a0e0a050a03020705030d12150308271005032206061202010e150906 67
    0x510020002520700542100344030020307402007850380d2400b400e07048000c20180c44180100300300001071003162581442800040321929010800c442040081c000a081000100300c040d440805c01d0341ca220030030b4000c10302031402140c051202c200521040d070300b2031140350760711240003030300318000c010b152170340d0300301808140c05030541403220546c11002c0b490425070f41c0c01318400c1500c00030701404440300810300380b0090b21308ac80050442c0d43c105031019560307021841d0410000d503004000100050900d070041442e9160400a5446082051400c2a0784280052049015000e88440800c00d41000a84c9500c108207554030b011020800c1d840c03840040c1003c00c140a0240c40f00c3d0307404008640302000800320301c840ca00d130790310340e00c025400300c1d881c80904080d0b0300d40b00305603000210001550010a03030383c000682c0b00043c81008400c0151085640e444070300202024104000090507201c14060f504a050007a2540c0b15800400b60420030405d162180580ba450710070301c2014018142000035001c8110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 598904757 1250 598903507 598903519
    0xc02271e0f1504020f09120607021b06090a0b04050108090c03060406090f0210080105190b19110f0706113405211e0d0c0c091b0908030a09050f 63
    0xb01c03440420160b074041e0304100040d130f000040122690504188411000d20348401900302410070381402510b6048500c4c0400075030050a1403040c01707030742c0c0208071100e25000820759035070306658601c0401980c20503c18a808a040c0400040da26800441e4920345000010050300150352543d032601c0c024224010241c44600b00100083c1c010703121a00c511850002540314444903602d4082044188500e20b5880220460700701010016030010100f80c0e902e1008603084640c40d40c50f8010116071860241e1f292440c240f00b0303a10010804000490103070142c840b965240320004010800c026030f529060400004031110b100807a00601c8003a9241e80c054110780001390308480d90711400140005014250401c10715807002d2020241a010043c0702c1e03c3d0420012820035038461841c42c2a00c41c030603101c90034140482040e15004105422107528003415400b031040190924205607070800b04001c85e12280402c4584401181c05080001503c0d5040d805903510b41d0301900b420f050001e820380380d0000c01d410038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 598906007 1250 598904757 598904791
    0xc0f020c150d0212060a0504060b030a1109061615110d150503012c0a15110405040212071403190f0b0a080d0206070905060301060f0c02271e0f 63
    0x680c43c0010841d08022100d2a011418020100084e6042c0c0f640b00c03e10413440c21900304481500582520f5000318104000500078003903051441441c0300e150720aa9200d0000200c2e14001e41c846180c6000140c02a903020780200b04015226044861750640484420000d0011214007a541e422108254402e26000728520759158082400d5550707030014202c000c241c03c1c5400c10360b03200251045a00440c007130010040881c0d941c9a03403881c452040000c0341e03455116056014a078078008111001424043c000310354403201545a0004880d0548170b8400141d041d440c00c032003003240c51081d00c0c0100414224843d510807940c80300c1000b005c05011000080340c45004070301059032206603410003019160b0241020745040c0394024140034000f4403000c10302008000034040c545500050f00e05407030050920440c01c50f10300e00e09407461404208000e6009900d480d00250030100d1204451192240710201c0c001c41c2c8402031362a003803402c2c1001803c41e49910400044182034043d507915000004414142c0c001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 598907257 1250 598906007 598906027
    0x1090209070906031b0f051e0a03231b09210703050d05041505030a09061d070603092a030b0c120108030705100c03020d0218040c0f020c15 61
    0x481085400d000882d802800800180742c01d03014441300c5560100c2210500031351110090f0201504124000402102080c00710070200e020200200d5035000161079a11440c1041008014007800028002d503008039400840b421003c00ca140da0041241104001e40c00c1825018025942c003c042103a6100301100200752040b10306022447c0c01111200c06040b0190441c00d00313501d441214a14031041083c01c01007002030b55400d403400f5044032410b00c5c02036174030b031240707075500c03000d07000403207010302106d28020760b000409440a41c04000b04045800703540c0300d41c2d80d40005400300e4504080140c800d8032119030343c94030b4101c510482c08900038803400b11030303401d6200d4603083d024840481d942c0940110000b104c0d2240d281d40100e03d801840480c00652420355140d03074540c0c80f0280c285620289688070292804170303902a80540d805e84a0382e07d421500e44c0c2e80d02103c180e5044825140c1c0340210320f01006020064031417a085426144030381c0083c5079084032841030051105600400d40500310041c010380403e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 598908507 1250 598907257 598907269
    0x612170a02071e0b16110d0803010302220f06170106050d06020307091502060403080f0402030a0311010b03010c05031005041b08060102190f020a050108090d0e0f100c15110417010902 80
    0x10040d10285058501240d07480c000d10002206c604040c0b00d601d259050b0400100100c04403810769074150344030300403600c4a0a42c285044264415a5845810079124401085003980001d08803030302401c2c90520320200c0c00f030345801c9031210701400750031046441b5440c01046440e0020340d044900f0303150401c000d41d0703644188940720395501180b00050b00914140070078590300400d030342d800020900b0071003400e0405900003944c4211607140201030005804068000d0f8000f98810200350002400070712810903150300083c8594012030302809080c0003010007084505240c807540828100c030200344014403150b01c0042e5100000100f42604501c2441d040c420415940d4003031640184c810444c0078004d145610401c0700c145500d030019810040c18004006c0d00117800200030205440e03d0a0491030220070711b010606000070401465081030b803c03074030100c0f4681e000030901781180c0a0914400f0011540e0000c0c8207440c109040b4101941041c002884504c0c8050383d0603068103012800044c0002941e070124070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 598909757 1250 598908507 598908517
    0xe060724050f1806061c0501110318010501090926070215030106111501121502031e010906030308010e060d0f0308071812080903100612170a02071e0b 66
    0x4055840280100306030b6500d803d402c40045000905071510308078000c1503030f45041021030341408811240200c140007007907100e070004074001d1038800e58034a00014544400d40010b024100107618207000061070444038410160010703400503140b00c2c06118140080020103448100c501c50b036500f0400e042c01651503201d540401101c403103406499601d08031000e00a40401100072040f41c000709590030400c020b2201e180e05440c900300706031035407180707504040440003c80c0c00300816903440041844021040a200181a40c409000d000c10b20303a229044032003950307000e01c802404181500c0051040d00180c401e190382c090000341810020700c00649660411000401065012402110901100540c412180074003051516099410a8540050143e80d54030b482405001c0d05c00126002c0d5190317806100f072009040c4c490b4030520050b5100c101103c21040380800494501103846000c007403410300e0fa81034440d0005180c02620405140100d91000200000c401c00d00d61f540000e000300d051515a40504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 598911007 1250 598909757 598909771
    0x4021308070f14010c230307060e030721020a03050d0f1b020c220203060613032111150c0405030a06140907030b18010b0a0e07030c0e06072405 63
    0x4020903151007000642c0f00300340321007541040448500c450202e901c009003800003060030072210840c01c02c08505a801e502076400000c03c501d040c000c0f4548026000005001c4a5026016202030b810090008000b200d503075440c20030240e00411f10343d1000c0390260000d054035401c1b61034080f40307000040300000b04031800b1003c03100c0740c090403507140c0e41e50740c1c0e04111881c411542a94a040d040c06014090f500c1c3c0701030340688860483d00040001d0898440d03400b1fa07480280400d01402d511501d0349840501c00c0c180800340c0701010424070800480600c039a10711270070040000b0140031a03032594050f110030184010501c4440942c20040003440c5e8904010f00400640121000240c450415015108640e005400c80700c1c2a44110018404984a155150f411051540e50103034000144450680984400d947c080d80c4000700c2c03200040c800f901201842d110b080d595901b00050040000c055a80c1407041c0300c0b01d500590140000310019581101e0490700350081c0012005418007061070005651048900c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 598912257 1250 598911007 598911029
    0x13060b01030b09010305150c0901020709051302191811031501020a0213060816081f060506130302030606030d0914031c031d0d210b03070306051501020a0503090402130807 75
    0x1100795041c3d22844642080625548c03e02d0a0f1009000035500d01c0c0c540110301559603160045403c866034589507000081c0e020381040d00325041f8041c1205e580300c1921404601000584035004981000d1103600741490145405038116180e01c042c0310a03105c14515418154410f035811440580d40340050910400e9020b2008a4024140042c0500302803c007100e41e0012000c0d03090500c103001d00841d4070078009400403c01440f003485148000081c0410740e101641006000a410004500082c105130541e0700940481d031103034890301c0a042d583c80d5071040d0356000074854007040c880d443c58802c0122180c107004084801e041868000385001281b030310402000b01c3d903208600c485c150009200071002002c403102800b1f000780d0116003d080400a100300d04051b01d4041c00c0710500e601d1726404624103070006800c03a034040392a0f2609400070b190a445252099140107000e049541c40040c040d2600713a40403002c3e500f0b000011003840080d401007005640e01c804a19030108510404102080040c0851004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 598913507 1250 598912257 598912273
    0x32909010c030c2d09090f020a03060b0315102006040c0b070308060103091a2802090607060902040e060705280f0e0402091c020f030613060b01030b09010305 69
    0x40e080f6040040040244842d11045220a004040c07040e10070001c12000365040d844003060031501061550444410702c0e14002c0224540d00c420781c003405040c500764908102c010f40380d00701c101c610b0000700c411140e60300800030049045e0800a4150b078019905050442501c04520a840300c40611000314501c41d40c807220070031080c003942c00c03110300c01081000d00a610307100c3c0c1c07070710003c182c0c8000400302414140c50708650001c04c805102300e0180c403074034503c3c01001c07400c00300808600e441068402650030398100f002180055103e04c00c0300c1c0300200040c1094981201581e0b07000c0070301110042039034440da9900e15660180703400d100d1244200001c2c2c0e683e640d14040016403604a0380e1a03201082d80100c0c0c181000d02d41500103856a0700d801841c2040000b1140d0000050080c2c8036500c074550b009000c1e10f5030405c2c2808815071111800e07100321500c000041d40a002d0654be00d10854000c0007004100d580c460105140c1c1c1c3c0206d60f52071040c94013140784101725002c240010801c0c1d0049903e50f0101c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 598914757 1250 598913507 598913531
    0x105060d080912011e0b0f060f0a0f090302040c03050a0f020c0703060b04090605070804120306120b0604060b0a0504060e030d020d0809010e06042f091b040f0609050a08070f03290901 80
    0x10183c003c2407c22100035003050159210b031000f90150013201d9061004214561502d180180e41c01e078000c5600800c1440446408000240900000e607501e451b12030500c0d0361580e10003414000c0d80c140419220007000302034a581c8404010b81140300209400c5603860083c4808a0018080c3c0c9104001035147d0422500b01807400e11032800d000c0011404051400509001070121034000040d19a0000d5003101c0b107480e185c000074014203e03030f0f02c0b4101402000070b01c03000c40b80c2c001d009441140d2940d155040c4a581c61010b05844c0c0c00e0901c3c1540060300544812080c2c06c0c080c0c1030a03034102c2021000010003602c0119451310300003003550240c0d003a02d021390818003a0588901c841c4000d0382c80f11141504051a28082007503400043c1404030000800703075854070346240003030550b001032102e0080c1c454016074421020300210558003842380a03500010003c1240303800000e0b2041105c6124141d8210382d45144c8480c441c03081c1203681c1c400369100005540c0b80000c1203044140c0034507031ba40b000060001c101d207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 598916007 1250 598914757 598914769
    0x1a10022107170c16030203030301140402091207060e090115032406030b120109031d0d06051812041a13080102030708010816060c0f0201210e0105060d080912011e0b 72
    0x15086213140920b81e001e20040c1c601009072070441c0c05071105503642611000024000e80240102c044e08840c0d80c41240014040c0010140110340091300c4807200c400d825400d03c4a1100240a500030300a412190405500c0c0300740e2005a0312810000c400100d8a0a0000d2002c0d40c0401d0b070022001a0700c136070006400e494034900200d188002c06000b008070707405981e40508110381ca01240b0302d612060400300e000a44440b50b28145184e440030042080e0f1510086180f81d002e80e0001ca181c01d440707a01308881e00e0031011401c44003502c2100b0134843c14003c2c850003555041d4003030300c0b030000005040e0100046208003400a035005441580f9441c550758108940141380c00c40f1501c1140c0b0703000001a040003041c3c0c10038440d60000f9084000c0809104403800165500b01c901d804201240141415001e51156542d200940000c400c1d8024801c5031140b20801a00304000d80028141030790410554846152144002c07101a1060002040d000c11210040084644a16480003501d448003d00d0250786046 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 598917257 1250 598916007 598916023
    0x1302030a110405010c1b05030f0f010c03150b07030926011406151b0703080703080112081605010608010f0212060603040f021c05101a10022107170c 65
    0x1d0010504191816000030f0810400070740207094400400300034511064401e5034a17000e042c0203030454100c030208411803941d0303d40322603182c1e2040d40380401020142d8882d000c1c034606084007000e06007005040103104203450344100c1c030440c180b10381f09500007101141d8058800034010b500b2506200701d0342894100d420354064036820407140e0444809c0010650f244250300d801d941518100c00d41304c040409030000c0d0002d40c041c414986109040c00002080b103035030028001d8a00c40d90b950503540e41d13034200d64444a00a148000c107165001c5c40310700d051560020801c44000e00440001c40c045555510a5003100c01d0080c9480707046030006080c5003201041c804460700210142e440b90710f0342c6415203070104103802640f8020710410030072600340c40760415012000940c81c0c001007511210034024202c3c03002094101201c0c6414240621400714600d0880c400502d11350071a0040e061030320510314050709500b07000381040501c0d407003800904045200801c8208000c0d500b02000c580c0c1320391110400d4500000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 598918507 1250 598917257 598917281
    0xa1514160836180c03070e040204081605012a020405090c0a030507440718060e090a0f06051e09030703080f09030405010507030e0d0b1501030e06010e04020a051302030a 74
    0xf0fa0400c0c00800c041140889a2003c218949204141542d40000b4080c0c41194070101a1340b05a10030f02c080c0b40c80020451086842c2629182c0c881e24200e400d080035040c1003003909800040c02c88105002d4142900700c15030164050f0252103c28051000060750815240c00036105035014a07801d006952004101000c01a19000203001c0b00c2c2421400c40b842c0c03000e41625158041c00e444030050002c0c001c00c101c0003e4850b221102c1d800e000c2a012180003811540b0510074407021304404070b980400042010b088043d0421011010301c455611014040d017400b40c814220044a071282c546a4026104241c0c0104ea204001c0c580d0380b001c0e400c006103008000b44c076040901c1d0144007807010b81040001182c048880a00380b00d80c640c0c5950900799800519004401e030000c61411343c40007040800001e00d0b1003000f41c0b4902d610002044001102102c5201c0b88903681a0301400c0140300c808450303964503501074401441d9518040e29480451a00d8005e41070700b1031100d03004803e200402d2114002d41c5000c1603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 598919757 1250 598918507 598918549
    0x2030d031a0328171b0d0815010e06040909030c0b011505042c0112060f1e020309010e03160303180f0b0601030b0a1514160836 56
    0x68265180e86111810000500da092180c43c0d0000c101300c92500031004a510216500d41c442e503201080504850300342d020070b00e06004c4d0300111a0110f0003059a140500da6070280c91420340c01001c019600d1041d0351034200c0e84600107000000d1001c0f80c40c040c480030b00b486683c50307030301c2d101c2c141c90200d0140700d060300540c141007522001c03821000d0384807050304c040300d040f1213a800810815400c05c014901d00b02508603040e0742014008180d00c881c400c01032180c40d20404040052900b51b10010007280d4510000400300c0850024a030040711075078000d55003243d89a8000610010070405192035a840241d143c504242e1020060381403507014401c0e9106100d407000342a000348419910551081c080910042801d00d007600407a50f40c1e44241e0002110f0007002c1c10084001c0c1e214110114400009800c0c04000b4a2183c0030101400401b0180c1c1c0000b65181505060030a9070781d80d24549400c24070990100340744003440c440210b0ba045001403082240b801e81240314504490510080c0b11081c028861041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 598920863 1106 598919757 598919773
    0x150706050c0a080f060105091905040c0c0c0f03030c0602160c0306020c1015060c03020a0b040f11090403020c0114040308030907060f02150402010c030302040302030d031a03 76
    0x50054075803034010b6031343c64110411650101d9243d130002d4000c0c0900046814080440d0b240c0c0030790940f4036000b954550011404071500c802d00709000070880c540101c140048401c9140207400c03456003041440e0b08548015190740c80025001700920303400914900480d039160b40c030110840d80a00c07891181a03990910030060f41020483c0d800d603001e408091000c4403054810301c415642e8071b1814000782d074a005401d40b80000b54000a4080d400340708090000170b880b80302d0b01c0d0720130b5200e001200e103900800d050598030b6802c140c004c0c1e4000c0808905000101b074000842161142003407915a101e005054181c111b0b601440d44001d00500011041c000e01c4c0d140802d520701a2600b40d0354036000449100c408aa494507101c1000d0f102a01000c0800c0143d4494107298010728080d0801510700307680c0c0d81c0480d00c0c03d00d4030f404003030000350b4a09415812059030034211082843c1180181065 = true := by decide +kernel

theorem cover : BRFrame.Cov 598741007 598920863 := by
  have h0 := BRFrame.cov_init 598741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 598741007 ≤ n) (h2 : n < 598920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
