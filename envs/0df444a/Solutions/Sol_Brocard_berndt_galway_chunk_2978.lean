-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2978
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:17.233685+00:00
-- url     : https://prove2.me/submissions/b5e29ba5-71ac-4dfa-a4bd-ffb5f58333af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 535431654 ≤ n < 535611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 535432904 1250 535431654 535431671
    0x70b0c0a050c3406050a110304180b011d0d023106060906141605030f1303020906061306120605180a240b0d0f020a27060e04 55
    0x11a880e1140c41c01d10b04082c49101c0c0c0081c1c1440c90701c4001002c0025001c0000341c401d500c07007409500c05016100303400110300180f007440813041c0605038102c920080d460036203180c01e4a60540c03030349a030201407090120f1551405141b21950b0004140030078207030700d102c852002852400000744030701c1e40c46000038058140030594065444c441c01d0070310303a512007614412002242014041c80107113094404c2c1030028000351000076071a40074505020f00380c801103014500e0b104056504050401d0300c4482216240700401070b0502c1052014064040c00c0c0e940314a1802c03192960040105448010b0440342c4107d100f08a01c0920340e0101c502c007402c4410f80c0c1401030f050200c60104d10010841035004176004868800340f00c2d1055000b80d101441009586420024081c805410004458040154201b0004022421300c41000268060052a241ca082c00315500c03c02c1290102a41c2042e105480402c0c9241e04d40c0c1814450f0034030001124201984480c02c82d458a1001050007501288190090741e44001e01d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 535434154 1250 535432904 535432907
    0x603020702150d1515020303010e0402010908150702070b090f0f041803050405030d0c03020a03050c0313061206050319020906061e030901050f0f0402040f061505040e090102070b0c0a 80
    0x10b0040285540082e1226400b2603a900a0100c2d60769084000000c0c084c0031407981444113000b028406240d0046045031b007040c00345004c2e140e000d4802d80c148101404001030354101040403510500d9003186802580c2070400c0082d00c1d20030b082d0002c003220401131200303c0880c0c5540d124040725141c01c50b0100c40f43c400c05004200100101f059409002410045400a05070000018411500260121014101c0006e0200c039041048400100141c000c00c401d00c020a2084002c0c00d801e81500055a2414442a002000c0b004045d0f0158000c2070381454400071011251003010b0040c642600a8043e100445070403001b4517040c000024890301907900840c507607071580d20a460300451500da561540400507005e04c00d0740e400440301301d0b030b03550b007400c0016104440c40c0d06c18a008207074804800546840c2d603801c21010348941005ca0841a6503410001514400a002c4402001d0030752070fa15a140e0416040918031180204000303040d0380100040d03400258600b00007030f8003040180100b41c98052500c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 535435404 1250 535434154 535434169
    0x18010509060403052d0f070201081b03040b042f1801210602070507080304050910030f08070218011512180f020d060f020d0b0f10030f0b180a0b010206100603020702 72
    0x7800e4091480c00310740382d0901b032110b900911585000340c0b03c0d4200d40d500c0b03400e81c0c0c2d076130080480000f41141051000c100052640008140c0040c820b6400c01e5200350303010310000c010506408105500d0384a40c81c0f0740c030310b8200040c000c03002c280c80280c949070301c1d81003920091000d1181c942001c03440e00000000001e0060b030b030741a6460107901209540100341d583c0d0715070307642c1d802c40e0145134420620304c00481c511000b20006501103d81c4910030840611083e00c0301c05085e04042c0050742c20103214100c2d0946040690151360183c0701110130025a4100050000c20050300207442c140307600d1500d03400c40021065804841482640540040c0d204100340c80420300c000e07401d00340144950705100344a8000c43c8240c0280541640820f0100513400c0c0200401a15a0740601d2064102901e001d49000f103c2c4650002c0e80000164880810310102070b4010501000d40417920511201b108402d001d00040c05000e2080b01035400d01c014042801c0400e840340c41400300f40304600a1640c00120441151100f0742c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 535436654 1250 535435404 535435477
    0x9061d0604030b01150c030903061e090507090c0207080a020d0f0c080a06290f031903020604020310060302060a0c11130b030607031a22051801050906040305 69
    0x103000944940d40d0b0314045040e0407013809a9a4805200211011128401c200c1d010546805684002040b8596290303580208402c240101e1a0780e4415881d40d4855003074014007003403510500040030140e240c904104100d6110055150854022607002c020004002503084031094045841d012101c070b1920780b20a00c0c58800c4001000003c1000000401039004a034a40030140100c40c184142010f5500c1802c5a1720488008401c8442c40d030180e44140c1400c2000080d00c841c040c084510305002c4800460300d5804100080303006038004000c000840c02c0900003000c4503000b10500703002c401d0442d40020124011030b02540200305544c100078080c08078812003032003a82005402c0903035080d20000c27200041c1101d444118000e10444021951140c402d124240c0c0c416000c00070256036404a90030007610154074011485290309488001041801d50710410740181044010041030141c4041c070603095440003840745204d6003040f010807000c260032108890454060706414000f6200f41c1c4101e40342c801502 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 535437904 1250 535436654 535436659
    0x816051c0b033a0212030a090c030503030a0606090b030106170a090b0f070206090d0801050f0607021003050919020f0105091807030c1713030305130605040c05010806060a09061d 78
    0x40460020340040e50030018540f0f81d14141e6100311012030000d0743c0d145c66040c00c044001400300001205202e2a03032011140e82e210b1003408055564949809182d0f80094410301e4006a80d103070100300954120700204021300c5520460307410745d85844009400c032440b80c490314100300b864800064035942c3c142c5c4007600f0707030303611404045040c241000b0003011004221344101c054400c407000304548403400546042040e0352640c40058a0b03080000f840b511403110003410340c100c081802041d00581d14110104081d20050354001014544440c200e46444400b622202c03100800420703440250b10381c205840264030f402e00b455a51400350001142003d407400b0105c0e40040000014449041c1c0c1c16003103034100041d42e6503141488010025800ba04c070505032003896008041e070b802d03c00064002d0b00040e80c429161b14941c240b8070010780341d002c1a910201c0f021142c0c40301452042c40250303004001c40342c010314141c1d10030703081c0146004083d18104950145006000411100e10580c10b240e502e00c00c1729000c003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 535439154 1250 535437904 535437943
    0xb070c0f060b040e06040c15030e010f0f2003040f08040302040e0c0a06090e0f0705040806010609030507060801120b0a0609021c0b01170a02130302060a0816051c0b03 73
    0x840c00d1801c0244000c20169201e6410f103001c1c0e14015400041480c01a900b020f02c2002c44c501c0d040c00d191241d42082ca40105058030b030955600d842e2828819600d41c0888000c010803200c0b940428a42243c40203801d07000e00488070b1103070001c1c2020300400c3c0c0782d005034450034086840d042400c0c030b445580110b90000390310a050030107514402c0f030082599090070340140c5403514000d0700c402e41030b281c880e03040c0203201080c09040b0010302d2100c0109110358000155041c980d14003903c4900090a01d0000d800480119040e00d004004001302004500020100c515101c0447e50424210345120f2084130b801501d44040030010452901e059448800200b0303060100b1035641c41c030b16080c80781510003041d4a0310450b00d8154480210b5001b02c00312007000c0d4004052808035550784441c03100940000a0402d840048100c02000688a100c011b29181d0095140d003622444c00b1560300c1071030652169030004000050001c01841e42022044142051241c0d0012a9101c00580842d2070700c51010600f4012842 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 535440404 1250 535439154 535439183
    0x1203021b012c01090f060c0b04020a05030a050312010906061202070201022d1002030c030c130e0406021902070303092d1d010e1608060303070605040506101706040b070c 74
    0x1400b82184003814400e0b2507244900f0395031030981207003941c1486003001003180c0301040b4000640111019070b010317100428080318a80c0381c40121b072402902e00011241503000290a240c81280040b8180c01402190b005003c0c090030184000c014403400c1030344400064000c69503204681c020b1101c40d02e9030740002c0e503210780004c0e01c0074030340c4500c00c800c0c03a281868000d0100501b84500c15001722485940e85a8040e0300c0e40c2c5940094003140d512203101c007038424031180c2012800c690b0a1000e20300550060401680305c084051448480504581c400c02c250341c0603140410000c0d07000455402121016003508600d894a20705900200c1d110071205182112100c2010030149410113501c11025600001385070305a80b41d1040000030002074450502c0c2c0c80e1a40070940c41c142c8618022a403241b030180c00e13281840c1681d502c0c0303030a5400695045446403c04000c003d9500026102e100040c0554642005400070907241151244d001038005400701d05010300113982d203401901010358031540201c02d43c0c402e25 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 535441654 1250 535440404 535440467
    0x10e0102010f0c18060c080714030706140402131a0618060d02040905010f121502090d0f020405071704140703080a0c030206460e01090c1203021b01 65
    0x80e2081c04003407540030780e020b010170481e128803508880c2e594401d000034030b0400e160300c03243c1d0780300c4a1441c034013041e100400c041b10004206025818549040da50280300303d003001d104010300c450780c100c0482c1c042850080c045620a20840c8002d48184080e0b500384c3d510707200707001c1e2a45040f1150301c04e2a0018000030302c0c0091980c0b2907008201b2070304104000c00540c0d881348070b001011038092098040e0790501d80140d03400320703031804110b2180032a103d0740186080103910218000c030b5000c4034150780a401654803001581010f020b510f60200c12031074511000f61411340990350700a000342c405814590041d01004829004104200145401c54081611400081001007800380303042400c81c0140a51782c04100c00b0410107440d420904070401070b40c51400010400744d000e03001d1005207031fa505108510321a11a064911800c0b19600c0c400d800800d100d1030900b401e541c460703220350021040d41c040340900c5c0301084c1c0c0031440c00c511002042041014101400040750b0752001700c0c0084025802054a07030600c030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 535442904 1250 535441654 535441667
    0x414120405040c21020c030922050108031e090409020a0e190c0c060f06170706020c060903030306010c03021006150219020f010e04020c030f0301180515010e0102010f0c 74
    0x1e94080710140300140ba5070001301c46141107060480341c640d1203001261480303140c0d5000b924041c0c49200459017000411800618000c010107100110076440c0301711070001034018000d05000d000348800a40c40c0003c101c403019a0741082004203109207102203411407050b0f4864008004454000b0a109039041c0c8680150b90748900c00e40301c03403008000a1031581504e00c07960054450102c19911240406c030907944070840508500d107600318159030f8034800410081c103080201040ca90190008000050802102a00d0311f01807603c0144151414050b0004654001041300d82c091000c0c49c244010b04c3c00391800364980f50b61518844542c6081c02c5020030f410f05140d2080c80300e40069400c4542080516030084072940300b50402030742001610650580d207500518204030703010b9000d0001031170580901407031411604401202c0c0c0401000000412610941480d0001c04120f4010200074a04003681c03031110000c11581100e0500079903001c4101680e0003075004c101015070343e00090110100000009205 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 535444154 1250 535442904 535442909
    0x50d06090501141c15090503090901090b04060e0103080d11070f1209150801033f020c060f03150409020603070201050414010c140f040b0a020606010e04051303030504141204 76
    0x180d1031880381d5403241d220604144c004280c12180c020500200346410301c0203840707040800c1d20144030400c291810b03521035241050007800b800c1c800203181c08000c0c04004c00c4e00c1d8154480c2c0008246140140b0104044500311408000c0c120390000c1c4489010001d881070b80111400903151700414528541840300307442564000418607079035607000c00d80300e44400982c103080b00c05440c001410032005000054181400c1e0041d07403940e580074602446400d1400200360400280400c961521021540b01d08e03130100154500d00c0004c0300c46600703000441c01100258000244010007181051042100039156640b040f19410307000342950ba50391404140185c0a0402a0340494024051400101d0125010310418940c1316142d0340b00c5901c200380c1c07400100d80e904682101c030180740e002c020000d100725242e002400245801e4000e808186030040000d010460079206060203241440704100b82520284a6900002e81c54200000c10b0303210341c104120080241041c0075600d204800070040b0201c0354030090b108 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 535445404 1250 535444154 535444159
    0xe01090f0203090303060d1403042403050402031b1512040507050609030a1b09020a0f1214070302072a051c0c0b0f070501020409230610050d0609050114 67
    0x100c000350001410403440226102d480710381007480480d8462034040340c62a4460300401844c0308402c0340c610b443d4250b51155021800a040403000c0e500c82da4203101841d4817440780d5080802c001c4c9004d4000c280c5074122201020508103d80c01101030f26580e8140c4c1490300c0100b08111501c0350750b203411030001103800b038600b40c40e1032184400c0001c5518080d41100c40d48a00a8003802854880d60307281340030354040600c1e4811120f4a42d0b40070800746501e10103050b0760120baa8070b28200203090130b80603040100462108410600302400d0180380b10042000c02d800102d240740040e039032001800e0041800c4515107032508541502c0340d410009000140200f000c0d035604507069807a90058022402c2030040d600c5c80101202ca0200c01000602910303009001d0f000c032a4408149069180d64995003241e001c2e07001041c007135688280340c00c002000e070700b2200203c5854064000c080e04206000a6034511003029400410030000f490384080c0c2d5242d0800002000440e40034407465031101084c805040c1c902c40d5160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 535446654 1250 535445404 535445411
    0x1e1204120209090601030c14010507060e060103021804050304210609060c1d0a171f0c1407150506270714041404020a0e1c05011a0102191b0e0109 64
    0x2000c0d0303d4081000ca0403203030b0000c040c000241c98000d03180c00e601c0300324803407606100f030a00207400850345a015010115040c070340038000540c1184100500000c1c0b138010f5012a031071000c00c1000041c8000201d800342c1d500745000601c01c0d204a1500040c1403030f601d000404035410005030b80308001c02c90f000081c900b01a603c4440800c0d42d0203154200c8200c0b211701181d03000e05540010030202044844203003a019562090b203c041d07101c4a000000b000b0400d0107200b4166440c0c5005040c643c0c000e0007030708010b20140b40075140c030490f61102140000002c020300300003962000414804c0c0e4940d800e101d9054403002d0b81602500502c00c440d00c481000700c4418011400044403894181c4441e800c45040d41c5164451002d0300318100140b00094008001c4182032010b510b020a0035030340d4030003039802a00b0308100035100d00003003031805ca801d40b50311f41180d108102c00b100c550308080c4c0c1c010071a2456254100030600f0303c000396040803599100341300141a1034240400703000c940d403480c4a0f041c0d03050b40e1000c517003803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 535447904 1250 535446654 535446661
    0xa0609050615061806040f120c05060702090601031d1002040503010506031501030b06010e12100c020303011505030c07140304080d0216050f0d062309010902031e1204120209 76
    0x740880b40e55616615440141009030503a140780b10080b808001401810450400780c44100f08a40d00c130007900b009032001014075000c001c101c0c0c5610344070301601c8280c50150403c0d20782d601007441003d02600007418107440b0300140307840c202595400c5040f9198075040b03e03400c20441352000c0080d0f00c0b6002c0c040c001d5003000002601403c0c0003514925012400900c200ba5a01c4d58840c50050031000c0e100f01e0400c000c815420708540c1c2d86410454001c05801d0207081a170810f410150200c83c3c11000070340641d00244010019596921080110841c072405c120340d0300d607191040c080711445100b20080c12290303900301c500c5d100e41001000d041624840401c0b42c1c2c2c0d06603c4c2805a03580c100901905a40e100d2803007042c0038a08100407080810320020b041c4001840665942105540302c82c48801001205c0e410042d03c0c0500c81c148050708260000001c0014200c103801180d10b801184100101c1481200d0b245440404208090404182d207000d11544840d1968010f030228a008003050f40b048a410010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 535449154 1250 535447904 535447921
    0x1021c05060603010501080c0d0b03010219030f2007111216080106030827041a0f04020910051c0c0507020406081f0b01030b0d141207170d0e0a06090506 67
    0x89078145c82c0c0c161142001c075501c002d03d0b0b0f0350030f81c0420948000c42d0303260701904075151001d0020704449010803407050a20a140c500007000c40c1e0700760310300c54842c2e4140810780c68000caa0010728400c00c0e07121403a05070380c1e401c0703410007d41903203a200005801000c44a110b005000000c0307041c10800281c804ac46180b1a501c142c25030030707200b1900014041030300403c104507146040d00105080e03004412140c00c040300008000804071040356030b130080514003038000380e402d528051000c600321000854046040652220120381483c1502c40c0000c14040001100b400081e40307903911640600c0b56000c21312500155000081054100d604220f01540c10300174081104040410f5480c94546041024502c2030351010040d006808080c1906050559405401c461500d03094640c1c000340d4010140c071181155503604c900d01d0120702d412085a10303102404a400003960490103082c945860b030000d95201d0154a51f44c500511541e0700310320f00340c802d581c000820001b9680010324124051019100598ac544c041c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 535450404 1250 535449154 535449157
    0x40606050c1506120102030f15010318120e1005040816270e030406032004060503012c1e0f0601091208040e01030309180c08180a0501021c050606 64
    0x1106112604401d564000c10341c2c0b1204440d5200000904c10b07410102019040c50072a4401d80b1200c101c50b0b164020040600e07004042c0300f1901034207207820001c01c000c48404420b12402c00c0c1000b41069444100031660500c03641c00601c5084c3d00410700c4074901281000501075a11610492001c5d000d84d400c20444034030700c0941c03542100c6a861203100400030600c044402c15402050910000da9600740c0000c0c18001003025001030640c684002407a4a000210a840c0100c0740e908001110400c00040c003d5562000580f0304441d401c0c0440300440140c2c03c0750400e01c444101900356600703d0340c01081160000c410780f8440c41c4511022040880c1c885c2e13030b0366110360001186c40074082211000100308111500d901c1003401c5002d0000c80781032544518815100807401ea105400203401c0a406110a800600d80c10a45103d81c80e0100942c150343c0a020344510700c02811410350a03000f090812030401c0a020b005101ca5011000b155030b011a651280030341d844503000d14403172a2a0100080362400d2620 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 535451654 1250 535450404 535450417
    0x16030b010905040215030405011416020c0607050c010f0e030d08040201081501081305032a0f01022706070507240207030510090201090e071205090303070c080306190b0904060605 78
    0x5d00d01a00183c81242090044c0e102600c110350540d41d030001030440c1034000130244e0055180d4100344034000d0000e64024030305000d205016100700c030100041800582c0000b5102c2d0503500a003041458803030007400958886840784401030701401540c200880c4598001c1d005442680f00345c07540703140c075211805048d03944203800904c3c90104018001060701c1c04141c1010400032449541180e00c2e00d0810007410a1303407903c11545840c1e401025220309842102031150b0f90008010304021030a04e0610b402082482c5004100400c1482001c0c8004015032201c9040b981c00f25005412582c03142c2d5601100c0301b030302d00c510340f5401c181d07400d503441115030910224641080b40e07001002054101200c46e1108014074035003c0c00c0381800740003400041c0011b443c5044604ca85142d442c1c0f0b0b18120240a920740c2031b60001080313405550010001c020141307810217602c1030000e800c412466165614640482c2010004c0c110b070390181c40302a5800901c9002040c020003041c001610207000065441005440c98001c44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 535452904 1250 535451654 535451659
    0x9020312030c07140307050618120702120f0d0306090b13020904020c0d030507080a09030507030c03051e0c1605130c020a06050c0d0c0206060a0303120b0316030b0109050402 76
    0x55140c40e0026502406940c200c4140910540750400e15903074069892860040c00c07103160408100201400340610100380c0c440007210591103c480315041c55038590007403a20300903160201040d5803055403180c00c1c00d406036880701c0089a4000400901b615178451215402ca00000c1c1011008174461840340130303142651401809030080e4105014070f00001c1d420944585030426030034410124040c004008031a0800520384002485041200006000e084001c1c807070600710713062888403400680d21204450100760580380807070003480755103030480311031242040e643c0441c1c00d14043c04c50510303270304da001302110300440040321a0041402000b074903000482c071804e07611480709100211504000e801c409142c050500c1500c0501600d907a684003220b500b0345440310205400308500f000e40d240e5200700a88582d4600041500d882c000c400109120038a020050410410300c5d59000d4080244c4c001c0810220020240c68090741c240c804129400502e00c8255418031070500000342100d800d00c241401035402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 535454154 1250 535452904 535452913
    0x3020a12031505040b0409061b23040e0601110d050912060708130302071a090906090402030c0607031803050d14070309030f05100f05060315090721080a030c0909090203 74
    0x1801c3c10040284058101c00d50403640f6007029030001486480368049540100c10005107070f10b045d802c0100858585d02d416903070318120410300007003541001c007501d00302c900d400c0e2105190740c5c0d0703100101d8094110320310a4240303110320356566400c20741190191a0009050b0b80d881c206065000910341e541d641925035402150046002ca40054003000e00141d0740c3d8000d004481e03410b65586903503800740c08088200007103040013256004861501c00c420703d400001c1110081d2550501e80c0001e44c88440032615075209070000a0680205030282501c0018002840d9201c0007443e5a81013094486041240003000901d600d4121a54001014180e600494142d640c8810082c19607503042d0100010841c1500c1a1040c1e419204042c00c06002e2a26100c809903408152810704206051034168002000000c2510b10000c12146520029803041140c02d0409800102c242007815007840f20300f4480d01818001d00000e0b1003c2c0d0750b030150884c82c1c0500702640c620030032561340c5d241d0100b01c903103400d0002c0d0300d03412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 535455404 1250 535454154 535454159
    0x10e01060626181e01060f081b06032a0a2a02061b030d0c090f1211010e090f01060825081015020c1309081905070b0403020a120315 58
    0x49020b000da8405402d03901300d46004881148208501e0314000c810001c40c1c0d1900024000c43d034a10220740d00078034030000101040b001d400c01c00402040301c2e0320098001e59010001448200607818031004054400006414600040c40c01c585070703a110703c54070720109100c12008840844002c44020100c00900403414032040f4590030810f5030750103440c50000e5908294040001c11005000800003600d18100016807401c04001c043d203403500b02d910004c415111803004000e1031080320441030b04540d1200344c00d089007044034010b0303508410750501c0e20f402440d641e00b0840d000700d5110140741a525540c6410085030b0303600d13080403402404003030b1920302066001440344125024442c40ca801c49010340003100c0d015200c0d82d1a50724801d00051601c0140c5c004c0380c8040081c03e1000a41c0090307110000c00b030080e038600ea01c1d200b0340b031b100b1072507448942c3d480701d0041524280305405445c05554098844540d5007040e040c001c5d5500d62a280944030303001c9a580036000c2d64020311503070065801c51243d4528492 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 535456654 1250 535455404 535455421
    0x305100207020402040f0b0307030e06070f12140106050c010f0c140702120f0106030618050304180204030b190b01020105040b0711070504020316080a0e030414060705010e01060626 79
    0x4100801c12038005409020108189045101000103090714504d503c0d203d1621081c0101500c100341800505600204244450f55511a16029440780d1500b04102250320040d94000205201c130b02202c09048440004924140d0001c01000c01c42441002407044030013a5003d0b03811600c4c4941504085a130400d00c42010749001c001404546000030448040304c0b40c103442560030a076890b82040710303c0c1d40d80e034010300401220740b0400103440c920150445a15031113075207280ea6480380740118407802c0c0f540319140c403072207010b901200e01469000c003112160b8140b1030914001c02c440026601d6406040000140c4e03294814414140300d6a003100b0141150f4555140503100c00d18950150f05150050500215094940b4002035000312242000c04010303404482000b0000c0a000e00b180c2e8800d4103107041c107500740400100740e81c25158030142428491000702c00050403403241800040071942014011036201c0c1d41980f10808035035580d1180c0d80240c080300c442004001018401c4403412025001041c41c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 535457904 1250 535456654 535456657
    0x80d0f080403030b1f020c1002282402041503141801090807050607020c03061e3606070c0b1803070c0306050714030408030f100f060c0c0b0403051002 66
    0x4440c00713001c01d411303514140c1c4880920f0242211400c00b507401413040c147c10b401c016220a61b047d00f144041c220004040e01004005808a6502a035060044800b402401500c540c804050095114440e03440400f25002c00040d4219200e07203485c0c0040c01c0e165812460090082040c0070f0441c9000c102141e449050040c60b05180040017480e5660310740d85200090440c4004150b0680a4070017840345140c4030034001c2c5032101c2044d00d18000c0d000790307080c0170450500189130500d4401d45001c91030a079543c840380d00c58000788a8040c40800f00c1401c0586085225082a480400b0843c01602e4860b59580d40c103850031821410010300281c8200002a180344000003003c1070f094888056a2074600701307459034403400140e90400d0392001d40e102c0c107014a17290401c003000030743c80b6024041e90861410752549003003804000c1c14009201508400603904269456034403015000c0c880c03030183c0154807108010240701d14402e0032203020503030300e00200744202064281d504480d4800003c01007582140d0a400c041e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 535459154 1250 535457904 535457921
    0xc030702040f11160c0b091302030901110307030905010605041a0904081620010c0309060e130e070e011e0303050f0c1c0305060901030308130c031209080d0f08040303 73
    0x80e83c0e07501003495076034041800501d0205003101c444010740902c0e00f000020f0804680c41400c41c2041000074400503203410644a140c62040c420040c0c40f0f0350784400303144c0501007120003020003c100004000b80107800d43e1141c480e1901440c000c101054880c4113200440d482e001c5842c41c5881414040300491601c1d100441d845445500c8181c00d0040380454a491913251050032210b003031081514000c0d40c8440c2c5512002c1010919100c8a40c80068501800000c2640214410449880302d803010f0340e01c3d505218070031181da0400403c81d528441007080c1e00c9050718042c06c80c0408255000180032402802240032024848104080c290300d581e900347c4095001a5000c0e24111090220b4908083d0502c0701c0c0104660301c3c1003a800c180070003103008007280c2000308014031500c1d0307400c0107001281d030102171264070a034000640c88440a0600f4015522036003a40000c28800410710310030b180507404120300d821929a0f00440e14245184802600d402d4913840007407002a41c0768002401192198100003003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 535460404 1250 535459154 535459181
    0x120e0604021f09080a050109050d02010501050108010e0414060f011509051003020a1b050d12230a0b060c0a03090e010b09040f1409161205061603022104170c03070204 73
    0x403c40c0d40ca0000c98140b10904c04207413a1a592041110709015007400320203041007691008000960419002070301002044c040c8205508007280054100822441c4039260b10348808101c0c0d045107888610804501424040c905000440c6040160b000b401a0311402c240d55004000d00820300c24403c04400940001d0413031001c01a41c0b0034480005105003040143c810b000f4000380402d0042e440c4090910900b25407807040d0503140c900300c1141e03c480250418040348020384040c220380c445001034070180004032030b080d6200400290f590302c1102d00044500b0000d06c01c0d16815211076030303040007200d40c1d1300900c5802c40a00d403c100100191900e5448807a20184080001503104001612a008100115603041040d801280c514003480386444074040286005072007040c040e84141d0f00c607511080041d0044030640001b0003451950341c02a0180c0d207241080e041d035080010020354003801b000d5000e44081c1c40c258652090511a240d04070101d41040c1c040b50011403800d07000390b0030b010050481805401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 535461654 1250 535460404 535460417
    0xf05150c120c0a030f08130f0302032101090c020105061311040f181d07091104031704030b07180b0a020f06090a0c09090506041b050402030403120e0604021f 69
    0x88124410030082c18044950344020140140d5610b0040c0001101d45030520911040c2c2080100a010780e044011245900c90800a030303540d60fa01e400d914600814005c81d00713900008090146001d180e0070001d040b10071848040c05a034038030080070f900700c0300c05071000c40c0c01c03d003020611000c407843e40d0448005840d016400e90301c1d20381c0d50280c0480c0484c1a400c40c0482c0f02c10040810762070862030081e00c0d001441758071540072107102c52607225030301c2c0480d1042c003440715107440480b80354081d40f8080d100110740151362084181191400c081159005000890f202200034020840e00ca100b603140448e1125090b1407001d8050400c3e0f04054150030241c00d410071445442ca01e404040010320445000368250340003005102401c0c80d1281c9042007503007203030740150303e05605c030340200c1c90000340590010381116419069000717900041403d00700780d4012030303000360000003400b0805520411701511508007503000c20401140181c07d079200c1e50f090354080c1d032000c81500c500031085414070390324211031803034117050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 535462904 1250 535461654 535461673
    0x91804050f03030a060501020f06010b1b10020c0a301d0d0605090d020f1b0d060204030b041112101a09040f0b0f090607030b04090204020d0b0a0f05150c 67
    0x780b8607841102c0019203035482c2c004c100310550301040400c4074400c5481c0035094942c102100c03442c560140740c5580c81c4510544910b8110000c0901ca10302402002c1e40c070541d5070310007074100140e840403c0f2a044035016141001c1011081c1100e43d814001c1003100b81541d4030b02c58000084801c035800103409102c148000d115400745545c3c0000c094113007440303a000854a45004010182000c0c008030001081d904250110307046003001080c02441d02c0d4a1085140a500d542c002160424008280041115200143c0807040c00a10701c155881148076210092410341300d4001e2018900b400300c50b041c02e030ba1121107402080000c540200440c80d0701840c2c140301c00640040003884684043d5000c2e0303004040700c0b4028061107654010a58410350340d00030f00b510b509101856136944d07403005089508145c0e07640400d201ca0783e51f0b41c01806405800820641d210b11b188a5804002d10390b00701034900c20001c2510020704190704a4130b103021500000c000305114508211801c10684c0100340346402401640c5c074a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 535464154 1250 535462904 535462933
    0x110405060f06030f090d030902010905102105090d030204051e04020f16050d0804020a0e040f23100513060b0f090c031801110405010c062d06050609180405 68
    0x41c500c00c00340342c0c4ca15440342c180004501e007055a03003e1040101030401c444040503076009040042280c00586080900542c00c03141140e00c0c03407030440c0030b00d0030030325101000d00030884c0e54100501234005807060720b05000c1c0001c401c1d401c07403045114041c2c0054644000703541920f001034081c261801c026001501e850000095100150301c004881c503c401c88210652040c084200804403058010b0304221009042a80008022803071074400d07140111003001c009020081d00103659980c080c1d00a01c40f0702d010041d106070011508880c420301690748522810b42204803400e0041ca80990905c1515000d007103c50b40f1140040e0548412107a006401400c2c0103074213032a134194541c40b81a01700d604540382d04040c150313400020581c3c1c03403a0703084d42c1c1403d480c014516008412642103400c24204008002c115240400240540d10360945290090040004c108903903c1c2e1850402102050704000c442e88480030820701e806500503550300b041c2d19000c0381c500d0501040500e80c000e8011400c072040d08070108113 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 535465404 1250 535464154 535464157
    0x501050108040f032f0f060f15060c01021c050f13030f050a0509030604030e0111030301060f0819090503030928030e151611040915150e0907080613110405060f06 71
    0x2d0013100340e0300006a103a1029421300092340c0001c1d0b941400c452900340741c510307501c150f507107118040e00c5540300140f2044040e90940c101e43c21b01103200c002c0b04d9403142c0840c05800030030b0119508001111a4000946284140030b840302d101a410b881d0320209289040301124990010880c030070074400e00304601c07540c0742d4080002500c104c0c8a5620391040038500c1c400180b03503810f400e14800240c2d00034001408850f4100c0c480543e80d0b009881c007400d59640b026021403103480c62642030700c5103d02e01281c4005200300403000f5486482594116440b101d40e401040c40b250718603081d40700c404002d4a50200001c0d2249105a040c40f0000b031040040302110002c00c143c5070b001103410403207580b0308529802044080c02c0d1290b00403104507001c02002c070792a00c0b40720009541103d070705100c654400800524a03550400e0700003508420300641810b1815a030403590702c4400340602d006900c20500058102418510400201c6034400304469100f280c1c0c90501018182c090022039011480e000c1402407511042c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 535466654 1250 535465404 535465487
    0x1050403060e010e010c050c030a18031209140a030c030210020f070f0302041439070f050f0d020a031107050418031d0105040b03040c05041107060501050108040f03 72
    0x1800002d000c041348001034211240e10840e007061004c1400808031a40010069a81150310b034100705c91001044030340c2c0310380b4078450b820040c010800065102c0034030b940400c610050f0f61420140d44c00b01e66a240420141700b01d10710004103503500e004801c1c80181016041050000400e0040725107072800010200d0500b40340e5001150b09100e0b82e80100b05518080c0900b100a40010603c1c51103410115022501c0c88128100300c0d0200c1c000700404051a044208200c0880e0015902c094a418a03840c2030340303503082220f009507100e105002c0315499440021503403401c1c0511f00d070001c20903030582d503405990440070090720122501a5001c0015907844034001d40b80c1007207072424160056201072401402c8403604200c0013101440d00c0e806d05256036041800c54040e521140160b81c1c4a588501d001014030309250403417500641020109003100342d48001030850a0310402c0248207a88e201d0340110352960017158090304811841c20310030082070080780c0c0352001110045450182040b00078042080100f403d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 535467904 1250 535466654 535466681
    0x3020c190b090c060f0904021e03010f0e0109112721010c0f09290f031902070210050705011812020106060c12030c0c06060b091c05100b0105040306 65
    0x1400b0881d45201c1400f01401041040321050705051013000305c050540601950079000d994001400e0300d1845041103009003096220805aa413581c44000b100400c2c1040c1c8501ca024548050003ca81147c442c0501c0001c0e031301c10800d06003040001410040059400010134140308a2001c102c10281c44900b07901c0ca207002003488004004000c200301e42e0031a40d80d072075108200888108600b610700c0c0c1c02203902007180d41c4200000804501424080501e44000c0500d41c80781c000042c0401640105202070b5119200b00cc03603590f280c862211000d01030b44640c40c4000c0d8055446035a20510303500a0024080b601e0182c000003918600c89517a58882d0000130409550a00030201d0880756154240140301c050200c51600b810050f19940d0303150703440c89035085001e00740360300d9032288079a0074440d50750840d0503070704000300303104050340c8a1000405a112581c3e10303009030401d4184a108040310241024141d50110080000c0d0148128017030040200110740350400c001008008085440c5000c1e405428410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 535469154 1250 535467904 535467923
    0x80c010e1507020613021224150a0b030a11042d151b110a060507020102010f05040201051e1603020114010807030c0303030e160e060108010504060b0a03020c19 70
    0x4079081c0325500c000500c5001150f0003c020001e080000c00c0c1e11903803a41c3d0581b01c61103078101d809100c0d0306246820606400d090055100c084070280795000c985d01610500000b8286600104144210000103009525480000700041000034103554401c50104074003441041c14962198071000041405881c26500d940800004080c2008072004400040298000190151026400c090800c8009030405808c0c11080c000c50400e100d1408100c207007480c00145040d083c2512407034080c103107820080d0103034015071810088905080c9940f04050041d50161148d504005014200354100400401c48508404080c080313008050390b0070804e80c18031480307a000459400301d03100e80000c80c40016800485030b030303110300c0c400c1022691044c0304209a80d0540380c00704451402451680c60420007484250700d95007071440000d80c0c110340311051409050300342d890210691383e810400c42660418040c203020304c0020030207060120301031750040c82240300e110280e07614000100544854401c2c0041d081e15032180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 535470404 1250 535469154 535469173
    0x616050d05240f0f01050d060518072c1908011503060b0901050607080706110703030c2d1d060d0e06010e0f161106150307050103020708070807080c010e 67
    0x62510200b081d003209807022100e04900100044100400c005114103001c00003448050410a903003050015150280a0300b00c40400c0203c4560030420895540c40040c400340500300d801e2800c4000d150b00d28415980d0120b0100d4004200105004448409031202450003070008030501c0a018003000c003040c1d1000c8003159403845c20b040003038078203001809204180d00b40040c0030923a201025900015042030b0001e1320390445103050001480104400c0c95810f40100b181ea00301039168006007900c2d5030316a222103501e03c80c44150244200c148942c03080d040000d40030342240034851a0380c042c1e0a1641c2400ea0200c0c90b6020100340c40358840003019250503101c09e07801151110410509004115035251540c441c601000d02d202d04980c041d2401902290400c0c40c08840c500c5046642c143c2d183c17403800d45809050210000400c18160240c01d80240921403000420758064406d90b9074482d0003000551800031203036540005a84001011500790a0074840a80c0c104030911403100407464150080c0003410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 535471654 1250 535470404 535470451
    0x1a071e0206011508010e01030f08070c030510230f090309040e030904051608160e03030c010902010e03031e0a090807060306030201180b090108070e0d03020724020616050d05 76
    0x11603443c0e400c018032544c2c200401c440e1300707034103038141c1103070f8004040d0001d902c0c01d81b41040b010711419001503c800c140607404424070101144001034040c001c00304000c00c10403c2104126025410b00103100241c080000400d0140e0550a25502508c3d650640780307072403420710014013211511b082d410000d0f4404503074854203080912580f90015410f06c14041c20b2040c1003c000c1540e0340007403c404a07501c0d600807411450b40039020410380d100340201980d0f142c400b03c0c810a4024100b82c0d006038000b407601640d0f0801420040200c0360503c05e034030000e07d0a2040c42a820340180d0001e400101001520748001484540900c1802d0150003695000f00f0303aa0302d1400010303c0c03607a03001d0401c1c0c0d0105170400100940c2c0310713130012200004c20a080506c0d20765610b40c400c0d51402c000e002416040700e540d0460000305580800d09005540e042103071a1241c03020700002d0044520320b8440080580d0040001c0380c41001d2404251140e003017186002845d145480716008142e41c0300352000041003014505401407030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 535472904 1250 535471654 535471679
    0x40f0605090a0f0510030b010e040f020d11030601020a020f2103130b1306080a0b0a090c0201110a0207050d05071805070807020d050307121b0215131a071e020601 71
    0x5140c3c4030384854229081c00001004040002020320500d5500c035081552130b4040d554041071000003c00c00c00950f0000c581030030180d130004510025151502540810598158041e603014030b4041e80202217080a030707070a0107015000e200c20107a00089248103c805805a00301003582a0400c1010b07548034540c18500841202c2950000314071003406108403005000c1050b00d200485256180c40040e0361600c00110f4010700503105a55046800080d0100c0c41d0803154201c641c54418680c02040085903036a5180c1c0c050240740e440600680142c0f20411442c41d02c040904815801001610416551900c07084071000800150b96801c039240d40400081a070404c3c440742e802a03190000c2e124441c0c45910051a500c001800d25040c07180180e41050180810390050800104041100041400388040690303030740600c46151010340350070307800510141c12003020483d4080c0c2c4015200f0305c3d03850030400c01002d00b1001708010304114083c00c0f005c45e003841001400c030010405030081c0c64154104800c2140c030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 535474154 1250 535472904 535472909
    0xf02010f02070312081807091506050304170714060f070e01020607020604120903080f0910050c0a06020703030f240f1a0c0118051609140402040b010302040f0605090a 73
    0x7590420081040418101c00002c05107030072629040240da61000344650b0010b0f843c4407103040c5d6201d403403000f1903058901d500c41c500c81201d0714000c080c01640c5500850380e5200450f0010729260b0300c4014103400701008405040c000b4412610402549809140d8502c0c2a80803610b91a01d40e2940090046051700400e0000c60f01340284041c000c01e140189000e507641d003004e80018645e0011540c03080b02c5600c5034911101850b4003403441c690f039510050700c183c041d070022a41d281c803400c2420000980c03e8081c0c0101d4050840030000b4101c540220386846000f5008040103609142d102c860108602c070743d80c82410380700b502c04510246100c10321100160350082941090f503c3e52034243c024000c0030f0000b088004044100100941c0d202001e2401034090321026141908451800303003484100400403a001c0c5400710350340303401204990384480d2001660981c200078100399000101040c0903050507004111030030b20604003d40f6007591200e41c41c442003a641d000c2000140702240c807940071710341154071200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 535475404 1250 535474154 535474157
    0x3070c0606090902102a0609150b0a03030c1b1e05040209060d0e0709020f0c10060b070b04061e0209010315030302120703170f090f06090d030e031201030f02010f 71
    0x1c0e40f42d40c1d01080c00c14103425030300000e00130128034444c821a50100c0d8000104021100915204610f2600801800000d40112901528080d8000303014140e0710071007a070030200401e101d400034607503101520310342070141082d81c00310220225000c0d1051400c0454008090000301c1d542c1221110564480d01c040a0f0025031003517004002026203070341ca143c103a584101401400040c403203883e10905280c5401c1d0790250007507a001140f0410600004000380c100c280072507050350b6094542c16056011944540210842e8100501c0180d011400240403540d00510940b0001203010440f07585503101a805003000c9001500003600341c8240d60b0601400342c2d00240e20f40441da0403030860303601030740350102a81280c02044010901c0c400b0b05100c2c052060000501100182d10f40c00c15588841800000f213907035110910540d030126000308400111248607150300c40240440c1e0303001c201c0c1100507200000c0459194030061010700094070207010740314006c501c500100082c0d00000d10002d49000c1040440c0c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 535476654 1250 535475404 535475411
    0xf04180e120415030b04050a0e060112020d15020d0e06070314060901060e03031b01140112032c040f0b0f0303120109050c0c010e1e30040b03070c060609 67
    0x1008041c550241c5041d1416154441280003811400314000c0040100c0c0a81c000e09150a00480c0c000990040e04012644010b50342181c0e02d40e4107142d2140e41c51517009400c1080307804038002040c9c105401200441e000c440140c50815600704040580e140c030008441150400c0c0141b040058041c440c42c821a5050a400310613403030110006850841d0511071a0184019201c09a00541c0d050003103600448c0603600300c012241646000f1802044400344014503082c00000100b01550716582051278150701da514440c611143d50500d0a02c03401c2c84510030390101d0500e00308507860340c40780241c0201807600c0c0030018030a015141005075008890b092980607400804c40031780100040040b5905403185808042401c2e204c0590192151181c58840380b002c1d40f8000c21030507640c0000c501c401004010090304c07003004000c10f442c141c80e02c1824060002c00d0004031030380342c0b290b0811288dd04031840000340c040d007480e565207580c03d0746034811114036000441200000c0300b0041e55200d101d0107007c2c010000c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 535477904 1250 535476654 535476673
    0xc0105011e06050f070c0308070f020f221505060c0c09070306080a08090118082d19080d0e030c070b03010509070309020a1503020d051b0313080f04180e 67
    0x103801442200010504c000c1c1c0001c1650070311507500311010080d68861285541e4110b1703400d05106541d01400100d00c900b07182c2070030103518608402442c1c445801144100c1180b00f500810b40b00400c840b00c02c20f81040c0c6150030000d0320356140d0000e0306c282500076001c3c00345150305804000000400410070300034503180201c20b20010100083c1100c01540c8016983c1c3c2e41c15030640141d410000398510f03454003e0f516003011900ca5004650100c503080c55000302114400c080034042d20041c4a1800d45284c1d0340010800001c06600c45032180b207140c0600340d10f618100b8400b00d070340261032915001000550000850170104c3c00b0401c10ba400416440d40381c1e60440d41002c000410194000d04000105501c031003120f010f540d54103200000810394414481b89500c018540a8007a4020001d42030764945401d000518801c62040203541840041c1003040c0307142e803800c0549621205d08081a103030048280003071f49081c007803140280068141003608800e0043c078006400c0640d80c0d5950241042e800c46c0300b22 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 535479154 1250 535477904 535477907
    0x70323040b030a090f030306030b130510110d050901050906010609080606040507020102090405010303031a0a1a0a17010807050a0b181212071a06090705070b0a0603080c0105011e06 79
    0x291025100c0c01c4101e180e407a2108035114000d4a24140050a02c2d00c1c805010030405406900c284102c902c00d085c0c2030f070142e60304000c1e41c1c580c1c5022000a88960040d010703409e2211920f034090200d10041c0641903003455070314450300b000c035601100c2c000b00b40d80d07580d01400300c4a002001900c0c0109094500b0001407410001520b03150100600003901540c1c4030008140c10758002e40503528903c1c00580100600d603943d040050103004803100da27207000c042c2c242c01503003281410318141082d20b41c8140910f02c0d2039074845a9400c15072001c4043ca08014840190f08000c0324030342c09041c000c2003010011b0415500b011304110451609a02c00e843c52441004501d070303031030800450240d0981d002c981140324400050b034900d0a241c030f80d450915511758002008420025840d0080d0031044248503000440d40d034500c03c0c01400d040503212400452014400940016170311000386501807000180842c03856943d940d242d5258001580300d1100365141c800500c0130f0301c034507404640610304c8801e029120a181800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 535480404 1250 535479154 535479157
    0x9041407020d080c1204050c131401030209151903030807030c170405031e0714192402030a02071b05220e0f07030b0a11040e07020f060c070323 63
    0x2041043c80280d40010b40c0000e811810345012010000e400c00a0346000c1ca02281c588810202040c881d01424800000c4407015204840c6c00441c8680f002c0904d900b903400700318462100510f0b004a41a50f201c0000007a1600c068200e85003e84840401f0a41d003107140c007811400c1e00a01080c00c05141c1040b00d00c80c2944078400038180d0001c580028225207680c00c0941c154421484032500c0b12082c400c0d9000400a448001c0c01c450780218481d203c0340c1700041600b41c82d600c4640150324044d0301c4044c1d6002043d0900100d004a8102d440708440720003020755a0000e80e041140c82030141036011072101c0600c48005151024601c01c40c0f08007900314100790003d8008110044052001558540c5410600c801e9605c00e01002455200700c600301e000e00c0004540d135400d5804200c0341000d1500121310680781c54000c89003130b400207070390176030910742001100c0300448402042c0104500c10450010201102170100310f01400c04095810350324003460a001d400c40300108422000a280203402014a04c1484c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 535481654 1250 535480404 535480423
    0x30c080c0708070f0636050601050603070909050f040201080f0f15130603080415080108061305031903061a2106150316030b190501030e190501020904140702 69
    0x41d031054403100f035420910200d04840200030412481e00c0e0140f04080801d400104c00340d50442030104d6040c0702e510b400711490854040041c0a03030304c0980140243c0c40d101014542c89807151030079444050391541d41c1d40035600c0c15030703030580c0c6100d000082c0b0055503444040750b0341c0030448510924050a11040e445503e50700102045003a0202c910800c00aa8884e4100e4007002800403041c0100394603400c1070340c80e590192040009000101024510643c010b030f105a0417128600b02524042c1c2c0d840c501c110018200400895090200700071034140300e44400c6000b40d0408465a00060407401d010090109944050140429840a000c2590300c401c051491608000f40c02703014401c1604d0f160007154a0700c0000d00107214488012080128a030001a01050450f500d5a81480121400c00034007940c2030801c0c226107503004203c00c05005c90b50280c3c00000512058004849854481d455640402c82800404036803e940014000c126454940115000e0040c9841004111708040c64082e59501d03444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 535482904 1250 535481654 535481663
    0x70f03050315031c080c0405040f0509011407020d121d0d030c090803030408090a121b060c020d030f05040f0602010b0907080708160203041d07020d020712031b0f080703030c080c07 79
    0x10002034141b1035000182c0b00105000303032050010f03800000402d0060041107a03503a02035132800b8a2001d07494100d0300c840340103038002c0d000303004140a031010440340c0e8034002a030a200203032a07140705a0610111800d042c1c40140003000703401c50950024005050300c0c5801c481c0000c01000300001c2c44401400b208507038115900c07104050b81c07511a00b011841e00d5900e82d1101102e50020840c5a082c404c040000002c189080d9002c4545261501d00c142c40304e10b581720f40039400c82e02030030030b041c000703806a40300c410664130a040c0203062594842c0500401c00840d00310000603510350048401c1814058000e6811030f00350304085000e0301e840440108800c0004041120004c90801040f0304540240100c1c0e0140050308903100348580c40b01d403100d9200da81520024014410a1001042d0b0783c0302040345800c0e00c082e0040c28908180310b4a0440741d044214041005054881c01080e0001e2100c010601c2c1051280c414140c13110043c5c20054100c0d1030700441403080c0f004060800403c0c2841604458196602 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 535484154 1250 535482904 535482917
    0x906050310230a03050a0327060e01031515030e0c060919181d28050f0303090706181404050403020a060f0b04231308070f03050315031c 60
    0x599100d050250b88680658010856036004030a109000c01c2841d402400b07500e4903a00d1481c400385451001100340c002c0755518172060028404284100e0380d0b44d02c181d105140100d0b0f110384400c0002c0c5000c64690010b50704184145088203ea03806004040609240c00054001080f024012411901c1118492441000050095401c200b1107006110142100f02d40c01035204240a8842008280789a0655003502c1c132818903c0c1c0e0180009a400345034161410702120003110f824081220003650f0380210b4945c024941c61080c10802040654414540c01000700b403124078010001e08030f0b2220014030840402e5003d0248020745200000210212083d02d0025003030ba902d050480c103060125030001c3c000c9003028204084126260050030f075114048500b00228a8080c5014926100034400100007000c9440000d562030650a00c40207054011441350385080d00c59900c405030300212602c11004603402206104a05150a5015410920a500900364100c002d000144000000000401044030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 535485404 1250 535484154 535484189
    0xf0902090105091b0412060e0a0201020c041505130c030c02071a0a1202031303080106020a0209040b070c14030307081b0d0c051e030a0f02070b131718010906050310 72
    0x40f0943c0710541c004e540d554075612241c036410b000c1e524410500003076521505000702407504440114200520720381c140c0060154170240300078040640302d140b40b00031000c04030701d100107005d031180c100d80d0400400364040041c91103140900038080b0740c0d02500301821544502c078248280c00c01198910b1110303182030040c5032100c8503154102e950326250845003c14500110600030030034480c40310b10b401c1e103100340c0b1801e4640c0e803503100882c2d8412220f0806540514400c0119001c254507110264211904e450444600344603911440700341d898140d6401e41c2075000000b0810300f00c4d0310862154026040360664492200342c11403c0502c1e008110f941e01325035030b9416201480500900850b510b0b0a01226a42ca086062003d4410603420440b41d04440701d060a44903030052401d4801c03540069030001341001d0135114400360070b05034856807408403075240200d03500c000c5400284016100541c40802c0c403c2d001680800014008a0301da0301040c103200090003444641c900122000056030724001c01d260b000d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 535486654 1250 535485404 535485421
    0x50a0b0607150902040e0f0106080105100b0c0a02031204030b060609010537090e060d050706052203140c0102060405100c020304050402030c041a090d030e0f0301110306040f090209010509 82
    0x182c1030000942c01782c43c18a04078190340c030100b03e01503100c107004020800c4c2c075030341d44d1164241d503021115000d00701c0301c09100b40811a42c02c80548800c050310011104550140c2d800301b07140050091030aa03c2c0c920104041013002109480c0d960721140559449041000d91070020b002c50181840d240030006140303c24000988d4030007030700c0790000c0c002c285030461003103030410140040c1d0f00350007200b0083c05150300061950400c0c0c260103020384d6000c00101842494100c08a540e070b086075400b000064111141640c1241000e031844c806503000700e00c80700f501440c0c80340840c50b2102503240c0742e066420402c10400070910202c2d49844d50b68021601045c221b000b86e5089040d84150b8011030340c031170302c08024131413641c0243d80030300b0960300940300e52112220404d403d802d00b4003503008090340c08005001c00d48006846490a0408540c0c05455212082c40050010b404d4960020456008020100400c802450640102840e0100111b400c010f40c04031900400d10010050080310701a40d0244003150241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 535487904 1250 535486654 535486661
    0x309090c19050a0f230c070801060b1917010b0c07030212010e01050c1603030c050903030d050601090501090f03080c1609390c050c030f060604050a0b060715 69
    0x80311a8894181c141240703101410540042c40c03940001206140c50b5641d807406400c8480300708045e4400503070100701c41c005200d032941c4408018049402420f0700018200400d000c3c80002e49410b04e80c160b15003040b25501d940720300080b61120200904644031081740b42011a541d81522048400196502d000c4c402c118075103801d039440203400401880d51540c0000065000d0310303001078071030000e224503103c400c41100b4a02910020600844400c0c44010000e07000c0c1d0701c80502c0d9500c5080003800c000c1e2845c0042c1c115044640103610090311703070007009215a80b0007050f4000c0c1c802401e20700522030070607800e0f08113102d00d404001c190003030005101d41100c0f82000713400560800c9025034002c039910751442102030810181d2688107008102d903004034544480c99018110700782d2001c0000783e01d42080e0704850810140d0400d440c1406100c02500454030280001d031246034003500100920704004042c48100d610090101d642d80345031006441d080e81c0c5603030850788015040000300044440021559008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 535489154 1250 535487904 535487917
    0xf050102090a0b03010f08031e090109030c030f2a12080d02070804060e030607050a0c140303070905030708030a05031b0d060306050601110c03120c1015081006080309090c 75
    0x70980c42000a840c034100c000450588100101b81001369035180c030119924050808451900701c40707540d440184510781400b40c00100014980452a19502c0e02c402236960709582003036440346a055240004d03c40c200000c0c071920b01310741c5000c0000d40c00214809070101001d01035481c400401c0c0a00605000c006415241700d074214400440d03546138245015030060384148243c1c00840d2000800d1071140c40c0c00301e071081c403501d41525290311344081c0c00300c2200c1031510740408803603400040c41c44040c2a2420409188030f508692248041c0a06100400d032800d902c030b503c4941d80b40d004000400880340d001003070b62341040e06075102c207010325194521046640220741203560540d01d810400000e00c83d20380c02060143e00e0a81b103044218002c500310300e40f60110b82540c980c040d0300800401900300ba041005003d8210494107642d41465400d16800a4562008009640040503141800500d401f80171081c004138610700204101c07480c1810346c540f01c2c002d00201c1442100c1d40d200240b5114058011140c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 535490404 1250 535489154 535489159
    0x311030307020325031202030606071a0912031e070c060e060f060915060c01150e04140d0f030b010903050d0f180501020c09040602131d0c0a0c0f05010209 68
    0xc503840d00c024002d540b500011143c41d8140c0d0718402250700c01c541c0740c894012080e0550741e080d440300d460000381406075001501c5036400510400008000c1000911014605c9800c90344061050500303c07840391818a18001d00c69680e001002404042d00a14080c0d2000105146030640345607520081680e400040c40b401030719403030800800c2003001501280c16441425098651016034450101303125016a080314040347c0c105c41c04101600d1450890064200001c2030740010501c500c01e1251648818810380c0681a00f0380c1b44010720080080241085405003803203001060350080d1f036070000b0b1074803242d140d007013043c19a01c58001c15264481c0c0e05d8074010f503402c00c04071494100340c848010100701800000c0c60000e9031f40001d1843d180c545119520441d88164014114041200200311818202400403200c45038200082501440002444c00007000c8401e88654005010032940601100c0244201c0c6c007480200030b52840c00341c1019824a4040e0030040440001e0100e15007240217218559000f81d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 535491654 1250 535490404 535490407
    0x1507020604030f0306080d0806151303060605010c0b0403030c0e0a060e13110a0302160c0f09050c070c0611010f110a020c33041d09011b0905010507031103 68
    0x51115000200540a50300c641d4401c041c2c00e454803000c40407180140900c1d02c42d6040b03818000f91580c070a548281d000030006015280c0c260f20030401207000c0d400fa0740401d0386038140d21410000d10840e0300c9290010704003801c100b9101c80c00780d40e031004c2a4a00400c010281980ca42409202d64401c03024408c0b2403c000d041c82e810340303480c0c2002130100060300e40c81922602d9400b460390a41d190b2405808010342031200c16605042c0a01c1055019401007051040f851210076207400c0881c880945880c001c003c58199038449608018225050711002081c02501501c2000008009240d95815500310751817031400386885041c070880311f800b510100c0d429078100c03404c000c2c00014220000c2c0080400000640072070b801a5542014890840e080c01008025041030f2a08c044090b07041e901d40309480c4407418415490b20b80c803000f0342c2442043c410b84081000566408110600c602403003100c0c0c102c00141210180400380c440c004002600b540992030401a001c5050001c050184940b0b400040da15001e0300d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 535492904 1250 535491654 535491661
    0x309120a0e091503031b03071203060527070c031b1209090504082d0c010b010306090b03120a0203120c0705012f090f03150612071211010215 62
    0x520034001000060710402045010079401205400b00010000c0c3c0035010b5820414405050b21200010310500340850108200d00c000007500350082070300352102034400040441c24101485405e014008982030803400d00401c1e40360382d000051f50700b6032082c111701c1d1028840007149804c407420500000400b00143e0300c1c1d01110104401840007100700e03961503070b8814107969103c401c001a503034240c038050401d20701003000c054039950f070760300301c504052401148840e207440c1e50646030196440320105004695480448000e55030741400f4003401028042001d00c440e030240c40c0000e4031008008504401401d0010314010050b000f44140c0d4580081c1000d0780340c2a240c100c1040390030740d0056000302d44652070007007007581654030110051001205002011401034001c0c0c1914080d601291099178030a403a0341036800c4590b0108035441c0c4032401a40c06540d10f05004003841034441a480c440251a009075509102c08040051404100c507013000c5031611480380c14005034100400b664130114545504800c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 535494154 1250 535492904 535492907
    0x209070e090a090b0c120103020d1e050609061509130606080304030b04020f0a060f080423010f0b0604080d08040c0f0e09060a06030308010510110d0201060f09051b0309120a 76
    0x640325550080c40c44013a5540c0d82c842d0140240315084521041008000c010700c058240516a20340151060700c1c1c82800e18842e403210031002110300c0d801c88440d40000100a01d0060a0203543d80250504031031807086054034000400d00c00b8018100e81c0045054081e20040c00a6608600c1c001c11100c0305072940c41e5103038180704a080d8001c4505a0194408140c2c090450078065020002c94041340c0e101e030034080701603030b0407181c1000160080c1d488008029035100c0f110700e50b03001da5038150078560002420030000106401500d076500040c80c85110244010000030380e0104000300e420445181000d0103940390310b0010f18513281c0360030800d90078090b6000846c5442080c0e01d4039000d200c1c1401181c1080d9a00b241c08001d0780d942e40402800124130034010445130400001c1c856070000d080c14031183c030384618000141b80c50640e08131031b401030b912204108115118020f80c00c000c2c04c604601031003140390010203161b005c0310482040300c1e446c10000c002005020309200098030481c1c1c90040c130740d840c18808030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 535495404 1250 535494154 535494161
    0x902041503020103060e0f0103030c0f05060106080f070f0f0c061b0206060a0f0b07080705032701030c020601081c0203041d06040f05072705060d05040507050901120209070e090a 78
    0x4200e001c21700e017101c040748180d80a00180e225001444a144d401d030300703594040702c0e090382c4040102d801a85103121000000c505120b01d44c007a0184c4d175240302079860a0406200300000150800c0e00303201864403040217559120794410842001c0341000d003604070482c0382c00070041144610b600c8010800309000c4114946c00b05255015100490300b52064944800c400050f01016105901e00d81000304124000a00c03044050925640550140da0414060702a110a82c0c00c1d0050030201e0b01951106d003020668140c0301d4130120305070780d20041035a0342c1041413156a030388002980e01601c118520102031018800c004650180c59002c0280d14407424882c2986c05203441601d030544a00e080c64500306004196101d001e10811480d65222200486000c100075014a02403440c2c290b01d120b040045083d1303e609000b041c1f20200d03134200003000c1c03406091140c10182c00741c001e03510401c1c0e031000411801c0707103081c0b41001e456011100c580c003e488140099984410070160550480029010061005404d03071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 535496654 1250 535495404 535495409
    0x60b0315150102060108070806060d0c080a0302060108010513050c06030c040810150e0906181e0c030f07030c0b0a09120302210f040b160209090a050712020904080306030109020415 79
    0x2004ca58a998940301d036252905210b0082000981c070080c00560700e481d0154461b22100d00a01d8007200b0252210a00c60810f0050a410b90141c1d0005004120045d02441090b9104005002042441e1a19179680d0703225142500204c0c071070704000c008602c0e807020620844009120001c00c841d000511001004003900480254451b14400642c00007001509005154810301c4100c1c060911395991701d0107402060602d080d24030991040c440c205c800090800e41001c1c2c4840204000d006800031101010700d0032800c003041c1d09080c0c1201004100140e43e0640c0601551011158251200b03007145003140d4080303c40e48542411102c5154140038550085880c21200ba1140c03440003012081400c0354019201d0191003411128003004104410307040103001c1d110118100200060641c450740005031039140035a0b9001b001e8101d461590100f010400043c03000708003805121046103041c0c0c00145518100403c040c21106001000540c3d6560070350243d200654002d00810800c512054031281070035050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 535497904 1250 535496654 535496657
    0x4020a0c1101021606030911060a05070215120708070c051c08100f05060c0f070e0603100603030e09220b090c0105090a121704030b0609070e010804060b03151501 71
    0x101401a01c5502c08190103240400c0c88100c5000145000300c11401000c0b156005d4a914000113140501944c604c40103200c40e01c0381d540d550b503c030a864010085860002c2040d5100554104004541072151a01140c5d02ca1081c1c20111aa80d940340340640d44903500800050160003101201c084516101d0318802100c1c80755558400c1d951b4440070001e80e06650f50040040c00c0451072410483d40c0782400c01020041e0002003a40c00c216042141d5a1401c0141d40003003250082c4134082102a0404000b4142441091802480041e180d602c002d06106031244410740201039060000c2d800e01c0d8159070300c0c02d1000c80058ec18031440e034a03081003129040c05a17005001c0e40100311031040303c0d61240301920310200c40103001180051a003c0c1103400345202080031155030a00d0010022580c031341a0107803004602801a800385e51038860200b180c030440080881c424809101102c0000c1d03603000b0300540d44190301200c000381d08203084001034503000341c00050240c0f141d00e0504110981c0502510345022500a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 535499154 1250 535497904 535497923
    0x22060e0115030c140a14161101020a0f030c0c0e091509070315092a05010806010302030c180f060a02160806061f030908040602150604020313020105090f04020a0c 71
    0xc1c0101c040d2400381c0342da070300011000c040fa440301003800402008480244e04201030040400446095150007180304415500038200311f003402d10010011480d0300a4091000c3c2900d050185c2d5811280d03041c203540a420410b0f86120001044006511030010300703422006c5c54502e04d400d4003030396540c03200c1c2054103e104c2c1c1864041220410005000780942c4d82c016010791400b0a0508000c0050002c0c41080e00d1604804000020320b17a0408841441240341d50302d6044030b9403e0100160140e01c014100504044c81042086a160b0707613001554100d0341c46812014002040c080000c1c01e40303c8807a6443d41c800c400080789021542c0020301340c28071591480000b6409a0789042c0c807034507100d0850700b241d00074100368a400340c030b40d0071039000042e403c800f4100001da00b611500e59003103039003003030f00f1040c05684101d48050341c60110700324260740b03c00111825072662130a50030140052610b400000c1c1400804505041c2a6840003800d04580070042d01c2151680c0900e034000300340440005080d81c41101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 535500404 1250 535499154 535499189
    0x2070606241d01020d080a02120103050703030807091503020d0603231b010203091c0b0c0a02160b0f09010e090a02091002060402090103021e04050403050910110c22060e01 75
    0x1014048480030082c160068200e040c40403506a8488030000e0401c40d1890342005a50320b036460500c22680030350b01440092403000d045180c080c0c0107541c060450018007100300c80804c00704060240685d041c01c014500543c4030442c0d040d000700507044540000700b0380307881905c147c80c5c0c940403d403034003007a506540101c40660503211880c0660281c01e00c1c005005030010000003040d4100400720124000012683d220b8880994850041240060300c01c4024023a0004074185225030403c420f007252803403920341501403842c01e1145481c911070305413611004640414454072aa004245804c0351280182c060a050b1601525060003540a031210903c01c21900d0b030005211440051160311490b40600808501d03400c0d03800b000310f142a5401c0c000340c25136001034440515165409190b0050b0f2090b00e606448100c100c0400c09400d07003e070070500070400003a0b038031030000000040d080c2c0c2c070441c01d507511201128602100a03a41c03a103c07581c021200d00f41800001c1100341d1840481c100c600459440d80d0010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 535501654 1250 535500404 535500437
    0x12180a0c2c0f0103060e120d020a2d0f090e0408040306150f0509060409080a020c01030605060a0815030313140a05040e030711030c040c080915010b0d0207060624 71
    0x1c1600d40d295030b4444180140700190f00d6901841c6054141001c540610b00f1451300080240e024a40952081c1e07000300d90b2000310343c0c01004000c141c01109405090030100350a07000312240407450110100042420003003600c80c005e07030b0f00070040c0480d4071507080181307414282881c0070750041c40b00300d842c4c91030880c010154401e11020a000e8850140b0050300e890b01c0c005c20080380c204050101c1e03901943e500320b000000350034a80105682441d540180190107050800541140c2a6600c0f42c0c3c010f04040110a8000b030344040c81301c0d400050341082628000f0302502080c914001c20102d4000e0702c40589010a140c60880d003003440e500000c461280400d80c54100740001d650f044500c40440d036000344051000a80b02c04041024288040c04561008030b992002a081e18a80f110390400301c1c1e001810b008020300140080c07105410034605084880d4944410a1034134400c140000ca40306034007048240400609801584c01050010141144100502c407010f142000d0341018101140c0301c05000030703c1c907 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 535502904 1250 535501654 535501739
    0x602030714061006030c020c04020412020306010f061202030a1d1b010302071e03020a1e1401022802121801030e0a0b07051308010e0a0b090312180a0c 66
    0x6140021038260384500c2e202045e4090324071422010150b00031030306812402c2d02c070b0303102400007441c421141e042d0240190040c94100030060300440701c4007502c0c42d028446680c0007408841004003800006a0b0380c0c2d1142580c400601c0c0719074556491001000c2d404090f1140001c00c02080c1c0007202140d5040211030005400321712880ca402171188282ca4003040f440045c0c1014209071f42d0003070054451040c4141d0700c8a8803040e2092121301007010802c06039050100410392107000f03844a0000718a0300c40040c0d0141c050005900c1c07482100c01440601c0f0084510a1050085008042c014030b52280b000c0e0301703245003c209150000d800a4a428035002d002d101c0010b5074440c254210f4554a15034480280441d117986c030210b1400560410380c0c1000511030800d100e04200b103800c0c9800b07000799041d60b1420903000341c00030b070600d082030780184085c80e400b0000842c0d4135000b800d04418103101403c10301d6140e04000310080302401d070600c45400002d107043d20b11003035850f81158030141e050031017014480200d003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 535504154 1250 535502904 535502911
    0x14090d020105093301030c0f06020102282003070b060d0c03031206030c080105010f050108040c050405060d0203100b01090812180409050303070215060a0b1918060203071406 76
    0x1258132074181403202e51a80801d070700c404100a901c40812500c03928101958213020307841200c10720290581001a4002818070402400041c4000c3d1b103800540210f05106401100a000c1c10003d40c45080e2892409041d0701d03140041c0b455840c48018652010341070b00ca0f0000081039820a80d4000050f41c1c83c0340110b1281c19559100d4141084542180c030200e036082401e081c4c3d00b24580e82d802c00032020480ca100b8010007404440008100e0758185401e000d180d4150790301107410301c800013003440002601541120144c5000b910001010381d100c05c0000c0d08130b000b00d100650180030f180940041c0710f1740d176000011a03010030f07242d034410a50365110302c5036603008803000300c1c80d65a010305c6081c00c00c801d0446100c0c2a0300c8010300c04907500f8820385503142554030507520503015070710924400c1401000e07004001e5222400b00c4a504a1030b1400b80484554802c0400491002d61403440b400441e50068800035260780d03555080100e9542c44800280d566800350700240d546200900b50100c3d03031540060707400e20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 535505404 1250 535504154 535504171
    0x703060b07060f0e030403150b030309010203250f060e0d080601020a03180e073f090f050709020706050a0902102001020a0e1201050f0105010e0f0414090d020105 71
    0x94041d0540700c120091881d50110114140c03129006964003800300007400155005200c1c3c56445088100e80d801103c0b0b100340c1080c0030350000d10058880f03030780200a445100101000c586010940321200c0041040d40d60801040e9600c09010401400003030390050b141c0355004c604071161900010310554581604a0b600c600603031094000400092041d030354003401c0b141c1010385540c4e00d9152045030704034007000c892400004220035202c8214004040a007801c003c000e0401180042a900c000b0300c680300e00000e00c8400517190540c0c5410060501c070340c0f0304001c0d004002d654074262a141604080c2d44603402c00c0c1d600d0340c2804c01040c0342500c03c0c402d008184e07074000e00405160754444401e843c1c103030f000c80420300c0d000458851549213810038002444048a44e03a21111041c08200030008000c00012050f0407503894801000340b80080c4980e12810b41e002428603103036614071000025891384410b400396070030604001804881c15500410306025401001c1605c400c0350308000c04a0884004541240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 535506654 1250 535505404 535505407
    0xe010c02010603080d0b0607060c0c02150304080a0807020307170c0d08060f040c210c110102070b15040207140d0e060a020a0609020a0e1503100209030a060c0e09070509090703060b 79
    0x2140c65120750091a00d170501820090030486141c9039501202d108800b00c001062f5840c4c4a00114945020003d00007a00c0040c240c1c15405c161b103030740c1c01038010081e001083c003202c2004145c0c002e00030030030352700350b01d0344048900070b5060900f10205aa8221500000030751203144c010902c0306000c5c0300480d104070000390130042e44050980411010748100c030004010b01001480010304251041c464540300c103c032040c040369107804881d00400545002c0c072600d10f617910501000000460148401e41c010916480d03240c203d10510340040c000b441681001440c0d003141c010030001a080c0420074280c44101c2d500c5d02680300403103600380540e41c1b140c1440800144c100d1540140040c0c119800389003941c0c00505070003001a1288007a801c00301090700c40760f985001d50060000035107410009030040c076036a06003e50030a0305800200e60341c0c3c0d2062500034051902d40e9003e5010038801c030741011075258000c0946900d4100070760b001d0b04c2d90380503204050040e0241c8001580d07c600038002c0304105d805110070039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 535507904 1250 535506654 535506667
    0x14010c1505060f0a0b0702011d01051605030f130e1008030706020f120c0c1c020d082e0311060a052a0d02010f050a0902061207020c130e010c0201060308 67
    0x60000303010061000e6401181c80b0520f01040c0c96480c50720b0085d02d500e0400c0c0e6500c032131600016144105114070b40e48003030098001c902c5070ba60311501380c41041e14460130300c0051103101e103886130a6000b60002c0c10803020f4042501030703002d40200440f104480301c200c60703001241c960748080346151b0400c0c099002c540e030003000310000203080c6600500c3c0603801000d4507810701070102034405822030f00340ca40c46d9140b140461003030b088003828000b200400c0920262480c1d50300000202035103d0740c80c1055001400000d000103070000400342c4c40000b140d1001840394640950768070651480d0b0b041c0d40800c0d910b554200e031448076242070850403a4001d070742a44074903040003c054012503400c2d8012160111700d0088e181c8600d580c00c000c01c013900040c50560004a0500710b000da290044803801002c542200e4200440e0a001d601d0f800d00f01c4e64034400301881400c3c2c0d6070b00d00e003059140a00c403105141d08100740a107902a0001c0c40d5011460000024000344504040ca060417800d0310428007000c1c0103c202003144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 535509154 1250 535507904 535507943
    0x60905060f040c14161b030b16020a1b050f043602060415020f0307030816110601060e0f150406050f210a0501080303250c0203010f091419030f0903050307050714010c 73
    0x6502c4401c510445417815030580e1103e1411a07886c488400d2654200010302982c540003b400c010703108165000c20500804070b85018150000040589002d0401d031100310911094994600c1880c1d006420341f80e442e03948800007180c01c000819981d006010345130240300b000802008460341c403038066484481036161185020390020f400849541807081c03400342c0310050601401000e0082100d83c0700c0d61004d00c40001031050728600010142c0c4030f035111380561a0050a490141d50607940580f6040b62a00004440c140280c40380c0e0940042c60300700c41000c02586440903441a1081c85801014010340c0d1341c5000b407580c3d0b0301081d84d03185d015015905208442d07400d072004500a200003031501100e40842500441c1c03c4600d03507130607a00155140c0340003409102640981c20031720307030564009010302c0c0d401c8190104120a00880182000a81e40355008500d22608808001c0c2d5008403d03296100e20354501035556410b18420300044480448440300d01e58090750910010b1504250500d40e044140c101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 535510404 1250 535509154 535509181
    0x10e0f0303242106060402090307031b051903020102010c0f08130615080f010c0c020d030c050717100b0a080c060c01060b030712060905060f040c14161b030b 69
    0x24400c0041c1200221680356525543c800100e440007034050410844514440750500c28010000b07030080340100118481910000707a05000c49803c85509441c403c440a03444800d580280c0c012a40400800c0c48114803043c243c54a5044074407d80081080032a0780300244c1c0d1582440d83e00b800803426800c0081c00005071402074032080f610031000010000812a03201400710102d800c000f120740e00035140442c0509092084005400315800e203002180800e80c00140e094002034401010000b00111140410100300301810140902d2034005480039120b05083d540c41034501c1d501169141032082c405800c2c100310301d80e0f105a4451602510b00c06000005101c0301c0da00c051030210503590b9070740b00024003200034009036004418594a1004042c5000040d000396050768111102c214585010301c0b40d075555104684c01c004509840c04070b0205e801b0071058a928008041141c4c031402c1c00103464216000034814003131031600c2082e540502c04415000108000e44601005088244400108114954015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 535511654 1250 535510404 535510441
    0x418050607080f160507141038120a150c031a1c020d170403020111030a020a03120212010905060a0e160e120d031b080910020c0c04060f08010e0f0303 66
    0xc7c2181d40301c10302501180c500b08401c41540486513841d2420540d00c030240e410700840c0010040d131603280400b00c0c402041503218a52500e272007030440802140c00b00009220003018a0f40041401d5200c2101d00007810251000307141201c000381c0f80842084414070074ac06446061180a88084812003104461381030360300741028181da0180144010000055034620b9800c119500f40480c980ca403407031803002501d0001c410380c0d085180e401c00d0080d03d10840c0d000070040941c64042c50a0200008401081d0001b80b01e0000380030394031181c401c0081200101c98100a01500e0265a10200c041c1e941c070084d10380d100d06903021102c0280c0b000e090420f045c0b151310381f1510716100800e00a03040c0c0b281c0340c40301c1ca4002103a00140101e9124ac850034a05142a801e981007564681080015480c4c5000b0541c1c55080e401d548602c415404240c2c03e241c200c042040b00221400038100b006216110706030380e82d010b81c562240307049030344c200f107443c507100c80011402d00741c070074215001503003503403185198003405a2078030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 535512904 1250 535511654 535511663
    0xa02070c0510121d0c0303040e07050a050d020d09171215060f07030c0224090904030306080307080d05010602010b0a09050613140f060118140418050607080f160507 72
    0x1441103620b010782521030f2044044141d90340c051300030301c1d4540041c1807180003911076210350001d00c1300b0030015440c0e000040d4000450f103407490703031001b00030010348031401200350b01c94070a440480c190844080d941d01c04070806000b400b06c00c036550000103032640f5903c80d008a044140c0d603c00c01185030320b040380c0b007a03d006150003000e090401c40e800c1c01800d1241c2004105400050b60131600000f503081c002605128407000c1e20300103e1540c89818841014400d0b180c246000340f20380d10000e0281882940f020010341054401e40382d8810180c04d1200b8240c010b01103120b00d0501d8100001441c0d401480b59009007603001d4215262940740043c01e2009100c0180450b8002c50b038120001e148018911800f454444c074161400c55500b000e000d502171400300100820b052020103101940c5240040a44408032690380d001013260719864004100501710f1407601c12a060300c111032040400101050301403240d1125525180140d5814480003048801a1241a4501081c8030382d070035400d00c154003c1c50350701d004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 535514154 1250 535512904 535512917
    0x106230408010221090a0c03021903021f09212d0c0312030b0306060607060b090f0712050c0706050601031404110a0e2202190e010603050a02070c0510 66
    0x480000314260381c00f110701d81d0a6210781100c132021125005116541241c084401045140c030560789064117481d050101a100303a5030b8800d001a005003900d550805941d01500c000000704144203040101181c8480303020100300c10460100d000f0780c0000070b0191002c20505030f12894001034548940f4040d4017001c1d21500914000c3d0120424122000798002a10400301e01d10043e10358103160303010110001ca91802c05041100004e00742c2d50004207542c0225088450710340c0d4034010300d04003008101c00c1049035001300d007080400c42c4146031040304500c510178030b4031098451015021002c04a40b0100c516049043c0184403040c0070a455900c420b41c80f00040c1400034040580548400c03507154111412120140e010761008518200002d64000414540b05800c00c51b01b02041089640701d0112601031b04903048020501c251740c3d65403a400541c00600c168100341c1a110403008440d01000d000e03503408a8280004107200d480513108030740c2669000f80300e980e485410401044000d0500501c5030040106 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 535515404 1250 535514154 535514159
    0xe01110613170a050702120309010804020f06090301061509080a0b160905120d1202310e07030204030506060f10080606130803040510080c0a0c0f0b0403020606030c0901062304 77
    0x514070000e282d43c0015860300c64450a03c0d20421003001c48058011003d0b40080c8039105284e44c000c1c418a41041d4100c03549041c000241b004076030b0a0040078100e40e80b640c2801c000058041b8a84440c40d00a10555515880140c0b141c10309640c4602c80782c8000c1c4000403090004040450005c2015500009490556089960740e07000494040c4200000c038565042a0b086103151a00102e0110700607000d55019400c0081403510048000f82099011600c60164105624a20f442034000e001800f4014418081800d050710003c009400c107004c03c440c64030600021801c0c5191800030300c03e2810004081c4159a4217200c4100c452040142066810640c00d000c0e5000d11740c0300c0781002e000761030607000854545181404110030011030440d61002d019500303042c054201d003488200c800700c1e541814556006005850140190086a00060490303030307020040c002016030104041c6e001d50812130844860040c200d040010800081c422071022400d200130320300c20144040d500840c4803a082c1e03e0a0300b4260b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 535516654 1250 535515404 535515443
    0x90311030705220f0501050a051504050d0c03150911010e0111060921030106020d05130b070c060201050615030106030b0d02030105072d120b120706080105010e01110613 74
    0x180b4060300e040c40c0f48400c111224403a0151050b01403160301407200340655450030010031984442c5000e1035000c0d40c10511514a03910404048030001d15001d0130480602c0400c0c1080d0407007a82500003100c90380f0420034085129141c1c3c0c051340c0d480c5600150046030400c0041700559181381c00d4003400e07061040740b1110031142c841c06d210380e502c40c21b1700402a01e10f44d000000d0404000540f103194071800744007480180085030740040c1c03210b101000c0e410403680e0b4944500854541940d2030f8440314020400060f40e904008060103080304483d4150020f001c01d85603c403c105015150038075200748610140010408a40329030810016050040e00e01c0515a80175004a402c1d14401c940c02400f0074411600035160681c2c3c100262190300d00c80c04030003240e0304611801009540d12581001c2081d4680d801030003541c4d03480310350310920311101c5d045405035907540740301030082d200920801d804030304070070765610055020f0540760000043c018003a00340341e42d408003a0190503640c0b4100317030341410030300700d4008010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 535517904 1250 535516654 535516669
    0x15180305030f1c0c0809010c110303040210180308090a09021602091e0f0702120a02070306050a180309060e01090503030f1b1506090a0c0e040f021e180405010501090311030705 77
    0x800244e4688417a45441107030fa83c2034403410b61000c0c00300400140724161620f40801920340059040b01c040c190305241c50002c0b00d50390300145d0305210038200c5001c000204176a080081103400010340d80b5544181d135032002d41c800c901552101110b0004805113190061502d8241a41c1c402e480c2010701c401884a07103002c0394618002c540100007800008240001d2039010400340b416201224016407900562800c02902c602492000a05980d2031740c02107059807856030001354890143e848135444d8482c0a0800074039043c1035100f443c0c0460703a4001c144009500c14070b803400903180050025880c140e0010b1250289900005484400300240d00122811180500040c07581c1c1c070826290780002d0030034008010040f800605904c3e06940f4041343ca4022035049000c0300c0c1d890004507800601650b800d220360010b8800e401501454540340100e004105000320040c003102085a245040031043d01801e000458100380102404030f5075209080000a1580e0100744c0c40c0000175043c1c0d05000d40e03800c08141312 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 535519154 1250 535517904 535517921
    0x50102013902030d020d0f0b120d050d18060504060e0102090612040804031b030b090604120c0c0906081510081f14041a10052b0b0115180305030f1c 65
    0x640c4a400486000915020320401c0340c0045070690312001802c0031a42c1c2d2b8003600806003081c4000450f40061212140d40103203001017900f900d0020592040c54404010042100c0480301e40c2c0c900001a03d2006051080d981c07501005030100345032030014008540c030040f005000300e5064070208008000a007900f41c1d50703a07a4051841d1942d0b4002e00358034222854000c0144164025030041c000c010204082c0c5400783d0020609007000c9410100e14104280030710255001010203c1c14110001407048000030302e242c0c04040381014050545892840e945151918858003c00d64480680010042d00a201d014800e8014030000103120081d070342c1c154170340724049400f03035201c2c803c1c083da01c0540022240e8859000182444514085040c01e002a9a40f1f104030341c64081083d0101e2800070010300c0428101e52a0707040f00840501d580c2d1150b58020251f0f80950800000b0310750242400807041e106403c07002d0700e074045c1c00b030f600b17014070101e014171070790400c02c0c18012200e50000101d0081d00c081c81385024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 535520404 1250 535519154 535519177
    0x1a15060d1503230c0105090409032609011409060411030f0f0307030305010512070b0a031409210a0813020418200d02010207231504050102013902030d02 67
    0x1c095910400400180080c07200c400f040c0d00010340818151307030f104044404540c02160005141040e030709040714244c08559201040d8a070000100c4900710340b59090910030090003000b0b01000d0311a800525114100360b44d81d058640c8940b0210340082c21940f080c180700b5901030708440551400714101f07858800900e100c10815080012f0300411306506005090240c201a1614181003500a010607541c0159129402040d0700101c0c50340003540c400e81029503083d044c12042401804c001c4107080d101c804480b550207186803140c8104240340881001d503030483c01191152481561038051500c10351700c08940403607101d0b0380c074441054181d8560360503618403801040610103102800141c0800d503810301213540d101d10700314804400140e90000e58441964070078904215140b0360614054603000090040f80c0e40041503650104208c001d1501800465109a0090080c007011348100321032030f0410072001c240c4481d240c80d41003006409101c0d0598649131441120b180c060038145400481e00305902204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 535521654 1250 535520404 535520423
    0x1b030a0504051006050d030309021c050f06060405100e0408041d09070f0b16020409141c0903020d0209040c0915050a05040501060f080c0c01181a15060d1503 69
    0x105102c01007182551110070524204805800c21001aa01c005181401001c00da00d5003509801c42d20b521400301000c2c80c0b2840c4c1c00114071124581161100e003040000540d500c1800b0010302c15107014090f40f8015150a600042082e0800801e4840000002c00945101008020001c0c10240b450358071a40d00b4441c5810341d175142080d81c42e1a0612000340e10200181040010620404a04208865071284005404030701c080c0c1500c04580030f401c2d0054090030850034009281808180031071803590181041c01c6c0b0500c0f91031206026204001513003c085c0d00a5102001c4100605201045039001801040d01030030f042e9440041d00c0c01d4642c001450002400e110701c0030400c0c0e04150101b1030240c041210b00b40413560520200602217094501503004200d011404101d04021100c121203485210750028000028030703074030380e0b00d0040501d02d0807503041c044102015643c201018080780145a07240048503113240c28000c20025800c81d461880c3c00316601c80c60841d000145c566150000c51050100d40e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 535522904 1250 535521654 535521661
    0x30f0103060c020c1e0a0f060c020307061d040506061201060f0207081c0c0215071a01080313090e0322050102120a08040602181003091709010e04051b030a05 69
    0x41c10703100e4140c418030035940103074010300c80c81d03981039005116481201c14101c0800c5035100005d600f008268030843c9600314940010500c2903020170780e615054003d070304413510555901d0b0200c40300503040c0942034061114007090000391a081d001545c10400080c4600d08241c00c0301034071407450302c00717900040218400c2620408466014400c1c000140b45402c0600750088000310031500381e10b00c0450b24000c024030342445004640d5034800d02d00e000010a0342e0a07844203218648240e4a00341c03241c0302d00d540f00208000003a216800005c464500442030400340c8130324900010b040181c421441c07914024001032152820075441d05001f2600a407080c041d4000c400d20b80300029051160049100c11201c034100326a111540d0061083c507009079001e9030040c1d864407005502103008130148201c50340482e0381c8107824200f81d819008146154001e1403003030b05114086454480b0380c8907402c0c096003c2003900050329042e00d0550b001c1a440250380801d041003040314120700c81c1341d6104a0f06070f11150344d14000d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 535524154 1250 535522904 535522913
    0x120c05090f061507020f0d0318080607030f06140d1104110316080f0103110103061802090a0605030108100f18350403120e03030a0e1c0b0f04080708030f0103 69
    0x15103c940010301e003084c0c03408240303801181081150710552400351039020800402c051207205d40422a0703052040c150180c50322040c0141d25080b0a1710640001390a114020012800c50f2148108950100c1c0e05048c40f66103103000c0c0007008100300c005a0709142558009145501c45000c0e000c240341ca40740807255203190030610103003603a000070011b0003004002c804001007800c90b01c081c2415250805080c210f900031030001200502040e801c219000d0150102c59652609150007a088410040300d45101c0c442d2100310231a00c60009200300742186e40420341c1400c141d18107070b2290705c0502e4a800007242c4804500e49200071007203545421100c075644010705040c481c080c030218442e06200040f0344881440c401306528840c4c00b0318000501034005c6900410004d038020340104c481041c01034107030b83c0c4542862034058002c51000071194014180c81b0301800e198042042044100d41d801002d015058841001442d084007006104441c03c0400308204004641000701851140c09050401c414a43c1545003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 535525404 1250 535524154 535524169
    0x4030c03113d0e010902011d0a06080a0f150e0604201605030708090a090504030207140d02030106030b010807080304080a08070f06050a0207020439090f08010501081c09120c05090f06 80
    0xe560942c0589070740380234195102d01c1008201e038039625103412a5101c0c00d000d000100011002c030409140380c62002502c070040c1c030b583c2401721003004104401c29614501400709940c800d078100440d900b42501e580f04505520b9014000201001e0078500c9420000d541c0c2d03a14540c081c0b41e040e904682c000c03868480750b1a14034110000350400309000c1c4201c0c141560301968413040c1e40105800070f5180089001a51507100e92004401e40050003881582d80c2c905000100741c03c2030003501b685004070440800c804a00004580485203200001d04100d985501c0c4c0202c241c0201504645142c01000f000340842e03441e0103564000e9001c000c00680c0e50b0701900c108000c84400d091492009000500800496000c1c00500f9501201c43c80c0070744d55903600702004654600458002c5d83e030015040741c010400642c1584940d0585900d4412500300803080c501c07d0300c115505151040004904080c00c3c40703a00482845180628852000703481c4081d1030f0700010301299021a1411001c070400c000300b1215241c01c51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 535526654 1250 535525404 535525427
    0x901080d0c020103021e03040c090c0203070c0512070b0d05090c010903050a031110060e0603060a05010e0414010b12030c15010605090f0d02030604030c03113d0e01090201 75
    0x2402003820030400c0c5009040006071450290505902240210101c69003480d04001d104007020a65520701c0c0c035241030100341d0054000c220000d03242c0401e00d90704a000104541e80542c100380c0310300c0064600001c200290080e010003c03854011050b00059050003d80a002e08288260001c903403840c2a40c545890180c00805031030400c101603008101041c3d01007401c5101d00c2d010f140c0980e1544103180d542c0d10f05035000010200340e03440c1000001d102c0d00a4004240168000c900351110754940342d05903416a042801205850121000481c001403072141010011440316400820001e620314001907510440490107402a000001d05050610080c4018070107078541861030b0b0059414030700020580c0c05209101030191003505010300c20703076071382c90b00362020b040d4002e040303d040386060302d0028120720400da01180443d80c08001214080004281e00300d42c10100781142c900c0030a0416051685854180c0a101c070b00b0310b00307540007104030050155164107060343c00041480d01003840014010781000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 535527904 1250 535526654 535526669
    0x40b01080f0102070308060915030f0c190b0a0c0c03020a030f1245090e0f0d08190e0a06150b090a05060705070f030f0309090203060d0308071103040807050901 70
    0x1002604c2c0026044804550400710a440c08040341c0c2e5010145c0d221514090101603040c4140486481e407110005002e0a4580003501e00c050104940d4010210854860040c8080c80a007808001242441891080700250280700003d100c41e40c0c030340100702a080a50000e4548002000340001800f0103c2d5600f04006040d01d8066000002000e24194414101140000303c0d0048000c40e010a010480a210307a08800a90080c2065640b0302000003440460411100d900514610302000d107400704104099050311f4039569210341d221405681000060340842c0b102c90b40d50598a22410b804225075103005101d201c0004202d00c000b9400e82120566034000748910f40200f107509141c1c4c507030f00c0c420b1081320340c1910034503290390451501c1c1e801c080c030310340040c540c11000007000000c0c0003130b041d0071084da24080d403582c5001d41e0b00c0301010010fa00c01280e0701a00641c0204074000024070498242d54030940616040c1407910b017503c0c070503003994425400b010380d03170303119800500040c54068440d500620b0301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 535529154 1250 535527904 535527907
    0x21021c0f021206040b0114041d010507030e160e10030f030c0c1a0d05041e05160b0304020f0f010210090b0609010b0a0f050d230f0705030910050a020d0203040b01080f0102 75
    0x50b0f84201d1005c0c07050190035500900c0d004484441e850700d0704a0329032a0484c0c0c440010104241c2c502e82d0003403000700c17a5040020304000666589101c00b16408035035489500030218594246051719240440181203c03105521024000004c10100c0100c40105e5220360b840694642e80b0342810081c18000d5001140c0243c140c1c1d0500b500110044100c070880e1000070000324540e690f5081010b6808181c40c0401e02412629022104101e03001ca80101008030428004e01090780301c041c1401103000448000750051500c07001460300d4074012135901208041441150300e00b00d81d00b540c04e0151101048120380740c41b0040d042c003ca85c40c0094125024050061425040c101805c0c1c004182c0011004502c040c0200014840d0744c8861a421031004020301d2030300694400b80c0c17000c0300c010812080720300407001e4240c2d902041d0180d00c98004c0345e00602d4242c0003443c00b25400119880280009030080c150380350300700b003000b0320b075400d07400518071aa008242c2d1100962400011f40c2c04c0c0903280310f00d280564130 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 535530404 1250 535529154 535529161
    0xc12020310060c02030705030f06090f01110d0b0f060a030b030f0318120f150a0c08100b090103140c0702011d010801060f0e120c040f020421021c0f021206 68
    0x6000c0e420300d048440310b02c1d04100f030a0a03400841e04040f0700780c200a030503019240404840110005e2480e004112160031078155111032404035088030085500300b111404104400016400700c4d4000c6280304000400c2180314440030400143c80d0b50001c1d40000100f511030010324410704d41403044440015040c405540b84c05400041400c04140328030381c0500c10b8100c6c801050206108200d030400d90700324102140c500e440c07403140c83d0070000070884040e50164180b0103681a8503201780c4116018103240743c4035080d9642800305c064815002452014109659010401e08041c03a40c041e0742d004800d921640da070341e01c081d0b00005200845048103010058804e04000710566481040541103841520b000340c000c010241c801c5a18100c82c9400303991007003040d0008084900d000c1180749070b03031200722002c01803054140882004e038050741c4100320481140780d01c00310b200f134102c25600380317031a20040200c0415201b0603449422030301002070035215030f9100c6140c50b0460070001c8100710016403003c0180020314 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 535531654 1250 535530404 535530421
    0x6150f0906090c1908040c1401090e1e01030c050a080d05072414010512070503120c0a020303041e0e04020306151f0c0b010504050115081009050a0c120203 68
    0x40302500260180c1e20714400034034010303590003d680311302018011448a452a8080c01040003d040c0e030190b030744c50403c45000449170500d0700c20100c2148182c455800740e41ca011b01d90401c921000346160610585401020001440103d005000e1441a01c100030301c1e03810306040c03003c942102e4115004a51115040c025031581007002e1f110b81551100da900c1203115003050302c000392a015074a07070017a1420b1480c4000241c10903030341d4505a170700903162a140441d816149a560b0016481413035003580140c0b00022030f0300b8802e0002c040050082c022108240b6491b80468138540c00b603400b02c903420844200d10300c6916454181e4400510a00d206c015060425400194952001070710707000100901c1c0303095220b55103482d503c03418a032002816070302440e200c0d8503024000c102c5205080762400c08801c0086034900e403a101d980e050340c0e0000ea01c042d0702c400c8000262841ca130003503e161040c0064206c00a2141e00c51b0245d94070034607000001195440c140400030303200718105840f00e40d407180180200031400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 535532904 1250 535531654 535531669
    0x105070207030f020f0a030b060f010206240d0c1203090f0f06052b02121303020304060c0c1802040801051b03070c03142802070303140309100e06150f 66
    0x40f5000880f1102030a42480028540340b020800c01d50492480300b0000103200403d80c4003071003a442520410000e4007000012a101d03002181d1003016135801406084694041c41c8078070b403031040054819090728415840e0313402c8040c051303480000d030641d200e5455002c059014640388021f100f4140f018110074208044990140182e00511003044004640640050007440104405c455458100c42ea00c10115440c1c0f030103540100710107051300c5030100101e0450101e03040b003d0051074140e8041c41c00d250502c3e80032544400c0580090b680b602c00b2010104031f003601d0403811aa51083c1d1400140d945140940721070941c0c4004188154920f8400420f020344100a02200e50107003407440c001c100d80c001844e0a4400c145403420203052010007080108015030b80884030000c0001015040d000000c0c041002c0344c0d18511800001c001405c02401e541c243c107284000343d900076040c2c4064a08800300000307000221480c24102d22a41d80c03002d010701240c0000f00c4c010b40c11600c41030300c901620400c4000420440b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 535534154 1250 535532904 535532909
    0xf180e0c03060328080c15040c090b0a0e04081e03090a060c022406010504030503040b070629010e2107030b0c070b1503013c020405090414010e0f07080607020105070207 74
    0x803400000c012401a105202198441322003015901f0300e81818184881114074074040d0140e41d91504541402c0e61510fa8030100490f0745040f082481542c1d00d035241252034010007060481804400002003401025202561049480d03100800c1100c0c03480c20301506907039251203040190b4200d01000b10107403600100d580d0100c000c4d040d00c030010b501e03007800484841c402d562011b049800b01080c04514401000e008116a50040c9070500110f654410020710a480c1402c002c2d400c2e4845007505030044d4000c10340c103910280003c01346400c58107060380c0314000e000390380ca00411b04d8200040510401001a4606420540c4614a142003101c15500c0b56403960010f080c500f4030401800340d01c807059809400408508010000a0b0141007404112032003262048402c0401350079121203a020141191007654101e0704000d0000782c00c1c0c0ca8548820500700c00540ca450480d549603090015010010881a405444200010101c851a000c2c0450414030058104411641040d06004101d80d000501a0a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 535535404 1250 535534154 535534163
    0x80a1e0c050d080421110601141c0317090a021002010e0c1513031203050112120c0c0b0f07200102210409050a0203041b060f180e0c03060328 62
    0x30f140c0c80314103003601051a42180c84100f8200e280d85202c0d800c2d881400295600c2d803403c103c540c1662910301c2258110012188941c006d0390180340b04402807044070a4070000750207410401e8102050003100c031140130301150b94400940c01092504114145117480b070403403540c603100030091402e4654001da190440c403c0700d64414003004604440b18181d1800701c071603003020b9100442c205a50781c545140d90f00160100400881e280c5000016100e000703240000c1c12582c0210584480000342609032458000000150b94032080d0910104804c0141402405a2112100741a8803903106141003a00d07849104120082e0305141040c5c040280d800054644048035005ca0062200d4240d021007138050203140d1280303107070905020912000c5041603000358002d40c0200740350781500000c040104440314851040c000010b0b21001c015850720310550824001301405655000f103155144038894083e201600d6800d07195400100740076851800b0407181d2050070601040340b0440207904030544803480509000741 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 535536654 1250 535535404 535535417
    0x1f030303021803060c0316120c0201051b04030c06200709021c1103062e03060509071107061b0803010f06090807060801050616050a14100b090a0b030703080a1e0c050d 73
    0x1f503010b00070380d8401c134082c003811030411036085d50882c002c0c06420152480f1034048179020690a40c2c0401800715419603800200c1414079500e80b080c102c40d601405144890400d40303442c0e000b0b52070345007409401c00514184a01585406c285420b101e01060052148030025160405107a00041480c2c103880d800601118641851079107002c6036071162085150718904181032042140d20355030540c1c42241618410794402d140c2d9521201c00b031341c807200d541080d20360640c06858100811885040004140c264440298061041c196a6403031541c00a07013043d16000b604900c28085c1c0b540c44080c010041c140600184521880c1c0b5102401b080f2042c00b5440c0a05d000146041040c41c03840d103203d1440781d211080754252040390030006851591070b0103e07481406101d00d80803461030070780036041341d1324001044920b054440010300c9008040c0c881c10070350140124080000424500d401402021042e40c8030790180c5180c0f500f15031007140315851000c046c49a5000540d020604c0010032040e0340c1c04074100003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 535537904 1250 535536654 535536691
    0xd06050705070f060207050601050f0f04050c090d030504140a060909050a18061418252103030f060303120504050717150f0105010c03081f030303021803060c03 70
    0x464852107088409841000880f0090003000269402070985c0c40c05001610800e903240c00030000030441c03001c40580e001007020741c145200d2800d40e101d035801040f0848070914000e4250040f4240c08000c030070540100d03034023103410006204e508882e9018094216000d0810605065000c1c099050701e00544014644d107400003009481c16071300c4400c524211b40250903c5c0f60544c0352071005041d00c5103d40804c10003040204100000700800688608918805000d00d2100b0840d03503030b000ca40d04848201d0f035a440341000141c1258074044c04c0c100301403400d14201980c4407810701a042d2074210300005c01c1705161510800c04294006900c5103641c2c1e1581713001c01e141c1c4803400c10b146007481503000101621907440b40c4c0c00200d80d00085084540c10050501002603584450139240d809007441400d0100c0c00141c89800003911500d0b038654090040c4480d9043c000000c4180c0c0b042c46c64503013044002c280e00241c0071aa0f082d0700f5603440c80d008411002441185040034003e6018000604000902c500a5189 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 535539154 1250 535537904 535537907
    0x615030b04150b0a030b0618010e0601110a120816021506130f050903040609080a11190306050103030c0606091a0105131e03020a0503030301060c1211190308090307020d060507 77
    0x3c1002208020042c4041d65160305000000d03480c1940c01922a07400c0d2602c1c0d0b20110101069241268141c5e0702a034926600d400056441c0071440f410003c040c0a50820800000c00501d80c2c54801c04080c5c2e00c0a6641c174124610840e00d00030b080454055500103540140400c80f03508406505c034200740c4110700380540b00a0310310050959882c2c900441c030300700310800001040000141040756020394a00600f1961a10a07030303120501035001a160070701ca000d02440074201699490102200b050007020300b550341c0d813540021264207800c100c00180d1101091010b002c000e000b400090010104100b02000e0b955480c48035001d0340c40805418040c010a00c44500030300505104000c3c2805043d56030021079049010b0049013050004074403962491101090300d043c0041581d068800ca5200d8200395550398441c0f510034030100c010103003080880851140821014401803140c150489801c80c0320017090310f0701504040004019044582c824004600503130340e1b000c0703c03020164101c40d000a484d203802c0340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 535540404 1250 535539154 535539161
    0x605180622020a0806030606060f04030f02190b040e0f15120313080c15090102120c0109150213060e013c020f0f06130b060a0503060c070615030b0415 66
    0x28400d10240b0110344084080d4002e40030a00c1945c00703c0544003903507a043c04004050244800b0040803040901080c4001081c2c000c1d080d180b2400108446c0039110161072000003100300703810001ca00303200031808200da801e0007841d86030000c90301c0850321000d182c91101c01c160300455282c11031240b000c43d44110399400060040f1540400760240580403a925101c1c19683c0d00d0228034101e0045505203802d01c0344403d00401d0f6444010142d003d07000a911455004000c0d402178010114195a90b0304040e00241484007140d40342d4101b0300c0b015880d0405081e010740c846045900c0344e0284030580f440c074042c42e0b1b403085441085108564072401404141a16640640c88880380140540182c0e041c84000580000b000e1851a9402c070807140c401085440c950b807581030603240a00140c0c041640000003404d01000380d40d001101070305034180940d0b110300107450840300303131546104a4400100b81c41400100c1c0514400f03800307194602c41ca11455903a072803119500091000c1d020340000d503480341c541ca08070340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 535541654 1250 535540404 535540459
    0xd05010b120403300e100c0f0f0207080a060b1903050309010309060603050d09030b0109060e13060236030a0b0f04030207030c031a010602010507120b03100504060b010306051806 78
    0x25800394002c13004082c06004000d08840082d4500c03c00c0060521040c560183c50011311326a9035200700d400f500d18042d00c0608841400c041036000f0540f010510385010800384203401c1c09404041003055100c03080c0490880c1c0050a00a02c8003030a6045c40443d10000440d00e030341d007082c60000b4508865003403000c002c0038a034000800e00c4c0165041240101e40c049421400d4a001e02040c22040e41e84601c0901102d0ba1449907619000380600041e4046103c0ca0603030090301c6c007a00c005444c052034a280d40000f0030141c400d05500c00c820300c24078488000303410500300c10b000045d0024102440035071203041d100c0d04010b2082c46880d01c610005000c052080c09520025588891642001c82e12842c1c2504068041e100b0704d41010104400002e03182c0c170502510380101c0007074850214131044140e100018204c0c21001c10307050302c01d14100328a5401070b4424644101e0042600103100f003c0c0600060a566843d402144038104580d01d410040e611540000c0c0c00c0b2a044450050b402c5980072945003001d0301c032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 535542904 1250 535541654 535541717
    0x5090603040804080606011e05070606180f0f061406160c0602010b040b0114030420061b0106060c1716020d0b040b0603060126030d02040b0d05010b120403 68
    0xc0288000c121490019000703031244141aa03202c1e03540e9100440311a2040345074986031411410140341d29074080c100070103003a03009100229038203803503203203001900c0d040c92400460035036100d07014503407005648115074030b90245510610002e13140402003040c428444188512a140004810b800140d16040348507a05070301000300e0521070358420000e8000c044108181d40611300703200f05007149611640c00d0981c1e84a44494050558540d9103e40240701e05005032203001d00c0725003014800b075603100c0002d0001115846485550352048040450947d44d096000c1814080c0001c012000200743c1d8200da100070415801e01c0d030702e6071080f211050340754440f01c80180d00010700c1032100080c44960401c907882a030169809400a840794010f0680d520b000344114401d0344080541e040c00e414590004140b10424541281e0a01c0000340302a42241e00c0703940b00301300844000544425080c0300780941801400c10790740181c00c240c1451800148c03050300410040c10030541d40b01c0d44403482e0601c1000100880c0c007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 535544154 1250 535542904 535542907
    0x311040b030a0225060e03070c060f020f010e070609080309010801050d060b0d0602030411090c19020a1a09101506031e1514030102190f020f030a03051008010912050307050906 77
    0x1c04948044c500008815106541420b4103510f510740c00000b100c68160340420140807051810f103045983d8010000403d0444c042c00c61034006802c002d003d00400d43c1d203483e0127007581c13610b0824050001d10495129541e0350b04184100602c580e000b4a8042c119030040d5036004080b00c1522b816030040c00ca48884a40c805046004001031041950185105134894100d015801c00c02c10100040300c1c0d8205c6403811481e10420003191a80850242540c291617030b401200d040f8121031340c5d02c00d0280c4d0a040d07004a1007040c0f8040040c00d2504008050024805100422107500d4001c070f5281424141d0186409068032a003c1044d10665146080e600780124071041048641e0355100c400000b0841c4911640c0c842d803800300b41d64030b02d818400c0300c1075001e04c1c2000541c5280d544070241d5002180089007001d5004513400c00e03001050900041100414954002810b0716100740800315042d55500240400da00d080803541c00205c2d07092548001c0310982c1861912507076646c07401c0342c0300c0c45010702e0143c01040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 535545404 1250 535544154 535544197
    0x9030f0118030912050a230303011203080f04050712170a0905030c1c0b0604061208070209010b0c060a11040b041206110310030f0611180306070311040b030a02 70
    0x111079641e007801d94407075070b1074000c00780c2d8490300038071000130352840074080d40c0000c152100003c80001d81503140300c4003445600c0000c241075900e1030454000768400c401d100c0305800307103904041e4415a810ba100500c03540074450b0341440e8450b01e0703440d4403034060310480840580d000401e001c11003028103260201302c0c03c2c49641d2503161400814144051081d41d0007032150b4404c0c401eaa2800c0d803c4881c882003801e08040f59904181c54402c24078074060401c54010b0f654100200c1d42c0200c08a8401029009000c015601c200f9403050005800050f444200200001d22100740118030101f01c0c541c0050340b1500108501400d40b00c1c411035807040381e00000030b4000000300018046402c89400d0f048034004c0908021200c1c08400d42441c0c0e12084486500442003284c0030f00000c1c1c1810301402140f8003480000030085200321016032644d010072900c00040000314510307586480c041115a82c00780706894140305110703502a00f590580140c1c01070080d40f0705c0210002d226070403658147c030042c19007a0701c440100314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 535546654 1250 535545404 535545431
    0xa020c01060911071a06030c0d020f1908100908031816090617070303050423041805011808030a0c0e13061502030703050319150303020601060e012309030f01 69
    0xf0300804d03080303c50348184c01200540455180c4240e1061101030081d101d251000b00411280500520b0100d07131005c502c440c1c03ca000e0315400a4401600b104c0391140d05c080f801c0480851401440c50f40c2d686126050400b01c40011354180300b03a9402c0a804141188420325980b002c5007010060b01e0454800580c4a000064110443c0c10402c11520f40e281010418040501e460303449122501011740840c504100401120b0f222980f154807d400705041500a08a15400101916924411604110504c4030000c0c2413110a11980801940545491201400036901c00540b400000d2004802e2503998403990f0345507014800d00000d0300c40003000180501a030000141c010111402480f000c0c56032103550684041c000000c441e8641d4158841074150b0ba0303a44170740d0b420403e40c1e100c100080fa403200e008010341000b14915102440c80781c0c0180610307605000004000154058505041040d034039400018161540443e100f1044071001540d500c950000c042890601c03081c00035140c942c079000c07048090f0b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 535547904 1250 535546654 535546657
    0xc06020702032109040f110a0f122c0628140a0204060912030c0602130b07030f081b0304140f060a0911010305040305091207120501020301030b01050312030a020c01060911 75
    0xa00c000c031000c00c1503840d6280c00008887c03500080c15220b1104000c1d05294500030b810400400c0218034080c411016019064002e8803602c0350383c41e41180600501084518412020107071102103103001345203d2600142e03030062100342610711003046e4506015168403245d03e07080607181c800494012180750402107861030080d88288036140010340c5184004c04c10b0101c001406c4c181c140c160741d034103071801d05e039407140030013503000850508482e4075100c400185000000c000e0a10b040c025210141100040d49010740b8141e030050580c0304200e1702c1030084039000035440540e07410076000b0700d0584400d240a00c80514123041c50036804483e11440b02004041c2c900c0360408440c1910581d070b010000c0000000542c155031054a004001c05c0d0180480001c9082000868140d0210141141c080e2a51000710190310f401c201e4099449940000050090240f9003d81d1401000154010440e4840c400910001404042d01c43d010b082d0300010b04614036142504140003410218100700504000544400801e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 535549154 1250 535547904 535547917
    0x611120103060e2a0d0f06391d0a0b0721050a0305090717030c010e070302060306100905041104050103051e010b1b06070f09090203070c060207020321 66
    0x109080c074030449004040444d0309114800c070382202c0041d10701d40130083d428040507621015004504640c51401103480840070000541c01410000b844100648000c040c100c0041c54078901d440300e40d200b58010407a118040d6a2136111413514030040a00e00417045040741299803440e038000c00f0390b1000b027100516000201016480346001d40c0020a540e000d012140a64a4003000031560902504070068082c0e0003090f44007100b541601d10198076100b001c1600707405414100b809600c08031320866000c0091145060007030f901d20042402c2842c550025404e840000e00280c041d00340442000c070041c1c010003184010340340081c0b00340704041c50404603214980044c401c20780000e0070700b00458055011b042d0413030b01c20701c1403404001d01a820503281c82c40c41da001100040d1103a8240d4000c84815109100035800303a4250f5a0380b9103440461200100032541e01c2d00004a050301c1001403000b000c2c2c000c0400040c0e030b5400b804c00340c1c488185000181c2002000340e000c040c04098852882c0340c03104910000c190 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 535550404 1250 535549154 535549163
    0x1501110c060c010b090c041e06050f0f071403041d040510151205060402040b0d05070b0306060904020403060608060f091b0414091e010b0904061a1206070212091c0611120103 76
    0x2c5c1c8d80701c074005696100c103040c465034010034030401c002140415008014004081c0025020345840c110340d98103c80010084a08420790f013020405101c4130a0b00e28052030700c07100032180c4d4030075030a060f16042d0b1555491340015031007980d600032421184224000070030040620340c1c00030710215618102961142070458040380b1541c9030041c40c01440c0342c584525090306401000a100b51811f240c50b44001d64000340c03559030b11201c244519640c0da9100d000900c06503200306030108046291006880c40c009024003562240e24554042010900001440110300c5030f130b40701d903c4214403410307000c680140b030140080081d50050504001c1603110014000c40040c03020f080c51300340131411210032801c039110b0b0348000341c0c49400c8034003050108142d40c00c10b04528164180d03207680c00d4002c40c0003449490250844c0b01150b0440e02c1007092540d01403200c0100510340e403c01526119000d0000340100000c107890001031080020808144100c99220307034010403641110030381c0c0301240f00c02880f05900034441100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 535551654 1250 535550404 535550429
    0x601060c03080f04120e011218021f0215100f0b120106050c100519020a02070315090f12090807090f291e0306010e1501110c060c010b090c04 62
    0x11001c4039a0f0701071a01c04e54001e80350315144106003008840043c20380000a04004161b411020b880d0440d10900c0c2e4480b000c01c0c01060b40192510520450f10556000001500550000c840681c0c0c1c010510410014005201200325500e00c607074240c0c80c640d20b03005003140700c8011101050001007500217000d003911458990400b41c3e80c0d0f00c0200c0d00e0b8810590120b505030041c94403c2c08100302a0417264000514119941039842418591012604101c10090051744220380c10030034404080c00c001c050807041d807014400947e082d12604100f1007140320040138025002c000a1106100c2c40c3c0d4600500b80750026104003940c4c2e00b594202620994004480da03600e841d195840a07070210708060f4000f400c419508601c0501c0500300311707007840070460f10780480940550401c825502401350314080e01c100140080300c0c0c10820801582541e403003080d5814441000c80034440c0010000f849550400c0460780a82d60360004800c0c540500103540301141c0001c0000103100156003c00c01400c1560800c1d03400c803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 535552904 1250 535551654 535551661
    0x306031c09090c0903021e090106050301030203120a0c02040905061e011802070305040e0c1b03030f04061a0405130203160e06060a0c0822050109050603270601060c0308 74
    0x1000ca108000820001203290803508000c040d07159002a000c00e00b00341000c00b07005580ea00414007081c028891020307001603a0b10030403c07038903207085400d001d0304452030030609660466011a0341c0c0c68180c1c2e076403c0132860101e55041198407c6101d5000a50701600c14801c50000b450180c5e640e9105031002c10000e41d0a086460041c024070450341d0485151282c030a10190385140d13001d0095010032416002c002c03040002003990190301800e00e008a036054413565940444c0303041d100c03609442440080240d0002c00c2480424a00d0444054000343c100900040254a062811170500b14505465802c03e00b400100461341078445040b00104d4004e42c00c1d5074070b02d0020340840034030329400c0c05004840502440414214105070020b031116507610709041c4030422a503206d00c0c1c00c1e50091124103a503250074010b21440f40c001d50300301da0000c0c2001e007403e0b51818108400180c07240402440000c1c44090743c2c1c5503040d00d1407411221020200382d0381c142d4204e561a140014040e8005107400e401140c0d000780170 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 535554154 1250 535552904 535552933
    0x150e0903090d06050c0403210816050706110c16030b060901060903140a080d090c060e13020304020d02060c160f050a050d230d03050105060f16081608030603 69
    0x125000740400030507420480c0201d030f68060091101500140d003290f8140004400241419103080b5170a83c40c048001c5802e00b0b142c4001d20901c4000c0407107046a00c2c182281c241503400906403030318154000004100c031003080c11020907500900f600c0c0c0c0f40c144500080c486610001c407031504190f90140440d51101c0c2d58081c1440030491080c890720000507000c0c4000c00209000040c8803244240980540b1050303074541e100c144150b0408200349265030b694088071010400c40c442d07680010540ca091103035440c400e4000003540d42400c081c0c101c0000e41c00200040865542c2e00c90340101c0ca900400240e2103920000185581c0c0c1c1b0108008040550b2100b000b050000f01c180203542100c000414040741c0c0350410003032254442e40364104440350440012418072180220040a400c40240343c01031240354410040242034440c103a101d07500880c3c007001003020300c0200d84111130000c511441c102e02052400e1904c80d005214170000b010040121103120020407052134004d50048004404856001c00304502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 535555404 1250 535554154 535554157
    0x8061f031e0b090c0f0903030a0e010806010c20010e040203040c0609080f030a120e07060e100806030d110f15060405061806100905130504050f0f0304031113150e0903 73
    0x11010303840589000004d203008208001003c0c10f8038480c80d038070300305100100468556042020340c0004941522600e0b005540d00903c4141d100700d007440d000303030290407503160981c03000724a0380012003801990a2020460740180644141200c0103041155685003d04010a00c1d01c07060061b50700094000100190451000403099503031102c8001451078030f102c0324010307294200d00c8040059140e8681c03200c4e0b03c10080620000b4018015502c0326403070141c1c1c0f8820440740380800702d03a40f821f014001c1c0912009840000329003070f004280303080000450109240c2c007443d0160100c0041c21a20550004810029082900074080e41c010b0720248100c2d1a41400c200705070300b0b0040b600b554652200b000485610f850102518180e001d818141e02d502d840d5404106510043c030782e150f90381034896081c0310410104103e810300d174003000000f078100f1310940c101098030f9124905c4050310750000c0030458940303a0355102034134207602d403082c600700010308564100744402c2e802ca1180801028240c400542505400700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 535556654 1250 535555404 535555421
    0x503030a0516090803041211060c010608010f09030905060f1902100f090203060601030b040e0f01021309050606070f060213090903020c030304050a09050907030b0906090c030c1008061f031e 83
    0x401171801d003424510041d1442011210a80b09140341810341c4c030054a82c40010110b281303503000040b95041c14001c05031f0070355a0513015000007615008200e800700764049201010b6441c11038690390346560540070340755640501d900c212200d03103502c242d5010150f00014194070300ba214803c144010301c0c54010040444020040180d0150003040002e01c096109900103402084001c000246199490b03400030300c1c015040702c807110036070341c00280200c1818135507001000400c00b03001c0902003840e014002c201c00d40074984c40141910b01d00072841e0100038898040c0d4072114151140342071060303540d080d072801030014401d0a0303026010b903503401a540d04021007100c2c2510310292801c110302d80340004c00d9005000041c84107050340982d61003c40040e402407581801031074200300402c2c450606801d40c906146001ea00b0078401d610204949200b5210b950840e503049006007002601340e51010301180c0300d268a1503100e140b0f02c07202030102e117149800d684001e0a0b28008600d44484ea8502000c080c119030064 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 535557904 1250 535556654 535556669
    0x6090e1308030a0b13181707030e013501032108012705041416121101022d070f03050307060c020a0c0807060f020d080619030503030a051609 62
    0x400025403140916001301111640207001504107031241c009001c11542000180c09000368412050014425803404031008201100d80c228506111650301a02500b07200c04140d060101c3ca000c0c001d0384c900d110440c0e5550b0300815120400c003051006810794070751000d0000711426002198021401c07038075840b01220076522a100c5101a90030030b01e03201c00b141c014240522811b6425405101c088199010b1280154455014a04200ca11005c2035080407060482800d035551603d40070003030001100107607548590000b544100103c10f03200100d060085152036007498804113190070b00da44e0050f880012041c01620140d03594076072203041001c1c4290391484042d100e54000e024007004075903d54000010b2800c94012910924440d648490403001c41e54030071b40040e08450341c10841e082c0c0052000f1080c014600c054001070000e144094400310004c5c02c0180a500c1d1b80b4040400710790882288406190000210382d1070b4138213100c0c0307503001e070004494840910904801000c0201c1c005c15295003900c039803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 535559154 1250 535557904 535557907
    0x60d0f20040e2a030f100605010e060a050d020d0204150c06050718091d060106050a0807030603021804080d020c0303010801060509090607050f070c0801021305060f070221030406090e1308 82
    0x36004003c1401184124582d41406000c1d0b02c2d421541d01000400c0040424100108001e85400300240c0001e02140415000c3c1400b048000101a03002c01260041083d8100050b141d00d80c0d82028002402503400001c407080c0c040718000100c64002c200602002d03c6010280b00b242e90718401110003100038a40c04180340f07800d41d0244900600d58008102d0020941034151101e20780100052600700b080c0c1c000008103100080c51011250300c020b03550391125a60030140300750f62441d80418980108a0b00c11042c0c17500042c086400c0015050440c2c00040001d0403c3d91035102210046450713500030b00c14240103600c2d0400000712070500c0014144110b1407500641135503518000b00b95101d9010102003210f500041116000258042d01c010002d0b00604000684503040300c01e004e001c040981e00710610800c01801140d0a100c500e804441100e54151341142500500060a00c2800300a0b02600018000803c1c041100350b44541410100c1e00c0d650a8040305884c3c0342e0100356200c2ca00d11014060480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 535560404 1250 535559154 535559203
    0x5091005030609310510060e040b0a0b09060409060e01060b1314010219050705031f050a061401050f120901090b0a140a090807020a06030204060f0215060d0f20040e 72
    0x260454140841c0340100251040d40340080341c0d000c107c1d021a00450009010b020038442403003580c0c0c11160b0300c405000d10410020040380009241003200500c4188100e459403202820056250091482c0301c07080c4000b806900d40310030f0035000a400200741c0b180403040101c400240620200002c002503041030b0060045641e0200c5208001e055421055419104500c80000c56440400218072145417200c024034031100f89070704500c2540c0019050044003400c0c200b05100c85581d58850f0b880754602401d0296840c144170701c0c050b03620300515a075040c49000900c2000f980e03200c19000103010b1840794050305199904c11130084120307040c07940d981003009402c1e4000303080d021059000f26005030040858030304118150b400154042000d42001c0002a0042820801e40d6003010810310082c600e40003810418a400b00048100e0718000e05e101d22078080340007000180f111040b40c1c484d1894020b00b40340803060101c8061903900401c3c0050318016031410800b04003600012405c46600d15500c04089043c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 535561654 1250 535560404 535560481
    0xf15090b0a050f0603270105071115010501050c0c041d0c090408030415020d05040c030209010609080a080307050c030a020303091605030d030c180e040b01050109080d030c05091005030609 82
    0x104003c0410410385020040b2010074040c81d00004d140c8906c140000c03420746448503000704400030038180c40a50fa03002e401601506c448000d11541903c2c82031030200d407152020180c4034078000e00c040300c56801514056016640308140a2800c45031052881212848440b50007488001c05040b00c0151400d42e003800407600107046084040d0146845071005401c09024807602011a80251401c85808188a10420440c02c00d004124010f144a00740391240d6854403c1803501c1c0c2c50720700001441d031310001001900460142d03098500f4054004103c0303494102c0c014010f55290f00a0703d0070061485940d01800c603204480c1c1c0a0029641c024000d002880c00c0140142e000e44405141c0d601881141002d48404090909440c002019010070300411820281800c521038001030300110b0400102d00c03021b001e24440015521410031203850000350303130080c03940100c8070350184003810340d0300c10748086580c4489584040a076000d6402155046e2490b183e010000001c0000c40840342140000d408002a40c3ca = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 535562904 1250 535561654 535561657
    0x825050415050f0d0914010225140607090807090c050a051819030201090504020304110d0302150106030f0c031a0f120a0b040b0907030203070b0903010f15090b0a050f06 74
    0x1041c90800360f007054886070741003841d50450300315048210f940e441c04505101d00400500d605404c044021451b0107102c1680442003000102c6914420703c40300c1070b0304100540c0201145201c01180c0940c1c0b003505103001c0c0145100720310702c62101e182c4944100807031000c1c11845003110900d525220f940c81c100d10001c041c0c60507002903c4410f00e0440d18040601642c9407060111070020171500c03000c41c81c40c110b2002400b2000241c2215000e02d105100300030004107410144aa900c00440301700010b98405d00c1c04a2a14219010041140d16140000601030760150024007504070a15814403000c50250400c42c201c513840008248880c0440d911b003007850401c03074015250070001400c4d2401c0b000c020440d161400c51030360001c55581d0304070001c1200340030b00c1c25111904010100080c112491450300040d035074100600902241610004819009030b0b025484200054200d20041c001904141400340200700948128041035040c17030740e0b81015181241c01001504c000400c803d80032007219050000c41d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 535564154 1250 535562904 535562939
    0x8010b0306180a150b04050108030901030608030405210703060f140606433503070503070e1806090901020703140d090f26030103051b041b08250504 65
    0x10307612017011200e5103d5010b100d0207800e10400860303944154500040441d41681d00c280d00541040c0002e02003503850450b9a1424a42030704080c822030031014000381800710a030310040c5614600700405c4411030700d0740c00680c44003542c502c04100e296102000d001f4140b0442064074582d9080000c50b42c06d08aaa610b00c030444c045c01410014110b0765003604051224249105403982a80307850442803a00d49041602802a54404920412000340310074507080e0001900c41c1d01446004000601410b00c204507241c010540201480c0700d000250100502403001580e42c035000e0300ea0200041c81c5440e0500031941c3d803030380c03640e03449001041c41e0318550701a410800081c403003542c4074122030010402845004c0b001d42e014050159001e81004004600800c1d160520034120400b0b000400201c4d030003140202c03c0c0840d14003202034040c440400100102441850490801c844c1000d9113880c507030100f05280700380c0046c0c5000700c511100300680001e4410003291600002c4013000144282881342d10100300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 535565404 1250 535564154 535564193
    0x1090e071d06070302030408060a1e052d0402010201061e050d05030409091a090c010f0503040c050603011701050a0207121b080d0207030e0a0e01051504080708010b0306180a 76
    0x1da0480440008210750300050094005910214050180c0b40c0280400c0b44c01000411040000300207107403072000b54665940c1c0d1100ca10355078400140e540d801610380180a1403800c1848010303035189200c1070300e8081003518140d00662a0000110300d5002c040b500c001c030608013403403441d03016142204000c7c6090310342c04100c41d41e00091000080a10240c042c40c01000c0c8248000000e56050b004c0c40b191410006002d44065441454448442d0345c1041860443c0e11070b40c60510780d0390b515801d01d024000c00c2a840903800ca100000001003118080b407200b030340780038500003e00c80380d102c1442c100180d02038001c018195580c8148407102c1c03640102130442d280c00c101400000742207140d40302d28040390400350303002d504150002800300805034401c843c03420310b0004039102d103a03207030925601d4640300c403050180740d02408110100a429074041070540d4002c4c80d442040300c04031610307962154040c1054020b9240240306030008115007503039400d403540c0c041d2098801003101c4043e984a00c2d62a510000c6402e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 535566654 1250 535565404 535565447
    0x60702031509030712020c0d1130010b18010e060d08030114090a020a090603051005190518150d03110a0c3002040f0e031804060501090e07 61
    0x1041810014107540b10756444400386440340094100884815809000b03e02103410400200c240b503036504a204250940181074601c6184000d004a12905601942461144424100c01d82c00e40c0e0b42108400c22064840c0003441b4001c1c1d160203000c403d4000c074038544065100240103008007400d0000c0d0a600000003010440070803202c2e100e05142e64000c1c0c0202200711012501002c050901035026030704015005000c41c680621110014070140c424041d0b101055200c002240c0c002d02c210b01820003074200106007140070400c00802d40e244036414403810f809461554600c400c080c5040c19014841d24400c0802d411044945d410849011400c03c012010720424945400100c0030030804045d01d244241000f400c003508001016511403c0102d50990042d0307258802882e045031201c1d000081c0e07a044e03501040001e50703803a04174003600003c00c0206442c130010030f00039111070801411004c181829138040006a465900442d903440c04c40c083d030f1050352a240c0103d00443d2050f00343c0716103090035080c0d60 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 535567904 1250 535566654 535566673
    0x31061b211704140d1706010c020f150310060c03080712060e070806010206091b09040f140a0c050105030606030f0405010902030111091903030804020d05030408060c0d05071d06070203 80
    0x8540c0c1c800944042d1400502a46203520240041018a00790002410005c54144000b280c190791003c00400329410030000102e00d4045403030300a028201084000e04501c400d0700642c01c0383e00d050f00116540081000703d5100081c265002d00320005140381c0654402d0842d5a030808107446410341c980b0a4201e03691359100006072008120308060061801d640c8000250400400080c500030025140c0d0900307070026074219059484100e40039070050400e903100c03a01999242051008400402d6016014070b006060000c0f641d0000700780c0a14440c811070103100c4072606d44004540b0b60104a070000e4001004001142ca00102e032403080b54058481d030000300e0302e03100603804a0b00f07550001000c0c504c0e008003c501d201403490813801d113896011401e086540d1492558800500c411005031001e8003a520518038031040c44002d208980181422500300c5046003051800c11310580d21108041010b00c0c50710010509070f030703c03d201d082040d28501d000d402c007101e06034040088680c4024002c80e030511580307424 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 535569154 1250 535567904 535567937
    0xc07080114010509060a0f090e030f0403060501081009150f0209030d03020a0306080a050a0b04030210060303050a140901090513021e04080705150d0231061b21 70
    0x121942101d0810004045500d403500340300050101034510380c403450300a44203000c0e160541e000325089900689003c980c001c4148100e509510440304101d1007944000350104c1480400d4002504903824003040b602144601507a0001b00c80300610700400318045441c0b0408240103541009824507080304006181091903000039140005142d804808a60003080440200e07030940b0402005140202c040c101c0760300c055503880d40b80c01010200812618205001c60240752003041502506441c0e5071003080015220704000e45a5000581c005002416182440c41c5084003c002c4e644d178090182c407000980da007400200a041085046440c0f902d55003400405182e854180c1201c0060000700041603445003407500f07031350411f04c00f5040360340a200300100c1d0315403412000013110f1015980550041c2ca400c8043c0030101d0b001032203000c5008091001100c800107c0300c0d0540901115010344800d01056a0310040c1c03c0c05014404000d80315034102030075400624521619000c0483c00b0349403404207034010400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 535570404 1250 535569154 535569161
    0xb0c060117300d050f0a05093019030504110a05100e13021b0d05030c040902070804030c090c0f020f030f0c07080a0f060c0e1302181e040b0a0b0a050c070801 69
    0x240d0151981510040c000b043c0383c0b51103500d42001080c13018004020300c100d0040e9005000414000390403034227464500b0300074203a000740c0e00000602003000a040720b03c42402030241000303440583c0c122040c085401d40c1490070300318001c00c450f0050f25040c0e00c0c00e2240410345014107804000c0d1b03000900c0b0030001580e031940c0e10080041441c80c4229050458040741a20b1034076841004c142e003444070030402d000c40301c9810810380c0c00f00c90000e080540c1e21107c2b4507081c0e103a030003a940700a003d450882408a08c1000a0300209003c80a541e02d01d12402d1710610200d9441180105c2c04000740c00070060103084100d050010300345d20030640b040310500b42d5240d0103240352007040b41d07080d50980c185000348403c03c50540207148a001840c506030841040080015414103c00c0391082c1600742e000521280d0400044042600c0e01001802801c0b400c21502100350b03a0114051500c1c8a50b00c5d24420024518003442e807082940c2c02c86c0c84403801c04103c580300740d40e5a407184804902c54401c08030005201a000d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 535571654 1250 535570404 535570411
    0x40e030c10061511330a15050d150603030e1c08090f0307050d080901080708070504050f01120c230304150213080601120c0902091311040b0c060117300d05 68
    0x2214140d0844511105e24080c0406040722610a042c200d5044000740c80b22284010355000711044100c0110b586454075800856510304081305080c143c00205040d0040189051181c0540d40c000001541559004c401210f0500040c1001d42c1400800307038506050f101c14100b6080a021214250303103440010b08610300e90b00b0200e8000714005081c03032840d40c2c00044241c1104090407c00f4040c00c00e07040143c954000c0b03024250040c0c00107004441107a1280c1a200e603120052402000001c07590348006119101d03082c910f200030600c00400b607a82c031014000b128410380d0061296100c1706044c030303410070281d800075014113140801c1c000080303003841051040794020852901c120700350f02c074585420740c000002540105140c034414007681d440c80e21500d4441c18420145000080e42da00047d909801e20b0049801c0b10505000c08260102811000100d040c1620342c660020007603843c1000c1c3c903981d25016000f242043c1070381e00310040c16040411481c0b000f04445051800e0500e81c10500a904580044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 535572904 1250 535571654 535571713
    0x1f0609060b0c0d020d0f0804150c03051b0406080a02030405030702091513060303120c031d011a041e0c09030b2e060c150209040e030c10061511 63
    0x5442c2c10703021410000c0701030719141c0340083d00e810114074401500c000c03640180141409000c500080030440003045204c2c0303803070780c2c1003080100a81c0c5481c0180200380c200d41d906401c800d16030342d0f03c00003d034003802d41d012140c480c2d440c24060343d2050070b03c80103504080c00c1250544800e101c01c40044e50781068207842408241158044e0b81c81e034504014880081447c1b00341358610300502400402e0b8000642d140002380d000020424940d8020224000c2c090409610f80d8000000c800020704801074100e0492846400b100a00f020a40c60400c411075180200545076000e440383c40c45051402504040d07000843d9040250074240d99444004d0721800030ae40e90082251a03200070358028902c40c3d103030604103541001c1038055500f001c101074071200324050083d1030f10800c0405407030f8419150301100d00c3c001c8050b2040c003d150004444968a40049001c0d601d94040c0e0903400c50510000e209020845146034000490240094002da4000014058003902801140c48141803201c02c40910803000611 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 535574154 1250 535572904 535572907
    0x1a0705011e05010902040b180d02042c0c01020c010f0507061d0d080402010206130c03020d060e12180607021c0809040617030307030e03070c08100b040207051f0609060b 74
    0x100300003507040720816004800c10b40d1051005210420041c2c0540b25802c0100440038625200800000e601d08401400207511074107103082e50118101c81d11846d40201290803114078070b01894407004e62504403207400ba90050303006004056580d032040319491617102060401d103242c08000d8441c40159044000b40d111101c06860354480d0030b8004014142920b400707840d245c603160801d640000c0d102c003005082d02c0b20100354021030900748078184043c4c4006650040c841c074039181e018544a0081c1ca004d04803003129018216141e0701268816084846602c015460f512043c141c4401b0001260480b400503604103070f01140810040f030290110038407650240305034580794a02803003000140c51464003c5152881a64100d1003841c100105403904480c150030081155200181c1c02032a5000d05440a0001030035000001400800030503a40c0706000344800501c5000c0c80542403106070b2180d041c00600c0d90744920000002d84120302c00320342c000c0b03035801c5c00071a013183d64000c42c3d000c3d02e401d9000784101050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 535575404 1250 535574154 535574201
    0x50f15071e1103030901020a020103020306040e0303160f02070f050405040614102d1505070206130503120705031803010b10030e06011a031909060501030f020a0b0f041a070501 77
    0x8540480b84440d4a08900031450810314600003912181c501000905058002c03020819075039803500b2031038070809150f04072a01e134541000c4014204403032400c00c1010402c0700680084aa01c04248001034803851180a13240030700e490140700c000c041c003c2c0241c41250341d40c643c200307070710282201f0107024541e0b41c0309402d4024184446499030309032046500f40c0c10100980c5001080c10030314182822644600020004810680c005031001e02c0b620701c0c000d40c040400111100707002d00c2d407a941c400b69002a0b0440d11144034000700680a8484d081008d0940c1d40103021143c420803101005030070b56a40a000450580303011004104208003079840200400d45400188101c1e0b00e0410589004151181c03e0303c6151018820981142c8000750040c0790184100c5405801010681c0060300c895074000740800c03880da0340703007081120001003038030407032252110200000381d100c0040c090380c600b901c551a07c5450a850244206c034490380c00074501c00040c0c007d006800c0072440a00c503d542e000d4419040421098 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 535576654 1250 535575404 535575413
    0x2100807030f0510030314040801180605011505070807030201060b030a0c030506031b0d0602070804090b090906191a030304083f18040e0c0102011104050f15071e 71
    0x450030325198640a280108004c800052031450004407038250504118185440940010a00c00c94001c04031560a01c04806190074029071112455402039400700a1070740c880324011080b40b01d040060001440a01904012032100002000180c1c440e0000243e01c96540004074607542003252801ca05075501d81a400d0343c5d5405001c0d2540c00041200540303407008180b9208224800050700c0c260041c105003001388204401541207440d1542c0101c071580d140c03943c80c01d00c2000b511440b80a9405150f50311b0202c3d004000001e440f41c0209075424207045131560340341a200043c03050b040032001108000f90240b109880500040000c0c1c1240d0003e06003120044c881042103140965420403403007a26058400c0100c0f2200e030b110446107056861035911101d100d1441000f441740761a003036010349009114030054200154010310f00e2403e800034081d07541030031440c0805d80503d00c036080d00305000d505261520b1600381f01c1c0d032206582803030416051080d561034010f00940081c0c4100c1650f80307210107071030030301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 535577904 1250 535576654 535576661
    0x15070c03050d3e03040b0412030e060703080c030a0b09090706030c0206010b04060e0d060e0703050c0f13112205090f1e0c0d0e2407090308090303070210080703 70
    0x111520300502c0103030640300c014080c500028911000c800c10204a00707010b00b6411320482d401403a980d4040c40d2150340701c2801c6818604240d40840c08908010201c1e4140d08000e415541040c0e00754031907420b503a0b914007500419500c02098080c0749030792035861809c2036440381c01c0d060080030700300700800c505800e01074080c017100ca0403585882036600041c0100000c000d50382c1240c00741c0c0d43c145805041031800d040803c00d5030408400042c034240c2080c12000710300e40c7c00110f071400c0724010b10131243d84103190401e1080b02d882c1140e040d81c0061550a18030203610483d00400382d10030481c42d50a1801c00031244c1d6441c00d203014066542c00c2040044104890f2404000503900725104a01f0f42d401418500726001051407034030b03446620860504001902000300300241d450401d0b440c9420702460050390703d500d46801542000d10103044010080418003042640750728440d0300306880e6400c035281036854030070564025001980c0c1c10b2004104240058940b2181000c0748400d545540706c2e50300b440d00001c1c090703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 535579154 1250 535577904 535577927
    0xb030610080a030c0219080a120504060215100f08060f060f0a090b0a09050709081e030306280608090607030e1207061d0a022d15070c03050d 62
    0x9100c9164180300450010510700c80079649400c09003510380e25440441c449100c0c10b83e24076040050300c80c0026810401180400d101032043c41d012451005c140340c10f4640340254000c10006034400c41f00b0341c410b0864111a181c12041c190b48030514250383d0041c1204955290b00802d9154000b881808824844a80e1050700300070121440e0503d05c40b59408640c43c038050f40310f0528459100c807600e400e5500c5800111001c2e080015003481185000d0340054080699403044050070320424054103074110f0782d501504061b1450101030341c6592146020000c4038070080300700514445290101132407a10000b65070b00002c01254450380c0c5107290441d101401c1a100a004030705041c2042001c421136000445c1d41117003079041d088000c4d1070b50f01d1810401e00403d04403482180000c0398004980d821900040d01007400c62003110740701c46150500941c21541e401500c03141100c045c01041080c514038020340b84c40c080301c02c034441c06405c0011545884a50002540c004d480940040c811402d59981c0000300c03000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 535580404 1250 535579154 535579171
    0xb01020f031213290106020708031204080a050d020a090501090b0304210e03060a0506120f060712090f030f0311040303080f130227100b03040609050f07090b0306 71
    0x14807500010040e00070070002c02c101d00f00003030550f150b0208514507036440581003090810780d50b10900d118409200da02c084c041d40b0054410000d0010720394200000300da4081c2132107594004107407255a02c04669803c4101031005210080c00b054020300498070290170382819941d600300059150000141c80355109400c1030714111020410000416441100400075034040302c81c1e0702c0715000e0385200312003014182d10b29603410302070041800341814082d0411030042a0458031a5140700c00c61a4160361800400031380c03800f41d000580060340346405078102c03100721407407480003003107a0406585003503070030f00c44003000c030040760f00356141c4001c440d0305128544102d80c03814041d81c540740c1107440203800c40344020446c1c8a403d9000c1c00040b800220071101080107030380a0030075158485000d9030800821b0821038185541251400020740303101c0e9080c024022103408044d01032540e142d540313450002e41820101a142c40c40340030760f80b0181d240104208401071105000001d42c0162002c1050300f8400003071708011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 535581654 1250 535580404 535580407
    0x504060507052107030b0a09020c011119081909050f0c0604051e0a030f05031b2107020a1503020c0f06220f0203100209090703052a0405130b01020f03 66
    0x11000900c07048040b550900d1843c40c2c411903924100102c028090481c0c200c0c0e00b01500d600c2c002207102c20341e006407018604500080c00081070110590380380f0f000341801001c00d0b411104c503003444240a290f2241d00102d0000042d000380099000f0082a102c01c0c0b1001c40343c80d400366140d04e00741c034818000c49008402c100c7e600c0780740600c1c2400040f8681038849007142040c10310701c8001030702e40c0d4a240504c01035520241c1009886030750b00b460f6880c0c1d00b2141c61684900c0c00003103072540011011691030145001c42d0100c600500c00804a03003003a070425a4203e0300115070039404904240803114608120a480e500580e0b01e03040c81101034201061601c40d91402d82c01a014024000f000081400050811640400f2580514109a5683c0c40c2014000c0e42500812000c68006100c0e0340003011900f02c152a40c20281d00c41c103408504030b6100301c1e08644070180144995940707511000c10724007410702c0c006165040075200d400040921400724100d00055981e0050714500d940c0500107100c00c0700e400c00246 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 535582904 1250 535581654 535581667
    0x130f0c0c060c09081c02031b010501030312050405151315051501021b060c0a0f030302090108181e070e150312131505040306090b01080610060507020f1c0303050406050705 75
    0x40d03960717141e0381060500e4130501001c100300c120300c01c00607506000403000c80d15441d41d14044015009080c20f00082e4005034089040c40c0d9141d0581c02030354003499014004000c00c55190381e02d050246405005140e507000703150050380c0800d0346550b001c0f4200d445e00c000043c060a010042600c24602c80940e42d041d90805007018050b003147c8032141c8000d4000f070710781540d1609006440380c00d241d11000300800d1804101811030030b00d03038141c0c054401c0990a032180e2038280c4a00502c48000040f0b409040c0c40c1781c0c4031a518107143c80540040c0c01040c1104000c60303005680365004910490001c40d0383da0702d410750001080301149001c204031b520303040305452060700c0c094101e8040100b07605d03d401440c2405030000c41c120040c910510440e0300460f0444e07000c02402c1c55500d8142103941081c0b003a10403e21aa00101350f0301629804054112822921401d144c001507500380301c01e91035031074040c0e54020000f00700d04181d0f44040c502004034600ca13940001d090b2034186403000440d10090412420014140b100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 535584154 1250 535582904 535582919
    0x1e230a0e15060f15040602060106092d0b0408010506040c030c080705031e0106080a060608060a0e0417030f070206070c0f301101060b031302130f0c0c060c09 69
    0x100044400710166079481d55070306011506500454850540080c2500640e480b0280700a02500980e0a113509a64045e6a2210119800341c4a400380b10140c0c40c4642c64412040c0c030756103401e0307016803545003280c0c04d20380d8030506014990400d03889400540d440303d0801c60149082c1c82800c0c4062211b050811003c204524000c006000040284040c00000004201e000d4007244070002d00c05020b403da450550b0710341c1c0c070080030b04d1001d680c0c0d1821b030703810810302146460044c00c01d00c1c410301e400707881c494400d45400090380701d02401410503103c41400c7e00e0707502c1c6010301d80e00c01540b081561080d07110190820303a00092034010014542c0080001c030340890800560248520a0001d030800165000b164032100e60185d0300702d88107100c0d0f82410030b012480f0740c420b410000050f85165800000c1143d10b80e00d640c0b255461004850039503a0541039507040006160044030a490242c541100281e6440a00d030341d6022a0792100c4140c0c040790103003801d01e0400985024130420031060380740c07400036945400c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 535585404 1250 535584154 535584163
    0x4050315010e06130e0303040f0302060a0509122127121207021905060a060b04080d03020705030c0105042d0b042303130f05030607050d1e230a0e 64
    0x100d12034416444c6044034440c16401c09224032071407009a0f03969092501d040c2c1c8681014001c102d015005a80003c0c0040000d441424480c03e541005043c00683d00b0701da94450398460700802090680c1d108a1500122554103407520805400c4075540303d00c0840340d60320032400c04070840c241d6254800d484019691142606650709040050301800310b40d11120016420301840c0e03181c401c1481445000d000c207110000441c1801240350300300810074251078910b040c40e00e10850045820540c4501c0c1c1010403548254014501603009070103490605503906100750035940d00b550190307811a480341541d41e458010403032220a21a507103180c8014511559a21188a00c006101a01d40c10303905480b0080e0034a2084408018051074040c2e9541d0741c901400800e0340314540c05a10300721000c502010810f070900050035070107450540c842a091a00c10301a0502516001d031000c1340012100380700e1180483d550040c00410161160115400f8171242401d00101100806103049241000700c2e82c580c0c1f040109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 535586654 1250 535585404 535585411
    0x18030c06080c0c1506090a18020f0105070c06020106082418101415040c02030d02130b0703020a03020d080705070605060f190905100e0708090c0604080304050315010e 73
    0x414800640c0c8041542415000d107507503c05140c0221079a071660903100600040c8980c01c115501d070480d484030a5240200d0740d41c0f814444500c80c0b03001c055405031a01c0c801e5030f1052101450854074205d920b0307a03813107911341c401d03404080582c1d111002030040b58000e01181040b50030740c00c180c1c00c181460501e501c1e48103402a1500500091204032650344410612200312500f58070001400050030720752288003812003c45040c44001d000610141580c503050280340922754581d8001d44c100018421000000c0d407088031010802070340d00900040320700c17160014203c5c2a0294000d002c0240b80c60502078240580b100c0c041007000766010410800581120a8a050f0354101e00d00007110b83c0c0320408103500e20035604070154480701d01c00074500003180060224082d41c80c075510a000a40318500180d18500881c043d18000001410010340e0003403150035120b50058a0404130354510100e000070404990050f0005d0480743c000250500242c107007040b071800680e0948010007650740c500030805103480f4000d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 535587904 1250 535586654 535586657
    0x28020d09090515031b041109030c10020c1c030305090616030906061d040224030c0309011b050c16030503070308040201050d05010806040c05010f170c22050118030c06 73
    0x2e10209000c10824405900c01400144c12940c6a4030021413104110500b8181540310307504102c9107401c512a0070041d24040784000c2c00a2060200705001c121440c48404115800c510a4440c080a280c1e10245180e1480c0b40e00340e03000050701c896003801026910014229070240d48100240118190380002022954000c0d00d0005203e0741e007442c01e1000f030001584140a0003088201d00c80c80d07003624580480c0201c0c0708690a00303c03c50141d149240100710094012445007007400010314140c103c000540d4044581400040c04454007030005c4690031003c0440000a200420105200384042244600030040000000100d0b40b03959105c0703640344650a001002c0000c500040360440e4000d000340c2c0c1e0030a1031504244459030310317480760302d40c0d5810031941138a1050021400050550291017270f4105043c25036641c0391004641c9081742441c0130090020b0b01c1744082005100e885400022a00490342200c0c0c1031861027134601400142030310341d0362020a1244103190403c00000e4604624001121044d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 535589154 1250 535587904 535587911
    0x9180e0705090c041707050a120b060f04180605070e030c0a0902130e0406020d060b0403031709070801090b01030606050a060804060b06090a09020933071728020d0909 73
    0x7000b480c2c0f80300307014503803110084026218440c0704030400418043c2c199501641c0a100581d038404440f4070304c00e000301d40580b054a140c40801e665041c1080c07541400c107009080407500c4d07686408202c80b01580b00106035140b6503900c2c20b00c03000b154021906a01c036201100184064106500000d4845c40301d48142c589aa030700040303100150105c001108000c1c10404000f0020789824101f00029520082d2121003282c900580403c0d80041c280c00c0d1000e494155841c0840c0c40e910005074824100060301c3d00c0a54443d003000001c03034810074041c0346800f034412901c10f4120351651401d403042d80d81035000288600e84440d42888840d43c404021a0f10541161012803d040800c0205209214048046130444280c950100b042c03260b40d00100b0f20010305503200000b41c21480c041c103203407800d07064001b88061344c8501c48040010f2000060b1144d1801045c65114200030030424030142d82c055a902c4e40c41d07070b000032001c0103013491181001082140324009450824446240101014824041d05010650703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 535590404 1250 535589154 535589161
    0x12010f05030c0f18010605030103060509191101030b0a1d06030a031e0e0901030c1409040c0b070204020f0304060c1e080109110c0109030203091002010e06011202120a0309180e070509 80
    0x1220754104800d80d15000c00300259503146c107001002a07100340400d4030b00c0350800d0081050f182c8002a080c03000b2400448581c4185599a2456041106e0300003090401d0f03226041c1aa03a80d071044134402c0149580305002005c0d070f000b0005019040340040000c5c1c46904100d60b00030100b900440d041107022543c000c5801a030381208000d5035003010039211541c1091301c0b10000701c10005402c00740d50680d08040348820034080048104071000d40b04440040191910783c4040042940c2e40c400b8000300c52004101505211f40e5254002d4290001c4600751212034440c00d4422045812805c001118402e0b4550440003da6110015003001c0061040e48030955407050707100320401407003050b55511003a0b034009118080082c24001d41ea900b0020380ca520400c80706030aa81010300510079030014094a41c050844c3d40c0c031700909003402008210302660020080075500910320414080403442c948640c035048440c5040099444100291203000c00506140592205c8040300014101044070700440d6030b0300300c0ba43e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 535591654 1250 535590404 535590409
    0x7030b040e2e0524030c0d12020c030a080403020a0b0f040311150d0e0105010f0e1603180f060f050f04020909120706090b09160e060402130b12010f05030c0f 69
    0x1c180810b008005481c210600109086400d007115040c088a4000301d2095014000c15844150324030704941c0c4101d88954202c00240030b48501002e510090064464481c548004a42004551002202c001500150a008500e400d2008101408800001508200980e8060165031086d8080640b800c81403501c01c94095070742d940840031035920700040c1911400300c42a10009043c10a28002281d400e001c004186a00c1d1460418110b030a0718a0300c0712103440d079000c06082551101c00001c101034a0b0080b0b00c5000719164030444d0081e20400c805011543c482c18098200c0d000801131030b40450900c018008121903070b69141e5005a01158820700c65122464510718124422484118000b40400c1e100e040c4003040d40042100703030241040c10401d60301e401c065619144070100c4c4c0f0711701000d200d00c240f06099401e845941d120601500c01458146d6013880411050581d03403003144032107400900545680d0407810030328010103101792002c01e558100f0000944500c0e00030703156402200d000020031140d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 535592904 1250 535591654 535591723
    0xb0d0207020f0d20010809250f030b090f01060b070803060a051e1e090103120509090103060203090f0a0210050a03180c03050f030306100f110601080607030b040e 71
    0x440000f05442980d0005290514440c001d41d00003d2240d048032070344114a50103032038501d02c550b803c0c0300034002800d40d00c2400b59100d00c441c08000b80b08030078408042140480f1060110181d8040c0c0700c505814901011094a020480369401880e641014410403540c1d00c0c0e001542c2185502c1540203460740c2e60007003c61029400c90b4840751340a100000c101c01c511300c0224009201000c2540c42d02d810042052594000445462400c0d800041200041001c100b180e030081482c84210710340640381103008400a02110b4080c0c04c15544030f94008180002c046c020044d0340300c4c07808a20017038020359450f03400041003c00603014100038001c2c000307995010039200358080c0c0525039903080c0000480906040150070340203035000c1124984034241024032128000016a489004010040302780d40b00610801c44100180750038107400d001d4101c01c0e0440103c005e000160103000540001d08540c50a810024251602c601c081030051f45880e41c08914800007041d640249a48010101b02c004201600d01c11903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 535594154 1250 535592904 535592929
    0x6030903090406091b0801033201051006030506092412070803040f0501090e010902090111010c02010902010f09061d0307031e15020a0c060c09080d05070c0f0b0d020702 74
    0x2482d04801154904e92a803010544035015500403490001c428002d5030a59003c1c000500560350b002000804141400002d02c1c3c10208a215500310106014400d17080d80c0040c1c1d14500c1c15405903000703000803640b61041642c4600104c1c1c8000903401e1080880e00c82d101c1c201904d0725040500100030b24103032101c105514407100135504441c80582c0d525101d64498000b4000e80311454800e0000142070f61141c0b45ca40c0c00d4848403607407820709074a0101894002c0d8001c00e00e171418004202d80700c80038200284154162450720fa000820b0309001c91000401d130715406a4010107201c0c10300028004564494040083c0d0309510300707011031000c00706002078580759050f44000c02c10b13101c4404545140c8402c01003452000d10a1511440c50b00c13811100c2c2d0b044c1d0140c0303514180025900300d86a0007040054001582400103420305003000e0303807180516810408003079900300c0800c42c0040c14a0420400c6011200201108124022820301f807c1010351940311b2441084050b0b50080350039029503a0f180f040d980e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 535595404 1250 535594154 535594159
    0x12020c0303070609120905220f020c100507080907030221012d0603080f0313050303070905030c120a0b07050f03070e0f041407120216031701080a0305090603090309 72
    0xc40c1c0d5494504a001340c14408030071035400c1c05000c4c1407130000d80603001441c292540180020080010214050b07060310a403802072015a17100c80b5070b085c1140040c4018031004155070041c0c0004001104150240ca401a050004100b54902001001880425804240d82d07044681c03001e0324030118002e02059600824440407946402010103d0050402c03581200c00e6501440a252001c102d00100c121240ba00c00984410010070001c1c5020000c0001076500040041810b160300301e140d01c4151450f04101c131080045881d01e03909000c0340c81e0030010880301080898103070392000c414003110f9440c3d10040000520a012000104a00754041c80540d5601d0b480900c04540303e1038828001440340c22021007080c0200c0c10302c404103182c0d090601802d03488050080c0490300b139031240d00c0101c900d100ca1181c14080c05a00303022400d21540c005103100282c82c02940c43c11030f2040c00801005110750b0690255025500c000851800039410005650003800d040f06c4140d103d42c3c403011315a096110359843e096 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 535596654 1250 535595404 535595407
    0x3150b010c05160302010207080708070303030e0a050d0908120423030f0f0c120a05060106080703150b07030801080601030b040609020402041d04060e07081c02030909041a160c12020c0303 82
    0x11081c2c051020f2a011079000f64210341407290303a02c00150315070006000354a4150412f0505101090007500904855650b0300b048a9042c607181d2030799410141903042d0f0380f0010307a002c801006401003c20034401c003000c021294919041c500300b5040c03045507220481000e03003190750300ca402c80341e0b40a10124051941940503100ca1140352a070880d140c41d500c11034180b242c0725040ca070b4002d584001030408410b65000000f000c00e030342801000da80c00c1400414401c101a21000d500f10508192440c40004186550303405845022901d40030380821416040384204d070b070100c401007000c01e0310841040c1e001030b0070020020b0416142e0021070041d00c07071a0400d440c081144071640c043d41d03080d0300405100380d000741d1080108210780c100c1942c80c0d001034441c585a9034001020004a10800b075a62000d07107807140105e0b8030b4801260f01040d19180100c40c01e40c0c8480c01081c0321a04450800e908a921280060404000700c81042001d041314020610151a1920008260280600810040102c00e00040449 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 535597904 1250 535596654 535596673
    0x90e01020f04090605041d0c0d050c060d02040e0c0c0607050f071202060a1401052b050f030d0f0c140c071a180301050417030c0f18040b010903150b010c05 68
    0x2140130300031070310039140a18034012400069440340c00003010040da141c400b0300045401142084005030341c18070250742500070300545800d04c1d40e0300f400614030f014410718003584aa141c2002e07100442c400510b4250802c000308641c0044a201040c003584c00626400c0c100e8a80c1aa940d0064a5020342e01c00209001007600314200d04540000c0c00503c03034406020280714040c0407001c5045c45090030b118068202c100359425001c540402400145281c5200c0ca50b50103080c06034540f00e14000480905802d9600005101041d00901d4003440800b120003460500400160503401008079080007136680703000380b01084d5480400418422240141107000c17010740b031100141d0306d180c15a40204d540c00701a41c140b01400e04ca82c14107000c0e642c0304d82c1d04002a4014140000c00c181000c3c1d10080c14805503184c01c020000b001c0344000c0240a0011000110110740310464080c0000c54816030001810f026203480e04000007510b6444041031846401e00c041f0708a030803d40140c9401e180084020036034010f0f0941c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 535599154 1250 535597904 535597919
    0x14040803040f181a010c080702060409140f0c0901120e070602011a03061003020906060d050c0702010908012a021603061506051204121103030a0f0e0d09090e01020f04 73
    0x1240b090300c1040050140080110760403c045810f646425650754158100e14121076005111300d00403e4003031b030070003071400d1000c0e80018180d5010b40c000c0000c2c0303039603400c00c1c49040245149039544400c0c1100c482c002402c0a102c900140d0103203088950400c1030b520000b1178070301800d0b000403055108400880e22800e4803202d0181c041c01c0400c10300c0c030140b0800c110014a41c079001803490b0080201c00c1c01c0074905811b51b000c0c080320b84d07801000540c0120080200e10055035541c856984903031949142e05803180c00034400100110425440750b002c0b0b0381440c2104c0300781342050018281220070202208400c90102d40d00364100142c69030312001c0c482010b44000144015a0418008880d2003025a50403680301c1d1820340342d074022500300708100c0c0d201c0e2000400040c170900c1120f04000e00c2c0d0801c03100d1100c0350b9a4a6185a2044803c00311a948603003651100f048180241081c91178030360040c0528034414a0010301d030030071340e207d00c5c0c01e45d030f491710368210046034207504540040e80301c138020541d9503464807071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 535600404 1250 535599154 535599179
    0x106030e0a08030a23180c030c01080a15170303010503100c1719110915070f060207051f0f0c0e100810050405010b19050406120b010e030f1b0a0303020d1404080304 72
    0x300c20032074001c0ba02e0301f503480d143c0071404501041050711003e4907030312010040c41c0149400e5800e2410b03000c01100108081080c0900ca82c6074809001c0119503c0d1704100905007031040301c5448c00e00342170800c401c2c3c60140e5081281c40300b0805100d07610340d660b9964544101840500d08440f00403d601d440100d19140441000420005a0030f5807a490b0513080401044018030603984080c101800308c5108000042d6950000c11045010300c003102c3c100c1c1c1c281a404a00d09004540000280d40c6c0d40501301c3c04900e00340555041c0081a0400c090349010403408510509580d00d406410001101d0019804030310b52188039000d0074001c0d0042007150b13110f80710f542e4158130a038408004a4580032107200000c1c031410803030f8280c91440c2e0b9131000640303600030b070840507000703142d2042e0511002c444a044a61401c0040214102c0c224000f00b4a4030611094041048060035106000b145994004c0c40803c0d000260b0440c0c40310585000c06000340c00200ba0340c001c3c00349400914070b50100041c001416408080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 535601654 1250 535600404 535600441
    0xb04090212210a141605191b060905060903070819170405030d030905011404032703020603040b130507030303020a030c1e080910050a02030106030e0a08030a23 70
    0xb0b0009850442c04032010105001c0e0b401d0010004002d8150200c2e001c01160103085c0c00c0340d00240ca105034084a6035010705044101c0111124218010380c00e00600640b00000f0405100044013207800e076042550040c2030040f14003880c0d0140c0000110f01405031000c101c1d16006104a2041d5414010700b6003143e10a4a0804810b07581198104400ac2d40310030344070f04403400c840c1c00070010981e50f0b113144403d901405280d40169000d540e180e24030404d0003406001c80788a80e101f40d943c481d064420110b150f00350b110306000c80c4000c139079038a018401620354000701d82c0c2203504031207005003540d60180c540c86060403840c0007c1550042c03c00010415415401130a0780b0030841e1010f029290000303c041f200000ea8101340409000078203849100c807802442d0f5507400c410040240d80030300700380180c43e0050b52000c1c1c80380880d459000004002d22941031150030f118403c1c40018041d100340c5506d907003038a400050010b50b00250b0f100d40380c01c052aa0790901018486410341800345030f140400e080030300000c004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 535602904 1250 535601654 535601683
    0x1706040518190614090c091806070906020d050c1209030a20180910150f081c03060b030f27010b1503010503150c0c0a0c14150301090b04090212 63
    0x40e40320400b50440c0384c2c4a4841c281460041c03a085000504001081c00c011306645150410000c0c3c8a0f6031a6080c4015440b03400551100b131201450280024508440d0705031000030442e041c00b03455404040880c81c4c441350310319403808540712a015000281030980d02100107111581840c43c4d16481403105c480d81c1056a4100d400080f241d41c4001951091f13002140d5a01c0385401c402d850030350142c010f40c0012072030b8403940c02c0800219100d044100c800140380e08440001d61181c0144501042d8580e1071189540c801e103401d022175441d143c0a00d0303c50201600c0f190041002c90002864100c8482c010160390800c3d11094030150400e60030785008101070380049004c0c10216518100c3d0904030011281210340c05001410808250108154148000b80001c034001004000c8450460802c018007003605c0d00a01540f8400340c54104d0000040c080b0394aa1801100612400703800000c03548185c030b04485a441000c201038101c480010000d00794400d0080d4850a1510f0b100e40143d0001001220416a0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 535604154 1250 535602904 535602911
    0x30c031c0e1c0206130e070e04060801022a121303020306180d030e0106030506010308130905070507060203060423160c0506011214030c0c0f0117060405181906 70
    0x1d840c2800401d03020340401002d80c14408034118010708107000202900c0c140550f02c1e028064540d42d054511341d20544040e0005084100754a54038507042c49003038001c1004030002c40c5001c1180140044000c0540c40b01c04081c9070b0484070102c0c0b0501800203088c100d4640d990036540351000030050000d1102ea0000781c4c081d2082400080032402d091a01c40002020305004011003040c1620842c0038180c00030151541c3c0d500e9150000c005001001054003851141d503440341c0711013100c450420707545950390001107400c6c00c01e02030049141e001400c85442d13503004400584e4aa9440340030030013034110080d520f00d20715004101300c0c00018a00d211580a0031081c88109154108800b040350b20340f40c0664060115003104004004c11503003014043c110a2040102540c04620f004407242160007180d1081ca041c1c02516010020b460000b50221008009081c01c40c1e0703000c115942e41286410040c15207004642d1a0041989020032124285094200c20211f80c109036402c2d2149103460850003044424a09 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 535605404 1250 535604154 535604177
    0x6061c03110102042423091210090506130b0105010c0336060306140f1c0309060f0825030209100e0f0603040f03080402010e0d03030b010207050301020f0f09030c031c 73
    0x101d1ba00c038200d00d0101c580c06084000300114a201d041e803001c200c2e10f901c0800000040450306092100300ea440c5031000300000c043c07915090180c20514010502e5902c4202100c0701c1d000941032145c030341d0548000380f81c5030010000500d0181e60a50845502c0f045c802000a541c0304607541008605ca240a00b80c0000c00304255a01d030705034195241c43c01904903203041111f514a960134446103c50804030000c0c440d02003450740b1001401c00400754035080d0001107000c0341c00c1c02115088a01410081a07a00e050b0a1619060b405111041ca0b803000405980d04040074403480c240c0309805440340717510004c00749208030030516006400700310b031a22403e000b036401246c4001e4a1a00c070702540c3c0304030381242c0c480180bc2c44a5030101c45203000100b04034103004403410354104946801810084503407103918006994074541c0006407501c03205a120500c40d070300400010b998400c0c07860544012251a034045600d64040c08002800e001c2000e03031450b014072810744084280c0182e480c0e00a8540d1860b100d0794100b64 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 535606654 1250 535605404 535605407
    0x9130201030621021512071e020703080909040507030c08150f0403021903021005040602032a18010c150c110705010203042310030c030e06061c031101020424 69
    0x2940f4074000d6a0030469058000241c103010811606010810b4040d600e0801c1403c52038000100c00c6d03a02c0740c00034070b40310680420f0113400d55140c000e410171380c0002c0c240d0300d1031070740c03010300038420144840d02942d100d2011404100f810001d120141d0b5004125540c015118000d0702d82d03030101001c0b80c4817145500e0003c250703c2130b000c40c6c841d400307039070141c0c050035a41ca14020064040c05410b0f004030214410038441d0440300c10300b446910700491081038056502d0401d8009040500c1009007021804102ca00e4981e004802680817912541d000e0215583c003550300c00b0040e40c001c0342441b00602181013400300311210440b9603005114480c6c003a00c0310102d071012200b000c0c0d545c0c52113010305409039108010a003c072101e0a080000200e4001210040c41c0c1d4100003c9210315002034080400709403503c2500300c15030b80501030250036180e00c0e002050180b03051000034445103035a60800c16180c4c1caa0b0030350307400c0c14420004040401c440100035917599a0300e503c22010300450746541c8070040d00102c2d480f00050f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 535607904 1250 535606654 535606679
    0x80c0a080309102a021e0c10030c0e040e0703060f0504050f0a0b011a160b04020102060601030908040e1b131404020403050607030c050d11041a0703170403030902091302010306 77
    0x882800704003080d8003008076540d90301e0184844151040d88508110211254840b003851b1507a00c00786006041c484c1c0c00e010501c88810701d07000c216024942450140403611780e01034041c42c2484012100402c1c03100e0400203c5080076255003010305090b003005400003001d0704581016005920407030441e03100707a000c01c80315901d03061701010081188104400401c038020314240f13400c0c000a0b02806007441c0c10400e5114105403c1403140880f447c450b65800c1005540c1c042c848a81e01840a09040c002008545c1d03800e11144514040c41825111100109a100d405030f4001000c1d507110a003040c0d5100595042139020080c20301c5040c5085030180880d86490415000341c80c1180da1180003082c0ea510b6a6000381d024000c00c0d0341c18010800148020750801115009004900d00020728650340d5909001c801d00504c4881251100568410403030300c00001c0d4420214001e0303054248582030747c3c0e1164a0120040d11380f20070080d601440260911018140003142c0c0c881c1603100340ca040041e10359500070410070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 535609154 1250 535607904 535607921
    0x212070903021003200313150c0212030a060b070c0906140a030b1b0301170111070201021c050408030409020a0e0d03140c030c0303070302300c07080c0a08030910 71
    0x6000006a078903031138000d82040f4140780c8400c110000f00040d0207031049607a042203a0b50301440c01c134003501c0400d00050758109081340745005028482d203460880080d5952040315003c4255800010004045410940c0880050b06c0c0503030401d580c42d815800d0950000c0414001d002a807450403000040803c21020034000803000684400041841c640300d018183c4001824000100d10410740000411207a0780114042d02000310030101301d508000245007120703a07040f00160718400c100402c0e000360307800003060341c1805450540002902034114080f1603900070b40e07000c014940300210340032407890140d4006c0c3c4130400c6517546241c5030f0305004003041000c45040a015000c181c00f107003d255480f041c81300401045420380116850096a20981032441d0320490f05680020350100710580c0c960305000728030703960f540c00c0804410340f045103181c80c641840000d4020030800000207404810000c001e400e8808011482040d0755600c003543c04c00003480c2d4030854606031913018159081c000c403001031140b06413 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 535610404 1250 535609154 535609159
    0x70e0114090c0705010b040504120f0c0c140a090c030504110f150d1104031a0c03010b12040614090a0b010b121302030309030601120302100b01050702100e0310021207090302 76
    0x201e92103001c05105164480001501c8a548400c0041160b4859014440c003032885400200620440e104004140364604901041081004c0c599080444c004203030500554403e0345e81c281d40d1414500004a40f4081d83c1d00180400d8203104090344859007540c0710601c91409001814140c8203000304110b402c44043c0b50301d40e4054001400b15543c5031030140586248511120000b801e40358205411156400c250310468010380d1280d4042d20107140800a142c0051455070018290750401c2a4007002e0300910940c03100142960000a080c000150815100314071a40307024034280c140490004e4450a51641c192200080e0100000e40c2c655003008860400c45140c800f018151514401e40582c4410090166410720090040c03031001e0350280300c2c01d402000f11180703809403025035142c00788c108201d11407190515881c2c410341c2078403660010111400c1f030b503040341d04041040120f502660f00d151640c1505405109006100c0b200340c000e039000b04a000c0b1800c0c511481c50344e0700101180e1200d43cbd404002d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 535611510 1106 535610404 535610419
    0x1d150409061e021603030506010e0915090c09010c02040f020f030709080115060e01271202180c1c0b0303310b0a0c030909050108070e0114 61
    0x700000103802d0194200301d5408414582daa00074000582810384600000e1840ea106800840040c60000d102c0c40041c204030018035800c155001140b4041d141000100e40200c90110698030b281030143d4406c2d10b2101c480d0300f03010150200e120700d08100c940038001c001d02d03440a0b50103140b0030179603941e4050b015844c11010300e0a4440356030b00c1105681f0101c0d014000150310a0710003007207050030300749003800702e407001d401400c0d050480d920401c842c405268042020b48001e9002c480c07081c0202d40016807110140980d031007a9070159011741d018001048401828500c5080c001d8540310510400940e0744501c10200381545e000c40401c018042c5220030307645007204100304602c103040102500c00c00042c10542e200c00d90b44101d41105040c010800018400c0612030031401001d0100a1014030540d40d6030500140e40e1003490080a0b1080e03490800030442040d40c038000c0d11750301001031007003 = true := by decide +kernel

theorem cover : BRFrame.Cov 535431654 535611510 := by
  have h0 := BRFrame.cov_init 535431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 535431654 ≤ n) (h2 : n < 535611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
