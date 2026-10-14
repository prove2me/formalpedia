-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0414
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:41:39.663996+00:00
-- url     : https://prove2.me/submissions/27c9fa2a-784d-45df-bb01-c2b602b6a54f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 74280577 ≤ n < 74460433 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 74281827 1250 74280577 74280581
    0x1605010c110606040203060607020a1502010f061203031a12011a0105130905060310230105010905031518030c03030a0b0d0210080a09060c0f08090f0d0807140a03020d 73
    0x3140151821210710000951069103500020704820300c515000004604a56540e03020303214140d80041c0f030840b5140d51982201f061f40c07a24403601c40554245105074180f51207511500d411070341d003500340410348a21943c088000302080750346503080e4100421304011a07100c0d01d0403182d4a40c200e000028000011060301c2551080340302c03c180c10804200b00c1e40310000e940d940c140c41203540607917000c101d030b848000001e0300f01030052012908141c50400da40b880030460728440c11203071500d120300c8803007030740c8407401107540c2c4c1d00d28080c258150f48280304070010f80c02011b03141b541c4080c0c614040c0712604800c5c0c401d0b42c156400030100729081d13031005c801e01c15049403c1c880d42c865400f003100d8852248410394081080c5188010000e018400d09800081c0c48440503004a0740d0203501000401120080c088003410344070710710244000184d01c1c880000c823541000107001c5030301d00c040b500410f043c0600c00303000c42c2d40581c01800c00d401c1010300c0c17190048030b40c40307540500040301c0740e074801584aa00803030110301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 74283077 1250 74281827 74281841
    0x60903040302120105090705010c110910030b061f0e0f03060115080702010e120c10140709120503090d05100f05010509152218060c1701240311160501 66
    0x5507174034044c14131078494030016044040741c1c0d0070f083c203005040d55410110107a50781c2e051079603040340c1c002042150483c0d1084450054a114020412507903c502d014490f460000c0700204168070001c03e6038103200d5004021608441c900101010b40f5841030b440881d0500d0400e80c08103035000900e08a403031401e604245442c1e4003221500c002c0000d0b2085091459540b150f680301d105d2108000034918012a109005119018588201c140014090b09035543c0c00ca11088842e18005241c804010400c0301c2089118004e04d5001001103081c103d45a04000d802800400e0445040c450022280302c0340440c6e0140351601c40d061400000c0c550302d01410700c241c03000001c1c0f508408180c02c1e08101d0311030755940f45129003414002800000007200143c208000c045440c14480d10180c95180384041107c90b400501908c4119928403400401c800340b5021340744800c3c0909c403041015140712400848441400101200d4145004607486104068803503081e8130010030043c1030103c80f800603003800005d0003800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 74284327 1250 74283077 74283109
    0x60c1006031a07170c13050301090f020a090c1e090e0406050105010306120302061803041a030603010b09041a040201020102070f05011505060a090b0d020c0609070914011d18060903040302 82
    0x1c003522100d4401d00c008260017085103448281c04543d0354191151b0340300b051301a00028008025041c80d9017081140340c4020728040788a1280c0c100e0203d440d946c40e009117001001c103610382c00d03110012002c00e0038804c01035501c2e140401c8800c1c0000a00c000f1844400342c01180a0100010070794140700004054501c43c2e040580c4000c0c120b402000003030b41c0000c10700e81c40031494284004a60004803101d05610460303101d10004e8003e02142402c01e85003500a45c0a800704034000c1006800480a1142400c0212005050361040054407a01c0c1140203880a512a1052000500d0710501d40d07104150810341d00000c2e50303147c0d999040b10b402c0080c00b5107460040d0804848482c103240100300010100303200b600800c602100c0c007040c2d40c144229990182c0781c4c4001403c0595060349086164650743d120248198800b050a107a0300d81c100b2061603902d01d06844019056048800e02e104e40a45141c01c054508011748a05100d134020060091211601840811024581e5549540104204988030034490 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 74285577 1250 74284327 74284337
    0xc0501060914150d1209060305060a0b090d0309030f08070506070206090c0d0807020d030512180703121b03030507020c0a080a0308060102150c04090609020705060105060c1006031a07 80
    0x1092003007555071041c0c3e1142c0302110310f0b150800464013240b160441c1d510014103101350b8032010f4401507004440a015a1500c1da42001290703141001c01900c0e00107407003034000040003001030b4412401e0100389000c0d024001e0070060304169a91303031403003815240c006099a14120104521040150034072002e50840c0040c80100840c0c10503c0c8559100c14050ba0500c1c8104010080c40003003041107421b6070b05183e0020b00c2410356215600380941103901c85000603004840590018148250100c07101c6221b42d00d00c07008104550540d40c2d01e40c80499000c44003014004500c006100b003c0d00011002a502d10035074000c0f60900708400007a01c0c01c4103507440c180c17084112100901400c0400115900c0e510f82600c0e00c00401d03201c8100617410043c218011180ba001c410040210f00c60307109005004403030154408010207a550040b0707404900074403c0040464000000400092401070050017800d01d841c07041c0c500d190000120181191115801100c02284030040480e040c080f400c0916070100f000c0c103003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 74286827 1250 74285577 74285591
    0x105040902090610020c030f010603020a060809030d0c0311070f03020c010525030e0a0905060a051f080c0d060303030504150902010f081e0c030406060b1620030703030c05010609 78
    0x80d0003220000c09084c0582814041841e1583c401c01000e0078104000d000c7d00c040e03030358812501d40601220300040e40960303401d100c0000d4062040b182c1c58414400300014604010800c041c8001800c10701134027004054079922000c0072400c111008210040c8201d410f00c44a4096140190404240f9a500390520800740282d002c06030101d20501800d410306000300c800301c1503500e0300b602c034944103440142e0485011240482c00500300c1d808035020b010121081001e180c1d503a010410280d424481c1c00500c1c1580302d14a5403058090348020b50840f4201c81000e0419403210018000c40f42240d1041d030001340c560090206001403d44d0181c0f04007100002440f421210b40c0010700460300304c0720b06508011882c2c1c002038418801c0100c804204044a52500c02400c08502002840c0c10503241034903070a282038400144210303540103c9035200004000d44005d400d031601c82e410342080c5c4807282c144d003000c1260b02440c10740c0c084c06240007540c882d4882d4090707440c6c0c5051543c01c441c0076410010447d890199 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 74288077 1250 74286827 74286829
    0x10c0503070203040306180605010806010e0a0908090f21030d0501080712120507020a090c11010501050906011101023109020301050105071104020705070b0919030807060c140d02120105040902 84
    0x100e8055980084000c240004d410002c04e003801c61f0014090007a40c134080000c10300f1800810000e040341c0710f1a18000d007545840d8052000c88044520050404004000b81c035900d0528140181c40c0c0c400c001c003001000c81e410510036406c0801900359608036000000c0061401640e0300c02c060140007064000c0410506044111140603100c80307028103181004102e080c007061007034007121502c903400340014402555400c24039000d07003e41c42c1920081094442a03000b071060503ca08c40c12540010000d07a2252134034001515050450602240595000c01400c10480040500202001510307100050310308842c070748114054016802c0440105d004100420039680c0c4101135440c0190044180400d2045d41000240244501e1200502d1800340141c00103000d490f40003d044000b40680d00c8a0b2004a07024400e42500114000104494420301c0b0301c6000c111036a2080e401c10100d41414019516aa58404040c0d0009410394580340d80000c2c52403e1580f445407000d004007010348043c098070394030b54 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 74289327 1250 74288077 74288083
    0x50601020106270209030a0812070806040207111c02040207050609060106020718021804181403070804030605040507050d0503030a1a1311160b040c050d050a0f02180711010c05030702 80
    0xb4601d41d403c2c0e4000c41d902c00659400c0c02000a22540b1003000f541d640d22540d0405401a022603011000c5085880000d4503404d00b0700850ba589039218903178910045e10001008a40400e01880c40c000201000800380140c541d840140b4646005800a0000303242048445107801e10503080501103402100c8104060000301c242d0512032540000302503110101483d844003012028a50594018180040c103030b100c00900000e41011801005252000e040d00200c03590390b44640100202403c00420040001c281164450341d040b6110f502a00c2d8070a54032400990055240b41040d1083c1c0c000000b4420014201d1041f150030304580c54800103c06d600c1c400051040d10000506ea040316100e0100c03621210200085075000094071880446421203414945c41d00a0200d0b000c0714082e41d043c401040e40c3c600703580e0560701c0c03d91200050501d8011981d40b2650a07450032022a0824100e8034208020001c001c5210320400d11540c03154040204100c0340703800d44800b01031182c00d00c03400300180b201007a808 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 74290577 1250 74289327 74289389
    0x1111201180b032a061b06061207120602070203030c030d0c08060d0312060801020a09051905030601120c0e01030b090606090921090a0303050a021506010e090702011806050601020106 80
    0x4c00c0d03192080d280c9000c66030144603800c81486a11075000211410262940d44640001d03011000441d040355441c00c051115003a80c001d540c0c4840e6008000c00c01c4000b0148030005400780c03098202504140c0705a02007461604000700224442d00045030324103165402e4411818032408a107000e071030905040c80816001e05074218003804100300c3e03030200d109a038038a4011170000c2610700c00071540c4003880c80e001400001c99001d030342d10440d07074074035206100309000b14410207840f001406403030b2a0740303020004103c841c10000c0464a4507640c0c0d20004882460030205c500031401909800103601d400c100d200d0500744000c0c01140304100c60b40c140090b007540041c100d01c5110a4022030400c110174486a11094040c1030b917020b601c2200b12001000b0184e000018110320006a0210380c034402d08584801d51011017219a10700040043c1e513007100e2403400c042e00540084490000242d41b47c68407a002c11603100c4520306944440e181c50a00200e540d0900c1204000c01a240c4881c07142076101c007042101d0701c0c607 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 74291827 1250 74290577 74290603
    0xc0d0c021c02010c1a1603090c0509060a1a09130c080103230a051c021b10050906030a0933050901060b04080604031206030203030706090501111201180b03 68
    0x75401c140d0469020380081900c8582012020a50424458052402c0300003140c0b0400580840c42610303c43c9406070041c815599400010f00c440c150404090150080c070040005504c86070400b400203d6403504400d4910508086007140d54911610b405d00400440d003013101c4aa0519100c50000443e60113285681540e500c040d86d101d0054520805080151661590601d40c0c0100c84020042120014001e641501522406c802402050304240e80740d03200f40780070031901842e46054910030b1030008941c414083c045d0502078100400701c408120142c20481d08800700c659610046014026003180c0e5000c441c125440c5541505256120010001c00d44240c071000691554007040c040c00085d00907030080c1c00c40d00c080e561611740d1140e450340c2e02d40c0107886c03d6001c03600034403030408014070384e02407002034030380240040d0314242e15540c40c0d0000708002501900e082d540d6210f5040408508401000034451001001e080c41d4104140f141c4040b030403140c2c404001d8600882501e1903140403c689411a036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 74293077 1250 74291827 74291869
    0x4030201120c12020d02031e06030703170d020307030b040f02031b09061b0a0c050405010b0f130905010b1b03030f0c031b16120f0915030617030c0d0c02 67
    0x90b203010140c6040300c0240312454001d00202e0301980908841c0e01546c85021402030049480001712510788148401765059501500080000d20206502091000407106070310100391234102043e00c01c00480e0401c0d0703110000aa102c21206003149040e002c2c40010340035401c41145181003c401c4410760210a606023a01d201d40464084c030640d807144199103c40c4c208100e000401c0c1d07805003100ba105d9aa6400882d0070380c4a041e030114050501b4829681a103c08178201c5203408800e0b0302007030903500300c005101408803240d0404074801c8024050b041c005c06418071066110103045e05007820a240000c00120f0310fa00500030040d440903aa00d4294126001d0104641d89032900308009000240050f01c40300c010f00000792640c04864010071039450140600c10074140156410011201041103481c90000900c08210902c10040b0078400302e060304005081c00280c0f180e860003602d069500c0034414688981010400c104000810b00c1b50030b180d8907551910003c6400964001403c4050106042644038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 74294327 1250 74293077 74293091
    0xc05241305070812120108060105060f0f130602060a0f1a010e060408060708010f0506091005030a090c0b0d06050307080a0807060b1305010302010e042915070c0602060105060403020112 81
    0x50a010b6603000c0d0403038005664003004090003e281561000e03215100c110b03921800020b01070781c046001d9058540040c80a440c00d601c2007080030864000c0b002c8000004000c0080b0606a0b04a40041d0020700b005c1c0c0244c84107203440c21450041324040c40c0d5001304941460610781d03080364078a4584a0b058404d09040442c2200c13003005c142c050286070070000c4c9601c52076003481556504289154122481c004205003203644806c14003030f40303000b1900201d4016400030031403100c0500030005140d0103032000360300080300195500c40b2001696a6845004070440004103c4a000c0150150f24090401a00140401e501d04002c0079a203000424001d00030782000700d003020410107a40c00400e80300c480200001440d514030703900007000308000c1c803040340400c2c25803031440110f040a018580e01d10003003800d2004002d824414092a44604605c001c0c2d0000214800405400d0150050124980a00b120018803803c042d80640b6001c81a00400e102c1d00e8248800c10040c0e900c0b10b00f85c3e0240845800c04240c1c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 74295577 1250 74294327 74294333
    0x11090702070b0a0201090c0f080a03210606030b0301180201050a0c300f0f171515030702010e0c0a18060503031602180c030f07021c0c052413 62
    0x16070303142c01c440c840620019071425415815009011103901940c2801981a074414a282c00c440489c41a0b44154000c1085540483e002d01c1210b0f907901ca02c841055800e0601201120403104c06400642c0440e030f42d46450701480c00d00740b05511205c0200c443c0b180c3c03640303050f40002c0c01d1809800f00240c20046118540420031035034059512000c0200040440308145900d8452800f62030420400c002807a921401c03103501c1d00c40c3c2c0c0344100e51806a01c4400c5c0000501c0c40311900600000d0480c034200d0045c51444101c1d44407405440c3d0501c1c2109412603d90801800c000d0944858506540c2168840310000d2040da444982500444a02000d0021004544040400904a0365020311307850b00000c030350040040456001486001c1c400c885101e880071800045c0d2411043c25034a00307100d0170061001070f0203645540d0800b900564140100c034004c1e8000500c205080c0c65214107000054200762584040000800220521810303c03202d005004000020030341d18204001e09050034025511003010034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 74296827 1250 74295577 74295583
    0x12050403050a03080708070216060c14070306020c070f05100507050118050105011a07080a0e1504090f0e01020307170c090405090303160903050705040902044511090702 74
    0x4650003010394910b1006410040d05040d000c6442d000491104000180d031144049168038000d4149000e144001d41000411500c196070583c00315400e10901d11285c0311008100000c000a40c40380e0700150350743c0e485400c800e06001e40341d40108190f958051f0180119660981c61481e060301038a009516200b6074101075014058603405404441c0907407000d8070500c40190402c0e4141c078480201805020085891044248580318020708000c405000840718144141081c2608400040c26064610242c018050003644070380d105541680d910581c114020b07a00b8042e4402134a00000218154684100b0181220200244842400145200090584403e8070a4810256000d4010000c5d40346c0941c0b0141d8035403003a691565038180815030707160128820148442a20392000107007000314540018400030341411541240e01540715007901d40c01803030a250200c1890700503c0315000008080e0900c0c0302455802e00645035403022440d1680c00b092040f0141c0100940507204941381d546c031840100d003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 74298077 1250 74296827 74296829
    0x6030a09060c0e01030b030a03050316020c060409020409060605030103030c020d14010f061a041d0601031b0804021005040819080f130314010c120902010903080a090f050405060904120504 82
    0x901c61800c95400750b0140d02c200804640c6000307032420880c0c282848100b65580030780e000f0050020f10100002503444445501e10aa8071400d40121810440854000756568100b600041c5605902103010080031006004407001400c2d641040b40c51541161402044025002c2001e80101701c9003c105c0d0070000a01c100c6e02010311010004c10600043d526600d0140200e40704250341c410200440000702101e100c2101e080f5070385221580800007a003055000c0e50080107204505056403888110043c240c0340c034211400440c00d6a440102d8601481040002585040718104001d03042c0014464a000080d0312100700c0314111070403603100f556160042d4148254080c0c00c145010102e0b40018000300d90a07800c0549102e8000c0c80201d94104a4803400c8402c80302c0104000703916003001840100407540440a03190040c074242148035184c1d103030307180f00394004c035500400500e1405041121800b0003180401502c0103c41c28090381c2051000540d000101400241800300b071030b51009016409030301164 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 74299327 1250 74298077 74298083
    0x504150507150c17010801060602060f1308030f190501080d050c190609050d08130b07020c090709050a12050607081306050a0209040b0105030907150302070503030907050f06130506030a09 82
    0x100540500341e600a201c4d80f5503042400c004c02c03c000c00424a50410f00030081a20f031154020b00d010b581d4503034a00702c1008042c1014030b80700210155000421440b80003584034003040114034007181080205103c038420700c408414409031400700180407119020441c0c021601082c60701544904d6110f05190401141808008990002202072000c001080e0081ca407840d01030000d5501e8502007001c1550000c4003111007410a100503960b850000b0040540c5a0700042d581c0304840e21008104080b540c00f80094405c1004209042c10070061403504011720400381c11141c8411004954031b076215940c6401c040c3c140c5052107004000a0b00000e0741d02440d09115800520a01c103608103010340b00000e600900740d4030b01950030059034000550041d022170740201100750080c40310a2600d10202c003c000404103a10405400300030180200310104080c50054070510003911113a45010104016900240d03100b40c000c0d002401115007100d9038541c1081220000c2e11465601d941d415070300f85c010312280c6001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 74300577 1250 74299327 74299331
    0x801080f070317090619030605060715091a07090f14030a080f1603030509160e06040b030c040f0614041b051612030c080a050112030311040503010e030307020d050415050715 76
    0x441c164400000a80700c0080147c2c40402c038403a187c000380200383c031039050042d007403418100011201002640c05030300640e016085a02280072408030460101005654000016401000501401900300140001008410302c40851240303004003003034542c015810f024101c1d08020a2049944e0b04150807203101c014401c0018002c3c207240e15003e07004081c2658058041e1080d00d000030f245d082d01d034420b002034440d01e1803480900e60b00d031000c11000d020103a841d1501170280340b60740ba00a45640c0105256000c0501011075100d084c454814441c0b6001510709208506151681100c01e4401c100c045040e10310b46062640e030440220799451240200d0700040446100b50662002942e0692005006190f030f60380da1030040d1500c2e07070380034181c40c02802040322103101954145c00007030081e0300c02c0c42601c00d441101740c1040c1c0d407080000c0c02c4458500484609070000020005c4880d8140b014840780070795824682d06090601090040b10740000803008240302001030080213006045034064402030000c081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 74301827 1250 74300577 74300587
    0x110d02030303010b03100510140a03060905010b0c100203060d021009030b0a02030f070315090b0112060602030301030302101503240e01020a030606050304020d02060906040e160801080f0703170906 86
    0x560341c5103900c211140e140b51040ca14021405260090b03c0d0323914001aa52940c3e5400b01184583e00c107548024a900305060f030311400094150110701400b4024400841c1142d151655002c0c0141045065111400841d1042041107036594800c21080946a0191109036144403174507415612030b64103410192484a0b080b00b00000803040750000d620070034141c01c0140884c1c83e003240580954203140c4070001e91041d543d0003806146059444201d035050145884400070180940442c2140c40c29040280181c000000510605804201c1c50600603100941001558146503111480000e40c0c04000c0811a180c2520400b40c0420341550040c2141000e08025249000c680700d4000c2d401803a0b6800030a040540024140b03018005503071180f80c02a24414040590350b0030442030781c7c014403103164042018000800c0110030202880d208070b1248400514200d0840d0010748001c0c8141c1c00740120b940300986410340403002090610840360300001102050551909056544c09000c41d2107030000030100e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 74303077 1250 74301827 74301839
    0xc16050309010f0e010f03020f070f060c2705090c12090601080c01020a03080a11190c020906040218010c02032a0901060807021e0109080301030f1a13110d0203030301 73
    0x10007828500c800341c0380ca07902c1124071201500e16030251102907004c545c078403190350003c500940082132851100e0584500c0d0500e590703180d44411011520a131441c0d0783d6030801c2010150406819449248505030401070021002d42c143c0202105028060054030408040381e856800c400954030792801c040c03c51242071030484601c9683c0d85091041030b8013882840d543c1f0040d540041922160550103a0b41c18607650b41c1c8400c018050f040d248a4804c406204020b25880301031030714207070012048551382c3d844200095004101418601030041e6101d01c6c8108078204903c444076500c042800d401f801d05013500c9001c2d0001030b041c031072220454600303a188803c045420700c00306c0721036001c2c4820445440c003184e42c880501f1a400c1d8011903102000d684410100c071004034a020340300034400c000700004115044250340f100f195820aa00440da0200103e1140e01003000c540608000d440070307080d50301c1343c919004405040448600001821a40000f5110446622202c0e404070404d50060304036035480d651a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 74304327 1250 74303077 74303083
    0x70902030405030c0106050103020f180f0a030b0f0108010b0117060d05390114030907080712060e0a0c05040e030c010c020a050f060c04051201020d09060c0e010305011d0c1605 77
    0x1444884d89510341800440c143d8001c2c030940d2980200d40c0c000a0600043c4c0c1004504125075684140d4485647c0241166560300c2c0e008c40c20185220b020a040c250a0000348a4203003441038100710000d03410065014030a0742c0c00070b960310303409241c143c88107956113079400480c0c0d01c1030301d01070301815a009040e01c01011689801440305c40c03245042c00c030046040300c2560b18a065801c0c000d620b00185113001c2a070220010b10028640004200d1309840c10302d1fa036007900c0341c0b9040256200710140c0c1042804c8909200d1207100e0f121030810100c024108821860791643d000300e10600509125640d500c400604844080040c1c0d108906200002c0017100c0f100d4a020b90380e0712040c24100d40a100c0d8001c41a88820042000b40c05202000070035810a410002041241c00f4616803280084d9401d0018442c4034816000f000201d0b80500b9001400c80071142c4010044440452254181170030400100503400c114003600200030080e01241401c0e0300d40265083c040c0c80b802c914820f80301012440c84082c01404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 74305577 1250 74304327 74304337
    0xe01110a090b0301050d0f03110f0123070f03181403090f100e04320601110102090d02060c01110a03060e0105010c050d180b0a11010e010b0a120507090203040503 71
    0x1921607404071651002820078a00c000d00549030002440c5c5581000550f00041e43c001d458030034113101000501140d11180340083c42d000550041c1e4451070340440706000c0c40381c91400c0c2200c2c011840024a08180041c2c52700c218000387d401019601d00403500b03002c620365819006540e02c841c07030302100661041c1c002d55076001094403c0c4218490002c1c4107051a000ea841101242d03d9120001180000070810009115145041f002d0300008074400300317103046425213070700e00e6102c569015040c2d062550004000e01079503442843c4980c41009805026901d00185200695046842554401080d00818050180180f03440c5941d103000c50500c0b1090380503000329041d03411200c43d42106a90f0b03240111804210f680c0d000e001a00b000180c0d00d400b80c451a048030044a002c808582c100ba40c03039442c02c4560f030014080d0342c00a82611349581da8500700380602401c03994580300a010803074084c2d00040b41d4000034071402c501c0204000425042000501840b001001c038032328115180e180c20300f0301a032a039010b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 74306827 1250 74305577 74305597
    0xf0a030e090603150a050c130e0406050603010501080a0809041d0604050d02030f0304020609030a120e120f030406110709021b0c0103060e060d0501021605031b0a03050a050d0e0111 79
    0x38250008400c0e0400243c901c0780c540426404c614a61101d440c2c02c0010f000141c2182480c0404100d216148102c0443e48001080b4100340d4024901d41810058204c1c1c0d4090441c0f48a0b90409004200941002481403140354100056560700c0320b05c40c001070014813550000c210383c401d2a01c60131016a04c0411f80512650003001595002c003030b240d404a8a0b813240d4129242d0501091002c500907060a402400f019030700502281d0340b24144d612032031800d4902c00400800036001412903a024280154101c522800000007491290310000c9402d889004a00a0742d080020b60703001000300300c10401c00301c0e00502c040c51085543c1c3c0c00403070580001240c0320b01510303003603c9a40d40300001c5500c00d1241e02c04543c48000c10b036030720b83c64000400c15108422002500c05640a204d840f40400d050405e13902d409100d14021592804070b0408108035003039600100b02150481c0346648082500b08044801c0c0440d1407801d169100310f8605003d000b001000c0381c2d641c01c0d611704642e15180c4c040702d0009049202d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 74308077 1250 74306827 74306839
    0x1a0d05090708100504080d090828030b03010e0303161701060c02040c08371109090c04140108061206070306080f07030f15020f03040503030105040609110304030804050f0a030e 77
    0x280030b01e43c1600741e460a46000b810103130100700e20089021654400c02038544a91800342c680391b00b4240c92190b50849100340840600001c130b03107403032490f003501c10070508020a600a10a06000045854032070000034140c0901c00c50610084465074031511600d4003c4100c0303801030445507101c0500420307090745558101d0145140c0413001c00254054080c8621079910b040100c03d01006804003041146842481d1140c18980348149040c00c1d0103c1c054000901e54441180c2c1c0c40741c21400400c12442400b0f8040c14240f0400c01040c07003500300090412603508828284400d0703e40f0382c038021501c4800302071010750590140e501808045035150f001a4100c074100d000700c0e05139401708204035448040354400200005500d1071100e002407070350f480d82d12031201406d40042c107012000700030401641c000c90341280c0c95000000140982d103028403409003e0203051604002032618044a140280300107030000d010300020038009003c100301004114001e40f40f80051310b007400010300d8054510b600c211000b52180b2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 74309327 1250 74308077 74308093
    0x300303091002090d030c0c0f0806060f040e060c180a030303020d0e0705010e01031508010203040305070b01060c15090f02060d140c160818060a050703020123011a0d05090708 76
    0x1607490b0090fa00d590100601d68418a002c99500f942c1e0520b036494200c602ca4a6504c0c000f800020f04002030000300946405440c40303142032010800341ca5800c8034510711451030202d10f080c55241c0059800d5200c0041d200c141d40da0800c005407880305c2c152009415612124100c030104c10140e240d0058200701e0120070003401180f0240368000e032645040e00039540020480001e9200303e61081d08640229901e80304c451076001d40300c00c8000d00366442210140d000c12800204401002a1160740c00d005010398544402d00b10856030342c1d806100c458042407090680c464105000380b107408007403030240700c4e40104102d03078604c1e075078070003202501042040500d0301518000080000c445642200c50a003080c50780083c100095903903403403090300041c2845403082c5411240c000d050b21510000c0c00c20040d5500c074aa2102071603d002400e41c2c00100102010400c2003c0b0a06070041f5002401d05650040c0c1c0d40401d08102d90705948410702890410100107070508040c071001e41c2d000b04c0c5610988070500141c034151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 74310577 1250 74309327 74309353
    0xc04060806031b0415050a08030301030515010609150e03010507031b36030803090105180102090307030201110a0c0b0403030f0c050c150c0303070e030d09050f30030309 74
    0x260f40b00c90110140140b204500c41a501d4254840284940b03c1d2007030404154450010501d4101c0c20b41014185500c004018004e0090030032030709000d024100c0c04103c030742d8180200141481024899010800d007002c0300d10a906004608440080030b0281c0200080d01d007181e80200a0854800403041004207103030318100c00c0d48103c4c0d181c45040400000e422519a688122045020241092030b0308210700301c078080b00140001c002140141007140000c106410058640d1650b23031001001c0504c1d5a204206608860f00c0c08540c040132a0b80900b45841000160080581022a41c40008151580300200801d00300c482c1000341003682e00a941d203400007560038000303a40000c02c041004e801c5e64480802d04000346030000622608040e100c0c401070130540a0500549103800507107110002c6040c04000e03110905040012400060052405100152401c0d000c5543c1c07139440600303503000c1d005000c1c15008002c1c000c0700307075490b500400747e01c2c070010300741007801503181d400540308031009000d1109490700d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 74311827 1250 74310577 74310583
    0x140307031113090f05030705010627201615050f04080706060e180f061003060f020c12070c09050c0d05071404080a0209060303030411060a03020904050c0406080603 72
    0x19203a00004644141816600b0459980c0c0100d441c0480c103501c42000000203407a000102d1142803191000316120b080c0c0386000d60a690071900036803000c04065481c4014003c150f2001d0540103035803c0c00007808201004a50341075040c0c40054001c610001031480c0d664409080aa0a0325000350044d80c0b04604170760000042d1101900c180300014010030204020841a1006103295403084000141c83c940d110b03400645490111130104400c1801000420301580500014490403080f6020b01001d2404c8812a081c0410b00d0101402080d603070b1101012105466044440903050501207903d21800b00324a41010303401550308650b0301c811414000340820490050303c2c0960742941e841d82c1815030000e06c41d4020800100103204220304026070400842d1900003c1002d481c004001c4d12582c2c1d5540140050f0000c06007419000c1d910800401010901064103942d940758100c6029036221a03814044003c1c0c001c044038030358070074501400e2211852014004000f02e880980325107503540d4270342d000c251b2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 74313077 1250 74311827 74311829
    0x90606120b010e01050a180615050306030d0903051207020f0d080c150402010c0602090f090f0907120506011710020a1205060103020a14030a060f0b0901080c070507051c0501020d06140307 82
    0xc0c2140306c20106214248100c0c040b00442c15101a0010384665110180c214560802e601309022450000c10b101e8541014410520300307020034204444214515a41c055590b6052a008a10608041980703811035444985c5a582900c00501d6112a10001d00382624180c0c0b003009980d4183c410350400c0010352110811007849550161291500859161602d201941c0007d045a0380070a480c1c10828240d1360740f0801c24098240c104900c400303807401342416440c003107103a04640b40c51000c1b40b07521000110002049415200c1c024603807010104500c81841c82c000b45401900880350020170300c44000b0750302100311620307103000c4101841a5180c0c5801034080784200c1d4160400030b012200300621b600c240c5001540c02c10140407001400301e03134400150300101503580100d652200c0c0048d48021941c2d00c01461900301409076641d901e400003c0e9280b503501c0035030b4418503000f440152800d000010905800f100c1040c0c02600139590744d204e00c02c0000042c00103010301c12000c00381c40b0070f05104d030600203644d034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 74314327 1250 74313077 74313079
    0x2031e06010c170304060e031605070506041a0c010209060703030c020115060507030f09050a1d1e1b09040c0201050402030706030219180932060d020d0501090606120b010e0105 77
    0x145000c0480660f03100c00f075100a0069035040d0302c5030019002150204020403030f101120b0100c02540e100d078a400c4c1e042c0420395202901c602000c0c4020b01c12070b1110810544266000000c03940c2d103801c100080c50182c000c07420350f907911040104500d01413542640000d007507400039034000c0002010108400740211524020800001c1061041e200005c4c001d102143c2c0040c481d007041902d1030340d1080021445881500700441c02c4110a01031110000080d160315080b4422001c420845410f0507017003009120010600381c0050500710354001c00c09044002c4071070401000d48248891109800301074041c1c0416901240a489005000610035200f482662a400d10100703114000c071400c1034084601459950183c031a8103608180010012000e1288034511454584103207a0310b03104181001500d00c00d040c28484017403805080006550f030b2082c00c03140b10395040b18201085001d07805e00324010b10341140001c2080d45040c202150303c0e00305100342e961081c030540c1d900c0c0490703032114074a88005200303220319 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 74315577 1250 74314327 74314343
    0x1a0a060e07080a0906140106110610140d0602070206030c07120e100e0613060906080109021905071a0708010503012a08040305190f030c0c022103090402031e06010c 72
    0x42085100c854000e49004c41c05801c01180c07581ca40803101100316420f9020398049000b0030840d04485a00340a25980244228094201180313842918100007071259280e500c0b4080c0203180004104a0307034191243e0a070090300c604d880e8903003422910050346c8203170400d03900d851007800303100107003442000f60b8840c01d1400b4050141e000824407060303668500400b5980e51001c6d09000900502e03a03001e000c80010011541d40b40302d51460420054203614041c0c0152010078010400b0b550340c10010f030140300340c05506141050396042c60f0b050983c4a0310b4100c04c441c2d11440c0307640a0040182d0b00000e0581a0389045000b00302988240c0001c000310061601840b91312844e11085c048510f010702c00496001d4001e00300a480c202c600c1214100a041140c0d007900450511b9600001c0658140b044046062480c10003003860ba407503400113405000d03948900c4610015403400031401c500244151184610040d0040d51a41440010703040e44403a102c2d42c8603a450242c8000400540c820038110640c075030000b6003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 74316827 1250 74315577 74315581
    0x91f050f010201060509131205040b19120905060105010315030c12020111030a0c120c1a070e0406030809120106030206160813170105010603020406020c120a1a0a060e0708 75
    0x920a01402444103207056558580001605840d011001481441e10340c655042c450700b0343c6805000742400030b10220801074144004d025030015a81115100200701b201400b1000d001c0500701e994220110924074540d081c02010b10410100040d181c0c103807202620300b40040350803c3c407103030b41e20b584511003e00030080b50341d410411031000601d444e0099006241c0210110300c00340d5410300e140d04c01004440042c440080c44404d00001178010704400100f46441043d40d030341d54a89402c8403100b61013840c2e034410103401041403640280c0b0441240035003e4014030100c0c2c0e4030b081281c12600404680c44c0070710013035402c513819a0810320544c01030303950080c9071909040d900424915a1010b0040848236141c08111154140281c10010070041080c3c60320012081c4400c003040e0709543d41a880300e0103150041c001442050f4007c10b022640a100342d40f01c0c6421036988260a180c090f20300005080301084025240c04000ea00c0803e0b48660740381e542c10b1000d2651210030043c0d00d8400c071000700c00501c01d100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 74318077 1250 74316827 74316829
    0x3030302090f040203011502010b030312040308060102150907140a0b03010b0304030c02030304030b010302010315080601060e0a090c0e10080603070302010e0d140c030705040905030706020307050f07060b091f05 92
    0x4050001028040c21080c00c82c080c90000ca0202c0e4000c0c1c10881d941c001c81e28041c01c070144d0900400303160781800d502030360402c04605c3c0048402c40c40904001d091090540015281c1e0344204070018000441020401300390801c400202c1e1102000d005e110403000d008940032200c0c2c140138803850201c45c55104d2282c510780c038140d4800000d03000508210100300c0905980e6001d0390303081010741f0281d03020f00d01621032540345200140441e544807001601c034280e1640e0070070510360003043c2e080c1140c0c0c540c00d2114440c2100030014001900340e03001070910700e00e006103185642e68013980640815109444403046000e1118040d96441030884840342c1c10b80c44003409000651081c001440c8200e400f83c0b09010040c0380741c0c2c82d100d5008001281c001070b075220314001c61a6240070000b0a000306010b032800c10840c0a46d07101c1913280d10410750080e016903000408200200e00ca1412519510003082c2c07641e448000a140c00e0010f44800c030011481810000c01050a0b111000070301002e4042d0001c5101c6180e00e050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 74319327 1250 74318077 74318081
    0x6120601050d1b17010c03140f060f0111030d05040b06030a0506011a090d03020a02010e1206060d1109010b07030201061508151f03050105090a09050a0311010605101214060307030303 80
    0x140f120680c1000012000801400450190041e03500050000c1490b62a510004003206c1110340310b05000d06030f410900c08013002102207103800210681d1081101ea82601c0165051020070202c1081c0c1d201c0082c104080500039803195000ba407054242e50f000da21520100f682d104402000901903821800c0104041e140d03480a034498050010f01c42e07410a091030000881108000d201a00035030082c0510200b190780c440c440314418501100c88600d03841300e0107411903581c000104450300581d41c0305404003e00440380003140e62200c0c0204055200c1d0384400c0c2c448441c0d004940110095801d026000c541401d901c00350403101c2459948800f050f64418030204551033341010300315000544807601c0c50100b601c0f0303140c504031410651000316195140c0000e02c4070040008000380c030070610704030840e0001070000c5861090381c0e40628003001a84407440299004041e40e0b4170a59000c9029035008801c241c224500840305400312104011000c0030b50719020303d10302c045a10316030523004a941440002c0c042d03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 74320577 1250 74319327 74319353
    0x30d030c091710020f180316060e06040b07030c061404030f0e130509010606091a0702010513050402030f040b0907080c130605040507020a02240306090a0902040c0806120601050d 78
    0x1140481d102240781940c0b5404903440f030302c02411001170000b881c842c030300420303801009010419001400e0305140c00100780d0034400d01c3c0c02000c007000441409961259104015103020307212480300140e0b02d50b0b01e032a020300b03155070a1400b11816401c02c0b10b031040c0d2449102245202c1c2c0d8040c0c841d041e0302d0000c110212118017400b0422070b4054480420720042c80c0c0d0511a6600c00d01c40400005a2241444800b1700490105e42c0100c141d003050420f0b1400c082c0b44c0e1400c2e181400d9081c01d000741c4890781050100300301890744d001280c01074404410000f59601d40e03400d42d4041e90107884d031018030392659003896848520ba800b07000310941c4200c1d51300d001030500605028200456506c002041516100003038180c4a0a4a1400050b4440b190020a44c507000c02400740b819039030066600c1c00c540380c1e0801071443c0402405648281071400000b20486826000b104c4c9441e4010401c011a040d64940548030041c00c2d203800d40103c804546140000e0300006555050780c800a115900e00c010350ba480403152155 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 74321827 1250 74320577 74320619
    0x2040b01020f0d081803030907060c03091710240510020a0605100617010f05040c03091b0e060102030a08040204091b0b03090c0402040311090408040506040b030402030d030c09 77
    0x103003000d041c02d15005100803d4020390603a00c1404600b40580d12000000c40000124580e80040050118a500000e2040100c62031402c0905029109003030070b64008416034045040c400051141c080d210a001c00c1c0751020200148081042c0041184141d04440590004a1800581080c140840d190aa821083c0307030140348103c4000c2022503032013000b170b01c0060300d415800040380d010034400141c1000e55240320f0082141d0f05103844d850072003664400c0700140b007003d00441c2e90700c40c11042c0921913001182c1e1150402044043d55071320040e400300c82038242c03140e510030000720307004264103601c040b08030341075403200e03640c0d119494540ba000c11009041403c0215042c03c1041d007403400c40d000c030317240110041a4000801c3d4076850300d41a07181c00d00b40710f0610903200b584100000e03c0040da52041001d54078406940b800040d0b501c52074201d00d2449141c000c0c65000313074041000202401d8000043d88642d109074240d8406100000040d01a41d0180c10b080c4085038554009008000c5400040e010441d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 74323077 1250 74321827 74321833
    0x9040809030102070c1a03040f030c0f140606190503030f130503070810051605070b2a0702030115030f02060703031b030212060102210f070507061e1b02040b0102 71
    0xc600c0003900b20307804038404940b4506400c0c410003a00806850303259180e01a80314403485c42c50310b603403440c11035480002c00405211007100c4a0091080b06003806e442c00754000d801510080e2117801103a5501c2044858070310990840e40c140e110402028001e0040300e0000d0002c6007480090603440d4a140c02c1804400b801031a03c5800085176a401c100d03405c01048000083c201d1091a0b8105a0590b5001001031034200c0100d40c000000b00c2d48841102c04003608100903400a40318071078a48038900001c0c0c044c4141c13502414440011500200c003e01d642d0b84214000c01030509010f0502e00c00c0b4041d88409401d00da40260100d002d07051250007018043d1080c6030010304a0000615952008a40e9041000007a404100c0c8030003414840a4581c2042003400108110316900141e103a1a403079500c0c5051480c6004103070030301c00c5103107641a5800107600405a5000c00d407900c1c2c0c0201840722801034294140f10b4902017546003402072910540090a2104052600000d80c084c400038001ca244004e04500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 74324327 1250 74323077 74323087
    0x1505040f020d11042301050a03180c0b091e060403060e0f01050406060311010e10032408010c08012408060a05090405010c0914030303060d0c0b030703060501030c030c02030306090408 80
    0x30102d4401c150304401d004a00b40d48860911461846200480b000070140e0018825003c2c1d6036a00442502c1d2101110310b0042920a0505500442c0c22001c04006041021202000c00c904400c0006440310485c2a25600801070054442d69040301c0d14401c1103030090350401003031010034510340100c1440203685c01151408443c5d88802d0782101c800b16004c5d110150340312400d1040010200002d100e05500746403141c415040c08002904d001e001c0040b041c2416500d10103888060080b60300302d081e40c1c14850f4181d0140342d540f040301380a41f100d14030500000c4d650382c001142d50941d8030380b0341e500029a101c45440c0c903030206c042654140703030203002c0d1580103040e03400001d204d80e1040000e0b8816880b810000c076107041071990147c0380b42403d411404001114a45082c80c58900100381d943c0001d044403c0c021003200d90400d01580c80c8e25401c550407000000040092407600364100c10100ca00a9804019405610350101c045174464444800180c00c2003011610514007031444640081c01404402d10309 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 74325577 1250 74324327 74324347
    0x201030603050f0c0f06031501030b03010e120702030601060305040f030c15050717060901060e13020c0102070b0f0603030301030b0708071202040f030b01050d081b030c06100e09011505040f02 84
    0x39440083c142c1c0140d0011502c3c107200d0418801c40c111a20050701d4240c15070505c040700c0411812030104084c1019520b9420f040940d0b42504541c400021305410344423240f01c070340d81400e459409144264061300c202d4000041d564031902c00c0510842e00211200000c001c10f039800c90b50380c0c6020100b6584142050302d080306481c958410306000e10200d403030341d6411400390001c010804000500c0144030b03456850042004a070003400c41404ac04017250700c14100c0c2c1012a249000b405a10301110041d803001c00e10004004100e00114001c628035200051169a01c50801d82e4900c002d00005005600c800302040409000d40d142c0f940004807400c0032042d0700781c9015114202c1e0410b07446440d05110410042050010502042c0d01401058a0003000f44006032509000c503c200000c141e80700020301058055000180166030410521100340c80c86401c2109004403010468081c08040140b140041403080d00d0510480e610407051051204542d0f107040c082100130556a51482c902c40d03002c005a11003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 74326827 1250 74325577 74325583
    0x60f0f121005040f0b09010b0a02101d070e06030a0b04050a02121f051b0f0d0e0304090518070303081b07061d0f06130c0305030c0114060604051c020103060305 70
    0x410081025a001014a004100801da9501100507136455141201086440d260350700007a065401208513595521444a8128a00303440a00e000703c003242b400d54070f01c1c1c00700040000d1094181721001181c5490340c46520800864a09840c0540c1c1503100c14030100c002001003004540c05801681500c0d0706107441c2e00800d220411000310102c15410030307468248080c500030110400f41810440030400351600d0700702079540d01c040d4144e40c041d1103000703d84251480f0514088440340c072090041401181941807000303507a90824083c2c2c501c0d01c1c1c10600020307180003050030001020010310300105046455a00c00740c6854001804807540e41000c04407031a90075040d80020455940304020005140d40b001001030803048440d022400c2d43d0300081440810610005505034201440b10180340c0d1302d03034140c90408809219584000c04501011075015410801980080404940c08000ca4a255150400c104580c4074500030769a124840c01306480455400c1c41440c2245403041c140040c02e140c4944034a0f00d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 74328077 1250 74326827 74326831
    0x10315051c05011505061b03130311030c100519110f0f06070c030c03050a020102041208090a05040e0a11030309091639050a020a080c09010e0105060f0f12 68
    0x40152000c0207400410409101e02c04d240700e030300901c0c0c00b641ca0911000684510030b1711108201992882c2160303100803410300072114007051418203c2d8000780c1c0c078900400740d10200004d49210740211138201aa80c04c0c000c4c94585000c0351651043e14081802000520765110b840f404820004103102032826500c0800c09010f55414a074010040500b15129083c80c1c0f14005082d042001b1074410040006900040300b440c41c141d041c1444c0b500d50007607620482c02409141d12071142103c0395011030062024070760040086200c141c420243c80d81e1a0402e1109640e090002c0c0c1015078000d00200020130700c6d01d11035a000a84c0181601d241c03034048800240b500324241d85000074a81120a00404690011042400c4015510110001c2d114011007290510401448a079135407041041c88400c008060044e20b81065008018442c482c0e10f486a1541d00d50050811500400c400c0f40041141207076018510304907000181410b20f4031030340140400c0c00d90450074105024040030310100c030751164010f65040c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 74329327 1250 74328077 74328109
    0xf0212130302130605010203121b0a09180509121e07060c020f0109051005040302030c0a06020901090b04050901030303020901050d050103060b04050a1527020d090302010b090f010501031505 83
    0x10310500d0660040048103090500d1400c0103a103002ca0421003a6000320545042c00c1041d034080f18a80d80b15195100c04031034071542c2140d2503000003206031710a50060b030050151a0209135400141c9c0c3c11216810403542d0550b010400c942c07110290440b0b0006c441c0061200151070039042c09003182d014100c040b01c1d00035490840ba11754541c903020035007950400071400c62940a9000f032081810740d4944070784503840c00a862000c661204001030600d402041191a0140c201c021641c80040c03c1c20402c0007500614040c0780050103200d40000c00040700000d58040d618010700d424001d0346580d80c160000e6000810b0300341407210910610001c0c20040c0700305c6000318000c00d00401c03001180802c21048a400900c0240551700d0304203c11015070424000e0000d5070080b1035201803a1030000c04001e11040440844241d9a0001a02e0b0071000d120341c01000e90304e440380d00213200c00d1210008100341003004071102d8081c200d117100100100d41c466040129880e120201f1a29680e40724400700790100e014540346 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 74330577 1250 74329327 74329357
    0x50613091806230a0506040b13091e051513020d0503070203010c050c0c040c0201020903100b181b070305040e090303070801050f03030706050a0605030d20010203010b0a0f0212 77
    0x64420320032680201d038405410450f0468010f01c203882842032a40d40540b4070108955600006499501c842c0d0049540000061260910312402c01900d80074003844541110700c03a03170021300e044068648152000305581c5c42000360215000e00580601610401040da01703001c04000c13016000743c2c591032001d9110fa40188091039644080e4014035080d0340510ba065800c1205c00c004046e210754000c00c541c00c0d907141c11240481d00d0001254220b02a02034036629650501405846d225443e4a42c1d0041d0b00c61a000d5401868607000c0801040042c2d5044034003072800383c0014104a000f040d22030040551600c2428010304281c0c807003803940030110b401c80309410168000001c1c40700385c5420058041c014802258152203414400300443e03180d004001004112944941c08070301a41c0c80c642000b00178140140844030588850400104590080f1700350100968006415018415040c000c0381c1c10785503510001844c04089001c22180c28621001280440c041c0c9184201c540f48036400500c036103402005c0c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 74331827 1250 74330577 74330621
    0x70f0f030c1a0d05060a091a03060c09060a0c2a06020f070602070b0f040b030406090b150a180e0f0709060603090209040f0f050a0515010608040203060105061309 71
    0x403060741555085014036202041004030070400d0030381140e8050303849181c04941d5480c1c49010814042450308001c0c01035040035850442020049902d0202c02d804508540f900d0b1941d80d290000d502c9804181c0340c000400b0000a800030340684078204c1282e00c20301c00300e5400d40c04241101c0d40700414000301c2000c0c0b038680e0302c10083c456041084079800941040034185c81e83c034000b0083d42d1482c00d849192030b211404100241400b0b011010788004000384d07441180d80f482d00d450160020440110201c6100c40ca1401140e1520000030503d404c0e8207000e00a429214105034081000c03000c2409000305ca103465001c11150f04205100588014400c200201011230401000d2015510030fa0480c004062400c03144901607901c02c1002e43e08650010b0b90150001c0107410800d20b4200141c401030054410040c03108104100080c00d880a031140703505070096a6203031041110019000d13600654150302c440018491460000b0041510f01011040f0701312850b03a0320083d40650382c075540c195000b0300c5c0110f9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 74333077 1250 74331827 74331833
    0x9100509070303091422020c0a050f2b050f07050d1706060a0801090e07030c0605031509040807151506050310061106010303051606050411030708030405060a030e070f0f03 75
    0x43c1c50380107001840142805400f090001c41c000c0b946e031401c1c10149060000d0101080c81c6541c1c121111040b010040e41c5821103982407072540d60520684038040c1d4810000d04060300c403880c0398071001c990481c84002d20a501c0c40e01c82112141c0100100c1c1801c07400420002001030350070001d66050031030f20b8880043c2418031000102c406c5100800b41400f80310108070822206502820090544508080016801035410100340c5400107940000f00b80980c50907010400305e80000207141b00d2103490307541c1c031500c02116051200304402540c005007500400e210620001d104045843c020380781080c03000170406410700103668585401c0d880580807030000800d001450f071117072601e03101070401802d0140a140f5090f010540d0340d00d0501c006010048040f900718006d110781c40188070300b150008014041d604060406404203004901042e229109403140003c0d44100802602c0454000410003030505030041026409031081041c000345502403410041640142d03d04004098030000c02036020369804c601d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 74334327 1250 74333077 74333087
    0x1403010c18050d0c03020a06050c010b15040510030e031603110105100e0a020f0a080106030b03060105010221040902030c070c080705060a0c03020f06071e0903020d02040509100509070303 82
    0x500304107120122901440c4160210030880c0c0c2c060710055100d4000c0d007040000000e42da00000d41c018004038000410650242c007903e91380c2403e00003045006040d10811069241c03070f0300c02c083c1d81e402c00e100401080c98510080307226005541408100c84000206031030030369011000000300061104c0900c02030592116554001c1940c540c000c201d0750800200c801461070803882240c0844203a20000307802d80400790165045081445661911a000d10b00c02a010715070034099800064079142c2c801d0240e180000d8180c0c100e42068001e03010700309205002e50918100a90f42c40f88a050400c00050071003001e2004610454080c1d60040d110007061a010f0a442003030390000520b540000b006000e1a45c40074100c0c0e00040c898108a14010000e10f816401c1502d902503201c0e190040a00300710040360040c615480c62894040a907880303090f8007609803845446400060b4101880348100001410309030710980c2c2022410040b035110164040510b0156072003100c08030b07010303084801308004154000f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 74335577 1250 74334327 74334341
    0xb0f030f010c091a07082a011a030a0c06080c1606060501030510031a04020424032303030406020d090503030c09100c05030d0c030605060a0302030415090f080f0f0301140301 76
    0x31410f2903134880001640c41c105014040703004d40708036000104414030b04d0110a44200500c00030520b40a0360000420403802401610f42460303281c0d0342940321400b0b5160100f000c80e000c9612401103080300d401e00c0030403036224400900d5002800010803030601e401c51104010516248100000318901e41170400042c10348002400724104210582c1090001440301e03401110341060014000d0040c3d42d844c0000307800340a000c1c040c80d40ca200c1032851030300c050907a10903504c16640102d810301c10380002c0b5032071140d44210810040b01990010b02c0031400140307244d00100b4501c64081d002061601481d162241507a00035110901c030800000307080300c0503081100e100519100c0c0c50800c00e00b000c070161070b240d0310b87c4261540d100c80e26580344040c07503410380617500c02e001404010780295103d0000aa000d00254402e840035a001001c44e02c010900510354014a15080e601510030901e00c000c1b40d50f06a825001041e08180b025000c0c043c00c107000c00301d0340245d4005c10742403402c03044004121302414210f8001d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 74336827 1250 74335577 74335589
    0x80c0a060210050a0b0d081b071211030307080f0a09080705010c0609170d0c080a0e19060605031b1801050105090d141002030702061008060a0b0f030f010c09 69
    0x2540400c001003500495070303000c64008904081030035540d0000030002807464034142d0741c1c000c201c01d1030744060240394000307460500650540d00000c0f120122403560b540d4102d1245810703100000d00d0000010781e4054910b160f04002800b03c03400c0c0740803652120090340001c66400c0700d4680c08161a1001ca50111144006010000103084090304107000280780855810380980101d03111075440c3e040154400251003400e0710741c003910b44c0b40d1350440d600b50043d089130307a00c0400141e1008045400542140b0642040da00100c0080c110301003412120009101694020340c0c00a5075070304000344c03d4500344243c84607800d95449003c1d0341c2e00d0f50780401480d5424000814142c1c18004018003169030098106d0f002904211260320071101c03546402c004c44d00c0c01d010390f48054001d610310f0f241c6500481e0099401100b0a409840c08e079a070b8100d403c1032152030751045005076030003200403801c002215403102d0b01c2604c01904158580e45031001207450044020304074041c6a644200c1c0c42c2c40680d00c1407078903000d850f0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 74338077 1250 74336827 74336839
    0x604051005010305030910050706092604050f010c15060605070c06050901080a020f040302030a141c080703090314031008010507030b1e0105160807020f090919030210020d06080c 78
    0x410f6480d00c030303541d001c1e1081c024007900ea01d2054554035070088064410196100c00705000c1e46546203000e08040840140002803560140f030300040c480c1b055000ea40c01d45602a1640c07150101600044072080141c103010344003840442e44040f125810b1740a00c82c0540015143d4544da00c40d05e250409842040380d1120701041024440c40010760b034001501034201a60140c050703100c074840307003040354640b081d907000940c103224014400c0c007040810303545a03030074098042c2600d1412103200385401720000b8403c24200000c0700702000850040c000e9000c401a2402460042490420700d400c2e00c0d1283d0060f2a89000d00c0d1043e03200b0400100c090280550200c514901070054404140108103455200c40c112140b010101c45540c138503074415801d5034680c0344026030021101c600c034105282c0d181d000c950241e01660700b040c01d0008504000e100c241c040c11101c070040c00380601d5940c03607222a0054a8048003103000d901c04406c40780c1441d00241a540001d00c60000f100c0b0302e03002407249008140e15900740108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 74339327 1250 74338077 74338079
    0x80312072c0411040f0305010b0303210406020d0204030807020f031609091a04080a1206030b0103020618060309030408061602030a080a060902040303030504030210090b15040b030708060405100501 86
    0x41150340d0301240d0307580c00c100000c005812403000402514880606480b10000850000341d80d02558008500b128010002000b40041035424161684225103880c2c0180358600c000c0c000716203101c08003652245c000c110050030140c00031440c4082e64080c7d40141d42019000c00c441e800d521b4490313030301400088104c006014181c040026a0b80710f03405442550000c50303a581d103030001e0103419940445511505c9007003c8840c03505140081494000090715000602d1903841110190b859116a005a0381c000c203504030300b0307842e50f070800c41d0a9200c1c850000c3d08030351440407403405454103405107010300703c1d01c00a103480710300345880e441c90441d0092010082c90200920322840c9038003c8121614280240b510494030369800310a00c014000703582c4100d801c0c070b100040000a06038180d12150059105e0b90a1750440c41c0c40318408001e0700c01818018090610513004228005000d4551607002c140240011035a00c02c54000a820300b004d2b07911180090300000b042200300034060048071220008504100455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 74340577 1250 74339327 74339357
    0xf0a0b030c031902030f010c020618010501060207090e031c0203090c090c0d09020109030512070b0901020a120e0a0b15040b030a030905010c0305090d110a050d0f0602030c090a08031207 81
    0x1c3c0c2100d02c10401450b001200e140a43d142030002c5140d00d04548004e2205012001c0000c2d0b55204c225003180c2c4c9000c804420003e042c4041c005e26040395040d50081040307a040c1a880c1004189010f1000134500c01041841c1180052050003105007028940041c2c49140890940d41000d0740c5049483c0f01e00d5461040001c80c00304101600c1000d2080100041e2040b002c1c4016076495006801c044c013184207901500b000721850708014285280304000960182e103980341018280d010303250300381020070401c520701c012007007003544820307405000641121558019502e85000f0114140c0c3c1c120411f0700810095940c5003403902030000b050105034001c0022440c81d40b00240440d041d400340b6410005652082418140320350203551000d4401401080d1020040c98420010b8400641483c01410001000100352a004010b0442613801018072280c01003d5030350b00c4000c2d031000300704015071901808843c4080d1125001031000d40000c2e00110342d1040ca00080c103a05120017400c40d010401c0e010a56200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 74341827 1250 74340577 74340583
    0x6060e0d02060d0203090307020303030108030d15030302101505120304080106140603040b0603070302060d090303050115090e1b1605010b0901050f06030a09021f110a0b0609070c0204050f0a0b030c03 87
    0x4210b43d0b6200161680c4810588a05511541d0000381d41440080004200310f04040010700d0301b4480410100035501110003080c000034518400034000d07130400d8500301c50f00500c0c1d030469400c40c1c0f602021784880588480001b8560700034040700c071003240c1c0301050602c00003a0910400000c0d042400c1041150105100000da05100040004226801ca500411a541c0b810040781024542c0200055100c0d40300c2e01c005801880c0030041034001a00748000040c411811b4020180340490341d03070364a1040ba00f482200040d07604081c00c004910000200e8119100e02c480014085098142c041c18407000024185182036540445a0901c0b07081d000b40100005c3e980d6076010200c4101c01c3c2e80c03041c2c0341c0d030b5101d00c190700800e002e481c0a03401100305031a28141030700792480f06000e098039450708001c40d2080c00c0e07030f41e0381c8020540006050041031404180300e80b41031044541c0c00041440c100450194075408201555019244609070385100310034406101c03158001d441c8540c03401e400038104070901c0c00000755 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 74343077 1250 74341827 74341837
    0x50102160b0403150b060a0e1801211109070804171303020405040201200106080114130b13210e04331e080f030a02070501051606050a06060e0d0206 65
    0x11204c0c12440d5084c0700040617030000d942c400f000424194407000710490182400c2403d2811074442c8040801b40074018440e0014641610180d401c0085a80c501080301114082c1c0c40d101981c0b800ca6040d41d60b5030700d5546100c01d81c4140340640e1101505c0c02c1501d005580c09000208420700303043d05004074000c1054558195003142d40440780402c503502c9500060310010341031018010f112111000403030382180150480f00c2101d540f41d00801c1400d8101c41c45c0e601001c0d0680701da41c0040c5842c0c2461000c00d42442c001904002d14403007100c0203803c16681c509441c07082002e04017645142c0c0d000c240c0c02c21780002d9141180c11080e03071300b40034041c85e050301d050a81c9002204c60b148900f124098414410040001002500804d0619124120010807007481c21280d407149204031304c182c22101000c920040140c6c4d90020b4150018140c0c42c0c108001920303290020204010108e41c1e0f40f28002c04240c10703000311401038035610350000c0da103404c140009007d00c2a42a045005203018484c0c480180c5401003114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 74344327 1250 74343077 74343083
    0xc0f0609120f160c05010f020c0d0809010306150906080f0f0a0e07090e1501091103010e130f1406090303160c020604080a050d09081902010305040f02040c09050102160b0403 76
    0x2c1d0b84800a510440481c000d00308501040204024500200102d5107020002e0703500988030f40000010319401240c0c0c0d401c2c448801780c1c1100c20490010001400c1502070401020b05040100343c1c01d4075100402a1501468910300008903101810802c054100007010341090040420302c54910b41400034401581c2d000c0c1480540c02d54a0f860104809014404c10b0003402a200c010303c8103044140703080f541c881180c10202801e091100c000201e0015510070443c230079030a113001e1410760f841d11201d8a05500b004151801282841d13032680001650140d40b600b400780700d40c40c0030442400c410826884c100c00103040d10000c0d0b000700144022240054451303641840c99180c400c0011070319201042e51402685e00060b0b451195a440108102003c504070302d810030143d075080c1c0c103107540e841d540703560710f10000740d180501440748502009035110381c006640c86030043c0650300d90030f480e40c1d010030200c0d640d0444503400102240030520107503a0610000d048203c1c0300c401c0c10000c1e4108080c2c2000791185204c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 74345577 1250 74344327 74344363
    0x80402010f021f060609150e010c0507030215030a18050c0f01090b030705030106080c0f03060d02120708010f15030c05210114041a16051305060309030c0f0609 70
    0xe505490b10030802c21005044411402c05000d019100d60406440580100404900c21140c042603000307039448200b0119a055854441c411030000043d1400c00301d0b014291403502440b140400540c940074000445402c0740181c640da240390110903102201c003070100315860800e81c21600c8002c00c20004044070501800c546032a80c000ba18001030b030302030400f54404c4602c02804803c10048039000400345d07040320950b480b035004940d1b481d1034076030162103249218004040d0500208010381003030149143c0c0c00e480904160f82d0142e40049142c07800c0e542342d00c400c400d03a440d03c0d610b00000b4242d014240c540c02402c1070340300703138103041d5690b01c01c3e140400e024241c00b41c04c0c0c205030010400811074580401400c904000c0060847e00c15070402ca1950840c1c007514042c040309030a0200049103009948680c034494200c0d08800894403040750a0f51000322003002450003040c001c10682d0300c00340214024000c860041d075942c1241758030542081030141c075041031500220b0030400c2c5c5807000b02d43c040e0440c40035039507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 74346827 1250 74345577 74345597
    0x10e09070e130903030507050c0709020906091207090b0f1507020d020913020117070512060103020c070803040906090612112706030111030705040512010b060a05042408040201 77
    0x89076100c404142156009031039101c0da080303120441d8070440d0014001d5505101c00c0d910800280c44600c54490556581d40c8501801c02ca106803950161102101c0200a24a02400ca10008100f401002494549500075003c1001009100d10401070780c140d058481003c410303c07403c0001d03800454440b680d406d031003002450008554440d0f22030f0540b036600a281080d00d0510300440120b0001300441240410400301c13164609007525402130f07124490b41d582c0e80d413600980701c0b500c040c0c02da4041e200e1410715400744142040780c0c0051004401034140d140040d40c845140920b4101690416800110b009e0f160880070700440400b140b01c2d000c1c0d550041e4442803500c4608000c00c440d01d00784100c040c500284030b54480680c151506059004030001c800a1142c2800202410000d102c03d139480c6010450030002000b0500340200314010303142a01000061010f201c0300401c1f4240c0c0206903180001e04002002c0c8240301580f0707c1d00006401982d1001c5644c24040c4c0043c000b00800352020b414031a01000b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 74348077 1250 74346827 74346841
    0x1a25020c031203040f0b04080c01051302090a0b0a030213020d050604060f050d08040302030d03020315030705090619081c021e07060c02030307020a06020309010f020f030703030507181508010506030402010e09 91
    0x920080700320391001b44451181390070300380390882d900861038400c520350800020861034550107411001040c1c005002c28441e0f211400200300402440000c280c010142041c0080569900c09103401030010517400980e9622007c240314040784c90007000684200e25018080c0800ca44000300503040d19010345d00001509040d003801c140c0d038002c56000a5041c417800740d000c07024503410703005140130350410b51a02c1c0e0b4041c125403c0540300c880500806401c001030000180c001c1c035040382e020341d0202440c41e0b018000c50b00d4201041c140708660240e41e4006a00030038850388207a04016021764081c1a2142844100c1303c0c11255858a440348120700402a172620620195a0180304840c2400ea00603c441003255030342c4800b0752242c0024841c1e0380070607481410b07031030700c240045909510088030801440c6010403da40c02d03801020040c01c2001000a040000c00b1005003022580001d4090000e01c946400414840104840c505130083c43c000e64081c8180300060f41c00c951400c82040040360306000c035a80d519 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 74349327 1250 74348077 74348093
    0x80307060e12130603050a0902130c1202030f0103021002060c09040b1201021c0f0606020c120708061806011d0423100e010b040501030302191a25020c03120304 70
    0x102c0140000000812241402d1000c0111044401d82d0320148226070b14070403061b003201c1d01908003030341048099520b0315507182c05600106c20400316050140000700b5601c07040c030403a00200c07090504c40c223000d0018000e42c45d14002408900c0c2043c80185090b25290080003c240190034025000300e031125014a095a514840e00d018411100c00854484d140302102e14044400c81100140c101c0c80d001501030303421414001c0c3c0302600c99980081001203042000e20521120090110354503004041010505803000d1140710702400c15200c1c0c80390210901c40c009410f22906074007244540462181003c04240036400c0f0341e80c0716810218a41c80012040c0a080c038059140b00c002d08035000e0f040e9052004001d5900402c40d8181a4000700141e001d040140000c5820a02003d809644640c0104c140001004070000d2171a220300c00180349102d0300c032520045240c040d280c0800c03215140403142640303110585c22034020302d20340c401020520003013004680c0300c2042541d00e1412200020010341800164 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 74350577 1250 74349327 74349343
    0x60509190507140a022b020c06031f06090306050c0403030c0201180803030907030c083c061303080f070f030903050c070801090506070203030c0904020901020c12030306011701080307060e 82
    0x9000c4240c0c4c4241c4188020b46580c1c4001c1640c80c40c0744041c3c070b040307804942180c4600f1346c00c4071a001031141d501601c040010540004021401206140f204413102e07400ca00d264200410850320b82e6462070742146846401c9c0d6200600c04d0340321385028402080803d41c00b100102c440307602824219203405490ba803d06001405c0d070040c1c566840004140090340c400007030030800700c0340100b550010300c0342c07a5107001c1d488a00b12010140354250707401110310f000d422840c00381764001401080001900c480700c0018103103202100e06521140c02d21000005064010702c545610488084a120300703858030319009005250360003155400c1541d0381d5480030805009408071000c1c00714100c00c84101c0d0755610446400b03090382072000c0740c140c000d41001c503560500020580b80586501400b541c101405132040c0f00003504415209411440307602403280c041d444620007202c5640e224000756690380703441800074040b0301c402c80720561180b40c42c0004208080001c4185c0c0c490300e0b8003c0000c1550400e450345c0347d10700f0001e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 74351827 1250 74350577 74350607
    0x3040909030314040c050f01021605060c031908060901080d1403091908030601170702030412060603120c060b010e0f10110d0203030403030501090b030a1203022b060509190507 77
    0x24011301c400c0c481d120744070104481d400c8440c19036480e13000c00120b0f01da8204148071038009030030201c18440c0b880d00102502003045594101c2c0c0c01c1c1760f00854040b00034104521400c010a52900500002e814440c150302d0142910b0f10083c03660f0744400c48010081800d9180540f00a9808008034168035420312000c1c3e0070300d08000f14042d9110442c02e11740c1007944152545804134500d600c407680c042012854841c41120560082c605180c5000401c1049400303a40003112000d940300d00100010b81040290943e1329456a51010740c60b1a80c94200308556040743c4203414480d4150080740b41d980c0d83c2c0411a41b019095600e41c0101400640566085481044880150158200c0035558550000145202d14025034051103643d03616528903003107515001c081d42c0c02d41c00400c0c1034000300b08190384003000b041e194070f001842d0905a18000080040c1401c840a41150000c5401d80443d20390003803502170201280c85510314200305c040b40d00f9006014115061040d2100001840305004818038840010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 74353077 1250 74351827 74351861
    0x309080a0311060a15030b040c2402010e0c0a0501050f0403050723041b0302031b030c09031005060105040323010207060c031406010212220603050402100c0203030409090303 76
    0x24031880d029054441c19100c4030741c0c0f48514800035003005000d00030030104103150303402c42d4000c80c11504c402d116030384000c00503108442e20f600f0001304107841c041200c490401ca6800070038540301d1902c00901350b600c0c021074807840c2d51245020640365a41d444030141158001d0912130b68810105890b00e0480c003503544040e01c2409252000101014866580c00c1c403801107041800b40340d03100c0300410086034400307e07503020702049030903042c40c905010743d008507000203a6441683e03200c1d0103001c1042165208998007003c4640103c0d440c01507040400c010036003401800d00501592401c0000200140200d10014100d03002c000001a00035504010701301290707003040001e5650b801c02e4200ac03405001c1c09540040040d103007820f0094070b14010a03509004480580c0504450304a407000444980c1000c03010f030400100e0004841200800a164900100b81548005c510351500380100280e000103800c0b65001e014202c18210010380d0040100d03800d0701c0c24210300184103500d0b07080072002050500c1060348440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 74354327 1250 74353077 74353093
    0x1031a04050a0b12060723070203061906090b0d0618050703060b09070c0f020918060406050106020d09030309030f29180114010e0402031c05090103060501031116030908 74
    0x490350f040088510001c2c2da1034a4620403002d0b64075920102240c41400049486c0101b01c45010440c82440c0b044891071245070400c081500001d081c014281d0311448a554183c03000c1079400300300d00801d001445903010030011303d1182d801040161078404d0005080c0c1c1e0b51b81b80100007690314181c002445a4000742260001a1170b440c16000925100040350300c2009000c002865892090421009081e40101c0d0000d5030030305076091000c8c8200c05004a0500441a021026900c5080000c44c0c803441c010309011545524210010742442d0480903c0c43c104083e0b0314080c000b02c3e4100010b20226a800504c0040c0d40906080090401c20094a441000d480d10700f1040c604075581100a4019001d060390885a081e10003070041c202c81301490f030030a1600321a0010081c442c1e0500c0402e0744580060192440700301c041c03d0711401180e801c41c020001c100c02180640644d41e0600c60354026003001e003000c0103000c054410001c908d00415091000380800d44550100b018841c54440c1e0090a50508a43c059 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 74355577 1250 74354327 74354341
    0x7051c230a0c0909020d0f06060b07030509120a080a080405070f030311060f270a08030c0d051b0304060f0b060409020a02010f090b0103020d05120310030201021908030601031a0405 79
    0x1d07034030080151030224120901244940c0745108a802c0e0640c0180b1261010076181c0c1e402c1d8521012450680c0d0300c6541e544006240c102580041039401e00c04d030366241e92604450200810720208042d452038039440820240002182e0004548640110342400e0000340d8807450014a0485160403001c0c848108810010805403ca200f052146014806aa070207554004884490308002c5402c2c0000d940e4810040500306030490400104d5a03d83e425910240010307140c070034a41d8000d0711180600c2d80c0020303802d2180c19040c030890f500075038180b04010100c02d012b6601100d03800050005842503540d00d0750906161340d03543c482000510050459a05c40e42c0e10000f1000a4206000200c059420440050742e0346503e80320384082c6a50010715075496900356024003901c6c01002200721003034801d8044c03041c54084030501031841040310301c858001641c15071000a003049000e03807000c1004c100a130540400120000c0c1074980c0080e0a1a00040c0340b001041c00a0310600da07800f10f180c00500d808140000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 74356827 1250 74355577 74355583
    0x6060306090b010510030507020c0d020607021009080d02010504050a0b091c11010e030f07030f181e080607020a0308060a03020402071a01060507080d0b0109080609060105100207051c23 81
    0x480c4c000320783c400b07640c2002c044190140c03982141d02c400145c01c01d4544c900a480c1c000e48096440c0e00190285091080c1c660119820b03402001d812804900780440c00c000c07000d02080440c0429120b4802031002e03003816558180e491052640081000c0f581c0000a40014010030002c0201d200101c4001d46200c40004003600c03100d82045490f1140d42404800e02c5c0100d000411203c1c03a07082c40e140f40f807402006031001c95000d0080d030070410402c8941100c450ac144014800310029281013081d089090211180e000754107480380d8803c0010360040d07070401c440e05030042010600395070141031480943e640d40000905147c0c0a420003548070344040344003028030030340d42d03444940b11500c01c8904145980358201a40c890260700002064610104405d40203480c1c00e82008081e0081810461019034440e03c00e54200f20742141e01884641c072002c0104002c1c0740c482402681c00c41180081c090940c20103004c070352480f0481410214070310004e00208104803140325034800c038950058604d16505d002600705e40e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 74358077 1250 74356827 74356829
    0x40212040203060709031502031f0602010c0305071407060b04021b01090c050f03030a052d0315040b0f060c100c020d0206070513120302011409030a030513021c06060306090b01 77
    0x80a80f0032980001e800b14000d4103240c0c16250411050012047c40d5480480a5400207001540360b0441c003180707406201c2d90080300300150005800100d480841b5660003070407188020011404c001303000108000b108070a0b822908100d810100203d83c480304440400d0203403049801c40c09913402000d208611200041d4004040700744906182d4448035a9842003010492308070550301d81c507400c108901d00c200ca001d0f000800301c0d200003005815001441c1c041c0c030098202c582e101e00140e0300000040200c8e55024400114041030200c40c200000034422011400798001031031803502a85000618800b074070400c10805104945541c018041038400c2c010080d1100c010300c01761030140c803902010030200c0380034205440c044010210040001c5203050121a864000c5a030180c0c2035558804040481c6082036620b00c1c401c1807100019683c0c0c0c156102d000301210001031001440191842001005940f884400d090003940c940035030b480c0215038200903000f03050641c0001d02040c40c09410b002000b2075070000d28 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 74359327 1250 74358077 74358079
    0x3120302041e030203030f031b0703050d0e0109111c02091f080f28020904050313050604050303030402040209060f030f0103110d030804120c0b130c150c0f020f0402120402 75
    0x160078000302d8416004024914080258550010301000e00c0160400c3d0185522a80c0d403100c045244024003210045641302840c00c1c0d000910001d041c14090707040d4000c0a42091610008000395003458460500507145580300e00d20600252210444140c00c0c0c8032100040c0d500140484103905094080070718000c2c2c2c120203040680410030001036080004035407007001c5004080034091100501256003032241c164131418000c42480c900f030b9005600c541d200380d40f00718854801159100c80c0c60010075200075403940300c54411107042000380b01c6920003106590b001139060f6809611440701c1e000042d59030240c04150083c016000c010441c0300261203000078102e0340588030042c50b100081051101d0241600405030101d00c6007404a000510a0030400d206184a860103004103203995a4021101805445140d4500a42207190081c0407080d503a0200a0001410080800603550406407030184a45000340030095409469015502e88000c0c101c175030703440284111b40e910752050010702c4240701910300b0313 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 74360577 1250 74359327 74359349
    0x60d24060e0603010b07080708070f1a0112050a120905030a030207090f020f0a120f0606030509061003030206010608060a0306051f35010f0c08040605070e0904030c0c0312030204 78
    0x1800389050103001c0b0f9068604402480b407400b003e40d01c0e80d500c141d103d080c0c115080341d800c02c686004112134401e0400564131880540d581d03100c0104883d42420782c1a00070082e0072003d180c040000075000610501110791000e101d14404200c600262214034480d0b00054040c05194541c60070164040b40450558207a24410020300c0342685400080340a0030300d1140800c1401c0000e2007640780102410f10711042008008540029001d0034a4151002c0b0b52142c00400c1d160b100307010803040107000c0d03941d001813202c0c20009042d2558800a40d242c0b01841040107104c0800e012503080d8030791808890295400c81c0003030019080401074804c0782c660301c9101d92003081015001056031481104510410395814038100c01d03181001e0000903100b18043d203400041e65840c800d90560400f54003c0790042645601d5500e00e61030f141c00c0050958100600b0b00702046160b400d01a80e0340e8891501d150025018603010325501280d00d0407020301882d503000500ba200d03580010b0b2682d03e50640040050710000d02c01c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 74361827 1250 74360577 74360597
    0xa0f03051002210603010609020d0e0105060f0d020108040f02061801030c09080303070f0c0218070f0e0d08070302010f14011a070f0809150406020d091d06060d2406 72
    0x52030003240502e000f02001d02e0441000026903010304211542c1140c07005000180103540d43c0d4440089078003e40e00d181c0c1860f29a0505c214035a020b01c81d040d4420410346041c1c00b101c98003c00904c0f0781c902244001d05006800300170505101c4c01184914000368042c00003a42d503c0495040030031001c1c800c1800b40000c0c202220041d8503440307414480102d078003400045085855090041e6540b0030790b43c1c03c2504000c80200840c01580c0c03042c1040141480089070b030001c0d03080c00c1e40c00034080211b18290001b405100e00540b100d0f0386500c3c0d0703401f14480d0482c40441d1150320900e4224090614040316101c2d4a0030418580009007070395660904840d0707074104901d400030041808030458094000040c0554800c001d040c404100c0c888000c0980003001018103003031400d240004441c1b504203400150060340425180d00c103c541200e0390344040c112500401c1203a250500300c0c3d10109100a202038043d10340482c041c00010042d42000c00003000006c04898500050140d880501d44584030304000a100146 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 74363077 1250 74361827 74361853
    0x405060607020904060506030a0c14010f0810030308073501080123100302060301090501060306090915090519050a02100906050a0c05070f031a0a0b06180d020a0f0305 73
    0x4216070005901410440150f03465032510802003600a10311900f5006007440d00e0009820805800050300f48209891486081710000600c81032002102030b00780903011060007010340f099a030280c00c40340e03d46082c456565a40c174080f140b42c010300d140b4105482d42c59a0083c07200c0ca514500402c8000c8841c016075460781d032045120f0980b150f441ea1058600c0d000680100c2c40c0b800d440351181d0081c640c0100c0b240c40b555030750205090b075000341d1000d02600e9640005006040d071601480e00103000b9014203105100c5151141c108012a0b5100d018585030740328110001c002e41071101d421042004441000000c1c1141000c0e500c1d0003020710100e00c40c0500c10000803103213010390720984c107954043d501d990038103c2c206029980c080c40305200780c0305c0d4454541c000803c402c8190000d4069441029007005508180c0b99800c1c118001801c20070300941000c5e5406029124041940c808800c01c5411550044441c80071415007546039802940240c01140c022030b1200800c0028004c0341d210b00b0481d802960404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 74364327 1250 74363077 74363089
    0xb030108030c060f100501030b0f0a03080307020111070305120a1b0e01030e0105070e01081816092003070507020402070c091b020706050409020c031306030e10050408030406110d0c050702040506 85
    0xa617040d8000340052801d2115511a6000110180001c3d100c4503486010600185040005030310841380b20b02c0c00802c100260b54203002d141c04d5541903100706401c00071280c1e00070700180169180c92880d020004005218249180c2240d400600403021410218484080040200030000b00c1c01307000ca0300b40001042c110105116480c400c2646a0303861502d81d669800442d00004040c1c0340302407001441207c6208083d0034040140f10020f142c1e00c5050746840c01d2888130941c2c602c8681264034030b0003c0d604024515581c0c0481e81d01000a2400598447c100d1000030001d00451078040c0c070003038056070049400d000d5039002581e213030a05180c2c00424000c00c1c1007240c0d9600d80c1d020318000220213020412043c1c042d030700035004034101c0105a1f130a00380c0c244003080f01c1c004d035540f01c400000c2d2079211052140340284829580310301e2a9001384094601903d40c142648406000140382c00d941e1000c2c25661140d00d402d40740c1f0140040414041102c20382001000d6401050b02030788901d160502151052a00d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 74365577 1250 74364327 74364331
    0xb18071701050d1e06021612170601210906020a0311041206050601050d0c02210a1d010e1305090111070203100c0e030a030804060e031c0c05040b030108030c060f 71
    0x400700c1500c3c020540d6200c1c00c00841e02c03948600031418800e8080024078900180190010508542d41c1e003440a003460100c3c47d0b0807041c401e051201c0e5031546a400382a445040d0b903c04400c2c200b01c4d541090030f203041103812021022910305940391130044e40400030190010f02c0929180d030b5085c4004003400351095103500c030320f204d0040c004074200305140c00141903070070003a0301800506149003001010700025040c2c51680007600016042405c0c81c1010b900f0900b00c00c000c402407030b0030030780c1000003002c4041c000d1a100205400b0442070160803079110f0384170b0030307494646400107484424821a07001c0440c01418050355404a079500b0207481d118442c1060040e2107500b50000c000b00918081c0341c111400400e06c4d2004002000207c210340d1f201500c0400c1860203040c840d03624041170f494241040d108481c5806688201d42c3c00401125001201c0e002c43c00c1001d862100300052a000c0161013543c03240b08940c003070901404080000140380381c001c0b0140604400c101e0a4440d140d9962070000c0f104402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 74366827 1250 74365577 74365579
    0x120709050108040f060212040609060c050301050f0904020301020c0718060608160c0c2d0f0b03390903010c02010902060f0c0304050d0f0201020f060402010c080d0b1807170105 77
    0xc150002d030106950800d405080707400745c4801031420265103040048460b003120191602502c48452400300702080c400d00012180360715103142154107080004078045001315640380b00c0c80340030000c0f605558082d4125041c6d41c60340d004480f1081d90307401104c400441c220030070010031864880001400b60142d100f60740300b012448000ca00c6039000d400190b48981d1014400d807402704002c0004140f03640844c0e22011901a090036001041d5008001c40c04410f515800035184c10200d690b00300002044403042e00c0e00008218018100400a43c040388130030641d1142c1ca01040c40114140404074840d000107003801c4400b81c1c002e0243c0c0703400c00c90581c240c61040740c000350040b04c01c010032103816941d9030140004013200015249082e41e2500000e03e8009881030990711205056081021980c042181d64000007242024015030716040c0c0000c2c0c0310180220004e4201140050303000f100312701c194805280600000c20b0300030200c5000da031030700b40780004842c04808240001c000980d2200c03441c242c14109c440c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 74368077 1250 74366827 74366837
    0x50a09052106010e060a080a0c050108060111160611010b090c090607060f0203160c080901030902010c0f05010504050d05040f0512010605060409320711030d020f1207090501 76
    0x125010510031a800062003046801d002041d20203100181800352600070550030113200340e2401c041c0200444604140e1010015a0200c1100d1001502c00b0030b040086801c01d00301041030341e40386401610088500d80340045580110343c0401000711000c3c00150584102da036405101040340322002c1d08a90000d01000d61040c8030300001113680c0ca4080c0100024003001d8909030800580e560f5a6003524159242c000d44a1740100821440c4001244424000482d41c41c2c07022040d101d0342c507040300b61300c0b88032610b80c1015280c08802d000c0d0b9001c0c3c0c20b2503510f240c0c010481d446000903030800500a2005940458541c00741030f91545c403083c828416503084d180843c0344407007254500010000c8042d4440340e0300d05a5500c402000a056076080040c2c80142404032020400080e0f107040000102401c00b40240e80c206411000261b2240c02d50145600c0b00311820400907014482c403800f0f245020f40320040304114000910b00c580202c40001030022000c0380855401543c8401c101070390900c82e140103050001d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 74369327 1250 74368077 74368079
    0x3031202090d0212011d0703021302070b07050904020f12070306090608070e0901110a090e07090f0306020309121303020301050105060f030c0318030a030e0c0405090607030e0f03030a0e060106050a09 87
    0xc5030103000075020810700c0313000080304000f68040344900d0020040e240c0541c0c00122041041d408e000d50506221000600304525200b10780c1e407402d481d414094802400c1000129001b011605c85070b0403101c40100d400070803a145c0c4905404072000704004c41d4410300181c02c0900c0000e090b1754502403841036841d5a00a46505410143c46081542c0003e10b5592030f0b40d01d458100405020303540007428507071036540e10780c9003541c10000010205440034000c1e01c108501c8003820000c0e180e9050003c4250399001d640075903a515030751400c902d812600c46040140075000540f541c24036880985c15022240309030001e001c035a07a14420426140182040406007a1007080050203012488004590040703001d0704441214904008440c03558001210340000700b40d8520031018010020802d803600740400312000d022900d019a100382e00c501d0007034848c0040c541c5421558800c200180000c0d41d40c00d41c1c030b0040f20b172246040c12903403025002114038140c0601070a0004180140300b4001c5424411460322645002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 74370577 1250 74369327 74369329
    0x3120b03070b090a030c080307030207060e0907030f020702130e010c0804050a03080907030804270b01020d0f031d0a11010c080304020d110405070f030b01170609070c0c03080403031202090d02 84
    0xa5020000c0b11340d0050340341d00003100098400540b0806400058005c50700d4618514010780380000f2600088180860058550500c0d42c802d0001948501c483c1b40c0480d80110060a610180c00381c2c42c0000e50040048505070a048400d03030045000740c82c003138000d0214841d481800d888959080d40e02030140d400081e00e05d0003203401030380b01035080b00003802185c0d030a580d03d41301e141c0c5a40140d04a190b00981c0400b950f0340000301c81e50f00c150301c0c2401440411801c0d060200203951400c1c856695802e001243d8032070385c08180640d1081c3c00c2e900f440c10140b8080403a07074098940740c450401c030840da1543c00303001e094115440740280300d040300d5202e540c1c5c80c0355440f903808010740c0320801181210140c074181009440c5851f58011140101e085450f4403407206003201c0083c1c2601d502444150422100140820001c850241b1807074112000f6a0f52030354944408400720303524899141c0141c080c8542050000411045800400031240070b95550041061902c02880691040c0030310143c0c450103100d001409 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 74371827 1250 74370577 74370599
    0x90504080403020d060902010909060506121005040606020a05060702060f010e090111123103050c01020712050a030506010c0b01091a03010501090902010e060406081803040f090203010303120b0307 86
    0x400d019500c1181440c0d6264000b07011148880300031074001c1c0c0c44144500842d600000714002600c403002c0180811030910300030904ca4010b1041c1202003603801404513550f82d400d29680c0e0043c16000e44103200840c0c5512005e542c42403002c40032520f0348280b400280c0000e10110b48680602c00c2e01010b804a0b918200d820b1072014000341100321079542c2e5180001180c44440010300c0f032503400c103911141c185851041c1400054007960591950007000b540c1044004208403446011649403c00350f0310707821a025514028052810000c04029500b9000c0d04c001350072001420700d020042d41c00384000c1d912030004581e10b0000c1c44e00104135150080050005c0c0c5043c0e040410f08907403810b42202c801000700700207425a5000c1c5d000e03000d1613030346003400c200759688440c00303641d0103106445940ca41494400c0003466039500071b000e04c045c0b10500c20801d00e05442441224010501d103035480413400c0e15000080c00a5200388011004601d1010317549003410503900581d40c072079000401030306220340303405110a2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 74373077 1250 74371827 74371831
    0x20601050d0c0902160b06010309240b12011e0c0c06020c01090c09020a0e01021219050d090309090501050f280503060c0901030b060c190201050f0c0606030120040905 73
    0x1c0c1d2282904010070010b1191025003c00e8507620000e05441c40369003421100701c01b000d4507107410542085010000718203056540350810200d0311010b031381c07200194181c00040801001490380303c2e00f083c0d07041381e0720401500301e01040d01e456103052841a00040300b0070102c0c0c465509850200d08106400c0d00400d18580c050024900440b0010807503034140d40da41c10050885030025030341a6408202c3d040350944c01400c0c00f01440080c0014002e80224034891400782c00303480302440010311122441040c080c40f40064400810480f001400310142d18507021303140444078080c000074140742c0b000024841c50818010303000210060040d5510300c0d80c0780c80121044400052004c0d900503d041c00244039202044000d21841e10741c900d1646490b00741c0001419165803a40d2144030b840c05201c40708241402042644801040300c519000c501540c1c8010794880c058007015140751500890500b03049440805c98501c2100f08038020008402019031150007400351101d81600d01e071003440148803030a0254080340d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 74374327 1250 74373077 74373083
    0x601080115031512030903030206010602070f05060f041208040e130201050a0f090f030308150f03070e150a03031e051801050c0f01061203110607050306040b010c05010c0e0310020a020601050d 84
    0x82c030850303200c92445407102d440031300480000e01c2c4603008005050b4140446030250030346101034040c0740c0c0b4044911058980b240a143c3c410350000500e004850001001c40c0d0003030500f100c900720482c5050038407410076001407054260744200c220006060204450249042603030584915007002480041160907016113070301d02051000c0d16002140620f070607844000110f200350380c0d0200a150480b024280960400746150140c0c44044486a1581d004034030311341554903284581c03000d983d8480d800c5d242e0602d00e8544d150802c1144401105040c0c1c051400b0700c4014600c60700c00c0d02403102a2089038a841031450303940c0400403058003020690322443c028460b11800c0ea0454004180515985003110007a170301040120382240400700c02c2580010b100150880150081c0080389801074000d0414400142228401c1b6681c041c0250181c0c05036250507100364119000300100f40721301c0d40c068075400c1055080d43c03003031103104074805034420305008640d49001103a016150a920b81310034032070b2000c6554012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 74375577 1250 74374327 74374361
    0x30705010f052a0d03060b030601050f0c0a0204020d1b0e01020717100c020708060c070506070804021207080d1407020d0b09071703091003090f021509091608060108011503 75
    0x10f01001600742c1181c1c4490f000f101c0901301c2050700d01d80c00b408031030341039000048824090080200586e0010140e444005010340c81a0307a400c182140785060802c0103400170350052020ae1104550b03440d560260b0b03107611a1000381c11090750100070a4404002204819006901075503051101c00b80c1c010180b102400700c54101c40020038009081070550340f800900c080103902110f0108500d2100300600b680200707804916519020f0b082c0c03138150300c3d608000e1646040c4000707a00032500315101c10742c004070990054425226420b440b45141c40d103862400171000000303591010825510440700302101c0404d03600030080c0103110b07260b65500302802c50052030055940035115001655000a1040005020b103000c003659894003030404100200085650303041c101440e01000000180ca855803030390116030102c9001e1200f00302040c0e00880c0f03120341411381d500705480806100e8600102c15040e10300502e191105d04403076036140b004550340c5400344101000003604030012203804c1d010740e004041c115140c00311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 74376827 1250 74375577 74375617
    0x5040f111201020d0b040b220c1101150302030d090e0406050408070c080601051503070f030b1201021201090b031603120c02150d0609020301080703140a0203011104090506030705010f05 81
    0x30039400ca03002544c03400d285680b200341d00c01462400b88900c01c0c07114030441e1400e070842000905908814941e03480c0d031400654031808040280d01481c80c000700c0c40000e500074000d028911a94503030000440c482240280308148805040c0c1d0300072080d03003050ba120b80402048660381c41d19000d0141c18040c0c0261480f80003045610082031081c940301018158180c01014154940014800000903101c03c41a4a00d01401840101640201048141d10032460041483c20320100014400312000c0120740e440d61000440c83c14849418071014100c41068108125080c00c000516458811802d42405001910304c014400600310f04051742c81111130380b8000105400a5000c544400d070300106005030030344041580752406405006000c0603002030b880270f5003503524164004e541ca03841070100501c06140006074180d0030300d00700140404590014005d00c0500015094007106911078010b01c2015818580001c80c40e003000a8075004440381a074480d03000030003039203040302c05030000322030205940c00c2140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 74378077 1250 74376827 74376859
    0x19172e0e0c041403010510050f0310020d1d07080303190912090e06010e0a18140f011d090307030516050109030f030f0912180f08030a0806030105040f11 67
    0x124148122608207841ea955801e00c805a20807940c01d101c0c0b58400da040000700102011425406000c403a001d580070640c1c100c10200003420800c08001d200446480414101d443c1800d03604000700301d812a0101e0b51030512611030031a111005030044000701ea1040005c1001d100702e1030f021440713030080708500103182c2403603603504a06082040c2d4080c0020340560b009000100346882c07235030b42240003420140f42004c0300c80c0c0070504412142c4203800312560320121400d129985d5422500725422503c0d020703111841c1c1010500341e44842809001044003801c01c1c1361812950608045010716440c0c80110b00303110095904864030791001e510804219565143c1d103000900034024004c0c00e80c400d03160010220703031004000b03003140c4c55610a041490b00704560000413501c0b24000c1c00c803201b031070b1900303066000319070200e210241c25560014001d40101c1030001842d00d004400340a615615656850707242c1c035035038101800d8841c16600a00202500340548001400415241082e0a07001c4d000314440c000e140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 74379327 1250 74378077 74378099
    0x4050907080702030c24060405090a081605070f030302060c0f0306210a060b0108060f0d0212010b0307060809070e01150c0201180b0309010b03060c0703030b031219172e 74
    0x1034604540503269082d41146c006010b2a40b15406860800c070030324040340e5199590140749070103030280d0000603d01c1c0c4000003c014140609800c078013111070301343c0e498440890946142c03100b500107024030404035402142c210b0444ea840102460080d085449403010801c4100c222001a02456696400550106014040e07860040c0c01400001501d400f1040050490040180b00724071400458001151581d07501d07042000081c4c0641e40071101070001a4214014003d20701d09a03414810704400180c0d03d0b0348841c035184614048015200e04655035070710180440340c203024078144803416030309181506114041e0f0048144c0140740001c90201a1203c21400f201c050f044944034a2001040241d490024007076140300d00c00c141c0042682c1c0c50b095900c560540540900201050f46a4034050303803554080107841c0000d078481019681d85d0408000c040e09191810000c14040342285903200c2c45403002e4544544107052241d059840c1110801c01105061101030306e4000d50b10002801140b044050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 74380577 1250 74379327 74379343
    0x4200f090106050a02070603020408072102030109050d0215040b01062105270604020603040308040c0503060a021b0606030d140409150f08030a1b030e0d1b05010504050907080702030c 80
    0x80c3c860503a2002c0055000b4104805500000e05041c010402004010780c00614501202e03820304d110344104c030406107140401504414003961540c2080040c40a1140104100e4415812034085505120781643c400c06070010481c1c0140c2003907280401000300c103014039002907184114003141492440a030720f1501c1207480695158009a20003444c19a07080003100c0202043d0b4440d90081c070701403030300ea40014001c2c8001400101000704600100b004c001e04902d141000d08001000e6134010b143c0804e061000b504030450305010b0202e0f45e1101354072400c0101e403650080c403000d000703440c01501a9038141c4030000d45110a0030340500402c00080c080003548111240e07160002116180e051a009140750201003a8208450a40081041e0211940c100450046c1500b820f01003481d1032905080584038400300b905040d070003050082c0558104100f006110103d02541106111001d446500440300340c0035500070160032010080119291901a15032540c0c020501c0c03040328a082c1c11000c20604000d41c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 74381827 1250 74380577 74380589
    0xa050c04030624060e0111030c190305070c0e041709010801090b030a06060f0503010e150103060c12050f061f120203090106080703050f19032007050a0315050106020604200f0901 78
    0x781c0c3d1445c6502c0e44c0c1c0180b1031044043c0703950086044c81d248006054032034400c8000304100c904070750031540c02c2501450035034500940006040001c0b40d078548000201c070b00d049a00300c1e4505104c40400c3d60216410050310602203060359000041e0b802c1206800003807070300148490381032240e941540c0c0041c40600a24001d40b07020364a14481c0340c601400d03d801d54414803101071098004842030312031800049a41c50460360000c0c004601448051002e88400220014000005007000f08000c00c0d07004410001d4058130003652040d9000494000d0442d65030601150507000070301700c1c036906400140c42c0d00a0361700541c285000045140e170b20040c1030b15112090740120350030b40180c410f10381420818400040b009100d00e025009030035076aa0020501035220240a181182080305481d00b00010860500079010107425200e10f01e84030704140c0c0c008aa81d411181d9124280f20002c125948081a40d9001e00d034000b060006250102e00081100700c241a04a90031041e80007104c0d00640d0368240003030090503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 74383077 1250 74381827 74381837
    0xc0b0a140c1c050612011a09090304030f0b040317070c020f0301060b070609080c0304080619051303110705041805010e0c0f1203090603070309020306060a06080115020109020d0503040e0a050c0403062406 89
    0x7d0548280312085200a1a205464000b480100085801c4040c06042194040103104190b40c5915055490000a040c0180c40d25070303990401400c5a0403c40f45410180216003160604404508160a0b10010700907050080c0c405c4c40070301c00280158205c3ca00700380c03141e0340340d900b440c0035103808601e1500710b94045121030380180c0520481d010880510340d4228107482051125160805c82c1d6602e80c802040010100f000b00030074100110401c0c411507003d0701c0e00038018480c5c01110b10281284003444202944d6075403801d41b41c075841e1100094850b400c1680600302280c460701350030401c0f0307803903800c03002c1c01140d80003c00640c030544d074500b00214807c041d0342e280000d50045500526280440051000d070090394501c200303000f0103400403e00c904494035412051a500c10410040340541081c0d0002500845164048800c0200200103003044d100400f074200095640c101242054450548008050306810030091020803030942129014010b4500c080c051114114500ca10240099102d640058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 74384327 1250 74383077 74383121
    0x40803010509090a0507030f1a0f06010f030b0a0506090a1d04120201020c06180705060310060807140901080c09090420100806040c0c0b0a140c1c05061201 68
    0x80b420300c0107540c000000b0402014441c8413a44c07a160303503200307034003026000c4411402130700101700000110080c100c02d03445802e1708900f805036000070480001e548007400319800408405c20715100703108554600300001c2240100c2d510308014050b02e40d21400b0140c1e000b500c0008003107000800389034030400001454900c0701ca1860241420080301170301c290000116401013104801c01000000c9007500035400c1c03514002c0e0358800c05040780c0703080b0250303100580001303000c13042112011448261908540c843d407aa10b406685000c803c5504448481c8540600341d400d00581c60194862200641d120956800c22440c081d0b1540c0028a544400c4804803508241c0701510782625104010300f400c142011342e8103a03113a044409019101c118028040d078003039a581c000e48001c035842581040708140c0c01188034040c03401c1070245103014080200c010b81c2400103000101e450403d001c0e003207034541c00001c140020340d50007030142500a0580178000b694003003c90714200610794028801c0c088007841402c0c0c00c0c5881 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 74385577 1250 74384327 74384329
    0xf06150e04061103060f040e07150e0a0e160503072f0c01090b0d09080d0207030c0303060503070e0a020306031c0201020a0801050d1101050706020f0417100c020d0c0302150408030105 80
    0xf0710b44498410001c004140107005181d120f0108542134001c0c01c40c1c0c0030410140b80e000b41d03850000f02da0311078030282202c021300082068110004015010381070b10b03d03070b03000e0340c981018240c90081507071000c1c1c0301d20707050707200c10b0780e8520460103150803000f1864010b04180e440310600303001b482d400da000c0e100b064084c180812440303000c0043c090040820b08001d504a8940451544603007d15840d8a00c525260007802040000c420125001c00030507034021504c800036800d000301085030010084010038600070001c11a441c0c0062000110b40d840310781551207941b20000300002e504060f15150709480303800428018038941d0720654054070310365800183c50780d5160100802514040c0d000b06d0240b54402d821101090b00c40c090702030740f80b0080c00c0460740c6031340500c0c00200034424580003820780711001c02c2c00304a00d0064150303070354000494000c0b0761419545940300c0381100e014008840150784050195102103003d0002d07445014000c0c0199880c0e0b10071500ba80b0b180070300448003128091800001031104d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 74386827 1250 74385577 74385581
    0xb04061205010b160305091305010e01060503010e040f1406010603020a090e010b0d0c020a1a060108010801050f04140f120c06130f030302090406080d09030b0c0a020601030f06150e0406 81
    0x140c84000c42080c401949030801107025403243c40c600b50826403040ca0700b0002d00d4020400c481c41114060884401c4014101403100202000c0c000d22a01071400000000c036648035800707490588418411015603506d6640c1e42055503000700d40101c907086010308488818803002d111040c02894a6100540d9500c4103140040c20170200b0303003204d60913001244c0140700015070340096135000321280d800014440728a00e01a8549054045c0040c9003804407094545044411440720b0300880302071b01c5029003a601d51000e64203845e021240c014139940180c00140110f403440c03a07600c568000c25016030340c45d074000c4034540d418000c480c031500480307a44c005080d20010780c082000f650320599900081022036001c1c3e45440038801e0312a009010150045480902a5103a620030002045043d0031140c40c0e280509020f40f100f44144415102209600002006842014221079980d001030303001d000c02d40e0940e501c00a83d089516415640d0540e91201100c21140c2c81041d040500a150700f800c020b40361610708101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 74388077 1250 74386827 74386847
    0x100501030903170408041203050406080f04111009181a0d080d02180d050c0102010606030204050f04180c06021506010512130f1e1b08060414160b0406 66
    0x1041514040301500440e90200d0079841d00b01d400140d4000f50303103460426180741c0c0504c1d0043c25040c400308420604140c0c205008108035903032a1502c015560b102032015610500480740031344880c4ca0061030b42e072246004004d00c0d071800d15608140000586452444260340c81040d480d403140c0b588d0b9400f00702155002106d0038a641d9045450903200d0080c0e550b1248603004012010f03a00c107402189124040455004001c0700c18000340a260301d031462400d11070f66076245440c0e158003651070031401151240c428001c4400340c800161240c1c200c3c1a0300b0b018000103000325900e205026910780c0d058000108100d41010081c06158000d22840540882d08500b50300b015003040e0600608109640180d12a0014503070f1005090001030b03812881c17400c2c8800d90250403100108403280c0841311214500000c410139400c54040c502407684032100796440440105a0300821f840c1c1da2005000070006521000c00070010344400c010b48000d880394503011200200c1641049041c2000850184059980551008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 74389327 1250 74388077 74388079
    0x2030306011d2b0c080f0c090403110303040803040b0f0606090111072102010207080a03090927030503070323041e080d020405010f020c0a170f060c040501090509090c0f0a120302061005 81
    0x380c90040300c184a540d801c00500706a0103240c8c0d420015082c14021800c03220b510120b001900d41d07a140502d060417141c0d01c121780413114003c80501044040c120941524404d000c0038103d40c0ca000484030064036017007894044054175100c5e034580810340983e851407808000d00b04407220812a002e40c400a800e00c0d4094001071707050b038001c1e512940400d500c00c1c175081c100c4030745140006a036280342d248a10f00050407601125100d801105001c1055400401103114054a079801c1148044400110348140c0c6030b61500f124a401320400300303011441034540f01d411141d03042c200603d02d6015554100f56500404000714046a002c02c04004c40d5800810b4600f000d04148007a02c418403900001544d010818002d014419040c012190700c42038003000045411a0548212241c40c038294540003001d1340305004990000722800740024071801d04492aa0080c100782d8060301e44820084107110007103003903004441d441083d4600000c0c400f000c101034002d626000e40e0190000340380480542020550700d50060f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 74390577 1250 74389327 74389333
    0x1e0705070302180c0d0b0103020904020c1501050d030206041106090d05010501030507060c0b130201020102090a2301031b08070207030807030e0120150a0207170a03060602030306011d2b0c08 83
    0x240184d1000e007150408174804c00d000a0b0a04044012402030042c2c0b010981c10610000703640c0001c000020304002c104c940032015000b1a0381b41c1040c0209404201030040140c0d2200c000315001038080c450040b015030010385001d00340b000d0708001524514440d4000d40b80d0340d54070001841881408d015400140030b490030400121a83c0b41d4404007001001084034040b20b8940303d4440c1168801e404469820b00002c04621f6001c3c0c9070301c01546048000b00704410158208140104d01c1c0d4068040c120080e0b014034001030051170240815a03802d4001441e0070118041c0c6034020000448500182c64480d0007503a0b01e00e00242d909001514501300300410b20949101c050404080580c0028920000300c200901d804590b1104240c00001e40a0588014840142d1241005456881d0701c00b9180e0f40141e541e0511035170341d940405984922056404500003403980750101c502001802c0464070020010b0125410172100c043c51041100000c807402c4070f40d040b824400801e00004808038400340001d4406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 74391827 1250 74390577 74390581
    0x8130f0b0a030b01090b0309030c1c080714040503010906020d0e21070311010609090213020403020117130b01060f020d020102040b04062001050c19170604021e070507030218 76
    0x3084164000c0452800825495803c20200c50348603004401c0208030b6090382e5502c0e410103250071612034000c1824182c0520420707101000954603800c81d206980950786491901d51101401140d40d01d04001d40800078903810000044c2940702440b902c001540644c20051711108504030300401c1e1f4244820080300f0358064420540d81d03c41000744540b00301d00e0004426030341d401da80b80a64213040c0b0040700907003d5103450b030005070b1b0352496000002d84510031240007041e2061151000300b203014900010f170000740c0040070402c91300351030000903070081040301d2000c205540550b541c1c44c1d5440241c201000040d840030011241d5501045080a496100c3c0001d40c240f42c28000c044a480c01036204407010840030f000d40e2204984500c03d421541010750b0000d03c050f00c1c055441d80500c1e1700151000e509000401640b56459210b495042d50100c1800c0a10303d054542d401000301030b40040c12290040f1a0041442e0b80c4411480010580148124041c045051940c01003188985400640011340045d0900f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 74393077 1250 74391827 74391839
    0x2c04020a0215070c0c060804200103060b040f030b060105030f060402070807020d050d0e041e090813090504031404030b04030309030207091d011401060207061206050405011205010605011b081e0708130f 88
    0x49c0e00440a400e040b09400c22003202801200076000d164410702d10340c0000a070100f440011606c0c00f00940380201e00c0229161a00001101c4520084402e003d01000301804103401d480c20340c004000c2078ac06581142d04003200b50300003030807000000e0001c46513940302100087d00d85410106204800108583c03c0212032010040002c81c107504401600c004c039500c1144004101c00310003612040012545580151130f02d0700540f40003040c00350b03403d07004034824805800a005240086a00350b941c00f50f00c0403400d480341d5030140d015028482d421000d5004104010610031040e208960400c0515508040c8103064400f980d800c40300443d0080503242000e400500c2815000646142150000e207000e02c0003600b80f101440041400e074004a83c00307414000000b030340145000005082c680581e00800805940307200640d80f2441e02c8103a40c1d80c00b046c1e00d0b01d6002007210702020f010f030b0300d0725036041c9400200342c01682106c0c1e91184c0d40495034040007080c0c140c86040d0300c103060800b41100d01c1c140c44000381000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 74394327 1250 74393077 74393093
    0x6080d02011b0f08130c0b040e010b0403080906070c08030f18060903070501080c04150e040e0a0203102307020114010f0509010e0405010e07152c04020a0215070c0c060804 75
    0x2070f903031420b100d40403011076608140c0c043c0100071070f41c01c0111401d1568445030b0b450020740c018411041c03158020400440c002c100c003004c5170b044a5114903442c3c41c00480c0300c14401e50350000321040e200b2004c0c102c400140070354140018014861040035550381e07203000000d41c030b402058020406018400920025180b42c40c00141c03801600c0d002d01301a4144c0c0e070380750b02c20b82c0f81d803213141c000346904000500000c6450f50420070000d402c844c220f50501a40700c1900405607101709030980070354150f104003a44d2a0001403a84200d42000c91035402207070b5003912981102c282c88050b9800d80050f0b640c1c45000059103540a041405000150201b0341c029280000040c581031381801040e511391000300208042010035403111000083d05010741744641d0369000317a18038405050100d003002c40c00002403c9107801d8050303940c91840d9803403124400c804039110188802900420107100950cc03072040840c5210070301407101442181241e43d6401c024007180703032158070b0320410350040c1c0a11094409000004840b8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 74395577 1250 74394327 74394347
    0x30601030e030c010e011a0103090309050609130e151303020c010302090f040515011409010801120204090b0406050a0b0405090a020d0606120b01080d050c0709020a03090606080d02011b 81
    0x92a01241c4807a00e016040c0c254881c03211034500540c60a1014548200190040c088041c20440c1c90b0b0343c10312148006405641103040000c0c0081c110000034411850044040c0090f00d1009c0c0c40c1001d48422a1030030802c03101480b0a40009500401c84680b4043c14420711642c42400c03d0140102c0803441d03074020390f58030701701c20b4004e041c142c000c83c01c9103860712100b40184005500030801d04c510305205411981400d19010001d0004440c1da800c070728211840400c6030303200303030701070b580c00c1d0442c0e01e01001c60001c0d81c188202241d0180c0c0f2094040d003c0f6140f0340c400e40c00b560140800013040e05150103190210307a0302400f0540140e007000d080080c005004140c0313034412901070343d003030000c030b074003072904400502e100e0b0006c04c54459500d00e54003d1182d428841416a00ea007401c581800000080584060003a540c01004992041c03e0030300c010036154000d45203400441c103010410301ca4940e503960550701c007a00000b025601a040e1624480e509000b503903410713401341c4c401c0900703043d03a084010015450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 74396827 1250 74395577 74395579
    0x8030708040e061311090f040506030a0311030d05070503010906050108070804061802030f030c0c04090f0f0816060b010206060103050411100c060527060603101e09050705010210090203030306 84
    0x20382c0051410340380d900142c0800c0101c18000c0119152403150038180d5088181c8842c02404841e01c44034050a2500c2040c0c040c050003801820b41c1c0c40d6680c1e0469200d1040e160031041d500050050340840103480c0202401800c850301c40c0342d200d40c102800d02003126807952106041111680c1440a042d0f002a40107400940242c00840e00022004c0605804081060001d42521072a0642c01882c0b0010001c0c154890844040c0d562403a9660204000e8545086028011164140d40d00c00040c0c909640c042031140300304a514281070a4204c0380c0c14521b031045c1d0588025461301e0a4101c29139051041036030040c02400c1c00c21150a00341c84881400d12048480c030b00a01c44d122903161924000c1440c0c000107076100b401403041d443c20100034a10100148178582c440c01c0d0402c540c40c1e00403c0414002e01c21440603000740f10a501c6a01c200d000341046202d401084000c5c83c40206000c9c02c14013440044074051402800d2542c50078000a01e440c0d0201800c007000ca00d81240030b00103940110440e0f410400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 74398077 1250 74396827 74396849
    0x12303061513060221090f0103051008060f0403080906070905060901090b0d1b021207030f030605060c011b02011802040c2001061802030601020312040302071502160803070804 77
    0xa18000788007840c0c440c184a4100e00c2c00440400507001d0760004107148044078800b00c0140903861103c0910050140010345a40590b0411540304039506c42d61120ba40810b802010081c542d0b590f0210a040aa0071f480341d483e010000410003080c141c018002c0354001881400820075454040001801e0303040500666100312000928034100742e219201c5840a060240711050340d070f00f0b5104100d0000c0901030707c2091210301040c502880a4000300342c0390909015002c5003441c0c040160b50440710b21006030044e0083c1580d8000105240d02c940020304000030b022000090003a041142807202115240000c00440e81080b2801c80345004410b1808007480e0b0564000c9200580000c05a4443c11071000c10b921410a0303170408174260300150401801c90b400640c0e19003c403450065488141e1000321000b9000d03034400c01103d1505030b1903248095100d0b0003481a51a000d031104a4a11400380f40419840181c0c04090070f105c040b00806241d100900b0014011413400749035a5488801c1c0c0200e202e9400c03150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 74399327 1250 74398077 74398099
    0x3081503071a03040c050102070510030e07030606060c0c0806070c020108041104020c1f05010308041e081006170303040c030308130204060b031f18020d1b03090201230306 75
    0x14404010741d00103070a50980c000e01d06400e00c500d003440d5030001c84003500c00c001030b10000074507940080386520554602a240465640703509406034044c10401e101902e440c404c484002012600c00c2c030484001d050141d5400d03039104054240b100c110406a0410036043c0c00000078040980e070040b202c449074950a08004520b9a15801e1501c0c5110b0b00c0c0c9c210703d80160000504031451800422540b1841030500c079002540c01c002c82004085610901004101203c01c110070b020920b04c05003801003400b00760000c040216140d50380c0508140d02d014500102c40d483d84400d110300030724941052520312103800214190301d03064803503603400481484040c040c40082d0b0082240762013211035542807030ba0050000e1100950324024100d07a507108486000c110140f8010007540140004130100c1140c000c500b40c0460100c8401520000354040c0c5d01d070705040c2c0e64513a1640080301c441d01030a9840d0095413000120801140005020021440d00744500c0951002d51045880a0241500e40000c0c06841a410300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 74400577 1250 74399327 74399329
    0x614120717010b18010806011401050a110c181806090d110f0a05060f01050102030a091401051204050105010f12080a0c0804051206091213151713030305060a03030815 73
    0x14070350302030900c1d00542030024942110001315840742c103c2c1d50b400304540d000d0f0f0b03039003130541d0312521035010007030014070104030826950344610b41c1c20350b04646000643d0003410340c5070001040070710002c52115a44880d042040000018483d50251a4480f200a0103640c81c090696a890305805030200090000148945240c1a000c11208042c2c0500300c0c12a0710840d21801c0196565000721105070300000c0420001c10700d5440072064401800d455101c1640490820a4080003640441880c904100d420b00420003d18040c000c400e0203240140000030307595061a00703c155248a0741c101d083c48080d01c3c43c0e16000696040701b240d5484946140c40c1e070304072400b440e0402c0148aa6406258403510b038042030400c6103404240c442c02440d141d01107505c803c2a10020300a14000c503156030300f90011200782040072000791502400411a42d24180c421039010700700d4001224401c0e80c24800c050466442c80d0308041d00344c4240e68000104464041c001c601c0c41d80c000700020401400c4031219240c0d04224070342 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 74401827 1250 74400577 74400581
    0x702061e1213050c010f050d050c090d0312050c07080d050406060306020c0105071e050403030513030204020a0c030905060304150e0f1e0c0a0b120c090402070303061412071701 77
    0x100c150316481c034079080c241410704000705818400160390074090010350110544c060072651102100c541c0303c1c0c90030400319550000040c10000c044404c3e2000800c130000550796505101c0100b01c1c0700e80c584100d00d11a281c0310300101d500013040701c3c141900c04c01903c40444e80310b00590b81c0d800113615010035076aa49103054000703880e6581c8014a014000304050f00c48050640129216801d80d0341e96041850791180d18607a120f51091a03600852020070081c004603114038002c150702e602c0242018a01c690f2a40854202c0e403280121740c00107202e806000701010b500510200c0144000c45e5001d06504042d11166164220740c0c0301d060600c0d540d0003400304400010f2049903940c1c3c080c0c41c281d0f4944a622548000210640000700c44640501404030b0b6807071405c031060406a0391054241401c10060401200d44890b001d13003034540c111f20902c0146661744c5e40c2c0c001004014803070769000c1019450100140710508000070320b10f101c0c04a201c800c500a035000281c4034100e400e280516032a50702c81d1004580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 74403077 1250 74401827 74401837
    0xd0804030f030c020f0a0e130f0c0b070b010b09011e0c0b010801020c0d020a0803010603090206041827050606010f031401030c0608070507120804060f050a0506040b03030702061e 78
    0x200403401c0c0d91464050541001100103030034000e132500c240b00c02a40c41007040800c102c3c05909460064400403c58100c0c0c031550103040c942c480d00c00240c945145890380040442a0381c405015030400003000400c1165806c01d041c01002d10003411405c010b800e800180c903019400c004040703031040e842e00d030706002803280d240c2600e5107800c00401c08072942c5a850860103075204943d807405520408043c1c02d5020b01c00540e00081f1500540046e0441e400d02201310050020020b00344e038840414000030801d800103845d1040e03401d0400300009400070903004041d620f03608041100b002c641c4101024004a000031072030590084092811829624400744190b0080410581603003900900800103c03c0040c082c5001c42511826150403065513140c81d02180c043c451184028503281c1e0580c542002640521800c5412511400010035100019400007007162001c031420350b102512102803000383d0809114403e141e10050b400f41d450b0074500e40106440b4421201c0d40102d092100480701c0030140280c060b90 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 74404327 1250 74403077 74403083
    0x3050a090e150307140a150e060a03050402090105011704030e1906050c120405060f09010e0603090109020a06020f0d05070203010b090c03070305090105040f0212011517120a020c0d080403 82
    0x80840d0400c603900c070b0b0301e1049640405000788518035012500c10600c1031039000c26a002450b800c0d102d030038100c07048035007001c0a03000701c10b1040e00e11200070f05584180c064188543ea9550025041c600303801000140d05060703100505100c4541917200043d00c060110b254001d0701410701d0110b0007482c0c1c0224100764003440d900b010300300902d107012407169070040050001c4103031001101d03120351700d01c4a080d40d44d10851060b0b5070b0000d4100540e0f521a125000a4581400141801300a03400742d00045411035100320f03120581659144484011840d10326000303005026180300611062a07085c00341c40d0350b07254210764101481000b18403a011950250080140c4801c09440c40c0700a05242215080079001075400b0070110303041000003901180305100e041c1c86590002c840c5e041241e0180c0900000e0020000600c856541b100071085408507030300e103840010203020500f601e80310880c010550900150b5121920340010800c220034071aa400550200c10302d404403441c40070840203203010880c921545d0f10003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 74405577 1250 74404327 74404349
    0x1501060f02010b0609011b0305040306020427111b0f0a052a060904180f0804050f010903020a051002030c15190207030804031206081504060606020609030703050a09 72
    0x8202240d000040001041068000b80195055401000f207240210920130f4002520399995040c08030f0005140040e960281c00e109290588070b0f200d20040c0d074031681012048000e60050300140d1120a4205840804828820002c504120460b40040c8c800c60803520a001c0c80407845500d000b0081c0800c00c0da0303c4020084445400c004c3c9405503c2d101065030b8584100003d50465074810381000f4104d240c240001c00181c50a401001000300514031791000d40354840480d403600c0001000302c1c00702e00e005400b94002070f407903900c4c0008020421059000d001e040250300b0f030042005844490383c010a8034401c0350300c0545040309402c00c900c0c1d80101a041d80b42889124004049180348210326401043e5100012007490ba048400109a00c5001030040c00120203500003000b0a10501d1141410f003905140030540352395402d01186084180d00c180229070800740184020005184203c0005064a0000e07010034501100020744030300a148019082c041c0c0021182c61040c0300d4105e52001d4032a0a040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 74406827 1250 74405577 74405579
    0x1170c1b07090c05030103050703030318140c0306150312070501020708040905190c08060f0301150801050118050f0f0603010209150304021513140a030203071814130f02031501 77
    0x540d56a480e1680b107550300203494030031481407140c8034504403070580e43c1000007480c11925580c1c040740100304543e0b503000c0420b502e00030b42d000a6a008051040700c00903000610201001030105404d00401400da00404944040f410216440204014200fa56000c0090341c44034101d0810f1400380c1714105005100e0400010b011451401c90385c8090f00a2405644180c5091808041030044a4140ca80c074004500c40f200060000d140400c5200040302000e4000315800c40000452a40740e551900440d0751179440d10014001c404c2000c03001c00213954121018013490500c140442c400c904098869507104101d600011000d8509404a801212001c0d10041901c6080802ca8403da00300b501c04030310521414009100100001095480d204030400b07400c800f03185170504071381d0102e04825180d80c0051141d10000003594040c0401001840d16068142562082070794150407520114070f454004400c28060014142042d051401026401a842c00111880c0c0c00003134580814024912021031700000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 74408077 1250 74406827 74406877
    0xd050c070302060f0c030105101e030b1e09041205040b2a0a050d05070615060806121204060305041104050c13120f06270807021302030601170c 63
    0x3880e020380030b6400d80b641034980da50783e14110002540c003a8013044060005000750301c1c101e05a81c00e0100542015030107204c3c410440d250840103580c610020a50b6800113240e82d007440b2661070a100030061000044124440000305400000380000d40048002213188041d0303801401182c000d0010740e1185a1200c0c4031031074103845075500e1010315110142d103100c5407d003034800184111010794040c01800c40103460340b0741114507030083d10081d44d115458014a0380140c45402e00c0e0360142200e0390b42c3c2d8079285845000e014400a03540b40c041c020754020080c4810000307801042d542a0781e01d41c680858aa2a24105446091504209182c0c05071403d0144002250304400811483c0041800e40c00013030303030794480c40348900b4001c9006410307070404032210000914254040b8003200f008841c090445191410038088140d980b00742186d100400003203a10170b62400c012441c290041c800c005611310314003500001c200016058850310710403240004180f0803810002619000c40002000d1203441c0d41c5c4030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 74409327 1250 74408077 74408101
    0x60118031b0b030f0105270f040506070c17030406060e0f010f080a020307090f06081e1b1e040f1404021503010b0a052109010504060b030106051012020d05 68
    0x820745500c624022038001148201041524864028801040490385c81c007020f01420b41d851105500280307440104912031288902c3c10139000b101c051002c0c0e03c062070549082c1e8607140c00600403905002d06d084c6140005200052150307510004450740131746a4440345403100190215411442c411a070f80810030990461104801c1d0407116059080301143c0e5031100019101d07408018042c8d016001a601480406001d410038010303140d07070210005207550b44903200d40c00c00031010061b80d554150782004201e00382d42004411181c02502014100c0d090b840000100f851443d540100c070725800e4210000f030141e503190700200210f09070060621012610202d4995201000c5600301d100c0d50052801c0e440031a0003005482c107840d48406854541414400700313980c0c0e1f411003688a240c00c00041071800d16615001c1815000d026010008505410030785010302c15901d1100d5814003c1c8c0c5441002c00c020768442607140440c80c075030704160380d100c2a007400c0b80e40641310f41c40301e072080d840c00e1006001e1844990 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 74410577 1250 74409327 74409353
    0xd0c12081b010c14040b0d02220621050f07110a170a1103040f0302011823030f0a03090501051e03040f2a0302090a0906140108010b01050f1206011803 66
    0x10307a40302c03600c01d40b1385401a0854080c1e40940b168280e8140040e15903018640d004200d03101e852a01501c5014a0091b10a41800c41d6000700c0000742c0040706050341200c1000f16800701c29101c8030240007602e0a0a80991401c400a102e001004502d1440081052003403014500c580d4009132910305001000c492503a0650220146c80c000885185840d6801c0c400401a50182e485001c07401c3e50842c515001116403500d000500e8858540048001482042c803048000d002c0a01103043c40318280008201800e001c00c0208026132900701c4580800001d61200000043c0c83c07007420800d88910400401d0b01c4103024000c1c2252425200009001c14031508400300b16106101d030b41c2c03e120304000d213003d190885000c2020f6240e0b0141c418028401440d0188016600503400a0000380c50120398482d0001c5d140680804a4561a03850051143c103a0a002e4001500403c0c20018940240c40b12013a0861080014445440c2e801002241050307108001650313100030013804120a0b581c49041c44109210741d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 74411827 1250 74410577 74410601
    0xf0a06020106080d050301031a1e040506070801120c0504020a0203120c1b070b0a0f110d0305090c0102030c030702040902030106050901090c03050a060b0a080402060912070e060d0c12081b01 83
    0x8080c40504c40920600c102da0503258010141c160510a003240d060445030064000841c240342c99280c14009503d581d0703450321850148004104c01d00f46580e000d440c407441a00807a071200300f0102c0e428049070303541070301034111242901c0050f6500c3c04442d00b00e055004000c07421804620010901612250440c00303440401c000041c105800f44c20039621035034600c0755204809284009002d2003945a0049000c070034004101e040a01a01062206003400e0642c0140b0301c00209940c0c0f41440106141007000c1010740d90203000035840c00449221050f80c038001e09000a110320348075000c80d001c6403003c3d0071820003400c000d0103190643d6117502000002d4400143c0360b000003460607000480b56805401000701300c552101c140c030318003183c1e454101c80c500e00061050703810401c1000401c44540b14151580301404400e0050030325207090070241e0f411908098074a0f403188407146040004580c802001c0c0c07044699001c0c1d00036141c0c3d03491601c180c050280c01c2c0505030010640e901d041c5030b20019004081d01c100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 74413077 1250 74411827 74411833
    0x1101020c03031617150301020403061e0c0305010803090607050106030206070b0901140f060d03140f04170a020105160c050915040509060403080a0c0e03010207060b090106080603030a0e0f0a0602010608 88
    0x1854120744c40e805401c000b499503406400868840b9144d406a2460b9001c080c002616190f01c80e12070b2025559980c510940303004010524040c031030107610442c000685d140c43e052003d545080c4509036039000300d0054a1046200099010400400b50f000030011640a445030751136181038241080040300c00c64110a00d5401d22400f0010394105d600428440c1c48560700310800381c1c540c001803100f6940201011428403e090410440300c66100c400342820484008005607181e0424410000008a003052408968400300340d41c00141c0c1c0110544902c045c0e181c003da2590b040e241082940f0040e0741d8083c5401c0325045040c00260200c0d00044441050155414001512098410391f035611048901400181c229008200c0d6880d958002d100b07003007081d15050b608010410300180c220781c04280111040796840c4004012420060307a50707801480107052a5100e49000b802203038880c4076842c4d080c0100400c04000a407240e45420082048440c00b0309407042e030310380301d0001a00800036400b07290220b00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 74414327 1250 74413077 74413111
    0x20c0108010f05013009110102121201030f1b0b040302100804030c030e0109170607020606060705030406030207060207060504061a10090302041104030827040c0206040f031101020c0303 81
    0x3203070202001c200c0d4010f035204401e80e4007980c592003500e030341100d0550f0701914100405c403c000160142411941c01030b00910a000318190000e407030144c0414415404840c14001441c1e20300c80400e4483c1100c0d008484001400018541106c5502400c41001825a42c031000443d45a1045001e00182c0c2d10030707140d80c1480f000c000400c0e610307018110b40040c001502800b0250019104114488c08040107041c4407950700d4890707401300400311010039440101e80c401010032004d6070381000b02a401410a8072000c1c40d1458984510781c80e446540908800d05800207003d004000c40c59040398062900301c1c0d030400103030405d032400c50041c0802113603030f214526a00740800d00c07914003039041d042104038a4540300845442d550a0002800d10b40c0c8126444c07401c01d10001010903e644010400420b01c0720b800c021000481c203640044884001141d0b0044e40b40095a20707840307400184d2140c001d90005045081c1807140d01d0200c59802c104049011694008a082d1080543c0000558020544004481244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 74415577 1250 74414327 74414339
    0x3030402130e0c0d141e07060f0f0804081b030a020c060301050a050f04020f070510050906060604090e0c190501170c12090a020910051011100c03060e07020c010801 72
    0x3071030290b8071101868000301c0e1000d0341480c040140b160820300c43d2030701c81c000301d4880d0580ba00703180c0004290b89001400001c1141062404d014500142049041402d04198442401000380720440d10401c184448980824144904501a82c668100003200202d00c880c20784400c139103c1d0014107184000d40320301a181303082e41c54080161390607510054802c4c64020b19240c100409081e9001d80c894103c1d6081001c0c2103c0c0066400501d400d83c02200140001200d11290104442009010b055180c02460500806907510811a4115112010b000c1a01d806418809080c03403d207100e000e0703010704400c180400d840c4d1801248021280240c132a5000d506070b120020790080021a00c000924104211201a80d07140c4962190402000e4044924218503680403c41c5200181d420101003c200007040000c0e1a2080020f141c0314481d19010107840f0680c48541d90b690010b00c14a07001c16120344049002d54840c0e48004000c11040032040c10305e05045401945520050300301c1400103503003000120320 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 74416827 1250 74415577 74415581
    0x1f210c050c1605090a0c11250603050402010f0518030607030c020706020304030f140a0c1d0a14150f0a03061a100206060d060b030303090c031c0c0b070c050303090303040213 76
    0x103c810261048001d42d4543c20325100926101c681d440c00c1c003da0303012030400248200039060380504150040800c428602103c0092100194810f00405041c2820032005076440a0400b0254a450503d83c1d22a101003003100c0311014690600f54262084200b0032114542c15040030207140030743e40a03246d20640381c0404a890b446180005402d03890414403c070002600d201c40c00040d0303600038060381c0581e41c0c503a950010481e01c5500801c56101e03180701a00040000e42c0c03850b90082d41d443c030208a5200c1d0b82c00000d00c45240201032010303070b0002c02d55074001d40e20394003034407484100003e102c00101522841c2c1070000b0b100075500e000681041c018200818200300c82588240402e5400422031135951008100c44040d40350300c11240c082d02c4030500180f03034500300041c50080d46888050a000e81c0d102041c50b15200603140107601c0000010301c280e07034640d0081951040580c111540c2211a40c0740350058440509564004181d44400800c00581341c2000c0b0295016038422075403024607900c92810102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 74418077 1250 74416827 74416829
    0x314070c0804121a0901150e071e052101090b0607020108160903020604030501090b280203060f1c030e03030a080601030216080d0902010e1f210c050c16 67
    0xc03007288200018000703a4244807a408405104510401c40c0580344074581c11046000d9400c1892691181102e520008408070141d000e04072144c00c164082c42e00b60b07001808880051000111940303140312001c41d00d0b11036000c4400305c1003c5902c4194503850002c1c6440300d9a024404c850485d45810040e00d100c0c5084811900d00c1034050396811513a403502c2078074061503c1c0d65003c5000340040c11200000503140c41014000071800750000046504a0b81040041c043d0000d2685115049540c8203008012820100d90701d000054400140c4950350280821001404103800355400041e092160808240d60307030303181074854465a2400d80108244c028507a0b01e01030100c0c0d010200301f0010024245510036401f070040104101241c180600058403a031240741d01542000034200e8a0f40881d5066582220b1200607448095461500c44040005070924142402c110003042101d558024000d800460500b400c0d8955402c00400c480d00c0500f40103005a4005410841c3d0360051601e50030548684604a41c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 74419327 1250 74418077 74418083
    0x161403120f0f13030506010f06080a0b0a0b0906070615080d050702030705090601050702100504090e0f101503050615010f0810030305030a1401180b100203180a0e070314070c 76
    0x282050104a01046150004010f04000402400b40080800c404100c0b0314002c1203e400090a15414007400401c0703104002c0600022505001d00347c00240c9507824018129000c0b81030007a202c40c85c110001d0018170402030042c2035182081e501c9140b2003114281d85045a00040464000704020101541c083c0203000380650702d034001d0f4034100064141000d441d5802003052400b80d18186490340001d141400164412000541c0481c042c0020f40d87c0784a030308a416010001070000e40b14001440343d880e064141d504600c41c1d06c42241c08101540d02449501441e846801d1b15200e10300384030350b035480602c48a0b801d400038074041605807070710b40102c20580c0142608005850300a086403001e94080d48040d064603082945d07504407031510280d403002c09010f80340e40c114440f80080724104502c01e580c1c0300d10f46644650405100008403607000021150f4021070040120b80782039000e0300054858a180c0d0150803103180203c03c03c01000d81c1a800321880c404c10080c440041e86500d4012500803038598001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 74420577 1250 74419327 74419357
    0xc1b1e070e06090a0216030306081603020a15090f0608060312040503030702010f0509030f0c03060702011103071209080705030d1b140304020604030c030b0103050d030b0105160516140312 82
    0x102d00349041080203244d1004084202600c6c2c0b0820906400c054502014181c0009036074601c1400b14140078405080e01011315400c0316209429600050400a050b00c034907a05034418032103165a080c06202c18000074242c041e80005070b60303603864001d04081800c807070f03942c800d0280c500110a4a0704010540d8103860010300110300f4003041ea801907075441d407481580014448140305d800103e58003009401c00007600000603248500000040c07614000c0c010b8640020340e4180100c00408850344401d483e8400400e00d010703c116802940310b880184070a1502901d94140054000140302c000002080d00c0f852a03002001302501c481200000340380360141513000507428106c000f000b070340d40601030f54100340000c1440d454030381d5a90b0348441000890b0b2044594018810040051000070320460115104a050501098040000080103032140344410021100c91400220034000c0821540030305001001d01c0d0300350b90341c0305c400351a11495401c1610784a03100e610400e92600ca06c00f02a18040c103030b4503011b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 74421827 1250 74420577 74420581
    0x5150a020a0e0118091514030303040203030720130c08100311040c030b040c091701020315090a0f0f3c050402031c0e0f010f0905090c1b1e070e 63
    0x1190002034454402e001c48280d100080b503148118821080c4802c0d40006d007504031803801d8040c15007140c0c1004039611980060041002589000c02210450b07644201584000443c0c5040f000011541210383c507002001071184100c0c2c0b2060754010707134a542168540450075511000da0244003489400010211903e03406a41100c0c2000c0d0800010b032095030030702160300b540107408641112540d1710761500242640b002041340d100400d1000c02d04655000080d4903506e44031480641c1900341140c054083c050020001d0b29400b0b0990020718030a03000031040c007054601c40400c0001d0150b0448a1003881e840902d0b41c0701c80040d106001c0003503845200b5288001c1d1040040300000d003001402a0703014050000b44407a001c00920500310042d505444040002d2168014090701c90300c0d21840710305110346a1200d520751500280c081048850442c0e0702d92103a80e8000b5070612034002c0c11080003e02e01c00e403d0403590140080750307102c1504801c030314200d0030968425200c0e075101c40320700c81c1c0f407034200744900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 74423077 1250 74421827 74421829
    0x21050a0e120d080903040803070c03260304030e060c03030901060609060302120c0708040506040e1005040204050303030a1505040e070e0703110d020a030b0901030812010605030c0f0c01150305150a020a0e 89
    0x80c1042d804442c104c10fa904040d070382e8003118150703072084004642042c0300c082c0038020000c1c40e4100250010210030000708501c940c1103600c005110150019090245048114885a4072038003219003844040d0280c0703490303007070003d00d07140a800c40d0701a00f0040341e039409000c90f02504c00d00c00d80b044503d90b044400860b4440400882c0d295020407030603942101c0400c804242030b2220030060000701200c5a41c1e485502e4442c414103110311071b50300310a100d00d004000420103507030000142c98200c000c89000291514ad42e0540119422055008035001420b152940c48100e00204e61031040310744202e94207603103a442c40c0c4101c04540d440c11038554114824410218022030550145c41288040d00340010796400c00d60004078100300c01d0380203d454820004180f41144401c0040900500c980d0610509505196070300e0006409016100034410301d02065100c0421025040340b140400c04550b810391540c0c6a0801944a011600315034858a500e0004200081440d108070741e100c1c1c416545007111002007070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 74424327 1250 74423077 74423087
    0xc01050a030b0a030204020403140c0f010806060a030608070602010603021314010e040606030804120525090e120d0203070207231e03060115090609050906040921050a0e120d 76
    0x20a10350401d4002d40f0200042c0c403940b0003000a10b014201c00c50b1001400035141d46007110220f40940545841c01d0240d90b81d0b60008007507500a50220340b8140c41c0d60303000c60110001d0100e0390050307003640318003140080d4858041d44800260b03030099400e40b56402c01d00314a501030b200c40304400310780c605860f801004240103a0039000d4119100307a0002c90515900c1e11251070640146c3c0200342c24080c02451002042810411010301c80c40c201c2d0703940010b65041d03100c3c1031100b0581c40340b001204c1c1c80300c1902c60481c05c24040c0324030400c80c0e841c1c40381c1c5596490041c0340013900121803030009841403200110ba45c0350078144001d903e40b4065a02d4800c0d0005605000544901c28020300d52006000400e0070b0640c0c061007614080c01841d6154040c07641c0031180244802000d5001c402403044840c0207110b01e80b00c0c81c039960ba101c60b05a501003468076080c604446d241505414170088076135070b10040a4500d501c1002080d14515503500c80815040e80001c001100581900ba05050b81c4803240c10b460b0a4050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 74425577 1250 74424327 74424341
    0x150f0e0d08090d0b0420010807080604050606070c03060b010908030f0d02070c080114040201031a0307050402070201050c420a09110d0302011b020610030b100906180507020c01050a03 80
    0x241520022000c5560341009004040d1404c031283c84805101b1102074402103030410000909103070903407180c104941c0c040c00c008005011140501d4440e000550070762500e0049881080e40050f661046076900e0401c10001c101e15544140015500103001402c80800015a1442110100e070b092414048a060720300950014204a69039080c00f000080e08400a10038184841c030390100da14980d00d454070004049448800140d02c0d200c110910841d81914001000c5040d03900956005a07031f21950300060f11540501c182c90140d500c00c03480350388040300d14480603400711103400140c20034802130000c071072075140e24070280c12481c0d001c0800061030b000c10b260000350300b0078041c1a034040c2001800c4c001c900f241e01c0105003076000d80c0d15001d0180056024001d034680a42852010742a10b003455008200d00d400c86220181414200360041a44600510460802401c80100c00c21100782d4601103004440f0403180d40b402c04500d81170018034600d001040c064540b0805070350382ca24200003d00c080d0014101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 74426827 1250 74425577 74425579
    0xf060302090a0f091406071101020c071712031612020906090105030406090b0114010908010612080f1306030c1107210510050406020309060106050424030213150f0e0d0809 75
    0x1a0700925021035401e001700c200b00e030f5001c0c1c05400315140c680e40241c04c00d040c5034840b90f2aa03104000c0e0f503049100100c3c450099907084d40d500d41a421580c83ea447c50a81200550b0000e02c000106116004082600d0364102c221592035904030b107025808280b0890040e0132006410030340c1003068803030641c4038000845c0e11900c43c600c000b581113003d0b125080c0c84003098105800b826007035104d522140d81c100300c01e08020520307100203000d032508000321414820b482c4c980042060300d0104102d4214001e403810b44450000821040040c0c42da1800000d002e800a0180e1002050500070b9400001402142070030985d40040c1c4030845007061111580900015144280e6807800781412040d265400340c000c0a00a07400303800c3c0035881c0e0910104007401d240c81a8426401e0010800c010081142c0300c604001c4101c1704082d460f040f49207014010740280c85020380c41541c0283c0d11601145005041c0d001c081c0500b500d50390703030728040d205801c00d8940d60038069401e6841241c4125020010720403c00608101034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 74428077 1250 74426827 74426831
    0x30304030905210709020d0e190305160b0702030720010819090c030615060c051504140f10060f03020a03080d020f040e09120a050714070b0c0309040f060302090a0f 72
    0x3100b10142459080e0308145000c0e46c000848800c103014078000c8521032141030300581124018011440e6034640e203210001c051110100d452035401e44002c0b007140045420640d0b092462410540c025201d500c000411036500e00c84000240c80070b6000002c0c05c43c0810180c48841d01a221483c02030f9690140750f5203a0180340e01d0301c00080c00511881d440200840c841c040204140c2e0300c00034a100d600840303402000030810902020808100d000442156001800d8100704281c1c0756400e001001030b0660f03507078949601c11606946009540003a81d00080c030315410b810030000b600c6500c0e0780300b207903000e10000e54440f00703614060003c00e90700fa0090425a16002005180c00d0005141c40e81ca50083d500c49a400a8000d0800a000c00b050003050044001c0381a643e20f40350b448100035143c0d0007240400f50801d408149034100c02e0804002d1400500442e84082c0c3e141d4241009507a81c0f0360003c46954055414280c07401e100f4031050003810140e0f540200300b080b10380e0f40c4009078070050412041504d281c41d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 74429327 1250 74428077 74428129
    0xc0b040f081b01090c090507050406110703080309160519180e01090c08010e03090a030b0402151902070503030a0206070f0c0609080405090f3105070608010611030304030905 76
    0x108440c00506030601d80300b8000b00d00c14410f420b150051450715480003055038140403c03c2640c0e9448000c40c0c00781c070090b040405144441c1000146400200c1e04001d140e080b0020622000d100300243c9070101520056444040b940c40d035041c00510b1440a00403e5107544907001801407401d084010111600c8003400020180c0100c0100750079200c0c003a00c240d03a00c940e561014031200c1c4080c06880141003202004625081e501c01c0401c480b80001c0c8005072a0200030404502155905941800400c81c03c41c00192240c2102c414184480c0c002264500540f02c3c07030b040054581400300540e8020005500940060b90302c201c0309580c07054410403aa01007160031105900002c86030310038000054011912103032902c1c200014020800805480740349440741d00010880940300d84084d44126a811011490602c00354600e840400300d05e8100050181c00748a00210b00e107070703102034158101d54031540d4400e6580c001c00b030015224442501e0140000d0716001c1e01340418181403003140101d44201000701c00d91 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 74430577 1250 74429327 74429347
    0x813050c150c0f06010e01050d02010c02041d0106080a080a0c05160b1206040207110f030705040905030d0b010f0504031101050d020c061605090f04050601050f0a09090c0c0b040f08 79
    0x7220001002144210010568000c02d00c010490002a074681500070021541815010808200c0c1445030305e1149000301c00c0784085901c1141c414a41035805801802910000702071501030080324507081ca81c940c0b81800000c1c0b04440003072150200c0740c0209a40e40740a541c5d100440b0101036109050350b080c4148144c0052208010102c0001000018200b0b07443e200702c400c200c500204060304840c42203005210103400f240d081d403000000030a00703c41c54000c00c0c0300d10f000321b8103082d0141d00080e801840e081c0b0803024000044001d080d51440d445081000c01000001903c4024243c2214030015a042c0801d000180507135650810642c03050500307506041c14403d410069900815038103a89400c48001c1c0700170b0388070140c0c10300540c4245081c0541055007000c0481d0b24040800c81341e034486c98880340410001e0b4064000c0354818843d0340316042e5201000c174409405440070f842600b10f4185000c10401046101c2e106406815500c0a482102e40e161740d01e62510b4400312040540d0044400c101c08925 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 74431827 1250 74430577 74430589
    0x702010c08030a090f0501020901170114010804140a20040c050409021c1a04060803210a090501020f0406120902130504110901091401090c09060c050c0306010306021c06060813050c 79
    0x345c5206e039001695885280000404007800000035007084080341c00140410782902076a403c1c0000c007841c003094960341728104a000b1a0030582c04070740a010b01d000c08400d000c10380c2403040042c0c081e8034201c0700b98901803041c0011203140c0d03120400001c0c0140b0061001800980052502e4801107000e4a078940d9803d019004540840030320b070101149105000e07020f03050034003410000b0200000510f051403140095441480c1003d41199401110300000401c0d00c030440d480404041d81140085484200801548a2592003409200c000c152042090011380071980914580b095020b4240700c0107244501004e0054030019200700e0f0300c0d48112104546c0c1c2e4071000c400d01d000308a413100c0030441c84007a0200034021501a00700c806600e00308000c1d10100354212200c07000700d079402d14144808582a0401500b8004104003a3354035014840000041c031451f9000b40240c4461241807062007084182640c1c00c5801d148161713800f280311744002400e05013070080205078050007001a100504d46d00c41c00038107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 74433077 1250 74431827 74431853
    0xa0f090302062107080c0d0b01020a0f0305041a03190b03011805010b2b020d15060b040f0504090210030518060109020c06090f06060d140d03090201140702010c08030a09 74
    0x1c103590020031000340f1203640340001d41042c040d0a1904507130070180c4040c42c0078454541c1c0c0034800c503204e454034111a4420880030020301e800c19040352412150f0310300189a82d10030700c034081903281a0a1000010302d00c00046a0003549145142110b0750300350f05400014240c591a03d6605541e0f81000b210714404100b201c0c0602d9104070000203600480740c0401c4402010a0307008581501d0100b10f046601c80c004c41114a41d07a012035607180014080d00e014003d507032200442c0e14686d8148100003620581c1134000c0d000366224500400f020715101c40c140000c0350f2140310040c0d44204028030391041c407406584281d811060401c4123520040302d918046d4640402030340b0465441d0380c00117981ca200b400c00d03c000d81d00070f842c20020b0f2411000754001282d45000243c881031080314541e004404120384810700c0118001201e040e14052410680c0144c001d014601050340440d03c0c190009090380010002c940a20f0f5058486c00851020741d01d601d0758503000103103c030305215960031900300480e0f10425408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 74434327 1250 74433077 74433097
    0x5040311030315030d14221706060901120503120604020408010e0318270903090a080a02090603010c021e01021303050717070609050105070606030c06050a09080d02030a0f09030206 79
    0x240351000f44000303052508801ea0031010170009461030314412003541204841d141140c074039174801c00e80d0744804888813403c0d09901ca4400a1400010304c00c040e1408590b803845103a0485109100741c3ea14407841030890031f0840020001d800400461440502041c40035410a20180c00181400c0d105c800c030340c3c01c50780190642d042d20392012501410010801400c0c0f000440291105140c17400085100c20006500c20362040450a528001482c0c0c2c180400c10b0b103a0180004100840003540e402c0d221341c07aa640c044060380218140d20004e42d1900b014050748140c40ae41d54001c151944c615403040215084041000381c1654080148107480004d40d1461405940100e01628260b4940507400d810050f0f49180402240c10600080003200d400c07051359800c0720000c0c00c0c5140e840c41c5501d0303c00000c045540004002d920302d034801107086a48000501200b15960719450038958a841c5031540d03904e54840ca40c00164010854900e005100d4181c03484000050704040030050381345d0780090040e0700960101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 74435577 1250 74434327 74434351
    0xf28060305010e2103070201021c09020405070c030e040908040503010e012403020d02060304020d0606260313031112030f0702010f03181403070c0e090d080c070303050403110303 78
    0x51041c00420712619103014021030040070401070700400c4400e20b070a00d010121844001100080703c0078000e4044074081000f141c802101072040054800051000c3c54085c3c1c00380b403070300c8005400c0341e00030195110003a0b0103440300318140301d00c10704210103080d100d0411074040d40140000156074034240038080e04401404008181c00403084100503080c1929564003080301910b4a08001580b2200d111060194040d50001c1e901d503603d001240500d903521100404052a214000440410422681c000c2c402c20038030341e0403003c8002414680e0f900440c2072850204403285010000120503d489a440f42c0010703080540041c0c40743c01032806c607008244201c2c84004001003807800c42d80d1041c5000703002d8003942020001401128420241901007103001030240c200400110322141c4204140c03590740307034424403600505403100003c100385181a00c207c80c1d940b00d0a0280d43c005800350014a128100410660b82054401c0d281100a0035010f0b005030144440b00d50300c04100700d801e0006511498400d021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 74436827 1250 74435577 74435579
    0x2040f02122a0310290c07230f060307030b03060709080c060c0303150307050607110a050301020c0a0f03030605090f060123040b1309052e0302090f2806 67
    0x210607440d42d422100501d040c5010401c202182d10380e9640030044e42c44412800454409080d2000d861310302e941c1c00503500030008a241c0400142c002509415244824000302210040302280502441c03c04031181d40004400c09026090800c0ca0185a1140d00e5107801b0491403c448007085c10004280c0d10f0800203901010103000d541000c1044c40000d14059840c10702d0b1261122203261203000c0904a80c1401b041800b61240030358041106401401005000d0355680109140001850049204903805002e0b004000607940ca03040c826102101201c1000d84180115544c070f41c802c01c90702490440074581c0e59030007c503180d00c82e200818402e1240949a80301803c21400141c1070a80740d282e20000c40985070421449800745d10242c4044401a0740740359101d401c82d040d0300042e0700d503d4014103481840c1408220047d1580b445450449a040700341c0c40c654101c8581410024025001c0690040e200364080380d80d40303102c0c910241e07101d00031901040c0301480440b0360854102410007451a002d4440b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 74438077 1250 74436827 74436871
    0x807020d05031818040b090a060e011d0109020105040303050a110105010e060102010f06051f05070b0702031b0d02120c0c040c080702010b01110d0c030207090e01020703030b0405060108010302040f0212 88
    0x1200c5a07500f000f218502043c94490441ca8078401005100500c1d0a1207000031a510b407c080016010040d441070701400211142c1006600810064110302c01c15103502110543d043e40611408071000d4060355507030b18041c1151803d88660348401403003c200076840c0d840c14909042803107054040c218440010324142010000242903800340401034007ca4900030003040640d440405071880c0481d040c03000740701407000440c181c1d018000c14101401540c0e40004200106901000400c83c0e62400c43c0400504201d2030f2585130b5455594040b0009a401084c0900034150701c940134041c000d220a0894250902c9000070400b07441820324024049413074601400713851502070243c0141c01e1000e103040c00000b0485201282d44401d240099818002415a0f81c400e0520a00c182d1014013015402841220191400e9600035489040c0075400285070204555140c0360a000f41c0b4007904050707641d06260703401e50302084002c5c8450484110b071030782d0800100e00f501014200d65445007842504820040c101e2003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 74439327 1250 74438077 74438107
    0x3030203120606090d170c01020c010c020f2a06040302030a030201060609050607150c020c030a150c08010e06011206050a03080403140a020d030f200607020f0706020309010302070807020d0503 84
    0x5071245114a00074400b2a019458429400300491b07001407080e07044620f0a80750702813910032200200b42d13030750000403c03103442c01054101e01d500e40300c2c80d400c0b80c8400a07044040b07911800d004c8241c12005070300f031421000080104040305040e902c0181807a1800d60f403503001924041c803080003140075035100c040c03c000180d0045080001400269080c5103400d50a94803500303500340c05044030000d50b40c3c940003804a02d00c20813003072003242005400c0394020b100798140503121000e5400c8401e941400e040074400001d11866401d4101c401414602c6490384603280151050402c00b40c00050050f40c07110000b40c0c0d40d5030f002d504001107001e8500709a40e0303429402c00e01502480680c002c03003590b02508001c0010b0320303a0003c042c00c580e018a4100d0410a980c07008584040c0d10b62a18036008c000c055598032090808030702a8001c040d03136003c84e0170341e1660749007407511010310340300b800d0258005001c4d40c02594041d800501065110b0b07200f1601d062040d500080e0601046032080d10b0580c40031a00b0030800c0040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 74440577 1250 74439327 74439331
    0xb01080702010c090302040207060e06100e060a0f0e070c0503220803040e04020105070c051e031c080112080f030103140f0606090402060a0c020918011a13020a0908070303020312 78
    0x3900c02880b0030074950002034060f84003484002e000d00da00161800601c02542c2c0030040d4050a84103466150a10f10103484114809014803210366203080081a074502c0c18040920450381140c4182d04a246404944155034000410745014054004074070740008005100400354400c1101880383d07000602905041000c04507000082e00303900c100000c1c0040710b070001f269944a6424a40a5910902071400000340700150303100d0b540044603203544000b4864035911030120790109504480c00d803a94100745951181e8060494004542c01000500018100e0782e00441e480d4018a00e20b1300e07007400d810324100c40c4d40c0240c1c026a4064494000c01c502c07030405000b0702080840c40401018203003000300c001060410040c1000307103d98800140c1c2140c142c003e8a141c031405800420444a503d030402841c45c12200e24400310031039519000b518203c80c0503c002ca40301e0200701074418040d001c1802d9040c4029800400e1810500031b540d6000212003104000345006588203070702650f00c0d9448001c0300e1020200c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 74441827 1250 74440577 74440591
    0xd06030311150c040905190e060a1a010f08070c0506041b0803030702030301060f0311070b04110105120402130605090406020c070b040612050a1104080f12030402060d050c0d0207060b0108 82
    0x6082c00d1011035441031080d6020b13a2050040003a040d16a881d070f40c00d5030619801803004040c00d0510070f0f400e01c0d101240d054416080044148a10808100141e5240010080c145e0109203c014000c40c1584182180e5600817014140104c003c0110388441e881c03d00c04990444008552180b0009610200700c0a02d0040013108025400d45c00d145801070f440ccd0105004041c1000030310790815076640c2c4203410400c03c001c460400b965446940381030540e040601114203803681d80a22040c903125501c03440132680d090030340d0098810551125400c01c07a8000c080101a070b042502c1d2140481c03580d8070008903500452140c0c200517501c0200448460400200c0e0b48802107602d4103000401c40d0541040c40c440c10303032241a10000d1182e4441081600070006a07100c1d09942c00003103404038601e00001040015075007024100c40310050b040d8000501c0788800c0360300035040035091100c0e0b940d5841c5a0001da80040c100c540f03040c10541b032510258202c0c0c01c8450b0913a00305842e0885d005072075070000704203038000715 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 74443077 1250 74441827 74441863
    0x30c0307080d0503060a1a0d0b0307060c1e02100804030e19090c021606020d0e03210c030903121206090402010807120605060c030301061404080601030206090103020d06030311 77
    0x1103482a89a00c4607407821801c0b06000001001030000d65421024101a1140c01ca08022030b00115211a07902d81089525502c0e4503d03180719a8180d1400140340700c1202d40e03da84410301080190b0340c012000325140340746400300324502021401652000901e1010260969412180d1b00d044c1c18001e11081c0c610f80c00034010301c0244052841e210302084040e060b80d41c07000c0c020405041d4031008a241510b550b8684070083c038030b2140418050b07408240031603041150b07030702c039042c9045131002c058885403c9060803103a0107909010000603c4c0040c0900300c2c2000080940f400d02c0c000da8042801d040402c1d0100c054580005081003e1624800110390805d406588812403031034180d0019088131009000e00c0c0520141010500104656400c80b0000e410b002c2e040c1a02c0354040b08405540b03130000c0c020480415484004244100305510075201140c6540004149030b034a11380030700c22198060740d10301c0c2c10981c0070000c4031711100c414050240107501c00d035120004242d802030f1030b6080200460300c00c1e030254 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 74444327 1250 74443077 74443079
    0x405072d020d0c02010509040509030306130605060901030905030d05010e010e01080604030804060b0a05060f0301080d0c0503070204050408160f06050a020903031e04080709050f0a0b101202040504060e010302030c0307 95
    0x3607002a19042c9542d050501e031400464a00040e180380c011f5038580c542c45800d2408028070124040051800b034001aa9150340840b011510325040d113071140151500715000340541c85080d84217070480616580a0010b0341c0c94200c0d00c0c030120054030026041105090001001040085010346d16030b4010548a40a01051308060b600101041d0000c0e0001c0c0c00c4036102c891051881c0d0f503802c0c5140081c00c00030701c016910012181880159042445020042d00500d1501c402e854099075100340c94551200c091841c0030034550030840285400340042c3d1700010f06000c071a4444941e41260410a4040c0c80d03981c1514440d4034102080d100001c0010030303280c1c01401a4803d984000050729005007004481c81001000790020143e9405241e00040c0284200000080c000c0c6960b40072034001c4251990244c060f40d10b050042d0152080d801c0000d4221205e0100850040d00c901500220302e5000f200151502e0760315000141a9905500440d5000b81604010000c52074204104850b000e01a405801c103d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 74445577 1250 74444327 74444417
    0xb011b02060a200102040905100812030106110c04020d020c0c0a0b0405060903120a080702011b050f0a02010e010e10050a050f01031515090b030f0615060a02010b040507 74
    0x103402211001400e20424034580583d0035420141001100d000030021034030f507980d07041d20002405040e100000340070780041c00456900004112080c5180a03400d0191646e440c4c9442203406102000340780c40c240c0980401407019581d0341c0000d003901c4146c10000b40e220300805044504143d01d0603d2903224110407003007080b94a0000c02550112030003160720350340b03441c214000b090a00c00c1d0740b80c2c90003590100281410626800c80709846c0220681d030300820183d1442c1482c1e00e03c8449074540c100c08110184008141d40d46040001d0060280c184008100740c1c0c0444545825900c0030700ca00360068100c1d00385010110540c0c40f450382d0241c0007210038407460800600c0400550b0040c00003030300b4600800a115400a65904464103c0f802c04050501ca15a14a00d000061504500182c8280208803094540d800c0006045005015000d581d0215982403010080720f070340500b0040c42036540380c1d81e10303694607503543c41180e109070017075140c88041e2040d9100240700b00e5440d04804113601081c2101c20b00c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 74446827 1250 74445577 74445589
    0x10020607020c010c02031002040e010f090509120a020c12030a1812110d080c011a040507121802060c010b0109080d050304030509010c0b04060905060702010606020a0213060e09010b011b02 82
    0x3800001c2c00c4c0800340c1016400032070b0130805020b62600c2000c1c000031300041c0800000802d0f0b812110f106a08085840d201c8114105480302030310b109c981d030b6128104100019010703000811514070a8011501e0701600f402c041103400108022040b1039410100310b070b09249401507028400c4070000d04c03500c260b103814440030b442030764829603024080d2811810070944030f4a81980c461403150b003108174503440d04c26000010f03020306101540da6a80200c0d0017074200560602c0c1c000c50b4019200394981c0e821501c444017031100104507009010403080301c441c0003240903858010050096060b14000820071001e1400003415500d0240d1081c60301d58040504443d1642d880701c11f0300d030020391610703001d90307250600720040721541c0d0002d00117000c07900341e40140010040d5560006c122030348207005075602c2c1d0f40d610405a007250b0440c403030000980c2014a10314010302d0045040010040116000561640c40d80c1280a140708104c0d84200f65a548090850883d0780202046c024540c811030b40e60a1a03050340d000c00e903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 74448077 1250 74446827 74446843
    0xd030c2003100e01240306110901050706050c040b0c060406050c0a0f0e040906020d0c2d0c020d050d170606040b0901030c09080102030c1209010b01020613060b0306040f021002060702 80
    0x201076560441c01e0001242900306800082281d07804111058171203e0243d005049880225a44d502c0c5c00072284094504400340c828842c030584078203041217610b46504001c0d00700100000c1d03a00504002c080f9180d8120005882104058001845c291800386041d00c21030714050310010706003500f448038004240e8803803180c818039002c500d0020303a01001c200109028000034400144818004160040001400e6100d00c16080103070b80c1310103040150380340c403082985060b442c09941410800c074040c0390074040d0a10568962010304030a22406040e20303520b0915600003581c4001542100d40308196003034500f0b06a40060741150510714003841c017440c1d43d00c588030b42041c060500d0340b902880c2e50428000c0a9980c001c0c068030713000395600c1ca0154101410381d84600c2900a008006c140172a0380f94038144207413100101f043e0001d003165290b18040d0160348441c070308100e800c1d6031200c400d0a002e480a020b1180124841d82451383c00d0303902c601c104003050f5105490356086600080030888070590001d074100c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 74449327 1250 74448077 74448103
    0x1230706050c03064e0c0a0b090f0a23090a0c020307020103050c130305060901061e0b0310030c0602061b2b06030c0b0d0c050c070308090a050d030c2003 67
    0x7100d0604000c01904446200d0381801101402039442c1039031401a40445e60040c080350b0583e03250403411402c204405081d402111150101400010010b040c13024001c007450328010640000c1c10350300d410000704042c42c00520a104200c00e000c0c5d41d09410851400341c2c2282c1824400e001c9500d43c0c0ba00250f41b070140b402e010741019128000f0445904952040703a65030281c800050f0707102e54a0f1304010b50f4519051712042030a62a0141c002901d07841c0d00c2e15804441c00c2002082440351821144943c0d0340c00140a011381d000d640d040000c001000250040006c01c90340d00070f03050b10720340b15900350400d1001904100390110204019030083d46881034a640c910341e040700d9120000701d0400160010f014540004018003010480420100c50107000781914000e655020700c0400c0100c0011589030242c05140030444c0c0c080c0b60300707000140d040c2000d4440300b240030b480c0b10000c03270ba250000f4014640314002600410303030b02004401800f01e0354604258810001c0a011000c074018000b0079503071100f02e0088 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 74450577 1250 74449327 74449369
    0x203040b12041a0411030601060c081b0102041d040204060614070311190507030203060702070806070e0d0204021c050a05130204020306040f1d06090105130f0201230706050c0306 78
    0x5010050a0340d1903d4410084501c0c0243d9850989810303520400d14018842c401e00c02d103400010074030301c00c0c03803141a10350344040a0390800c440a880341b68643c06044018520f950244004a24a8025043d0580c2c030f0345031241d251403504080c0140021100d00d0303044142080a4004002000c401000071640050343c546810b0384902d003580815420031941c00060202c40b0a05c1c9007034401d04c0f10009980c000c1d24006c40c00e40c0ca540d115014140c1c0d45a01611826205411174000101002e00443c280045582d01a2504500c414664001022607010380001420040c221000054464041c8252a40040d018034104840c0c14900c0f92020312080f07180000b0720907900000041c81c20b440d80c1e04075240000031040180000b0080000d001c503080c12441a25003148180000200c501c1014050303103010382280200b03410740202d140c03a0060540440e103000d81c14014818502e000720208041c0030400e500700d650b882502c1e5443ea1400d081982e001910b2114861000e00604c10706035994190035030045e00d600701c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 74451827 1250 74450577 74450581
    0xe0d050a080106052106012304060908010b100815061911070303142203060c0f0306031709030f101a0102010e070905090a05010515040501120c1505090402030907060e010203040b12 79
    0x104d4400100c0c4000c0702149004208c03100329401d4541c00f070000c3d40c1c41c1d912010350300c68550203941d088a0348608200d81c844505040c4e40c14031401201040c0c0c10040c1c02081c191501006c0c1d000ca000c0d640904081c15010115071201e884040c0c0c40071507110801d401c200500b148910b90b413001441120702c0c41050482d10800600c1d00311940c2e46000c0c0341024205204070715070310340d81c2c1e0074140700400f607010306400402c103000b010103c0c0d58070a03c2001d0030baa03030040c016003600a40300340c0361100b80c2086907840d405100b004071f00c0c0c0c0c0d40d040030032524480000c03252000c1745414400440b0302e042e4400c50041419681000640904000007207000d100352207002d40e0000e95655041c804610b001d024020181480d4a03240c00d1040e2403552580e00c06500806540920507a6a02d0b404039801b082010320207090b4030802c4900f07004540d0940c1d13481c00501c2c05840c01c241041410710004040380e00555040700c00f60300910007001025009401e00e59540f109001841c107240ca40a400400c82c8211401d41032007441b0100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 74453077 1250 74451827 74451829
    0x230109020a200c03060708010b07081e180f0307031104022203060501050f09130308060103200301080106090608060a0209030a0c180615020d0509040e0d050a080106052106 75
    0x40c1403100302c142c1004910505011a1289032a00d14050315a8024011000007074402400303420600e0407a404450701038501180303a2942211500070920405c0088a04007400800c44984400750a40310f41c9944480c6100403aa01044455114581414029007020b041000814401000d126045900741c4001d683c41280d20742c1c1c0814076a8100d5800259040194040240a520380c4404c0c10380303c09559003a454802141000300510040302e500e07070b0000e10382501c400080d220f403134026001030060401082174030350260750142e920038803541982c00c0d503400b00040140b4142409098000d01c15440d0400000341048138050f00c800d0002c01d49000b045c1c00007160082d546041120505454010074050f001e0b030748503541030a0607244070218401080c1040310110301d08002d14803540540800d038008104078007000000340e500c3e4000032800d551181d510403000030031600500071038000300c4040e90350075a03403144208003034080d690680100301006001d0101d03d04050414410310328110480890800707503502c40c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 74454327 1250 74453077 74453087
    0xa0e0c04090507110d090e161e0c0b060405040f12140d05010302030c0901260c0a090c1d0f1302160615080c130e0a0f0c050103230109020a 61
    0x15101e1080140b0b450108820590300528210180c12508241e415a44c0e05110407603620707106000c1c00030000b50f81c50124020480f02c8000910200c842d00300704281c9425450711154078401c1000c0e8501080708941c03040100300e00c0108003a4412011030701013101d8145911401c5c500d0342000c2e03005080c2c600704000010058040d21a01002e507014440c070903070303d912070480e01000d048288000c9000c0c2c4200603228601b4a403291602d4140c3e040d41d41005c01254644c045254065102c0300e030a001030140002192040d10b0301c8000302e0141c041035034042103d0f20807010041500352584a16141110036658004071a0b56200e000e125144007114071160021403c100c2c0c40080c8641484244800340300e100d2941044219000006940300032a60124065079a02026440e0b1114103402039200c04501c400710110708150b0700249442d00c0200848400250907618031000c0c0d000600309913070181e03000d1400c00a660703050241c5841c00d07400c00c038403603111700345040c2d035040da1113060041207011a00800c20141142c071031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 74455577 1250 74454327 74454329
    0x9060304020112051510031e02030a020c0604050105100509070e0d060b0d050604021905030303041502090d06020d0b0103020702010e12010e070914060306100312031107060506040606020c0a0e0c04 86
    0x241104001508100b070301150f103c145c44098138007403050521603c0c180c40c000d22548440540d403c3c03c00d1800a1710080b0305009600060400300080d48c2440b400003518030402c0720501c114414400012a41003843c6000c2c40c0e50816800140b040c82c1c21020000d055070300c0340704030300492419a1107504049140c40c1402c0901b01040e00c043d044007818030444140440001c0560060380255001d41050101c02a0a00703110a42e000b0250154400c03c0070400049004941007100350343c44a0050505944000043d50030344000700c16141e403034022540c50710b0302ea1a4440c104020700b0908085240c901c09500280601c0300308211148100340810002c10901c41c2900049d41e804515000e0728240364482241d84001c201b071550007001c440d180e100250f001e040c006000c6004034140480155507a2940c1d94460240c10341c411100d0415440e164010490070b000c8000d4070700c2c98030880b0301103144c0c6003200900c821500140d104900715488010865100c0d140e811241081c2c0c0c0891202d0380441c0d51380c0815a03481d200d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 74456827 1250 74455577 74455607
    0x4020a03080703120c0503011406070503040306060608071206050a050d0c0f09020a021e070b0a090902070807031205040b01050d021c03050415080408251202010501081011090603040201 81
    0x51580b0405500500b00c03100198508020001900884c0d42199140424001e4806918080381104400e04e0801c0203490046d04c43d0040f81c0c5080e4503991003005070342050b4000350100e074080041c08600354204400010780304445000b00042440d000001d29150b04c1031180c20700a16191044a0600c6015802100a807400b506400da0380e0384d03200104070086d40440303644e400502940f000c001d0f080400c0106044051a0300000700078460401c03500412540c030161903c0140015000e000607203035243d00150000c176008075a66525500181000307041500d12152140b81d103445d203400c2000040030312030001d055401c240c81075400f0480c148081038098006d0200d220386055001210001c140d4040010004d44a40d4031210015800c5c07008250360100d403c1c3c4004012050038404000b202036070000c0031a0140080e19001c00014040d11740326003126021500e00010717519480103000c00081040003030003044002c44200301c22410107490985600850002511500000000c601503a2107442c0c1103041c052 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 74458077 1250 74456827 74456843
    0x1170c01080403021c0f03060b0c03040e1e01030516080303070903060f06030c1202030111072a1512060803041a072603091b09040209040302100e01060503071406070b04020a03 77
    0x21000c0500017118244245000078102310012600f4520034054821020744000114107103400e14120300c030004d0004204d68608030703080902000890030003c4e41070003140140d024013098443c000080000f02c2058100d1041c0d42d00030010b00c0001940480c071201100c0c0c2040f0001900003900e0952805041e16500c0641320640004012444919030807518280c2c40c401c40c0200109455030740e001566002d2480c0140c8a01010380b911300409050750203607256080c655021407941e945402c01c0c0c1d10f00c3d034020031501e00002c4120081c041011142e12901000c0e11501c0c00442c1000e280c40380c00d0b001c1c2d6031711207620300c5040750110711340c020003030302400140140310300706860101e2210360240c9640310303002102e802e1041d1103084501c0c0c214000e00704078070710140e40c090442d80441c0d40341d40a00802680c0582304804610403100810080340c403d02c60b1000304180c2c0b80011491030319250800d4508504d40d00019144e480381440605140d44080880d4100c5034000100c03469980d5900010b080c40005a0014210a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 74459327 1250 74458077 74458123
    0x20111010614031005040804030f05010f050c070302150105030c0409060b060f0a030c030504020f120c03190303050c0408060f1012080403020910030b0703020705010e0106081501170c0108040302 85
    0x418240441c01c1580810f404441035241c1d45074115098540564024040c2d4034200414000b140c80380c000c1c00f001b603009a001048003075620120a08485088684540845012414900b00356051107200010804015000184d50414001079220f02c1c60b0005075100315611202d68040040c243c02c54070141030001c064949032559101c100b02182d114a8074540020300e800c07040c11101c0d00a00c1000e000d1900508400005400c3d202440010a03028203000140d110f0030341c0700c800664041000c040e6090f19029510081c48261501605444c80a84039043d410001d0105101c0c40000151031640001d290140c4040c03511200014a816510340d00212448021a800c110a00c61904000d04c100ca10079201308065540301d0082040701c140074000104506501c10109076011301c2500a000c0f0349004400000e401115142c4d40307800c45290b6032101000307400c005c1c1d0381c814103544d04440500510903003407051001480d070007480c2e8680d41c8001c02c00d4140300d081004101070510070807105082d1100c07000701104135 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 74460433 1106 74459327 74459339
    0x1b0e01020c03120904060902040308030a2307030203010e090613020f04061d0103060b011b0308070c05030a031b0201060305070e040303091703060f040b0f010c0201110106 75
    0x14420511065419a8140070b02c83c010701c500001d0b19a03403080d5400740030039101c1ca680a801c0703c0740306010400c082484131044039070044204100141e041c19019a05450f6130042e00030a403885000010425042d0b01179000314185c03540f43c4410400742d941c14008964030302d02100c0312400622000034060050400085190740c005004101141043d00d81c00c40c0255a40c000e11002960180d1400410030700045128060451b0001c1c60240400d24039600c2c480c9607214607407402401c1161040000d01c03907911030506031801139401019680d40300c0c070040b402400303004040702d02800902d41c511500f03805401441242d00300d981c05005060654607150001e84c002c40010b100b9024191544540e02c00202d0b81c0807441c070801806543c5603100c0c140310040c8480006001e0086004920741400ca000e2030b0740302c00807c40c00001c00d18014043c2c46440c801200e0507021107401840541c00d2203004154 = true := by decide +kernel

theorem cover : BRFrame.Cov 74280577 74460433 := by
  have h0 := BRFrame.cov_init 74280577
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74280577 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 74280577 ≤ n) (h2 : n < 74460433) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
