-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3527
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:54:59.944977+00:00
-- url     : https://prove2.me/submissions/2b55d9df-b383-4d19-acea-a6afc6324def

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 634172661 ≤ n < 634352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 634173911 1250 634172661 634172683
    0x9010b0c2104051309020904022407120f030507140c03070203060a0203041703070f0c02060d0e030a02010e030c0c0d050316032105070807080709030206070c0e0f070519031404140609 80
    0x40a84022a00503d00340e240d0a0b170300d8403501c401d412b52640001c541c1c404ca030484942910303d004c00500c05160160300c4800720403111401e0074204045e080c030b2000104034004044074414420380c0010108000c0d5010019560307090750040480300a031400c0e0900d0000783d041502d00716445d100340c1000c02c080341090010b407071056416a60701c0c100c0170408402100c448030401c60a90308144100240035050415020f03140b00b03400a0002150385007242a8001c0c02c5511079445601d90380c0041c48007003440c050200b80c03a00c0c402c1007204c4400e105000b9040c035500b544100c10340300c00843d40803075203035040540258441c0030004040740750354514451031940d6802c1d0303401154603c0000340d060002403a03c6004004080e001007051410001403500c2e80d000c50307110741c4030b01e00aa5031a50780540406c903000c40f40318981d500484d904007401c1035040c0988050940d01400c5c02101c02980001d00c03d02005200c1d03030000701c0c02d001c170907941e01c6030707003054200451805170b4801c4900c2c0b640241342c0090701043d00022448282 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 634175161 1250 634173911 634173919
    0x90907020f0c190905042109080a020f22090224090405040606091e05011e2903070c030201200d09060605150a18030209010b0c210405130902 62
    0x20501c00100040c500890f0405100c03003180b0100800c0915040c0b082900c1385202e0007000c440c854096071b01003254501c0e031810b4800c03c07a076014244004500421040d039455410350b100b84075000c01300005159503a252104d0340001a0000f0000491406500054203040c001e40d4010b03800740c90119a1311501e008016070740e5806a04124103130240c05d1950225900078043d94001482e40e483d00c000405560b60070101016004019418a0400c0300500c51310340140200e07442c600f201c00306044410031002e0700c4d1040003103c26500411540704100c6285000781c1600785000039940307140910300039040e40102001a4010342ca024410300c141e040c9a0208540200c0300c151541c1001c001c0550320020b080d010314110358030b503100c1c1c00008184c0c8880340e0802e640c4603c0b0714082d45601c42180000c100d50fa0302480c83c541e01040740b4080003d600d40e1800241520000b0390038543d117582d03a50034a03103440c803034000119000d5810741600200b440040098019180d0031542c40c00c0d804840ba034640300b901c0c2e0b0504040e500c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 634176411 1250 634175161 634175173
    0x3040b01050108041b0f14040218060304050c09073605040e010b0310060e0a110f03090a0510150501020303010807090203040201021e0a03031d2a060d02090907020f 72
    0x79960291203440e500a109103460600032281c5450036025035400c0d4818005000d1588090103090801c01c8420304a50095030118200755860394003600402c1c0c41c8900c140240e900002180510109001041d0580c0c80070340641154108040300400d102c50010b0b9003001544106e489481003041030880b809803814050003485007508080411005040314400c0002540d43e030301d2040c0081c1c40c10b0010600d86030710395100251103443d04102e0000000300505114107980381c0502e401c0c40030003501c2602d94030071075001c0442c1c499071141642843c0040c452070240103481201c0403028807060f1500484401c0780d099901c007403210380e5031006903941c4c0020f004140701604204010300498810340e01543d80240144100c0394078203001060726000d031310100d265204a070001c96018040c9909406011314200e15080501c04103004605c102d900c80034000030b8141c003400713620032030070604548030f2070180350f0301c00107056603640e81101c2d42107402940006507540c010340b41e081c0000c810324008501d01049401541c06410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 634177661 1250 634176411 634176419
    0x6061e0e030d0f09031b0503010c020d080a05100302031009151512050c15180117060f041118040e070308040905100906030f0b0a1104060e04180308041202010203040b01 74
    0x20703003144080f052000c0151029000020a00007548a00071000c0b00c0780602400703040c4002d0500303554006800c82d065600240032125120f07071000b003441d4002100f134400501900d07405188402c51841c3e0340065890721420903070368100e62807940000e058034030405900c0c8091200c00c428500303460455501c00b0501031250130401001a076040c4080f00c0b07a11500c2a80d440c00003140000713903101d07440e0401110469021403000b851007140c04444003042e00908210482c4c0105034048144480003e00c960302549218031441d03443c1d1543e400203803071200c41d104501d8581d003c941d4088103d10302c072a10148240e0800741e1400713035210045560340036a03810000c1c0503d054100844007000c2c0501820200f50070320341580000e1000300e0351080354003071071143d581030b98000c0c458180780c114a240940b680089134a04031011103c0114074080b10101c0341181001040c1c9446000002c004010011054030100c40210440040650040c0c01921881c4100001030300c064511408901300e0004a078004d280401242c0140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 634178911 1250 634177661 634177667
    0xa05190e032b090302070603050c2712033408251203061d06060d0b0d0f050c090f040309060c020d0c08030a2c0409021306061e0e030d 59
    0x30700302d00407541c0041c050710b100000c0e070119401e01509400682000d6014411907600d8001d141c0c00c2100540c40307600b00401401000854000c14040d500950300149100088c0c0d11544109040b8851500a40f0386564080380031400c2c07801c546c41800884080b4800503074201040002c84200b441d0814501820002c0c0050784102c222103e00101d000c400c0d010b0140d5000502c119014035003458959070105119250a6050759204000142800003032070039020032690f80c80ba03600b41c408920344100c0121313000c00c140001c94401c042c94180682103000c54020642400000108104e40700d809640c5038030315542d01e248100c094001030b507000b0000340104004029091040508480160004210701d1a452041d40c540d101540a64800121a00003041402d902c0c0e8200364500c16181400c0c00750903201c003844040010000fa400032082c442c0b0b40d904070302002d6488004100074441b88000c0c0c200b02c8941c55110103454402c070810461801c2c03101c034840c0700c5074601c180d409a5616802600400e00106988015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 634180161 1250 634178911 634178947
    0x906010e06031c0f090e13060c03112805030106050717041e0302010806180a050a0b06040b030907050d0f030c03030f060609030b090114150d0b0a05190e03 68
    0x1090b0b00d48101200c00b044540c00c420380b12880c042c140c98042d201006060007814228440c3d0000081d06640300811400c1300344803070032840050b480a00014006200041603004220084291212000100380040148030803050322a10003d102c02840d40902c600e40102d505110034011500021f03805c1c48002c00081d006c00000c00b0105104184604041c3c8500000d24455032600002c00e0ba50880c0f04100b080d547c00005030341d0000302c1901c1101c6100381450700512400c01c0900800e08881d0744200051070740ca096408880c14210040541341c1d02c699441510390715403c01e413101c1542d409039010001d100c0c50305038a0301c20980d60280d0f50000883c80c94609a8410007502c100740e0a1503158821488502c40038070905010349070548600c45a00d0a600f01900541002050341c181c1342c1c907106400b54814012101154060b03c452030040308003024601095810050380f200909038174240c3c06101f041250358012720310420400020b03034004401c4040003416505d00400e403201c2504200302d19038003e6100004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 634181411 1250 634180161 634180171
    0x9151f0c1b0807030f030c0b191103010602030a11010b030616020c0418260f13080c0303030105120708100f0c09150f030b090702060402030f01090c06050901200c10080906010e 77
    0x224000c103421a46441c44240d000300c8414270402401290f00984c0d01d840d108054442409881c0c803401e541c10f02384007a5032481035444074410704c01c03e01000d0b00c2c2007809400489415102509a07402810040c4200b0151080c0980d050090300500c22054a5400c4c603104001100100d1a440340c407814881c0c85038035000d00750344181c00601c090030581e9803180ba5030000821182561221582d81c850380450440c00d218041d812000640d0410030824815590010a03241990001c42d00040d0340001c01d200750b4078207c0c06a01c035007120b00801d111a0603510650748145600711007010305204100854030300310b40442d0b0134050700880c40c40d030803542880c00d032040d074000e80f014056040020b20f1240d03000010f844410121002c00c0180d00120800046090138000a040401254020700000a1950719180042118082d0750200580882c440740540e00c40c0c0d0000105500100141e07038185455000d19171600400c3c0b10b1940034200b18000010b1103403041000c0b512445090014000503424181005940c1101510b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 634182661 1250 634181411 634181417
    0x50a030f0210050405071509050603010918150c030c0509030d03360507120f03082508010f06050408060a0506031609051b030609151f0c1b0807030f03 66
    0x280114200350b1600c034143c015400307000100559460b00448040107200c0c0400c51040100412040010351650382c01d690554442c03440100340718036500702d200d40a403081100600b5101a074401400460b81e03035401034102c0240d80e9024810040707100c505039607910814007203d805a01811103c0100c5110f507100e510f00ca01c4105000208200e01c000180c9141c5410100c00d104065130141c0c0d00c00c21800b000540018190105c51040340e0666860380d445244502030050207000258001035001d01c0d1861a007990608404602d6a000241c02001842c409090207980b61361b01c0d0101c400301c0d12034091b000b81e80c204d40c0114000c240326501d07022050060080074000c26010701c51410030400e07c82c2000d80074000b81c50984400070f89450041e440c400b968010820003220b10004000b40201500e1341103940f903100080041c4030840c004450042003580c02c8014555055031500b500c0d01c9501640602c0c62100c09001d04110360040d41c0e203500c1c00c0007140903480344400030b501911040002030740600711500c3d114044d007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 634183911 1250 634182661 634182673
    0x70303050612030408100c020c1c0303020702091f0605090604210b0c0a0201050a0b060d1a0a0803040e0609070c03080c0c010f051e060a17071502010516020604050a030f02 75
    0x214030f45150001d0308501d50b150040703030f60310381586014403883c501005a07100401001c410540032849500c0c1040d85a40100640c02d400320a15000c5d80440e203100d07a0180c4031007a02d2030013450919518281e030003104c843d101070f4480015468419411f491803940000c1c041840c2a15200c050986264440300300030110040100c0c0101180c0b818031000e2241004507109651030300046002400c6890013410480910710300b0714804466201c1a003501c022051114000034a0417040c40b400001b014511002684500c1c08280450540300100c0604110b0300300000c0c424054a0340e8041000f1004100c134001c0000c1c00c5c90100c04040303486840c131036030810100302c2d00e18038202e4200403480c00c1d160b10310104104162244c00b800005c2851104001810165900070441c5007820000140303900303c1803003440191028030300c0015102001748405d00081041580724085081c0402000c1d000e480300720307820a90101d0048048103420b00218016205a0f03000d000341c6607040a5650941c2c0c0260b28443c103000318807d007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 634185161 1250 634183911 634183939
    0xb220f050d0c080f2b09180e070605090a0605090f01030903110118110636040501030501090204060b03040308040221012408120304020d1a1312140703030506 69
    0x10311501134889848000391004841a44003040d44d10103c10820f00007054042c01c444200e80e1000742c15040e1501001540c1c450903401103940c020748500d0002803014010141c00003200394211005004008040d05d40104441c0e075011300b61420301400304c1d06e90b0054940e44940855600c2a80158140c1d403103410000c0d003640242d1003560071102800c0e07c180d0030700114603a14003030140301c2c1110901c003502200d00914003696203466031b8407804a81154a01c410107010308071b6613011600b0002c60710b840040d10400c40b46d0b81d03a050840c043e000c0030b04241d01462410b0300100c0c0b002001000c50b03104603010b49901c401030b02c0c0c950038014280b51170440c040300c01280c8894007003000400e015200c946c1c4c420040010380c4414051030031a0342100d1781c2c0111001e511100c401022600c044055130ba1042d0100c64901441d140380c04e00c08840c1e03106a400d40000920201041020b200043c0090f054a0054070b5a0140c04110081074411001255001511002c01c0c0b05c9000081e210ba00243e5101d40c01a0115060b2589 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 634186411 1250 634185161 634185163
    0x150f02070c09050702012912070909030509130b1008040206040f030b07020607230c16080f10270507030203031c050a05040c03031103040503070b220f050d0c08 70
    0x1041e0082c0403040c0d110810300106583c240506e0b402900207407080c0900080c02c14403000c2c0c0b61214180e69000e165150140c255550090241c400200082181442000c00901d40101281d1149400c1442815078003043d804910b07040c0310b20403110030083c19811f02902e8206050740e0529004200300c1c0d00c4101000042407262920042030011482141b000149040044d0301a04041d0001c0283c0100b01c81c40d02903038140708001c0c40c0880340344043c0c45102d0b6030f102c1c0c03000040d0508000080c10311200e81e6041c2e00081401d00043e4031007960b0040300a45031000c0b681d0000a040c1d94106070744104508001e03684c0300307140c1340e5120074046a502c1181150340c407a83d2a800300303066404c4030307140070701480d000300c5030301c102e031405008031540140500307000c0103135140607500c1c0c040b447c00f42d00010782048240a2000c400303080030800c1f24040c00d4000d0443d517440d507440e003004410b030380441102401c00070f00c0d02854544182080340e0005560068800400e054144420301400801d19202592403c0c02000700080c0494 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 634187661 1250 634186411 634186433
    0x11806120609030f0e0603060f01020a0506090c1305070212030604020909010602010b040e150106081812031e06010c060209060409090f12080403020c091503030309010905010612150f0207 82
    0x100c2040040350042c00b40c140a44041076034411581401032581e640f100a0350340720100c075808113040302c14184460485004030300c2c0c2649102c00501500c036141c00d0016607000000c1a00340b09404a030850641401410350b030702514001e43e81c3c4800740c0e1014060842e2600e01c0d5000d550f01c01c0c00603100500b007480140008032501e03401c0c0d20003800760b559001108036a08140c00313640440e05134000202181103d40c0d8110380310a07814030a40c0100700c400b0b00403c0c000c4162051001d8504030210407164182c100c403191540560055031816581c031041c0084404d440421100d50b4401c40c416102c0280b51911031307c0e038030041d601011007180d00c580304200203e01c50030745101d505000ca01421030300d8120b0a00c0c0c0361800703101c41942004000c0c44061b40c1080b00217540001c090a40201c203961031031894643d210604118410300c0310207503140c00040704100f0152015171003524003034018402840310507526203c0307400f07151042c803003e85026100345c00300344600356a4018040348000c2500040c03506102d606c8480d0110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 634188911 1250 634187661 634187663
    0x20c01060b0f1e271c05070e0a060b03040b07020607091d10091e0b0d0210031107060207050610152003120405071a040f0311014803020601180612 64
    0x24001c090f105a00b03040817044800c90740034040000320f0114054503a207503a4080c41c400c2503000c1a40900180c000526500120010440c4c81c101d40d0b2a400c091030594000c11046800f030006200d011300080c0524810303098002120307060b03d80d40480315405030004003094802080200d4a01072202c0c0058020058458041d2100c0c62204001013014104448001e41e000001d8551049510540810242c0e54500e40d084000c481c0d400d00250900210760742418502030b003040540340b2440400d004052020108071184902c0502240340a01a1540e0b040d49800b207001d409440099040c140800f8082600a03146130011260811030341030410350031400501940480e42258aa0441801000160b002600c0c080180c0001410f1a04150804c0e1514200300124440542540a10102c540f00c59014003021300c001d40c00c078940c2131050f007450a4200c1c0800801422440c07184003001e08040000e00b03c10f4034600d01d95042d805042c40d6440c016054100f40e4007940b04d01041c643d250400a2031582901c584141a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 634190161 1250 634188911 634188967
    0x1e1021080315030c0d0c062007060c0201030f06060207090c090911041701020a120b061c06080f07030b04060b1507031709060709050103020c030913020c01060b0f1e 72
    0x15010342c034181402d0012103404a40030384252140c4000088034500040b0503940c03107150004c4029428090560420b0120f864030718280034025020803010742c071821040d031280c000e0b203090011000d403500c0032084480a11501700140c201c04400e202c1d9220750f07002020307030340e1039442c0849200d9120f10340001250740900a500ca41c0000103401c002c529aa00300801180c68403074000c40c10581c0489029005070000f010440c0c4c1d80356568101001952584155a0b501285900680b08030f01d08500203401840b06008500651055158820b129100040c005007504c0c2d10848855540d226170b65900058500290401e034040707480501042101150000b03410220300030f82d208030f4015a400104800d518002e000d94031603405c96000c01600380d40044844045810a1030016039904501c0002811401000c11540c1e00100c1c0100107005910140c024284850016008008a554450600229108440c9115007848081c00003640c550607042c1000d42d003803900f0503070300d2601103d141000301d241d42d650469601 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 634191411 1250 634190161 634190191
    0x1b0403021f0f020604030804110d062409150b0f090904051b0f031e07080a060e060901020901080f0613090b07030608060702150a020f0a081e10210803 66
    0x1103544034502240521140c0054280c50401c6e4400506c0440c0040000d4a100080d044484c43e41e1150200302070003c2d041039080141c0c81e591290812811040c149802c05484c001c080400e0200c0d192140c1e100800c25070b2501e0303191500c1c00342401c40d20741207918003414419050010104a80302c1d00710551045101c1c00151529811203604400d41155002d03815008104803040c0c24055200001c40603240e034031020411038841c0318107a48a140445980001803607016891302041080350b5030f005180c2c02c1c0d905c1000e49001e6aa2421641d0813402500e40031400100e100d40400c0413120400a05904036030041d00841c825142c100c0400142c40b074030b00046401c12841010030011540c1071203114050900c600c00303032441e03060220000356642201c5521242c00358118000c24641d1f03c40780e045580343d0038554421520781c484a50003602101007100ea581c2d1807e40340645081441140b040c4a01c2401e25603403041c0f6440c208400008098071040d940d444020854160310301082c001d002440c0f080b03510503402c2e94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 634192661 1250 634191411 634191469
    0x1e09030d0f02160f0b0c090a06030216061b0815010801050d150212090c040506012715051c060b040e1905010806160512041e14100605181b040302 64
    0x10a40e10046c618480c0e0141030000c418103035158031841088906902d0056211076180402400c0820b8140c0d0040a20749440c0050f02c080040d4448018001c92944504e0305030359852041102d00002d043d0314030300081c81b241c010b002e01d25112038640d064600426100c1049100082c40310100da000030301c0e10004142d503c00308000300504101c01e041c800e8007642c00780224100900042c08080742c00411004070383c284210328400486120b030000023007005002c100c1d0158205500940035511503168540ca005a130000c0484904c1075010b440d081b134110947d25483d117032804a040b240120054001c2c100724008003e8114550014010b0a0181501d800078201c0b60500704040d0b02c83c804510b600d42d0078020103010360300104003240030856120f03800020950404442502d51700c04982481d4000703242007410b0b41944049003000501d110405030b101130822030342d03444100304008072160f01c00c407482d02c100c1e00380001c684041004100f00b408203039804031804d0544985c0000c0303860907001000c0d0300075201030200c16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 634193911 1250 634192661 634192673
    0x309030f27030a02010c02120a06141e0f190b030a200301060b1b0c0907030204030302011d03071b150203090a060c02030604030e13141e09030d0f02160f 67
    0x8409507080300100f0340203490b680041c00240b0741c1000a48035491501e002c0d1244c3d902808101c2a0720b601503000c0180d40b0050106a0344d0200a0b00c501104110601c8092220700076100c0305400388000040d50082d951311081400c0f040c2c010f181c44945619115202c2d4511600e0402c502c41d0094441d8005501e61a00611500d034071030000e4503910310a030b040090801c042c3c14480111140d1505588100c1c2898100e40c200078a0041c4110740d42c1e402045003020000d116a00d54050b000740e074480c1e4001d024030300301844d641038085610101c1242c00d40080002e00000f9400d18011740345450441c000020380742d980c3c141d000c80105030021600258100040511f841e241c00c509003005003000c0c2c14510800003658000c41c2d41ca0000400050501c05ca60b0344039060369503440c00c4040010f0300342405101c074400d214039602c007800043d107034040c4080441154411412541d14a80e1242c0400d400550030300c1c459042e20805000703058a40c00001741c0c20003a01079500821b4484200041c0902e4038004546405d180c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 634195161 1250 634193911 634193977
    0x1a09100c030510030f2d060501080309061209070b0a090905061f0f0507021f030c21110906040608071e0503010501080a0b100f0f09030f080309030f 65
    0x6042014601001c2092803002d00b5000f0f400c0c0c07a00b14108204010851038403500510030801d504048400c600c482c00c04d035401084070986141c2c42075805004d5640d07240311003903507030148020441d8080410301007500c0c0800500001c0c2e61103205042141c155036507900144207141c1c000d46000c0001420244144910b007118000c59400ca00292011088654182140c0e8005465003594204000ba2040180e902074407500a984040d031b0020b1040069850450a160041007045006400b10703003412560700c512030146110090341031089200c461180c6c040070b091030040404001c1500d40e44010b0240071a640c41781d01c00b40020705415102e1031403c0c00c1c0070304087d1101100001d00c1400d84403405130304c07144560100950341120405e090246642d00c411350a0000b1b0603459000a400050410f460090300754800b4065140422507112950003142545e000c0303c40c0702e02400003806141c644c1c0e0b140d400040c10701c0011a8010018004d490404003103a140e0f01c107660110b88905d2450f9030001c0c650800c2c2c025603540c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 634196411 1250 634195161 634195181
    0xc210c0620150406020a0909052a0a080c03060d05011d062d060d060905010c08130f080a140414010e040519150503121305040509191a0910 61
    0x140006408000540703100b210060005000316004904515a140110190307405000d0882051160389401c11900495121684da09159140e21401541001c103006044590234801591111815039803442120303607680c00030b015507800440304895800450b03428420306c0d101740c01c00164608029404c04009180020142c03002c81d004030000c10444481c80b840342504103401d8030ba013a90806945410000e61810900200600910f0234402d82008002042d0300c180390400700783d20341600350389644241c10503085550394010f0004003c02d209001260001000d403c2d4000286001e03038420056030882074a40d00710350721001e4007419081020050703680001000300c40400948080007640341100039080300da5180c0b0001740145076030b5121070484504d6000c9010140c240581102d82603e0b802c201000b10398042041c41020001c40030f0046994941401914042c030340100080000c0300c614006140d180000100803120342003d40890b20160700344550041c4100300c08400760481d4080c2d440c035602592440070b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 634197661 1250 634196411 634196413
    0xc1503050c160221031308060a05160e01030b0d0303050f0c04150305060312070c030b0108030910031d0708030409110c03190903020d060905060a060f27020c03070314070c210c0620 79
    0x2b0070448103500140480310524054030300f61403080c42590050b8014059104000d80000001100381c0034950140c000da40101084d070300c040013030b40d144100305081d8011401000002c000c00106440502e12a401440c0c00141c000c0c151406080707292038144460384044407c450f9902003203020001e110074030300c4203401455160003461030070440344000780a900ad000da8082c14581c2d901c0302000d2001d03202166008480244003291011501c03801c0c007540c1c0c4e0700305220b0f5111007400c0903100020694488140c490022102c0c00843c00d00355540074070522143d0000c1054208140b880b0300002595031900b4144040e401900d000030205828188142030180080024100c0c1d81089070410030441d51014080c11128054a0a02000130002012400c000c11070526a800b900221740ba0032003100c048020304481e84203440d002414104c0c800c018046010b00031303000c2d1503489004400c00965444200c1402c03042501320890115143d207503209004034546402c0400000c80c0040800c1c03290350140101c1f85880020383c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 634198911 1250 634197661 634197671
    0xf07060305151c06050f18030f0706020c030f0d02040303030506061305010e01030e010e0d270b07140a15061706010308090307030c1503050c160221031308060a 70
    0x42c002a0151070b00e549010301640c640700290100c103282000007460268088020b010900f083c9014810040b030a03290540320340d4180042c409420000011112038250f005143c0f42004044d49440c40207411519000009001c00c214001d00304000c4c5008080c0f01c400264010f03111421420000c3c12518018989400381c001046842802000d030444502104c509180c4404606151001240034180c8042e05090707070741c00d00d4400c40700b550b00070608907200e04243d540d841110060039a0219a00100c0c00d20340b50f001c1ca00c001c03c2c8000350120009025490148820741e101f07030149501c20740f803d84d403c40280d83e071300400307880388806c2005070144074010041032424403595003120f9040c0b82c6801c1d061100a1000b40005a1107a050b00d084c09404000d540002e0aa400f05a5072081c030b00f12404a2074031308000a1400000034040304a61054400c00440700e0810708001c1c13600d07400e001c4610401c504409450799406464140303500d0400007410034030404402e511526203000a81d17480c09102500560120b0f08003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 634200161 1250 634198911 634198921
    0x70501030b011211040f0b09090708060a0920030405010203061009060225080a0b0117030301120201110f07090f15290f0a0503060f040c080601210207050f07060305 72
    0x1c0042000fa41d10014400030700d003021100c6005061240e9800000034a00b440d00025045030903801a080c41706007900c10030880d136210740b801c4500b41030803558a640060302e500d041c8245425513009500d1104c07000f81340380c0d48152004601da51a0000c8400300c9540c0e40010030084241400c080ca034081007480d0800640c4181801400380d1140340d441c210100c0b1b03c810761070400500140320544802420080141d802004041c00c110040c0c81090082460700a400d05400c3d00075080081183d04030786d00e40c5640c100841e1150300448407000c070881410028810740560450601042c040383c402080e100e0700004080c0c41d05005201030300d94a44040354a40c84108041113411000c14085011950704030740c069812007845440143c81c01003c0d042c105410012948001ca1604a0000c50049601700c800b00090b51007203042005032080c2d10f100400244004004c550b40e54054511a600382940c01c0c81c01c02903111150001089130490340040d602c95000d407800d210078040501030700c4054115850184807030700c0c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 634201411 1250 634200161 634200167
    0x10c0f1202090303190804031428020f0607181706010b03061f0305010303110307022103091903020a0b040f12021f0c02040e070e04020906180901050702070501030b01 73
    0x40318022502180e000101c102040d502802100d0004840420105010300480300040c00d80004440c1100420070085000c0c45513100002a0350451000b030750f80c030700700585003100d03124403a01850002c015842010300c0050a02c0c021311480d44501d040d0f607100c50700280c0048181c2c1584120754052011040703a000d46d80b068100200380c003410340340450b40c5140e0340d0f158100801c6883c0010702a070000c00003040d01c5101c45684c19000a4103d80c02a0350f060b035600212260141c483c45604002903000c203807138100c100c07007040300c410301c541424900701924108001000443d110b1303c00e99105041a41c50150280b08502d000c40c485000740c0300c1c4540b401d0510341803410000c10201540901101e440c00e4490400c01c5584c1c40d003a0003400b43c00c0d10101c1c00c20307000846010f09a11160314049108604101c48144003000008610044a456556020702a1141c0d002d00072049806449690041200700d0b80d05c40c508a42d42990f409200400c0000a1030310301040000e06200a0743c101c40d041604159041c400d5a074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 634202661 1250 634201411 634201427
    0x6220201020322080a0b0f071d10050d020d020715020307080112050a080c030d112110120f0c062d090f0f0e060a060804120c0510050108010c0f 63
    0x10212040002920340210f02c0401100c5540c03004c0958401c51491904220001c1c100c0ca002d01c070038000c2d107000c0340c5030208142d8108400742010200610803641400756443d00e400e941448078002e040107442c1c14000c0200c80d0680c0d000102c00748900342c0010f10f0000308900081110089e0015480450a42c14801c100030640340040c455005a905080850028000140203000d81103a2181509903180e010107160f540b00c1e080384009041c0c0a140040880300c41c20b1440481d290791a89484400286181d07022502000300e000d840c008a50001083c00f06042c103070900c4010240c0c1c0501e030103000e1680180f40088498840760030000c1000040d0a4601c039207103028400c8003e5486083c1e009111b46111001120905459030284a90703500da420f00203404803002c45410146c4212201d8448165076207010720260000790f105034070000d821000060f005c02c3e80790380140c04041b800d10f00101c09417041d4407003525250303003c0c00206086981d0401003201d03107001d204561a845c9a410000150000401c1c09041e01c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 634203911 1250 634202661 634202677
    0x70803070c080d0507090e07030e031905070803010e010302121501030618200307270c12110301090f0911010513050307030f050d11030712030902060705062202010203 73
    0x50601d00c00380800004209031000102622001c0003030f450a030400825510461158081d2900c42d40b001c41e03440fa00c01d000e00c1d059901c45000035413404501d074102500081c03401d0500000c10005110f0b820015040740000c0d8020700b01024002c42c5541140100800200c07003242012140d40074049202e00b144403543c0c01c504490704240000b039014900300700000c240c01c40c0e135402040400062800c040c003c04011042d401020142d0440d50869101c031703030540100c07040754214040f90318203012030301c038000254000304410440e5144c0a15071262440b004010b90b00c1c1960240d05280d00480148681a62072240c6546802100b40602c01640785031202e030038a0212505003410000300292110710000340f4819440240f0014040305c662030350b81d0400b1600c00d0000c6004440e00d00131448000581c620403190f0310b0074910200080c5181c000705544031107500c9000809030003415201c058510160381c80c40b015062060080307002e0520b0f4503201a0040950309080c442044209005140e840580d03800801c0c0c2d4003203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 634205161 1250 634203911 634203917
    0x40e01150f03020f040512010501060e03030901170a02040b040f080d0f05071b08150609060d022d041b030605060a0c08070521070c05090c07030516021009050306060607080307 77
    0x241143c13030b80d01400ca00c600c0c0c0280c0d070085000d14401a11300015030105049400e199550b4818000341d100300354980c0310b0482002d00242c0400e40b410b0a032440d61032126001402c1c440b00500e1700795605c00c2c0c1c51454000398001415245056001c02806a0902c100b007460102d9250550409046840203496402001d5015001a8814901e030303608403518040b0001420b201c034100e03810b268068080c81c40e0080c045844501440b43d44021405034102040c2070405580d005212000041500138828220005100151040000e540c0041895181c030300c501d10200800b010039198170a40000042c1c2a9515540818040d0300100088181a41d125a00e809250fa01002c0e03142d0750000c03410700300d20700b08401201c02c0d8980034100121054040380c6000303002482c4201e0b40003020903621010001400800c072020305c1003200070008100001d12400c01400084102c13940018010707200e801040030052003880c000d000c20049130050010b85010040250710041c126102132410550340d036025100d000140844080c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 634206411 1250 634205161 634205167
    0x50d0b010e040f020a08010911030606090c0a021009080a0314090303220602040e010509011d040f05210315040207050703030311041e0608070c0b0114030a0c0902040e01150f0302 78
    0x1c010362100c41c2100031340c000300001e094a48540c4124024884001c089540440c0184090310720300b800300302c4d58401d620007440041d19640f0307031240a00c1f030f6101011100450003000712502c1100d04510030345503404d000f151140c7d00c0e81e0b1284000343c01c4800752118010500e10950400400e01d0f00002100d601041019864100031440d030082c00200c6026000100fa443c0007040200c6c00d50340d4410520b04030350301143e03a604c807647c3e41d0707411240384058400074051051031000098007103120726004400d0070780f0072012034480c0b0784056051040c0d40b480308240601c0580010500100c0c0c04500810401400f04540461803c441e665446ea80e808851100605141d100c95080d801410014251001009920b0003138140a110020819440496000d0a03012800d15004a09440d109050244c3c101b0f88c004184c040b241d082038509000d4690f0084825414401c0d510044000f85002202100410000001680b1281400c04401404105811003415000704052850101d54400c800d440182e050b401d006075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 634207661 1250 634206411 634206413
    0x30405071a040305060901020c0d05070b06060304020a09050a0b010201060f060816031b020c091b03061201230402030c01050c0a0308070203040b041404050a02040b04030809040b030604030810050d0b010e04 90
    0x1c1c503000c0c0d5400540306002d9581040138080064000307000220828090302c29a18540b20284c40d1806200d0b00540080b003410300144140c01c1500045400c07600007020200c81e00c4c6e46584000541c0c0d0110b400d1004991240075001c3e05503024000d142c041e00d09004c05540c030b5400c20b01d00600400e8003d0284800303560251a02030303128026030003440800100ca990341c0b094181c1c9100a03680310b451001d0386010340070200024000d1064007004561914003031072564503580f0760100304003a27a5442040c07504c80d03540e684284040c02c81c42c00c2c8505070300100c0e0310030b18255241600404bc108240c1c07120b21414010108092220b80c1c0d00411000766180d03040c10300c040d243d15681d808900e507000d55004a01c1c40e00700024003241e0001864000044141c0448042c046685c2e4504981c00f6409184141031034280280003e00000702c5c0040501000e40001d030001500d120301c44006807030428243e4090780401d130503600b4050001d05800d0481c01a000944904e01d9000301513861813444041482116514502400494 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 634208911 1250 634207661 634207709
    0x1c05030a0f0c020307050d0504050d0f1a010f140d1101110f15180109020604060f0318081e09010215061801081006210f020d0602040b18030303040507 66
    0x320308511a1a04014010860b00e02940d00d034031140382a21944613000c15205900e106804076415143c0150038261072520a80c0e4129116850079000c840000068400303c4426551504d8a4000d00a40000e240010b103003802d5029820080740002d4080c899115600010515001e000080300d9801c1c60300c0d10b00690030760561810004c5080c0140240d0103072041210740000c10281681c05002444106410701092415035422100c406030300940000c8140001c005507070003501c11008640c19402c0201d00c01d00d980c604070041d080f00e002e04031020350010424031460001083d8084a10410071401d40c81c200075000043d40c0c800400341d0400801800320005a0151198200000401d2410100707191703a50b101c0c07844581365070508003401e21940c68108005040c64030f4010122208641303094400d500920390b00c6200308428240740590b085100d0301059000101c062000704001c001c411030068580807a0100c000b000390000f00582c2c402e5209000303210105202181c4401291001041001d034a4170441c0c1d03038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 634210161 1250 634208911 634208921
    0x10b0307050322050d030f05090604061d03131a1c05070302070602271c060e0a080d021e0c100903020c03030d050103110415060e150c1b031c05030a 65
    0x480b00051020068001308000010408090196900c1c1030009403050f00c00702c1d0845c1c0d0304407203a0403550701c01408034001c15140d50040c20908420303024500400c61181000c0d25550207141540d400c0440c1d0002080020000098402010712010b082c0785008a80b100181d80354005160301a07207182c3d500003150a507030081e4111900f081e4003c03401d40d260030300d0038080c0360003191081080c040f04407408403244a6150140400280d041c07146c0803160345442c2515600c0042031009402501441103021070b1010070290800340404408500c405070382c40302032469400149505030440c1d00602c00511280184810110f00040e00441030300001030302041c82c0c20b08038513000d90301c4512601400700041d01c501400c59a04254141c0740940c0c1c48881c0000000241300c01c880e2900c40d0400c58024040080c0496480348801c0315071040c0007001d42c02000614000d448065004181408041c1d001005404c5850700e2006000000c00341140903141030500c0000d02d21100120400b0007080290010000b00e001c2d10035400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 634211411 1250 634210161 634210201
    0x10270c03140c1053010602033906091005041a1003140a210c12090b03010f0501080711060705090402040803160b10030512090409050111040f080303010b03070503 71
    0x143ea807004103054511900c0d90004000c0c5130810205928000c2c0300c205070030440c125540c65004525010180d080902103208982c1c1c03070110003900c021031040445106101580c60f000d4140900044e0070455011440c0860ba400070030765070b500701410040441d60784043c1035a4003030312449410440c3e0350f08031814010120b5030801001f01c41daa0072154102d0b2000141c004076103104a15001909010f00341008a642a80b90290002074820710240d000400b209001481100c0d1414209075407522400550b03550340090b004690320400600d020005503a2110203550001420b00b010310034004120507207138442d04000c1c9401c040c00000920300d403494a455046800411428040e0f0740c580842d041e0b55076080e40da41da4140e03032180340314012880e1400075040039021242d001004040d8070040703c040c10003070342100048641c06655030031054041002802080f401c0b41e0791800007503459041c0781d110b46001c0c000d508520140d52013440140221f000d0b000031a03410041c1400d1494403a9640c46012003142d22000d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 634212661 1250 634211411 634211477
    0x50405010e2a030106230a080a08071a07080403030e0304050a030605010503071703031306090f0f05060a020f182202040e0f040510270c03140c10 64
    0x40e584041614501c005500585400340c155201c0b4004100743c26146103004135803000c5403204a0a0f0068102e10b0010b48034070001d800f0b101034039a18011213041815401084d034070103800013054020000078002c11a24130390500f8502c565820010002849010020001002d06035607040114403200c0c1002550004c010017000d1401681d2a85800e2020348400e20685000384a425008540040c00528031464561400c0c0110304559400d0366041c000c01545070162826940d07281c20202050603038070800c0c0400d000c0c20f981d0314410998a0f25500d403d0380248003100b020300c1800700e601709074201011958105c03620703031f40c11004180c0180001d01c5004c0001c888144081e800c4000b500c1c00004d90007038400c941c04840c01074480d03554800c0e15401c2190444000342113400010203e1684a06603002c242e0300400d4001003005122040c40c2e03141d40125240040e03480680140040040005689000d480e54010002034044000701c240810303040718100d500d420500c1440c4900d40ca051081400100c500c5010103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 634213911 1250 634212661 634212673
    0x3160c0b0a180e0108031909090603050102030702150601121109040c1d01050703050a081027050612210f040b04090b03010b30060a020a020706020a0b0109050405010e 73
    0x240c03002d01105038209201011802c050303000248186400309890484101001451620500840803644061442c030104103102c21800c000c5488410b1b0b2044001446c03040c80010780e80c0c2029503000e450301681c2c1e0b8143c02d059804408001040c0d07440000c180c2c150540240100302454030b001c2112560040744202c5070082e14020164440940c40900906468030980d11030071942908401190a4800d03640b0140c04503a017044211a60362207001707074940c842002400481603a40b14890000000b0a06100d0a040ca20150030394242c04546e20800390004011507000d50380201c07045480703444036687d502170f40c0c0040061001c3c100d101d49040480785501000b0781b5256555032113600c0d9800507001030260218551034000220001d040510400e000c68800034408070000d00745d40031241c0c401c440e960074900400c49070b2100c24000c9070100005030050100c1c504c00740c5c0ba0402014028900b404c02c3d40400c0c02c41d801041400040341b00c0c00c46441c155079400b06e000c102961141070160240840343e5444425200325 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 634215161 1250 634213911 634213927
    0x2003010b2710150503150307030804050414010f0b2503170903120c0c0102040b03090d0e0303041503271b0801140105040903020a0f0605090d080903160c0b 68
    0x6541103808801d0544041e8200340c076011001103602005002e5546085085820500c815005001440d80b09544004c45144d01590402007070500d1447e40c4220f0b003400c4082001d00c030501d4180980c020071086030002440303030362421590000001c028440c5680740c400000d66030080c3e007104200d6800d5811417580074a040d603807034a4010094802c12989101c002810f40108038031401c040100e030740040415100b000d1301d448411003e5090fa0192a5001d030644d03007004000346010340ca0020354460203013a03000d00041860800040c2041c1c1072000d40f00d100360010001804850980d0503842341d00000d900e030000e02a9034255001c1d010180c0c00b500305110101c00039600301080702c000f021843c41901038002c510400c1d641c985581c03c1c0c840c5010802034144107440140410b041903030003105854000c0c41111104902c40e141c1c503c5000e4072000a031002e130b07214010014103507002c12a40d913031901d0910707000b01c01c2e10740408110388901581040740c010040d281c002c032042c00081c6450002900880421607a18170007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 634216411 1250 634215161 634215199
    0x20304030b1609050105030601050702010806060c010e0708070b09031f06050604030f14010501080a0f060207080a0f0924080a060305061e011a04050904060e0d0e03010b0d2003010b 79
    0x8803240000d5183e10f408121540318106890007048182c442500b005100c0d4019110000000c0806400580c00d205d0902c204509000e040d1240c02214090304003182031003545410010340350081c82d43c0400412950826403400250b0b1b619604000401550003031044080d40c0150003140d201c0c55104078086404021b01c003180a505041c180304070b98003d0005032440d03400382611800d100301d10b4941c1121258002003505032490602051141000500e002c0556645030541c1c0c200c0203101f03000880401c400d0401c01d40010403000501401c40040c1250003a201200b800c602400010400b044102c1020641d4241c10760072000c051948801522020300c2d2043c035942004003128100700c6040e503500000a06e100704005250841820302c0125072a181c10030041c400c000c20080c000300c0e401e507038400e07200d4080403050006900d41c441503a12840c0d100c2e411070802d800d550141c505248190303506a0050005030100507003030003503c00500c07900403503619071001030700515180c9200c0303402c00303140000c110444e60 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 634217661 1250 634216411 634216441
    0x3240e0d090e0f0402100e01031104060f0909050405062811181503150a090e030403060e0c0109450606080123120a0f3c03020304030b 59
    0x70b01d00074525090b544441c1000b0750303d9402c0d1000307500300ca500522820441e00c41d0250b04c0ca0020181404110651070300e890964591050384007000240040203010806984040c24078010000250140010309150302c50b90f2302c40ca800382030400100c0c000d506462004401c0e00d80900b2044002908010b440c0303503020207007841c0d840b0080f851032496402410325030903c2c00070600d1401104036a0310714199580d00442d02402ca001c2d03800c0a074400580c0100244035081030089101c00c034103000141d03489510f1484c00909039500e0414400058010070101e40c0c00e642d100301545c00302c84103042d0720761509070740c011500d210007401040c070004107420360076032600ca0f8480c102034043d56203046020405940d8401c0200e441410038020403462030f4040301e024004807a100c81041c440100144903041c0b4600f4107400702d01c1c103c4050004c440e6098050605c0040c000d440da1646120751080e041901d03000f1100c1441c005040e0107400c0c2d90a1907003041c0480c2d01b80b40c42042a50081c60f841080300120741064803000075004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 634218911 1250 634217661 634217669
    0xf09091801090516050a1217070f03110105061c0b060112020c0a0c1505030f101220030705010c060e210418141501171311090103240e0d09 61
    0x104503c002030780e401c000b4810710843d241941847c41c4140955200c5024000030340306003001c020140311b91008210000481d00700a44242c503800440c3d03201100303071403d540008161510034140c1c0d00860f40c00324120003250800710361104100b10690344a6005961400f01c402c40558014800310390300c6298400011700780c40c1240602e01680104c1e07910418807080d8040280c3c2c0e44005101840454440c2e4281528540c11028014a05c0b00301625851041d14004c0f02c0d91042da25038134070360305050000d1045040e80300c1030345060b8050480d035410900040c160100110009080a130b0301c1c0c05c03018980e0814410f005000d0817006c0c3c1c8030201c0920304109801c0350018040e400362034049010880905520b48034070302810106c0fa215a40c1a691142c3d4840c1c0184084020303410f0142050b032805101c14138500140c0b00300031510b404006030b02c180c101000000211101c19000302107000061000c9208001a1510003070a5803820a0543c0cc00d0301c40e4019003408aa400a03034401c0301202e1410300d811000780001e417 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 634220161 1250 634218911 634218943
    0x914070f0f0602071806030803160305100303050316020a02030d0e100e10050a030e0d090911090d1b0e130308060405150105030709030f06050103030e060f090918010905 74
    0x481d03228980740070400901d225001c0568003401041052001d42c039010b40590b04810300c0000c1142e681d03181c001d0950f0017104c04c0c520740c031509840c48005c940c0510030282c000a0005410800030306541d03000d000b51001505444800446400300301c9241d1081181c900d0742039015003a80c0b4007031102080541100c03071101000344038091000c800d207038803881065000e040400c01800308041c5589640291807552000700e40703c04040d213802c40c0031250101044800000d0400760381e814000e0b440c0a155404460510701404a607400403c0200324aa5810fa0025501508105000341003150b070b8104144009080c1c0c480742c040440d0a0802244201c1d60940b0007d050090f00c031100a0787c4c0d0007040008682d02141e4004410003140402001544194051580410141480b10b111522521854880c4121460840d003050300c68006000301944404000703a4000700741d6440c0d042281d0440c2443c0c1c50301a07245224016505480007401c0307461086000142007102c00000c1080141906001e6107803011034001d032101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 634221411 1250 634220161 634220189
    0xc2f15011d040c1203050c0d11160e0c13080703081213050a120e031015090903120203040c05120a031413090e011b0c0506070801050f040906091407 65
    0x7282003981c1d03045101d640d00c450307040794880c20a113200e080356440702c0054003004014400035017445010050302da02d80c2c1d102c0d180c01e24100c2c1c0e03c1a8007880c1580607100d003011201c4503034042020205e01c2807860742001070001a251107100c4002c09448100c1300e40c1c0202c103180b05248000090100e150020000e500f003110418105980e01e90341d044c044030511000410a0b800910140d0100c2c82c594074208032559140f5045680414030b90000b4030740b1000502500115581e00c60002403158040700706401400c2c034040c284403000302500c014169506014000c02c13032940000001d0200840ba030744180c0540402400f071032103c5c1289681316980e0529800442c0440c801e201c00350f80241104054074400701411007815025402c00004001810040c0d6407140c03150340311a50f0215440c880200364044003029518030440c40781505015143c0070000d45480e061018140061013f034455000c2c6600c4000b01392008214158245401401418984009005082c2c808039003c481c000109000080311199080c401c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 634222661 1250 634221411 634221449
    0x10e010914010303050d0c0e041b320a03090c030602041403010506060f070204060810090c06110d0f050d0908041701050c030604050903040906080c04050a0c2f1501 72
    0x107071811080c0000b5020440600152031890301541000ea19440c05180080f4202c6004012800340c07028080c03603425000b001c02e0f030748410300c0d803041080d40e0034000c501d4030094141c070301c02d607500b5507400020503195581c40c0000c48034a21030081d040081c003030f603000c1e02080c48550f5905005000390418054104162400701c403c0885d440c05000c0c150042000610042c41e00d00d83c40c20388521030f409010126001521a40300050841c07040c00b407421401404d40e80801d0280e202c0c603240310740341042d0704580184440703504030703428135900041e00e40301214580c00d0580b8424000784c7c05503001d0281550035001e142c203048005041003020006042103c2d000303048400e1000c54607002c0c41c00da4500b243c8806280317000780300007a401d01c0c19420490b0807061000a0324607082e200e03a0300b241034512030b40105807035500017034021782c0d40c0c280781c42829403000c8010801c00050640031001031030f134008410b64001e8182c0221003c10604801310351840c46401c602d040f50390401d00100c0d20a074940c003d22800000d40c00f0040142 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 634223911 1250 634222661 634222691
    0x13080f03073b01080a0f020301080a030305061507081e0a0c0b01140612100e0708060a1a030a0b041517061806040312021204030c020a080f0706050918010e0109 70
    0x40254114002c10003800d100c41001100c005000400060004da2990a410300c00d200c00d1005501900315100035021845443c1000340075a1070141103940107083c3d01d8100910310b001c9005403511140d104c03203095034882d54401440c0c0940c3d042c039041900d440300000ca0f40c42454020402030011071040b452025147c0e6245545031002c0140d0404540103c0100200c4250f070303450081482d400010f901c5007541c0542c0fa0b115114801d0000c65881c400b14052800348003a074a0040109401050340701c00401da4420401540d229500000e06007040c40c6841f004950856540c40c1c00c142c0c01141804040040c0e10380d07030240e5041c065401807500a0500032070f4086028040b2080141044a808800805d01c0b926146d80880e10100300304a0208010380c24442d40c04001003440a03940114020360703c481c00c0401a004000035801981e005012560018480d0019484041501411240c680c20a2621842c1032008114070402c011540e800340d0301c0c43e40c008184000000031150580301425402c0201c80b1f6a08401c8d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 634225161 1250 634223911 634223987
    0xc08130b03040b09010b060a031112010e010f08060412030c14220f03080702152a1c020c0d03230c0d18030b0424020a2613080f0307 58
    0x45410103020403042300c4140c040c1e00007503818000d0f0348a1514045d011248038000f44001c1e04880404240c1000406c6452942c00340c0c80098a030900c0076080c18101540d48481071180300500383d090680350a100e2283d14081d0f405000208054001c040c1e44002c85400ca102041803004143c00c0e80d05401c8001c26591092015081502e03400b03e40036217090290303000c2200035605100021461007040010134074926448080c080b0038400c00f480b0300d40010100900074140134100b000e1845111100e0030307500045600140c12605a1810349001e01090b42c541000c40341044e0014000c0020b0680b01c41039100c082c864001064080da0600c2911110258000700b214110034900007000903141010083c0081507414021030381251042000c8141c02140001c11011041310400050540350f011450f85c201d035401400c0700f290020303100c9090003240b041c149102d40314400a0032482304640c003805107404002c500300880d07601c0c506000800d5140c0c40c02200060003418041451003181d540038a00003c003440181039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 634226411 1250 634225161 634225181
    0x3010e0604060f201608040f06030b100509011e0e03010207080301050102060c0406170c07061b080a0902061206010c1a0114010903030e0d0309181415030a030c08130b03040b0901 78
    0x2035600c4c20714084410040d8000d2400d01b0380d81c6440400c000503120400d1002c40000f0301c1c86807404034204860400300481c54205142d07403410f020003001105156030f4000701074103000007444584240c101c00758000b00d44165010706180e426601c006407000900030620042c60488500740d086580c1c81d69134051141e03180c080c40c07080e200410000400d503290070035407803903843e80302c5d03c040860390814500c2e071640f40075075031045c05020704c1c103040141d0000610303403205015600000c0e080c81801000265400700c0e12900c128014541110030600c085078003070303108210040c001c40d0401c901148c206031030341c07400c4403290080c450104e80a0000030170790740d20f50240356982c085980540307a41c1441d8030800c041c00350440c10690210200101d80102190b070b841085001d030000e01c80100005801c180800704035504100c0039180b00d0031010340300306801c41f903500007038035070300b184c1c0d05250131852030545141c074140a0150f82d03142d490501030b0940c00300b048422500030b103109038002c0d040048070b500d80400a078201c640400d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 634227661 1250 634226411 634226471
    0x21011150a110405031009061506110c04060b070b2703120901050412030c0c12020d0e0a080307021c080f180d050d18180b1207060504060c0203010e0604060f 69
    0x4070741c51800704d075580300c7c090950059802043d074000490250184035032070340001011418551608440304020445103407c640300f5038081240d0340c10540814520b0045071001052001402d0001d500e4061640803041030344100c0c10303250030b000d01c60500e150b125007011241c0d0318442032000000e4841041409418003994000204c1454146d040400b24090005c80028000780300260030101c00084074003107990340340031203035020741441c1c4212180141901c84491303c1d54480c2c0620038050000d0880401100c0c0d2041d4101e81c5016500392002e09000b1402c400a0042c007130000116020401030000002450707500f003d0300c4001d500038011000c000040c0d24619024103d5841a0b40280c40c1500a2204441040700031483d0046d15684098945c03021030269200408152120b4201106092140d00f8400341c0e50040e004e005c1c2103041640041890045109000c208184145c0c2d500541d00c082d4030400e0b140900405564003407500342000c0019002040740e05201074034015026010700400c0040c07181c4d16643e10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 634228911 1250 634227661 634227673
    0x2030909010302330405010f0504030804091503080c0114240906060d09061b051e0306040902030609010b12010603080313060e062d01050d021011150a11040503 70
    0x1809201c22050302e0910280030440c03210402102c1c0d50003440c2c2101031300c10383e10740326902c2c0c2c107240005041c850018100705c240a002d000c01e000140d0a1000e5400351040c90700700113101542c2c00a210783c850300561000e48440300006021076000010740000d03200d4a915000040f580d01c408621402c512040043e0315000f0042e5110302100349800c0e11400d40055009086600706100c181401b805c40e82d4001c400c4588a980303405007008102c1e0080000130b40e1a06060040c101542c0c400306800449007080440e041d41030000020344103a40e268890301d8102e40180c11507540e443c00381c1c00140200b019072800c07441414101c01e41c48807540305018031019603034460f01890071500d5000640c0408180d00c041183c030243c8030f2000ca0042a002c01c200b500c10390b0340c00d6a94144082d0a83c40d09114504081c00f500002d401200502543d02c864441c40481641030b03c0295400e400300c242180c8406061503841c0d41c500400c0d0407111102c9401c0d060700c1c002c20b081c0c070041102c058443c1400403030388110300c02e00750950461 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 634230161 1250 634228911 634228913
    0x603031602010201062c180d0e1c03051c0e15060604080a03021b030304030309050909010e0303070c02180403200c1809151b0a0504080706030603050607020309090103 73
    0x10103415036898810300021801d591504801405154806240c10a604440100681c00104044402d4112a913000280d44089807603001c00d480d0001488064244004200c204005031601c040300000303440c1101d40110621524603000f482c036400002e1881c0d8000c0210310030006008035100da003800e16000303801000007222001d507400a40c2c00051203ea0311140901c800103000c2c40c00d00031a50700030b00c0381d07014080c1c4035510a2004101140203210600960080c0b206200007a0000307100826148100d51074000391b0340b41c010711750143c046902f80840901000c001d1103d40c46e0020071190701c90344202d900020440d01c0b1240000644012a4080e00262500720060708400c441800d8101c50502c1c00c05490f280200c40010030340d0506c3d00301c020b030300c0759170034004201c00040180481c2c4101e101d2040072180508021155882d03501381725243c0c070561140016250865405501140e00414070002030b030360100d9456401500070080d6100c06c0e5014010b070400240818400300c11a036501c00700a080010a900b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 634231411 1250 634230161 634230187
    0x80717360a140a090204080d0906030501080c040e01090f030e0a0b121810021206090901092a05030708060108010c110604030e060412060608010b240a0c0c0f0603060e060303 76
    0x40b94062030300803000a00c003148000c4640001d01c0501080c00081c6010a851400100340b9078640d8019401c00d40307010018020300c44086000d40148500312030204021070400b107201c0c01030180d000020290502c1c4026002010303008940000c144400b02c840060090b40d50500c401c441c03284814107000c800e64a000107003504502c0114001942801f012140e100140c010340c0c0007240c2c400382102c900411600100003c0c1d142c0400d43c941c3c009100002400340a185070b03104022000560780c00481c1000d1580c440e608034602e084890003e010040455030040e039285860360315000280640041135003020001c424040c05400380e4429104914002d0003e546c661300e084680c1c1a1103109141d21910030040040c100d02034654103c440d9000360000650513203400c03001401c64121000c101c0c060fa840c0540024104218a040031241c501141c906036280503141080b5203464011400410a4511020110314a85240c00b10802e07205151402c0001301d40302c0321075038804d42c021203100e5850b6008000d03501030242 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 634232661 1250 634231411 634231439
    0xa05040306090812090106050405070507020f15091003020706050907121203140c0c070905090a0b040606050406080f01050609251e0e0a091107080717360a 68
    0xc01100c3d42070a02c072161060001d0303414180c031014100c1e9107800d414003051506100e40e641082540c1000f9181210356408500d50300480280c4510402c10805c070214203002d110300b156100d404c010402d1003043c192090140007034000c8901078500e1450100022501e010000b03c2d581079501c2c01a803000020010340d282c00f40070406200340e404060302c614000d08040500241c850182c8094584c043d201c0c081100840c3c034112095201000f03a50410302408100000440e18506560304401c03040d00c140d865062400c003800071540078541003032428100154910000c42d003845003040707550080c441615001c0c00c008424500b9508030070011005152230002c00643c00d5008603000060920b003400b072140c02c04940c2085004c00e50900440c0005095000c94a48051004050a080d005c108000039200c44d003000d481c06400c0d0014022a80080c4070002e109000601420000750b0b5030304280c1e2107940c00080074004641c5c1941542d41d40c003001d4000094005d80c1c20401c500203000d010300700c0701c2d4640307038075048175803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 634233911 1250 634232661 634232663
    0x6090603091204031212050705030a090809060c15010e060f01080402030a1b0603060608190b120607051e0a0807050901140705010203091528060b0d050109050c0a0504030609 76
    0x110031503140b01200301507100030300010340c01241c070894001d03e43c440261452101c00e80e20040945001e0400450303907001800c0c1d903000b82803180001a0800e0301c1c6492041c5102d0300005651108000c03d00d0740010700000307942840b10207107503100703480c699841c120910314000507138503980d001e98100892080c80d4442c040c1147c0c09400102196070025143d100c0d00f071541d14012140c0d104654020060080a815026401c001c1c4203600c0e02421700e10303150020301d011200005e8861002911801c1c00740140d501d40c1042ea41441e140030558042d400d04110203811507001b40d2035100d403040d00b8824801090404802e6840400d813544402c021651215422903003030f4000e0f40040d062007001e00852450f0803111010b0800710b40308000040e52810f152030524604610381c011001e0aa00141c10004031103224140b074403042510400021140d14041c00700c402400940d0040c100600000c1980d414540c515003060b8121342030544108600e40b01c00d500001d1f50f1207001195804070b0810442000058280e038440d000035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 634235161 1250 634233911 634233913
    0xa050c01120f05040510051f030b0406022104020f0d02012010062601060501141c18060e0d0507140727060608060d060e121b060c04050609060309 64
    0xc00c402c906150859000b5581a1480c0c0c5c042c0248141c1803c09200d01d41c1c204d0b007803101240c2094924030301201d004200d40001030511580c000850200503050301515580165030006555031034003148900c1681c0b000720f409902c5421101202146070410403409983c40350103954010b0780c4410016201e000541c04000300d40284a403038000d00e4054001d11070900034018842d9403020790034104808141c25000c3c41501540d9900d0b01608020300c1c5c4c1c0000c0284802c0c0c150351041e98841e00b100030200c503040b49140562100b1418410710740782425007010004000c1e440307030008202803400007407103d5903030700e0100f000c40105008000903c00310300b10000b21245a9a00012a48c000ea21131443c0c203040078045044085c1c504000d0f008011101850140c0ca02500303007440c0076101c81c5014000159080085c8078003070310042e40d0f150b0120301800280014a251094554046d9a036114040c1c1d070300d02c2a246001411180c0500310103c1da400d180a03045a044a40003010301e800c0c80300f0102040401d500c00740c40040d003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 634236411 1250 634235161 634235171
    0x30a0b0112150c0938070b162708070303080910050702030a031505060f1201080d0e01030c032004140f03030702061317060a0501062105090a0206040803090109080a050c0112 76
    0x80d04178480c42e4400c14040860a51712084c8034940341207003000251031410300703c0085070300440041d400b41c450b014002803405d04481e90340c175201c4241d4100340950007000840c000e100e000301c14140c22030312080c012003940b412241d0b078880c101365401c1200c105941c0301340103810070454030f0031061083d0442c0c1c1006002184030301c551555800001d0444d8000341c0301d800085408680c00da1008150b0308160700501c0300001405040c6005180104900343d10b4040ca41415643c2d800300340814841d9114100600c1b201c0110b1881941c4040f60006035081841840350f500640c408014440c148100c41c0720101d80060011400c180155003041030641100e042ca40300c01882d80c031300049207242d035485102011184000741039207081ca8607484003500c105070003810034400d1024510303d660942d02c0450001c0c076400c0130000303080d89485940710700b411100c0502940c4600d0104000c154840e0102c0104800c0901340c03188400259985030407a12500440000b9125400030a11a0b140d5400b40080c04440b50140c0c030000342d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 634237661 1250 634236411 634236479
    0x90907360c020106060503010f030f060b0405070c0209060a0b0d09080f0a0e01090b0a0e120c040c1d0d02060f130909060c0305072c030a0b0112150c09 66
    0x11212248030503050181e4482070090034241d028402d50015142c40e1600c2c3e481c56050140c9841040440c6c4001842c240e1085410028010144d02c404810f1000a00078004e234185594020501c0756468400e91040000d500800c2d001c0c64000c01000495000003501c0c0d040800401c0c0140051071400802c1d2a1a0700c1040118140e210316001005100c4454940c450a035880100041032000c6503002401031804c10000c1403400ca82040f68a5000079044076149401c240035940e5504107418000c072182c00600744240300c40c50980200300b11009264a900c1d104006c10039a0812043e070400e2000030350052000c00003030b0b06601c01c41e401014160800d048901040b40e440600b4811640d202e8800e079181a620140c6603005030b4140a07964100c207a0f03180101104e6820042e69010350080a000030100304030311240e500030340301400041c2049800c003158480300d6940e821b10003440e03891344a040b0345110118400e40d9a401e034612501d01a0003199031101622400c040d240404801e03403c1c11610306442c1c00000d48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 634238911 1250 634237661 634237739
    0xa06060f140d23150a1403101a1504050f090a14040b01060f360f0e06011e0c0b071704080406140c10020a0909020324090907 55
    0x846030842860850100d030b00c0038a0f111a04071001e008141400b00b60303454814240e90702c403850415a49050b075044107017001c05000a00d020980711080c06481d0802d02c038090a15184039480301401c1044d65180c80301271144042c107203188558050b4030b510a801c444c0c0d8200303d08061068551040e86200001070b41c0300f00c000d068000540032501202c06407185401070004035800034488a0100c010b0601c00c110343ca069a00083d248807a40400c02c00107034400e014072000903c2c0d00000002d0840c40d040301c003203545400c2c1042550504035850b40c007040c107035888a100000440010170394009503542e041d038803411030340d5071003e00d540181c0454100b141c0000da1002d03610760803a04501980c41013034140d540b00d250980142854442d1966981e01e11018000c1d1114040b002c01e209113030031803c00005a981e8a5010296107106054202d5614a0300c044204092159120034007107010082c0d5081030004d13203104040166004003101d0003001d5400c501c1007080060410030030840d01010108031144451031b403c00310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 634240161 1250 634238911 634238921
    0x20060c0601030605071101050622060515090102060903040b0d05060612070f0f090302010903140703080a050c060a09051005072601140904050319050d0606030506090a06060f140d 78
    0x503100e0f00c0d0780f00180b008030740c1c004041e039108032040e07802801185019000605c4889004101281d0318031480c040d82d180d0b040070b03440a03003d0900108003565480701513a80f4441e54111501d0741d4050301c161004108000c0000044c2c400b280e000030207151504001c0d01204014001c094a280c3e08140b082c4481c0c1d1140c107500081610511480c3c0d01c43d80c2d024025203000300031031000d070f010405200c8091401c2c00942d03486042c103000d42c0e801800000102490043c05854082151300140200d20049858054030368031400404050f04084219215520b0340c42c6488203c0c0d555002c024516404400c0402501500d60080380d401383e00d60400c3e0803038465035403040048080c2070f048a03007440240001805207038a607410565185100303881c51080b074901540c1d1690740b407107003907044419208071480070035a09100b5802c564000020400c2440015076584c4050040e00c2e0558007a8451035001c000120010583c0c42a0400c0b039500d581c503549030a520500a40b50b021089280d500407820400543c03040039041c2c010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 634241411 1250 634240161 634240163
    0x10605041e1a2d060a18090204050d12030f051008071a160c0816060305070c022b020402030c09100504051008061801060f020c060720060c060103 64
    0x441d5401c86420074040100d51400003600c1c0c1c45500406004040d880701e1604802d10601ca4484034440e00725107842020810580b4491540010001400400e8980c4010740848580040002d0403841c0c3d141e06c0c0007010390085014541d0000d001070340c400049000394040c180b4808283c200000ca0076186501081503500071280306403007c5031910b040043d85010010352004210740b011000c00140415a82d800d00d110704440501c6188010100106002802d00310754000c0c170403001210307450102000306541d103400314443c0c6030100340340c50006065240600c22251003140c1c000c00c10b5801440001b01d5000628580721428108103d500c10040185c507140b0003140280d00b9204000e848450800400c11413080b070b15081d0303041003002d110800c043c0c0c860052022440c3c001d070402000d40d41c1c42c0e101041e01c0002440b008030f0741480b48400020010707049409601c80031526800d40b003024182c00b06120f994400c030b01c030003880316043e2291445600541c0c0111845401d0081646160503110540301d4981002a04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 634242661 1250 634241411 634241441
    0x801240512240904080712050d14010e0c130312030e030403060504060b2e0c08030a090210030c0203160804080a03120b0f01020604061116050c180f1302010201060504 73
    0x1980c4219841103003482c0b03026801111504841d02d0941d0740d030509030041c40c0c1e008091002d2200907590490080042d0350132150080f900b0402000c0c54545180c0901c801c1c0702c0d089031144440c01103502e0278040700c22107408040790702c0c50400c06491640e9030f0084901c811178040c100741d5907880c80c03c0100001d02c001d00046001d00301c08145030910341405401c6540702c0001038461403010707801140b85002e0310794031400038150034095400e40c41d440310281c8007000d035010001c06028000040002d03020866101240031802982e8441d1080800d48042d4102d030700307084071040507a0041c4880080d0382031507002a9042c5218140703075400c155075156010300c0c204681c1c100b2008140c854500145201d4540700e1300107840f90440364650030300c118000103915040702a002824041e15900e83c3c0c00c004a0100071113401181182c8620820181c506003d0344840380c100c13400703100b075034821500c10112101c1c0b03400500403a0391030a44ac0a545440d07800807007811300303c0350803415075482d4070002419a540e84690010894000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 634243911 1250 634242661 634242691
    0x3050c2416050c0102030c0a1e080c010504061413020904050c0d0b01080d0c0f020105160b0a0606030509010504030e0909150c0a0e0a1526040501021201060801240512 73
    0x110b40503042202004209046500a0103101000080020b50343c00e0982c000d03d2078115800003144001500310b041d44040c11360300300040c1c119030a03101584000c0c815801034004000400744c0c3c0340e070082000c00984a901d080110b070000040542380c40200c05402501c210301311035400800c900070070008100c1007001e50b400b4007517100401c1901c2d02400024241c180c0e6150802d02414159070724400090403100180c1000404160b1103c94000e0301200000349411220100d6076180984e54080030b04218095000000d0a00c0d0104010b040c0c1401002c2c000e40e8180c032140e000000b2101400009000186200e415108044100d2440d0350302d858498080c08200540540c0d4031035840001d4110002d000c1c004d4083d440b041d10401084104030300c48601080702c0d10305904a245252055824200c0200e202c1500185003070a210802c00154000c1500290740d500301c8400d40e0741d485054400e11407d05c50f049a80b660001c034404031107106a4441d80940300f50600d00e0500400394600000144100d400c519608804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 634245161 1250 634243911 634243913
    0x150e1e0105041403120703020a020c03151603050f13020d06090302071a0c0717030403020405131103070b040e0a0e0a050c0102012412020a0305030a051206040603050c2416 75
    0x115180402c1604a20010741c07034844041c0003420b117a9002403c0104050340400c85001061080c003903240c100600400303c8110b13080303000d0584d080c02415500600400012102c3c026094000c2c01054401c4072822002c032100c1c1d49040349441c0029040400300d0784098200610303c000b90141c07148800c0309009030b005103c0f1a0512100700800e0105610520b4074140034824510040c100180d903200b56403c4109200220b140f1900e078915502558000a6104d0308203410014400329410711004464094210013524030410f005068890320306016000816004104c184020030808138001e8020100010002d000800829258141445920100d80a411070358010f911580e09000b08501c82405450007111103e0b01155001000700034418140f5907480d4506040a541d6410240001141c12800f9a80e032003031a55802840c40e400f440e4a00724a801d1400403500d50708191190101780c1341d00000038040006840d04200e01c0740020b200e22506000c400140b41c13124907400c40070b88020310072000b1402c1404a9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 634246411 1250 634245161 634245173
    0x30103030f0c020f041a130e0c040b0108010e06240a080709050d0326270c090a02090d0c08030a030608150708100801110d0c0c150e1e010504 62
    0x1030780707541c010803030180c0d00c02016130b503900c2090b01c0300042190001100203500ca00868420711006440b54084805415140c8440c440e400070309006404605a50203911020200003c0f03c880318000b0780003079800c100500c44d00c03180d50945a0400c038024610404201c1d064203082001e00c0454001038070038804500b508080380c1007560740340c005a450403c40b40250810020444400d80140040c007013051810142031054800c002d1132000d4442076440380ba10b8908090100803c42020000302e0503071038000c40007441c3d01130101e003034400100c0040240216440e40c07108040607420102c0415488450074405400140045108000509074100030b980c0b1200e0030711001c0d044031587e90050400e90000d81500c010071190000055000803242065162074a50601d044080d40b00c642010450350b180030b11108401c0c3c2e00c40054541030426200130f024800c240e50702103550340b141203030083c80101c0c07810078030307001041640259082d10021011038842142d800302d900003000b480d2030070300700c1a5074030303420301c814000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 634247661 1250 634246411 634246427
    0x1a13020409150f06181a0306090a0b010602030c190203011d10060f050d080708130e01030204061d01050f0d020436120302091f0801360f11030a0203010303 68
    0x3540e43c0108101c0d0b1900713040140d444585045807058035510070003a04100c2a107001e09010500c094101c40c0f10746020444250785601e85d40302925520001400050114400012103540312828406080c45600030122004d1450b68504126815500c503520550200ea8000700d0360b10180c404802001106e034030b2480d00b4210342a036041031026401030076007400b0640303d00311440b10096204202e2982c0b907816041c21780d96401990625000da180762140010b5084508a0041c1624002c80341048260395808643d200180319813001510b664018004100c1d502d04415068490b80d800703845682c100b102070740080e0450740460901100d52180a80305003051101941c008902500c42028031401001030320352519481d1854001c608050b000516540b181e03c81c20004505102030104644822005110203043c0c1d507024001c440c003807004540c907800981130b4101c188846940034002003136480e51010383c20000d40700c1d4803080d003603440e00c5003004040c42d00d240000f18032400000d800141c50794114075000300036007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 634248911 1250 634247661 634247681
    0x703060602010b01020307080306060f041203260402282402072904051201020a08090105060a1205120408070e1605030a020702040b031f050c03041a1302040915 70
    0x1a24043e43c0c522107036000800c440c0400c3c3c0100c600c51300da58034000020031a101c0e50751035003608240400d0001300000704041c8140c1b200d100e40c948124400e4040b1010198070100401c1c0701342c0b100090041009410000d501c602001d4603029004034500c0d10030340c03a69410080394006145280c21140b16100140300d101ca48860003410702c082c00310a807406083da402d01d491f45102c1c5811000d589040403070b00030b04404480041c04043c0881e6800d0840d00032480c001d4100038800d01c0803071010000119821818440d85100c0c000040110b0b0010341040044503460040c2d40040f03d41c0d110341140c20002380d004102900050014100500b401d90400007803010000c0041c1000101c10391032124005032903000701c2a2a401448a1001070300c03040300d0300004000e0030182181ca60140100790a2000021199010803d10040e40000f0302041c1c603040070320a0326100c00ca4018140d03403152051405055008001c40d600b02d00d09030038a81000d04a500014103e641c4c1c14022a500502482c02607200301a83c09265815 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 634250161 1250 634248911 634248913
    0x80f12040b1909081002041404060803040b160b100810020f04170102091806100e0d02010f020f12031605031003080a050409090b070311070503090d1109040b0703060602 74
    0x8580340c4110703014103004020729252600c2840c04000d403150700c20a001c4000742101c504403500340e04004282c0000703511138007600710b440801070017030134840c101409480112040d14004501d05031900c0c0c3c442d00107410180740300c180941c064035098003068000b2581d44c0102644961403403035a182440c0d50389045410070070004028010311090100980e03030419a01100c00da0300444201c003203c0c41e00180288500106154084200c00c0798420f622078080c5118841d20302550450030401c1d00e600c060394003104030810b60364002440781c66040154480c807846408920070b801100c000440c8000070340d0802901c1c41040d15480d00120800081035481211070701c48004900f0003925505100d503017a102c4811500002e000d40100103062005140714070300b21001000010f1040242854a29080701c2c088015269a00064248000740400f02e02140032945060341c000011480c0076020010b0140da04411403068170143d0111900d0b005585503039050320710580c0301e81442e030200e06d40083c01400300c80c0250084811 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 634251411 1250 634250161 634250167
    0x20a0e0d050d02061e060105030402010302042616080c0f06040b0c06060118060206061020010603060501052d01020a0f03020d020f0f210d1404110d0807060b030c0a080f12 75
    0x280b003005d5581e550000001c0c0f0344145d03207a9803800140d000e0f01c11548515038865252040ea40005000c20110125505a030190b6203070056201401001c10b03200c0c000e4400e01d8100c211004c2046c94103107503903181c139000680740354101585c0c0d1500704072075041881600e40d103410107010450f01e1340e84103608040d42d000d101480c0120701e04040000b035541d00014143c50040c034100d140c0c488014000c0e0b088149840364900500c0b142940c6d40c0f030b00350280034988821142e00c2e0030036002181d117291060300c118441450102e1203540840807200303120b0040003808014194002c626180001ca0990311404100074081d0b0010f088072208100d000f4034154494034024166005030b078038035044030404640190200010301440034049418001d01d130182c41003010181c1d480f45480e04680101c101007000500c0b80b4050380001060202c90802e0201c01959500d0050612400b08450000958194403401d203904015040300d0408900d140420101511a04101c820b5031181c00980c0864404001500d0040003240400781 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 634252661 1250 634251411 634251451
    0x326040b07050c070306051306050a0b010e280e0402100c0b0c1b03030f01080706021204030f260c010e0109110d080d06271e020a0e0d050d0206 63
    0x400e0160150a40c400c0140005020035680020000a4080d5400410401542c188030040c156106640c100444d441400e0034009a0328106502c00d140c2207040603160803100782200c40c100308950070108003a480c1070042e1404007010b680c1585c80d00b0080d0019400c100c07558201030042003c07514450445000700b0101071140e9000480c1c001905401012504200e0340352104041803104210703034061403088511010080025201c0d032120680d0480300810b0a6403076103512100e049071260720001c110343d0341c0c450130001000010348404c0c4038202c2500070071419156943c801942001d11070786004000000f000490f40c10341c1c4020a00c511135281d81e00c80000c01c0181500d45d01c00c1c607810008a00c10f88540307030700107410080c84007a801f198805424100200401522aa6600030040307240c01c145c0002d81080458034040f003042d10841c440c60080b00310807001c004036440c2d101c01039801124010100880e00c140c802c2c5036161051065086813040002e0b20340308070b20410003441c00350000c0807080e085407000401c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 634253911 1250 634252661 634252673
    0x402011202070f02010806180c0904150f0506030c0f1b1c0e040b0a08030703050d0605010e091b0d02070311060f010b07030509151b0c15091318032604 66
    0xf2040ca68282048002a6203160001d84501c25031145a0711031010f01080206a003140c800900c0382c444100d40802040c0c0c46403c1c448880f40550041d801111174440050000b03181c5400516442070b0401240d6251405141880400d908007107502d41400200c200d0368070317600b00203014143e441880d110000200030380300040100b0b04036031081a1030160350340d403d030b101e0547c90300c00c02c4802500d2030310704507513941181d490300814a43c80a00191070140c07411101246030761080310324444c0c0301001000300982d43c40d810500a446000440d5983c1410310800100f0203559050018284041c000e40f42c51483c41002e158950802400500c62a8807034200c0005000024054054501d60303509460020780311010440464100c00c1d00d00301c0460003030408209403050a41d2003140b607440100a01c2070b20340c0341ca401014850141d0705160310101c26003042c800e140b011308100180020f0004410004124010038020824082c02185403d800244c50b12100c0114005000130000c2c010007901420082d43c50151150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 634255161 1250 634253911 634253933
    0x30c060e130e1c2c040b060a0c120302070b060609030a021507110301022d0d140601200c010e010203070f0305041a090105120c0c070902180103051003080a020a0b0a0203040201120207 80
    0x10320155444503413107000f61300d40d90300c03480c01d403080680496610007640d0006422102c501c5421a035001081c20801030062084c000c1c0c03141c40303170304c01c006007226101e2808000740e91308080305554040c42448281d02c0544d940e03a09841803804070032801c542d80c1900b402d048010344c0810078854001c3c0e004124192040322400d403045861000020b00d100090b03002c000c188010310031103010b4046181082060403c4442500e0f42c2c50240030b00346ca070b02c1180d0030b8906600760a0380312488544920703049021a079800e0750140c0107800c1c41100502c1601d181124a039514a81c844070b0030410f800094012030184012403080c56001410011190f506051201c440c00080c154840c7c501da02c2409140d1102007540701031400142c800116000741955400d9469006070b00003500112101d441807203c44d940000e455021b8400c4601854000802e92035450943e1100725455100d50305040451142000707020111b0584402079001d19800140541d0305d0506000052941c00640944102c45204101c03401c00906401c1c20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 634256411 1250 634255161 634255217
    0x6090b060d0522030f0306050d020a05040c020f030c030406091d0a15032a0b0f090f06071a0103030f080c1b0c0d06020d0501080106030c060e130e1c 65
    0x8042850782d681440c51000000f0b182101c6030010a07000e00d6420142c201d01500d41540e030545d0b04000055a41080003c102e082c28006500442c500200380060304007600444900c1c040360040318400083d44080324030b1544201017a8902e03420102d03090200c01e9001c000c41008101c88400c0c07442c110940402c10464200242145003a40c2e682c0d21000ca0650b600500d203001141c020104040d00d540c441000c6101000701c1c03400d020015105500401d0142010f0240c2d034401c02d6021005041810b11814400900501c4001c164410001c1c020b41c40000c9034046c03180c489125660034004c20303516529000c0c00301c450035811442403204500801500885880a5601401719980c0000481803030b2200e29040200c3d21081075000070840344d038501400100c2e0000c005030690381d080ac215a03a40c40031400d02722415070000500441d108001045403d101c0c1c2c0c0b103003980c25002000403d02803a04501031045a090005611858001d890064108120b281980d41000100c0c20b24852448101020020b917032903c1c89 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 634257661 1250 634256411 634256437
    0x90c0703170709261501060c020103150b03101415190908010221130b1303050f0301062f1207080d0608010b0a06051806030612060a0b0406090b06 64
    0x100040302203104083c0440102004400e03c911071240c03200c02401100420701560440c403c2c0200d01d01d500343c030140d005040310010343c3d480101011310742c011405040500316080e5039000c1d4840100e6000703041c4001710f004028603807159200d2450a484942c4141c28900c2142c4a07911246440390640810800c64019003601011040104d61082040d44c6c04070950f00030744d03040d42c030105502e50248a4540665002186643c0c81c5608c0d5540707608000740d05a00400040c424110140454981510480d21911051184c1041d60528400e090303201d19175042640220001001103a0801c1b030641a41c00c501e400301070a042920920100300c144655500306001c64011000d03001800300d003801a01002e4505c1e040740590b040c80850768569002e03020300000001b01d44158802d8000007035046c0240100c0748101e0100007204a62658102003190036040108520740180140e50801d001480520a251007001c0d244000158002c00d41c0034070048500d6500000142c61a080c1c0051807907440000340c9050b22520303d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 634258911 1250 634257661 634257707
    0x4152c010608040b0105120f060c130506030105030a0615150305040210051611030a050109140c031f0c030b03060406060f0b090f0d0614040c03170f090f012a02090c0703 74
    0x650715840c1c06580c541c52000b5000c9c041c103002c03042d800b440c02040700920207440b01d00050b031a402009614030081c418168940c0c0000050800036180e904070f03c402800d0b6481c5600c081d81d036020100c81d034a48403e440d0000969440402045103401c5603c0001d660040c0383c010f0070642c4480ca0001e0030310282c140509070240c15940000250760800000f907074550710030000d01c0706440e40d02c2c0c40100c154840b581c1d000d59004902c0803c0190a0010b8040e104400c1c101d8003002d02c00e50700490a0007480e41c40e4504c002c054549180031000e440810503140118800e0400080003840d1408505861015401502e0b0610b02048520269620483d40036901e0300202c2c0c03002004846440c0c81da000381054a92850000e03600010402405083ca1681c81168041c004c101c081b05e001c062181101d103d00351842c2205d503800c2c0318800050802e030455142c144418141a820041c1c030340c42141c0c8041a00480c91a0b07030f6041c04203482181032001c00380d0b40004103060820f01704030325a50044c2400540408a4121031448 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 634260161 1250 634258911 634258939
    0x10b0a0815010c02130b15070c050118091a100509010207090c120f09020312030a0b0d020d1b0f0b0d0b030a0b011221080a15031104152c010608040b0105 67
    0x250b11075065401c00521150b905c44144407503ca080c0c2108c803050f02d8103605940005415409242264207081038803640000b60341c1040314440c02085c040c4665801e00140703a1500c8525118084400034100c203c1e07c80750b03121a6843d00083c80e010b050f070080301c50682000380e01c034074141d0800d50011400000c14008140030380c1e480300081c024031200101951500c110807540c81440345010085000d010700302c5040c0303c420b1168061200c0c1820602c3c000790131138503644880f40460032080180005030180c0301001d0800390341f50035100c40701c1c0c485d070082d0410b000300040c0302004040038480e0b011188410380141c00503d40b6611484030b071501c140302300c00d004011050420100030312185805c90000050031f0856905120410081142c90704903080342d6228584200700c1a20f02035066028202e0744e0204981c04801d2240e01880f010707000c1414822213a03000c4540110b0070810061030301c1d0020b1407814036070103000a121210700900106900000511104405100224410074020b5040d40d40985245010f0040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 634261411 1250 634260161 634260199
    0x608190213030f0b012c090c0406030507170a050705010c0c090f060317121513060b1207080705030c0f070b040b06040b01031a190806010b0a0815010c02 67
    0x7040c00310241010020030100401c0004011590094060010300715182e880e001c1481c00540d042866442071811122030000700c0c3d80c183c0c070642d8490154400e0784c0000d2001404034040e9000c41d002100e140c0c00406040c45050070744c5a16450301e04448005200d06202600c416444517101e0180c581007100d003034814018001c8007001d44000301f07500a420400040811040e01c01807810740801c4860328440c01d01e02200842800c10b440041500d00542d6006841c4e07514002400045000459044000c140d0040003140f641e108410088c0311000c221a9100c0340c4002103610108003d10180900c000e0303c00703002138507501c90305030303948200700c0e005a66844000c81130b100c0746406140c1c00203000c8405801084100840c1c212118011242502c00344212002d120054082c1e071940310209404440e120440c80c2e05141c20b603a0443c2048846840801164490f004c05003030140907004104403000014007a44000e500c0402503620a0500414000c00c4030f83d180000c04030806840d001e84900b0424400484002c0c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 634262661 1250 634261411 634261417
    0xf0d3e131a0303030709090f061d070908030406031a010203131e1521020313150e0102031303020d0f0509010c0515070c060e03031b0309030705010c0306081606081902 73
    0x20002d04981d03d07441c14180040c22100c0d94081d1402807810122000c0c940a01401041c065555485600110555101c040ca41c1c09100030260300c00c01500700d00000c0c2000b1700740010000380c005030381c01058400c101b4107807486803801f0310506811036008001c0481015a44c500038400d076032011122403400c0c16030402e00d44039600703543c000f8610100340884041c1ba031038011410250300b80610190b8001070000d01c041c4404ca0204a90340d220340286d04041c00005519049281e441b10f20160000078655940b02c141c42c2240c00450b1006030b25011107655405054041244800350b000c14904150309084801c0010414001c00c00103505105e48100144100071050090701a1064007130701d0000c1a20700410000c00a030010301081c1e55081ca0302d10040310408011088910480035201c00c040310326000e002441341680000d000701c505010a202e440006882030150f0174207401c480c0c1d400300f102400e10041505042e280c020304a10000514010803600e600043c01c10303441a0380082d50461500d0703110005010f0304c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 634263911 1250 634262661 634262711
    0x20a091d010e0c1b0d092d121a04030e12070f0e0a330801060f12050a1704050a0504051314011404080a090f030c050f0d3e13 55
    0xc0900c411401d03d9036400035400080711007801850880e2043c01500503820101c41d502c242c00e035030f00f030901446802c03524607481d0794503031140d1603527411001000c43e0f4946200007642c0440001d100480a00c2042c60f1110011805a41082c060f290040c030f090041c580c046014400c1000c5000c1080c00982d14484a512401030700020b80311141101801400041402e06800c4401c151015003200104c3d14000511411040c0c2c0d46a00d950118281402158082c030f0201100489a600c100d2600100158001c5015100d6404200c00c0a0302e8078180341c10064217a07543d40045009a2800040000074504c241c000020b45420403001c41c4807100d801c03499805005034419030118806039405100c10810f040c0d008160720040c50b55141c18164842c24440590012840050f00814030110144601c0c5020030440b0000000141100b1003094940d45000c0d80380508900824201414404120000c5840141001c65039890b1700e114030410840000902e85171003100740700b00fa00e40d508005038501402c010142c5180c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 634265161 1250 634263911 634263913
    0x4020607060e0d0206090c010806060906190c0203010f09150b120a050321040203100f0213090c110120030a060306050414070e070f050d0b04020a091d010e0c1b 70
    0xb00441c11402c90390b07140c0c12450301c0010711958000800c17a00700401c3c1c0f0034005905a507000c4444d100c0d007041024680001c03100d180e001c1410012058612080b615007a076010071a1181a00c04541d8010182165010044441e01c1400d00102c0000240003141c603024410f60301c0800034501074518046070f280d83d05050005030921800b0b958000703006001001d0005008002110203d0380c0c0317416021010000e09580094040d48184030301e20340190160801c6c04003d0b05250018180402200441c80205695104414155030780c0041d8542c00d45c880048104458014001c0c05054012420030000e49800d03802220120b0700030000c10194062a08088011504110148030908080c02c02c00d10402a10709200010f20907000001615010403054a00c91422600e952000401c040e6082d241035001160302d02e00c5030b943d01341e10740e031300d41d1188098519192540c0c0c1d4080c035036040c40c1d060f41c100102400840c5421090304010000190409808d83e0f00900e28488281c40d688150360031000e00b102114982d2403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 634266411 1250 634265161 634265171
    0x30c170a020a08102004120302010912080132010c02220b100806090f07200d031109060403080a1b0b0609250f0528030b0604060f080402060706 63
    0x903801000580913242510034000f00910502c2444a011a0950b00f1310019a40c4041c031041100422006214002502a000104043c0c0c0c0daa5030b413418010012131542d0110301c04c400188440070011081640b420a042c48003985103004100c000785074100ba20f001030400808440d10001c5403119007001d0304070308900702115010502404424060410420030a010308941d028040c1c3d2544160b900a0080342d0240100e480381e10b0b84201c50302e40c06d00c000c142e40284440c0180721040d0140c0f8004c0907070a0040d09000d0845580120303401015030b4180c030798204015800b84215900341c0d550204841c2101d0380441d15550700c2ca1034450955540401d0001c600080a00c03c02c041d062091151403a84103020460b0b20f0b01031565010464110055507640c40c80020b546035164800d81c5004140041d082205801c0c01c504007090b040f040c1d41d1150501c518010305601100c15460015054001c20001d02400c4581d141032604084004124070500e0701100100b040100114040d9241c10f000c03504156046801404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 634267661 1250 634266411 634266419
    0x31814010e060a0f180c03023001050703050a140f04061b170703090b0f07051e04170d02120f0717030405062203030f11070b071404030c170a020a 64
    0x51418001d0f2500f00c500b00080286002d5644000c400200e92103d41180c03000d0650f000e102a03c03103402e00314271510764810312903100342403401c011040680e500c00020485140641d001000d4410152001d10040d0030000001c0c580400c00741e038994000060b4002d000b20b69200d00b00003015059907584848801c8007a03078070740030240d486201440307181001141b6990603125890120f0888402c0c000140019885001051006104920030341d00300c907840c9070007414444a0042c654044034000e59008440c140028200503e402181c02c1804101007040030f4000300c0d1721702034045e4651003d010144521500080c2d04517042203240e003903411381c13604400c4103036007102400b07604071190740141ca05a8691050b400000c1542040314103c5e80050425026003080400554007900a014404c5040c1c02994035681e402ca400f18042000c3c1c150a4054032600c0e0b00c5082c0040094503130500c01849041d8220200310600c0403aa81d111088102c84d20311240030b843c900441e0340710b41030508203c1e000354400e25440c8006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 634268911 1250 634267661 634267681
    0x5010e130e1606021b1c0803130b0f06060a0c0302010626010f0c1407031b050105040201140703170c1902010615110c0906130603120f031814010e06 65
    0x10800b54880710325258558682c2003d07660380d04010090203140c0005a01d4007100c6c240b4840590324890f2040c4100100d0035140c1d10701983d0f810445409820386901c00b8020240140c614603030350002408154075000c1e003417175808616548200c00020050009a070030b40c0741018400d5100c3c500410920007106602d9032000d81c0c80c000391548204ca21f00c1c81d82009004880d000d820300c41e400a811150f151072044040c0940f0005182d00080350030780500034540f07501c2c0c480c110030000781c02080b40f15000001d941c2c9410b1001603d02d4070003601e080380421003800110002504200e4011001c1e80c20000924642d46144909003144201c4103194001010050402d888580541114042d601d28605110340b0b1030344004100e610148071010050306900c071400920382800d00c00203954120502400d040a07031602c07034200c0d60642d00b20340c0c001c444205e202880100c0e80b941c00018044102c9175841c00703112060107124900402810480d014103201200d00b9070103160802584900c0141c0310041c25240240340443c0342c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 634270161 1250 634268911 634268923
    0x609180c0d1d0c01030e0f10090515010e01290c2802030303180c190e0105120d0f020102090307060914031204060f0e04020d020a12021305010e130e 65
    0xc0000300d00b4410903144100c00294041c9280707140400808001c0c0580c1d00450140603154502c41050041c641d48080f014030078443c0010001e40b036040400c0605071840d01c58a03200d0324400301003103e0840b00050043c80300240c1494111003895508048040d031080f00d000c6840c06881d83c01120103000201920465030204021000081c41c0030380c25298000c00c0b0000003004080b030402581a00b0410001d05990a80d5422410343c034040400c86041c822403001181ca094101d4850300f800c410b0320441003083c107105a178040d02501c0d09840b110f50716801410915543c0e2405690740c020300c00844500c0030118400d5050b95032104d0010103d0780519601c80d03024100401038001c80002c08440140c1c0305c0701c0d00300000d00e618a90500308045190a1610300d003183c8000e55100c2007402c224003d00003035410307551030010781040e403c0300f000165512107400010300050100d0008600c01401070044044524410400e6022160282804241c66180b0070003c0c0b100240310010584503441c000c444c19620300b0000780c0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 634271411 1250 634270161 634270177
    0x140d08070315121b0501260405010908121f03020d0b0603211c05160f020705040203012d05010203180103020708031003030f0306050f120a0c080d0314090a020609180c 73
    0xc404d1103a86500045400c44000104580c020040200c071801d1650f07042d500d10b5000c1d0181e00000b400b000656280c50702a03000700f0a580500107081d0a1240c600715640014491200440300342290368a0341c1e0200310b405100d038101500e9100c00100040c15901d06110070312410301001004000358407440107000464100c20343c2d80c5003038143d4490100c5041c549111703490140c1d0146000c40c00c0041c00c0a0200d8500508024260031800f170042d001515803603500103180a041d000304400c910a541100000b116107800d2200c003d400e47c0d00c0030404c1980d0b004011034240710704901060224080000c01600a44a1100700414485e00001003100e45a0101c2608050302c2c400e6031034820380c041000040b007c1c0e400c103008055200040ba900c000c2149400b44100042c0c4c0c101405803148230400351070307118400003103038440c0c0304c80d8104100103145103a261040514200446500b9013160400310350655441c0c0030070350001d020f20340c0040d880c079540d5144e40c440644008c1e01045d000540c42e0820b904595900180c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 634272661 1250 634271411 634271453
    0x109090809150c0d02010b0f06090303040810020306010e100f2a0605060a050d1131050708070201061a030411030d03090605060904020303180f0d030903140d0807031512 74
    0x13440d43c21803040c06460522207000305050641d480710b000700030301a40007400e410740c91b2000708400036403901700b13001c445800c0c1d803001001a141e261080001d0440440484501d10640e46a190840f407941c002221098006032483c102c848890030070001503816561001007152030500f9011101044440c0d000030344070300d8060360744881090b6100c040c801a0101010006c043d03445510090445043c91030559000e00481035601c9250700c3c80b0103204c5030030021451005201d0351034904001c459500522840d403c080184020171803140f400140200424403840440600000000881d06010381d0f80c0c010142d0310340040c00d686951040d0040500181120303001190900c1c20700d00010040e00e00916114030407900034029614004010700d400310b0000e039130702c1c0a503030000b0009900206902c1c1d10012012a82c860f80751601258114200b9082048501d41c0048641e0f10408038440c1041d40020f480741c01040605010400d07900d074403804001c8cc00c40c1d402241001e95460310207018804030003d010a8200240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 634273911 1250 634272661 634272673
    0x11210c010b01030e030d020a0309061103070917190c030c15030507050a0f0e0a1a120c040f0e100801150512340f03050f0d03140109090809150c 63
    0x194251150ba10300c0000b543c106122401c0710346d4560300100110045440c0000b040d00403a9a24002c4a41e60f550b05900d00301d02004021860781c0140f5503802803c2e02075440800442068185581c41007001c1d00380f08941c03c9495100f0030040400c03e86405075505c403180c01c0c03049031560300c441017090601079100e0000c0d03b42804941180d000d60304407420014182d543c0310380001c45902c00c0e19148641010103030459100480011013403210218241d4110709a03186580e12054174082080c03491000e40350007c44c1d0b0341044200f00041820110404540002d00d18620503520041c000f000000b855003c048294208400b04150078409488030007601d804450031201034a00c09401c0e50b0310201210f001c2001d80784011009400000c012aa05440d00200c000300724184d217404e200039980009500403150381c0d02211200030b6100d801d21214680c2201803904109d00d40d59054a220454010712403440c205e503076505a9000d0140a4007152035412000e000181944203504580b80658809040c4400c80e001e01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 634275161 1250 634273911 634273931
    0xf0a0c0b1005010c030806060d06030c0f090510050d020114030907030c0e07020709021b2d19150b121621020415150908070605040501020d11210c01 65
    0x34154800c00c1d14410ba503440300e132041030303a800d07152032101400b855031002041c024003a00c4c0d0600c2c0202005107109441e1103000c0c500d0031241c1100b0003016046083c1090810342000100031085c820041100c07811038088501c15020b00044c0c1e44104134002c50340c1c040b40c00000b04101440f0001d0a4800c980c0b144000302c060030750b118014840f1010039180c1c840180c2125000b0814402c0d260042e20712081100e142c020044603080c510752a02e04d614840c1960010700d501c183c45003c00c500e40c01d10450170000e01502d004401c80b05140d2081c202114020b121008103018403041044540c007928405401600444109005070702d02a03603800810711031400395602c03280c082a4204030b96a68015400c1c42031010b5411106a030801010309139064035061503009080002501681c10324580c284c21040c0d845510905041148a42c14620035811800520800304000c10199900181500000030145041004600011130013400c0a0302c2d68100b40c03d6400f5a11041469210755000313181013006403000304444c030b5917 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 634276411 1250 634275161 634275181
    0x3060f0f080d0f1b05071203080907050105040506040b0d18050318010f0e060c10051303020c060711010809010e07090b090115140309160f080c190b0d020f0a0c0b 71
    0x1028048000201e010040301d0128502d607201c0c04c1c1291240003903401c0c0715210890b03680880502d400541c0000c1552050201e120420300084010700001e207071561410b410100403420038030841c4501036a460b030005481103581c080da400541d000485c00c0210000c5a01400d00c150f40c2c0e04900c1110a8021038080d03c1c000b10b41c091460080e8050303050301c0324503412070f8076410043d582e00800031480b0a40a4030951266104c610310485114000c10a02e1490003500c0b400d000f07280800100134640600700410560000c01c40c00e03030000c0890031003407815048079500c0c401c0d00c502510034040f628040340314241c400b103003628503034121180c01c40e0143c444541a130f0b640c02492240c080c1d1038020b00301088814808100100420000b10381c810800320445079001f001c117074100c0308809190310100c07544116003014004e050080c030120003580710444101c841c00792000010300b0400b640d413041504402300024246130810341e41e0141c400101851100c680c5812071480d0240c00b00703852403400c80d680c40c1020001846041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 634277661 1250 634276411 634276427
    0xc08041104090b0a2c24190209040b040f051503010b060d020901090312020d1106060f0f0a05030307060207060e0a050a120309021003060f0902042403060f0f080d 71
    0x18121074032401e207480f000c0203c0000c00301c54803c08003420401044405c2a04d41d500c01c409005980b80061281c0201c036560701da4088503100005010300504003c0c416003101500d2505000e00e102c000043c0d03110082000500181403e4150039005424480c2601460850744d02c05442000c01c004e881011180381000c01d404c842c101e2210b140c1c010340030310150b4210781080e405000740f08410305011030469140e8456400401c0c4503006503005900c140c0d200030703603180d1010061071119281d03001010603017480d0340000c01910101d20400e004881108060405566000c03a01008110181c103881d40c900351414010041d5110301030580d00701d801c207074842c0b05601002407441105600000030f03246841d1280d40c3c03481001c402c0501d0408050311032200c0c0025944a000000340c03d002d40c1c800003290f610788405503da00d04250701c0f2100c2d00f03105000030455030407145904010b8001030f002c80500342800320700a500a007000d800c541d207800050345001c203484481d140a0420b40303070101c0440ea0485040e81c0101c950700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 634278911 1250 634277661 634277663
    0x50705040b0f070f0c0e091b01270906091d06060307090504110901080102030a05010501090b041a12040302076c020f09100b0f0d0c0804110409 63
    0xd004000800851014a01604000780b0420b8502d0301e114030fa480c4d01da06290340740c01003203859141401f444002242004054000203051700400780c040392a000103818042a694040b0f2030b8060b5000f03094486807410a4003028203030f502c2d03041001c580c032414410020101031002d031110941400d80c4240012001032031502c030703103801401080320a081142100c0034290240003154a2150041d112480f0b656462040d800b03096007600050b103910340145140291881030317200030b060003034021040c000808080115400c4d6111001071003125044003c4550491003040e144408041c081e44c28170040660115031081111800307074448910781c009005400f0301c030a000e0410b0010700c0e044020031007020044a114070100110b503c0740d000345c0303805007001801705506000315055124001c20510861400656421105400b0303607407120f9503c4c14a0301c1030a245094000c104046901150f1030b00050b0001040700c0e00300310450380c20320807491550b0340900140f400341c40885003030082c466500550304152085900003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 634280161 1250 634278911 634278929
    0x141501170c03071214010e04020f151b070f0b0901080c090f01030f1404030305180c0907050c0a050304030602040e09010902130b032d0d02060408191b030f0305070504 73
    0x152541d07041a241001040c3e054035926440300100c410700da11100255009047d10340007280b4600e0144104000951021620b034815139041d40090410507204c01954900840c070000c076400200d40c05400c81c170340000c65111804112440d0008151076903417070060000402c00b038035000200d440e0020310032a02c0c003502100765004060103003011b8556100e508032001002c40603034001130300f1134104602284206c0485003a0042611036090040c000b0081c1e040102000720080600040000400021031400c0050903160400801041002c070007070003400481c03041a404000c43c0d945559a00c1d040e4080d4000e4031900450749001d00009004c070006000380c4031131540c02004502401c6400d20183d0007000307099040b50f09441070b4105c5000b0704401d005045200c001c800c01c40c0c003424540c0342000b0315004480e4001c108640120b428003002421510540f406401c5204400d294400280c01c100c940c5170b50488018001400303040503030145078001c184081000d60640d02444517943c0d03030b00103030385510541c40380e01030f2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 634281411 1250 634280161 634280167
    0x11012f0c010203042304140a06050f0402040f0e090c0307030f0501051302091f05040f020403020a0b0703090b0a1e0305070810060f0e0301110c030a021902090f0402010201141501170c 80
    0x1070442c4100b1524605c85006000060711402a102000f0749101220041249640c410041c001441c22441e0248540400c80f002e51a0504292015000030f80b14843c0d01d01556000000c81c51149045c860f86100b200050b00701c1d10740740c1e903a042c47c0c0345041090106031455441c11000c690f4403404018190a03042e0040c2498400343c0b58501205245010301e400c0310032121803014086002c2c0d465000b400da5214800d400907880b5400e6004001e5802615800001000702c10095800001d400c83c0d500340407100d03498aa6501c50b0040281030350042011920800f031320060341d180740101d0303425511440c000c00c2140d880b2079550369000e4801200428901070b480c0414415001c080201d44142250b8981840c090000301c4c1c803004807103403240980c21440c0d44017020340000c1450120b46504011042c0250000800080600d00c95000b049108a000c0d01d410708400032000040d0959000750401c482008401d001844580b8043c8006c420702000c14200e00d00081042d0b00c503c2505441d09804c50241c0051805031b45 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 634282661 1250 634281411 634281449
    0x80310050607121d0a26010204060206010614090d0c14030a150e01090f0b190c0507060203071b08041505030c03160c05061f06030e06010311012f0c01020304 69
    0xe644c41840c00c00031504000f03c0200c4120381c41d020b0a50008041c014900203900840c01080f8800c4115180c110700c1581c41840100035480d030014800d81103c81a080040600307001001845045c0304005040349c000000d50b64500030404414100400c9580c0120b9501d40702440700201a02c503050200050603101d4060312140700d101083e8801c501604a40300002041007040d43c650051680d004000d03145c43c2c4d1f500c8200300d11122908803c07500d00b44401d078100f001620502000d009070056643c0988155404000141e19a010b0741900d00c4525100c450300081120b42d15001c07115511038041e0030119400e40e445841080e00450949006880b4145070301c0c119502d212001d0200c802200010081058601d022000700380c05001d118021000c4240f065161041c60340441000125a88001c040600c0c181c035016080c00042012410340342d0007950881e8002e8840012140ca080528030305c020340f61140c0c41c62a480000d1003104070460702010658281210150040e030f160701540c0b140d030701d2043c803c0e41400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 634283911 1250 634282661 634282667
    0xc032403210c0109060902040b0909060403232706071505041109040b040c0b0c0a1112030a0519170f060415090c081f0501121808031005060712 63
    0xc4240080d041c0281c10b001181c500c09007541c1081d2019070301a542c503450007007581054011010b5520007914015194101400e49991307500b00104003a0401c1901012a0401c2700e4034440303903034010b081c0346045403600382200740b840c491407180a007942c107030346074129548a508040c01a260400c3e04142d00c21100c0003144c45820182070300501c2241c0704014105504025070f56007025500440c007403100965a86810f2a00146640094200300d40c995010310982814090003c2c54405a50340400f651600203013041c04610210701200300680030b404003140c00e8070015030100c09080f9041008001803044650102c00f40c8605030400c0c6240d190f100c0d054001040c4032003d9040355080343c0050800268400e50b00640905030000f0b4200c1d039240d580310062400203a82c0b20f5480b64124298500e5243e11194074403000c00f1201c0c580c41600c1c18042414001402c0000c1e80d4404903c1c41100c01401c000000540303000b00da56030044860b6107403d10358100215440c100344003941c0042c0d0340500c40f1206500b2030351050b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 634285161 1250 634283911 634283953
    0x611010509010b03121b0106060c0b09032803150b0d1a1507030e1507030305070228110303130609090e060123040e03031902030609060d0503070b0c032403 68
    0x201483c0806c186030a2190244540c50080c052542d603068404c03e90320b018011800007804019199009008000d1003015038038030000d1400c002080d1018103421340d10281d01030b100b0303189440500f01003c0c50025452900c14000c040101c441c610801c01d0038984400341e004114450030039a04000c044180d03030990440c40c0700505c42603000341480b404200e8084c000400f419141640340303142d8540400c00e030081581500480b50001914009071240081d0380c0c005095040002510584842030340300d0300c202b0b02034400182242401c0282c00c4c2c0f80d0351628009103180018091181400182c070300b00c4006107015030780c4500d0200c5080311005d08056464a2101642c0d00600100202c042c0d01c1041d030340a20766a9441031041000744240910b8691034094040b90040d4500700a00695030300403c00c0209031781e10700d21500da000004075485010044c00741080f6285010341e6a00400e0281c040040c4148a8601c00155100b9100c00c10501d103004120381000801c101c90420654143d8084c010590610690a0700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 634286411 1250 634285161 634285177
    0xc0414130c08030c0a03080106020613110a090e010203070e1f030203151008040203010c0306030203070b0f1201080f0c0103111e0c010f0b0a0b03010f12020a0e010611010509010b0312 80
    0x18001500d40942c20b0550340b010b242c1a01545c40050120300301500001c4041c01000c00340023802c102d24045c080048040040140144003230001180e1002a40d510b5201e0400341040800802561068078040ba000354020f480a40105a070500d40100910380f00380031161461002603106101300c510001503020790000340201002c400301031400000c548940803c1203c24445a0341c40f8001d0400340149421100c400b0392044c10981441410b00158500241410440e0f29140d86d13540d445103551130145c414000c041400c00441b4068000240115000992400301141d074016995903600400041d000c031030300b0761300c0d8031f800b0b14040c802d841c0040032a4510001d0362000d81c210a00d00b060b100b41103400c4900d0f2207a61040c069441e01b403280e081c00d1170605400a4071694100c5891075041c02114a1001803900c03c1c641400c005501680464403004071060041101040c0c10103a96100c02d40502924168810340c0d001c1e41c602000221001814042d54903401780140103030811807101003480c42698042d01c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 634287661 1250 634286411 634286423
    0xa061706030a29010806090703150b0603100e0a05060d0b181c0e030a03020a0f030905270a0c140703021203070207050a061d1309061406030c041413 65
    0x30705040441d41580c4108042c030075540403010f80d0b4451051a044080b0181c1104c1102d40c89141007020310903002500d9402c0d241c21181035410314000a0140018240c40d880c1c0d150808004810311002100c031200d25025210b04109030440750b40c4000351541280c1044440b40d03400f00d1400c0c80e24003c01c2002c12a260400b100c0c0b45660550580d0b0a181407074409416203001c0c0b04540544c1607040c0c260300594400381c2d42000c0f8040c1842c0c80568400a5855a191002502075004103a00004250003070f07e150000b020042c0c1a810928098007450b441103c0b520300c030b44818034920300083c500001500c12041d140d43c4a888101d080800b46443c20f2958018490403010340c80f070f500326a807003210501c0245108880c070b54020083e031030802c0300344000341200340d2110060000d16100f81ca10452a03842e10031a07140166000a90081c0a528440c040c104007100a0000352800d14581544500c0302403191240c0740940c2107030703d4101918240011203140c104000d690751441000f08003803003642c261607440e4a01646c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 634288911 1250 634287661 634287673
    0xc12050307020328020d2a06020f03071a131401050402040c0302030f0a020913090b1b0c030306010f030b10081f061d0d0506010b040302090c3a06061206050a06170603 73
    0x1c00147d004902003200000c0790302c003011080040c940c1c10020107a00d0101c940103941807004a03a601002d59840d0382e029010701140d500001d1050b41f45400c104107a03034000c01c40010780c3c81e05500e071a0007410b007500c050703004a00741524020100c0c064001ca0f4000e808aa07800300031581c2c2c68030300100941080380b4803988a440c1e41009030281c0e000f4003e490260b4098040100b02e41440f0744c40803031410820380c1540d518041031001100e510380c04070659900c0f000c00e0a2004680008410441c014455081e480d603000d442c034001011400c2c1c2c8180030500c540e09001d501101ca25140310359845412161280b00001251500030300c40782c2240d042c200780c400c40080d144401000c000d60f203c60501800b40c020281c0d0070700105081003907180400e91a904041d040c800300d480d020b121544c02059480744205040c429048a514101403800342c0c194040400d5061001c00c2440d8980c0c1004000d0516001005003050a2a2011609182500400f400c48445071121510300c0800c04207a684c5520044c040c9905008075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 634290161 1250 634288911 634288943
    0x10e15070506061315030609021c0501050601020c01110a02012a140c090f06121c020322080718150303050702011206051c0c12050307020328020d 64
    0x505a00d41c440d5002d400740d85040000d0010001c010382403a1140b506205c044601c8204008010099170f40141010030000d00034000f10340000007652a010f03000e2141c038007820620006500260040314240e00b81d508152814004540c010045481c44426400080032600150b004000b55083c2c0e0300712502186d401500d02201c3c00003400c1500381500c624100840340b040a641c00e0004a20741c0c00304580b2104e090500c4012000750b03000060041740030b404000c00e114030303000040101da00046e48600070f07c007006804c4407000b5226046400c00f0300860b41403881d90703162208601c00300d00545940000800f00107141032401c000c00718203040b03c2d1515690b5401640040c010719542000590b0080c5c0382c0a548902c10720004005290000002c0140c1e85000c10501a0b82e0f6050a07016200036885804050000d20b41000c80d10341e6055800000c420381400a010104440840503240c2e0034021401e462b510190342c6d21200b0380c05000b0750080094101c0c58200c1d0010300c1c3c80c1c0280c489031030042a000e03d0311480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 634291411 1250 634290161 634290199
    0xb160c0203030a03091209030503030a0903021c030605270a11041505120603061b090105090306040f050d0f0f1d0603070e12070b07020d061506050304030311030106020c010e 76
    0xf03c1015600000e850301050000d111800240e8599402c0b03c0c5031096070030785507440b403540368080139096407411034807007500209244c0f003004507000c00d8024400c00c110541e01c00303902400030b000910420340100b80c4100300c6e12001c14000445041141e26104c00080ca544000d60034004246860003e00003000a01c03001c00e1500c550982650300c41a00d4403940c0d07031150300412400d2400c0005028a11940c025400c228a5044050200c0d81100f409036110351112804401603800d4000c0600c026003500c920702c2004140b0402a4119291901034801c3d1288002c12501c00c603800c0021481c0f610118086403c100505446101c0700c2580c03812906200514180c80d030001785041d4000d5500ca00010003023100380d81207103045a521900000501c005010061810748008507902554001030321805444900d181409900d412040182030001c61710217509440741e202810b00d800c144c4041d400240b4084200e402d120503101101c1c1a2407003a00200a504200d000440d0000502c484e526001103d42c0002d0341d184e40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 634292661 1250 634291411 634291417
    0x1c03090c050405061503090f011a010c0609030504090212011502010c021209010215010b0a030605010207120f06090c031407150e09040c050411090f040b06090913021507030e0d0b160c020303 83
    0x5030038000380000b00c02400704a80ad592400440c244a50150040603200340e0700100e010f820710341d101c20f01050814482c10196250702403644008281390001442c0305648c00300d111801c2c141c42c6014941590800c1c0000128201c554001014016a112039240c06410f07051801402c145c00051049410306514006003e40d402c9003031744100c4a0b0140805d84444141d09401002c010b40402e2005000c050316246412809041d400d40241c010008107810405102c844c1e0020996260002c10407075815a40f42303031045420100c0c8800030358a00038030300081a0b00c1c01c003c5c405c10191140b03944510f0041e50130b00403c80d610381d0251080f903400740180000115500c0b68003554003400304d0390b50303015101c00300541806200031100342c0300c502c290b02e0f02c0c1d0750f11204c1d031302c00701612001703d025030b641031855680d0ba50388596440030343e90103540124841c1c111340700c1070f14201c02441d02c1d520030380d110544181650140022000d18200003081c00440100281d05030400344003040c0460070529084864644580100341154 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 634293911 1250 634292661 634292671
    0x301020a0314071809020705010908030f01032d06050c0c0a0311010c080f04030507141501090c0806030a1b0b0313110d0305040306020901201c03090c050405061503 72
    0x30b440381042e441c03425080b0030190b842445804c0540c3c110307030341081801d68480c1c18040d98175880d07804103124092080075400300301156400340210395a403d0a00705c0c8880d5038401d00c42100c0380c01e04016065020351030702004010841410308500c2912800b65030f584003800c001412100e10000c284540c0e00f02c94420401c4a2013580a0384448010340c440149003400d54198441e43d4041c44120002d101d0b11111800b22241e12607054903205894411314501401c1004c180c1c0c0200c005d5125130a0030a0304410a0000709048860798002084400c03100c010645038603170304482c1a54181c00902c080c802013044032039810b2046030581000141c0903203c50010301550030640d0350070204850038004404001140240c070b0207568080b00d903d241e441c12941c0040080c8554000101202c0e00400d903100700d42d0041000072410b00c0b10794041019011100c0d4040d648041140002035090350310344a0701e2041303001c1e1251046103500085100301042c00d0806102c040d050240c4695040390300c24921180c141d031900044c60181c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 634295161 1250 634293911 634293917
    0xf06030a050114030a03020a12090e070503093f0c0f0c1003090c06030c02030d02070317070e0d080309030c15090c010212040e0907090c030207030306170304030b150301020a 76
    0x2941000f01144403c1c2d00b6159660199110550403030229400203800020264401c010f00d58210b00300e102103c0803a090360085020703031200000e018145801801035849003031302c08111400d1161941d45081c4407045a081c1080440030700322440c0f210b01030600803c04410303000c800300d450410000019072821885801407211130b00b26001c00b000a280030300c208c8000032003621b0140a230320b20320388446c036003036900c0e12038031060582d200440f58011f03009005541b0110080d0300c0071034507001c235410003030441026a2203898110980c800040d40c041d0240c488020400000341c04001400c400c0c1d540c2c2c10a507400074018440e21321003071025200b110300400c1410010300641d42da41240d0b04040c0c1125103420180c2e400d8a0640d00507012851030311341050143e40407514819800c031969190f240b0118201a0b0a800811815041070050403407130340c01d0380007040c05610945e01000000d0740d8941413031042c4514421014140c00c02c010400108030349580d9640c020b80c400c41010400c1c040440040c1c03ca03072106c10b1103004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 634296411 1250 634295161 634295171
    0x1104050603070b21060301060303140c0c0301050f0a0507140f181003060509070302070f020105090f0909030a0f09050d111306030c06030614091b07020d050304050a12051b0f06030a 79
    0x640b00c0c03294102c0d80001c5c09800900285007182e80240086c405d01e10300e00f40f030540c04990703001d60700c208020b100c0600c1e1014008008504162600a44002c1d04440c103c7c6201d041c41c020031801403041c034403065801c1e40031001904141118200d001c0540c081a01003210703041166414155594120f8840c90302e031041d45001542c5891328050140c1d4bc2e10040000081c941b0611621010410701c0003034130451582403078010703641c4440c00000703103644804152940e0441000d0f01000303050000000100006902d68032101000b120750601150b052455001d5030742c00580c0480e12400088141300d4028010b0002422072150200c04000d0740200c454039441581d42c4201d0704400c016464041c49204090215440020764041c811004544000c502800155070404c001045a10000f1201d0a03200300079030003050300710700b81ca0904240da0703690024041c062098a810000080c4404c084a4059180d40d00001919000680e20001e4001e81e01001c0240d03003244c40624013900c213644a200440c0b045c5000c0381c0c0011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 634297661 1250 634296411 634296457
    0x40e010504061505090603040c0b45060c15042f012c0613030b090303070903110109120b09011a0616080f0703020d110a1104050603070b 60
    0x30aa50746580300e46103920b10f45140d9201650310100301c580b41d00003510204e40e613840d10320b8100c509031081c0e03005070084140031402d06801c4681c1101039042e115507050015407182c0c0114258980d8a884030070390180d17494404000c2160030040d001e0110840c002060303d011050203400103051003401c0b5011200010845c0350800c0d00c04209200c901300c82440044810001c40080020381824a001541515410301ca40c0d00a61410200b809894141000d0126600d41e0340072091049509220b0004031000701b030140005504d82000070640e0b00c184695030b00c3c503140c80d1458850081c500c015400a40c100107c403840403075412401aa0018207501c907610090300d900d4408006e90031560050000d40e51034a0703070380c41c482d51682d03003500340c0d40c0032902161981c908004520382000e0621a2000808031081e001c00c29500b8190081440d01c400f07403032a150902504101e40d10075854080100000f84041c520600c036840a01b070607881503603c5040078007240e8000d610b80c2684100c94112035001c0c221040d1005c1002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 634298911 1250 634297661 634297669
    0x2130b0321090a0303050a110d0516050f031c0f0203091c18060917070320030114040b0915040203060103030c0f02090103060b030f030c0304090b1f02010b100c0b07180902040e0105 79
    0x1d58023200f0710160680602e41a8001e140d0310440307008a0724080006009001d1005c1400310550203560201140c0c2e039004a18031000c000b82d010044000f00130301d04814103c415403140212485034a01a002c0c200001c680880390b801e1415800040703040188150b491800c500c0c6103030401005d05a10344603c041146410542120038011680b505007c0c0c1101404100040408540c0410f10700d0205009880c610980c0100b40100302014074003455a00c4c003000d010600024682507030144074890103643d045a600030b00a41146002c3e50000d426500010040010900c03a13504540c020b480f0b1419002c40e5a1a030700003c6a2103020b03082954400c2c0c1e11580154a890100000c22481901101440c01d0038510204507480380124400c813110951034440e4080b1941e14154004003003107081240020064141600034000c0c01d4080605010f124108101182640505004c40d4507990100d044040c5a942180031149034003c0c640003185200010408141785665002500142406c02002c0f040d0f0f600d490104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 634300161 1250 634298911 634298927
    0x12061a010c03080f0a0e01110403020f150d092325080304380d0c031109010c050f0d0201090b06060301030c0e130606080a02130b0321090a0303050a 65
    0x2906004580920000081c2c1049000307501009501c03c1c4400c03551104003c00251003100c80042855103400011450047c100f005001524002e40701c0303840500b02c1d00117010b982e40c10404a07008041c014020740d070b01002c2039000340b000d00340300f41c0b0394030171071a00c03280c01e24180c080000c0d82d4007403600120040001e200340d0034200301885d4405a0788040322803515120903264805c0d402041c2000280740c8005180071545045560280142445400361040c401642c10311034008c07254045602e420085800245442401601e0784e800321004035911300007480c401590400c426920849450103855500460b1401c2400001510f106070380002c18480803501e40800c08503001401103119010600040c00460004190201603d002e0f4034100314603180e220203030419040e10000146840d00703013900458004c80104a05422031301c290b07100d5842012100b01c100c01d41e8040a0300e03580650000071041c6007910f00402c080d05981c5030440c10341c03502e8a101d01203580141c06030030541c0483d800041e03190120f81e01c5000c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 634301411 1250 634300161 634300211
    0x40e06040b1012180c03140111070804120302150916243006051c0b150f03070303020604050f0a050a020d03111b0f010e0f09101206 58
    0x12201c2c0c0c082030b052018080c01c00c426145003189540302c3c0f2401c140041c4101d10300003980c202400000607075903444c01444080c00f0b107800c01065401c1452600306501da0905488036154012007aa081504044443d0b051000b8580c09500714420b4040e02d031301c641c00d1403070701e0f9014020860203401a05540e002041c00002c1560200c0f004400d8141004070a8003001d041c1000440a890301c52120342c103000703024105820302c10280454024580c0c030014241e5440c1e00031004c07140c0c25107928051600c071501880120001c04805407584602100140c24041c819401c1c0201100050190410044000200b07103010b081ea00100e0269210070148400c0c03144c1080100c0d40740400b0401000401c2c2d00365100c54035440b2654009014608203680001054055804481c1058104c41100c0303d00803070320060303d94038480113065070080310035101903007141d480b56040c450811400780148042841500c07c1c07080d100070007040d00401d603c2d180c0c1e01251030b801d02c1041c3e0303003424081c41000c82e514410440c9103103500c5075484 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 634302661 1250 634301411 634301419
    0x22b080d0b0d020a052710050f0607030807030209040e0102070803041112120706110a08070906020f070e04021206040f15050402030d0e121e100606020304031214040e06040b 76
    0x240302006a684d0001a0141c5506842c8001880382100e551003804ea213020044c40184220820001201924240c0c002210811540d40d5a001c0e80241070258902c981c400143c0001c0c0500b000070701980c0207400900140002600020381c404001c5503103400c84c2c05c5601b08444407800041032209100380c038584070031614400c54089100f42101000c43d41d03200c9582c02d02e60900c00c400300f201c80502804ea84a8080040e40c500c0040da14003544c078000b004103038110f80300b00105400b40404114a880051740951044c03a400003403075040c1c180400d446138580010700c101e91040c02042a1450660705014503401603220f143c208851341113926120b01c0b0000084070801e0310514000c1003201580d0300251000e802e11881c10a01da03030030105408500e14a002c803038a42c9140c45850b4080c0f45000b082003080ca444c2d90490180c0e0302e000007581051081d41d010380f040d8070041e40184004d0000c03405540594100f0901424100c400d0442030b540c050307094001c0e43c00214842421401c01902c0e042901503582c089000311 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 634303911 1250 634302661 634302679
    0x901200723040e03040e0c070212010c0908010b01020c120307171306030b01050f0a090e010b070213150b031e0f01170a02011413050a0e06120a0c03022b080d0b 70
    0x8007940e0350700d002d10301c5006d0b2400440700205400f98400002c5070541900600107010b0091a000158043d04400c0d6481c000602c003480001074410040c42884e554000c141d01411142d9440020007440b901602c80300509408104041000218056a8002200c2c8125002a1140e020080d0304420215680c010003e050400c070703242109a0b4402c04603030b5080100342c0501d1f16002030890031a42c031501a0001040c1004007030011404607030420261032403501c00c5600101e0f4102511421065540c9240e80c4000b10000c43c10501500c210314010b907600c00011003034964001425a0300c80c2101c0c60903128035040d1003984006020b8502c01050f030b100c01190400040c0090301d0b640d80000d0000103c11966000b4020204211425444107500c40c8001c101c0248454a002c1c0c68041300101c0d09000d48600c1d108140c2401a00101040850340e0603c950300003414100041ca150284000c07d0110401c42842d100340b2800640d880c0b40343c3e09100c024602032544613403640e20390480031045448a00c072051081010ba = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 634305161 1250 634303911 634303931
    0x80903030c0304230a0b2e0303030c02030c0a03030617060403020d0503070e040e0c181e04020f0414060411092101020c0703080d0507090605090120072304 68
    0x9a82100d402c264040c62800c00c000a100c003112544480e811081d43c03030300462010741c041c05400d82e4224080c0052124400f1500d000c1d0038584141e0070070264801c20305036070b0481000424003e500c9107102c1c40c0340e0700537280361a00400d01d140c1400c810050450103c4e0342c0700340901c9440c4181036218a0714a050b802840c89080070345004e5a11414240c00d01d0400c2030001c0003481941c03040c1c2100f140a50080c005201c1c04000d03103503587e141d10820b100c40d4000c44020701e80c03d42417641600e4090203660075403240b07101094450f183c002c0440005105a070080344099014415889511900360007160025260105080c0b5000308002d490007250880c000303160520040d0156543c00a801d8001d0342c10164a000741c101c8010050301900a02041740110b0142c403000109000a00d40100b50740c00b0f1484007004181d0302c020050701c40540303500400f80003c0b014401d41200c5e5000d401c086a00c00d450310220000303105c68080444c034212460700b0032441162604006420800c1c40d96100d40340903001c071b8062006000c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 634306411 1250 634305161 634305181
    0x1002030906060925050315060a1b030912050a2114070606030812011d04030e12010905010c020318120303130c09152c011206020913060608090303 64
    0xc0030b859a0321036007941e40402ca60041a0201031340000e980d08100501c100c81c54000f40450f001200e031084401d51011101c9024a8080103d4004400c1d0380c441c155007031281310043c2c91084800d0012414806004404100506882d8800050701d00c5440180b0308100c0a00e0558054190420665001120322009251054020480b00250885180016210740050420402908280c0d0000d0110394001030001780d038490b0808a181a1881c44104401c14030310b204030b03400b401030202c401400140c1c040340030b00d88901c0d002e240c4414640758000042400a4951075860844040c0c04038400980c1c40001c0d10895102c4521003a070802070111814005420540f032025101d01c001401d480342841100403110411403d9406880a0802d00608000d07203050103040c608502031501a002c0c6d0703d8202e404034240c03a101040c10588a0115840411243c0d29040700b004403840c030100200ca8854091145221a460707207181c1416000e1000404501e0074a0f2000281580300043c20711605c1c0e0300100200009010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 634307661 1250 634306411 634306423
    0x320090411070b100e100317070f020a061805060408030a141b0d0921120201020405130b093102010908030304140709020a021513020a0306090510020309 67
    0xa0a8401140800404480e580700d803081280c0101460907510502c81100c0c115540802618004560b2541c01e480750704120320074050740d100040c501e81d24110550080d10204000c2c000e25446800c0340740080c110b03540000c2811103580c001400142030301e0f420742580003032011140e008010559100d4a4141407201854491107440d511400748034900f96011095200d0740212000140f01e4034040b02c0014182c01c00580b684034a00c241c000103202d0003804544800811601c3c05840304c20008401c8400803503450f01c01c0d05003032408510541d5428000041c4039110440d90001c43c00800200040348207200b07013000300e0804050400c601d11001c11100269407660091851404042c84100f03810400092004903218403450300458440d010101c10704c0b041240c500d91000d15000f50100f036482c01522105101c0480c0241904440180c0c46501c1551440e00c0083d440d40d04034806088d000b00c0c080f01e6401180030300c445940b04441c1c00350384482e08000d0280c14080c13243d00c40d00185096156003000b90300c2e25581c031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 634308911 1250 634307661 634307677
    0x103061a030c1b0610050414070807230c0703140c0a121509060c0201050114031002073002070b160204020a03140709030c1409073c0320 60
    0x550001010481c1081182e0003a40f84901c43c1c0c1151190702c3c0031241c6044110319407085a014504000c1c82c00701d420001901203104442c039540c0c52003590f40c6c4000c12101060752021020403080042892011511000020010340c0c0781c0d10000e2080a2540c0744c007150100d11249c0c111f50b590411500b00c1040c0e034480b07400008803038603415901884281810f0184985441d00c022110403850000b030041048030302d403c00c901d100081e800801085c0ea03a00000311881c10401313241c07641500031980c100c410f00010750103044036600a1403500034080490814240031b024070051100b4141480c41508280f41e4100240750103080d45d40c09107030400c0c601e0707180c807019101c4070f500c002e101e2a0085808151144260311214202040c04890a05410407c0c4054965065070005503800c8140010118107030030710403640c584400016002c0210703562602d0b0704549180400c00c0c100030005910854001d1503084440c030340f943e440d01601880880000f888013a080361010542004041c40100c00010300f6814142514488 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 634310161 1250 634308911 634308931
    0x2b020d1d150f190903030f0b030120130509070203090312040501080112081314030c01030b0d02040b030717070603050603060603120a020c04051008061308160201110d030b0103061a03 80
    0xd61610f41c08403100e02580141254007500d80380c80030050581c560403036110800701190822800180c00140340c241d5003040c62001d914680c00313a241e40e030070b00c08100030410302c004884c0e080d000c40d03202c0700042c0c0c1c048001e8a024005a1002c101c40d1464a8280014441c8641ca82502031502d45044000703484c0301e00512079040c81da0154188141401100d6003101d41c180003102c00b0203040b035152408070454082020100d400b901c00d01d0317110495940a84280301400f123000b030900078048900d900300005000c044e40f20076014090a18006502880c13404044100d100c40c00c05032116a0503c040103088075801401035101c1d501480030701c0321540380450704900418840d07440750b940700e407200016850445450703c040c1d0050328101c20015000080452030044d18105030aa41d19501c0e420700c280c81d44000c41e100a0200002000241845d0b00d0258001d00c916206040400035000350702206400c1a601417050f10203c0d4503640c0368009981d05104071320140152401064100c280d0545002d058000144100304c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 634311411 1250 634310161 634310191
    0x40e0304060c030f031b020d0905030123041a0a0b04231f260f0a08031812070b041218060827070e070309082b020d1d15 53
    0x40b62291b0040c10004615007090080c0c06400c480081d80d40990803600000900305203000320b454601030042203d80e40720361040e02c03940b0450381020482c500c0043c1007141c5480040c12480800ca920141580c03040d90411b0001410130124400d110658030041007918520701c1601640c54400c500560054210194501103c00036003404914201400c0c03941180700030107a00c01c0680c4c827005d0b400b0102c1c2c140e0540e82d416165a036250801465031b58400d044018960802400003d004484c11808400c14004010403a00d0f400e18099058805d5408228141d402022031010030091010b03485100c2e814002c285440000d00c000700810403042c40e064040c01c1c040013900c4001c03e0a5030300c01c204064240400701d42000c07401d8120800550795040c14803500e0b0480e0409400102d44038024407840204d6600001c42c60724000a0108140001d2029004201144019000805064014800752a5071040c0b040006010f00300000f1290210110000000386d551042031140d8208200740f1242e0340000400242d412 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 634312661 1250 634311411 634311437
    0x3030c03060819021201021204030c0c05090c040e1008120a0216060c050709180809040207060f0221040c06032c0706080601172701050c09040e0304060c03 68
    0x9010698408605441a4022941c09414028080302410320840d45145d0b500c808200e003609030301645d8100800751007800c000070301081c0280b055145035481040d409440783d807168001003c9290960b00b0b00090b92021a0500c0441c520218540e00310203e1540755038000e180a1503030b6a640701118070499405008a40700408500800c181c46002107598155080a601c507007000313200040c024010b4515200e00700b400150000c5070301c10038400e640500f55461502915456402059000011003a0419820050540410031a00c0b549484038104072025a0b1041c0c2c1081c0402e40804160445000382d03840414400028074041080c0201e40300307400c1c003181440c40c0c041204002d20000c5a03010080154500d080c4440300081000c2c6c09844803071702c89500640714100116101c0d802c03070f0030041060100307a01240c044440c01050340d604c40b030052540014100400c0c04142503071000c0da10745864482c04520019a454980a08659010010025400c141c5085801405000310aa01034180040e55014030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 634313911 1250 634312661 634312667
    0x3060605060c0a02120c091e0f040302070b032214060c090f040c0504050d050d0f0801080607111216120c020d06090516080a03080901050106020d0302131a120105030604020d03030c 79
    0xc242c5001802d00030136150107251054050140304455071801d082e08e0028407460030800026000d01c0e0150b006141c098200049801c00c0d900203094120382ca100740824980340340d40b170301924640c03500c00c181e03060b00e419140510302e1400300d004d41071204103001841440c0b00c503120034000d00d9020343e0440e404100070340079941c00c2d41c0078491904055001070f403507075040050090004140048052554440b190210440300455040c48280511082a001a40881c22051007114600300700b100002c15110300396a2104501030590000c8074034520001074000700020300c0101045c000160449080000b80ca503030795400200000840c1c0c0300101110f98643d0000180321003003000b0009400c089510b5107441d0784406110703503200d000d00d60444c001442a000280c50002c1801018101d403000e800422001841b000c0c250041d40000207607040c0c244098100085080034040c04142c1da068621b600d0381e130f030400c0170203182c0d1081c4142c020300e0090380031f01d061000580759880c1940300035416103000919010509411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 634315161 1250 634313911 634313923
    0x50301230f06040609030b010906050906040b2b060b0301020a020c060c1f0f0f0b0303091c08040321020109020a0b09040f06080304150c0b010e04020a0b120103060605060c0a0212 78
    0x81d5822000c0443c01084554001450806030b9002d816020100c4ea03a0300940300075180c00340150fa4201c444500450040d04064201300d40388900140705442905083c00025000003040e481c086443c02c0500d07a00741805907a20466107a94020b030000d629018040030042d41c0e40c0c09030078071580a51400034844a0808041c0b00c0c0c000c0801150b01a20f101c4050b0007400005805900c4411110a00e00a045503002c020f5102d580d0149801402031400c088812003080320030000a110300c101248507603182800074096600520155111b030074110b48580c140d000189010801c454103034190380c9030244120159442880f030b10110b0300b00d2002c003036440780704a0201e4090009840040c004a040100110f0504408400341c01510a00980031050300c003006c01c205c40012024401504100b520340c01401200341203140703168000e00103040c036899103546000148580c0e000041c61040707034400000500800602d0f02039000140403c5440604145415142548410f07a0f40b000901c6412140c0c08410707012342c24002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 634316411 1250 634315161 634315189
    0x60921010e01020a08060301090317060f09090303070f0207030b04060507141303020f061309200703090f0603090503160203010f020406030f0e010e030403062c1c05030123 75
    0x307100140d035034a0254080d4106842503804204030700700044040c18144185034013250150b442a514207420656400e4050026103410b4014554005210700c40d180c90081c54040d03462580255520316000100603e04060905142c0442d000300000300b002c40d200d040604e0f0001d401002c001440d858481c01980d102da003105100148480c08a000c0c0b078000d03000000c603c03c81e402a174080180311081800c04c0401c0c4a5420543d080112400041c4214100759001186050202440704005000d907100a540c0d600312010031400210610003d10000c055000410b000348054201488030302d030140d43d03454490080d11400e2100c240c0e0824401d003590790135084140c0301d2866078400c40da160b803140001005400010000840d00e42000f90384040c465051285185858200025504250440c4e5901c4040c2401140040743c642c84480000005100101c2c4600d80c15024030081c01d8441011424010f0300180d681810309000052004010b80c0e000c0c0c1c1901c00c031076822a058440080034800002c0e034480801e82e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 634317661 1250 634316411 634316413
    0x90303120f0612050f0706030b0109030807080d11030106090e070815030c2107080c060708210c030103051504030f05130902041e0b0306010f1d040905010b1e060921 72
    0x9210140040171a00c02c100700b4102d0165042c032031301c440c803d07016110a03113002d50018808000c100041038111018000c014842c0c0b810728544108040c40900340d07507408950380c0250344000010003e242d00078902074018600441c4c04680d07880c0600019111110080061407042007140360711001d541d06101100e0400380042210380342504440c2065280e0208000c5001c070b42c070600001051500f070000300d0b18021503004110f2803420025685440c410b4201211160f0305004200c1d601c80a090040c01c200c0c4580700c0e40401603207079851424840e1078801c0d09240b46908402d180244004a948001c131040d81c0e854034241561381707164150205081c081309a00009142e032000c1408981c42d40c600040b0700242c44002c404000315500e5200d07000482c8030036603005000c500400a10310b4001e0154034030010b9001407208660140002c03501040030b640070302104031056551603920361a00d00d8030311241802c1140072415100c0359015400820501d00c264000d8600c501072001400d84418a8841e01540e12140c1030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 634318911 1250 634317661 634317689
    0x920031c05030105010e19140d080403030309062f03150409050c10080c04090513050a0515090316080306030a021801050102010606051c0b011e09050f01090303120f06 73
    0x3010080464000780140d0340010200c5101070120b2900010b0800009041c092110001d4684008448192135440388150009030503202c100200e6841d002a0005502944010525400700d1412404648001c160035580d18000d051481000345123444044142100c031101a540303442d1201265810140404c40603070260030041a0810041c02044041c01d0760415182c807100c04440b5041581d8151044030700070b111100500c030402030740c08280c11843c2c0000d08070300c00040c2440d0360780380e050900300c8081098500d03a00c940440c80003245d000000950000c03d01010307500b041c070900f00d40d071210855454050540d20780840411015034081c084140b400da402040d00120884103c00d001488009105050240d4600303900000c0541c042c00444084488451170302c0602682d2209200c014044420014104a140e01c04500d2501030401204a080d4442e16861291b40c0350100b007160a182400001d4100f0641281c00c100081d084440c0d0701039030504001c00700b244000c00390304400030311459000c030034030803202 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 634320161 1250 634318911 634318963
    0x604021b031908061f121b120b060901120b0301020307110f070e040308040f0c0810150f1206020c03030a1a0f090a0f020c030409021c092003 62
    0x400149186100ea20b07940c085400d81607a0b4000210707102c5400c80c0c40803a40c1d9994025110440c1c00b15800c504243c1519141c51078954100c2d14a0300c06455400d42140350108030a8004030101020700c80d041050100c22030890100300c01c1d015440c5001c0c14004030900300280d03500260414840702c0d40c0500210340300d180540e4001c0a00402d007241a10601400040901070507012a950003503074403c0502e0000c6440d5a80c0031100d0100c0100b05540300030600103084001520076a016004181501c01032508604502000c8101c0b1001c10701d803014403500c040b00f000812182d4060303a08517800701d10300582c5500300c2d051502c007030b10440c2e074105501e01000040040d000d016034002042150345a04102c164111201800403468140d542158004031401c0000c801541a4111540941c0b9011000d0b06240041718068a0360b002a00a40c001903008140e00b00203629041c085011070304c0c100300c01d01c0907800507200c403503001c4c03013a0000380b407502c0c002000e801207500c00300030b411907003103240070003c40010007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 634321411 1250 634320161 634320163
    0x150a0504082b0e030d0e040f090b150a0315020c0a0510050109110702090118060509040506040210080705090d0c0503030703090510031a060d0b031e101b03050604021b 73
    0x11200c81155100500b00d541031003450080459030010300204103100c0d031030030b040c0c0300b0350f001901c03a0b84d00c9512a0040710011042e405046295403180413001503d041a46840c889150300c044000c0c0500084801003012401003541003a00c013045000042c0d41704004103486c0d00308401d00801510a21900e024a150040142d04c11412208446001c100344101002e0185461081040c06544160408014006110104101083c04030b0603240090b001d955000800c00001044500391b815403c00810002541003511543c590703640d861820000307034542450007404600400080a005031100320f64407042001912640001c1d0a004049076280d03141840d0007800c81c00c0307901556000381a12104020244d00901810841c031001107000c0190400003814090680c00c410044d6007441d89960030307030301d964505001d00043e8812040002c20510350f00705c01c04d441c10840d8616840003619040d1010942c08040c4003c50555625140100d000d48071240003074040d0280c0b448000b15030b80c030b8018040020078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 634322661 1250 634321411 634321453
    0x12071203050903060109020f07021315030606031106040e150102010207140a0303060503120901110c04020703120605180109021b0115050108060f0904080f0d05040b150f150a050408 79
    0xb08070100c40d000da80740c154100c180d0052020041864000f8003246c0b0044c0f41c0201c224426503144000044c0b043c102da40440024401396000351005070b41e0340c0d002d1041c0642d00791020600c640940d14180707054a03003d000c5020000080c04559843c00604140b046a8802e40450754a940c02210041c4c002070841c048585512120108601081c681003002481c3e040c00705240b40d900000310081e13410900d0b15001034941822080101d0b00c0b82c000c442c4203404580d1988041c0051500a0b52036210240101e0340140c02c840070346c0c0205102d4a010030403074104041d0b54409074103480c0800009070701c0385011706800c88400e04240a001e01542402d14810300c1601c480f0400301110000d03a1200f0203625a481071058014200380176580100840000901040f221001003010881c8840100e182280d40307010ba008503807003503a08882001c0601c050090400c0418940c45003070500304c03a41003e5600401c00907904020805901c0008030b404500095068080e2003560014900300e000d0b103c05c0003010881e10f003108 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 634323911 1250 634322661 634322677
    0xf050706110f060403020d0e03030d151706040b070e06190503101e060c050f0607180e1501030b03151003050f07150302090a051c02120312061207120305 67
    0x200c1802c1101070349502c001a29801160150054102d02c514000201d81440c61082c0968161108000c848403400d030358458800b40000e08040c0202a50500b0310b81d803c021003a950b0355440f548014240804180002c0c20fa54000c003481c18034584490318140825164040d8224802409048402c0c09030b0440d005401103128510780601404001e8581c1c0c81d1180450484241d2240c10b504280c003400070a02503a00a0150350140c0c04440203070308200c2030b20b07140003000c50f029400121800f40231400c0c900311404910240c501c00e0300d510114a420000c80035540039040b8000c0c101501c46120340001c0d10b003403080b001250b03040b40c0911114601840b00c1941d100b1244000c680354811204070700309600c80459480d050b54004a81c2044000003000f0440c0a500a0350541da80324015480006007551583c0c10f03111046200c072140c01d420621030040000c1000c05c4540e0501e00e07001004107001c900c10810030302d42c2c04242110201002000ca00c0110b207010304941006421035040318411b001e054225028040c20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 634325161 1250 634323911 634323913
    0x9040c090e03072109080303010801020901021903051c0b04060e04121407060515060415090e010b0435030304050708030a1403310c050904020603060108040f05070611 73
    0x248440190300c0d0307881c480c041d000303807442440400110350300e504ca100000c00528140b07006050507890342e0000b030440d402030340910904c0e03500044580b082d513010b1001060603100c2041003c0c810700d603510050802e00c03542440072002d19440001c6d503420b8010368084c0711001000f910802406441e00c52424000c001984c0507104020701d1407041010700e100381400001d68103140fa45a040403074036907070030b0302400c4007400c200a40c50141c00080202e846c8e090250000b41804251100c2d00103030050042c0000e055500041c48800c14000184103c040690442e41201c14141c0307070f400d0030002c6250350703500151002c800310061b00c40c0d00c100c0c44110f0000409503014074001c100f910000365503484d25a07030b41c0c4204c50100380407901901751440707021a054080c40d0b200b14150081e05040b802c0e80c491824440d0503d18020000452810260500c07141107107001c040e0200707031107400d0f5504141d00014035901008005a04114081e4005420010042400140603601c403046500d0240c40d00303406070986041c1b425450f45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 634326411 1250 634325161 634325171
    0x305100b0111010209010c0201080408040e2d1005010e1318330506012123220f06020f090909010c0e040b0105070f0602030108060c190c06090209040c09 67
    0x100b40c041c4211112190305840c0c0c004505031540c01074a0300a002401500c00e000180301c000740303000118800c02c1c4140b0094204410081e400e0b16052008548000140c410b40c40142c20004656401c0380d03c1c87c1a5523003400c00c451540041c40000700c0c0c800300c6c805800f51640c144004000321085121907002054462400704001021002d196841819004000c0078000940130b01e0030001c031950f41c040c0c0c1d00000c06140903055035081c929141c0d20075402010030110940e5a025100c107041181841c245000580000c040460905502d410018a00c6104030710303100c1c410440880800220a091010007503000505545641501c0022074140d00001c500c180280710350340000d80c810006200340d40b80c04800d61215001500c034817050100402c0f003521410f041c4001001150049600c642501001a02c241405aa2907051402007070810b074002d450318103414030901a410715690110920600c0421514024950340b400342040c5000e400d81d0071001e0b400c00c1d1501e0510007401130903d04002074856039281405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 634327661 1250 634326411 634326437
    0x9060609051005030601080c0706020307200705010c0b0a0b0904110a0f05061c1d01090c0f05010f030519020a0309021831080307020a0510020310090b0a0305100b01 72
    0x2d0040d10051441d0300003001003000601075800f1340c0c60f464104114800b11420448680c2d1440120303841a244600852001e140042045607140c3c446400c02c180040900a258648400038021050b2044020203030015a40091a9803030242d0000d01c0040d002002c502c050f040508080b0b00d01030b0001401809000c8040700400c014841300412000c031003001d8101842d1020000341030059121204500300c00d507032210880d008182c034024181501030247d6000043e40c1c8480c1ca041c0c0c6042455512074210300e102c5090401441c1c0c3c100d450081ca14110f0304010465a0b00c600e4640a80301d02400d03c00240c81c400305400090680c10b5001458047c401d84045010801d007424850100404444076024aa10011541081e0000e203420328075044000781d40540107a21540d501c04aa0012525000103038003120616062000400c0200d2901b00211811855800c000112404d5921140a0101051344600e085030702910342401c070000035600b04c070a907240248011001400380014003e0540020040d1801107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 634328911 1250 634327661 634327669
    0x20d0204090c08062422150503010b031902100311130602060f01030507050f210f1902010905010c140f01020a1d0d0b10030f031e050304050705091f0906060905 70
    0xc10b9005d5002507000c0319a0520401070900c142d100700701004c4005d03d8110304c00060500503c5151040010039005940c20b00d02418210b6000060003403203070b1300011201c0b1800b4050307048088204c0e01518040c10301024008140e0140a030344010030059500011001c1160b20402005401d49038607900340c807000d490728403000c00807120030b000150403038020460401003440c0051050b120000c0c0902404001a1b280140c00c00710140b00740c2c0550590444040c911203c80c00303004042d826411202c4000c081c020030f80009081072050b01400781480b04445400b424060804880b010340d0511034101c1f00c401c000289018040c2d00103581860108842121580b0b181d4030305130840404140c090141c1e1200101a140c0000e50800545200640031502c94007002040d507004c1800d1780e82d80030341c484003540d030b0135001300b550140d6060a201c401c00c0070a106100c0000d83c04260340c0229181104c8505082d142d141001c46405051050f40e416000c018000207550a4142c104a04075800f9032107007540580c1d0f41c1d041c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 634330161 1250 634328911 634328941
    0x915030c131410030507180f03020307052b060921030c0903150c11070305030306010206010f24030b0402070506090601090203011d0c0f070303090c09020a1209020d0204090c0806 78
    0xd42d480403542c140c0301c000742d1081d817042d50b02045a14281d039039032000d8440002c080c00c06822120f03400c883c010051041d030508110500090106030b031a42c0605041d4540d150100ca200070f041c6030090400803d0000f408040e4100e4442c0e0390f00a4105042c22010240907420800d80c102c842e40030a0500030314521003801041e000c412a60040749060310307101041418802004491401014094014034100d0320540803c50f50f0040d5129000031681ca0803c034001a140c1001607126035441501c21005111301c81003215500ba4482411f25801c030740c04140002034016100012050b03400a01c049080300038810009000c40c05561400280e400d180d07203559181c0242d201c240112001400d0f0901c095105101c0414519400b003149030f210790a0400c0c00c0300c4c038185d076844101c09500003619208040188460858070384010704451204501d400f45c0c1ca480900304d032218041d0008120340c0c4002207400c0d501c3d1143d488000a60040c41041840300510304154027140701d01482105110f50400203100d14440d21030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 634331411 1250 634330161 634330199
    0x60b04050627040f1a01210f150b030703060801051504020315060f1206090402030303040f0305091518030d09050609010e03010e011410060207050f0d05100506150f040303050915030c13 81
    0xb91050f907002c12100c41014142c030168a50740540d89518001c03030350035030270028405400c904400300d50764140034600400340c481d1500401096454103050040550041d040d50b00e01400036038000da220340e2400240d04060302c0001d0f0031030f08080005004089910402e00030804d00615030a641a80c0c3c56410070b02002c1c020071200203425500420204010039813414600319690b101f8504103242c000d00002084000140200084c2e0075080800d40030301000c03140007150460101030300101420028100e00611a0ba010311075a8094038001801c80121b034817581851424880144c0284504054200003600800b240c0c5c07200442c0322403400220380d40505206000086030850350003010740c0d5043c0000c1110741c1c41c07039034202680443c484d02c1c0c400009200744258034085140b1440020f4030f2a10b0700c1446510403050442e2403076440204560f00d0203601403800d03542500e0301443c00d43c2e1509004008a11071098101201100c010003004120f08171075800700900f004592210a02201c0350740c1e0400010182e801d0607 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 634332661 1250 634331411 634331447
    0x10c080c0304022e020d08070e01090608061306080c03060601090305060106081e0a140105040903081603020c0a080301031502090f040b030102041a040801060b04050627040f1a01 78
    0x410b002d0f252260b10886201494131080522000380d10518203009130881e10b0101680200741410922504003901a9200e0302d182040000401c004000802580e030b10302507a414070400320b010a0032a180c021048017802031000d810010b0076221854155104000d0104ca4402e00c18500010003d511030004142125400b500525490b401c100c010b8074000f40050a625595459100c0034090710307032603406280a1481c4401c0050f40c03000640c0041802c04058200b2802642444080b1001075441242c050b0302c03400c01e4501e0b0042c003000c90703811400b80c8641c22940806201c0c030f550f44030a204030a0000d60407070f84666040d4180c15070010012059005040c0156804186104100e1942c2043d811810090744020001841c2c6a00ca41803640070705000703c246c0b4083d000114060008400074425000070b8411140715038109490000054a588203000b61380351304025041d149180920303149520200808010030900600c102c218a80000b4488140d03c1000c4200683c0050041d5000d559890701c403480600c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 634333911 1250 634332661 634332667
    0x90c0e0310180605180c150711030703050724030c0c1104110f0d14010f03080a0203040b030114040c090f1208250b09120307030c0509030d09050102010c080c 69
    0x41900340240321903425240307400b100100c02000500984601407243d1481c107010078109000704042403410844980445c002c1d0354000c810084201960151904a640602c00c0d01a40c40c19502081c2407500a5000400c98440d0b0300010544004020004a40050030b46001980d156855001c50039502e1740d05000000c01c940310f20100c040344029120614a10340540301086064150039245180d038007502c00000302034400706144a48030124002c00120044405580d0025414405142071041c0c5503c0018004080001d0b2601014000d1007130310020301d1b064000b203450790f80d00d03800c42c0010046e004100b80719500c1c190342080307954000c6a070b0354160740403410031129140c20051200601651503401b44c1c3c28400521a011084201606400d400c021074020564803104d64500010140000b4001280300c1d0017040c0b00051025090080d241d12403501d00e0080b030380c0c99031014240c0b00e502c20104110b03054081d039080482c0440e0412000300846e0310070b071b001300116440c1c401d00703c6046009030b4610303045007020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 634335161 1250 634333911 634333933
    0x180b031504020618030c030f06090d231c0c02013908070203040b070c0509100b0a030506060d09051c03140411040605191a0306010f08071116090c0e03 66
    0x3e100205104c200140c202c850071320465000034504401240c107021142d100c074081200f094814400c0c0701c40c240031401c0c100c481d080380c410903290002011003038102d40c41010456900c10804000036a141030040b83c01088043c00c500380c024080c00d851003244403031090030450a2007540804900c8000048000408110001c10020859480102803c0b100452000740004a250700c01c1c44c00418007544200914200702c1c0c508014010728905c001d1035101d180800450401c00e0700705903000c40c4c034032b178941d481c0002d025680c0c0c0002983d98003400009580261900030703003000700107001a1482035175101448241000c00d64210403400d03503500364004a404045980807030005210610550f09426008202184140e12640410a0710700740004080d000304071420200640d8000c10410340102e020840e00ca841d46c6031800018024011203601c2400b0015030400080e000ca00c96215040b6441010098660700340d4a807d00c1100f120180c09401101d42c50107000015180c0650743e4003000c00e401a016100407820 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 634336411 1250 634335161 634335187
    0x4030218070e0420040801060f08010c020607050901120501090e0f0d0f05030a090614010f0b040614030a15140f030601030c060804051002040b040e06310204180b0315040206 76
    0x110f0301005160b0301c0e00b40130a80c40c14555801030000383c0321000001034030910b01000c0550f5003425030321816090749004004030491b036011801c2c03540f0203114100301c1c0e602ca03e0b00300100c91204812043c04c030880c2c03401c000820007000a80010703031843d088100702c031a40c502d003401c2603848140c00701c4441701040444014541c07070341c01440555488234020100052600e895100c000550b14040e0400c40084007000051003515292a4107402170528034231030508140c18840c025204296810f0f000300c103040d006c00011903442d4650841035000040101071383d50641d841c500c05075204600d45a40d88030700c80e0030402c0d06180c1400a801c43c100d9130401e030350300d0115241060584561401030011703180f5014500001030000305078001003008010192880d65600d10f0505050350702c002c0504401c1c401d0009910704e06030724010012509580450140c00d41204d154540104001d01c5554848403080070324008054042d050b960049882440a905496142040c0090380c4206c0408a170000d50181041c0240744161503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 634337661 1250 634336411 634336421
    0x60803180411070b040201181d0402120106150306090b0a1e0e0103030e0108010e0f0103080c07050a0e010e010b03010b0a050d0e19060b010f0c1115030c04030218070e04 74
    0x8006440002c5291a480d100010769000c0c160a85510314080c0a00046503401005250b0a0803110ba000120130f0400c0031082c20421043d098070121581c0c130000c20255662800c114050a21030300c020816160758065401c070244030b6103490404289000000980a100f0b8040c101c4440300080c088254107003000203081d4580342012014031040e450000220719401c0c80c8031031034041c43c0251030742426100e0b110300041c403885050704031180f0705404c642032010b40c060038001281500e40c8166001d4a0b0f002c0038120300e03d090055403180703605c4402d801001500f01c10311002c450680d0b210580b03444083e030300c1c1c00b10b6403020b01c020b2180f0b07580e600003089480ba510340301e200904001054010041011404050900c1c50005050081e051074812503004008114403803040c1e425a01007800e1440303c100703044802400c1c1c0d040c00d060290910200032003411403580c0384008100780c06140000306d40c4030b040c40b920280281c0c02901080b0301507002124880028156010400d126421690320070a8040c42d110520000e05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 634338911 1250 634337661 634337707
    0x50c040c0e0a170d0309050c010c15020d050901140417220602100c230309100504050304060305070c02151809090c01030b060903060c18040f0203150103060803 70
    0x1c0e0400c0404515550005840001d18011285480440554600c141418030060081092500e0b0980303c0c1c0004c3d03008504c6034591202420718200f0300c02981000c0b22106501d000010050388001041c0c5910305003603000034000d0302e00c40020441c40c54604911128200c0641e00501040107000a1641c071400d804c00803e44140782c0001c1c516400500c02d581022100a90003040140c0c100a200c0080f00708240700d2041818010300e007058150741c80c240054640c04000341807054080000000521081d020002e1500d0304000e0341e401c010919183c1411910f0340c1042c028080028100701c0800d021520450402010a400422418410076022690202039100c1048004401d8021240c80c285d59201001d851041507204003401c50507080c0000101110740e212440c5104850900104200340c4000030820384c0b0117000c91034035a81d40c0c991000742003602c1c150441c0e1584107041100000540d10150050342c054206003054041038041c0800540a803483c034000d10600c0e91040c8030500c2c40c0710f4070f254800307100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 634340161 1250 634338911 634338917
    0x12020c0708190c05151c140a0501061b0201020123010503060f01080601060e0d0f0305040911070f0f0519030507231c1701030b07090e04110103091104020a080f13050c040c 75
    0x301c81c5001c50341002c40c0c06c0406801219541c0d01446406100250000d684021030341c404005e01d60500c04081e0803c100d1074002ca80b03003800b0741041001c40e4005d6108240030110402c14010f6036141c51580d4182450900849010f401408003180c60b0032111006241614401009001c0c26800c2c408101c03540070f5036803101c030b0b8420b44c0380c07c005000c49e1800b0381781c40e521400b0350b6900d69070300d0400e00b426040c1d40c2c4142103400d521a0800004000c5070880c94425465540890f645501c00703001d06046181442c95009a0840072102440204042e000802010180d105590300c03490b880300c858500e0180b90440c00442859003006013107072a240030304c00e035080002405081440d060310384056100c4c2c200009030011101411210140100f5070f030448030000042000700c0120441d0f1a0543d200c840f1080706941c0359040c035441c1c1500004008901c5034072251840c014104546680a124004002c0841903900150340b10f0000e001c220841064001c0c0500c241d0404020a06e0007103071000c0c800280502820300c820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 634341411 1250 634340161 634340167
    0x1b090311060f0a030f0b0d030912050c1008100e01034d03060903030c0708070804050d0b150f0307031b08070b1c0911060a12020c0708190c0515 63
    0x44010365005090f0004490f9000125032004000080c200c81000403024444c004a183c2003001a0f80410400c1c1030758003100720740c4003005282c07a14500d091070550780703135a006040030001c03c01f2962044a261052650707012030302040b95944140e810100e07007800050700400c518101c107001a00390070309a03524215440f001c070800050000c081e84a10445009483c0100718a040c40311a9240401440d5044280400550304d07500f00f05040c2c454603c0354035401802c071603010070b40d401802440419a030041c00f001d0303c01403000c4903500e481002c101c070403215922600d01807011401e603421720102a2460410181c020071a9030704540b04c0c000c02d1404e8030510030465018040c0815136910170301143c1d0040c4040c801158680c500c42020020300c40013802d0407441c0714942503100b00400c0c01d240e08460840c00940301103554940001c802c540070307841d1141c02c852443c00010000614440094070310121000d800540d000400d01c1d29107451800080c11015120389103600042c02645031561003424070840d0341540510b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 634342661 1250 634341411 634341427
    0x70e0306010b09031606020319020c0406090f051014010522091d030903120a200c12010b06031611010908091c03080c03060402041e0501031b09031106 66
    0x840c08400740c00c4040a00004104128203003000c02420b941c1d100e0000c11917003101e050060096490080700b041c0300700b01c0c1000c502c2061312402805030360100c08000d401440310309c0d1128005406094003012101803540b5001c0051144000e428410080d219170324120350304141400c004652581112040000070284900c950342502110304040300206110680402c1c4240c83e5418036a443c0c00c0000b0380303c5503820400c80c907001d556002c03840724401c5004550458465041050440e41c1540c140b80b030284080001c1d805070400207000400400e10700381102c01001d00d5550a052901742c1c1c10310001c15401c0300080c40405e441d020342e900300800c2002c4c0340c501146022140302c0b03020b003512003d05043c0c0308030800043d107180d94104144a2100e03004070340282400c1501c01e0394001e0075040c00034045500510080041101652950102c0c0c004003100b0f21103089c108511801070310303281d002e480740f10b01282ca044100304440907280e80c08101e0051720385502d4442841e42c3c0300d080f886455000c0d0103a228108018000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 634343911 1250 634342661 634342663
    0x6020d0b090924160c14010f09021201020403080409050402030c06120105041803020a0318080f0102030f0f01180506060d0c0c030809011e0213090c271409070e03 71
    0x1e4482e004080c01051400c3e0044524514101c02c5442000040c05150400660780720180c484000e0034090316101d89012018244100c44003901603090400d0350800003030307911902050300608000e0b03000b00d88641a0f900d4580e0a1800c0748a5884001c265400501081240306855481254000d0000d0107840c0d145c00202c002424a92240c2c2c84030314038800a000600640c01e0910445080d022080076000306060a501c01a40d50f036031000c0c000f420230400020301c86001d034410074664000c0c0400012646882080f0041d00d000c0d4104451030740c601a24440018540103020900b64125400d04404111600265039060080c203402060760390040c40800c951b43d5120b440d48a0107402a07805d54500c2024219860024010880940103484036030400f00c0c1000c42c08000404015100080040142da4010090700d42d901c03406564021319038589450030030b0003000d8210800100018554050526110541c0d038000d41c282e43d076000341c11600002c080300074464104840180e81120751810020b801002d010700107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 634345161 1250 634343911 634343929
    0x1b06060e040b1e0708180c0310060311040213060c0c0e0a051519090b012309030d03060f1406070b0a0c020f03121b040f1203140304020d06020d0b 64
    0x480300c1c0c1c401c0b40100091400c9044001c14424000051a00981000400104551405004210340040401d541441d03104200b007410801c81d0060155000e1540c10f0b0014030040c4464442541c26400c0341c01003480c18503080c0300315010015000441e00f50681001c000f2251060b840ca81112980c450a002088256031100040d11895407100c0201e6180b1b410348961701c40b03a540c1840316018103038541c0c1941100d405c5290740402e0724920354000589195081c01242d0303441065001d0003140310012414102c0c41c0c0401d0007040d400b8410390840d80da400c41040100c08175022441116015941000d0901c5a08201c1c1080485054010702e19070411410362610100e1000c103590340c1c0350440d81c56207543d462680520000884025000103181400382c0c4007d422030540c0024906045141c40d071040c20102070520050b98007170040d081c44034602d90748800f4070754152200c0c410294085022a8188041c890350308040724800c1c0d074007805810800d0301607038074400650842e4400d03091054507810100030945922000b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 634346411 1250 634345161 634345163
    0xc15050d02042303010b0a0306050c041206020c01061502100b010302043311150a2c12250309081204170c011709011803050a1101020a1b06060e04 64
    0x10002480c1c0e040c0d1003042c1403c96601c0100c0c000c0e4103103842021641d880f0450402142d03009a0045100d07503840c0c0c03030382c0240d2181d0f4215809055040c1c4140e400e0201d40e50140c1000003440000700580c03511a00c80c851143d6041840c000180d001b00001d10118100e60411200c040d018140541099291088101011840c210006101d040480c2c0c451010511612043c4000130500f4204a00c4a144171480d440d501d00860b91600003070990042613204c9520346c0b2583c1491740c3c0e59890910813003900c0300c1c0e44424606020315140d030312804d07000744405c402940403100c16250002441c803c1d500400c10329204511100340a80901070072613000590344c00d0038000010400b8440300e0a690b41c44c203100d52001081070400345c103822035000c0c07070b030086040c1d8200c0f2859460490000b09201c00342e40d4260811f0151000c1094124640120410181019041006444500790325101c0001c03407840401842d00302c1c0a407901c4d00d40060100d40d1a0b4600800c3c400d800c3c12100e029031008902103403103403c020589202558 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 634347661 1250 634346411 634346429
    0x206030c0c0a08210106031802090c280306081f0903020a0506070306050109080712150f02040e060f09090c060f190e010f0507050a14030d09051b0307030c15050d0204 73
    0x4c10020034000c80d0500c075000d000c140c00c01300032040340d40154002c51005050024050f094201c085a03000384a8810b40307070310f40035100c0c03141c003d00702000082e11030707804070f00c11000482d0400c3c1021650b128081421074002c949000f606c0d80c0000003568020250610702c0c401c1e415801a80500000300b101844154400c0760507440103d01e1500e440001404116903920151058001041c144108801c40464200d00e9800407081d503004541c02c92100014100559602011440000c00080d03940104412605c2058110b602201500c0c2040c203004c40508215000d240a41103000c01015910b0544054003a080395610014100360160030b00180150005040d0130220b21130400c08100c40d0b9000300002c003c0342040c68400c0c14089140d0700c2030354500b0707030f154020080d049010102c40500b000f00f050313840300400d0750428058410b0a040ca65196500b04807803107041d040c000030080d03032070a002444a080301d03400500416183d1600c1e82d0301180c005007903030301020070004000d16098005180003800103082c000d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 634348911 1250 634347661 634347697
    0x170405090a05270606150403020d06110f0d05041505040c180e011d0d1103031501050919030323030c030601020316050c0405071e0c1403040e1902070206030c0c0a08 72
    0x11013080b001002c24101c1b00540d01c1e00304028001a119886c00c4100744c0c0d4816804074010b0780300b0440c041349000710041420031100c041244044002550481405030b07000d08403c0c100c02c0180020030302652411100640312561403041004850540325003011000d080c8140000c1c0c04652400442c203580d42c0b0244488200250b0355101c159810502624411480b603051803000d180004d40165100e020040c040544110800e04c01c109507401401115051380009004a4202880c000030009100450105400081118010004502c00040000001c00c0041045400c0d961043c40900303d0f540014150760443c04240700c08070864494007409244584224045c101c03168031403003440116900242402d041050402100441d2200d01c540c08400c101d07903140c40c1c0d030700b40380c54101003103c03521300c4034150014440060300003a2000030101441c0500b0300380503150001a003260a0380240e000b041406540110300300041240394a0384c3c0024040002da5405070380c117400c06c50f00d0f800c1194000e18404030b0000d00c51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 634350161 1250 634348911 634348921
    0x1080a1e0504060606050a0c1407090c020f07060f0207030f020a0302040903170c03040209011e03140304240806060c0c030a03050a0216030510090305040f060507170405090a052706 79
    0x90050b5001703022a8075281d41044a0004002c05010700b000b40500800380b1700e0240f04140c1410700c2800043e26440c0070502c80008a00c20084d03a400301905030f6182e9001e10440820782c40d11440040c00500b0b0941e006107001ca01315181e06094180c900303000c0744d000040940000041e01d40340650103507503000e44c42c0e8030302290301c0e29088402810700a0180302c0d2120204108001a990008503d040d03807000c100c2c00307590821104008903865146d030006048101c000c3e8207891310440000c001e100303a400f90403c0c003c1c86914000300c02d00d42d9600c5140c0b28040741141000440e18107003007020b06620a102070131a0031504507680480e00300034030b061b82900010340000c0e0105100340c0400070500c0946800c003c02c0f60691031500e82c25198020300610f4aa419100c503001e10506100e00c080d2005004951804200140d071040081c00951116108981c207802040d402410301048a0550f0200c400140c048030380c40d0703645010000141070040c070b0002920701c41c080350718a005890208446090310b06d40148800e02704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 634351411 1250 634350161 634350173
    0x30303050613150909110d1110090321050d140a1805060a0b0303091906170f06060706020c010207031107050a0b09190e13030e010f0203070201080a1e0504 68
    0x1414a004002c506004010a0303040d4540c0441003201c201000001c1d603940b41d0b1500d11070508480f44503070750003000c07510404180410b0001d00c8040c0a811541c11100807629001600c407001544005002c0301c0281c00200940311481511206400962411600c0c1503114012101210050034016110b00b26403c20004858018442d03d4007107c034141c0c00c210f0003080d82da04d081d500c080040c40202d101d91500014070707588d1010400c0e220303a040002c05022411a6404081180ca41c03a84902c0000940d845600b1020200c6121417500890b02c881d03841007140c0d601c2e02408910341c0100302c1125825070800400e1a111403c0c40500070a901c6070740e80304200c200c980c17004c9150014a0300f01501c101040b040401500040104640d400c0d1003d0b1040a0b003c42071518030075008120b40d0080814000c01c0d000c01c082c58010401c100394641c820b403a00540100c25800440c1d510072306042580160b4400c1048101540c015010568050142c410114071603003a9102c00c0c980100c683c08000c0303841d80ba002071008002d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 634352517 1106 634351411 634351429
    0x90411090d08030f0a0501080a170d050a0911040209030c040e033a06050d14122a031602130609020304120f08010b0315030307020a0303030506 63
    0x1c5500340807442d42d0040310511510030000f030001e010700c01d183c03282d1410307118800010540035840f40e07183c002122640c0c0e1700c5015110b081c0300b098002c04103405102c0c42803400040201d80c1c941c2504c3d242c0c5413030f048401c42d184505e0060020003202d44000a0295280d0002c2b100132070942500111542036104416400c42100344103100f182e10700504c1c2400a0a80150030001340b950301013080002c085400310f0044543c007044000000c0d010412a00c468590903020001340c6400078802588000c050f80000b020f0004019503518181c5004810f64405102e900060003951812a40c15071004090504000c0240f003040600006081403c4070741c86803001d4100c130b1204554a041c40e05158900d0320021000100007440c0c801c8003244144515020f9040b181c081c4402400d503151203a00c07581030340140d0f96140d010312092014001695402e05001c000358082c0d01e00080e40e05040046c450941 = true := by decide +kernel

theorem cover : BRFrame.Cov 634172661 634352517 := by
  have h0 := BRFrame.cov_init 634172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 634172661 ≤ n) (h2 : n < 634352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
