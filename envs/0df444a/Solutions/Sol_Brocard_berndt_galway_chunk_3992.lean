-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3992
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:15:33.612247+00:00
-- url     : https://prove2.me/submissions/0e2ae1b0-5a0c-4b41-99fc-70c15c518977

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 717805755 ≤ n < 717985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 717807005 1250 717805755 717805783
    0xe090d0f05090f090103050f070b130302010e030f0106062118021e060d0c020d05070804050f1c0b0406050603030a08180a02130501051003021215151b1608 68
    0x510307001d42c00c0002e40c402c1d0b02d551105070000c070840d0000c414050f0100303800d5018065002111f081a0b95090322000318801c250b0380340460a01c0600c144019031080c9524203984600504590455100410442c210344103640a1008210011020341c0b0b546242d00d4407081c0011010000c00032040d0400500512402a500c001d214035140d901c004140c50048a03d03000c000006840340c0d44940440d03407000005c00781004450b0243c03050203040540e46104100b100e0060360302800e0641894580414403151080c880840d41d40111a1080754041022440b0400201c502520b20302d52241818103140d41241c1001c2d15a90007a041007020720f0728690051191a00155200020100400943c03001400c1039058100294080140318041280d4003164000f607040c0c071030458010700ea99006210079004c03031281c88814004214994005100000d100d0007001044a0192001440c02d0304100000d0f5a640080c141c188249545240b001e04c03500100030358000403418002000c2418104800c0d80d83c1d4000440301e101d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 717808255 1250 717807005 717807007
    0xc0b07051e1e030c030408011a030c1012020405100c0b01050a1d04080706050403020303010303031413080a0e0604080f1e1207080708030709060f020d080a0b01050c160e090d0f05 78
    0x44045a003c004480b6a03e01000549464507140c0354140e0103840c4081401300804944200b00e4800d24022a0b0300980400040c035201d01c401d62024140d071003080903419500b805c0e60a020009007034582211281d804000c6075950050840b07145070840e0108010b030841da00a003000c40050107040b02d0000c0c2070054031203440324160240e980e4a0300b00450b102d5a20020b05003800e0105000801d600000030f10b06032403082c0c40910800c07a0340c6040d41c1000c04212000c41042c0808242c01e40459494001030400319a02c0c541000c04004510100700c0640c4141e02c0101c0035400007500c02c80915042c00090054000b554103034101105100d019031b901c00d030011900d40500000610035080294640c00c554145600180700d507220f10341404081d141007054880c0c2d81c003103440f20000d4030742c8038808902080303410303c0c544500e2099143c5c031b000e04005180d00340a850501000304400c0b00080020080000c00c5020860842d0351a03062040945a030710000d080d016069026400d200390543d0817031100581e41e20185440b03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 717809505 1250 717808255 717808303
    0x90d0e060f0409020703030902091501051206031e0f010c050f0a030c02070f0806010608010815070e01020705090103080a0f2c04090f060506041b02070e0408070c0b07051e 75
    0x80d001d0744610350084550500c002241400c06400d038103c0c2501c02d00803240361080d90360b070032021100c0312207603502d15000a404002050007400c075605020703042003010b42110100c4403c03400709280800040c1040c102c1d135103d1014008621300034000c06140c00c0c200d141482c10170610038110f0a050082c40c1d1080c1c2415160600070003924420083c600003401d41c007248505080e42c961609442c0c950078040c00c0c0020f040a000800c0c800400200060002108601103600703944011085808010900d00c0604500071030200040319640d42d00c0705406103018802075075407040c0c080e10141188044003040c2c824040414002070321406405039403804c5000345012564407035541000900200001c560041c0462941403003902031040d20707800700e441342c0b80980301001000b0000c0c0072501c4c800d8680280d840107030312983d81840011062621150024460321102c2c0c140b038a150345100254100790000c0300030305808904202403100420005010340c44141e484810820a00001c6032520108009003030425140f60303503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 717810755 1250 717809505 717809527
    0x2070608131a090d1b0212030c03070c030c0b0304031d040f02131715071d060403050307020117160516050322051e0108040c03050f0124080c011b020a140306090d0e06 73
    0xc84558103027000a403980d034812440c0c41079064005000c00d417000748c1c0c41c0c42c000c1480088032046900030380c1c0503200c90741200e03503002e144a02c0301100803103036030059100c10700326010710450b0000e4443c1e09502c07001402c805080c02d0303904201800100002000d580a08040c11200c65403c02c00c0c4d0f0001d429243c00c010300310308101c400c905200b4601805420440000d000001e1201c00f0028000c818801da0b90311202c1ca004614100213300140c41c03120100e20602a031105c928003400060203140340d007190841503010b164890a0554020042030310040440e2420303000b6060b07018152030040c080454040690341ea0020550082e07888402c6501d040c071100c0030228003841004159203000359440000c541107102ca241c141c03170181c088003607070610340440f0410081c80b41c4071440748101691104001040180c00c05001150440c0c43d0605d040f52061140c0111000b42c1c4510034202d0240c80f403040c40c00300110317100e0300345890088004e081074100d0300901c100c0c09965a00005040c81000e048030313140e072501c541100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 717812005 1250 717810755 717810757
    0xf020712110a0b27010b1509010c2901090207030207091109030124120b0a0504020d080a171f18020c1c09051002070608131a090d1b021203 61
    0x4030181490405804202d004103030310500c405200e40790750b1007820180c2542262170913180190486688071014451903903d00440b040589154181450007104140141d110401c1c0742042e0b00880c0c54034105185045a25407900075254010b20483c1c008614280d002d8400a48801c601d01407804a50340f9840310301902d0180c0f034152075220341c1c002e00800001c00342c1c130111011800c2403207562407811550000000c4140982c101c00b060a500401d0ba40300c4c903601c40561000030030004001326400b04251101ca00807a000c40080c000d00e85040d240d141d07106601140c1c08483c0d02000300075008044280010043c8090f02d14180300465600000003038200c04880d00070006401444109a600c0c410701500380b0181510612414071640035444282d80b1681702d4040c0b0504043c003000c5003025030300141b130400a03103204200169004a4138540005002d105030341e10f05004040aa512400b4540315081c0540f205d401d00146c1a10045400c14270040c0b810b00ea507001c0482d4110b1006842030110410180306107038148 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 717813255 1250 717812005 717812023
    0x1b09101e0510020a29040627060e070e06060901111c0815010504080706050304020f1f1202030106350702030d0c0503060901050402090a031203060503010f02071211 72
    0x30b10210081c0c040c1c050082d500d002952080d1074902c0071401051003c0304641c1e01d60501c2018141c440844c3d5210b40301e40018091400301d8903600078004100e140030b4040380302e002d80e01ca8130420700400c00c0489400028a480c885400a00005108000344401980c840c001c90308182003c0c20000c200361241304030ba40c203020441210700c15071010010042c00aa80c001a40da00c074a1340700801a4001094500458203801030f4084c000d080d0b030207100e00340301d81070055000e19441480202000d9084020101007003822030305d000918181c2c009c035158000c203250000281800d1840c0f4200c11800c1d503246c40802410708541d68484c41003484000705502010000c101002c030900c2d032030a076204503802d02e024001e5480e40310f01c110320080c03032a10401c846000c0c0b041303044034007441c0010012855a4248010003000f0b501034058258000c0451f48000001600080929250621514001583d600d040141030a5802c40d03084800d1040c03040080c100020359a01c8048492101c502e0304800c0c0c3c81d90716600c08d10b080901d07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 717814505 1250 717813255 717813259
    0x20714220b2b06050901022d0f0403030806040c031509020708040b040305071a030103020d11010309060608030a0207091107060b03031b0307020f090714031905091b09101e05 76
    0x2480ca02d102401d000700d012042441140100302c20707503614003805c0c00c038021944c940410007480003900400300e21622540c0d286041044011746040d040c1488a807541c0c0c4a580102d02007002c00f03040080604c0c281c8240720319460682000e024062400303c0b40c2e0004500c50040b015420b3b40070840300c0503c0583d10581c1c0107041a151400c0da9a82ca0b0b003481c540d42c540c40c1c422040d8a540d01c3d0840c0209000c03980c02d6a04907030340641840d60150040e650030292010090985041668409030342000c00d401d8022140100740d10310186075203102c103c1c0b0007810003000d90055054141400e0928a10850100844141ca9003060000850150341380c00a400c51103000c0e080c5003102d80c0408996144030f400700061000750306c00c5a8441030030389030006000010104403034500c00301d001c04d41c041c45c2c01c40f4440c0085078000d80d00c004400c00d1407505920b2070100c5409841e00c040a502c60400c000807009030005411480e10100c6030202c05142a458402c41e8a00314001c6400d119003203c501a0a5550300e19007201a00d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 717815755 1250 717814505 717814549
    0x1018020a03080c01240909060f140403090623070305070203060103080424050711010e12060a0f0b0303190201091502070606050a050f0108100503030a020714220b 71
    0x640c0c28000b10581200481800340c0d4640590b00c51200790701c085114000c03086101c86200c10f80340c92261801040a40b0040e501a610f03100c0b06400c480140c803403075052a00c0c400341e5036428203180c00e004210503015040402070010103c4100440e5443ca072190b04001d600c2c803c460340d2400d25140403143d5004040000350940324030070000c8200a078400252050f00c0e80d0070241121500c40d115080c7ea40066041803102040341009580301060100844a096680605000c515400c0801c00729504100c8410b20726090b4029105128200d115030044c800301034403140b402d112010058000a80300d00c10380489099840748042c800c8111070003908107220301034020010001e41c0031a007225101035032115108507203061071b00c20f001c1502c2c50302e031103210141c480c060500c40000d8a1800190f50520340640800d03009002d1a60008469a0030401017500c0d1482d40c1c0030b040200c0c500f00007101405071035243c4a10490100d0207007003000b200310f00030030401d0040780e601180c01c13902ca4000c65104454050007402d1003403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 717817005 1250 717815755 717815759
    0xe1015030b04052a010503010b030406152601060e0606030a0f0f0b030c0406030803061302070c121b030f060222090b010225030209061201050412030501060f021018020a 74
    0x1010035804c002002e8004098046030030513000200c1c6050002030140810014001070040c0c10b1400061a0300c28030074080010100d0310b20086200c40c06043d80b146d2442d9084114010005039201000d000d4424800000c3c4185800e1094400e040c080040c0001d01500d0040005030722401c1e660081c0307412a038102c02c200b114980d0100b5000242172002100c0f8041e20400c1440d10513814144108411650800502c504503101c00c810440300e018840c52012600d502440b0410114014090b4003004000c14806110078900a207005410941404e40e01a0034646072002007010503105040c3e03041880d801540140d403603000c041d884084176040071582c1d2880c0303003496003c104210039910011080409800b104c03090700684078105c0400d14216290340c0c0c10949120100010b0502c540380c19002803005198040300b0001c403540a0841e00225820b903100c01c1030b03031840c2461582510a460140081d4a06a5190241f083d000381da070310202c0c0c4000d110380fa80c40c11070450a15102d500320580300e900502e03080e1031507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 717818255 1250 717817005 717817013
    0x9060b1204020f01023c0d121a1917120d05060414100501020f070b0906070515191503051b040e1e070e06130c02122701030e1015030b04 60
    0x4420000c540480c04401425a203c000c000070101c000600351340da034840541e0282188000b614900010300c1010031803040846042d6a00060178203261401c2c692b102c0c0003071400070341071500d0a0704242e5410f40e4000c070100b0241a90b1785803c030b03004048400d4010400c0d80740c10700860010040400e01c0c5001c01140401d00090b00d51b1a118a401c44009a08580048010000081e00c6540c14820003907a042d0070003a210f4241070002c003810145006a044c1c62507550058140000000101c485e03030b150320620f5105500102c0a44100c85400300c2c030480340143c160540da580c80c1c0c1e480c02020300d1129481608100412a0b03581d411140e07400c00650f040d102941240015039071072010740101c45407980240c0a001c40d070302000c4000d4900c40c080c003d221031001c82545c8103580c000d141c0840000114024074020107410700380400244008020b04d612500c010310202a140960b034810f1607103504040c00c2038090301b140030000035030225052881c000000c0300b2995a03840d0194070380c1ca9000501310002c22040000384 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 717819505 1250 717818255 717818323
    0x9060304031d101706120703020f1f090617010f090203090703080f0702010201050a0e15042609090a0504110f0a080d03021b0c010203040e06130e0709060b1204020f0102 74
    0x104d9005101e03400b54480c0402c00100901401040c4640c0c3e000ca4410800b42c5801202c18490761406005200c0c4118a80b40c00d072404510007d0500200f0a03078001089615480b5120f651200340036030012509505205401619103124860821600e4021012482104040c800c07007000b16404452183d55440322188440b45030450b843c1a07026519007000a5100600c0f0300900c5009102400035008010f4025911481c3c0a4042c0069410131304114503808050304600e06d0800e10046481502e0703c82c05000e0410010034030040500c03034814202414040000c2c4024520200c1d9101210440d8800c0c1c040c4010600d900e1481d80460814418072a02215850f0541e00034013805030080a00019502e01c0c1d800150340b1054081600d0059104000801c00011603d800300c0c1c010100504010103441100000400e40700c0080c44014182c100c0d0f0020449100c8620482c0700601180c0c590703e05081d402041c40343c0071100244064041c0c018111740c4c245680c401d0044003081c0e24003020003981c0d079440704004491 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 717820755 1250 717819505 717819527
    0xa111e12060a0e150f04050709050408040302101d040b0d061401030b060a06390309061b05100903050909010b04080d030b0325120311100209060304031d10 68
    0x1c0ca03107041d2518100d03500c04251003001310b002103030544190300e0300000c1381e04a20000388140da250003076110100340880030340903250240d402041960344903401d42c01041034940f011000103042c803a15031480c1d9014507041036400c880c14400c880000d8080000800b0405281c085100208490700d000345607a0304400c098a4641a21701468281c200b650f03546040c000101c5540c05131030003098410501a042940c2841580250180815100c1c20440402039141810f008841c0c11804102ca4010600102d584001d041d0795840da545501d2a4800f515143c40352160105e058010003540c540084009150240c4119024203002400c450855a5602401c0046130042c0c029640e15001e210b03680204030744207004801c2c200f803004018200071411b018110760030f4030b03070405110103114944000081d0184482d0007940380a009440c0e00d480303000300d803503d5400c2145c0f1a4600a40c5d0b44140150031898807042e0030369a2007a410305042d070512860740b020882140ca0014101e600c0342d00b15003041c020303d9111080c480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 717822005 1250 717820755 717820771
    0xb091602010e12041d130b1f0b120f060607060203040c0e0907080606090705031602010f0f090506130302070611250503010b0901031e06020f04091d0a111e1206 70
    0x40070045c607002000580e01521041c404000004000000c1580b0000e60f541000110701200003141100c200f4008502c495031081d600f203a4042803070b848010626192541c0801c030070180790014900007000a1860146000242100343d0101c002802c114420381c0c3c0f20041c00e40c0c11000b120900d0441e940c1565284a8040c01c40d25020350341c0070483c1d6007130030b049083c0a54100e032100350440d41d034007510803450b1f401588a60215901c072107592040003a00c0c41070f856414940040440c18281c40e090940c940300c00900082048882c500d808030110f035000c10110144c070320070b180000000b48100c00640c0740202e20282081c0c21480300803e22249100301d003520048034130a4009010080c0b030f403000c2210b03642c024807019021404080018680c030101030302402205104200050401ca20b800d81c0a0f030a402a810001d0591341e00c4210840e0b80761500011316106405000400c0b10040c203a542d0480c1c00150518613008104400012141403007401003207000c1240507081c0c3c1c05094500e612075641d01c0c81130710040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 717823255 1250 717822005 717822029
    0x1d131103061003050105030d350a0e03040515031e09011e020306100f1403010b071e1104050c1b0d080115020307170f040608070e040b091602010e1204 66
    0x301c161400784c00b4440c12038200030041c001e0103244800640740c8101c131070b80342200c83d0207400212107000140104400603444ca2507821040d4070740203000808591140601c0d50300350303009100410265a9608048090501c8090000c0d105c0d1214003c01740407010516801c81c10341c03011420019112015030001903041e42c0110840c5c2c841c01d080c511541207220580d40e840e00007000748201104070b80030b0b1700d24a0b01081c582c540301a000c81030204a1003141c01c280c21141a500d0000b40800500012a405068204a0612f07034501c1c00d03501d0ba100d05888101440c3c990085449400180129400c08107a4076142e00c4203600d100044440c9c8001500d90700320a40b0038011449a500101d000138441c0104468042d5a400551402100307480719014504200910400c1001c00c10a50031b99010550180c070013000035403900052410985400b41c4000342e840c000d503004a1a110007420a40d0f0341132606500407071603c0500c081d081642e42c04070b014103042c91142203c1e03c11440c29040b20325841d00148200c03031445a00c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 717824505 1250 717823255 717823279
    0x2092103132c0712021303140102280e130c02060903091302030a090602070c0f140a0b0a0c0507080d080f07050405060f0c0a060501030209060f011d13110306 69
    0x1c801c20404810850036001010010030b07148821988225420800d5414124591107a540b107000503680710072065038500310785032020410002d400160321840302c0402c0096007000c50310f01d0030130f514046101004c0218200d200311003249501034030361040e41d00d1019002007400b0086001d0003018000c03240d003400c014803c1030001640990084151101d104004124034542480291120082e42000d024030340d01c0c1ea66885020300080c80c0344020141c00f885860303103140003882c2902c10300700c62903507034008402c160f5510064441c9a490140c40c0f415501d1004000303455841400703080701c921203000002042c9100386140490602c0703002582c02c40c030f02d503070f030b83c8403807041d40c03500c00701d84070b00c0002d0382c02001040e800c3c88180a07a24215010f011104080c1c44a1030800100300821480d0000002003565055a00e6006100394108a2802584402c083d41c0d0403031032204a4000030401c0140117070704039000701e0703a0040080d10383c1c0d0aa04c01803e0004a20213011180313024000000d51344c001d84125102d01151800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 717825755 1250 717824505 717824519
    0xb06040905030319060506070b01180501080d0c110909010204150201110403030f210609110901020604031202090306010b03070206070804050a022110151e090209210313 74
    0x203458086a0101c003640c00d5803070b80c4201c0441e0764281800d1000f05911204040f481e611030314043d08659008103034805265240c0004803505090701104000054200b03070051003031074000103a2074144609490001524a61814603030a440c40c4522115481600b603402c0c0540080b0540103042902c1c2c0801c0543c01c1030724105026400c94100d02010340341c0520034001000464000d401d1403a03401c0d014101070114010b02484071600410000e0451001caa0311318090010030424484e040d800b40c41106200e01c0c080c0002c00107075540c000103000504018003d03050b000b8004c400c1d0141d4002002c09030403209035507195140f100c416003085540383d00510500c0c0c0040c0d10284100700c02c0780a60f82103000341c140720519800388004010413500c107c00e4014408200d0ba0310480c1008046143c141001c1c00040c2c0e504119820801c0c404240d00c120a10300a481503100460344040261040b45e030714410050b078501c2501d01003818150101d4054070f075030050690500f020600440100003016800e01034041441d100e40c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 717827005 1250 717825755 717825761
    0x106091104051305060301090212030c01060b030708240402041413051b0f16031d120c0418141005010504020301240908061003141915060e0f040b0604 66
    0x1040a9116503d482c01640450440d4045030300b03e40043c1c000b0940c1d080c0e98002ca1104941c7c106000425400000c0c100d44225081c4600d0010709580c4074810310f1814421320051900102034454100416000c00c464011050f0b030f1040800038078083c000f991103990320035552a0750180346500f0340c042c80f07401c00c0c5880112100d219691242c62180f254070000003062401d584583c00404101c0c10100082161341c40c1c40f01201c40c403070401840f9076901aa816401c5030300d4030005081c424443e00920b50203c02003c1e203c0045400e00c10028240c1d4000351a001182d45c002c415038107508040c000304a440903600c5248000701d003240710b031018018140403d90361030302404224842449255810400c8100c00c0c603014a048040c589c844442e8600b12100c0e5448482c0281040d01c156013828201e02c0f07440d0304100300200404210b001006000107080202508213600d805112568070050807800403034600c4c0125081544203d0103018440301c02c2c401031400d4000714080306425501500c4105c94000050390030700d0240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 717828255 1250 717827005 717827009
    0x31b0f081302150705010207020a150e04050709050f03030d02072307030309090513120306171c050705030f1306270b13031a1819080307030e030c0106091104 69
    0x5410400750066000e04040b513900101821101d95408001480160b41c420060303101405040d421998a22180c84001c0c0038011107002c0b0b01d00450500b01003140181d000022101120700c02c0d2481c0036208486c1001034158400c1e40380841400d480424007009012a080c0c107401080c4203104142c103005803514445039142c4140c4002000104c101d0b030705210182d0a40c20503a009440c80d5401c811411595985a0700e50070010400000203603109410409000201d140e0010070102c500546007030007901d900b0039039485203400c0d0042449000181501040300810480d040301c420001945c1e25030700034500143d1154041e00c101c100081c00038090380b002410084084480900c2c080d00301d4113051078944251034175041103817405950100b191000022030245882c1980e8201c1e9070000d00d100e45000b00800c841040d160304400d50540c46843d00200500280313828109442c0c025410640f01e80c2c0b4660203c1c003524036020702c1122400085010039280134150842815122010400e1264019002005c4a107001c0c80c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 717829505 1250 717828255 717828259
    0x207060f021e1204080d0924060b0412020f01020309120606030c040219030b0f100215090d020613020d0f1b081609090c0302030313290f0901031b0f081302 68
    0x6580030400041280c001085408090346c0082a0080143c542c070380d040c00c42c055280b00309085101005447ca02910880c1c001d401f2002540d400d0905126001e42c4080c4030401c02400340d400e12000380000d81c000c00079100201401404003058591404072076072550070544021707000c0d00c030b809105c1600f841c05000360b078404c1147e00c1814a444d8004c1c0c00c110098a000e021044d000079900041615035250844100ea040380b00360001c00f6820045800c01000c0b40000f00040c00039040030040804440d404100300b038002885a600d85c002139a81d0001601031588036030028420311001d481c60040010319a0940f40b04681a10084001680c1e44003141d00d0700c034038600c40f1f450000342d82d00c148188841c59000c184254011080c4c1c20046481e580800c1c03450307003c2c414080314401405000c03c05c46110b220f1460707a04413188008000500502641042801401c2001d0a2030102142d00000c60f486a40402112604940301801113044c0300c401038500c00c60346907804005055180000c860050403950741d00308980c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 717830755 1250 717829505 717829537
    0x309150903110717071508060105130e010303110d020a0b01051c050d0810090c0e150702030a210c11010f021c200c010c06020d0207060f021e 62
    0x64014402031040010807000d100c011820703124114001c11101000e810354150003801900c00503444d42c506a280d0344500074803040c002680d6052940002d50796000b010a08060b621003040c2440c440419103113800c405414020b10300004103259200000607a603007c003400b91980c1320284501280ca0340d00380c01c80078000121040042090341042c0c5084c04030000d04420000c6403000740d540d20744c1080c1c06182940001001c842c2404018100801647d0042c0682001042503c80205014040d051001150780c41038494000c001d0340d54108404480380035600505403000b03c031075490281104000d19125214890801c00c200c1051f47c00341c5ca200000d10f4000d030210701528040d80044a060a0702110301c000c60064140102c030a2100c03102a6640b10b2094070350042d5000510071110002c200b04d40c0681096120407140b040590304500c043d043e080e00298050303512000011500040d10851100501a5241861590b4000026400f50008800d02d03882603140c800410141140e038050282141d482680d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 717832005 1250 717830755 717830783
    0x1a0a06050904020d0f06050102071203080a050408070203030316230d0e07051906020d0525081e0309120708030f0a0b0a03080d0b010f0e090604020706090f120309 71
    0x40034a024004680c4001c0000d0b280801489501080e1401880341d46407054641a09004560301070091401503c00b001480d110601c40c0d8400800718580904550f04075a600c2000c82c0034000b4070021a07441540143c2202c2e520300380040c14407075a18074602d4039400154040c0700030580818060242a90b00840c0b0501410903840d1a0000002d00e0f00007290320b40c5101c1c0303140001749900c80d08040003004041030368000d4140e28000020381000c40300c4080360200002017010361056005204440800807a0310221020a50302d450441d082d8840c00480c0b045100c100f0090755852141040103500c9200640141d0b007045108a40c44203142c0145400205010418400140641080d00e0250f500100d240c0010a440350b00c1c401142c0840310316042540c011900003100700c42ca100038051600c41007070a181000c1880f1210704014106082000c0e000d100e4140603011030b24541c1c640e015660301ca60041010801110303286080312950f00818001c441045101e4a2818058003910039400f80f180c02c400100510b00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 717833255 1250 717832005 717832007
    0x302060a120615020318062104170304020108130f060e0703030e03030309060105240a030209011112030601180e0c04080d210903031d160e09100b062101091a0a06 71
    0x442c06c09210b0b0442401d000714559540403881c141c10480040001d100c00781860b0400c00081c410948001c0b20403c0d08009020050368400e0101c0d6003c00c922406c0707244400b1a20303012030035003020712018010a00340000301d0b15400c0003086603c201d81c800d842d024103004100042c940c0f01c1c04100c800c16900c4e00204010081e50825200c0000b5034103405101d0070f43c3c0c001e01c03c03258009070002e50000b00001da0101d42c4e000c103942c0014090407020403000040c0521190150700c1d030158031006080c20304002405140c03282041044403a034010f41091042c4100e645403a02010040790450b11408a10340b050480c0010098003c0c0c403407030400c02c0100418405100100c00308001b800070414224100760b6540340d1441a018002c140044071101c00c805040051000602459212604d0700700e005040140b07420301000e41c50001d20340d041030081038004101102c00600003041d501034a00103420f1000c20040c2d10940c00c041543c19030580d8401e110403c41c1c20b80f008180742d564a40c0b05000b5400c009000b00c20700c00a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 717834505 1250 717833255 717833287
    0x601050f0303040b070f020108180a030e01020c03010e0c1018030318180501050427110a03050601060807080f1504090813121707120807090302060a1206150203 70
    0x100e00060300700d80c50142c0e01c95041006a0101506880703003070b10511001300715a071140c0d040c0d0300000550501401245400031aa481e00c1d07403164028240034005180460310b900034490f58415540041c020031141c904034800300d445c2e8110200c010300c5103440301407005000340120310020071003c0500030b42036802c0c1503070740968a02404583c000c9103840810700000354010350f0040b05448000241021506514000034001501c0c159043c1c07140d00141844000140c0d220442c0c0b580303080c3d0304244010f1200a04202260380c500303681d00050300741c0c092200081600d50308080ca003402803402c0d503070790481d5545440c03400d1030301101170b220020500c1a200501c015840c064215a84d0b017400b403d000e40c0340440c00e81115105c044250311001c00120307408400401e110f0384824000c11034240b01001c070700c0d2400c0c0e90344094031881c41c03203202002d1107030354800f0030112485070b50200c0103542d02900031562840aa00003a240310b0403c940e501d041030400201180c0301c0b809003842c00300c01503103030015410700300212581281 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 717835755 1250 717834505 717834529
    0x20f0607050601060807170c07020a2403090606050409120206090a0c06050304170c0706110a08030c03042d23030a050f0702180402100c08040e150405010806190e060105 74
    0x402c100d447c20711803901d0070880c500f802610550384a964513805031040c000282c020f940884210408201003e50329a500c2c0110102c0036020300e40003e0344107007032400000504d880d420081e04245804802020000c41061165904034144c00700e03010b941d25000d1147d03903900c03d40b00050081040000810602e40680e01860700316100703072044003c01d000c3d6441c2c0105500301410340c05803a44058000c0000982000300d085400c4d02c842c0c00b50210407466194006035100203840b40c51080320020020b8184020b840009042e401025603111040142c6110584401c01c458400d072890a024080042c010071a98038020504604030302442c2055104902a02c45400c09a03000646c80c0042011000580d104000d03002265600c00c2d400c4814102401030002408810501000f40201c89200c4c8001c40c1c230300d6050b10215050864002e240380d032218204001507007204d41c441e421505040001c0380004002c1100e03441400e100c004044020010401501907840003070040300c8030f0f00020018815400e001900c200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 717837005 1250 717835755 717835757
    0x80a0311070515011d0606090f010c0501060b04171912090806090a05010605060307050d09020109090218040b030a020d062a03060501080109020a120507031512020f0607050601060807 80
    0x10030110251502c5003030070300c06814424050003200040c00400740c031042c18502d1049804205100f850030703a021400a1142500a6206410007291406180e22804428200c55444070082c04840e07950030109646800c580101c030886003280500c01a82c2600241d103003e00d05425480d20b0b403803855604e40500d46d0345401c140c88104001e20b0808200305000700300d140c4c090400c240051080000a080c03050071038540b03800051082c2d0b82002407000241d80007064a64044001d040011204814801070307440c4402c03907001094983c0041a0380500440000202040304400e45041c80a090900b04041e10b4103a0b83c03100960080e80e00c0c1081010411550010742c2e00b840c10010059080102e10810302c40c0e81c200300e48000081e440c1c01042c062541e100d1003103801402114002c1d4248428501c024024030015a50034403019501ca0000d01483d11a4000040c1303403501c14914151140c548002044400c5004010b174040e411444a900c00c50400d2012150b00b03c1d001b901a00c080c0e400d1400840d049100940300c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 717838255 1250 717837005 717837007
    0xf050603061504020f160c050f0901030b09191103060108070b07080304050a0618050d0c020d030f122f030c090904030309021e03150106051c0f050a27080a0311 70
    0xf85c0d40008080052540c1c40c0000500c402c03950561506145010039500400c0c014100080c03150404d4072904900c0d41580d40c4034952002ca65285000e1525003910210624644410700b121282031001486100c05140380990a48501c0da0300d641490b6035030f080b039204030f1000d002d0030044803000c82d4030f400107182c110f440b40d03040c0d9058444940b5000c060f0386034026903680d8580344c0281d11041000c2004041180c2102d4104204808404c1d00050310214500d840a010300441c94080010244591080341d17881040b82002c00505480d005012084107040081ca029590503000d80180000c41600f038030701c40c018403045d191409044800b0701000b640b0181040b000c2c140c0322119140140c0d524840c0d41040e035044142403044203060810180350203283c1050802c40803120340103106040e400000c940c10382c1091040c58540f0250003581340003c140d05404010a907152500340442140c25402400e403040ca4108840300f44601e051007418032010321172000300086010001081100d000e5004030254004580b101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 717839505 1250 717838255 717838267
    0x10602100b01090b0d0e060a05060112050601030b09010e1b0c0a140709020304051605060703090e060102160305060a1b230412111009080a14250503010f05060306150402 74
    0x1000c135982001d4070b5404115140d400e42600f071031b004c000213030b48004504024005c41c00c0c400006042c1200301c9800c0703524652a800003500d81c2e40650801f034010b40024010004540e502c00602d02ca10105a0b0049175203011020103c5003250440706440a0280e280040e0941b04529038405012800e074408001050003000c40c001f904011a1015601c1a8040c030040d00480314100c900c1040c600c81c1b03400191240300140040c0d408079502401081c03d4034003520b80310b11140c8031000141d1415801030355803042104030b01d201104108002c91254018001c580061003601c0c80011034509041006a074030001910710100061003030304200c0303006060300701065aa441c05132100904105c0c00d02a8409030340ca828105480066403c21002404000e04980340544085040c524125250668400d002d811f03104c80034402c200302441402a01d608050281c84507011074580c07401c11600055520036a44654a040080d004014050040e0352140d02c004002c0d210582c3e40e504801100e5400c0004150040e83c2030286e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 717840755 1250 717839505 717839519
    0xc030606060a111009020414010e0a2f07020906010c02090a050601090b04080c0108070305010b0702240a1e03020a081906091a040b0411190c0501060b070b0f010602100b0109 76
    0x8401544da048001140d4090640180019510041d80004c601004400100000240b00c81100c0e000400c180703000c13600c40ba01c040c00440c0b014056901070550380a201810b4026a080d1005000091003950300780c103660380f48001135400711004107000e50004100310001d020150141e20055100078141001e60006440c1e1030000550380060f0004610303540a028030595070b40e002011580d0000c00361806210641c1804202002da015401009001d0000800482c01584100d200d03c95000c00748030b04241c440c246907000521494010910720b40c440c0d210340d07800460074424004c13501035518980ba80d02c559100d0349401c1d484c0d941c6c9110f40043c1582d81e6500416501030030700502c4131310940c0c03083c2c142c03441d0016410001110380703083c02d40d4030032407521a41500002242e02500d02c414074518540c0c4889000e400705031168a524040107002e54a0032902140b90900f000c05440e08a004441001807555011826001000203001e054003507400381d92180d0008841c2c0d04500ca8440061400c484100e0703075083c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 717842005 1250 717840755 717840763
    0x5040e010530070315022a1906090b09010b1c080a0e1c03050307110f0703020120010c03091101081314031b010b01020114070503040f0c0509040f060e0c030606060a11 73
    0x281c03c54145c2d80024283c0440c030f0400101c2451b698000e58001c0d01e0740c00310804203036148a403148003460840003003021414004903901c80d070400e03500600349da00180b42103601d6900a121002a040c403550060009003102d000903218056030541c45a03030a843c0036404482903e103421701040311070b4804030420000345080d10507080c81e038065100351151030722820888406011540003141500301d90b400003040b251140c10004520048940a00741404c43c48116401d4840001c1213a5801e0203c0d800e00c8503d030902603040d844004c0c2940102002800c18804100440f80c0e00000d42c0d80d4a0f61010341c0503240081011221000d1240e0300100449203040500412003100008482681c0c4950b5580c000044e00c958080c090300c214a250039004024a2410f8270300a0007030302010340042c20b84c0121003400d90030801901040780140400400c0c442c02407600d45001002c0c0240f01e44111022814507d401d40030640002d40000c1e0448024040c0070540c4c1d03250180f0210360403011030300c000c201102c0760110391514280 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 717843255 1250 717842005 717842033
    0x2280b06130c0306060f02030a0903150603140a0303051e0a0c02100f0e0f120d110405060301030b1005120709020d1d0a060e06012106091205040e0105300703 69
    0x144020400a2500401606c10038550b01000d0642d00104514819a640045d8a00903698401c1e030811025401400440c01048190002481c07005080580041c00000140c6c002500384a84d07801d102617034036042c0c0c4140d1000700d4808101000b11850215030021055001240d0324070292046078000444030880c80160740800e02c400580580c3e80444001c920824050001e0b000014402041440d90041c0066a070f40701e00740383da180041c1d9448408002d40714620499006140080446071203503168203100720185030a0f50700402e90040c226000403203041144801ca0345500030005403540f81c0c42e0141e090080c0d0f00041c03000300901d07900c0500c166040d801d007400c086003140080017002d41c40c1c4903140141c2124020705c40ca040e1903000e100100032011802180609082680c0140b2103c4e0003180352100203000d11620041815402c00741707024150358048090021a20b620907801201c4e40d0300e00130700054280c60710b41e0400c02541c0b1110121100c0880309150540a03101e012100d1082d602d890710000843d540d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 717844505 1250 717843255 717843257
    0xc0c022713170c03030103020d08120414010f060806010b0f0903030705060108060903120402100c0b0a02090a060903080409090206210f01091814030c010e070602280b06130c 76
    0x1008481840b00c11110300e0b14030004030000e80e1421280504143c1d4a01052100a2191031921012010003040e6000c0d07440d805004070411405050030320704126003100046030503000d0340c030340611003100c22038070300031182101c8140016000c16400c007039450390142c0c0b2004070910040d4003002071012540f4100000e10105006101404032541807203050390822401800c02c181c83c0c0d00a0001030380b80c17114401c000d904564102e45803040c240003003105071041d240f000005491089800100102c2d018541c0040801e60400c1368011440c2c0d0b00d44c1e100b501c10084500001c0c103418400d0009000b82542075000c181c0b028002000c06041604464481c0e03041681f01280b058522401010f00002d003184030180b0303005d0b240000090280c0040318141c04034002c0c0481001d485005008040d4480101c00e00803a9a0115410b000b4007402d4000c00b180c5554008501c621401840b9003010211184210f010101080c0544800b1a441002584450000781c0e409819158818680d80c1c00c04405021881008103100d0302d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 717845755 1250 717844505 717844531
    0x40902090118180921030c02060a060b0417160602300702010305060406231315150905060403060509060c090d02040e010902030717010f0c0c0227 64
    0x10310005049400a40d88801c240b9070224042c05041240101641e0a03a4103803c00680183d042c14410a0792458904403800c0d810100c01c814016030307240e0011560061140c00729a410744074000e0b5101110164840d400a0320010300c0f05100c1c41000d1703a103260307031070005070226521048140328440c41000154842005a032082509500d050f05000086820b020102d000b10001800c3c40412803080c8a4180001c0c100b41d61000010461380c1e4603403010000d80410121918950f01322200f5405148000c2c00151103190341c23200e007004c1407a0f1400344c40840100ca070020070961b45012000b82038925204403000504c14610000305654032800090401940203440105070b600340003007200e00340788014007121003085042048080948801403100400c80c2d054134001000a180030a01340144080c83c402941801000380c005004900320140c582a580800c00030061902040b404c4400c40301015000d801003043c01c0344131000361618006040c00b8001c000019444860a11407800c00c100d41250b080780c80b011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 717847005 1250 717845755 717845767
    0x20916030c0201060b092e020109030206060406210c0b0a0c03110109080a20010f0219030b012c030105041b0f0f03020d03020a1406070e030613081608040902 69
    0xe80350240c10244025030000304852410f0002c031040c0c40c4a003d681c1d40c0140c1542060f0080f1070000036007181100042c2c2001c412500314050001c1c0601803280e020b40040c8a0100410441c1c40e01d4440c200803945a80312003240341030944104a00142e9144e41680d0041041100240483c508030040c800030851381e0b944140c0ea2036074030300034007141040ca10060b002d07850403081800249a0008484403404603041c10320002d44c1c030420f10090003a02e50010081c0e5400e18242201100054018050609a1840b14020714540322011021030307181c600c00c180016030b00f140103242400107489042d8174002041054403080c000e040480c0c25640d00f620211a03011802c00c5022071802041511401341c00480305502941c0c1c41d09207030f0159107803103003c00303881801940c22480c1018020004100c4195100355100140d21400c40d449407508402c1b28100007140c5a10b550010b507150100d10907200b100c045d01518a40030ba507480b00341c9280c03c0300503400c0d550f080306561213002c03801000251004145194001da9654 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 717848255 1250 717847005 717847007
    0x1b0803091c03140f10050a030b0a060b16060f06090903090f1502030f0a180308030f060406051e0a2706050609060a030f0b0909061b03070f0c020607020916 68
    0x301e10003100e20070140361400c02c48010b4407103508580c000121545910464890007042d46107034800b075209079404045410000704001d15080000d1141c00031240420070513a0b103a81c4c5644074481c0425008454408944441c0052641d52181184d00f420b5200002c51a440e141ca41c000c0320881c40094020449280e0308010012911113130303602400c402c141d50105030708803c0000e580c0b80110002002c00e030301d01080d042c0750342d4810311000002230350b5821041c0c41da9a0324180080303a940140c0302d510300e10840c0e500089980c2420300440d012101e0180c010355950b10610b01c041f4486140e010b107070341d11901d001c4000500342107203010210464042c078040100b40c00c6140c8200d040307070135652049004038428001089a0760315041601c84031290b604011481540001d222002807401c01113595001d00a5418040c9800000070350520928509400c01c0102c030101805400d28001100c070070000412011003110002d01c035040d05100d007407018019600b414a6075000501d0001c0441e40703841c182405c810b22030003807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 717849505 1250 717848255 717848293
    0x121a19051302030f210306130213081513230717060906040b06060d060e0115110a200402040803070605100e0f15010225150e0d031b080309 61
    0x1c0c41c8404d0060401201510f1850070382c0f540381c2601c0020b142c0200c009041034171142e012100b03240b809a0115030707814000114070100034071800b075100d240c0301700701c2d900c865203d50350641401090740308038105000d182070750f50303030700448900d042c2c041100002011541000b008000410180030119540200c01d800700c4545854a50010141040c2d079020806200c0850b0b590b611058002605580d810356a500002011002e032805501203d52441c00c0000000c5e82500c2d0350303194581c0c4455a48403400880c60a000a9459018400260071700c400c1001d44a8250f180107800c0503000c6c0b0103000941883ea56070346440c203681001c0c2040c1d0700d02d42c40f6010041c0c0d018500c02180c01600c0308000340003c03410541880042c0c10304c0281112000c00084151603070680c020411400c1d0b203120110400010207004c4542c0780000a03a100707202c044081c80049084da18001c240c1e184034144050217a2030043e0560b00d0854040800c4190060003580e4400d00e4000b00c0c1c8058011841141c01c0c41c0240540901c0044080b01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 717850755 1250 717849505 717849523
    0xc0b0c1b030316140c0a0309150e1e030a020607150e0d021b0f280b0c1c05090d0606050a0b0c0a060b06090402041e121a1905130203 58
    0x8103070020420850402c1509504600c54140343c40c000749180c040c010798a0551007000c040241c01d1141d0000d4108040e4840c400308141d845e0400143c13900901c54000344c40c810040303c0d0305a4000500450309200d80c0e0168403094184900808035003400d1519000300b0000d1303000150035620300405000603805040700d07003d1442e0718015900200103503000c2d903000940704d20866202040e107040c80c10007440541e445032820030302c0001c0240000000c4540707587c3c07200da102200300b000c070041146610000d45c640c604802c0c1c5401440003009808c0741507810f031b1904000d0360118074003c03d0000903c8a030b07016440742d14450222038416000056843c1c14a001c000344c0b001c1540c050703102c8078001c0007040303c624008584219820f9121101180301100303c000140d0314000d110409402c18800326000ae01ea12100725000900c061503100640f2207500c0e00d80140f020402000e0240c400b65aa1440c00b440702c2846217440d42c0507010605029054a02d000b2030000c0d07403015510901c140b048941e002055240c18400d0541d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 717852005 1250 717850755 717850807
    0xd0e01200307020601061d04050711010c0206010602071e0911130e2806150903140a02012703060c0507020108070809210906030f010612020f0f07030c0b0c 68
    0x10952621101c000d5503950140100800c0000c845c00c041103244003d46080203111f40140180705910786801c00805072481ea00e01d5090940c01c00000984050020504038180c0e54a94003820743c503030400d41145a106107160300e11215180e403000001d100e04683c80b4040002c071944a4842c1d5400019058003201081a0081c0007400442c0c001d100b80442c0d220400c02d0170b40c1100c680000f43d00e05409161008015640c0f080340180c800c1c904554104d07a0003030380034050b64400e0100c0015800e401e250b150362000403020081c04031b04091940e04c850f4524000c066941d00f0210002c003080da4481e541c0e0303402e07100300327083c5500454001b00d0034004541e08009501d5100410f03190190300c501d042c40040d42c1d0f0b030b039a08250f22881d00e140300c6402402400241100c6800b00013030100c1d9544e05081c0b0202c50443c1c800d208080c00105646200b0a210b115402140c00200d644014a403c1000e03132041002d1590000c0011024000101186000541c40343c00145c424080780d11256161281303d5203a00c0070141d031a0000c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 717853255 1250 717852005 717852007
    0x8010e070206060f010e0d02040f05010504110906160c1206051602061608070203071e022404051c060c02010c0e06090901031214070c05010239060d0e0120 68
    0x10700f80c2c95025a2102c19078091905006502c414004100740031010346000c1d4225040516198280440ba00600d040761026902040400c2d10030000043c2c1d070040321099944070f1002c000c0002d001845841e00c0361114003451041159503a0b038080080304007898481160450f440307004020940d0642c0034141c42c1015240060080d91810f03d03130304421114034100c0702090003958130210761040e00c02c005032050a5400140c00900065900d8820030b92030700440c04034030a941c0303403015908414840c13170704001240c1444140f81c101400d2004200300d201c1e01884507072800c40a030641c1d5021507594050101070101603000000c1c0001902c000401903004604040c1c042d01c0c080200780c1c41c9031a0f000c40641100c1c0c000c1703c2460080e40c5c00000b1914207861140111040501080420911070000503210441e4026001c451a5101070441c1511070b0070048142601c0750000000300013900061442d444d510321000300035503d030a0059521500f12105540c1c0c9414a0703666030b0300340305078205816400380d08040244d54a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 717854505 1250 717853255 717853261
    0x30f030e100e010e07061e020a03051207120c12060f0f03061a0a03030f1205160305061f020f07080f06190204050d0809012d0f1101060608010e070206 66
    0x140d035150103419550318035036542c0b200c41c40035240030740c018103941c01104c0c00e494403540d54000050030403046540c0800824250b003c020040d500000342c4ca070300698551595414002085401c40d0b8a020051003241800148143c0020800c002c1c03061040401003600c0b00340314400518418411508190003118044506142c10f00650010300700100c2240da04c01c4010551450009501c40e00203503110659800c11a07100340401019000b0030010a036403030300e039540c4291380c24501c1c0c90015210b050b240190441d880f05061012340f4440d030803281c0d01c26000f4102c5008401e8028141920400c0c807c094170058000310f0061030522018010040180188070041125503042d90103546c68410103411040d04d0321b80e220888040c513030103805580042200400d41a6202042c0c00c0c06296a80700e1030003540040e601c409408400348010300d1000710030315040d030b0b0052110001a030a950030201681a0400d11644000c0a8a494001d0103203001030000350f1756180082d41f425540e144e08440c0508030301c2c10b6400400c20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 717855755 1250 717854505 717854531
    0xf020c060f0118020a0c05030c010e060f060f011214010305060601120b0306070c0c12080306011416110112020c0309030d091505280206040c050102012304080421030f03 74
    0x84201c1070600f0300c0005035644007820094850b106403200c018600e0002164941102c02c040d442070b110030106c6020b848250380c0d032240e03542800c942198026848071039807040881d203503c680e050248042d01d001d00054605542c42c2002ca510340260300071607280d40424100011541d000c400121400c000704028407600340c0300000261112001480305041000540820042c03001c2032082400801401d5840421a40f860428002c503520440f0080d012a02e426400810180d03000c04036003d000c50382048860004d007a0782c8111001003110159410000594a640c01c4083c0c1e40c0b00500c1403010ba00e0055942e0151907090500303244501806d6010700100607010030442d06480e42d03240740c484d0140360540d80c820054480040000740700a0103004461090310a11502d60001601b0780518081d6032424481580c8000490136a21004554076081805640c09a040211100042c0d0032601c40d003041410300303031249003082da81000101c1c3c021900d100141c5080c00d150f0820402c4481760b000340360a000348410262 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 717857005 1250 717855755 717855779
    0xb0f0a050d21020607020105060a060f030c050928051903110112090f05060c0f042106110a030b0303030105060306130b040c020705130b0109150c060f020c060f01 71
    0x800c550045008650311000c0000309219071107403040e8103070450021503424034029a070b00c0040364602c0c095071803c1b020070400d02d03215030007008a8a86c0e1780c56050301d0110507000c40141516020030300501800703102e42c020b96500c0c09044010305800380454a5040541c0c41c0c4000c00a8107584024080c107042c002d05040c02080400003000c0c2da070840081b03803c85a00f44012100b045080b01c011b009145451041401c00002003601031045020f42d044480311b407901200c0880d40d218110700fa21030464100400c100c180000036103207582450040007120780c021716403114410f0701d266500e6980c42c1d041c005880c2e801150140306026000a040c3c005500315810100407824134803014203054071641c3c803040ca48400a149401c01d294081003d0030502040c4512030019645035400e0182c01d1154902d0710301155100200c1c400c00081380301c142d4584458520b40744d5407502e001104042102000840c8810802080c4140034040244c0642c2c2e20050b43c410018014a042440c05410342241d00b408400400042450b08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 717858255 1250 717857005 717857009
    0x120307020d051504060212060108060a0611030405100306170a0507030f210504140103091703040503040f08070906150c08030c040e0109051503120406030515041e0b0f0a 74
    0x2491074510358049003045032806040c3c2800b040f07034145a00400c0b08020158010300405482c80c0d000a5070b54848800641b000c11080f80c407641c12000340041040000e204480c5480c1d444800b60a807854039440f90045a80111148100310100740c54200c10421815a088541100101c0c140034109031149680c88075142c80841c40040e05c1c0c45280b40800051059282d1062107043d10080500c03020b80000320040c140e9003040c403d42d0101044051140525402801650040c0ba4020503d1040c2d0304100300c1c104281d000030340142ca070351001344004146014682000000f078014000200801881c041c07070300c03007600e840b5000000c01d94001469401e0b4250099800c140d03c0b580b2541c0152aa07032490f5010320b09000b44e07409820303545034410000a43d030010307a210030300490300d42150400340e035000d0090650341c400c01110080701d901d04120401c50280300f5840f0a030000030300b90032620001c5555000070f0aa91403500b6102c0c00c004a1240241500003e1049810070070f0103076141c07103112001c8400140c05011034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 717859505 1250 717858255 717858259
    0x70608070e04021b0a0507050411030f0a0b2817060601140d0f140c0406080711070905041101030608010c14070f0b0705070c0501030b0913052107050c12030702 70
    0x11081c0106076544540503a5004010248115440324851101540e1081414010380b0b0364040c029001c03d69041c140286045480c0301d004091468590156465007190010f1000e03035a075030b441c44018a01d030740d0580c1d0452800080415500c0407000c095010a200304070381d00c281c0d00700c0c8001c3c00d64680d14a000c21190343c440003d08008091068603482c3d03801c0c03840b61801c2d40c03800524010400000708010352107450f45000720310b030781c01079566070341c038880c0d56403145004580100c0d12708000500321520519681c10414500400d440c030403596000e8410a40307405890484901440c12004000c0356814800c5100600d10b2800030311030746020000c040c25284102003444c40001000400f0000d110305041d407001c000754012076135400c074580300300010241c1d0483c80040f1000300d0f40b9800000e007076100380600040c2400041c01240c1580350710011b90704200c0814411182400340e085020020020300c1401d00504c100100d4041d81c0703d4092409504205080c0e284502c02d0400d600c2d401d4000c4000019201101c0d41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 717860755 1250 717859505 717859517
    0xf040c030303230106090810020918070e0301050403030b0f010801050a050d02124309020912010606020610080105010e040803071e050a110a031d1c0c080f07060807 72
    0x500c8126242000c2101c0c3c101c51143d01500020301103501c07405290032102c00380c042d58038100403d80742c24141c2c41841c2d07015501003c0c1c82c803c002064001100302e50044680d0034000f028080403004a0b0130358004a40650110355960381301800d9040c20201207485c44d0b0240380500c240c3d8100000524510300b98010203015a0809070514110f4071007581440017128907808403024070114101c2020240d41c289014a8050010b0410121810000f001301d02d164000010240c4254140232564000f5003018041030360040d40c84800c00281403003845200701910095000d429a450f1034200c0300c1040200e81e02c8000e07141c0c03400d8010400701c0c10a50595800c160300c4502c044d03694860210466425888a030b804240003041c2400d00c5410b50403000600c11001d02d6202d00c000b42114450443d15944285005000b041643c2c0301c002d040c03114a07000c0c007400c44009100170100d800c100103c050a042180303003240e9032003204009009000b010002c0c0d000d1013581c040280101030610341c00a0803400090f10400920172 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 717862005 1250 717860755 717860771
    0x1c05070302160c0303020c010207140405070521061c0b15040605191806080d12110a0801080712170a021e240c0a08060301090b100e0f040c030303 64
    0x1109404071032950044084400741d0b030400703007007500754030220344021070142c42590140b01440d40085200c03401c450754910303010000f5400c48248000380200070702e14010440e080003420b0380014000d201601e915100d41c942500c92a000c1c0c10f210460f0144508155402e401d1525500015045900d01e42d22035004400c00791a000c0000c04240505155042243d0050032040c40c0e03008014210329407411620701451111602e117002d0b048034201c032514014050560420f10440350407900502d0515054814107800248041c0c502c2650404e9421503220000040c1801004016100c000c000403c081c240e8001c540310311541669030720002c0254501018404003000c5080c01e0214000d2288a85201011085001001c0386d464400c0e110140c01903d020320380d0003c0201c0e16a0384040042c94030403190311364070764a411012182074511342c01c0100107030b5142d92200da080d00012503208205004a43e00c8a4201c0352074103017210321484000040c910401c01c101281008081007910b101070048030b030142000a1508 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 717863255 1250 717862005 717862007
    0x209060901050921030c010515011e090306060b04050a0f060e210111030a18020f04112a06011401050f0306040912050c01110715180c0b09010e061c0507 67
    0x1160a9501c608413180aa1404241d06008001410010710940c000c1090390b8404c02005a04481c07034040c140080d0310045c10000510b070580791190810954100008901d6990303031040140c510540201c10901800300302000641450500c0c40003410074215000b100a042038801065501002800c034880c0e240307071055007015509400080c2d503050104000b0b206500c07620241c130003154801d5540c1c2c90024501102804074444180c814600142e0003800d03640b80c11185820040a056910035084c1140d404001c409081010b084a480341e230026040818402d510030710b1500c0c03d1140503405030003909006500030350960fa102c0119014080c480f18481d440c0c1e20340a0200303000301341c003c0000380804040109104115006070192802c3d0b4460002171000c0042c03040002000e0184081c01042400780414a482004c2550401c50649800e940201c0000340b0b0fa0312803142902241e800340301e50002c009004003040d41d0150210380d002078181d031103601e00107140811440c504860fa204100c80340d80c89010990321 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 717864505 1250 717863255 717863269
    0x402031e04020d05060403080403080a0c0212090303160c060306080f031603090b0714011d12070302150705030405151608100f030503030109060e191109100503150402090609010509 79
    0xe5500402152840c6c5800d1602800c5c085c01a44e0a0f00825400400500c0407491401000c3d10111180c0c06407000c010300c40c900310003603003115190300d078103000a000c5003008191040c0902001409440d101c00b9543c601f031806012500c0c50b80003121540c102030f8100949000000c1200d0204003024107105042049080c12160721800f50002c0c4c5c0080390000d0f00e0b1061242c41b0801c1d0148946140080004000042c020115403000301c1041c441c0d134110011a0b21110460300286c000280a4015501034004120701104d00e42c40071121900424400301c01c0c07106100702000100012032515013141c003103041c404207100a1141011404e800c1080c800d000801e5009040b17032420003040c5150005030301c5034481c0341998580d00300740510070842e4585440052124480e0700c902d80185030182d400d4a1600001061a020703106940c500d01002d03008104600745621451200d0243d240035984154813400e1540710207040f80c506540b503c3c07099005000d404e50654488003101e401c0d1100b400c00c10b80e41ea64030b80118020b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 717865755 1250 717864505 717864529
    0x9011a03040303060b1603030f0c021504050703060c02060403020d0f0e0904051204090605090603070302061c110307120b1002031912020d050924010306090809091609050402031e0402 80
    0x500800c041d40e8040548246d20540ca00c01c2d00c0502070703108520010411034021410000040e48448511000703058918011078103c0d00842c05e40f171102d40c42c2d8450000f61080d4009110042e4450003c20081c1681488208400107051805101d0550300040050000d0304104d0054800e900340c4002c14204081040030900c40903403110b01c142c44035030b2041c103c8002c220070b11590b40103400c40f00000c0d000745000300320f0301c05480d0b00421582c20100d5100041c0f00381c3c14031a40900e1040e5032501c0000b414844080914400d41c901d51f030f40c842002c00c0003052016a4101041c05001e9201104140305c020707000300588049142d521550001549068011520084000b130b40d045180d2001074224230316007540d041a031140f114002151056210301141450040743c102c0c2236000702c103401c1d0050000a0b0540c2180080600486800d400d0940d01c00000c0c0c8211015651454283c2c00746d49a01c59403030300003440d8401007100700c0d4214190318062400c0d42c4424005204105002c20300300011b4210341da01208465 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 717867005 1250 717865755 717865769
    0x1115030702060601030e0c0a03081b011b05090a030c12120203070b070f21060f150e0d08040e090a0606140a1a0c0a030201050118020403050316060608030c03090f09011a0304030306 79
    0x40611b2740d90414076003660203040e040181c500001808007410710305000d103070b620104841d0000d83c1410700d1703e42200c17a900000040c940c020407403000003020583c00210900942418001460140003031b1518005078143c44503408103540040c001d43c408914014929584802181029648006070441c00c40c0c521559541d1703002c10341c100900d03641a2204d0355010500380d9502600303030300a9079211041c0c0303250350403120028070010b0180340344415541030140019034128410000d80d8181519645202030713240080300c0c401480c1d0302403240b142c1030040178000c2c00000c203c03d880c0e5440042044020030f244d1055405402925144104842c40e5961210100c0b00c0060410058400c16991850001e02905e07080c802c444d0350780e2404000c045020114421501280c0d4028000c0d07180214010103214100d034948001c2ea4400d17a200c03000140b10b9414001416072511a1014550b140001001c00c040000462100b42c0285034100041c00079025844d001c40c1c929829a00c01030b140e544034034044001d40100d0304200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 717868255 1250 717867005 717867019
    0x5030d14040b04140909071809030513081c031802120f03031609080d091401090b0409092a060522060e0906030a2415031115030702060601030e0c 64
    0x240c03081501c2e000484c1814110394801c210317110f03c280d043d03071452a401481d0b00c035004001d1803020280303207501c40107d091083c200a814100c8070480006503250503800040f0a0300b0101e940301081c00300c9400d074240440c990a0421070384040b044400100c00c1e01040081c0945a044640c0c10808010000140b091840303004503030b600d240407401c17203c03141003013042e6801040003042c0c00300d2141c1c1e01007100c43c02803178143c0d20064080c0c33400401c00d4810025089190511810340c6010401c2000740008001a190f01d0002003900800c901d002648001c049200c00e82401c1c0c051110070f6421420712956040351040c1c80e14a494034112582104825010401d170110800c54110014a007500202800402d40c0d00701e070071031542e075225414180c807280c003c00000c04000c6400d10503152076820125010368110000e60004d15141120054032021083c0d400545050304941007081d19850860103106a10080c08035660445c1080c4002941c1c5004c040d003040d040c580c580e19801d454020401c194046884010800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 717869505 1250 717868255 717868259
    0x1110d02061909171b031e07020d0b0406051501020105090715050d05040506010303030c0507050606090712141b070f02040f0e0d0906020c01051318090503030a02040503070e0105030d14040b04 84
    0x9420b007035010030091602c0421040c030000905c04040141d03154030000d89900c1566040382c6004011590064004aa101d6820101381e000b080c81c0d46009403040342710300000a4a0f041541c20441d8103000c0f25000e504581c1410204140000003090060445001c40c1c00700c1c03a5103000c010207890500801c55405816884c060402003402030010300d2904a90194600308010a415141103036540700f4030502400503403080380810441c0c24081c0300c4036481011403400031080a8400d801e4404e4440c1000400c209000c14024868100b00e504641e01481d88a0030000346000440c0d610048101c5004101910481e41c0f204101d84280380340e00714001138500b0302c05540e00b89501007000303441c1480d680101c2005100341403000f00d483d401141145d080207010007984081501c1d04035500350080f082840800300c1a200e0030403000141e800c1003d1402a484000e0168440781000d00340b5180070b0450b40680200880d0000420070f0b80c5001c00c10030500305040ca0b041d110460007450b1082c55101300c0c0d0042c4400a800200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 717870755 1250 717869505 717869543
    0x60905090403052701080109050c03040210022404110102070305070317040b0409140a0b0a0e0a0e01060e01030b130305040501030f0e030a05040e010e040222150608010501110d02061909 81
    0x4101c044c14001d817500e54190340c0f5a803128040340c0040b01c1001d5002400c00c0450b016281044652000c0318503841100e44d8040703034071500307042c0d8401000307081c0f10a41ca80b0140702c00c01c451007c280603640c03020b10003041d40034915103500e0395500e034a100103001400710710b0062040c1c00c0c411041740c0240840f04000e60b525561441e80700014071740e100b40c1407446a02200803d52203040d6002d2095a910000d041d402c070582040e1840d100081c01600c11440e00e80c1c0c2d5100c196480f07100f801002c00400f40f55120461943c95070505005840006144090f1050550700307400000f504030040c0c8054030401e280c0001d40000c2804442c005050701c02d92900f0b00e11010407d040020f604c50010010b0354100d10400c0e105981c0ca1884000b600c3c0c0940d8020750040040301940100d0611340701c510a416110100421004201020500081c4c00c3da000b0800144181f030050002d03580060f48015142c2e4900020640342e5030032440251a6075025022000300645072240b10142d18403504125501c0360001140000952a565 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 717872005 1250 717870755 717870817
    0xf1203110a0f0f021f0e010b090a090c0618121109100501020c060705030a0c03092408060603090706140c01050c0a14130e190509010b0102010506030706090509040305 73
    0x24144000030581943c01d100d2a03c003141c024216041500039090150a82c05000013601d040544003001d90360368000070b070a81d514030007124060001c1040020b1130b03585074146004006615002503050103500c108501181580401d02400c0303d082c01014802003c0742e00d4452401e4120300c0c080c81d4030036090350500c4220f039003044509048500903003c03285410001e0051040c1c074011941b01030042d400034040403070194040c45462a001e446480d090412a0b140e0b41d20520062490b60000d00300120b00d045140142c0d00008107030340044007119202c2c11403602c59042a6100000d00a500401031147c10f00c40c040e442040030f03900c40c120814000c0c860381c54009101c04858000c59143c00002d01a800d030500082e2444084802e48580010f00c965901d080c9802484120710240045d040000060961826003100d0700c205401120484004100c14214100080c250350003e0a154401c0d04103400c10001340782c00846400c2240c2d0256018602a039460400313480a004641500c603940750007110104211060345 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 717873255 1250 717872005 717872027
    0xb030f010f06140403080901020a050d08160318020f130f0e0c01080708070c1a04030c031103030112020111071d0714090108061903081b0f0102070f1203110a 69
    0x140700d040c45941c0d2508212950007412107000c1c0b01e40d07820001480070800002c001c100e40141801200c1d6551210b0395407618040c3c03204412000981058284903d451a00c500821071049600d4103000302c02c42808000c8042d0b411850007441013035011514038190700e8100501400346130481080200100b1044240081c0c12180035040050040b0200d2100c02d6000b01800c9005034443e07521801260b440d004103499900701c6c110140c8100c42e050619507040381c0262a0544103500c260b86001d015280f600d0003820403032254040c00c103075400c18001403004d01400c210b800061a02460903890740307104004402d0808000b504248046408a24034984803401c140400e8068007482e03984281c10001c015818956000f440c01d4240000c0c0e1220118080e80381008140261084800e07141e03140176625610ba0445612101c01e40003640001c80c80c824040209000004606014600070742c6020f00d07640c1d49200005a4400c01800c4455248402c904148283d10404800101c100c40c02c0c3d4910020b000604401454 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 717874505 1250 717873255 717873269
    0x40f020703090b07030f1b020307180b01020a052802030706020d080705031006050f210106020d020a0506060622121101020c030606090c16081206090106050715060b030f01 75
    0x44207000590420b01c80c111303900103406075161a01c0882151044070840f1940d0b0202d40426080c0c4410805a903052110400800310b81c0c81140d41860502124800c8e113180800c1c080c19900210a0f030030125601050200020716445054006001440d448050a076100c2c41c2c083e4061040394008121181c00080e00c010412150325410050b84c0e4400c001c03901844101c40d29580c21070303481382c01c04c40c89004001502001d401e00119500341b0030218004401181004061310300b00c113080c0700410400b501400b031030b541c0c0d2890344080c140a40c40d07601c13101daa071800600b01b00d001f103500082040e0700a40c11703500020103400d1900403c45144ea00c40300302d80003040c5a101030319504c41c4070302d08a00541c00000d40740c1e80503c011380545101ea90b0002008140c030f100420742003803040200046410104101031692206104a81c8951a072898150b000350941c40104401d00980e084001442103a400c00d040c1c829032a4402e40c1980341100400022015049a0b40b1180e0458030200600890005071a80d46042c2c8480e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 717875755 1250 717874505 717874517
    0x403080409020406080c03010305071214060f0f0a02132d06120515132a08090708010c08220602120402030c010e10030506041d031b07050f090601020a02040f020703 72
    0x46c12200c3d02d0a88028880200503a00c00482046907800c06d190100080d4000e4141452040744d00464a00704041250000a10b407502c0303040001400b82c224509401c102d240100718204001382485a1402626000e4580c0b030440422002244003c3c0f2150021904c02c0640801844c030303900c3d01d029004181c0c10050800043402c00c800907000300880e0455085020005100606d03281107040080014007242c4440b85091034030b82c4801204664a00d20312210f44150764a400311072400b40340c140d0604a0b0342e0840d00f03030369047c0005110a00d0380018084e0708074500c5420848070f2070490983e88034001110100400c220300118814a10b1a101d0154900c107034002e4064403080003280004440d421120800194412590301c1608070b1b00d4400d5000540c440301c040c00018030190ba1301000c520b00020f20b140710400798400182186a81021445410300120381300082c0640e60801000501601d0219481d9000d9842075000512aa1080105080c0c141d0080d000f0007283d03003c3e60a110213540080d00039004611 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 717877005 1250 717875755 717875761
    0x90b10031a030312090105060d080a082e2102030d20060f0a0c0801050a27050c09190503030a03020705031b07080c060702062209020f0a0f1701031502040308040902040608 75
    0x49c0800c20140440e4442d9082d45800d080000c161784400e80904080442e009900c044030b5080b800c400d0032a91280010a00500c2901d40601c43d80100c4002800040d104c624003110401038038000b45480315030a240c2844030501d03030815070006100310743d0031103d5124841e03a4240601039291070b007030600a0041244c188001c141c10b89003613510b000288511a040354003c41300300004180c00c0342e05000fa00580700045a01850b81e980c09060702e509403106c540071640060104203c0c0303480000034651070b2000c52450901450180001c0d11782c0a003164100c145600040e00800f001410710488445010041465580c95140e840240e5504068092502140300e494441c06203490b103007042e00d420342d9005000601e41303085600041943c0d0894112018400c8041c5008660003016001070301c1910400b06010741c460544140040855044000c10010b01101c071003000c004d40300e50070318141502e03004050252640f80c003071400b500070310551b800504108000b1502240680042c1c00600c01c03034080744d8030003215032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 717878255 1250 717877005 717877009
    0x8070506070503090d15020d20120a0b040908070506010905010503150c030a3c181713091a010903022107050a0906080c0307080a0b0703140108010213090b10031a03031209010506 78
    0x32262907480c0080e0600340ac005101d0080750b4104162005019102241100c11581c40c103840340c00101003290240c015030014400e000440c42881d0041c04110005c10002c5c2e240c3c080c0c0c110f0743c3c0d07002d009480c2d0084000001100c08040d90801280926080001da1075a64601d83d2141c5002961000a10301582e060305580d82e4500b40c00b0306c280c030410340c40209a0b43c001e00d07030350403400f4044c05101c0f811000e014013032184003c02c003032a9540204526107010031050b803400b0181500faa000b07008217061060144090016071140b07401d01034441240504a074900006458032850580c01c0d901080e84021030f84404100d07484290000800c980c100e400f12038603c6420400c02d5151403482c01a41e10310761100c409030010580100313099412030311134100069038401072080c10310b4040098102d071030140e400080f001c0759420b0a1161400815035400d04000d9a58400d0000300440c07030140c000020961601c064244180e680c4060f6131800d04001c040303a03500c1e000b890300101214800c54401c4600d51030310000401d14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 717879505 1250 717878255 717878257
    0x2180301051524030f0411030d0c031d040f0b0a1d040813090f06030203061b0d0207060209120a0215031b0a031e020408070506070503090d15020d20 65
    0x1602a060501280d02100051159034007489401c0c4095070112030f8488400303485400150b0050040380102d046511701070428003a04d500b141c441600036804512400c0c071080c0d2100070b00c4c51555040c940035008500c4a0094030652801c20101c036030107460988804010350f15079000c0c1c941003000780c03000d0b88401d0307031403180c070141c01c03038405c1c021002c00d1a240c0000e002070200070080c094051411550489603490319440c40c02c845a00f1801e001c0c4982e90300b418819407400b0010b1a92040700740d108452090341080c0d200d100d9000d156084c011280c1c020440004004998068a0942c0c0001e41940c0450344031a61142e52400b544009a010f10103000e039001d499a421400c8900c18060742d850a02040501165003080382d000e85800c1081541e40c0c0c0348210710400a0490311030030302c03501c0d40242c6ca960500c12403d040500c240c0c0907504c545420800e41c800207001209a0b85c0000c0b04840b902c0b041511030500c8500c13044001140201c02d880010003600c912010350003040b021102d600c08242c4c5407203501c960081 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 717880755 1250 717879505 717879511
    0x1b0c06023409050603190308100e151207091112103506070f020c0307050d110105040f09020307030609050402130509071a04170a020603040305090a180218030105 71
    0x641940810705014450391a00000e800c580c1c080c00b01e0340e080a000407441c1000c40e100303401b21f0004070003105100a06203804005000b508071020020003500700a4040c0e40840300340c1d07032901d00401144800b6180d640f000d2082e00c0c002c182d550014005040850b0b105002a8455a0190030126066011451566101841c1d009840f001184030710031401300035143d0841c100841e03445c50740000ca04040c104454003400541d000340307456103560f41106000500a030400c11103000090080c0d200030001c01c00ca035602540656040d41019260107a0b00c0c182c00100c40a1040350082c000c80401d0440015219080d580150b11810292b5400c103c03071a107441c000300c2510810740e0062f500401c000074082403000d8952000790030642d400102c0e0852607681c500b80c84d20303c4c2802c2c0e40000c1c865011808021004401002981c1d00c0741078405403801280c41e0340082d105000240c005800c00c41c000c610150a5200c115018000d098400085a158540580140040d40c0002c0c1b520420781360340c3c07080148605050040da80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 717882005 1250 717880755 717880843
    0x60606140720060703030209010e09060d02010c060b060c030c06090714040507020705040e010204060e030a0c06050a0203040812030a1404230a0804170d110606011b0c0602 75
    0x8a44003958950310307210400d402070300c6407460702c00d07541114564031000100f1595109440c050703152070903a8000340c0190580c0b90140e0146080788204070450780e56803403102010381e090819081a2181d410440001c049011680e908104001841d500c0080008080c1030b440100350215001940d40b07102d03039a121340309849003a2103c00c8030280c000c114070f483c0c0c110542c0030440d03104541e80255144005810340300804d00758034660358001400d22225510190703040f02140203400805921035556a000c1c0015400d20400381000804507440360204d109200300c900401481040350b04104180c150144198020344600f12003621707002c610300b09400c2c051449880350350401c0c51071006458005c006c24107010700c001409100c2c018000442c000030240d202410140481e000041c040541c0c11400d2443e004503560200c082c0980c00d0002e0540b0f80c00000d800707502482c203180080c0005880412410340441c40c036801490b030f00d80c0140c08500ca59002480c19510900510300c0007004413000c81c045100360344926206 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 717883255 1250 717882005 717882007
    0x7020f0604030e0d0203012a020a02211e0106362d020a030509030f040317122509061d280905060609030a0f080c031606060614 56
    0x207400b1034081c041c0088980005840f50118580c3c9074006070860b14500a42164200103aa00982c40c030400355281d80d00c00c03003030300003401c18105540000b02c0041908804401c020701d4901c1c4400240c905021915800390701100960f2517001e4000d54a010300040e000320400c0243d03001e000c4180b0b061948100721082500801075621b58840354480019004c00c42c00d00e01d40041c070510f0507018224400e8002c0762492028401a1100c94507440102a51000341c003400b100e03482403301e41c0d640403d55046400302c07607120301e5000d0711a030742146c41411402815403070112840001c041000000a07444040148104001280000c510307101050f0307108051401503000054501d8642250030802220003048210010b004298060b41e10040300501201c4403005001d811111008200740a01c0d8041c40390072007000ca407850700b05120754000c40d68400b841403016012809210286044c0710a48049691200461040e60ba840503c0200650540004d140840d9800d00e081d00000b8400d200b5240f0050a443d070900742 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 717884505 1250 717883255 717883261
    0x3070210031a0405101a040335070f0b0403020c09010e0915131b0f0b0909072d0f0e06070b1f05040f051504140c0c01141e07020f06 58
    0x48401414020001c0550700f00d8100040781c1b14044210320400c0e44c1c40d0107140703983d0306e00758904540303c071500000380c0413002981404500c0c03c041801d9840f072a894810803003900d5154a0078007234038103080444080c1030200904140000d2603408508040044030542d044205a40c0e5100480340751601152041c40035000801030050303807900c0c40301c1d00c1d400402d042c0b444a0000020b445014a0b100302d00c407a070141805070b4504000120030413260790010089102d18078100340104010a8010800400890400007100c529040c9458125000104510031601c4101d41d5006044040c004000714548040402c17a1401340b0750355840d04400704c6480c00d40c03224072026151668680d18051641600e481c140c1a4994600030900d925075214040072014007480124041c28541e003d40b0340e424010488500a0342040c1103800344024915010f900865200d155640c2c0d041c420f20300c180148a60812000c1c1d0074048400c2c0810310780e440207109071114189041d85a6034486c002d06a0780c4884030a00a41e40390411800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 717885755 1250 717884505 717884509
    0xa0e10110303070c053c1c05030601031d0105060a170a11060c011a040e0a0f26040906031704030b07050307120c0c140a0201080402040b06091203070210031a 69
    0x21080b903017441202220160060485075902916007421481c03520351038120f201d50401c00c4a840707902c0072000000a000a000c007102d085800304186072101040c06400004140d0300e0744646d0207020803100e025003401d43c442e0025203150107424182ca0443c0300e01c01d4280041190042c903ca40401540b032140180354040c000d907100e2400740c48902620fa4002c00c180114068003074203014421080740c003400c24000c0010741804000454981807c4280e2039030200e05e80c8000500c50803461020f0a402c0181c2a40c458002610901130fa403800c12394944104000c90300152040b12034203c2402d07241701d022103544029500786641e00700e02640c800a015000030501082070a405480250b4010980b03160003560442d04201070407d90b001030300310700001403040b582001840040340c1d44400d90302400780688071120301c030b8000805a82c3d010b440a480341b80d680405c180290743c0c09088a030f4000c40604842040a8203145c179540702e4104034400c1c1c0c007030040b451522005a101c2e1044102c1c0080030070000c402a451002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 717887005 1250 717885755 717885767
    0x3091d0105120a0203060c03071e080f0a1805062415070f0b01241404050108101707060905030105040b010608060d061505120705060304031d060a0e1011030307 70
    0xc045102da000b9010841d000d0303181400078521803050b154240c0d0341c030700340764200030604441061046603050044020008030380d445100d00b500002070011840160f00c4030710b4003000a105082010400740110711240b0200800494086c0c417032800e00c4680560102061040c1040b6150700030019800090990440c00070840309005c0d01400c1d009481c5000980c80d20340c1d40c006224000c1c0c00c512114070000001c42c484008640c115100309034645030040700380e01c00080000c024003ca0142c50705001805001450460102c0e200000919244058880c44404004115112401030241d400001c0060781e000c0ba050405004881c004e0754812106800d6078a0300804580a4a01520301e0364003100140034034010a07104c1c001c600f00054072407001001c843c5000d08012a102d840030425080d604003000c108066034801058035405600740c104100480510000c031219424403485840d40b00b84081000c0441a80c000607400c0901c4007034a00b10100e41082005542810100c045080701e0b5004000041034980f2a00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 717888255 1250 717887005 717887029
    0x1050c0f0a0c15051005030d020d12200f040e01060309020d031b0f06050a1406030601060806220b210703081b01020418050f0709090203190905070303091d0105 70
    0x140c2d008140825501c01350f503c203031a075420800b1112001d0145240600445920b40d043e030009004005c50761101612100c5250080c01d00740b551100342501c3c1501880c000c00c07414a040c84034680d1782004120074540d607005801140010941c2c0c00000c22441c1c002d11072260910340007000510012035540d0216502030086d0440d04d0b010111785043c000290b182c0d4480d588a6100313100104461505180b20001c440c0140d8140c0d0206c20642d06008041c1c4020030544c2c10350b20140b030310f8005a50346074041855450140403041d9000d0710300c0008203106485520800d25071004a80c24042c0000e81038039031000d8064082ca42030160811350782040010745880c024405400200c44400031301080706011f0342260010740c0050124407801d100100c1d041254460507500408945a012082c140034500510205d00750203000031080e40000410000c080305a2117103107804a20109008040e441c1c544541c64540303d01c0114040f03110030b0320109000c1c0781652062400303e480d98000c0020fa19000c100005047c280d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 717889505 1250 717888255 717888263
    0x4170405060a0305010303080a020f04120f08070605041523090f0102070506180d0c0b060f04230c030106050d0906021908041b06050f13050316060201050c0f0a0c 71
    0x420000516888900280201840c0c03510005065072441c10040c0025400038103202c0c0c4107204209241e5052410800d0303a0585042c6910746444100c149000b4828680441020306003400100e039600c20090715411203486207224048251340e45200040c00800c1d0b541d160b0140d00d02c000241a150486500c1c01c40f50f5a0202c0c00c0802c9030340040000ca082d9003240d0245070183c5e03543e0030002c01c005c80704411103146010600c03113400410f0070480e2120014040c10a50500812190025001c1100d0341d8840c280d004003040c004004105112200b60301e0000e240c0d11118104000c2c10b070303400056000d050701091324106d4a540d2101032402145561690080050250481c5c045609106e04550b00c13031031501686501e1036680f16020a41490304090b1280c6270a4520340c100400c5080040c040175038000161202c00b00c0c040002c58903a91409084101c120711600555014801c4990101e4555a42034a020845203d50001c00854032010079684c801d100b11f0341030041d5640c0400c807500d80603115206c0e402c9802c3c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 717890755 1250 717889505 717889507
    0x140703050d090c180f060b09010f0c03180e0403020c0405010303020d05090406180b13090f060b2e0f08040807030c03050c0a03030917070b3d0801230417 67
    0x20ba844c10070007040d0b106000424030341d0700c1d6241800004588a07010140212501c00d40c1071035042d02c0000c00100d0403880340020010800b80060415000f40003a9000f80c180760118429291610f2800120480884082e0014802c01c504450f0909241c49240e05903601607024000311410300c5819102c90344140c0310315070450f0b540d6600107500d18002c00c01400260140701c001c1428040365041101100c04c03428080f070b94524040820001601c1d1203106108a5800040466444a01000208500240000e40003000c002d4000c0803a03c401d924142d0004c2241610760f4030100c40620012643c2d100200c0300104007000c2000700102280c091980103500e1172080c07610310b103403a0744d030701a07a414844855411004251184095002c004041100321000f00c0c207504030605100068481e540921340107070003110340c00308240303e21a8894005000a821074920f40e24110084d022451581404503584031b0004d40c0d5182510002d09000c01c1c0c8050220041c2c80703502600661034980381c00c40d020784080c500c00e0140300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 717892005 1250 717890755 717890759
    0xf030415030f1e0c021608010b12030a0906120603080d090c0902091e1f08011d070503061201110a0c1101030c050304060b3111040605070b15060408030a140703050d090c 74
    0x113000300c1620082c041100001c0b0702745044e07030f05014001c0c118124a030309581007403145160242e032082e81101103868030314241e42d85052094942004100340d410241c0f6148d00001c03040c000d082c40703401400c0054031a01c0d07480040e0f503640b8020001c90148885075980005850035405400c1607611a0410502c0d0080194403000c0403400540410b0340060040300126581000410030b40031050350307061960407412503000461800070802041880020665881102400011007001c1425405218071f1010b8081c001d55510107074170081d00014101108035a01c110007010700045d944280103401c44402c06440d210f05540721591050f01030261120702d01d0308001c0d180506e00086815480e610102c0040d0110072051701d9200f2088019607640d0081c04085800400c070802c40680d100c003c0301c1c0019000403003400b85413940d49440c0b031202808109182e00c07020114000c50145004002010010540d456056160a880305c0c040b405004200c0050b01140c41407109095200c40b0f034000304a141d05c5010305010700e81d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 717893255 1250 717892005 717892033
    0xb0d060e0405070e0703020a210608030d2a020304050915031005041e0302030d020c070e0403020d0908070f05120a2316050904060b030f030415030f1e0c02 68
    0x510860381502d20754442c0c030041100043c480c0b551a0090981d01e019071604100050141441d41d000c01000741104c1d045511008000440d406400502618001e990303407040c02960030b0015002070b04844040700c40001c1d001885004c441d802c400c00104540240d4107291038103041001d600c1d8001c014180f01e0940787c0c4010000e030b4042c45a1a1010303800540003070300742400c1c1400d140d00c60424544081725640110381c00c6c040ba80000c2070320300c1100244409a9075240e409030b1141405100da002c0c031030240300c12061008040d000b04880e442450140d596204407680e07980c000d0742d60105481020035005001100344460305100c00403098420005088510100f541e41d00d29880c580d031227555030b211001d0000c0d080d80381c40060102c082d0740941d190710350b400d16080a002440900010704020541a903c00444640f43c400740b01034403040c1038a0081c0c030b1f150356030b07040c241d240481c4442040001038504202060000264454042910903a000d012200104020002e00622940f03503040d00b54030074070701c10f08412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 717894505 1250 717893255 717893279
    0x1a1824040c0f09200703090e0a060e04050705010f0206010f120609081204020406080309090609130c030c1a03091f0204092a080f070c030504030812150111070b0d06 72
    0x18182d0150011340704084040411481c1807502004c03440160410040021903400010501a071742500604449903e94505640060003a40d04c1071104c400944100000c1c40001300e00c19080368400c1c0c030f40d002034001c9801d00300c1e141e00090280c142044841401404032070800102c12241074818100010307507480300e0b00e82d0710325908100e184c02c251b0b0312540200411030520b4002c04004000d0480114141042600009c1c514200100041c1c024081d40001031002d1350012400da94450b0400c541d80102e03901c07030a00002e0180c0c1405121104004240400010341e40b54084902c10355204003e849400504451b81081d920b04071051111550248000704132007400341f15032000c00344080030b4641029804100061102c4400380090140305588041003540a070b95050194400721500d0502506240c0d0314096840e80a00e4102a25403c1c1c0803802e040b0030551008040e000d00c0c1000740c0e080007003420708011100740500c21842012074000701c001308210100b20001d0660014004404035030303d0f0700e5904103601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 717895755 1250 717894505 717894509
    0xa1d01050d0f05060102010b03060112060e0309120a050f060601050f1810030c08010b070803061005070b0a05010501110a02030d110f012a091409131a1824040c0f 71
    0x182c180c1c2c40e02841055a024032402841c00001d8010381242e40c034003071502000c002014000390925889101c080d035003039010300440300958401803481e0b40240c400705401c0c1c5c1d41c104041c0c040310184038880305007046020004c3c0191248205035102e51030001510304400241d000b2843e68681b180d80f902c03000206554040c0280c40e03035140e5036400144540411070040000740e0680c424800034000308503c3c0046107030700046960000f400d59034039288205080c012502803068003400342141c44058103108840110b07401c1941218001d82c0c0b00d090958848081c16180c6544100096256101043e040720607801181500d515840100665103184010303040070707094402080d07840851603000d007034020300c04c240b10702c1072902d01024ac41e2030444542400d41002d02121642c02a500c5a26410001140b42405142001280703521070f400c2ca01e030b2003d8800d15400e80d2415611a2000801d00898a902c100000751140707010400c40841c42805440d28210701c1c070030001600c1504c04440c59600404c29480082c071b2240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 717897005 1250 717895755 717895781
    0x3080406200f0c040f0209030318011713060c0203031303120605030a0b011d1b1606090c05040c050c0712021f05361018080709050c0a1d01050d 63
    0x1c8880d1070340c0d040000f103801404d103c4e40e200d84140000e08041d10004168ac0e58446041d51280118000c003005844600000c44012802400d4104104280320070601031410b06110320310520450a2850041ea2240030441d50564040d06c0001c04201180c410b25840c20490b9684070700103525030f1a4008a800c0c0304620500b924a0f80c1e082c0010040945142c60400c4c01030420703050049103082c113810496008224642c885c17489603000c01e6011140043c80f03d40308004e94004c0c0308210392440c82c03400f2502010079108091003186008858070080317004030202d41d840018507009d4446e06081c10040c916943e05248242e0b04944005e24640440030302d0141400c0651898484580300d030b602c4500c581c0103030342168110070700517240c40d006a1b0b0550341648040000e00c04840d0700d2400c0b00740c4902140e040c000b600b0007100c1250b440070300040c03010340416690282d41d04c5034818002c82e40d4070085400188201e0241100044500c500b401e444c200000246e0003404c0305140c1170b8a4040040d000300240c071040e250541c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 717898255 1250 717897005 717897013
    0x1403060d0206040f1d130201020d1101150311090601050a0c150917071b0e07030c0c060c0504050103050609090307020105030a0b06030a060e060102010e07050d0606030c0e041b03080406200f 83
    0xd42c245d0150918541c42440f81345000d260458990000b5103c000c8943c02e00140180c1900350b601c42d4500703410820803124203e9144200c3d50b07590800341803c031080d1802d940903c0e10380000c0360007540b00e0801c8909000710b9841d0030022090a42d240205084032640705000705a50b042078100055241e02e1101c40300501c4400151035900b58100348892414940c580d2801010141d002c00521004240d81d0354040410300340058180d00064050b40d582c00f0f011001007a0520700603110349a41e40101c00b401c1910001e0340d003003020b95a00720920540369000c3d1004d0300940e00a004550042d8454001582c2c00800281e001c1401c400341d1004c940c8680080d2030012490307484090901c0603842da90301e4541d21800910080c040300080700034a41d113aa44600501e4090b500d50308180092203034582003d8011a80b100303844000540d1110a80c500750400d50b0125060542d201c146484e00c4400b500890940360040d90443c034251400784144c078406240c880a012046c038032000d0240c031040c02c0c8446119000901c0c090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 717899505 1250 717898255 717898289
    0x804050709050610030903020f0715020c01140412030c0b01080a0b0a02031608131703070207050a241106070206071b0b15040603050304090603050705011403060d0206040f 75
    0x9410100d4980001e803010703282804100060380c0b00c856024030180a03003000160310640307080490401e5940c11500d10213100e500d0000841000444d00442091125401d0340d040da106d0b41c2c011a8000b02107042c0c102c07051014441400464522590711300490710a04000141071176981d41c101808000740e2154035a504600700071000d104854100903803000301c52500318075515180c107550b0380c81d0a0400c599010401c1170400580110f4130640003070715054200070844d2039000e41c0c0e10180003540c012a1b2840046c0951900000c4904003060100c05889240740c00c8042240b101d03002003d4100c040b040e4174204066400e1181c1c240000b400124007800d4070758094003580c40d00c0c0002900b030703800003081000740c0000c2c41c1c0c490020480b080c0350180c1000c002c5423884000140c16000402501c0981c2010382103000001d00010407411030782c85901164400c2050f40d01017036840e001528424008040b40308901d0080000030820710b400743c600c04031613200030042da0a260301c40c13800459043d03003a004503540d11203d41103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 717900755 1250 717899505 717899513
    0x1b041a21071505180f09040b0a02090d050c03010c0e0a06051c0e010c18150e0d140601030b07080408180d0c0b1e1e03070e1504031a09071202120106060804 68
    0x74071456441300703403030b60041d026400f0080341c100c08000300080c2600c600381002c1703000e0400c03640443c0d2001400a040e00216245400c3c429180c0034035100013407196290542c40400d4900489000003403020017800300c2113051804009495661045844a02c1c41e405644442b080c9090b0348104d1402d20480000010082c507190030240111100458400c0740310004c0904104030011580b428202c0603440c0b03130294108d80060003098011400850060842d080b1028000c030000000031514100c90055984084c1d0340c607030300010fa8482d00190340240501c1010400d44190032080240400c1446000c5d00031802400e460312000d0040ca0260415100c4910004800076411220354004d803144200300085880d003000e210500d00782d85a1458042803880002c00080d2100340518030b11000010054200491880c02d0b0000e05c1e90380e40540030460702c4100f04034000c07001c4d10016410038866905000182030700703403c00c50803049060f0f07003c40480e031058184a00700c00510b0b081c0980c100520894450019178145450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 717902005 1250 717900755 717900787
    0xf060c08010311060d15080610091515020a0b0108060a0e1504061119020a0201140a091e080102040b032502030a0516051b041a21071505 60
    0x4100420428040c0062000c00c1c1000c45002403035904560b0141d4421000c00108003404168443c104421042680020820004154684030340a4011070708070640d207409150b811592600c80010507501c900d40144812000d2103d414014400350040321008403c50b514400c0041098103c080da5800c1317a41840885003150040c44030b805200300143c840c02080b12070190050302c0041000c0e0405807a41e240140e03003806401103450048440c40020140ca4480c60080c1d42ca00252100300e00003003081074890b019109000c103840301d2070200e66604040a2501010340054100c40c01030440003c5c415000045842c4244020001401a412050b03140c2c078007a030a085004c407022942940c3c0500c0a8460b1140545c080100c0b81c20207154100b19480f8484150521442404c02100070554414401151040800402e1410303190500320380a205080011402d001048800609603400203c681d000030035200c4913041c3c500e5020f00000440d01c0c966956020180058042180c00d000700f00c00003a868803d8607041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 717903255 1250 717902005 717902021
    0x60305070b1219021c060501092106090524040b0901060e0726010810050622050924010e07030b06040506160b150f040501060206040210020a0f0f06 65
    0x24201e03802d2100016003140d80d0a0010003c0d492100b902d005596554000d6064600b45900400755011125040040100034001400340f00d0120b0545400020031081485654410480f084005c0c10804020741d150300c0580408403048a06008910109214000401c1609102c020200600d0201c0c1480d041c12048090050140483c0381d04002040c05103429040ca829080700b024544a590714600e000600341011600c3d240d01d1001009000000d01504000b500a9010140c100c081015031600b1080009109003403c0c0502c10079884bc140381090382d86a400603601102030402c0c0d9a0000707901110b00850703401c030805c40c0e41a100000c018080240f070048100d600c802c0e070341801c0100c1c80f5802e0018446006910801748900c070006103000302001d0b69440c0403e140c0d0b1144c80c0b01c0141c01c100420783c007103070720743c000c501e010391901d00350a180c45c68503004060407240b2580182c1101c5e1619020301c8061552441c41a05502c1210074003030005444011150801e4020702d00c2e640c403285549844016602d0035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 717904505 1250 717903255 717903269
    0xc0a11030d0503061c02060d050f1510121119080a0902030c09280b040e0613061805060103030f081303080c0a0909020313050106120f020f0411030a06030507 69
    0x40a19041c1942c100d800c81e40c001c00215070101401a05103041e01c0d0400401e88006d401503404103c02501941c0f80d04010b000700380d0b4031550241e564641140c168101c1d12400038980c007280e414a00c0c0a5507019031044a5071881c1e910010810500200100c1e80903400f90074440104241c460107010099401440540c029850402c00d00814499070002940c858951890600c201e06000124020a40c1c4205448070056210b2480342c1c00c45803180000d00038160605030074059820300c071020b1003040700401e406200e400c0564410310609041d45490005120b0351020a4070202c4003480383e40810020084140207503c04e594080c440c00d4503c030b005212420182141851110796156400029049a40c455109107401b03801da444400e1054115940512540032007580e41c400000d20602002c0300c030400540c140550028001b041c0e8808207183c81c1081d0345005400c0000c502142001860011382003884004020070100744025903480c10680d0354001d4802e131030043d503a408108204101801960000c1a034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 717905755 1250 717904505 717904513
    0x9051b0a1706010605090d050609012a080c0703141305210d0806131107060c02070b18010c0b0a09060b01230705150702060411030705060d0f110c0a1103 67
    0x207455a00c03581d41c0418014201030100100d0303100065185c60b104c186804d03400c0001c5520381e05040d41028000c0500c2906030b100420104008510240e283c40300c1e51f0b4145080d580c4010a641d100d400703010941010740200e04000c1001400c00e208139058026080c0700c0000304a11030024540741c20001e1803c1100c100c09102c0c0c481a220b03001c42140481c2922840b2040d08122070141c0d01c00c0c00069000c40081054004107241c11b039100103603071018014042e200d1080c403003000600d1800740243d95401c3c2d280314030424038078104080c01012200c1a81e901c601c038018113102c1c8048480c1d42d1000000c0400b201c5500314180c0c1c42c0e007150306010f014001c5100c0441c080c2402d035110340440c0c0c05012031100d8034040d0001c481c0001212010040b00b00443d0f160700c0500e6030390804500300341400a440700000d0f60292400c0c800c130074482240380b402088000458500402c840e00d400c2c0021070359400341802d0220030003081c0d0b0b0317443c40c0720b030580b10440107150b1401ca038000b80c071884150b0301c0c10901003a003c0c0700d0280aa84 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 717907005 1250 717905755 717905789
    0x6070e0d02040f060b031006110f2d19060b0a050a050607140304030f03080906010b090d1a04030e040f06050a140607060c02030915090a1809051b0a 65
    0x119500341800e2241c06840215841d090810840051329881e4003000b6449030000c00c200888600611410940d0610380d604824035030680304031942d640c0c589101550a400090440542825603580000c0744000c445040050480c405101400e02c03104082040304203d544c10b00b4000c0058a220f1460747e120100d60796031000e821b01001c00d090001601485025460005404041c450340b920000c40100408045958031b40d00ca01d0246410f1100c40011030105000b03001103105c0410201d40c50f03041e200100030003410300a80b5810085015507800c0c0903214a540309841c540981c80350740701039120307030301076241c114480744070303500340b108884600308540c84a503c0c2c0803061100c2d5441000030700484400742803071540d8084500020f0010310418074018045031030080d007011050f4011010b42507040701207622041c1c51441d0b10101e4464410a4111075000009290034007080a003030b251412200c0e9890320004950540744e442600d1b00340049c440c46582040c031808008140703050f1508001034a440210188410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 717908255 1250 717907005 717907009
    0x3120305041713090608072612161208180304212109050a060c02060a0f11120d05090f0d05070501020f0d050405120a0221040305060c0301060206070e 66
    0x40c0380396082e50900310005061405070034800140c405891200d0302006450398030015075580724410312039880c2c0418490725034400600c1c40515001c001007400d01400807401060b50b03c112551003140403c1c8403a03820724107030001c41c82d00c030503a01102c1c46580305d1580030300300119400196052254050901d07807041000b4014180c001131008007601d12814184041041d500d04403408014003100d8a00b000500418102019070041260088030819030709214425103440c01250521510349020b50800c50420900400a2041107805c4c196801860069180d10030060180e040000d08828241281c1c0d01003a0b103004c00721584a80e030b0f00900c140004158545e6042c241c207845904986400d024014041000e0050003400c0d01142c0104100000707690707403442408e900034028030096a066600d0b11480324001c14689a050844074602d00c1c5800402d50400304403170000c032010814005a005080030b102c0007000441c1044224064080c801781141c5960411030000c2c640b40f001000d07501003080c0c001c644030043d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 717909505 1250 717908255 717908273
    0x2120a0c0e011202040e070507140a0308010e040f051e060f0709150e042c0105071d040b030d05070317130618020a06050a02010f0608070506030417070b010312030504 73
    0x14003e0a01a40015501400c50004d00507a07011501d0680764a0810405652101c02092801e100b8445ca1415616100440e6034038404160020042800700006200341e0441680c0c0325031080c03040700c40c4006a04240c0d04c182c10007407031541d600303146000800188004141481116071144070799041c1039061800000081c003d0695103e01040f0340c0414899020382e61152544d0f0f02814009081802240b866404d0a014410070b072510034107400c031501d0300168a46040c09498050003150351403280060211624143e49801d00c0c00c038a9000d80c1d11040070b990354805102060ba4003019407551350700d8080d18200036282c100601c00c8410b4044916040040c4890b000c0712104031070350400c0000403541079a5102c0f0300381c8a0302110207984061200000240c46522000034004400680c0c020305c0300847c00350400c0c040e50b84030f010b9000e40350082901400b05041c0714005c0c4d40d000c0d000742d88000c0406600c0c10040402e80c4901c10580f0f0007031540c4014000d01c2210720303010704e4807580b6203401c00103031400361190024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 717910755 1250 717909505 717909527
    0x140d05031b07080105160801090507090501030f020d05010b03090f07150c060b030a1b0b0f0403020906010216030503090a0506070503030403180519050907020c06030c070c031502120a0c 81
    0x408801c0040303030701240e03104112460280095600810141c10f0508158240904c406100c6002403010780000c40c5003129030241c103010300b0568851000040c140740054000d04180c00b0058102c0d40c2c02d00512520764194010f1500a03c450840b05680e41000c809881c18102d0001c060340c07141d0b00801d010031030301c0580c00035801030002c5071500241080080c604ae40190020124459051040380c0000c1d060240b40841c644c0031a042104d01c0185664804070752000e8000e00c41da803030508600b0300c4208094101283c83d43d5200005105030380b901100c0d03111522170702c0300701e4006440c20350011814050505240c401c80000d00000c0300c18904192041d516665a888018001410000f282501d03014080100c4040c0c4054400103204080c0b40c1d004071120110180a441014415100c20700031500715400464600c3d10b0305005802e00340303035a640101c01400e650020b0811601881c4004000005c0f44240702421001400340d000941d403103150380010f200b40c880c0a04035483c0a171070404503001160704100740313040d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 717912005 1250 717910755 717910777
    0x20604090905191b14010f0309060b0405040f1208010e04060c020a02030d0c03173304090b1e06030606131d010603030f03020408120903010b1207140d0503 68
    0x21403040600e80759040c03c0c030031220000700d04000072000080000030400a0a141214243c0581069540200c58110416403650311b0108010400000c02c20380329400c4440b840b40201c002190445080c00032a044900c01c0364142d5038030400700c00d0031007009101d405a01c4031000301d1501110075410301049407480c203400740006007110741d640090f4415900901040c00f0043d0010165002c005480d0f03406040c0c4071031070030200e00156020f1105107502a10540ba81e010340554441e20070f410800240348140e0f203100c0d0030130f41401ca199045019003540c880c000c21450503c41c4120040500b0b11982c464000e002d905800203150312039100f04541605c00158080c0d10a4084801d040a2004210490b00420030800c10b4512a43c04042c42c21121105411034021680b203542e40541ea490200411800c90007180034811a903041880c0302144071046002401070454001c000084403041c0303400069040c50001c01d01708590304090010015014034001c4036004a8040c2c642c0d000c0c0345038640e145501c920031010464 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 717913255 1250 717912005 717912011
    0xe01062c010507051c090f0803160b0603150106090617090a022b080301140d050304030303051b0a03150807060203190e0306070c020f0a08062811030a0f0902060409 72
    0x2071000400080c0d401140f00e0300801090f842d0017000034084600d1303004000345049a200000343d44800002100d01603003c03580042582810340d603414426880c007030b00c4150305101d065540b001a5140d0240c9a00920143e00c440c1407851810b00d000e80074600078a9081050790100b001c1060b160f41c08100380400e2a41107600010302074480d29207002203052008420110350030b41c102c80003005240d40003103040c1d541c11094402010003903410000c0020303404d81c0080068005200800000340280c1046411003020001d000381c5120000c44402150405045000065207450301503901044000040b0050101d420140c0f4000b400c11030065540d1181d40c0b0a41c805d90529204001e02034400e10500d211042e00400303951180c107000c00c004107818010402a40304020f0f03104402d1980c609054403100300d9810074040c190542d04c000e00116490320051003034811903081804191081414464032200b140b0212030140c0f241095180801100d04c2c000c4000042e91801001e6005039803004181d40880b100c0d04c0c008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 717914505 1250 717913255 717913267
    0x50d060e0721050c030309060d0f0204030f111f05070b420a0e040305030406110307090e0109060f17030c01061203110109031e0c0b010e01062c0105 65
    0x1545045000d50200201e4945811407002c1ca08450051050041c00341044034032244c0c002e41015202d201d40d00200e07600420030032802c1c1c80f1041d40d1300958080c4c1820180141401e80d030381c03508507140c464401e0481d00c8402c10b103000e101d2468040641800210a00d403001e0307400d40014406040c520070b1807409001422984001600038580d41d00740f11010004810301c241200c05d200840304c0d414044600c0c90403001000d115240d03141450300844040300c9040001031165100ca0700c2c280c4282e4400340040d240e080c2c840400615180d0030380c0095006040303d51b00c0f00070140c40c00074502c6814a041e0040c10703000d81018410012042607a007000155048a501c030442c0404485000d0b00c1e41c454000ca0885c103500301b0200040902006a0490119009807a0382000280c1d4205160803158052070050100c2e4480b4090808040c50f1075541a0049a501706034412b444140c8861603c1e6409078000000d00e692100140192503000d00c242d040c2d43e403112080f80241e150080c01880748011400094100400801c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 717915755 1250 717914505 717914531
    0x414010509150a0308070308010305120f1905070605090c030c0409020640061e02071e090f0504060c0203160f03030603080d090c1d01120236010609050d06 68
    0x520f0001d5901030041c40c2d4442103403a015040b90401d1005403000e0158842400c05c00031014102e512140b0501121454031140b14010b200c3c0f1b41125841070104030f800d11000f400102188140c60003400740e034004262806203602014a0f00c11903003589030265092031b000000588440069450540703000803040c108120650499210a424909281800405a1055040c407215803291400c0e41c2c12a030b6501e4031003007083e0701d1501e0490403444940050303204840802103c80020020b102201c01c4218205110f65241b0240c003d40d1038210069500d81d94650620040052622542d816101e05001542c24183e04030108902c07910b80e0b1201900703800d8042100b00801d84a0fa000c240030b190300840c4d050320380c909280800001c001849040f03c500485c2c420100d50320400218801d52006c2c00c07c00003c081c0e082c841560f0400042103001c03a0800c1c40346d21a4990341404003030220742c0309200481e0b603d1002d4114001c0c2c42c480303030681c0a00244000107000f489180c9900d20101b0046800000210f606104815 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 717917005 1250 717915755 717915769
    0x203060105210403020610180509030d0c08090c0a030807030509150301090c110105010b0f07060b0603040302100f0209010c0803040311250f05010e0d030908030d0b041401050915 78
    0x50a81c0d482c00000c0709285450610390701e0007180264203d5010741c2d0745080004820311940038480d440c40c0d03060141d00c580ba28682220b0750052585042c9e0f403c0907001d525041c01d8400c000617010200700c0290401c141e00310300300f080d483d01e507604499500e0701300d00d95214540070b4854618050108000003643e00f015844006a0074401c10700c0d070140320348e6580d55220440051008000702c80000381440d0042d031894a05018050581c0d0742e041495141000740c000c80b00c038551011504851054442030302d01e1155440c42c000d188a14000e40113000c10800e040309a1044883d00050451031502c10b005148032039a1020b6011100c1d940040300c3d40e900d4545e400d054400400000d0003411341d20490001c84075080c51064203114011060321110203058488200d13860010207802601d000801f8011900740c1da02e400030984030f102e8001d0070b098400c15101c2d0b50880c00c6d41c0c0107000c0074505c95220040d1400b40c0c00c152040b114403070041e004160305541080005000c071440504003c441442800e41c001856036420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 717918255 1250 717917005 717917017
    0x702060d020a02010b04050c1b0a0506010602010c080912030c0a030b03060a0c1202210c0f04080303071d130e0c180f0609070f12020d0903020708010b04060b0d0203060105 75
    0x10202a00c80c0410440400a580001c001100650030f003485d070040b45c205400b540b8059003200c055982132001002c0e040255000c0001d98249038070a00e082440814024003240303010f441d10f0b60011400c500004400303010482c000c2e00c84241507004010360848101c10350140c940082100240070f68500401404034042e044811401d0b606001c3c4105010041b1607650203010101056103900c05000d0700a01031100b2030142c501c87c2c0100d092100c5d8451120510383d00300a1740300d0241882c950520f01d0f00c27660300700180c200350008901c5610010a0006030b5800104e000c1c0b050103102e44207030055200d10003103031142401c0d480030080c107529200d020f18070a41c148a2104080700c090305100c1022000d864078070740d84406468600c00001000046001801c001d21124425502d1b1303111a031494405035000c60740e11a41c0200254516400c0c01014507200e011701488a40c180203600034840c4074140f401071400c4411b101c40d464810b82ca800410880601c07214152940c0500c107a40044c2c5aa03101001a501c0748030301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 717919505 1250 717918255 717918259
    0xc1306081503100c030b0a0308032e031202071719081605061e0112030c02040b12030a110309130e030403020301050c0c0d1d0d0c030b0907030b060f0a0b0c030702 71
    0xb2180c00060343e0300c5074050740880c03103650b40c107000c207542e0a000c2c00f5911206000152220404000040c52446101034610b1101d0240c0000d080203071151038401c100c0c00a0307400031200c41300c420b4032003429540e040040c600640b588110b2031402d0f50003607410f1a41c41040c05601200c02098004d614123201c8000190782044e9081c80c4000e446080e503250072a1203d00445100c4034062050748203009000c20280400d05807a640c03a034561544400d40c82c00e54244102d0f20303040741c1c0151a04032041180c2c803080b00031100c0c0e80c0240000d41c1c4980205001a2101001200490403036000348030f5451903075960005480306a60045000030070b000700d00d1103941140b01e150800303905503003443c0c10320080400e000001c001180c940e0094860004050804071804d60b401c0c0101d40b8045117a99401032a460302e0040b1452442c030a84071103580035543d60b60b48070301d0385c8111000015508540d00400500c0581c8421590048080340e03a040b00d0b04100b00042c048080d40e00551405000c042009524404204121680d02e600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 717920755 1250 717919505 717919513
    0x140709020a050406030612120c082101061d010912051c021609020702012003130305061503070f35010b0a140906040b0604090f02030a050c1306081503 66
    0x40200182c01c2c0d900910504001926003080000c4101c200d00c50005400c0c0d000045184000803003104a440503007461003591100010071054100c2440f40b010509190849180c0f4581503141100c0608041030207040c4486102c00140036000b03980c2d0200740c03003003690003a084200c940ba140d070800c10b2038140b0b410714400d80030303613103501c00100d064002a45040303080b1215400480c1079220325412050b4014100300a0104501c40840108000b5440f9a00840076410040302c3c1030000c080c10409900420ba80140e44d03c2c0c1104040c4071009451000d006c1c8850419801460102c0c030300202c06812144ea44600101003000c6100030f10b0030b203e8440c1030a04140300090004041c81c00300d800c60700a0280d42411880303076010b0751002034811104240e0b002074050082c2800807903910140ad010180180784070046d40000c04010102d18021284503071071f84030842c0c004c0141c80345442c00725030048400c00351a4980c0c19600380070410104a401c60b6460985140c1d2400c0c1140e51201e040c00d0f08011821420300c0c1d4580a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 717922005 1250 717920755 717920767
    0xc060e01050f060102210a1e0c0b090102040e010e0916080c01091d061e10030209040501080102041a0705070f0303030509150105030a020103020f090604180b041814070902 75
    0x40542203240108900340c2c0140030398541000582e41d461b480c40070308071041c00c1501c1800c40d00030240040c18034a0954144921041c2480d508034081d0142d441c194800f207094420340100f409541e680e503a5101d040400218a442e00b400700c551401d100511a602003030000340c0000300403503401c1c000a514282072203001c54209480c0d8082c242c070b41c5000388000d0b00142e403800000031402800703d240499180e24003020452601e0300d00c180181d480d01c440480d0190580c0707860980140e03c500c1c14507104504541d80050f280c00242040100360b5406078409822603005106c20b000040381e00c106c2350841c034203940041d5074030807840c03402d141006401e51000c40c1c06001c160001041c150142c020501c10000d200503910462501c00c0c81c5a003071102030003295010307840f4104220040d4002c5d4020007104807084145401e0403180c00c000780096005070092600c21107990300c000d03882c9026018030880040c00312403e01c00710300d0006504440c0c41c04002e002c4c1c1000c4600d203010b0401141030043d8005481c2100303003036503116 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 717923255 1250 717922005 717922031
    0xe07140622081b010c020d03140d021e0a090e04060b03010216210906050f121509010906030b040b06061e1b07050a060e120f0a060b01080f04120c06 65
    0x41c003280700da0380d080e009032805030028181580d0003600c03103032058560448151494080c44600700e1807100417800d1103075000369201e80c0707031100e0082d118645582d4009640c800f1442240f0202400412171403e925205101c211304146d0842d0440e415105207060200480c3d54506204000d086401c83e0141c16520001d0507090000150306030480c1c0e02d0141030000d041000c18200704144140000d50000040e0664400303005161043d00100b800d800014411418810684c1b2401c0320068191240340704140885100ea0382401c3c01c43c0e13014014040c1000421400385075803105410003000400042100c5d64020000704560b0360081a6081350700e0103c0c80400344015100144556481480d20b001c007040c1248210030021760018103c410360340043c0504220b1441c2030f10036100d0345480c4c024680d0158140344002c0f961a020401490802c4040000b4583c0d01060306101c4219050460490b0400c0785590070003204460044090390420703400b01c0c5500e25100b40920464002d0081c010081c0752a0420510744540c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 717924505 1250 717923255 717923317
    0x9050a080d0b040b06120703021305040e0303040614190b060d15030212010c0e19150807030c030e0a11060d23060409020108150a05040906021c0e071406 67
    0x15000580d4204807a00c0b4000c2080080d0080c5a40400d03038200d1040042d00c00740c449e070050080c060310364200e240c0050300c80380010191540e12a052141d5807022040000b4802c09010f95591800c0c04040300070b15040a800302c3d01000361101c48142d00f2516558035103141c0c0c6410044400300603a228081004002048035801110843c1c0310503482104020500d0b09508018464103544242c02e840720a80c0200250500c0464003e1017100405107281031000910307042d802652240542460340c4400315498203250150440710b210000d8010140740981289208600041c5440c580340c200120603540c2420100080c0300b4070481800403201c034106254010340350307c00da01002d01e11080075040b01d2a6600c02050004441d52400040d001400388008600c05596100004190001c00362010612903211000b0400361484914121040d0780d00180c0c1e22281c008920340e4240010380403205004281d0100d0b120fa9460006000b150380194407001c044e1300070380d505411101c0381410b20b07101240d5480c180103003086d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 717925755 1250 717924505 717924521
    0x1060912241a0f0d060b030102040b0a0f021902060d0519020a1706060a050708031b070f050c03121b0f010f05041506030f030807120516020c0306091009050a080d 71
    0x2c4550822111400b80f074580c0b4110f420510103004181c60303540540301e1030007038405240c105130595800c000c04541d01d001c0000a0100c4040e43e11915070051240740005e250801001c80c10448214108011006985101c00c07144c405008810114007a00c0b280040d0905183e62403603168840c1c0300085680400d40c0100a2021140d070240e000c1086503918420b1000511685072141c00007581000078500248280300030355007001410000401c6210818240d100552001c01c017034503050401d0340c0710010840c0805c404180c218064020703020751b0411030740f0103041d8015440082d11400d1b000b162090198001c00c24100c0b2000f80500a1204a586210b404010300040c2c5003644e540103203500300311044076507009400803243c1c05141844034606ca44c0b000c68207501d0140540701003000c00c8021030101407550040c0c81c000c800080784009804014103010b80303081021000c00d40640c200908000007401d000c180392028140401c0003240504862030624201842c080c00180040d1300400c1011200b069035101c440703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 717927005 1250 717925755 717925781
    0x90f140f09070905010e180f10060905090d0206060f0d020d150606090b07110607080309060105011e09121e200a030f240f20030106091224 61
    0x401e8940c038000f020ba50b02401100100750002c004280c254440b840d4000c40d0010b000103840300190b00c10f142d18200b008909810029517120402440708011500c00d00f5007000c1c0b15001000954107c0300085c7d2500b1005011030f10a0710001e20304149a143d0301c0a01c4100e60340202010b0004072141b4190b200d04010040030044203241180214159000300c080714240c1c0c600c11031403804c04600340c0d50720f4507540d19a01640c4e017010003031050700002707045240590b0040c00d000e0064050356041400062107040e1900b4140c40f01c0100704035090343c0c0758001c4600c10039142011241c02c044800e07818000540c884601070014a54940f5080600b0704ca03080785040741108400082111882c0b084003000551882c0e40406407103190342010801c00110951601c09200500004c099001c941100d00d403c112034844403801c402544818035400602c1d0078040105003205500481810f55041420050801d4001d0140146c148030241d06541030011324518035080c3ca540080c0220040b109000e0b074009850700c408011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 717928255 1250 717927005 717927013
    0x190305030907060906120f110304030e0111071406070f020607150c09030c0b03060307050a060903021503010803040608090a020d03090503060603010606051812060405010209091f090f140f09 83
    0x424014400c451080407102c05941c2d9046c080d116030180c500078449480080401d0b542c91001c019140800405584110f0007034032000c0c2103089502c0003624480d1540300341c61207a008040c09004550403451035807481401611074944580b00c0740351802d4040c0f0351240c0030354405008129502040200a410140700c80101000d00c003803043c0002c1600c005510380001002c0310750000003403085200c810301555007d117005084803085541d4030080b42c0c1e000c4841d081000007607843c50040c07041d410b0610700d501400302203901e01840c40d85489803050b00e07030045010f62000c0000c00e20101c0c00c400c0c0c0c00c01003e05c486030018200c03299030046140c0a042c0700e1aa1013002e00034010b10380040c0842c50188506e40440d1901d440305450108602078003808100321a4040e41c0c840707800c00f10342212010821049115600c180001a0340b00c43d040c0c2085000c040041404054403041c2c800c140000003c8604003044414646000c078410311a001c0160141100c0200170304070104000c10040d05d003403101600c074012500c6506807 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 717929505 1250 717928255 717928259
    0x5180115020703050c131b02031815091021050a050705160204110f041d10061706060427050c090d1211060c0901020d0806030d080405190305030907 65
    0x6a0b102c600900c8040d2240e000f00d62404100d046c0441e090001c0440c40c2000154079010000c40000c0200c00104040103030b2010525814031101107402038045c2404841c40c041e480355600740d1005920480e4003007401201443c0108880380d014464a0404006400c82e4042001d0184020340040c03500700c8441001d2420b01d0040b840450203542161000d900303011254010383c45580920015250720070307180769100403c0000c01e40022041c1c0161026280c0140e920310303459481400c803a00100c0151808941d0414082c00b00101c540140c00301d101441c1150220003580e0381c80000901a0049a0068511044030780000c0460010400484030742140d03c841000f058441507080145801503001098018020312030a40c0800e50b00d0000c1c594241c010320707080e070740421035200040c2081015104c01002d0840414208910368041c4400708010640d407802c004540b800f20002560740311211407020510004001003401c8c03040500c0040c107000700414086030b042c101864028051307402124100018000c000740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 717930755 1250 717929505 717929507
    0x23040503091f1211091206150609090a0f0f06091b1e1b050124050108280f020a0504090f0603050624090c03090d03050f19020405180115 60
    0xc140e4103460303140d4400c9003d2030320802c0a001889a09041600b0b4201406404203a5507170714015000710000201902103418001c06920044410074800f40c40340f6428019614035458444e406940f204594601003600310b01e05070180c2c024081d05040c0449141401c0c0045030014254103d04c00d440300043e00b005032075442c030318102c07a4111343d0b41039043c3c001030404942e031b111481410311040e0f1130788402c0c030342d03086901030b076140c2d030031603140510300d0030500c1050f1002503418180035175401c000d000c2030810183e5403804c5080c080f41c070444080008181e0b8050002014080d030184e0001042c007018074011951000c0c108006400e6403ca8440d88001a0070b0501500d00c0c5150383c0a10b101b141d900100401d0f89032950fa0565403c1d8040e2448a03984880c44040d08cc0b0503994a85854000d001d610103155803030401c40003980c1030442030780c2400145404c080500204a11150030284e00c03031141d01030200c055000c28881c802910595209591000c4404008030706e100042072031034126525070411007040b01500e60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 717932005 1250 717930755 717930799
    0x7030806010918020705031b0115060c151a10081b1c0209010507080a08060f030f07031209091a03010c110a0b04020a030605040311010f1a042304050309 67
    0x40d03d02e140003505510603400f00c0e82d40180442521400a1f24140308540b0540a80780580c104061031680d102c080301c05c0c0c100300310b45c5001c0c054041c61621a1154a090302c8a80072215200103041e00b80390703241c04a038100340b0999100f090300d450080c90010b0618a80500400c0d021056a02c540c605000ba4141211421484100c6007146022134150b0403078080226100000d41250354124148803080090303500080b229030007002001401d445800b1907040200a009030246010b079014003130b5001c080040385001000402e8400c8a42c071511140002c129810b08840304d014030b501030449581490f0079410f0104c44658180032803c41a0020080440b098400700c880d030700c0c05c0140c10090f420000300080407907105240c5951040c000f418040701c10342c0d01ea48410464108603025400034048401c09021060280280400e0140209050241c0503a41180c1c071004800482d0007842a5a100003e480a01c520b440c20ba10307a0100e501c84001500c2c082c18840d40300e038070981440d4440d4140d1600d002000803408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 717933255 1250 717932005 717932009
    0x1406250f0506181b040b0d0b0a0b1c1103010f0c08221e02040b10180e0907060507020a0e07090312083c0a0906050c0c1207060e030f070308060109 64
    0x700041020280c15a0081c10300e501814113582c015448540002181c1c44849482c5405403046440c070b5240d1510080340000c840c4522103c07031051158041c480045140c142c18140c0b0075402400315840310700f0901c0000e0041c2240307a0a0360300d150408824602c05d9400c02580c9201e81c101405000e0a03218146541c440d04009000040c0090520b20040801d04031a1511071190380c80a40000ec1402403000080c2141c00380d03240300c0000038201c8031207900090103545004028000a20039800074200b4011aa0b25250076000c2c001c20000049104400d56840110302d000405041d100c502c22030903e108014811030031400284ca00303006a80343e07050521300ca005500d11a18400087e605071b0b10740e0391405208a807040ca603030b038000390700102c00500024000002900840000c4000122034419241c0102900e400420000c90b0b040c09008074103a40e0030118440f445d0000b010551551061a80341140007000000b0384014684000325400c040c0710b00010080c05168025200d07060b60f5503c000045413860024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 717934505 1250 717933255 717933301
    0xb18010914130c15111006140102070b03010902130504020a0c0b0f06010207031122051b030103230703080a1205060405042117100617011406250f0506 66
    0x40b42c002c01c8441c643c0880800508590718203c0c03c5007505d4a0003610381040c030b21120550303d548820800c10842c1180c00312248030302c02e001402140307103040e500083c2d50205215103102650001000c44104c100c0803400070282c40001c008540f512980100180744000a03541120440024004a480d4141c0e0380d42e494443c9905a0003010b119040d551041c403020744c1d03145140d4100083d0700000d189448800b42000040071003a60009892818800d00b8034031b000000d03580020031808000520125521103c10783e040d094400141c2d03135261414102074a8600c196001034200c140119192076aa98080301740d101102c8620428052038468104000440e00c0558004050a040062044650009a421a80300c40d182c0c2040782000c080c10415642100d0121020050075000140c24000c0b03030740001d500400c821000800d941c8560504600c54018013155003032501c25000403c1c1c214190b003d1f084104a00c48400320001c42440300c51507e681c45410025088890b401101c00040e0f07004408012641c6070040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 717935755 1250 717934505 717934523
    0x105060603090d0e0d02130c0207060306061e110a0305040e0c0a080402010c110a060503010306061a0a030f090c0b072f0d020f03060c070b1006120b1801091413 70
    0x1a0010076680441d09050960300405d44d02142809a52175082d0044d0441c000075001c101344001c0e0000900f00f0070039420a13410b02d0729040c000c6c0403107a84041c4004440c289800002c4503812111030a85100c0983e0759000300b9842594041c00415901401900c21200505401034080c1c60b441452642802250b081000046400c000500990f201e544030564444c0100300d0f100c25002d020b800b244801807250021004618000010020095180b181200a00d0004a403005c01702a2000c1d4130b46a2244042e11405c060301d071000c0540c00e810b55802038980d20784c0448503001c010b035955003003015604084802e5803403120070040c120b02102c80c0200d0601ca0f001c80180700c40350168002c200840001c01400680e0081003840700000c55440030441e01d4010811500d4031030f100c803241c2c0b070511249240142440c0d481c240c902406c00c502c07a0028401c3c162081c41050106010023110080740302940751010b0844061651800001c00007210703800300b440b00c140f02e500d00324141e4030f070350b44541540a1614010f1040030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 717937005 1250 717935755 717935773
    0x319021c03020a030e0106060e090901200a030e030d0f140105010e0607080c030f03040c090e0607030504150504030906020d1d1908010c020d0e01170f06030703050a1202010506060309 80
    0x201c01d500510503c041801c00052040c0e55144003421102c0c00e40040b408924038485503107807464001c1c030142c0c0c4000c042e80280544a0401c0f0201442403c04e005680703080404150350381d100303010750481003180c0e202c50100e03070310b60141e607210784090003c403046240c0c51840c040200d00b034007041600351416509c042e102e166103540b40400780a6598080541602c151500f404510008041480100000b019140006440381046e0600d4051f98846500160740c440c60300c0c00c50501600c002c120b01d5440a814240001e10b559282042610303198a42c00c07506a403841d002c2000101a0081c85d4042a6030f90b0303a084500c03d030404601900c00381040403942410f0941e8185106051621070320b070304401891f640795050f00030b0390b6494040c00d4401104a07140903801c490034040c0707000d0380b2000c0d41c05007402c00d03c1c010000804403910781c1406d100c083c001e49012492040050070545003000148010f507402000c07100242c9283c103011116807880019038005500f400042500c520340402543e006011150280c48030328 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 717938255 1250 717937005 717937007
    0xf03090b0106080a1e09021c0c05010e1f021e0d080610030b0a121502030105060901081b1218011112060307030b0103050c0a0801110928080319021c 65
    0x2004c2c0030b18241c9030000202c8001d008190000c2c10070900340c002c17031001110310402c011070b50340c5092108609140c00600e0003050040c0300c164201c0d4401e08000400c60340791408151b0001c45100206103054088241c00420344d40010350f500c61034014104c19000c0d003000e051480e03d0745591700c4640c0002c0c00c4c00000c81e9a6240c178403204010001c2c0c0e401c001a0b405c1494002c1003188241e43d1010f001e58007000c0c8940140210a034001c0d00b83e02000030214038540c106000510b490068000315410440c45000050744072120703541a08100c1e900b81407091316140114002621803104a0300141e03924803c912078400e50005028010304c403640c140d8007a0401d449800403623400f03400106074641c14030490400001140c5803d4490b40030b51b0146001d0132440c0c5d122414000d86049960011450703070302d000381000c10b03480100140c2e1010f0790211451000403480511072001d42c1c0082c00040e049000344240010700f880e0000040a00120940c11148201840b04050380c6810184002c400d1003044140d90800e85 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 717939505 1250 717938255 717938267
    0x10b070213200c1c080103060e031c15051507031209171c020d060504050702060403090506071a09030304031806090e07020109050f21041a0c100e0d0f03090b0106 71
    0x19101c2800f2100d898401001c0441303103020101900c4003040d0a40014400e101c01402411a0800c401c1c00440c5002c0241c40138060521195401c104071558414080403100100d411000040900900c42c00c25602803a030659016406014120301045808048000d03e40560148108082e0014180c9d04054a00c1c0d10742e00090303204268034843d141060701807181c032040d184090a41000e82d5200041c28904102c240000c5810203884401503511041c1080300080d07020058105440065407010303110000c0b460224600c01c2800040c0c070215094900308803c008000029506c00c9010380c3d11150240c030106468155001503001300c06c00510140c4050290360305401c203450f00200944000034410180f0303116030381444404566441c2d16041000c16042c004107034a2052041c0074003840e643d150603d000141c846000d500a40360303c2013440400c900185142c10700c46404d42d00d41200f07090040170b6862034906d803180300218080c400304046a00c1c04041c3e0307201e48181d10b41980d0203000210740e43d081031025244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 717940755 1250 717939505 717939517
    0x1903080313020a080115062705100e0d140c0a060c030503060a0806090d03152108070b090303040b160507060504140f0709060501052b0212010b07021320 67
    0x81c40103d000502c09900348103541c12415100d80103d002424100001e2016020841170116510226680301e03245910607044811148119000c001440c143d84046e108107001b07000641c5d0200c40488008244444440c580000300200020b032818211a1420014500c90300d0080700002120400d0301d900117030044004503003051008200002c025a04c0d100d05240842c11940d002003608801e0f03a280c40c258040c000d000c080c1c0d00c440c0b00c0d2543c0c00d0420004240052a40c1e81c4064912007518a12092044000440780e602c0d80000601e00c040c03800b0381d40300303580e03030700c00c0c1c40031204c4201142c00030350041054210b0b560400d43e0365941c14600440c2e920f03004003821010740240d07000800303040e098004c130034100141d607101903440002d021100d02e089140c10445200d0f6200d5414440d01304002c0d4076034107852507055106c110707001040c00c5905901424400a00070035804030f015164940021030682d1212001c0c2108510844509070307115109000740003624100151100d0440c40308001c4500c951580c0041c100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 717942005 1250 717940755 717940759
    0x2030307120e10030c0c0215041703071509020f12120d0b0108060d02030d051e0d050f1f06110c09010608010f290a210506190308031302 60
    0x10038400c4035110010880744000c120804144000490a4a030410003a030b000da0407904d0a0030010142200c03070280541c80f0140000b8440d02070070702118441e01c440c10555014200840c3d210104141c00618960350703900180d01980e80045503d100c103845560b80c06000c001d1a806012101914100800d0120171902d8251201850203100081c2205100307510241c4045102c002000c1020218040090420078014083c0ea0084081840e45d038056200000c081001090600e002c40d900c90402d40e0301c117910a0482003106c3c55031070003d01440190400d0700018003a02444032500059101d094801300b41259080f0120140300903500e04104082c003844c4000c0c3d01c0202d10098071580c841d0480003400e100406d82100b40462140360050040c0450401a88040d18020784002c942000d00b8034030850180b89030b05d10075005a13002440001c410700c035110303420090142d8110303070740b815650302c499101401c03044503014000c00020443c80c0b40c044001000c81c04484d0040e0007189543c460409141c140400e840041c0d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 717943255 1250 717942005 717942007
    0x8010b060901051b0a20040b1f110303091606111203060a12121b030203220e0a050603161a0711030601080d17060f010e04150915050922020303 63
    0xb028000f424000c4400ba079108103580e10004054950201c3d8506e403082140780990301d055002d1009842c0d4a040c1e411604000354000e00b0001007440888041d05440200c40360750101109001c084100003070f40d0401e4101c55448091a242c5234013045498203c40e88098415501130181504050402002144c00410161407503e2698482a561200c03800040040ba0440c3c241d401034441158401e40031005461201c0b0110701d46a65a10025030f03d018a0004100da0812580200f050910240c0c0b1400200010f0f03070f1008192074a10080402008101c1d81c50703000340940141d0703005450a0600c0c140685600c0301001c500c134240f00300c00b20300a0308205000c84038000d01c2c0f502840aa0360402c0301b28000c040f13580050080c0d2202c14001014200c0368042c4001c0020101c1c1400030990301c440707000104803000c1c60651050403849000a000d0080400c0c0d5503c002080180810106100d42140b4406414140402c4134103982c0d0040c0890390b038040b91aa481c0548420032402d050980c1c0380340d9000702e03000034200d13 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 717944505 1250 717943255 717943297
    0xa2306010f140c030c0d23030709150c03020106060809030f0c0115150f0e09040f0204151e0e10060c030e130203010e1e01120201020f12031008010b06090105 69
    0x1103102c5a00201c0340308101d9101107070700d10424900b00000b00c20001c0d5071510101c1e540030304190101c0f2920700090558451808400101c55501c1180198028513400d01040404004200c01400e58042d25000382c0c015402d1140128101e40682034182c09907040000031842d004070044003d11350303000303000e11029035500e0307a203d900c1d070194149039040031b46542c65031460b03c84490140500350301e4103c0c100c00280000007000084695483c4000b0b40e0058024500080314652403001400a044030041c01605000552000c00c0c4c1d02d29070350b580000c1320806401c000303c19886151400300050205d940e011480300508040c400716109a211507000307880380c00c00c03010943c21240019000c242032248000165800700040145d410741c60012500032201004417052031050b1040510350020500800c0c0300301c84050038034011a4400c100d0081e17186400390035503003203425880c401c5400303510561b40c50f104208410780104007010188207481c40840020b000c285889110001510301d6000520762808011120000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 717945755 1250 717944505 717944537
    0x30803061e0a2d030519020d02090c09030c090603030a18090504120e0409050d081f1d070206011212030608060709090f1404110609180a2306010f 64
    0x2011000e41001ea01c040d180c183e100e0420404000d075040d414030040c18030502000854808607000d0b038102c007500000e0550302c1d2540045100347e10781e0344000390020007903000c01182c2c0c07c544002d08050300c0201d056885601c0214104200480e098545691603001041640d0205000d60480c218a401c001120b1003803d658542c0da03021100f003100d05039194181d0340301c540e0b0690b501c10720f410383d09001110100404c000e284c490503514621601c08500344910038011481184111900f01c4104c1c240861031000300e0745805803500300000c801e003030015142e0702c03c0c04105074a0000c0340d034606a40201d0320580c41d00b280e6440d09551486400030700b0003499525940460980400d200b42c89c0f0034440341c0c480341d681a1501c0c02110031205c1c2400d24022080c600b4040c94010308900c078201e038010b41c00007070140318000303580b00256982c40360b0410b207540000d020000d1920451454aa24801c0d03c000c4420428415101000700d00303105a0160941d0640f114400100c256010342c064960801c071924040700352505c00b0107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 717947005 1250 717945755 717945769
    0x30b0f090a060b120106031503050a1106090303072402040b0f0304081312031103030c04090f11030f0103031b030f0c143a02190311061519030803061e 66
    0x14100e8132512411005124036609409005054100348c0510519503296484054403180b000300d00408003124600c00d003059684000030390b440c94900a00b6203903102001c5ca04001680b80d149803043c40007010042d0300005180600c01c0d1001c45030012495840c081404c8043c203e640d10060003142e002500b885410350b06130300000580d016002100014400000c2070034043c01c40c0601d0400c49000303500410410041c1020701040e1400c484075a42c1c04034041d20034000a1000d04510082401000000720401c01e007541d14803520350480c0d020761194921084200200c0400c5054000d028001c120260f00190500344142c48a1285601502c49040d03d03420301e888250402e2195100300820104803101034260150800d01d6007404200c02ca169060000c8850300070392030b608048214800901064014014907000d401403013102c0c640700c0c060300d81610784081c01515903331203e031886000e08003481c03403c0803503000ca400d50410350390085040c03800d41e9181010000a1600304c846110040340001c006095501c40c50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 717948255 1250 717947005 717947017
    0x70312050c0d18020a270504050c0901090c0c02100519050a020c010e100f02031e0310090b090a11070605010e071b080301030204090c05100f0807030b0f090a060b 71
    0x420090742d0380003109081c1c0c15a50f03108821000b920780700445500503070b105020758040f02c4400b184140701140e0240da0110418902078140c149900303210401082017404181c05d403805000720341685040c2d0b00d94445004481046540d0b801007030025150401501d0079040e10b828129082c5801c40c5064454581111400c1039802440082070022800144154050212050115081ca84501c1d08000c1100048064901110000c2805140ca2030052240d1082c02120000002c410410090090700050078a50fa48200c03039003c11b4141d10300d000706510040d07000d54081c0490080072201c140d10391480440040c182c3c0d2410440041041005d100043c1e81c5004081c000e1030108007400d21441c100320003500c44990700c28140c82419000c80c0c1840003c56090540741500d4040d10005004180b61600e40c00100041e0011071b0310809000103003100035030194405422041503601ca25658640100541c2610110030a1f0313503009072102e03100070781800c000c010b155009113040e40200c0d1031580c5043ca0301d4294818 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 717949505 1250 717948255 717948271
    0xb0109020d021b330a020f071208070219051506010905032e0b100e030304120f0201110c100e030102040e010b12061e010c0203160f08010b040c1407031205 68
    0x100864050a140c0d40b8144950320790b40c005000012505902901c1141002072400300861b03804a04202c1e8012100c098404040d4491810b0100d40c84001000e0010701085490030014070070303200f48082a00c5c205081064996100004055036260f0a2070b250900000502e01c038100720030503200041d140d804000707505c500d0b240c108284100c0c0307050912040c050fa88082101028a04010221415032545404080d8400b20751800c0c8c480001c140380001d00b540705e1984440038030011400101c043c030034602d010b0300400e8402d885440502c80540c8049481da01d0400e4100d0340101c0303407540b502c031042c00390f01d034035400b00001400180303072507192842c3d401403d0702078100e40e00015010640c08803600d0307040e2509820400c100e038a040c0b840080c1f94000042c1881c00036550400812610304002c64070104144078107070b50103040e911070340e07920341140c205419140d01c14854a5824200711b000c881c01c06200e21080c622041d506c518165901d80756400386980408012010000d8040b200302c03013801c0600c1481c2c014015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 717950755 1250 717949505 717949513
    0x70303090318180b040e030306150904110a02010f14060d03090b030106020106050a141c02030c09070e030d0c0b04021002150411040f0b1f020f060c03041a01030b0109020d021b 77
    0x80034290f100f00ea03a0b076500c041c051482c041d20403a80000000903a40e000030304541f4031901021107039000445008c0d0040c8c5903001401c2120700344100c01c1c1c801c007500b11401c00d03034001c10581c4007600806084d9030040741500c80300035402e0b000c14118141459801da455000c0c1c240b0001c00307a9581c03005189035009074000030045c0d54587e4244000d10300701070540014654400b001c6004046180060704c40d12801c0c042041c4600004126011500c0c180310480caa58001030025405d4641894050214171408083c81d2090249215400da11406541c0111006400c00101820b95940f03a082c0304514072440c01680640c030415031010119203089c04410311031441104020804190300c0107000030380d907910312a612100d0070b11461222540b00c0344802503045030809141007180521a13002e03418040c1c1d0348070000381d602400c070401c510381c8403020081d0f0241c0c0c80352a07007210103d0a03101842038543c007804000c1100300d03130300010000c80c010764024000d400708005005252042e5110101c0d26051504145c000a800c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 717952005 1250 717950755 717950789
    0x12160e0906070c170702130c020106050103050c040e0f06010207080d0f1206180c0e1302030103020a0b280207051f0f1b24050405030301150c08070303090318 69
    0x90107200c995000074071410000c0901107255a03070080c40303800e07078450318800743e011401006565401d0f008040004511000308034154004100902030401e60280c103021a0416001c41c421408802c00c490440740748030020000303602c802c5c5e00019502d9026000a0441c49080b001150348442813202d40d4000ba500c0c0c03540000b07001040005001081c05203082c690030351038030b0381c00c0040c040800c515098025110301300040c104d07010030b001d946614000310090381104059001210342c034860740c0214141ca0084034000281503565541d03000500c50008201c1f2001c407400010114402c0d030402400d4a14501e00581b00310503100c4c40860740000304070481c21400740c0700343c3c144000ea5030000e40565008241e03140c00794080c4200942120000e4104000a1000301100464030100504a480c80d10400c0c2d4403805008a0800342009560f0303030030a000b201140300303003207003c00c841c58014902c0c14400750748891010f044c1038951702c05030010886c1e0070059040c041380030152021501c11080f01301c040e065017404030100c25 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 717953255 1250 717952005 717952021
    0xe010e07020c0603040c062001021c0e0a0f20100c02040506010207080c010c1e0305070b0c0702180a0b040c030c020d090b0d0b030f16031a0f010512160e 67
    0x444120050740240f000f0401c1c00040f514800b108403d40b103e90a021031440640c20304100c081e0081d1010400399440401c1c02c00120001c11005885110710400900048000111450312a0f6510b00014421015400071100242a220b003000240c02d1220011940b00703801800705241d0484211040c0000d50074940210841c5842c0c0705142c4c10443c01e2001b8401c81e070805004a50f50142d5440c19410b02c440b16030b10f803042205140f000904000d8803030564880000e580f0700030f44181c010b40d008075980c0d0902c0f40001c020500680c140c642681d001003901d2491a07454282003103003c0b000c0d00c0c81c1080c07600d0b4000c001094503030780510034070940c440c0d400280086111500a05041c14403d9190403c00005010000c10781c0d10307400c4e9012640c2c1c0d0540024000c4141000a251100f03001000e000b6001c8e21103988901418024030304120380c05085100b400d860042d07010f04040314221503030002c0111400060144e41003820308908010041d0085440c10060041040c4a15030103038801060031440c04104250a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 717954505 1250 717953255 717953263
    0x30702090112030c061107051e07080d0e04180203011a130908070b06031e01090b060f0d1205130f080f01050c0304030c0f0602040b0c0d0f05070303150e010e0702 71
    0x1002c01c40264201d00d441a03800406850b00d0440141c5440d88607500800c0d01b082d080c0894100540c00002c490301c40c214000c1c0b051800c0d0031441804042d01035111f00041907100803031402da1410595a800d2801da103800d0411000b810651000410300c044007800340b0040e102442010710412161800803415442442002003002090200c58203142c10003500300009080c03807082e1120640d1020344260b09540b02c41c082031a000758003541141082601e240700d40380b000c040d4006c04103507010b402d051946550340003e00c448101824401c50304000d00c08120f4011800004903c81080040e207810741c41e1406003152105c000d001030f0003a260b141d400690420503c0400c01c84660044401c2d4000d001614240b003032001580001071000e01804500c030044400c0081c02542c49107072135800901192035070389400e1302140396008620030110b0342c86000002d82c241c5001e408040042c010907501c4507d0201e86540440240c12844450214482612404180b40f55103034003d5010301000413a9191300e03d0f00070002450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 717955755 1250 717954505 717954509
    0xc0830061e0312030402030a0804062c0a030f050c0603191802010e2419110606031c03021303050129030607080c070c140f0114030a05090a050105090307020901 70
    0x24001030700740104226200400c51841141a203241c070b548a0f44c56001090510104410040ca054000500801d64580004400503080101e24200005105203145520704210090703045a020711100030400000703585c1c00d00402c11910030300584010f440204017045072a00192030701c0d0340703069910149400103c100d108000140c6603820701c8910304411500081d2980174025030082c00740c00d4000ca41100d1624040e4401c0c280c0e8000e68200340c0d60401c40a81542d01049400417100081d02e070b1405070140d40b400603106000c0c820003000b50080d1501144940c030031603001e80c4683d0070302d074003840701c403410a002c02c1000d0b0003540210000700304503440d5554020101044030104040a08240b4141c0d00c03503d0002d2220b034803400508010946803203004100d070380340c0103150004040203031105001c5a810320b100b85140c05018241d5a440800f03c02e8001910340102010341180d01120620003d001e084268000c2d94100c02090161580cdc0340850300d03110300f90307402180c204180e9440000d496085041002e01540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 717957005 1250 717955755 717955789
    0x80c0d0e12011b0e030f03040e0f15150c12030a060608010b1315030b060d0c02100e030d09020f030d020c13020408030909040c09060e04210c083006 65
    0x1183c2081c100750700d4500c1c072598070010040a41e100030780039101080029048980704c01100d4a440d40c5001444004a00b119204000346005c80450340c0800c04035401440c40900030903129039001d031881d10420640005043d1510b41c855011540101e8018600950252007601d00118410b030800d10043c0003070006030702018164000f0090030440c02d00006140c01034074603003c2c03035540c0303d90740400c100c020b440d0f4280981d51003400050700580032901a0302201c2001c000d41c09460215500310881800c032400714004c0b0031982c01c10040000c00700640e80c4505c41c01440144000c80c0f040b0b0905c00b117450540e03800806405644642c101310304c1442c015240c20581142d60f04190b01d420f04180c034584e201c1c010958060b0041d5110000309040144522084014082500701000320320f5440b00c0c60050884159402d803200f400141202c080c140384d8600d00f0314680000d85410459800650f00c800c41e907408222122070808c00c0041c0c4485805040601c082c048030040020380310340c2048002c100307a0000103100c0c18 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 717958255 1250 717957005 717957011
    0xb090d090605030a1a131b030c120b03031210060305010f050a0306050901092f0910050607080706020a0c02031e12070503130905071b0b040807080c0d0e1201 69
    0x30140d219007166030001905070301060301d005e0380d1030340a181803e1850301603201104421065007a4242c0c0e000d0010b00e001c94982c0c2d0790108070b44105504444510760048002542e00200501444254005280006002e02240e00d4448001421004d1010940344030944140a4804110b1594980103403400f402002d011b10454038600000038100b000b45100042005480d00c00140e03ca1600b0b520001000c1e0b0440da6200d054a110359420340b0803800d16161b52407070500c0c0b0b103102d4114108034690510808002e03201c10100c0d4201410002203810200e0b0031606a00100180c800040c0e13540081d0000c83d4480d10b8043c0e1003021881014140310300705201b40700740100c500c0d013802c170400e0020b000240703c13000707003c44c0756140946c2c100681107100c0c8401424640014002c0054103c0a60740014401d4030146e8544070901002548460384518102d0003900c42828000481c0220b0682002482c1c0c0c544136820b2280b4144580740b07024180004080f91201280b90441c00314000e08144e4180746014000380020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 717959505 1250 717958255 717958259
    0x6042036030a0b060d05060405012304020a0501051c111c1a100e0d0812010605040b040513060801180308070908060f040201090e0c07021e0108060108090102160b090d09 74
    0x709039125840340c40a0000f1a0540210781c481c1c50300071071781903000c2d0801c003510254a0175041c164043c000c0c002103c58084c0d040040b85443e1075101842d42d019580c001c1004090600c0c0400454054102d0600461400440007018082e4403d601c10b070352411510180740c50300d030341100e00c02c030307200d008854504140e06052024004130614078203010319048104541802003859007102c01c4074480b0103240159000a0b1006400082c82660b4010340041a400003141c0d07601da8072144101c0f40c0d802203114080125a041c0418802d501c0c081d00c99442405404100040d00c0303a40701c2841d0b00b510010b048d503001c00c1d04010018014982c4c80010707aa4401c41c242424160b891034041041d40e1220300804403640e084403031011808580c400d560400007410b0880e00d6101e00d090050120859600c801c004a00c1006481c42c0c40c44042e203445000f00c4c500350140c44805156490a00640301c0d000c0c02089000d02d0b5508011030321002001420784d10f0042d001d484241002d24019101c0791405000d10305031001e000d10f0b1001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 717960755 1250 717959505 717959509
    0x50c13050f0619120614010b0f0403060b0102030f0706020a030c110a030e030c042915040b0327150c03010803091005070203071706150906042036 64
    0xc2507401c290142c80f281c03002d08014100740b410a01c1c2c1d800c00001e586100840c0c00a10640b60446005242e1841c440185a40d85520130307407080c032500b19140c41451042c0420800314220394440c0200d500180162490489609541c407100ea01c0120704a5800d98081210b074503107030323262285960351403d83c14410024540c8070011592901002c10040801c160650700c90510b803001d1152402c000030107003041c401603440c140410f122010180c050804540e942141c0325892034000e528514138002240074604c0c0c5800c000b070305001d45d8001022884411441070303021001c07210790540081003024460103000c640c1c40d01ca83c0b842c0300d810082c0030255911414001070206090200845501c2030080761203403601125148181d4584c020000046e5040c0100400085e01660769261030341001c034800241c40b425a11601801509104121807075004464400001c544d42000d031321031280c000100001101000600d40980001e074002051042007080703000d030000c500038920602c001e0501e060641040c6c40040000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 717962005 1250 717960755 717960781
    0x19030c120c0c0204050103120f050304020d12050c060c03070e010e0a1e030503040803040e07020f0c010f09170c0109050901030506040b04020409080304051e0106050102101d0604050c1305 82
    0x160449115a4680d0107a9a2a01440c0141c00e0039501800034040c03981d40741000e04064182007602004100300e0407941e004a48a2000c036840760394014400b041440d1291102d1117050500781494040c40420070104028400400c00d003031003012900c0c10a5540d10300b141c00180700001070080a0306000c612100841140d403a40b02c0041074400c5001c9100401c500d00c0001e51030460250310141160000050100b00050040000c100341c8806502c40f043c0c5485103d001caa0340e0841424107809500105540c0d80c0382c0d032003035140d800e0002d81031500404c1c0c0c5c1d448042034812112240d11800003984102600005540c0010442d00100800c4440071050341c950b80311107844400c000c000a05012038500058219a540c0d4000b0354455088005141c5030329061400740c0d070791221507558807404014562480380100d414065402500d0040e40545680c0c00203d110502030000403080c100c171481d07640c0700d50081840400946114900840062110078190000d000160003002d8003000070307070304140411032040c840c46 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 717963255 1250 717962005 717962027
    0x1d070303020a15200a1407051c030e030c0a1208010e1605160b06042406120f09210206070801180b0306010909050c040603050a1b051519030c 62
    0x1020103c0000119609070f401012480d210088130842c440a004003100d400001e850141001d03168180d1001d01c07110786207558003540c8002031060f40406050f5805541c10f4009103144040c50a001c603031400c10a206070b0558120135200500c582c4003145a0060104218000d0104003150901d0036441d418100e012030b81c5440182601004005c100703007540d03064840c4007140d0000e0202c0e46281c1d0050001d14048025003c1519000d00c180c0c1401000b00016040082e1031401b213011040080106203040016a5180d0140e07280c219082e0743c404204000314064003800000602c503c950b601c0104414000c04195000b507a0140c0866201d2070402c66010b07006900107064440c40c1d800c0541c108101c82c1050301500c0300340e403404d415010b0300c0c00010f00f2582c50b03005190014070403015186241c0540342400101c50340c900c00500240d102140701000720324004901c8444031261507007640c07960345410200708802540c02540343c04002c001740b40001c146106501c644480d5140c90248a00020040000d2100e107041e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 717964505 1250 717963255 717963263
    0x8211501050a0c0503120f011517160c060203070512100f170f011d0c09090c040b1f0f030b090f07030f0609090c05010201060b1213020604080a061d070303020a 70
    0x5540c1c0100b807103c1003003591021204a512480306191407800d00520040038489d03050080240081c0d0b00140d40200d0500c0b030302003040440382c10103540d07403002d0304900488651480e0500c60001030b20710106849000541c4211055100c85546020030600b895105100400143c0c440c0c024500901c000b0308032040d04022100b81a2035000070001e00c04100d0b0410741641111501c40d0f107880d403850f00c44a4003440084c4085a0a000e80354611004410b1182d401021241e126468102450350f0a81c1e24081e80a015880c501900031000701e200c0410400340003045220440c0490060710070b90100c9580760085a003158819500711360341c0e082070030008800c448060101e106150310b1740c0c42c1c001d500295034050704c0181000481407040740450300702a000b49103203001c3d060065007410404507485c45001c1c111240102410b60040d20303030740d440040c0300031003000d960102e83c401006c100000301a002000340222050141c140003c100d9000024080304046003565840c2079000004108082500451500340395908 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 717965755 1250 717964505 717964517
    0xc0a0e13020918030c010902030c010302070809090a060b040e0f010909020612060303160b16050c0307080a0201141f050a0602101a1908010b0418020607020d08211501050a 75
    0x1400c850880403d0100f005010510001c81e00c03460320075054000088103802602602c01c4d502000004401341d126000f009442484200000316103418a020780641c040b42011b400900c841e221004400c40b5032095206a80c0d8103010000c0c00782800f000e0300014014400440c04004802c0c0603404540700e4000c2611a50784018200002031b100d403010300850b8180b00d130701d1000007410f9901d45000c01002000343e45004d0f4110540b2a2689181e010324100c0d911848000e00642c00c04d912580c2d000b00c1948084c04090442d501d506044007262401d0a030309018004421285e2180c850060100c06038010541c000e40c031034007007800c040107032580224030404002c51761a00482c12400191800039240e605490030340c0c01c4020a0517844119402c100442c007503898010003031041d0a0350030b08120a85981c02141982c00543c0106180145001750080c001140302408900140034152502640c5812103a204c4010128101c3c4003141156002009544120f50044c02e0083c040300c000003c00c180601d100072428090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 717967005 1250 717965755 717965761
    0x90e0a0c0509150306070f03150302150f1c0614011404170102190c0b0f01030308010b0304050c090c09030c061804021308030316091502150a0e0f0c0a0e130209 70
    0x1880d290110f04456024085a241e4104807000034480b0b803000c0c0707151000030b1500c1032006040d00500e044908a81c0c008203120201c03841061a007034154043c44070301c21418402c002c03c0e4a032026205a0f54602410000002601444c0c2044519810002003200341082440100308198036070380000d030390a480110910101080b48404c21310700910651465001c0e9000c0001e84020065000640e80c22040c8110001e1701151a4a0400c0c0000c00080c000100468120300c018400100750f0b00c0503642c400d0190b8202c40c260315400e0301060042409484072002140002011303101414100801d090640c0c0c00d490342d0346851101c0c008101810b02100d0010700c11500011111003aa229031070f95005060300c0703c103903a0f80c0c1c03c001c26526108491013250314086042400001030000607042020903c410b5900682a05c011544078650740b080014885c180c450f0f518a47c0d40b2120f40c1c01c0140138000180a8028105032925000300002c484c1140d1007030550a05000c100114840703008549402a40d0540303c00134691 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 717968255 1250 717967005 717967021
    0x10c02010b28140109080f01200309030a0507031b03080906011e03060c050f0f030f010501110a0605100b040905041a0709060e010e0d050c0a1a090f0303040f060207090e0a0c0509 78
    0x405c0591081c440f074444c0100042c42014103500c10385280c07074000743c641c061824030750092600307002c129020822604140081440180100700800010384a0302e00b1030756100890308460341401c00d902080e0001002c0c031041007040d120420000d40503000c0e001c440079101003a0710020107035044902005200700d403920910480d941c00b520580303415100c3c92010940310031000d03520340c015800840c3c005160088010001440b54091007004998501c4a4050816524243c81e07210192501804c007285034040705000080b0b542c8103078007030005090030344400714450902d0704081400614407000c2d98850b11a02c400d0104c429001072000342140e0207414080f813112a1280141d0742c0c800107a44d12a0492250102b05007000004a00c4150442d41180d03185131842d12a00e20f242e001c0307400d40014486100401518401e03160007100c140640030010100c9280607150030811458507115803050000d6480040148140040c41c05492400034207440204010b00c101d0f260050024004d100c0c03107004a04030741c0469048 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 717969505 1250 717968255 717968267
    0x90601081b0d0503040611070f03030503040816080a0c060b0306101a0921010f050c2704230f090303190b100809010c05030903040314030c010c02010b281401 69
    0x90f5007020a6a4840e50f8440c400341030003182c0c08000d40305000d03009010840312400c4900e01d0559406981d01c50655440f941d070800542d2101c0341c4006c640702450042c07000101540300400190f656035582e9200a081c5181001c25141781400c4d15109800c00002c200c09034085001c50002c07680c5000b810303110180540c6209106d440303880102a00a07080700310003070816400c800e52204404911000b048103800b5400c464049030340030381d4418130300c5408020580f0907644000800b02c011003051481c1c44200c0c4010005400c888400c03c5060134200c507508400294942119201d510540d05d00d0030b241580780c8030343d030700c0e03100d110040407070780c0c06411050907149886d4283d018103075104000d440034001242c000d0004e0b255290860b8140d8943d03091540c40c00c9000d00c68410f69000d410050011801c0a042d0341d5610440d003616020800030b440f0620090200c001e00b4065112200c41940001840780b14040074007404c00c00001441600405400005041802151141c4210380c10354241031124201d0900498803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 717970755 1250 717969505 717969529
    0x6151e1406180d2a080318120313120501150b0313060605120601081905030f0c120403081801210908130602060a0b0a150503150a06080f090601081b 65
    0x50740007030200b800314042002c074101104400d111044041c42c1c0e0b40d582d4265240720340c85480060b87c0e4000b21180450610b441c80713541e0048010b00762418051016120701603403405900c4884110030020400c002d10400b8814807460754910154000b030b21f410300c00c0012981c400540100c0d1803008030320514050188560244000e403030f0040951002020750780825554100a004600340f40c0203505e082910014207036509072000781c1c000091410444011001c14691b00100001440ca00592020089840d0210002c0010b1481654240c2e1140c0b80507010403204c800f84180c03141409500c00c929040956520174002210303034406004110b003c0c0c24600f1000c60301881642d078240305003500340030440319004a6903501c40c3c0007141c000c200c040817210030454200141d03c00c0c550785104c4001521403007441200110382c0580c0903505080014070800118000c030b0104d52201c400224200d00340024a1243c0300d9494207d1070309001410307994180304005031250040b907241c281816461a461159845801030001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 717972005 1250 717970755 717970763
    0x6080415020d050903070b18121e04030309080106050f130507140a0309020f1c03080c070c0f0e1b0f0a020f030c0a03020d051801030906151e1406180d 66
    0x12a013000c0e8009680c030f030048035044a000c00c00d440040e01004100c1c00240000340501d00402400c01d500c03040b13580070750110f803034034810000c00348110508091f41c000810040d07120765201c20442d807409000070b0031641e0725040303103214000c3c5490161040e0799203c840b1224900d648030000751383d00c800c9000c1e10303a44800e0000c245020004220381200b5901507100135141402901c4012507140e00c20100001e246d410001c4600342207a03080c094000c03a220729001c0340e0042881c0c1c0300525244117501e03002c0310380886030b020607071003640719a040c895145040c09940d0003004103a42c007003a141402c00072050f207001c2c0156466000002190030140188200903c1c072a034610305003501d603500d0182d960140c0f6071424031070035400b5105a00d565403085205204451600320513040c18410211100d0044014211085090f200d01d41c0742d0200d0350f011a103140650004080d142095100859107848a680700000c0d0342c01080d0b00c8003c1900d070300b881e494207002c03920f40c0707524500c0380031003a0044de001401501c10614050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 717973255 1250 717972005 717972011
    0x18020a021f0f0c0c0f03200a08071208040c05040c0504090e07060201230105010c0f061b02010608030a2f060907090f0e0a030c0510020c01060f0b0406080415020d 71
    0x101c603006501215104141c0c00090006aa0400c01520341040c20503000305907030250400700021a116014200c00c1c800750704209504086184449031524403601e40640f0400300006a0303008000000d0100005680c0608002d000382c9030545034002041c0e4584200760007551256941070080f445a001c6401030b0004039410060404003038949079540e121406441c0c003541c60040e00c0490300001105011000503001c400092980c05c0c0801100c20b40b00c034040c1100d80c40c002a0606000600c180100764680c49035100c40004c03455810380090944c0c680b40d101000d81e4004010b450400742e0300c42405282c00031000321b8104c0703401802c2020b09000803c080803100d103000d0304003804a612804038070316044580000c0b050143c2013a041070541201d01e500341103002603200c0714058001a025500c02040203014070140e5201c440802129000ea902c0600c035000036075520310007840708030811000f403000381041c010002d08080c01c101010f030a00e40c000d0000342c410403410015102c0855940c0441d845813900440c01c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 717974505 1250 717973255 717973303
    0x813140703080c0705060702060f0904091202030702030d05030106050a08090304031b06030b1e1c080d060e010b0a0215090f1519090c120204062102180118020a02 71
    0x91142c2d40c102180010840c010188001040d203018400e07100302c9a0010043c0d80f034400e0107000c1911541c05210b507140c0007601c40503584085800700c4d15014000390300d0740165595001d50300c101030811103901078a07001d00400344010302130198081e0640352082c03102d050080380c03a1684003000385540250341c001010502282e042c2200d00198404102c111003283d2000d01000424004120050b000304604c64080440d07001000d0842c03408103481544088e00a0f01071000044d261640316a81d882400108851515550104440e040d01e48803a801440840500340c1041d810f94002510b8085041245043d0a607041c0840c0c0454130610644441d1581301e001c94101c0f0741c041d044c03141a49000c55003c05a500c10050116105900780a54600542d11100040409090690040d44210354980c00e907041941c400c00484c0800c00e00da494002c001c100c0d1050348100e5850304c10054032090801c08a00485c0303202004014200e0850ad0030001201b09010150300d40d0029841289840c500150080d00f4246120b11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 717975755 1250 717974505 717974513
    0x1a0a110d09030e1f020f01231504090c0f061b030806030f060406060501090b131802040b070f0501051e04020603070302310b070f02130b03150901150302010813140703 73
    0x2405180180c0780d000d0351b000071281c0707445500b00c80140d00207002400d0201c14019611070021081540842840060194080320101080880d02001d82c102c4090340101c900b482040000c5945100a21f03a40c03810407004807049152103680b04047c20002d02f07000103d80800c4866170140f01680741c504180c0c00f20b94161819080c58000f8000600c1103d012846044011489a0080c804c9900d901e0502111400c4c40d407502c6840605440801c1c4400241e503408d10020035040c03500f10003011440c0c0988021142c1040c14280242128005449480214030141544119000c0e0610596000340c0450301c0944a5659480c00d41c003911a0f030203100c03000030180240b4404a040c040030422000c0d1078102910415032a0035400b43c8a105201025014000c407038031400051504400000c048000d0358008120f0360a80c001003858200c03104826207812100d14100400c00000740b05040d02e001303425001c0c2d0071040c074580020b460914084c0082c025100f64000c200c09004c0003400103220b445c4001e0444114586c2d90030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 717977005 1250 717975755 717975799
    0x12070503070c05010e031c1107060201240302220f05070804210210050a0b03030c0303041502030613020a0c0b0c04031a09121b06041a0a110d09030e 65
    0x9001c55000d506100d000c03d0300d51140e1220030038401c005e4010000810740e10480007807054000c0426040102006842d04168802e01103800140756580002c503520300da0b10001c0700e080e04036041311443c0008091082016a03580000d0305540c00e0607401c00302081d240c01600d0300c050700c2020303410842039040c00c0500606a6018603c40e2066000300c4001d1200402c04002c1c495180300e07442028016407041c00010046040e90380000d4105100c480004bd045421030042070550b00080701228031a000442000700344129091021403d02c2c50140852952600e0800110b58080384d03d00c4040165000c05c035502c842e8043d07110b41c80c007035400404101040c50100b9000445030b200f800b044030407000d103141094220304400070b1700307000b411070b2800b800d01d0141c09540400c03290459850000303e240045110300388000d062000a0082c0e019403c0040b104204444400b012640902a819039a01c1c0040105400a020f800e07200704001c04c913000f190007038282c182220b803645041419a40400e8092070032010310301d091 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 717978255 1250 717977005 717977017
    0xa030b0405060f0405070501140c060709080715170a0e0703060b041104030c0e040305071406071d09040303050a02070b09032215050a0311030702010c08060d200312070503 75
    0x4000c580c1c040d610420906040030050368010110f0744050007d1020350301400c1036916844025180c6820107030000401d07803a00c04241c1c3c03880c001c81c8510200340b010040038402d03000903100e078195101c182040e00f0070091848031308501c0d1000a00e26070000c10300c2d0132202e4110403028000b100484500e20745a080c030400030f045180105100740d14044804100c005a035041d80d04407900003142d545124601052038020200040048080001c104040d500049207042d85114821600000713181d9403500002c0035190001890161213200908140803e140d6211103425504c55414580820340780c45150a82019005003c0002d080d503601c1000c00040041c008058965800c2040002c2440c2c14020010340280049026403641c42d003440c4001d04140d03000c0c034001c1000004501e00018510175140d4408010342055a203600146d454070076902c42540d010079400d420000880c0d481c01c92181035a00d51180c510b00e1402c1701e016a5408004000710341d81800200d01c441d01940e14555161607920344170b40c13039502c41c0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 717979505 1250 717978255 717978263
    0x5040815010608101208090d050303160905040203040b2701180c0b09060301061d0a080a0201020d020105090703150b030316170a0e040b03011b11010612030e060f04050a030b04 77
    0xa200081c003a0b41010a102d42100c02c5140c20400d81402502c802d000ea0b80200780041d00014012303415000500108011f600c02c2c4403080d00d880148002100c0200585500d1380050b2044d8018002d1201240520000340d0f000009a07101c140d05c0c0c1400d010144108100340304801681d483d08403102001170140601d001c1c0c09201d04850b2405648034100804140203122030b20783c22071030030300c0184204d5004040954112400003101e000c03d000400c000340104c20b46800198458100e8405541156010005440d11402c10700080c4030a01d8003410181c1d5400d0188009000c404003807115481c400550307030014070000e0340503081e00e40d2145100d03022401d40c105403004a511040300e07848550590260001c2d100440360780c0d0307a1444034a003448104000fa2420042c081d40c913550300c0d040281c12001800e5010061480307a01c820303041c9980b07081c17100d003183e00f294841c030b00082e15100b0b00c500003035000d02d400d54080800c44013070752160340303a61000c3d8082c0129041282c02191004001c0305200f40301800a02c40c3e449 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 717980755 1250 717979505 717979517
    0x5010e1b04060609120f0f080c0d2d03090602031612150308090f130516080c0904091416051f090b0315060714010c02060106140a050408150106 63
    0x400240402c0707603007610070500000d066010074011100d400e00c0390307032959004580300d210741501c6445030a5034041211040380d18040006154a40840610209907200302c20300f40b412031422684a0015503008000c031042000000600070241240694890300c02d50303400807000c54917494804d0b001d00d0400d04000f0000301090f0001444106503944e0300803550410702c4810288035091855a44580300e402110b540d550044121111a09c29100c6014417000301c3c8a80c078000c202801d144240c052040c0c1c01c0c4a40d482000a01410890300007070004c1110a411403e460008200c042e42c20040c01043c080244c1d141f09024031895801c045001030006400c0e80d40803100c408180035200d02100c4c600240c1c8180c0f0f00403400c411410021076050f807018540c0f2110f04141400f44a05a400280180d407000c0d008031f42899101c0c0c00412150000d100341c14062286000400095040c10b01c090100f0001e0150b0407220400011180e01c042d11560a880082041c5030403903507001951140300c0c1000707400b40190300000da0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 717982005 1250 717980755 717980803
    0x30f06041a061002030a0c02060909070c030e12060f130b0708070215160c030207090c0c0501060602010e06150307150c030e100c0206090a0e0108030d110f040504150305010e 76
    0x207883c40380d02ca866840b5400651800c0d450100585587d17405803820307039112009014075401511055000e521511a0b941c1e805441e403c2c0385030180c160b00031114540c6c0210030480c0c004440081c0064010f41004201910000550311021604404800c94038024402c3e0000780034410402e0300281d4440c000c1c40d140c0c095582c1c902180b1100c0c104807008a5040d0600c0340840e00c0c03c5407640c0604452007142d1b0191055509050300c80e8507086c2921a461038400005200d485510b090050a201c0c0744041c040500c001d1041190038400316031b640d400542211540c400030495120182c0d0304015000040410a540709041080050041d0603000038040075404210402c040f0070717880c50207a600400c0e4141c0c4e80c681d6402182e41c0c1c1c0034407556400c1007400681004a652001c5080311003500c60500824030400119941c1e403000811805440b120300002080d40000c0c0324440c034040814080c1d4050351400e8600044101c4003500c070b0b0109004aa1000d0455440c01240c1d81c0784000c0030a00040195420700b44038031940c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 717983255 1250 717982005 717982009
    0x303110312071121070201090503060f01030222061214060f0a11120c0c0708151302030109121805010203030f070f020f0f0106061b0b010b09030f06041a06 68
    0xc800d0180e0500288541000101203c0c0582d441285504030541210140d01c81140d140340c05082150743d89108a4010401d03900319070740311503c0c2d4080d01c010b8001e800c842c00c013050702c00300c00e0106000007403007130046603100d116094656004054130188480148410380d40c0c2d04444045014010301500c84c03241031091541d100c000011484e0080f110028031040340d50380c00c4d030140d0041c21006000c2c109603004004000c2da9a820f00415801240d030070761041e41d42d01341c0c180090b01e41b420540c0603074030710380000710302c0304101c207400b50b440d0f07445003041d2840c1403c02080c0c80040e0041503c2407006000503841c81300202200d034040c0890300c008410000d4407000644441c01680d490000312103601f5003410342000214130314811410301110461a0040300c0355200300200080c00c2224054603a42d0581d5103030410040f241c0c1c17100510446c0310340080580300400c0240c82e201052101400345191031200011000c210b51000c100340014401044103548030307801c0c03524000032090000b08a001004c8440c00100d1818 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 717984505 1250 717983255 717983257
    0x5040b24030a050c07020a15020a0605010f1e1a0d0609020a0305060307090207150b0a0e0915010b0306031902270609070e01080f0c0702130b03071e060305040c0b07080403031103 78
    0x800c6d0024481c0d200d036880d11994000450040c0503400450140e14081c1000032a0703806201d01a00140c00500201c90074000aa2904903510110844c038110b1800200b24005004100c3d4130941841180c10f82c2c0c85085004002c003609041c0c0c4001100348c400210901c50342d078140d20050090000702d0030f4407401c40d42d914900e0240e0103010405403405150034440c00c1455040d50103801c4030f40e00a040400c0f9180c3da6040d00044400c121001049504001058074069030781c000003c0c050050a02c201d4214107000300481c0d6540c0200e030b9010807003001c440d00101903540f0b26440e4408140348401d03020054031054004804207070203489c1e0501808111000c51519030080880e10115807040c0d485e45c41580e120407040a580c400901411111a0b0411018000d03889003403580004c014051004a94003403900c0a143c13038102640d10010607040c60500221550844820701002c0300c0b02850003141684841c100082c07005080d40c0300c0c0e03c640c90006051410480f56002400c1201e009440e40c600c60003540b0711190726 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 717985611 1106 717984505 717984517
    0xb061b12160b01210b04171c05060a030b04170d020a0f020c0a03030f0e0a080307060e19050706050f07020a080601080c0d0c05040b24030a050c 63
    0x5000c0302451050040c801c00c2052401c51341404405102440003500c014030b0400c40c2004078090280301c05003a45200034000040c0d039555407400440c84840080b8102c484005c0c242070019190f440c1031182c4604580c1c005a2403c1599955901c802a84461641c0c6204014080c0030a6800c1412480a0600078060340c60356011320302a0b42001e86402040203405129504d14203060000940c0041f60984c1000c240c20000c203002c40c15000100c03140e55941182e0075520001c02d0840501510b5006811142110800d035406190801510ae10b41454007101a10301d40c4840720403c81d681c400e100030404082902000380c1400350a81c0000c41440c4540d2180144d41d000344013300001105015169500f0b00c01c840040c225881903590300e03030340f072264402c0c04c0c481e55071425159030307540754110207130740364128801650314100d01103100c191a03800c282c8540c04041c2c074040010b18074421140807203035 = true := by decide +kernel

theorem cover : BRFrame.Cov 717805755 717985611 := by
  have h0 := BRFrame.cov_init 717805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 717805755 ≤ n) (h2 : n < 717985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
