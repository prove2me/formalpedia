-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5490
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:01:36.206992+00:00
-- url     : https://prove2.me/submissions/44501dd4-d1b9-4267-a204-3d166f5f1c7b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 987230215 ≤ n < 987410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 987231465 1250 987230215 987230227
    0x312060f060d090b0106020f030403021005031f03151103040c2c0f01141f0f0c0f06060e13080904051024030507030c02210f040f292d 59
    0x381c0130019091240c8001440ba401c81000b4446001c0140c0c2c0032241e020300000200921414142c0d800d4100400074915003510200403158007540807040401103000711500303080d06d580040940305650565440d40c04103c010024040007590102450301203a03810b01940c03040c4400a040202007450200084c031400510005000900c0c44800e00d0381e04841c40000c5514a0003c40c509220081000086852004080c1103441002c0c500404280c01e40d031010703290540b0591460b50b00ca80340c42c402d9880030f84203141c0e50b41e010f22038041b00d680350301d401110420305001c00301002d86d104004d034443d803104640502e880d0400310301c4c080340c0d41d401d6102503c102007060300c2c400441c41042500b03654002c0d803c800281003d0100d40254040c2c030414900c2e444560140c90801581001d0382030138107541d00c103c4004034040041c6500d140c0050054005440e038500c0da00b80e510f1030012101e0115103204190700300300350109418843c940005044494800415100045c500d5020388440030549400d49034680501001800e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 987232715 1250 987231465 987231473
    0x2040627230307061106070804020307170610050a080a08093d0c0f1b0b0a020f010e060105060a140c101407030b0907030f0e0a120207080312060f060d09 67
    0x341c05603100203600310741c106603494504681c415800504811190055000314001c1449450307240e50150029003103807003090b039914044d1312102040c040395100b0b07002401806084003c07401c034480100011101c2c00b4296007130102d41510f070201408002c02541c000940454162601c40b0500d080384134000c80100050709140c40882c550070100d40d009521043c8240c4600b845006071740c0030400e15002841401c04c9022a95030318001c5104203625582400007000000340030300c1400042ca51482039130701800355141600c0350306094807080c40300c000302e980284006010380d4841d5020b070b078103003806460300340c0c0070030700368405403600d8440c010914600340030300780f005c4610750b400303400161180703694941c502816a60120110f08a942d00d003031503135100c202480442c03a0070b4881e403c922484406000006a5203103031820503071900c0c0000d0021504200340480741d8814540500c9030710000c024020246161a85506100c80c03401d000601c4c0600c10200303240c0d60f038800c0d2140e8080e514007005110701040b043e841424 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 987233965 1250 987232715 987232769
    0x30302061f0b07020603070203070605181e060604051009050c03250c03050c10090c05240f070c090903121503030203090d03140a030c1202040627 64
    0x41d61500300030308010049040070700d1800e03082103410120b045030400c0229402c00804d035001800800441c8024055240411014400c590049031400c205d1500b5100410080d0b0034103401e042d10045850855a81e20a0b030900030400540c4020111800030305c0380d03558640c2d2001d800180d002100403d00d400c01304286c03040b41d82c2c0118015100c022240180300d0300c4980280c9000041104640000c3c80c516039140002e00810140c076803004403106031a03040300c081c42c0e0401201d00155007518003c00078442000241001003040d00000399007080c240d20001d59101040c11707407044070201d030340c0d80d840003648400f841600c0d442c403009090002070a0121070780b542002000e894030456051148c61a2804054041409003260800c40740e058028505080a034070401c03805002d450303000c0d014085d07461080b04800d1890001801103034410748000400c10350303061009250924040109503d107104020500800b500030742c6101c041440da49400b41d2500d084041100d0501a562000801c0b8240c0d072000303132803808410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 987235215 1250 987233965 987233971
    0x3030606080a0b011b080c0a080415050a0915051306050910051e0c030c03121e0402062d2d130510050918040203010b01111018020a03030206 62
    0xd6662a510b80340e0341440d038100d03550034010324080b4144241c95002441600c4040304c0c014000c0c2030460916888001c107a0038034800003411202e44000150501001c1c00341c204801e0001168641f81d401c1a200d400050206d51080c016411100881803028040521034421039045a003402101e504480e42d614025000360000c58a440c86480c244002c6a0076a2041081e500344640c0c1e2000c0e6421184809042d1820740d0044620340340b140810011310405180401c0100f03041b800d44a40ca0b144c038681a0311124450040000e040513182203001440090fa40c2d0b070042d00c2c0d07294a50580114200341c0c00158151610340000600c100d513001080e6100b20300241d01100040040b4030702080d4481800c01100c244a00c03904500d0201403180e80000c0c0f2480c1854188030700d01003000d0400c0e619007c2e050340021402101e180c1c466003a50350110400046041c28003c1c1c0030311170000c1c2403d075481e100811106445541b201c0c0e5003030740f50303540301000c090700c182c0c0032165200310750003900560010781c5a06000392900011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 987236465 1250 987235215 987235217
    0xb0d0f0f05100603110306040b0a11120108030a110a080322020a18060915030f0302150a0504110103020a1d0f0d12030605150a03090602070803340c11060f0703030606 73
    0x717001500f91400c010a40e075200c1c03a403000c1a94150364462911038010318050f00003103404401403060109028100c94150b0203001400002c64480100510044c1481048551010144c12000060000545510503240c1040413a801620041d03141c250072241c03403840c0071004e58040b0419000142d41842c070001188030105104080c403045480382c83e000e00f074030001752920203100c0c901a0100041041c1e51140905e41d442441583e0044c6c00c0d410314013600d250203903142508513950306d060204104480f103420126607801c1c2800c1d07050030349000005e0404a41e42d040c0c2040c045409861100301d640300101072a102e540204519000129030400c0d200c120108680000030030315011001c5103d01c0c004000513841c05c0b003003414920b00794204000714040c1400b4002142c1c11a003c0c4003503070000b000c0340050f40c801c0200982010b60150503662050724031640d0007091040e00f010040052000380c0c0072025228640c1c0001403800c0130191000421910f00c1225404084038502054040c101649a00010201c0c1c02c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 987237715 1250 987236465 987236483
    0xd061d0c030a030806131e05091605060304030e0a15030203040507061701120512030108030c011512140f01020f0a0f020c1e03100f0209040f0b0d0f0f05100603 70
    0xd10189aa07035a045800500480e1080300040c08a1408034052203402290800106003500d0005480303511450549843c55110386410070809444000c00102c400406411050544507180002050003488050406404c01440b1a0415001d0700c40c9074400009100000d18180030242e28a03000300250004d4030200c44c40e008030178001410612582e0400d141960800f0740442d076902c1c0c031b60440d64004080d0011034040c0900701030640c403440850042c500030480e580245a45120805943c4d003180d2207800c1102e40114000014000380d07226070201020164451100718099828000c0750b85442c03024604150342d98000038889680d40c140d800581f050300c602da103400403400400d810030b03a20f80c9200041c203034100500e03407800910503100d104010700e45803018054030080c1413200711b0103050b90340c0150307031000d40f0741c0025040e040d905140c8642840d0b2007610401700a0210b0b4200098440d2190001c0a062581c2c2100c0c80e80900078010050000d55620008a807c440c1070b505c1043c015061610060f02c01e048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 987238965 1250 987237715 987237733
    0x3121c05010518090f0618010f110406140403050d030e0d0305071d0f09090106210c1a0f03010f05091f0915181d030c0601060e0d061d 59
    0x922030003460305a5070020b081d21000c60140b4002ca180c00c00080c01800305204402e03403619160b10500c02c0c24014801440002c880560192855017942c00050812100c20700c0c004c00001c0c0316403010207171000c0d205203141600310390351044081201c501032130f0400b41890180504c14038015030564050710608100c4000d0740c91640c41e40030241d08032141201d000f408100300c0c84003040e60750300c00e001c49868140c0007420381400d6038030034001c200d583c181202d884942c1d82d0b54403414030075101c1500303a142d81e08000001c2001560450359407481e4101203489a02e02c0c50404046820740c5000c60ba050385c841030003403400c468413507175250b070315120390b2005120303c5002d0690640400c508140c03010031690030180c081030024015140152602c001e1004004060b04500c0c3d85030046043c0c00084004d04460401140100d56203160720480023a0860150040116500410114030400d901091007070446009081c0703003a8041c01003011540300ca140000041c285481c0030380315851412855507850703c038200750044901b009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 987240215 1250 987238965 987239017
    0x31b0807090c030e06040305070b0406090b0405010b12070303121109190e010605041d06131103041b260a0204110c0d0513170f0a0c030b0f010b270312 66
    0x3138042e24047c001500070868580810740c0a100303982c01920a50f40090140e9a0b920340c203195a4040d00c00302e50f640d464402013030641c03a0100f0305500d0310800c82d01401407030b40307143d4025000c1466a001e449245444544a45411140c2010f668003000050134075810759a40480c800c07110b840d18042c000d0005480d00020900600c84c0c000d45045d6080c0c03807000107182408103641e4105010040000740d020201c8519173341c22003520700a64810700c0b10050180d4507420a4030b4140c810300904056800042141c0d00104905010f002d2245041580ba1b40c24040c00d5500003d07140c10300a284070040d41003800d0508140d080301848005000781058a010341e1204841004121039620412920b0303800514030810034402200030031980344030000400304450b015411021254208004100c1c1900c0f00c201b100703010014071004051880e44a13541084110556041000303540440c00742040901015160541451600c01001c0c0c1280203810010704941c081c03501c030420444c1680c040491845440283e206803c110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 987241465 1250 987240215 987240223
    0x30c0f06050307050f0c070911070209150609010503040c0f3302100b04150b0a020d0309020a060f0e03100e0d03110d090312091203180507031b0807090c030e 69
    0x304815560303645481e403203200040043e048104121b03410b004298000403080403501c154101c510001102c1d54841400e4010814154030003041030424100300c05031804140c0c4c0e120122881901c1c24241380c0e13125100e40c00d1039400d09089400c1110700385c8200d1804190b80a8130f00c01c4030509890301310414044200080300000c83c2c8160707822880541c0c0002c0c038999580805800800702d07813201810001da031458242840356502c1151348441e004020004100b80c59980c103002490094085080030710110a4a501081a800441c410380041140030402001414031400000140c004000d003240c4509140c1d01501004000321640025a403180041500585002e07000e00020b10380e428445500b805401d0604034041c1c130740108104c00300001c0c10b100744e0880c1c0e41d80c89424901402031501400580e454000a1f04031003c010100007030f40382d44000440058000120301095a911111300301c1168251058803003580c2c0c40c0d4000441500600317002080d141c1070383c0c0c030010f00580f1030ba41c00e01011501d18091511 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 987242715 1250 987241465 987241471
    0xa0603090b06120111181f0503130f0b040c05090601020d0504170c060d0204031707050a061e02040608040215070317040219031208060f060403030e0f0406030c0f060503 74
    0x10700c0c8109001801d10315000c415082c54a841c000042414502c41c441c004481d841154007100c100d0300c01135811082c1c18420449030589040e00f400181000c0441d00140c81303408000c100b842c3d00740700036030301c0001c002c0201c13016924581d200c00000001d0416280411000e0740c3c9020f80c501800c0c24900188140d0b200051024006455448007494070382401d078505e40329000d1400a000500c40c2c800101802c0d00d41c080148403000c010540183c03182d04502d4038540045072001c1280f01801305000c988080340020600c0b0540070340c0024005000303040424180000c00c804030951000724400b00d0000794450308005c03d24440c5200302c4085e000302c1000c2e420603500f8019003c000e000550401e0720340d038041240f2040c0b19001400101200c1a010b25030a02c1681c424840d081115450f51800c2002c0c0419003040d045904650100e44104e026078040c004035041d8000c41c0310140811400214460042c1c45050140c641f4100180c401e0190684a0500340804c460b01e01c520f07011003401c5400044c030a8842c8080da80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 987243965 1250 987242715 987242723
    0xd09030315090b040e031e030901180b15030c01300612020a0e070e1009090203010f05120706021b04020c030d060512060f040f05030c16090b040203160c05031902010b0a060309 77
    0x907c685603095030f0a01c0360801000000c1c1c035035a80412110541c43e04c0030750b940051240e1503403800c40c50700c0c120359000d9940c9114a140664461f415017135203603030400a541d01250107489500400d0b83c1c1c0340c3d45d400f9503507414980c42500510b8414081a00c03c000e00e601402d1500a5804c102629600d01071100210012140c49001034200600240d403403500200500340c07000180340445405446294101c1203a00a0b0702c801c1c5000c2040404100504001d41c12800410f01070006d48002440c10001940303650400c803988030281054550b901e0155220380c15200d07410426400c50351100325005051000f048640103d03441184048080c1021034000540d42c0d200d2070060705554005d0b16107684580310b50580700411581400700340014000710404004d800210342401e01d0a02c4090316156441085414a076a0140190700400400c04490035003541d43d500e40301c444c0303818101d440860501c241540038100b5211042904040e034008003e50540280c42c1d1001c1c211118600e090740e480c810b50850728000300081c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 987245215 1250 987243965 987243997
    0x250f03152d170a020a121a061c0606081e1b060f160201110a050601150504030c060e01080f090d0e031e06090706140d09030315090b040e03 61
    0x801018801e002a110049078048040c0c0302a880d0304105006040d000e0b149101ca500c449943c00070351130810b005d40010700c01d000181030000110b403900c600201d20300441003040651000861126110010700c502d07408058900500c5600c45494a64040c0a9601c111005440344c0204501e80d10b01c0070090b4008070030b46c84000c10401184880d00100001190803003980300205102c2c0d490300b03404001c01880c00740e03031074100c0122000d194030002d8041442c81c2e002c1c0d11150f001c0618000011000a00c09040d154206207050441d90480c00485ea644070719040242000d00c3ca0b0000500c1035080382c000e40d0000000d0b26001010f59032280c51071100030741110100d0041d404090071f902031b203024405110308440080d0540e1498034003201c910000004c040006007007940034900b004001c0d0418000a0068240c92030841109400c48e050214240520301648402940d1140c11000f0103019900c500c20021100c1e10700c0c0301d0350f5943d000080080c80c0800340f050240d814985049002500401110034518507046a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 987246465 1250 987245215 987245249
    0x80a21021c02010207140a0311160509061201020a050d0516090303050901140c3703050a050c01141501080402031b030309090a1506090e0609250f0315 66
    0x400303001c00304001000540d5030030084040403c501041c6004030b48102e400810301959680380c014186e41c440c0f00702c0c03100c5400c140400d4280c00d03582e07409031045400c106e608141c592175000005546400075503410716250302c0000d28a01d09504030003c0d02100d40e00441c204029981e01d0605072107101070504000014001c06406d00c006401140544500388040c5050007502c15101e40900301c3d030344010088601c2c1c5d03103c42d0124030900039002c0c443c2400100305007400d0f41003426000203184140c6000e002420701c00b011540702c103c1881802510721078001400284090040700801c22094081540c11035103810b0012aa2002940500e680600441c0d001e001885480c807050400c00c11406a41004c1340d040c00204094004c51351558103250084100e650000303088651200508030400c59940b0070b80c28803000c640108041c0e90390000381540200152540182980d034181c0d46408455120349500e0080400609003a40650201003a84050041d031010003005003d030788a8152800300303211b44900310543c0345c48 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 987247715 1250 987246465 987246493
    0x403030801180f0e34030209130605150f0108040302060a051b03100501090e1e07050702090907030c14060304080a0201090b040602070b0c16020f03070807080a2102 72
    0x450482461400b000040c542080c0c000b48050328443e584004c03007940f0000340c0a18000381e06011280c0c4692080001d0600d0006010440c40310300c00c0d1001904c50481d140c009140068a65801104d0641c000030806c0907282c01c06551030000b050140d41401000c0500e0100c0341940211151805181c16800510440c0e8480b095100036000c0189880b4100501881c00c1d1609a40b18014600030f40d5005050981542020001010008103901000d4064440410311401d50007031143c1c030252000c4400840c00e6542c6119042e0f13550b00c61848020340140c0c111040202c0488003143c1c2d0310960340704040301d50f002d59a480d04070300e4103289210090350042c1e040022500003601c10340100f0b4101614000030400c82003544914500e00c074210703030607956640c0004110080020428002d0750200361500440d041c03642142146400c1905000020b008028100501100340d400b0402180104803a204030b946058a450881d030700c0d0b11010000700e5801c00e50728800180a40d0300d0f1004450510503034010980c00b981c1d030384 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 987248965 1250 987247715 987247739
    0x315081b061c1a150405120c0108070e0105191d04330806070c1a07080105281203110a05210d051015030b09060409060e190c0b0403030801 61
    0x10081d4010901490901265200ca0340b0140304e40030350001c3e082e2114609001d01c011ba0852199038000c40d041009120426a0000f4141c0e130050024501a0203100d085001a205482880e5040c0c0314107190301c40002189030b0028802112008100880d183e907040042032105503a90307003a4007203149400009501d07e1080406c0c0b64034001110000e070720f200682d43c900d9a81040340a41e2044002144030246600380140c0b001c0040d10141040c0e0810000e2411000c01044210103009140c42100d44e00207084550180a003240d0003181d070306039a1100281c1d0341918030704540511000310302042148070f40300c1c541c10000c00c50102e035580280180140200070002e4501e1580a544102900b04050207a451480d02d1845010320a0f805039840c1036055040280b02e4011081800300101094145081900c2e03d880d2543c03030a40010003a100814181150314121014100880003c592849422041c141c10300d400380c1c070404000d024040c8807070700301e440380700c451018460780c007004c1e01003400880100030b1400080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 987250215 1250 987248965 987248981
    0xc0b0615220f080604031e03020c01050a0b01030f06050d03140408060103082124221a120615041803030c09061b0605070315081b061c 59
    0xc20064a08811460800540c840302012540c101000038030901085480c0800360740501001c000409061405030f4000340240b10960305a1f88141500140c0a003842c0640c06407854640b0f810000d000610308554010002c02d0b030b0603c907500083c107110840f200b022442c4104c0381610130151140c3d09a0800e5101994910700050310260070031801c00c40020102c4040c0b009a000e540b0801505170b0340e03c02c501503031003007401610900d000925813005110b078030440d01c06041074400c8002c04010101c2d95440002e51780410105000001e82c10389007502014002640c0145040b81d004174a8103040130314641802650302610045111691091011170715010008800b0311003000018000310305150700e000800800655058200e01190302d50440c00b80e056084bc0c03500010303207a1440d15051050113846034004606410b070303020300f20a81c0e44002c01c0c0c07038034480e4014449200c44a0501009296a44402d030f41e00e8480301c1c081c400403030080f01401d4191070090201c071000711044918196441c0d0003070785140180400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 987251465 1250 987250215 987250249
    0xc0f0e0a051903020901080a0b07030204050d03120219030b040e0a051b0f0a030302030a03060512030906070602090d0311150103020a1e090e0705090907050303031902040f0f150c0b06 80
    0x40000006176102d425041c080c165040c0900300b041c0003464846541c880182c000030034180180014042520b0704a120088160945070070889050723034540000080c80f80343c5d41c0b411180801340c00c428205816811a4200b03102c03c4d641000316100404040ba00c03803401180040068001006d007511640b1014602d00c941c06e0024284121070342603000040c41c166660f44214056000812003030f2100e6014400c4070010a41580d80f42000d21030030f032a158a034815a02ea4522802d8081400414012254107031000403030050904448141c150130094032140150007684034030302c2000b03480483d101240000b00c4c101e903800b400c01d90140f4280507105856500007030f2808216800d6000c00070744200c5c0e40c000c4240c1c20380c2c0d01003d800d1090a280070310007040d0004040b80f00e40d0340030715801c0080303890010480e6032201110782500121ba0300c4c19842e0700a8419640315450b10068003101094220f88040044100c480d240b1440e010220184001c0d070380d0f08400003014202d0741d011f07070000d42d241c20704c03400c422541d80007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 987252715 1250 987251465 987251509
    0x50603090c040204091a090103030228020d08121b0d020a02010b0a030c080114130f020d0f08030115030903090506030a0b0603010902120711060a0b21010c0f0e0a05 72
    0x1001d00450201d030420340c07116900b1911103441c000880b94a03200082c03811016030340303050f5070343c10f42c1c9004e5601c200b020b0b0b00c5000b060b880d8655843d0012254400803255038001c000401851f40760501d4485600140b904200e000c1944001c180310400c4e80c015550100301c3c0c1c0354010700f001950307220f0348000c4d00400f00403010340d5294a2266815600d2101c03201c043c61041402c0c0900d50704110107a800c44103880864003440d124682400900e208080c0c84407100e60344000d004020078014404204058200c1000900d00051a0b012104001c07001b4007940c142c95001010309034459010324101e007038070000c050203404a44d600d0301c14401820060b0080d68403000c4100301084480f200340105030180e0090b07010b144840d5000c581c0141c4806401600c41d00280603180c255400b9040c12203668032802c020300744e8500365548400050880e100c01d081c80d0080407041c601007008d00c0031030141c203019103000c094140001c0c1d01c0a120740d80182c090303002e503c0060006000002090300749002c0c030854842011008400c8d02d0307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 987253965 1250 987252715 987252733
    0x30105070f020c150c160648020603090a060b0a0b1c1d1f020f1c0605120114010f060c0605130c151202070f0b070c02031c120e0705060309 61
    0x408100340d000c4070740c07001b0034840b20a207017090041c81103440603600304d2950700148117014154844100c0406556400991540e0003031f25440e11105540f0500c0d000b50400c501004002c100480410712a1006010707820034048010420201301e080b44e424080c0c04840b0f503080c0030030707440e40c0b01c5940d10a0500103030220014040b01120f41048040111407210310450384102d1080c41207420300290000448002d440c25030410b80440a000740c079001d094896422241004414a190811034010100130400a014155003840c144490f5028115840c4003822000c6044000240e103410148820100c0d00c0c00c0e40d0b022101003041e510f03a005000042e120000c4803d40c802d071031000c90400020b02c0010140d590503420450b02c0c000c400780801c8090b503100c860350f501c140242c82c04075010b0340900c001035500c2904189141c2c0c6000059070238040c8810b000c0d40500c102c01000b45007058541c00310580c5642511607240001e41e040009060750030381808860b0340c0e008844c00b00030b00e0415030040d40c0c208078100190f5181c40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 987255215 1250 987253965 987253987
    0x60b04140a08070b0a120c2015010603050105040510052d090901140a020906040b09240a02010605270408040e07120b010302131811040305030306030105070f020c15 72
    0x903103d40100c804c070103000502103141c80d04172001544c030454411043c80b01142d040c001500c0c1d451002002108400a8010804034050601c80e4007010460910340d03405650b1200300050040109008190080340303800c010540703408004502c042180e130020300361000611503000d2110b40c80c85507515004010f10398160240d0690311068200c1c4560059000014030310503c588950413107801821444115104100c101a9030b01e4200131101580c0c038000645a070b400448000c201607042094058581c4509840100030001881c4003d2000c69400d84c001d00400da1140c0800c02020000007400c1d00c0c078900700718001d005001a505041c0e12a00540e80e807402c0c59580d640e02400202c0803160200000d84e2208000000c0940307200d0840c0d609403c5c6801c41c1880c20a95450014080707502413035192a880b44141d40c495013039030b0072000e03582c204c0c0001d00340c03503541d40d20f8029929001503551902c203508010024200303d104504941900c00035034020490160b40bd8144500c088820540c03202d07180d4204050b041c68 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 987256465 1250 987255215 987255223
    0x16080415110a0c03200607060b0307050a080d1419020c0907300212070c050712030f1218080403350304020f040903110c010206070e040b180c030415060b04140a08 71
    0x1860041c4000304170082d07910101340c10000bc9070019441010b621509201c00c00e000955402036060b142800d0003600203002041c2d81030700810340c0c240e200440f5911460070070360340801c2428165002380c90724101a241d1100070341c0c0d00c00040811078001540382c030300c03040c51500300c1280c0102560703400001031510a100b0790f84580d401c4111440e002042201d40c800080000030003054008010041800841441c1075030000d1007804900b1210041050b070310341c0c0c820340155940c0321010681402038050840200c1e841e00e22840d030000c0c0310958299a09000304050200002c4100810310400c2c5481a541200f2100000b4a034002602c144e0f00a00d00b5a0700520381d440700d100e03100010703000741c845c08109240d660000385000808410f143c1150007090505c104250070400012101e07100300c0e00400d411075034401040c4215004240000c000300703d4410b1014480d1801c0040d4040d901a078000f00c00c45961800c00c00035540d540c13250074080c4104100030414140803600c0100080001000140210398403c44a458 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 987257715 1250 987256465 987256477
    0x1120b030a230a02060702060a1709010f060e010f05010f0c0614091905060a0b1201050708010f091e0504020d0609030201020901020d0801120816080415110a0c032006 73
    0x40c900c0b00099042500061142a100c0700040c400800b1091402d50110702035005482d0001d00a00c0c0102c1c0040d44a8065440d0400b1000280410803042c584400c0050180c1a094030944403a8904100868184542c1501038103079044001c4106015190400445001156580c52820898101da05100041c0d06010b401d10000040c403441d141402c010101505012046240412403030351420301c800040d41c00b0039500d078010340b031043c00100d0445440101e40521910503143d1000d51278501000382440c0c000400728183d40c02000340640007611000008211601c1700040401008003070982c0d50000c2180d00442e60061010308803007007116a036951a400d48182c550b0407800360b500443c1c2c170341c1d5a5034104090000c8440d81e2404560035407401c6503400300009040e002520b8140c0c00502004082064443d0908140d40949003964a80e9a43c9400c0c1058120178103032400111325048840045c0c20000b440010141c006407001040791031030b51041d0004404260a940300400009956016540e020141507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 987258965 1250 987257715 987257723
    0x1e0d0203040c0f06051608031008030304060c1b0503040e0a02070212070306050a0b0904060203090c060307080708011221090b0a080604050108030f0d0b040605120f010c050408030901120b030a 84
    0x40c54208038103c0380b20346039074100d0000c1003402e10940944401041c080d000c00e9400641c001e40d60b8460710356a445126407600a102c0c3c501c0b00000b03202c1000800d901c60904201155550003c203010481384451080311502c01401c1a0701c20710044c8400461a88000c2d000844010018504151540030400c060004050040c894002da0030801c10300c540d6005144c0d01c946040010083d0102040c0003842e07d980240014128581c080000342c48088100300e1a50110401451203031070303180c2072000610b5641c0444a40f00060000000000c0c0100310b10b201000c1c0d80c0d4000018002807410b1090050410304080841c420040c40c2200043d18640380720060144e5000f40e5110801c07403400320180815141e042c3c2c4240b4403a44108603112001015000350b540d0784600404c00f051020314640003c010b0420342c1c1116a21070503280d1203210040002a04070864011540288014408910240d589029600c00e00100d900704000b103100642c402e0b5649040300c81e03c41d40004154243e500420b01d48014100226 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 987260215 1250 987258965 987258983
    0x50d0812180d0f1b060903120203280b3a0f030e1801180513051c264008070501060e01260a031d04110913060b1e0d020304 54
    0x800389540f041e02300c1240303011980d0030341ca941000401010a210b207031030030641124100600e25074040c22500095440c040043c2130b01d9a81c54104500d0310000c0f01c0b042600f11400d0a000440c503d580304074902c1d0b10b51034210031248098031854806039130041c0d40c000003035401950000914021005050214080c1c0404110000301515070b400c00c408035030b006401c0b01d40300101100d10000140d0005400c901260540310644581c1245c60025a544140c42000d103040781d07401100303510781e0101043c503584a5001080d40000441440d26400000c00c488044010300024148001301192610002004098410a07045242c45d01c0c603154035013152541d40003101c440b102040104440003012051600580c2ca40c50640ca255400000c402d548d5020240020140840c80500301c00ea0505850b023105808005801800100007100c4003100c2a030181140500c00d074440d504160a544031803041c2001d039040c101d60346103810044c4c0b0380b0000310440c0481c0d03115003503802c004172290711005001950095200c0d200d02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 987261465 1250 987260215 987260231
    0x90607050115081b03030301061b061b0807030513020f0102030f031509010510050315040915060e24040b1c240506100e0a050d0812180d0f1b06 63
    0xf241440032910311982c2e01a101448020307103503000700071641144c050f4109011206d91686281030303103108074880600f42e03c0c9450f0800c40704441b40317843c4036400d501560301c1038590703600c046040d01110001d17a0b0200314411401e01c14401414280d075007071a0110140102c3c4c2c1814a4410a8003a59004991000d01340502030258512410464002c078090002112070751203030644a0401042030100418002c8541ca48600c0f00480d51116844000c0c555040524103a06446812115000c0c010358801c0c1040c4050450005286440c3e000710310405031948030300b894440400c0410440507001a60540340e01c9252490810541050280c001103020b1250f98031003e0804201d0101200e20058040c05040ea0f0801c1e0800c02180e46010700b4001c541c1041c18000344c10385d0103501081310300801e07070403c1d038201e0380800c500b000b44a200340250206a145ca00275441c1980d130f003103003152800c031000c130007800e40d90094150000840c00b0b00c00e9078031900e1541c508a598120110b1454040090301c0c00c003903813981c0e41d528031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 987262715 1250 987261465 987261479
    0xe040912030515220e0118033002030906060a121515080f06060102071212020708070902130f080a0314090607060b0306090601031e050f03030c120106090317090607050115 75
    0x1741ca100f441c81d110080001125038070700114401615a801810460707540b03000000d8101c1d5002080d0003c1805170030030403200604550f82d000354001d80b50b4448a2060318000340c51850180f0040c000d8403501400b14008081076603840340d00d84100100c075180152038421800c0e1040c0000104402408004001c0c03101c1c03080304812a007095000382405045410042c8184607454901c0d404400f0164400615105480120012800c08800b500225028021020001008201a000360a1551901001c112284c0e590003024130307041c22500c6611b03900d4001c52080d2012900690309402030341c03041c404940c0b504949200040c1d55910403c802c030f6555585070800401c81c10b081110640c45402c590051600d94115180c04003e44200800000354000380c100b035100304441800b1007040c4441c2801202c0e00c90910302006142c40c0c000040507091050044000520288502c01803022250444209030450810b40344103901d69000484a94200c80104403820000c0e6091140c1e4513001c5410041801c800c1c1040f0b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 987263965 1250 987262715 987262721
    0x319020112020310060c0609301805010309022e110c01120c05040911040305121c09082209150308030a0f091a070e04091203051522 58
    0x720041c4180c0c814402c00c810301c024181c503031007518071505150120380300d546880d034003400400d0300080040c180240400b15000e03c42001005480b9a0001101d20011214044501c84090f003001c04030340030903080c10406035000c1d5021a440701d001500540c2c5950b880c580c103014400004281c091200b030b48070004412240e000e105104412284030250103e1800c0e42c000910b5003824121901e00a6602d000d520403030740c001c8045030010034000d0800c5c030031044849240c500c1600644404c0c3e40d43c1c0500f00300a4032200701d5104480b4102c0d4400070030140c1c0c402d08001c0c80010094098100d500690821905140414210145410b403460800c1e4465942c204410081590501c0be2111585080e0072418000540105c0070303681d0016070f91000154500c0620001e1001d13142035030014203080b09108941a071030012101280c440d603029141c002c40e40156030309000440d941c0c0807028040c010401c0000300703802c3c42500095004440034240421104032100007038010124032440c0208407115807401504030300350b80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 987265215 1250 987263965 987263987
    0x2401050d050a21090b0f2a0f06011517010b361201060501120513170d0b0f100302130f08030705011104030b1f08030f04030b13080a1b0203190201 64
    0x406172400d0159101114801d802030600040003403000101c2541e2481407843c440100311031280c1200c0b041d5600742d1840382c42c0ca034203001d500040c980c0080c41d190154012000380c400d81060022201030b03a880d042010420760803040f601000400003c0b41c018407202e010029600d041040520b017514125070000700b0001250200d048140b60341401000c205507a002100d54940d001d00010201c4e440c0d03110640031101c6a550000242445903d100640d0b4505680c0098960183c205204010b2505440100030722480b0794610254403001210392910318910076006404103024014004107856200c844106100d034458002c440ea640c000704080c0700b13001d000d0190401c40440b10202c01c0c03600b4155100c0310386440300240410501c0b0148001c500c150411144100002e24801381a252125000200703502c1c150301c1480240d410706812404981c45501c10310078000399a80c84101d903072800c0c15001c0140d684030f21104030701d0019800801e120000d40c600703014007441c684e5801d81c400490b050510000d80300103154 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 987266465 1250 987265215 987265229
    0x20604030f050c0a0b01080109020118082a040c05130b0f0901260a0504140c0904030e030f16150801080a172106032401050d050a2109 59
    0x1090102098001c00d42100c100c6451500741c0ea502452000c4625102c800a0020b045000c03035400000c0c2034406500088600d0300c03d1742e810300001c100b114549812280b6000f1904143c1103c01c0e055440b0300740400483c0c80900030000350503036510040015048034403107151039020900000340c450310300f080d00c3ca810300902030001100c0d0078205075200c44580c5001f42901b10341840044003221034616411850383c010403e00105508103480c02410700b40280201b43c400300c2d251100046104040c400c0807800a004c1100500924496611a01c04503000166920165003600030100c6801180c0410b0141041c0400d44080505070645448000000d40321a00c4a203810070001d40010300101c0e1011905000c06600100184c580ca650080d50740c1c401c0c401c04401540a00d034810100003035825000d00b280c800c00d011810b0347e541031a003040c1d40841d01c50103030160111485440060020345003640b48198024010b10403220703000416503a148170004c4c661000a42d00a0700c0845424165010340420068840c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 987267715 1250 987266465 987266473
    0x1502030a090209360115080a03030c081e04061d240c040b22180b0f010e0918032d090a0315110a03061a09220f02040e061002 55
    0xb200c0c0c000c0301c1110078501c40901504034910440c0300b41e02c09406c0316801d80303102c00d60003120a030360710352059844a4500701140424144680c000d081401118414410314850702e01619180417030100e1201c0200081003142c1c0103030341750150091103200303501c80c41042050400504146a0300342d0b0002414154005100c80d00e01c2140c1000010312000f015102101c030b2822050b511801310164800c0201040c20301580c035144403503800148040285650180707124420420800d414100052050201c100140c0b140494800c5400320402d003806c040d10741c0d00089810030306203c8a084906c403415039008072041240301840d10004031000c8443ca49a819660200e03030010700d450031308030210741d41c09500d1102404000f1014500f010302c8501d900480110990b01c145943d44142c01e2034003070014001c5000341100ca1a08201d9201da60b030749281100d980358001410127500c480043c844400403a010700345959103544550980f40c01c04e102e80040d01c003400361403180011a02e0a00d090250b2a980114640b00310741c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 987268965 1250 987267715 987267751
    0xe07030201021903020c040c080f15031c090306020d0e07080703021516020306190605040209030a080c030d020f07121e20060109060905180309010c1502030a090209 72
    0x82c0000305407400d84510024546440c1103420164206440d00c0c18507034205003010040c6c0701803544944001e11a5503840b20f42005602d40e0150030003403440914405070154050a10b44009441350107012284404518010752420b840366900fa060f40c100101e184100354443c882203400003014010607000d00f08642c02080054910b4001605400060a03080c200d4280003500702040080e40c0c8003c0d040399000b078100c80c803508102c2d020309040250401001c80d464901100850b4900d800d0007142d03101d031030060050440301030940b5081d940b5030100f01da081040c8020802203000300403600260200009005040c3e480301c816051203c402010305000000704600014090910f070355460011482403034034640303440ca11074a07105040384001804125a080d210701d500000f42c20506420020560350030900c00d000d03e0300d608080c81030080850140055503007047c0f11850441d4821149034030310034026001e420640d4a004450310481c1d0003520700850315a2240c1030b030030035403e00000503504440101c040183c100c0e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 987270215 1250 987268965 987268967
    0x6061203050a120b04021602130e1c020309031c02150106050d050c0d090605010311030a02090a18060c05090a0e06060d02090d23060610080c0304021807120e07030201 73
    0x8481c2c0042c010600003502e990090283c80390f80102c08a0001800443d501d50380e50306600b05060050b20124031540b00c041c4020503040541c011901d820401c40700500e1100c00108014420070418032074002180b205019520b5659400c0107451103408100d407909501504106000b03007050b03010f80080c880c44544000402c40194031108480348095410000038040d1107481103507203940304a45103800418100391001e803d005540c0e0129048030b21940310368510248041c00c0c10b84807081601d010307601581100009540c0000c070b4025651600d0107001a1400c00d0403a9280d0003250b65406c40c150010794045204051410400003580240044042096051601c43d000400b1442213862210809030041001c030840d03190315402c0c50b4803503402011100b010300c40908003566031603051404000d44c460880414001d040c44085078200711140d54621120780d0355140c110860760f20260049804c0902c1d50b0004615041d06421a8000c2c031503070b038403d0a01c0c01410800c10540b024000207410b00d80014004000507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 987271465 1250 987270215 987270217
    0x7060c05030709031202070504020d0b0a05030a02090708150607080a1724011404030605040b0a020c0c0108070e03120a0905010e0d1101121103010510080601140c10060803070606120305 81
    0x320f03800030785c03d500701c0e040725412424060b5690129400c140082846000c1d014140c00501d0120303401e442e103541c0d4a9841082580e03409032608003a4004080601007125507110b41c51441d80400c43c00680c44d00c260349a07000c00c2c80c560012000b80da1005001c42d0f000303503896100c07036121004281410a07040c1070810210300001d0101d14200141c0600e403220300fa50959004116808440340101052a01c85a4070708041c8040c0508a8080f10504600c0000031084a000e2094a110b01102802808a20391070b03001500c07268400340c150818401d840088403042d0b81c0801000c104444050b022585800802201800305440c135000780307060042c1008405020785070007031061580c1d0b80280710b485c2c02c0c070021030041e070303c03856203080000100b8200203800300c2000404000310304903501942c40b07884040381d440d4216100740c0c05030f070b620340091004070a403404100040c016210510129081e500b4202d000d0142c082114400c1d4040072042d0030215007036082c4070442c0300e02c0c0c00400072140f004104c251180d40040407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 987272715 1250 987271465 987271469
    0xa170f060f12010e060a060512032502011704030320090102100c030605060a021f0908030610030e01020705070e010f0305030a11071d1b040b16020303130b07060c05030709 75
    0xd1141000c0e40041ca1009402c6079140a500c0001c1e5030140c14200a41ba019208078080d041c044d6041d809810300c8004000700315122025841030200040c3e154141c0c00501c40820070303099041103d6140c49a0840268500050140d0300ca51400590013110383c003100707030a4190200b03200c01e01c40103001d80b442e66600858805802c0129140c00991500c0401e4140c000b01001d400482c0c0080d03000c103828200e0b640014401d0301288800d90b000454410500c3c40d18113403184500014030341d407010b0000c6203140c100706084a40340129420301080e002d918a03034190072600609016100307a400751008001e00210600b03094003610588010148840c20354580541e0ba103d5000c8603010004142c41500d501101032001e140130300242240043c62500c803407140d140c08002030320800a580060f424880c1c0d496000011582207600250050342085040801c6a031903400e000d6060780c00d40802c104804e0200810800c480c06090801310098640c2c100e41818001c40d6a407045180600c0b8081040c0704d00f164102c049401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 987273965 1250 987272715 987272719
    0xc0507020f060316111c080f06040203071403060102071e030b1e010608222001032d1e240f210b0924010b0315030a080a170f060f 57
    0xa2920003100c002c0d45001014942403c020501c0c0c0c4086c143e890740000801d0141e00b240c449403000c4e41f40c803403c1100320321007510803d0106a2140208104025000195604c42ca050040d04c0203e5030b60004055a00180305103c010350805034018010050b00d603074581e80001016001011214001c00c0e10f140005060141a09006400001811000e19103000003820783c0c0071261100c0b540b680b468003004400c507044142d5503210403054404115442446052152104000c05d06100312801017085144840c00b820240b500b903c4003555240b8050f45000240040300c1d1520000e4510030024030081300c00c0150f1010004120175103400c000c03030040100b0100c150360b031102c100a00400f851106281088882100a183e0b1110404200b4240b5021810403498403800d5511403840a0012950020060074000c0505c01441400415055403c40880150044000d0101c45122801c0e80b1851100c0d00030705403e000190100c40900900002201c2140c0c11034402941407089040c040002116291443e030254 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 987275215 1250 987273965 987273977
    0x160507061d0604030609020d05010c090f0e0906070e04020d09050606041103010b040b032205010b310e01020903100b0a14010e0108060406091d010e03040602120703020309040c0507020f060316 84
    0x400c3d9a0740b07082382038055921400800482421b400050501d0707082d449007070b10005038400e0002c1c000c5d0200300030500c550303072110207451180d48e10701003963f0041804542d1500240c2c00e001008030645030344139401d05140620028981490b003041040107a0702210702c10740b0104428401040300c00f016105030b84c20b503005203c06544170741c1e810303424002c8101c810440c1c0d04c0c00720700c41c848002800010b61003241024001e0720546071007800104080004c49042c1c18050391160030500c4601411200ea0054814840e41c50000d80f80800c5100000d2270289142c06e0754000940d120b10f8140340349841903840b802000781a4540e1036800758440042d20040101c04114148101d580015011390765035840407015042c440001c00540c1175540e072079102910300d10258000c540c41e200b804601d90b41c00106a03000c8460036070003003000c51103c00c5100c0300d60308051412019844144030140203541da031301601544c06150794440380c8030ba4081c0100302c0d03506060080d450003840100706000681c003c507868424420301e54200743d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 987276465 1250 987275215 987275231
    0x170718090305070f080715050709030314041e090c020a0803010302010806040e0d02010b01030e2e09060f0228090902070c080105131a1303080c160507061d06040306 72
    0x559140c40f501c00d00400c14224032006004010710350006c0c120f038501507580c0b4170721507030300c24400f4040390020f44559005c50700c412820400203100b0800c06402c2c04288080509082e40c070501d0703001508d010764844d0241e48105100b485035503880d100d00190301c006803000304080c0c8280d0b01c44c41e41c140310601000e810042d1042c0003031450348981d08100104155071040301c0c036504900c24024001c1410710400e600003420080702914800001400305000030300f40f90003022131074140e0000b20881858601000c1801e80340d0b02e0140116030284a00c142150b505a005692005071810340700327800301c21848070f142150030091011003469129041106580c031440c001640d4030300504060010380c000d503018164541c2800c04109030541e04081402c0042c0c4107910074183d0910541c1c511400b08002c40308c0c144140245903207140070902c07403442c0541107807120140707601d040c4455460702c0f10b0041403602626940c0c40f9807020404141c2c8021100500e00c180500d0141c9035200d0b10009046200e40d1102618943d19203011b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 987277715 1250 987276465 987276467
    0x1d0105180f0a06050c010c081608060d0c08011505032b090503100b0109150507080703090e1305061e010311040b06040905090606060403030c020111251707180903 71
    0x2850503020300070100344590b50341d04401040e55000703d08045c540d508001402c11414066415a03000d240c007101c1015903044e44150850b111040203002561005180b840c25002c204108a400041c1051000100749012100307241c220252440d40118040e50040030311407813100c80d80350781e4280322207400c2c00c0c100c2d181c40c03115003190a8142500916451302a851400340412016440f22000d41001c0e20384201c41a91a10000c1070681c02c1007814000c0381c004c0025400141d2b80d80000c14015200742002c14035292943c99089441d00116140051001000c00080a1080c100b1825030301800e0702d00c458800703030025100c00c681c07a003061200a001c0071080a420019075510b8200c1c416072076019040d6a00c03280d540300341101404056801c0c28090042c0b90100d41d1a091140807981a207400d5100c210b80c401c016801100d0003a038094100c401801050103018409007a0011a81c1c615020a50b04002500700640b090181480301c2c0365000c40c2e40444001c11005421442d0703504081c030400c2c4000b40d04407650070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 987278965 1250 987277715 987277729
    0xb0c0a0209060f120c040f0e0601350a030305180a0201120e0d02060a0612020d0822080a0201020705090f011214060703060305010c030b1e01110d030506011d010518 72
    0x20b21150f0100b00c00c00c00c910014030026105d2401304c805c45090000c503150390f00c41011a0510583d40e101500882c005011041e55921406104041c0c140c5070708882503c0d003031a90b140300c0c10805441160300801c9110307061507854007d041d08008111000d000240c950304c003180d0780e201d11150082c10300c440007031410142d5041d64405070183c0c80400035a5500180a84003d4403400c04940005000f458070401285c421044140003540c00d9001e401c2d0142011282c4406806400022240c0e07241c249d0a004c3c2c1c80700e044c4407407002c0c00400d031500003070103880c0039817002a040100d240c0025018443c2203003040141c900003114641103e40f2000024031004a0f414081c518183c1050715500500c41d00e0184113a90398190302004c01c480c0107900030051880b0f00d07201113081e034440980c0207a000c220040380c40c40391050f0700d80340343d5a10814102a91915041821b89062a049181800109948804004141d43c2141d05a00301c414142011003541c08000000b803c140140c031710f002c0d41d60001204800607500d8442c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 987280215 1250 987278965 987278989
    0x230a180b03011104120213050c0901030203060f041e060e0405070e130b1501090801150620070909020f01090b0d050a09080313030207090b0303040b0f04030c12020a0b0c0a020906 78
    0x1d16070513500c0d41c0701c042c804001d01110004a01900c2003503016070f03400c003492160a00407011a2103551600c0783c10001100603401c041c00c03456000d04c1c0c030f000410b503079502e9126010b1441c03046090000001411a00d00c012262154020b02000c41100100700c006040406d158090b0740744c200441480ba1070703415402440e030348903003402420076100f1002d1200b0824071b507501c4403100000340e0f81c80c004c072916a07118900340c990356002c890b0a408a000103000341030007000780c9400d09901c00800c0729a80115904640340681d01c0d8044462141d031b0362500c6081d410480c0c2c003507150401c2130030070782c0f005072810000d1445031240540380c29100da56000451400f03142a000000c9450b04860610b0312401c010483e0000440c11550480140c800c01e0800600040e15010380c1c03070310740802006541083e1a2241c042601e5001c0d08144c0b2111008200100026001a580320094100394034034012003400d40c814000e0214040e0003060fa0f90805201040800400080f04002140c1c10740d0701d0049501c400022811400b002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 987281465 1250 987280215 987280241
    0x20703030b06070c080129010c02030f01020a030204051c030801060c02040f060312030b0901050105090d06180c0807080102041a07030c050d05090306060d02010807050f0403020604230a180b0301 85
    0x801d50140311030b103041395003550541402000320707003090450383c60b0b56021608000da14603841801034203190300400420070780a0000e419100300190000d0310b2401ca86c400301d41d41000c2980800c040c000c50a01c0341941e82419070110040142d00c815403805003201105204510800c0500c252980842d216074000407405a5120760a0007030766184d00c0d15026021200102c84006880c2410030a003500c0d00d089014102c41c410303140e06182c02d13041c0c1c050200603c10880e041c0d54294441080303c00707010b1101043e00c0e1060040546658050a11448504214007940510341d2030380144410310494400c4040d04150884080c4410355541c03043c40c0907100e034007030030002030114012519520f003602d402c48020702120b042241510815035914040000e5007000520290025800d00f0016046900480082a0400c0b0f1680c03800e040c45d582e9400075640750700507001040810b485100350f0010034513150381c040d01034904441a042448c14060010300c05807402480f04412611042120302540f420351117140c0348070707017 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 987282715 1250 987281465 987281467
    0x705060708040314062202030102090306010b1c050705030c07020d06050a0516090b0306090612120d0b031c050d0b120d08070219061512060e010615080a020703030b06 73
    0x140781498181a0050303c0b040da0012098511080e18900110b4098400e0904e4018040c40340c8652070003071002506030004980566003000500b1165400b0002c0038000c28990051642d00c600c0645021041e1380c0320300780c07150714505000c1404969034200068a500c00b07441000b040d210000790001800840185001500c0310380b03003c080c082c5000090300f00c03130b01c2018100482c2001d50129801111024480d1061140100c014404034500f131030300d2081c1a80241c3c00500c14603d60700c41010290074205020603041d40c2c144c00040000c10007025004100c200700044000c0c00c10036220b2541d025248005e116010f08000001840210701c810545c40043c800d031026050700558882c0c045220f070f4454404542070b020921000001325194400248a01081c103ca000c42240e0002075a420000c2c00750f40411040f6203205000c0403507003000074610a00b800c4d0041d04040b40e01c51803880b080342107400b01d4100c0c1003060700110b410100d040e044404d00c0e40080d0fa00d0750040c1d60f107043d410210001d111081d041540450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 987283965 1250 987282715 987282727
    0x1517092121070315031703060406080601140f0d1211010f11090a051504030b1005040f0b0109060203040b0f090f0325050405100e0a15260601030b010b0c070506 70
    0xc0060400b44111240e4030304004019072100e540d141c414040c44020103000505110380400c042840c091034110300042c1020441c41d445050342400d12200341c0181c82058441d048180b5030f4a00101000725a00702540c2040b000744450b251526141d883e0900382c2c041c4660101d00c80138208096000c0311503042011020080030301307003001c2c2e07910030343c040401c0724881c02d03440c0000320300c6d840c0480d000041e003601429854a054516510f0203a9003200408803054100d21400010300c2c1c0c0c4031030140000c06c40e01224006a440c145500140034882d640c2c02c44001c56000b0303c07040c4100424801110742c17130442c0c9441c990303d0f2500100061000c100000c03032550580104945210600030f0610305448060440d61075a203155100c406000441d02e04962880044144e0102005510080110030303130010b0028501188171100c01c484404194070f2544024240020300c400b10a401c1761841c0c504002c00001d401810080d495034031001c2091106010b00d55102400260f08503540008001e568000d080180034591912 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 987285215 1250 987283965 987284017
    0x61b05070519090f0b061b012c0d030506210f0a261c09030302090d080c25090e0a170d0f0e0703030e12010615170921 52
    0xc4840d204a0fa080f5051480000c0180101d001d22800303108003508035410303e04003811038a03410011081030b001d103559490f0441c40205000c0d00000300005c1d0b1807030007070a030980c00880702d14144021215100309071420b001d008403a80c0d031803200140030304aa4031401404501409070b908009401d04944128801e41045404000c01d4603440c129886405203074551818101886140920952004075181c00a0408980b0f172002c082c1d001003080760091400500b0160024041400f0180d8120240c03090b10011070000d510150412044501c5502004c003101054406070a00f601d01c00c05004001ca60ba488400740034400303034204008200720f0f4000d0b58203040f103800c421820200754001402c1c0100582810300300344805140740030301852141190b0040c40100e00e1a10202c907611100c01001d0780c08a500328050300444800d00a140245c4500c0d07026060746120214050030070485004020100e407124410030180040200d407005112a03410108000004d0300c28101e02c5a120313010741c020302c01c101c100e0440140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 987286465 1250 987285215 987285259
    0x121513020414100207080303063c2418030c030a080706060b0c0a060b0a080706080a15230103020f281805120111070525061b050705 58
    0x1510140c1d070352000070b29030f840100d071102024040d0b00e0071640b04002040303442c24802a081003c06403000a10700e110000d0644d6a0500d4407090b0070200d41700b07605d01700361140c50300030b40c1481d811040401590002c400a6088883c5001d1081078010300b05d1600480842c6480611030910080ac000301500e0712070ba014a030405442d0000503040d5a00c500d403840c085a820300900c1241e500c882c2c0d003401880d40510301c2e07440030040c00d40711034001e401480e888800504000c0030000c90000c2e03c040c0d01c880605251058007078007201d0480100e107150030300300c402c00c1200c5030040c980107400400c0200d100007542d43e04001a00644a00030541000c2000000c0980300d0801c80300300030144010420310304160b40c01c80b420444d0010010035030084481c414030310401243c503040b4181043c03002600000328500c034141a80a0158005400c1601d43d43c215460100c0340040e1001045000b24203040d0b2070a00c6414100010805000f1852807106041d14049480074400200315075001024001c0c00e500b504030f1181c02d04590 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 987287715 1250 987286465 987286499
    0xf06040f030807140a08030a092103020a081f1502070308070c03050c100f0c0507030204050106030605090c0a0e090a020d0603080406110c1f090e0c090f0102031215130204 75
    0x822113203020a101c1140041080c4003110703040040d83d82140c0781c01c40200010904200102d82034000c0c07058001c00503c2ea03003440040c002240d200140c94900c90b4401a102c0c141c02441410107001008103014001010b1310030009542a1180d1102076003a030000c141d02d0412203410190002c2e4001c80d0b89801c00001c400c81c0400d1728440d405075886440071005000300d850102010401040c207142c1030038080c40c803c61045481c1c0f4050012180203035582d401280031600203070002d00019403a03030300a204030300381045600c1c1c002d80d0000704203141442d4107000401481d44407075818070880503480071400c229071a8054503441050078208100040c0c0e00c1c68030000301d600510500d0b0101e20020075a04005a01091801d0b0740100540314510690221003002180c0a540054400340000c1c10b0700030030f60061503ca410b2040901002460b44c0d580c4070780401c00100e5402295a045600412214211580020788036406c501520301c280b440000c904001401664220701e0745400a2020800040d207040340f900d5461 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 987288965 1250 987287715 987287723
    0x60e0f1f06060302030714090114190e12070b0310051e090105040603050a06020334090e151e0d03020a02120c060412060603140d020115140f06040f030807 68
    0x801d41d02c09058090303000482c4c01d00c0102d4070000240c80d010f0007a00003010b800d6814503004040000a00c0496100e41109091501aa11401042c132056401215a1030762000072120708040c004c8504816542d2401406003007050200440402c941808007054040a420f0017001c0c04008a00d040b80118003891985a081c81803044500004441c142442420b0a0341e42240c0903000c1c4078190b841c0c602c046d500140410b44007940e01c02c007170043c03d0640f410175421008244c1d02c9203066441c610004000c44403c1d0055030400c000c09080c00740c040e20010841413003410a5807908203941400c0460f6100c40d02036044950825044041c1504140c0e0200303880239030920842c0d07081600944485c8640da0348880342e81d02a0800801c001c10702c151200d58580a001034498440030a48681701d40c2c803600c1084040030003050641c00000844c0489070280900c0c00544903d01c46190041d190500320580030404000c6140654810791860300309072924401c0f01c001d08111980f503956240d9a107040520342c0c0c4a030034141c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 987290215 1250 987288965 987288971
    0x12090f15050c2d12010e090d0e1011121b0115061b0c03150606080603210c010f0204120510051302090603150405010f061202060304060e0f1f 62
    0x50318442c030041507640e060102c262400301200da1080c102e4500d03032909503100c100031091114000240210312403a0280c642080c442c4203a051410040749840c801646903c20b00200852090042d1200d00585d882c00c48649014046280006c03c000c0c10240244d40824a01100281002d42c40c201c1d40c078031004001e2407000030480c141006070300185035116030040c040041c080c581c02d0300710046039507140c1e084c89014100701401c1d1952540d440e10140d98001c0d030044515207901080113081c0d00140e4450348a5030039006400b2145441c22140665502101143c4080c0030101354140d0b200c10035400500c0000c084101190b885840d007402c040c258044850441c1c1e03078400c011346d141c4d1380790700f50241c1801070b140800840454000b56081004c010402801c0c02d8051040c0305054042454042d10140598041c0c00001500c10079204884142d5150340c0000721295016905440140c41d88411658000c2d0030060029007034403841e060904000d40c40d600c411280c03188151051841050403d09003004480c3da03410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 987291465 1250 987290215 987290221
    0x41a010f090e0106110f0a0b01030b150a0b160c080c10020a11042703030510080a050c060703021e0c03060f270c04060f080118080a12090f1505 63
    0xc884400d0140280b00034600103000421080b40100981101c010110f03054840148a08962a280034500ba50a0311442c40036170042003403040142c2e2103600100701c01203a41c507a007894404102000300d02e1140f4800000c0025a10f41d10040e0040c1c800789855009502c00d602641d1003038202d80e0380c41244001c6104028281d06145118000554503890b25030140c60305036030f000c418003048000c10315980140200140c0c0d2a40008110000980c040c3c0d441c0300c0e0b20005461b04021040348000d204580151b907080d0702c00102140400d83c001424050480101c800326529402823404a007091000e100750815a8600401c4110708000480c81e41c02c01c1c03101ba41126695603440300c4181c01c8034002d45043d280c940c0c1031a00052121400f080449000e0411012a6840c5802c0d03804107003100d5a81c0d00c818072501107400140001c500a0180c8180341c46c2098030099000d00c1511100001c1c4140107220090240e9107104588000c1203400c07821229800c105040f04c0b403100707410b100c4a516110246101d400c1d19003000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 987292715 1250 987291465 987291467
    0xa080303060d0308040807080415020c1207030602091f0206040312020a080c0a021507050d0b090903040b0310120303090203060702060106020705040914070b04051306061418041a010f 80
    0x50300d1048000811001d00c0303203040d49003528031903005030050701d102104115080210710050020300040040030b0fa5a09440b190203030080c102545000d10707a1241001c1c2c0d10314448040300081c0792060300c0d0481e40060741d03458100d0015070702d005107844032240355211a0720b02c07a0031034022528134812802034480e005176010900041d0124422442050302154060002c02c5043d0b0741100a0500d0900c2c1740101d4070081c2082d00300313410006040342c40c140000c200040001507201280550b00082c0000d03118444c0906281c0b801035101d00881c0540c2060000100000764400c100c5c1e403030a0b0040c054070031041059012814000c000d4400460240c1c000d216901c007160703051f440010000c0c12100e865000c2d16200c0e05200400001d07002002c3c2c180d0b0309018545041070124004c3c012030004080c0940855a0b0700e01c0c0106101d003185060b0341d19090103103008420441f09805c442d4152800c014403a1680d5203070460b091740b40703050500d0040300350801d01d024030b44041e0b81c40b14140362170340a1003601c81c810f94152501c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 987293965 1250 987292715 987292717
    0x1050f0f01050a0b0a0e0901083409050408160303020d06140907030c0507050f0703020a0803030124090b120411040204060518180f011d010302030c0d03030b19050a0803 74
    0x200b0a50003c0c0c11180402c5102c400314098480994645841c5040601503000560303040003e03003181c141508910346c4600c8081401c0b102048621244244000b5142d042685a1000380b8500c0340400c05030301c1c3d0001404001000c400c075901081003c125944220090074010001c8d00b05480c00c10103280b034103d000c100c21030700a0300702c125030710014940a001c1c1d0f104401100504950341c610011300905001e4100090400e00c003880d90101c3c024000c001c624a90f00400c10040c160750300c001401e070803c00040c0500010310104094481c4801c103107825601018200300c07000300a0f58000d0910740e01c0410081c04000009050703500442c09803000070b140d1402d400800040b8800c41c800d000201e2010001106004c90000c511030301100000c020402c1072422102c48020954225162181c01941f440184070701000e042e5808215003c241c4020704541c11a40480d41d03640409103050300c2400c060271900d04040c801e402c40b500c03c00c0d020b01000c002072501c150560182c0001c0c001c151150706a0880451017201c004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 987295215 1250 987293965 987293969
    0x4020303212d060d020a09020a1d061303121e0f1103030c040306090512070b160c0f03030e070b0d090309080a23010209090c0c3c190501050f0f01 64
    0x522600b001e61a103504104000d156004104d0b0005060300000803d0015803025110005450b141c082507030641703480310308003500c0310403400e44148014420744080e880c0c0c00355224107495010041400c0d0304d09001003034903610300a102a140a400d8140d5203881e06511001d0010078080790f8807540510200d14240c1d940301c0c002103135622000d41d010701040010074225040038504500420680c0c20750144101e180206500024003618896459018004103c11101903114101d001e803816001044041daa641401401c4001c003500b00340e2246001820b040082c81010300500c003141d90a0740e250110503014000d0404040e0a90118044040005444101042801055900c4009c03010000400340799241010a0484415015035080c0081e0308542c880d049113600650306a140c007a223070b40c0c45040080c50403a01c0703040c10080c00c04d50180044068021420310515020168070300c10200340f050141d42c43c000c542001503d94a8601140506110040d80018040c030f84103002740748980d84854a5001c0c080080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 987296465 1250 987295215 987295291
    0x3080a0c210201052202030705040b030c092a0316030207032105060a14010815150409020a0e01020706090b0d1e0f18030c0b0402030321 60
    0x10042009000c0c42200d00c1a0854850000007112035032420840002030010030015016030b5499041c0070100d0340203201160003030b8801c0c15045405905a021948440d40d62040328090ba4440d030804001740e6061058241c1c0041c090203406d4107290170043c1c119603407240e614050075091090207241c10344140108a80c4500d401d055242810203040300304030006c7d0f0003000c0c103070f04000e1300801c04e164016048181c2d60740340ca0702440c0811103003000b1003000090708881e44100800d07079103640d07d40a00d0360010000c0398444c0020900c181150489004244070040141c5003101100d8001001718110b82c1e00c0c1d02410580d05255150004080d4800044e0f03928005405582c01140c890441001885030b14401045002c01c5400041100141484000004404040100110740e2507907001034401e8800d01c692105096075400381170052ba6692000b50034a0508507014000e051500005019902c040044400d101030b2404180309049007014010402d10003520000c0606003a083c100030741180107003800580140c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 987297715 1250 987296465 987296467
    0x302090c0d05092a3015010824070e0f0d03050d0c030b0102060406020706141602100b010e060304080c06091b01210e0133050a1a0c010b1903050d090308 67
    0x213030400004459030700440c110316020005c80003419a0f0014040020071403015500d8480e1541004036035403d00e1440800c0c0c0741148642690158a082c00120080d004011401c0511800c00e51001048200b52003a13511034000803940142c800b0103600c400104021591454100188860b154040302560030079004c4030b00591102000c5008590349034010403050384982c031300080540b4001c4140c40e40034422544000c00c600d6a2081030951074040c894807202106400c5d00700031004642d00041e200c40041142c8500038030300880054100b010041c00c44036940e51600403201c0c1443c100309041d81e240844400c0d04c4400e0700060420603994001c003807008020340d402e008215240400a0b20900a04055510846641d00c4105001030701c0140480c400c801d11241c036040d00c840f159400d0201c0783c2c8219a20581c050351484200b00070b000c01c54a040d02030825040c80c4103544500c0000244d0140c802401850781c01a101e100e4010358690750036013031040764400c00070380701c02200c4031405483c410704500c006468040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 987298965 1250 987297715 987297739
    0x901180506091317120c0405040e15010b0d090c0b19031404080306220516020c060928090c0f031817120103050708061f0302090c0d05092a 61
    0x503102e40401a45414130b040b19041c811a030340c0106642000b80c0da03a0b0801e090001d014445410540100541024400c0060145120f50714819150404c144034048512802240042c08180d203030b00a015400d8010802d034040a4032850690059441080c0102d10001c0d05842c545015000c1d014100c0003881c00c2c05000d1041d5a985c403501c200341c1c0b0080c1841c4e401490a1111080d032036101c4070007012003c281d040020b852401842940c1c0c1072100c132000c0b105640c840403d10600c0d55510301200c6032102c00f92440c030030400710307601d5036803c049043c2200442c101a41001151140f000d92040408103500d40d01d1111002001c0d03015800c80d141d1590713600d11605020621400714043e0121255841420080f0b289422003524070001c102c40213801c11a00c54102d40b20402000c0c1c0c0400c80540c03c103080d5080c111410040c2c1e141c0201c02000c909c17000740500f010340c0000d04d04400200c240c951040b074a40c1c081c0107601c3c1808501d0b40302c242c1040c650a4220350704c4500303031518542e0103104660000117004205411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 987300215 1250 987298965 987298973
    0x3040f0f060516140f1605010c0507050d060b0d060b180c1602031905030c0d020d02030d15170d02071a04050918161a0a05090d020f09011805060913 65
    0x890800301c1551110245030302c1e58a4003004200c2c007030010038224040c200c445043c010501e031b112520b40c445810030208a1904011840100d2a0700c2100c0b01164003250182c91071508801600c0d00822080e8484403400c0003005024042c2c01000c05200308072821030171010151f181c507024110503944421526810f00008100507c13820312414418002411200300d070312407110408204c00080b808031065000403814598000040100a604058500103001165070b6104025900c1c01400e01c92041c0540301c0e8442c5a00241c007105d190301404080d01c24441d200101ea105540e40e03886030302c03a00010710940d0000241a8440d000424055558006c0f0300e103802e150404102d40100e01a02c80058662241280303149900100507298800c0300c410309540f0980d1a080c614002200d0000840c511440d0810a65031150303400f00440d13241440c2112081c221903402c0c0082544a4100003246811149040c0040f4050012008412021089800611250755a041030043c03030f09043d1019107002c280c080300300e000a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 987301465 1250 987300215 987300247
    0x403020105070c1505070219050907081b0703050c0607030e0d0e041d0604020108070804030206040f15060303032c2107080412021e0d03080910050903040f0f0605 71
    0xd0f8010185440026200c080010080e0600c10054012560006500045081c11510594400050558201d080d8179100100302940401031207802000110b200060040c031000503402c1003580024102520303400170340b0740a4050352180041072441e05ca8100010f080500c82d00410b500d801d00c9101070421032003c0e5400303070b4540c60041c8505500a0307e802e001d0380204800341109681440100090000d81010300014203601800342c108020010309404001c040b0783c0014440380c115034071041003042072032103050141c5481c081c03449120915080000000600d036042d001914000d2280003281c1801080386001e02c124101c0704064000c64110302a4500711424a1032041d100420740c405640c903090840d0354440840c1d1098100350301c0e4030b910780345100650901d80903000460b00d0000000e201a00c0c641d00150400121401c004d0400008200040710071a00b44060307860800340380028061810660340703050b100c0c0c01900600200189520000502d0010309405108442080c1c44a030303d8050220121004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 987302715 1250 987301465 987301477
    0x1b030f1009330e011409030409050606120c03190c080106030b0a032316060503010303090f030503071218090504020310050c0d05271b10090b030a150f030b1b0403020105 74
    0x140c3d55a130300d0441466680d2905d0144110401c101840d0f8650030b04c60080c1c1203803000b502d000c0c051391091120f400300c8a9401c441e20341200e180d620030368881d036841e160b074100f608070301220300070003421700c20900001c40c2c020400c503050317a256032010304c9406640340a0003a220001e10000c0c1c050354101c0038886a4541040c104a000455402030300d1007000c0d201d0300083e4168803944081c1c00a580080104107144d4403640900c0a03112590503640303106d2950b1180c86e5070b4003503040042d103030055010300c1c81c0b0f200e4011900800580c615115070000c00c0c1d0b546280387c005000031035007640280101d05a40640709500e125191051141c4001541042001e00d807070f900030315005101d80720140d10404440810041da410300e00246403003600230f106442c0030b801c0070850301111020103405008140c19003250740c1c1c1c114680c08281c400c5c000c0d0103a1a550f801c0c40f140301402d032151281c420104010300104606075038a805000f6240200d0000e802529194403007043c5400710034651140040a00c414401980710b5401029 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 987303965 1250 987302715 987302741
    0x17120a1805060315090402120708100e0c010c0219030b09010204030b06030c101b021f18030b01090f090c03060605032b2f0c01030605060c1b030f100933 67
    0x1408c85d1201041490700c4001c1c1c02c4411194010340722040c526066010303000d0528507580c0034203040e001c41c2002802d41118204000e209003c0150b1014005400d2042da078001c40e00022801032170700340055083e000350700c280415110394000744000703600c6040002380081c4882000d80411016140b1074021246054100c00c0507000340003c0e1620720140e510150031542007800c3c043c8541040d0120a405071803c8000114042036040306442013012400c11a92141162100c1c1070100d04105003c04420042401c910300403d01800c4140100a101140c2e10503021b0714015011070f41c0348403091421062071481000f01d40400007410564205062085d19a9003180c401d50010307041310705403003000407400140000e907000380c2c3d4402442031480b5a072500138100141010b440c040c2c58915200545516124600809400c80305040d031084007540f020081c00004035004000c2e03801c14414184148080c0150743c41c00e541d0100c4595100c4160212407050803807a4034207090b60044580260074590180801c0d0340341c51 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 987305215 1250 987303965 987303979
    0xd0c090612023109090302150f0402030d0f02030c030c100605090c03010909020d02030321130c120f02060a0513090606050d0c090f0b03091002030105030717120a1805060315090402 79
    0x244c040c1c110300500f03100c148240c02401003540007680048850f1002800f1406040c8510203101c00b50310041340f601c080390103038580a604403001200c20b030f15500c510030044406120001b810340035801c0100f405841c9100074041800b00c00c0e6218200000710f00103070f45002c2c3c04103003000100071041c040d81c0100c10007807000e000398009040c00d40019040d40c011002c00d0610004119038030b403c0402a1003855400448081045c003c003495440d90550001140540c600003000e04590809000d010700719001c81070703802040280e40c0e4010440081c107641140f009a84540b02a44000c140d600c124010441910300580d2001d041c003040b0f001140240c9440d04500c4103000f02040c02090007510100e0520103003000456040d683c4c107100b51240d141075510410414068414030040c021030740c3c04140b08045130061700600700340d0f80001c81160704041064001002841d070008403201344c1600401e80020356070200e030310301101982c3d40007400000d2104885224140300b152420102920b800180c25130440d001070151 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 987306465 1250 987305215 987305219
    0x5031c09080f0a0f110a021504090905160b040303080601050304020103141e16090e0a2d14160309050a0b09010e0d1b0312020d0c0906120231 62
    0x1d01000d80c046200c03000100c0c80011080042c603001804065241400d1604040c0040c88840c2c072502e500416074024440c2c030002d818546000c1d0301030203460103030020781810405201c1c946413590b0341c2c00e41421200f0a58111075070000d00800d0b02001d40742160f4058685000300e80c1d48400440e4241c2c4000c0c802c0f81455503031000c407200030312181c024612402400eaa03846481c201607a00c070301030381d00c01010b108010381a40e0800c01e5040e40110510200d421404101c20161144080da01c041e101540714100e4001d0048140c1c5401424048800000358042004102903400f04a810b40c1c14070b03088441c8980c50013105403d101d140d1288d400302c0100c0d400741d81912003005040e07580350241402039902c0542c0380c1d100c24540f8031080c4240002c500909203070500d841000d8041460010514541002a06000c10302c51030f44030240d4942c040b02d041034441e1504210702c413802440038200c540d1502560000410280840000e02800e108850402c4980542115112040400317403031040030200041c641551001c0c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 987307715 1250 987306465 987306473
    0x90f3e1b0a050609011a060901030209031e2103040c1401110f07030c12030e041d011b180803070f0311060a0207110114030a050406060b0a031506050705031c09 70
    0x9814841e4854005002141080c0302c000d17003035a8041c101e8810f800854080b8100503611003007103464406081c200075032100d41010000382010030300f40c0c07514007844804030081d00c207080105064818907100d8a003400280c1750503194103c0d42c0800c1b100206100e0a0110030f100148003c0402140400140b5003034403400c25640c0d68504040c50a05102803039404802d0030b0040014250202e4040d10f03190880d2135142c02c058400401c0321402980e80c60140d952200da0380704200700f0000ca58603400b0a031009010303017507041c030f0205c00d6120102d0320040041c442340464006041003120100c21180f40d04015401c0c0b03d034a45864000700d010040880078480c2903110760103600001d01c1824401c043e62200107844110700d09024469a0b0051b450904001d91410040d402e10319400641703401007429640025655a285411b100410407034004441e03081e00030400404403907154014100c00c1d041c80c01e81c403000702d41c0c4107000c0e04ca6024854000f81650428042d243c0c5070480900a8072558500300d0000c140400c1d40d4079 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 987308965 1250 987307715 987307723
    0xc070627111306060509040c05071518061d060f0106021f020d060b07410708030f09012a02010f0e040501030311150609061306090f3e1b 60
    0x100440c003161010801c0d846c145440d20446d480329849080c5140b410840c0d6860040f044841540394031420780c1c440c000803076240d1154201c414158024810001c1c103c600007440e1051014400f41d82c12840f40030001100707003c0c2d04c840365048036241d400601d11103021000150740c200c8240b4048080c00d501780200f42c540c40c018099840100b64004503140d81e4910303810000407024550403004031411508590303400e14400c2d0b284d0b110752204500c80c0d46030f4190020702c581c0c1c00c1070404d521411301c5100202d441c0c0301c4a0300c2040201030f5000c0980ba24511303d5485903071980301544181c401c00084041d06002c40c0994045c81c0c519039000a00e02e030000481c0f0185000a04448080c1c0040d0b0004054889080a0325803c001190210758004401d60561070b00c0800245031450080c0480c4c040c0140418880445441b9041a409090984018880c480e0800307250030040505000c0c0141020112810f00d140e500345800a440383d507520b4100c1c15540340c00320f0742e011583d8070104c244d49041e00f20540600010801b44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 987310215 1250 987308965 987308969
    0xa05130f11070b0106090b0a02030306010c1533051e01110714100206060f040b04020705100207060b1e010e1c0b0702010606090605090405060f090c070627111306 71
    0x35583c090a0f504091004092600c0d40d00080711500040100203041c079000410340303900103400d18208014040c2c5141020100c401c2c501d00b0304000d42030000b00c030620b03c01d100e50344500c1519a503000318400d4521042c0f800c6081c180c424690070010581105c40340d64001c540c501490441070400321307070903910a80d03100e10f000d8080e40070407502142d01c5ca42d44050b2030004820500e6a2040c8018800b6040c008002064814900e125512407540c440c4074001c0c644964041da03c0e20b54000c001d9072802c101411300b030070107948500421540c907850a5007050703041c0340041c1d84258414a40c070701140070410b001c005460002c0500b207100d6000041c65803024440ca80c5124440f1014401c0010000e5400c10f203030007038290380c0550080b206001d02d6001c10301c40b2076400000e6030a00d020440b07020886d600c84401040c03d54030710a100b43d8111408008000d50000c1c0e0200070503d40344150410000e0b03054040840300210b18003100550ba4250180420000c43c0c030841140802d200e0040c0440c941d17482d000c401c0401c0b1940d41d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 987311465 1250 987310215 987310223
    0x70c08010902101706010f0306150e031504080706020309120d0b0108010e07020c300d0906030903090302090403020f030c0c04051e0f090f070603020405040b0a05130f1107 75
    0x4401803000c60601180804907080903040000084c540c0560442582100a11403410440454020344c1e1041c803d800c46401042c00142d40c0c1e0074a280310f000205812103134000a0b02901c02c4c46101c0456402054640348920781082d0028244861a941c82020b9440540005041d101c0da04035614084102d9005101e100580800042d0006500c0000342172648140d0100d020a616042005159600460203000324402140e100d840c3c0310034484840d1070b07000002c10720300400d4500d000383c0c101c03000009048001c0d0752064440030300c80d0740c0d078410840540d40c003108000c00142d84901e081005003400510b007a04140b20740151031030401c1121180d451034008a1400c1c04075031003060306244508180c031849801042850801c1042c8040c043c08034901d103805481000e11405000006007800f500f80480003146500006440c0c0d421b54071040100690041d004a520039460700d2a08000d03868a900b2040858501402d1101481c00d0464035500404503d840126401d40740d40415114400c1280100101d600c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 987312715 1250 987311465 987311471
    0x72603061306050306130f1b0602060115091502030c010504111309020f010e01110a0b01030624032604090606030c0503090304031101140c010b04110403021302030606070c0801 77
    0x1401c001110004442507100720b03140040921244d140070a10541c0888151403203500044a4540b02525039020300b40641409580c03d0648140d03100401da03030046401d16400c030b51090341c85842d081401e94074002020007040055a00304109450031509180707540c9240141ea045c00040411142502c40840f1704540b1851000954841d03803a0115010902400c941d008000303030300c0d10394081002d80e48a1403165050120300c04090307910303a03c6014039224aa1091080c0c552044540c5001080c0d82c4081c04110b03282c2c2d0030300d10182c200300010303048807004800c9104042952860f54968160440c1c5c1644141810030405018800303071040200240001d00c400080000c555152a6000703003210780400e03016040250800038401040c0300081585c040d01d401030048511103803c0c100680e070004121007072940c02c017404650001c005d941903208100c2c10f0000d907410300c00003101c00111601417155000c001e52120359101c030704038205500e030701540d4401c0c8080c0c5600d00c0d01c0d5150f11400300504069003c1096691 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 987313965 1250 987312715 987312721
    0x804030803070e1002160902030903040f030609050d030c020a140709180c0f1d09010b0d08090a06050a09030803060d06241a03040303020702030a0804060e120a0302070b072603 77
    0x400c06558041380c14103201405080301100090540c0c0c110303034400e055031690084080340388c884c414000c46000300703001c480f00c80007c1e91b07924044010b0466800709440074000d41c02e0242c98a8040e000e10381c0b40d0541c0d40e01070800c40009681d040c0c841c0710f5650100c3c905114890010841c21030f40e200310306540455900c004026803ca1800b10b140ca20340f0303004801c0da511a904204030f107480a00b008245a1418980d0140d540c2d11000c0f494018914400819441034411248a05001c84280240f942c01d805403200301c0340783e4913200243da0314801c000500c00020103008040010071441c0000d160088002480100d0010460301c0d200c0544088054107d2010351454241e100304850041210082940c0140c00e0403152500c18802c04c00d00000700301070249038000a0050440d80c0500250100d00c1e40101103070340320368680c40002d00381c51000700c41038040c81f0200b00c08962208000307000c40301d0070360607801044128109089446103402c4070404613503202120f05010303c013040c1c101c0b4510121408007013003074480c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 987315215 1250 987313965 987313969
    0x30c0a050309100c020307150b06070807150c0504170715110c06120709170a02120109020a0902040f140a03140a15270b040308070c0605040b07020111250804030803070e 74
    0x15008c207250000c1c41d40740202c40607042e141c10060300c4c10346030040d80198a03a005414400000001c910890100e20300d41400b1886407074110f0301038410386510000001c10903d103c0342c0c19070f50300381c3c0b40150308031600c07140522002c0904c0781d8450100100610103840801c0c501e500410b580d600315030690101000c0d40c400700310645a004520034000c0c00b9400e04540c500480301500c03a150300c800302029010380c02ca02458194014250400c0c0c600e0341c0c0c0a450210215039030a0014000d4015000740f05c520514120006501c1088806040d1419230051900c4011451031741ca10302c41c0c0f41c02c47e940b80b0903030003820108000b2950341c2c81c1003003548510750408200c51500b20040042c0181c50282000300c18004148074010810105400303502a525080c01101603c1d030307401c15034118051700e42c0106082d0a00301000104182c031603089010740010740080c004110a105000701c58040d1041c140500b921011424140003648524101c043e030044d808c96140a403a40c86440b040c2d40203e031240041405420411418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 987316465 1250 987315215 987315233
    0x7030c150315030f0602071a1005040e0d080a0b041d010b040516020a0b0a060839090403081f080c130c21060f0303081803030c0a050309100c020307 65
    0x1066519a00780101d030a41d0b0300d090707450f08200c130050301c003503804a040d10070001170340820440741001412150051a09074000c4001c075403207002c0c0600640c20b244000084c2400020b802d00d4004080e2a983c00b1036590000c090024641c0700c0030558482d0311290952070100c0d840d040410703c294001c0010605416202c01d000590702c01801101c2d04002440ea1003621341d5001c614906c10903030010550300140c80c0c00308940051b00b01500122810301806001c43c69035500c0d04c0c80754842125904941542d07090124a140f8485016080960010751081c005000280f0580f402d0742c0c0407034900c8090741140342112000880e00c031290000c00c1103502c03041d4800d07514a0003002c00c04620425190510540d086044011708160b421b40d1440f803084200420809100032640003000608480840c40168a5503410010401d08042d6408a9680ca00701ea0300010b0b504080112446552940840e40c9052003a80382211207602c01070800509006500b040300c000300c501e00407510140f865600130741d1180e206051105403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 987317715 1250 987316465 987316481
    0x15080c010e0d06090c08030a020d090e0c0a0c05030f03010e0103020102010b150405011b020324180c060702010516151107020a050907230d0f290307030c1503 69
    0x5000300ea80c441c0845940b40300121081c1a030107000410304424610380003200e0301194020085500011400c440c01d55400204111290710036130b41c2c15207445da0f4041001034908241c0e6200c0c40b508080104000640c01540b240c030b403061080c1c0840b85004040607013100070350820307009501c400500c140100150b42c1d09001d03940c46002c00322001103c0d0782c080e200010b054030031442a1030502a60042c0000700c0c44a1100d00e509064003e000c3c0d900101c400308041c0c50640304d00300d8000c011080900460420004040c00240000f10180100f500840074410800d10b904a18001c03810000c003040080001903d02d006404094400c41c050044c203000c220701d01c2c05a032800f03d0f038540140014451540135039107007070320300080310702c1564040301503102d000c0111703480001c01d60300a001490f0b0f55641903203820031100610410610450070403021060031144416039112100e10b8002038015a080100480062505200e09a000f8201c0c0d0b8225640e0303640d40c07c0d401c020f9022104580b08036200c1d251302a014052101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 987318965 1250 987317715 987317717
    0xc0e0403051e2704110c03031e07090b16050307030905010219050616050c06070801060f140315192c1320040e1c05030705071106090415080c01 63
    0x2060600d20800c6000740000164070480071004440c43c01e030191500d501403258480148092640d4200d0f604100384e03250b0003501c2580c0c60000c565000300c80014a140918004c503029a205944070349480d1829045030060241980c218404040043c0080d800700010a00c1c0e030310988540803500e1a01002a041c4003640000840c4a44460166000288081007141d0f0101d4050582141210400c1c0c00f02c1d004e000d81c03610340c480380c0310748014080f4094200103024102c0c0c12070b56031000071800c400e00469a0784c00c00820080401c80500201e421004090651b49891a001d01001842c0541500c02c0c9401500741d84446c030030646007400c0d1540742a05a00d240e1501c0c502c99603d003014140181c2042c0c04946040b800392840d0f40035111203144031201e440000007400e00030320920038090442001600e5508000f000d82c0048404400b4503c001d000f90140c9100e0b440b1900c070700c1e0501071036446156801c03140c5688a54041020011140da55442c0c0c407132a44002c24000d01c09500c036040a0100d80360420040d0710354 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 987320215 1250 987318965 987318967
    0xc06190806061305040e0709181205120105011b06060b0a11030c0601180b0a03080405010f0309020f060c1f051012020a141206090c1c050c0d0c0e0403051e 68
    0x1d2910394a0500c8204c0c3c00c03d41e4002100d5072052101c1d418503020b42c000b16207140c00c010003c201ea92034648422385050103030700c12000946c00100c007030340c440c4100042400c07060a007800401c51903001340303d04110781c4603a00414001c0c418542c0c0f008220344690300003c4041c24041402c0011690202c28807652011640046140008006030345a032090148590300c40700079104660b61400640b500409200070010b003030f650300151071f0b1030520540c1c0c02078006c0700e001400240052000c288a800360b030352110b0b00a004030025140040c01e12031981c0c011f242e040d071148112a50150f50509540e200d0f50741050142e00012070342408a0700304041020740d8841801010200c61764000340c0c1d01d610240d81221a80d40740c60095110380000b00d01c0c2008481003100705030080808010a07104046401d00c0d0062044604100c40540514900c00440d44424003500c0755002c200c11952608200c0c510b1a1042c2c050100f5000060790307801240c148410464040700054008034210691300004c001054030645554011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 987321465 1250 987320215 987320227
    0xe0309061e1e0a3c0e1c03090b190302033c180303010b07060e0d05120c090f100e040207200904051903020c0619080606 53
    0x40c446008250210301c00c1580c1180c05005400e1440031911404100e0740c282100e50301e0782541e881030390803124840c0d010911300038181d0320005001020104041125a000549102800f1200c0241d4540c040d00c10510010420000f99aa52150721940306030440304000000e03403a41c03400620845144d400320841c03142c280325410440f00504029034103506a0b2030016180e82d00d0904940ca00c00044485002003028000d80075451803a00e02c6130600000602400c01c41a262099100e20088200400b2051504144018404000144000c002d00d50180e400070480c003c1017200e05090840d101c1001001c15400183c0b01c5888001909056104c106100c03a40c1c1000002800f007200c2d071010303440c81c621810034a170b180c2c2d0446004524402c0100000f600464a5007594074080c041c1103005007203440328803038a0100d00028a031601c0d807144169404000382c50030000e80b8424414109014004500f98001e05009400588844018101c12898451402104111038001620f50078020b085580101010005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 987322715 1250 987321465 987321469
    0x3150c0f12091a01150906020708070b13080d210522020a0e101409040503040e090c0907050d05070c031e0203091c0201110c01090b07020402190809010e0309 69
    0x94651030841c201103640344040c50210070406840d0490500303601c08a001041d003603440301c0c018845850a44840042c16145c0f80180e0740c858051003940410b0744800403d100b0302a90307802802400c1040820040340030f03150b0702001d0400100c22140303400204540444641a1039849070718103841d02c100b000700f00c60700f8003c000305003c0150280071040301d00300002a00854440c014440010030500300f402d800e9003404d143c3e4003500c0c2400c2c411080480e0382031002c50300b1441c1c030386003e5000ea5807100c011441e091a1107842e82034000c00508250f0701c1d005803610700009840b0310720528032030300e120359131240d60b03488511601c41203a002602c604100903501440c1c07000603400c1511407080b0a070003242c0c9021503034007000c200e05d548206da4000d508285d03808003048000d000c84d410358404504c03d0300c1d410310402c504500540c0d03030011041c0d9103000031101c1b042000212201e0009143d07450018101602e00a04001e00e09c8400c1c000c801c0c110002402030040003151308c403e03c1445159010040510314040200c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 987323965 1250 987322715 987322727
    0x30714011e0206100e13030c1112010507090f2315070f0611072006090d0b04060e15040206180418051009030233042a26031303150c0f 59
    0x107801018816a0082380085c041d00b000300d000208001046c5081c2002458080c0d40a0502a02d4030004100034410100b50201a1200c100544000c21b80c00d00786c2540c0d80e0400d03005091101c1c1d2140d080f10320000c243d11100304a40052617080d0040e0580c0c3e030405101d29110b0222040c1b0095040c001c00c040c421400003451480c00007940e1803100225040c0c050140c000900c2c0c234494116103580c00042b0189086c06c00107c44603151040c2d0081c032040008004021750103844040304030440e142041c0c8680007030018038040c00503141842124030401d0f440000c820118046420703407030301c5802c1c0c038007002d1800c01080420407520001c69080c007410f0055020300c0c0d6010f903540d0708020030801d001001e21303024282e00324142c04440842603040d8412903a400c1c1070510769405154195101c501402d68000c40b44603416061800c0202e4400312004181c501e4500303941c0162800701150340d03e00d07020402a24440981d500c4040300614040d9000f03081c01c0504540000460b00c0308030522003804018036440c280707150402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 987325215 1250 987323965 987324001
    0x6041b0609183c0f06030507061404031a090f010e0a0816081c050a0c080a020706240905090105041a1b0a03060603050f06030714011e0206100e 63
    0x90010650052100e90b10082c030f02d0b41ca81e6100301c00d46048400030003200c10f030109200c034100d01d4010850001c05000d500c4c19901103000c060610761001c84204660392180680100500d00d031160103042540701d0740c94000c50008490311140c0884618107001d54440248215507103800c546008000c00c103c0168a1500c8001c185000b030581d20010070756004030520610011110303640002c05903900c0c40d030741100c943c10010340207079054070520342800034410148604c034421f182140c1d070311107400580d00c44200d00040e50060804a9855444602c6101400940203680c01e00300500304020a41c1400c0000c00d000303c038402005000035030f040c0030074000400e05200c038030107030042d0421001155582c0d05a90100c14070b6203002151050200141101400d039050780110191505a03a05203e2a256444c0c0c03052004420707541c4613450307009440204811090039251203403031841814401d10304540740a40070100074003540f40a016801c48410072841c41410b107607483c05085201e6058030300e41410540000300001d42 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 987326465 1250 987325215 987325259
    0x210106020610030b1513360807020f03100501151215170f0a11090703021c021b0303040609060c1e03020313061b020f0a030813031106041b0609 63
    0xb0b11203030840d44400c44040314002a01d02c013031002e85a46030031f14542c098240381c0340124800d412010214440f005428803015a0005081810311045800f009001c0d6901501c43e68180305e00070301264203a03614041d03103000f807070101031100ea1042041030103003000000c001e040980c0c500e4074822460320210202c100c0160351800c1c0c1100943e941034907801d858a150190340ca801c501c1500028010090f4028a240042c1019a4281e001e511044d105500340d00501d4044000041381900850f0201c01d03d83c05000419508002c86002410200c41a400d540c0242c8064071050349034145030041c000c2c503000c0e00102c14454136181111540d4070f415202c2882c0c5172004a1704243d0000013181e5104034540c11540c105820407c20400b00c03041940003c00301c0c142030b003c5009802168070341d500100c80071842010943d05925070045c0317681c50707114141e80c0c819070b00400c40910004688803604507508100c0c00340b04d80c0c441c4505008030f11000a006140d030b40d40352720240c02c100701d0070018002400b00c010002210420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 987327715 1250 987326465 987326491
    0x2090312092803050c06040303020d0309050c040f02031008060709090e010b0a1e08070f091104150c032307150b040f020406140403050606120102210106020610030b 72
    0x10740050198400c03990102071540c6103554000328940395090007001c8a01ca14126242c40035554280b02030307030082e03210207000760b0000300700d0703050a9009400011040384504161000e502513500010110f401c500b01c4501241e07030120410120403809082c4002410424004080b140b500c41d0004141c107441c3d010700008a501c0c0d192128444509400071210a07900030000a403054a0701d0b6100250740703503ca040003402c258050300150480380801c0d03110a4550b03005d043c902180c02c054040024011018400074000c404100000700300c05440786842046403240c0c0c42c19810545030030001c1c0070300381050b0301082d07100002c280b0340200d11544085a00f0705501001c002070420041061100500c8500039003901306003440400c84512841d94020810388000352503610b086003012000318881d028502000704203a0000e0702083c10f0f45480078101e0f80312050b0400140c501540e214100001480865890a0302036001005002031501404120b40c004000d41034503d20500d551191940404040c082c5503255503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 987328965 1250 987327715 987327727
    0x20603180109050105160f0320070c1a0c060709080a0b04050a0b070503160503060d03180938010c11180f011712030f0c070f03090e07020102090312 65
    0xc01e40218071801d0304800200220b24040710b0003140c1c1c058036001d0b507000890902c0c80d5182940203204414040104d00900e0706103c3c035012a10074a5884100c09581d1040943c1d030004681c148503034003000407072980000940710440c030006580743c1500504103c051091960701031120704000100c41041980050b58404140c90720700f481030070540c008502400d00e000040801c4100740e0060015401040f440340d0900304010301804c11201808150f80e050b510454035007403c1d01180c0310712040c609494030f460a105846507543d074501c0494008401400901401c0340e100120005021011103c078004640d05d008078072501400282230b05d9444400802c1010180350003481501c514080f02d08481c82e41c0b140307001d5030800100301c0000c01000d00c907442c12144010040012408082a104081c3c89000140b608540b81d035580c16034003080c003c01c490001d020511941011414002003d01441d00035120703103035118104400d00d0030083d0014803c009581c01000300b10401c0e100083c0d6040c044010313012413038540c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 987330215 1250 987328965 987329011
    0x242a0e100f03050c1908160c050c210307050714060427020405030d1205070207151b06060603090303140c040509040602222c070c03020a210e0d020603 66
    0x8043c10798030720102580c101d4171480f042e800030142802407060308441181d02600450854400c551001c1c0188548c1001090308820300700b06010724004614038810500383e02d00c2c02042403460300b1017801510b06520241c03040010300203814200034190402d513802494075080020b00c019001c2c402d26030342034214268000902002859058a02601c4014240c030b4040c8210300c001002c0390a03110070b05410515103c0481d10309070002890000301c07001c0c50600248001040b00589122032850010101d401d81c00711448001580d6100b0007001d8070084c3c0300002d01300c40d90f0800604480c000e0104031203030640c0405015032004c000c0180c804440741290841070a66543c5000340190080c0710101c0080d007520200c1c0c0301c1e100324400aa50940d902e800c0141480c038403590100380c5840701c0c000c009802d041c003440460041841040318010150284c011038945200f80e560b40804803c10011020f010780f1441084902558440c4000080c4901220b00841110072900010200d01c00982107158001d1081e2031380d1004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 987331465 1250 987330215 987330217
    0x83d060215190e06150301110405010c0f06060b270306010305100b030a0602130302031002070305160206130303031b09030b0a05040309170102041a0304242a0e100f03050c 75
    0x507030f4a40c00b929503500300900301c840d040c0300c2c41ca0420300c070354280280454815041c0d010350341180d105030768280303000c0c1040c0c99480024103e440152181c030f03207442001c41d4000c422070040101e191040d4072802644070400443c034034803188441940c8641c00c40401000412000641030449048159001a1001c1610700080ca40241d50b04001c5c129800484c041540b103120749503040840e40203909540b041d25103000c00004910420380c0040100b0002c2c0700180070800b610100c84606031010b000b0070301c0c00c45400a83c0801c0409a40f0440c00607885d00491603d0b840c03c501310150b1801b941c1031180b03000e130940c0d82d0b141c08280001c0124903516510b87c005070070f25110781e45210051600c00082940f581543c52160301030350140c090415420041410031549460300c000f00d03445a40c200c103200040c040609800050fa1005614180c4c032030761100c40317078102101d410008407001084948100c1c512107028801400780401da9044511030050385186a80c40794100600c0381d1261540d10780050603a030769400f10016 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 987332715 1250 987331465 987331481
    0x1a0f1002100603140c01051c05060d020402070f020f06040605031501020a150e070e061c080f220e040c06030525030f050c0901050406083d06021519 65
    0x500c0d0300b014000001c0c00b42c0035096040c100c90701001d4a141040d01030040d6118400d680145a0341c1f48805c0507203040e0400da80c8030a400c40d00050411101e9946600018240c2e000340c0302c10b5810b050304a5600c01186070644084074450f9082d1240c900b464503004015040380070013861135410340900881404568030078046407a015600c0005041c0c0700d01002d00d00e2004100c0320f103400d10203100d03142020408500802070700d4030030000140151081e1102800550b41d00800000854030f901e010f2003002d82c111440c5018282ca0355540b00c0116030a40c0e950450740000c00c2c03d034400b00b20a191502070002040010201c07905403100c908001c146503c840d00c4e44d000340c1c446a10344600444114400290302d650680000c3c5950810312824440d58492540c000207030b100c1d606100d0701240c0c04000810106000c0e0704160703400a00c3d6840c039000d51700d0b0b8101643e68401d111a84038140000d1032030306030801c4000180200548103070b00c001c01c031080b82c1c034002600103400500709920807a00c040111104100039042408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 987333965 1250 987332715 987332743
    0x209090f070e0d0c1203171b09041e2315030303011a07061103150f090601030c1701090203090f0610030f060e1c120203042a080703151a0f1002 63
    0x2907403100608000305050f00d60307280d1200c7c554070a008034610860300300c503042882520300071840c50404018200401802c400c038610304c0b141d0b4807441d907101c00101d5206903045a0182d10000c000d078541c0b05060811540700400d62400d03e00d030044ca00070651000400d582c10340d010004907182c0c2c1c85800800d41c550380200740d001000181801d03a56000e00d04c0c2800510300440c01043c0000701a4091070403c41c443c5203100c511500604510000f42541d8840c3d0030860780036202e4100450751042c0b400090b401c401c0f00360170600303696400209002c90482d013082450201104200030304010300f002010025008614807001c0c101c4c3d801034a0120034005590301001803003420404039100b803140a640d400740c800001c250900410014440d00e954103070617000301c0784103a9010484d101a401c41c0601612002c400003150641c00da00480d022543d00010880c140c05140111510305208002424200507100c6030f95081c1d5074282c900d0784248682d128200d01a01d08041200e01e07480c04a41d004049217008840c1d540381e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 987335215 1250 987333965 987333989
    0x30519031a03031224030a0602040e0c07080904051509040b070f180b030a02190c02040b0418020409050f010c1215150518040f0209090f070e0d0c 64
    0x8195541607840210011030030040ea000c848200000c1649030701820010031450000100020b42981040d8000c603a9003102c1c40720000c02c6008100481c0c6043c0c1004821240c16500260078400d52040405095200700b42001d01403800703006035103400e00360241c0140b05009a80b0b40e00800c2e140000003c103032020b01c0e0041d114139003601d46818241c194200030303540301d0f001c16025915420058442d140310344049048044484111385404410105588001c01c1c400c0ca080e4241f140103200e81d80c10b12504480e10301a0340300343c130200c55401000200c8a030100350b98400d5281020b012078892103140300c4003d4030b4040b103000481420034188907007810044c00c0c0341c1030294a41032a03809807640041c551f50603005a04802c10103244810952140c060f02e07030140d001800c016101c100100c52050008010804103100158200f8000001050545120104a103903698010400c8545400d02d00c207070030360000c8543e2200350070303003480359010380055410480b05004044205002080c407070441441c00007010104c40e10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 987336465 1250 987335215 987335257
    0x2d050a06020d1112060f03120a08040c050a0e0114030a120c14120a12090203060613090515090f0d09140a05090c0309061b04050409110a140f1c0602070305 68
    0x903051040c4c01c4803a2403140341440c2100c07845060001341020550344000c02c040c5003040c0210140d55240e4010022500d00c10a01800b1401d6100c002c0010010031180865186550405c031b0400d641f22424a9511300a900504403840072505a8024903101c00c001e062440c81034105003041d280c1c040029424038014800c200451024011400041c130050b41190b60b20890113002021200998294220207941a4056004a00c0901e482000c840595401500004014400742d0b126030618168049030042e120201c810040c5c52401404410314681d0f800016007032007450424080e203540307654000d0544102607201807249540320350200002a00d8002c0c040c1d80103240911001130720340c1c811911588140913240c0800c0e03011005e491040002c07540700030715509260404060100808041200ba1001d200f0041e1391030a0b921070110351005070011260030680140c502c2c0c1802505c1c0d0a81c400180200c0040c8014214803104500702c404d52a4840350250b512903450900712036a0151403900e02070301e00fa084031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 987337715 1250 987336465 987336487
    0x7170a0c080d0e0105040503070b161208070e01020d0807031503051023090c0108040c090534020325200a0605030609312d050a06020d11 60
    0x2030b000802000360ba40c0c01d0044020b20044503603014621806405d940a900140a0001114050522660103425011007040c0030b460300440c0c110784050707590215644006000c0d910b83c0c48582161044e00a00081001c1d079040f040c000d0034443e0081000080640d2a900c8402c0d080c0e030403100500551708a401c450b42200c44070001e000602060045280280050b91494038605008494511459050001e03001d503100160064581e0080248200c4507600703d21004102290148280c2d40905c50901c0140b440841030351032107040c0314400202c1c1031a082c2344e059800d00a030707001089403c02c45506c031360f0441d5020088600e05007665501002007050704a8190b031886207000600701246848100d50340101c2035075800b0207813094803058039440d03040820078000400b4018050b5003888002c011000c5805104000481c40b1061a1101c6088504051030444001c00c031640403480120440c2c000c1030000280c1480e540c46030b03605074958004044c1e98000c10510b0102c0d6041d03001000d0b100011481664588450603 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 987338965 1250 987337715 987337723
    0x120a0908191d010905091605191d04020c12071a010e0a0609050408090d1406070509030606030601140108071b080d0e0d0509060c0f0a08070209090a030207170a0c08 72
    0x1055807090038681d1002d965610503078a0303400b2a500648160b000e0b48a4a204404c24028107105400740a42080b40000d400c140200c00700da021003580e40e244071075020364611405c040307010384076510460040c0050380c02c00c1004120144244020b05d002962900e880c07800e00700c3c0b81405607562104410483c00085c00049554081c2d20522602604018154441e000e01c4c0440360151005080312105015504560401010740d07440180901d018030301d0101400300603450030104980002c0004c3c03010501a082e41403c105160300141c0440240c400ca6040000d04252902203c2d030f2031741042240c10105001901030441c3c020302c0e101c3c0070b2141c5007501450410100f07580c0400c48075182a460204800f07482d0402240b05038801050fa507480c0d24013501d00d02007107080c0d0004c883d05101c90092190400c201c1c0403c0200b0084144a0170207a5118445401000820000104000187e810281000001039401300b041c0060350703034084544204141a0003070700e1900c079103440c0007001e907082a00c02003804c1e90005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 987340215 1250 987338965 987338987
    0x1715070c0209010e0118020f270a0504020913020f0c0a0308040b011d2403150103062025150f05060406050a090c0302071b050109050105120a090819 65
    0x510080c07078691381c414215200d940244194105080c284962080704034080d001030240c00c60280c146420501c3c41042c41c28420031a50001c8502c408c181980d1000e410b159a0741d44c014401107800b141007001c603002241c061004400210700e000e6000070911300c000c2c25103050b039550005600c100c2e00709450518000d05140e906607410380d03030746021200000b801c01c003403c03201030070641c01a042d10799519041b960001032031041d01c10b200c07902140701d071508035520200a11136284c581b20854072019450340c02d008044507c85401789800c5c1c0c2510300c034400b090000800719100c0c20300d1610140300942c00c404131040605401c080060104805107529045400b10350010704030750385007034000c0040b500d5280c208400c492151203007540003074014004004180150740806080c081904026181a60701e41e83c58090f0340a003a140d090105c16989c0521041d640041010003410081c2040741c07502e490000b0b1480c0001008101801194460440f00f00b04050002943c4081e480051412815007507107201404450400d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 987341465 1250 987340215 987340219
    0x10303020c0d12081911030402040b030c0d0809040b040e160501030605030c0613080307080703120b150304030207090e070e0f0f04030809010207020a030b0105090f101715070c02 78
    0x40310355040d40b03107032a00d501d1121a6001903400924514818140c2e48250020b00400c0c04000030324452400482602440d42258140c00225a40745802e20401c01228209480380b402a0b004945000094a40384503840300183c210846e10307200c240d6000054013070030791101a10340250801510440ea101f00150048005441c0f13051020b88646480c0110203d540038400c0e0ba03455440f0001064590a040b0010401d0b0100e41090444407600d58504c83c1c59580125802c8608010005c0d40605156112600315050820411b007030005400c60000616168100c03404850022400070205040600030072201c0018101644103120401d4820f41180c0c440502d48101e1091440e2680000d64041d4000800b0b031051220148032280c1c3d441385d440443d0b8281d0001c0100760340e907500704000030140e81c450b217102c0300451003080704208540c146014000c0708040941403560070700304842486074544807807038800705840741b03500b5000324401994940380c9030827011980011002c041000f8005d1036980721440e10545402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 987342715 1250 987341465 987341473
    0xc0b040b1204110415090e0609030a030903030b1020010212010b090609100905120f0d0c051f051803070302070303050f13080c03070e04030e10050d0f0501060e03160b030c070f03030501030302 84
    0x4026481f035100d40040341c070030038240c100b003084909040c06507010b800e000d80281b5002640035588408118900049245140414100c0840b1010104010380166080c01020000d500380030042c0f6209600d0f41c0f060242c80307544a00030520711800c1e243c681c1912880f0740005c02c03650603d03d941702d01820514443c0501402042e0941103c0f0298070f000031031440f01c200c508003c080c0c002145004a95400141004a550340510a00418400000060400031040220303000a00f42000c608442d06e02524440d0703e02a80c006100c2100400d0300412074604580e01410056690143c507071982055105507014001d00150500e80070030031401c000740b802c9140d0816070442c0c4545849000240c800001203800800040581074107141b20301b40480440c25404072810218140040000c000b4180d500340300145078565610401045440d0f0700009070f02000c80150064090000e036410405040f600b1400b409c0c07003003d000404100a8071010080b03803940340d00541541000302541c94010090082031005500601c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 987343965 1250 987342715 987342731
    0xa1b0302120c070c05030f010e06070801060507120e0604080106090608120d0f090605090a02030d090b0a05181801060909150501110c09130c0b040b120411041509 71
    0x40644216880050341c0d01c41c074005a07071618031410590b4043d281c00c80313010301c005a000582d81c07401c00030b190030380c02424000710b032030642c01010350b20702100106590304010540004114654000e0102d55003da00013140402c071400001c416100807902050303082c2c10140001e000101d0f9003041d03200c907043e07502444050140ca80c0d07500140b503a41510582e901400e1a0810807044610a6640012003241c0700000109000c4002d407600307002c4550858290b141500422808011403805000819004205c1d060a0f8011800c050307083d60680100408101442400070341c4480c0c00522020b4038516a000410740e011201c41030500280407002171050a0102da0301c0c10b8041055401e80c0981d1044c1c0043c4065a038445140030011101080c0d00c07d18a030313032801880301a12141d100c405640d88a070072485222843d0407498680903501540300d9200d0303404044240400d1004003110000c4510f811000c400210300381d00c031401c0a8040015841001c0c1d84249820980c0c030b141c0d003541d110340084074828070013000300034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 987345215 1250 987343965 987343967
    0x140f0129060703030e0a20040c02102a050a0f050405060708031504090b01081219210207030e090a0b01090b160b0f0609100f0302150d050a1b 62
    0x400049216400d0981440800209040c10005012840d009240101e407501091030f140e8148002214160b030820000a103200508091410fa65201c030410b032420400ca60001d50020340b5134001400c0d031010261140501da0500b007036004501c0847c4591880004051400d00003e48541d02c081c11040102e240440395030208d9000310f0944080310390103840c56281910350781c0e500403507620081601c100d02244845071991500c0b280300705441c845c4110101030b01541403115403464040103604410f8806800c00c02e0072a80031060b4414100040e10341030071800507201e1454541e07006603403500d44441920101d0f5900a25074050485000c10b003080d9820b1096440f5000c000d03041c1c40603100114040fa10b43c6004100d503032685401072980316030108c10011854160703034038800202c1e4140d40c0e0303031290042e1030300f40440b500c1c180e60000c0c0c1108900c0803c91441e4a40118142103100c50310020748109500e1441e429210811021035443c010801400c0119280160080340240340c03607102040c00aa50b0141c0130364003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 987346465 1250 987345215 987345251
    0x3206030604053c0a02090a18150902090705120105011b0b0901150e0603010c080910050c0d020412030f020d050f0d060509010f0306150509060f030a140f01 68
    0x7480d0040060000e0203010070304000058003100c01c5400340c5a03100041014000b40c020303818142c0c0a00e1000d061101040e004000000d04050540900c1c1c501d05940001c85441038070511900c150311985038a89d81070001e107808000c0039081406500141e411041160305d9074000014244030030251254030300c99885400450742c0704010000000c8120280038044045111501482c0c1d1120741c001c004141008000c62104011050340c0c0300f40c641c00131590901c582860207005200380030f821464402101c0c41c00d51400c580d81c1c100001406412565280401c01801c403010480f111105010b82c02d41d5a41d642d20741242d403660741400706800150010810f0405284007048010f921203540d51508c2c10f01c1a180802c54813a404940d0700c07041c959070380000152a8441d034140d5070080112400070400140b650814000350f6254003484420440e05410600c05607807254615a0090800d0f174029501c0f50320000440d02e400c3c031400b40038004021028110000c3c0d0350025614906c401000001e200911a440d04a940 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 987347715 1250 987346465 987346471
    0x10e0708011203080a09140d0908010b061207090509390405040b06071a07020f030403080301120f2310020403050a0b1b0c010207031e02070306020c0132060306 70
    0x1580e403020b050031021911440c0ca04e600031000600001c5c280100b40d840d0344607012503106400840c0c01107c00c030309495400030407410080440200900c1100c0c500c1e800147c0c584291400304040d8031030750f404130385204d100362000c0d40602009810701c1b00c2400d18040a1503220480384030f80400300f2200c940c0543c40e1030804040300180340f07200906801c060a020420010b85900c200503904140c00b8810b890115070b0781110800c04c89a07109010415040c40c2c08005c0c107041c0710a143d0071060f48204002c00000d00340800310707070450b26003260700c4074105402d2030080704001c8060b0010700f40800e400d00c0300c0c00381c000c640b240512501c0403100300c50510742c0c29401302c420382c0140d02c006091608941080c44c00324640f8501d031548520910640254510158000c2c4055041051212a26940414000100354020400300301d010340f40c0311880d40551103080c00a50340c0c80b460100038a49070b000b24681010000c2504000c20301c80d0484d0861022810b06200042210b0901c40340d070a100101001040382800d0104410780 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 987348965 1250 987347715 987347729
    0xc05010c0b041716081803060403090e07031e0c02010510180c0e21060708010b0d111903090611070201140c16060c0201090816051c0812010e070801 65
    0x145940c0c0c40d2583c1500b03000c88000001c0c2602c080001c5019290346641c0348003c607108440f8240c035205152032070340c2144c1c1e200013070a00a80c080d006120100e80c00500c000202c803056180e021560b034900d9002c6010300a188145409200c0d0100003480060464100321600d00c21a40200104e64a50b4500c0141055034070800040140400c80d9a55005e880c1d045115250079500304903090051103030100d0840103110440f040004144800000b19240070b010058110308185060000365041c090320500620419121102c415582e12030081d0050640c2c003943c22601e58880085809002208007402410b01e0365800ca80c038a1802c1c0d4904030741c2c49504180d400b11501a500c0ca101c481030707540054259840960300401e1449100c142013510b8107000300c0c0101400203079940034040c40c1d1078400907240d03011a8000310869040a0303814490350312100941e000722032040324807414040c3c44a01d084046842004054680e9100180f02038003010725840d0f041c100c0e2003044c49084155101ca108072048042806494 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 987350215 1250 987348965 987348983
    0xe0a05090115380d0b0a1a03160309030807110705030f0708210403031d060a090e07080622021903200a02060103030c0203030c1015050306010803041203020f0303040303090c05010c 79
    0xc804242c00d6000178000c2c000500140c5034151621240c880c08006510700411070400042000607451000540205805c1c26007810701c8514611f56001e020948001c100b1030805c4451840c0d08190346040111a0003810040e05646404c0e090300c00141d104c624a00418601f803052580002c0025600300310b07014040100703840c071810075046607411902da900208a017a0070120803035018000369125801800120707d60b0701c441c030100d450100030406201000b0b100b481441440400c00100c3d84640b03ca2089104688c0c400b5a488c1c0c60600128009024495020030301e0300c2c0c40a0b01185140d0150b00211030b40c0d56034001401c4110b4280c00c9109903100760241000160041001000081c0c00381d0904207051b0301c01802e813410406284c000600e00741d8845a141c10482e1241c1c0e4003021058000144c46c060f00d425005410309605220f40c481d40c0344650702c102810096804800700c10b2503c00e10410b80d000003802c1c15a956401c01d4100100038200403c000e4a42048410340000c01c0c0d8042c00000c2a002e502c00218 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 987351465 1250 987350215 987350227
    0x216120e19091817092d090603120c01060e010b07052508010218090a090305250f11012607120b190e0901060e0a0509011538 55
    0x140e009820140350b210040c0350602c03940d10004200b1011149481e0382c48a00b245c0f070350403d0080081004001018044040c2c40002e4190048a4007018000c596004d6400000c0d585502010a140006c440c2e15041c22072404200d502100c1c2064004400700d4503e400005000d1342c0b1111005110300c0351801c014417070f91150411100194a421010300da0001e20781100c00e08541d82d00c509801d82c4c0c001c030343d00d00e4402e40d0901007042a00c3c2100450713410030320615040203442150f0f0b81c0074006215403900507400300600042070000200030710030742d10030544c04a6042d101204501e04241ca0068103c2014041403c0201c1c81423190740300e03a1180c0c0b480c2e8600f0164605a1075080c41516030222180c1011003040e00c4680103585903c80505002d0900b203042d14209071075250021360418042c010784010f500e0390500d00700704240c00424910b0364100c90721106c0044c00ba00c8007410180145541500c0b5110001900c800083c50541d442c2144002700015030399a1141140c40046030691001984204042d1800e02c0302c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 987352715 1250 987351465 987351479
    0x41d06030f150c0d0219020d050c0d0e06090a120302100504020108010e33040f0e030729010b09030d11070b1e03040c450216120e19 58
    0x140303504140c1d10f0003294581a0b05081d09000e9900c1040380850782c000c0090528603580d070400503444c906007d03290140c01c04055001968849040c400b1807010000b58440c000b03603594030702013114580c000090024041550340c421040c0782c140a00415000750207040080d002c022514010184207035030507918001980c0c02c0001c006480000038046030075140d4807021201a4621407401c3c2ca8002c0d1b01c0c2564143c076090b00c0000c0205031a040385820001d142003141c115400d01d400810f94103907540c845041c6116144c2409205d215140101807444403684200002580302c080344018100d918080d41a522200350b400d0301950600400710174400d0b10b6101c540100000d101c91006000020011248005910103200c0300d14055002910140c9124011310000c01001620403000d071000844c0c85049000c2c509840203804808815800c50310904001c0722000d00c0340c0c40e17a5411541d40c07a480c0d031031041d004609814201450101c2110b000042144400b0800462401c022266030200041e9500c000c40c50070069 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 987353965 1250 987352715 987352753
    0x30b040b041533081e0f01060608010317070c05090601022431020609010c05061008010b120307121124130503070b040503040b041d06030f 61
    0x2041d595072a00d42650750303000800f8080c2260b102e05040c08610021000440301e61880074070344403126541d20441d0104a240310200780d641c10f4804019090300c0740c4254102d85810004441081d040729440c2880104502d07400224075810380e4005c2c0c80000580d981d480c08048244503816010f4450b001c040c0040180340f922103c8036501c0001841601d0204460340c0140f900340c1c1c2da0300c1d0103901e079017419410400b40e080003000d240c07a82281c01082c0f040d100215400310a01c00d503065070180c000d1000062564442e40240340c00e558466101040b40c180e80303400394010059400074043c0c0380c0c280d420b01600d00d00c5494030317401e215144500f00c005149449100e540f2001160741c0340c40444d082c0000d88039404003404017800041104103c08000340c0380d200c2a004449c1400000038144004c00c1d50215610011901c00000e07280c0781548030940c02da1944460410783c5c0b842c0aa98004114502c0c002408102c403151310b512500e1f0020b518003580c400c0d40301e8504040d02d40c81035a68406507030740310203182d00070064488 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 987355215 1250 987353965 987353971
    0x501053907060309020f040c080103030e0d1e020f0f060409050a09050d0503191518060e0108031210031106130515041401080601050307030c031b020f0d0306030b040b 73
    0x860450040206100a0804a5591000020944d01c1c0139240a60400705007140c020344040398108600034035070801501181040c003000d01003003428956400c6036190034007101a01a008403503108000008010800501d05440c0203d00400c9800c185a07101d0a2103100000c00c568010050380c281410000c64200030301c40180381000300e5407a402014045581440214416030f503ea03252a1fa85c90003108510b02074411400c0b00c9a020300c5c00320b025a40700c8a078404003003501c0c05070034a254510010320201016004030b41005080211303c4000052903600000240921265003a500c41c0556031404001c2000c0c103248009004800c1102c0780020514160000748a8028a51081c0d028584c507100440c0380d10f691130390401c0790068005014000c900000e1500081e51109180c841050300c7c3c41c000080083c040500503109043c0c503540c1c0001d8480c001d40005400b100080c0d10442da15003000d000035551224028041c1042c081c1c9140c0710107591007401468252500840e0950040d111035403814a509801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 987356465 1250 987355215 987355297
    0x3150708061507020d080403020109080606241902030c3a050c01090305130803070210030c0e0d050604170711060906071b17010911040b0303120a0f0501050105 70
    0x30003521005079902c1840c1748034a030041000070740f294110710016007a40035540001d030455120b0340800542d644e9101004c00859426040d41ca007418100e0aa65994065401c1240d0300592030111088440e900001800b4140640c000700c0300060180c40d803c400c40c21103000c0090454050b107003070409044407d411103415007030300e1504514088040480ca42141c0c04d42104800051000440008130f108501d580ca000d0110213003e5844c1c001c076a80020350380f0720302c01d504a0038141c40b4a075000207036009441c01d000111004e040e00b0100361651405984544080b18100d40702c04445402d0f840740240030056405082d8860144a600d040032401c004054012074481c030791002d02000004001a1105143c00d034004d04040301821150602d82c0e07481e4010f400c0c04500f413450707241c0b9a402000c648501102040c5100c2641c001501001c1a00841e06512660454601203460001403003142d640a5001c03d0f070084454208104598941c00110303046d200e99021040c0b10321074400d55800c1d40041001c2c0c031441c0049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 987357715 1250 987356465 987356467
    0x42d0c090b22080a030315080c01030f0609091a010e061507110406060c06060509190e010b0603040506041a0f0a15031b030b0f0105180411030304090b031507080615 72
    0x1142c10041c1140c2d4160b0040c42503900804a01e6007019003500429102900c020380d00740086040652a0790364550b0703454030504142d11a6401c1041d041c42e58800b03405004890010700c41c04d602801c01c01e000e80140f4a0102568107000b0000450015011006000d680014003200e82c02200d41201080f80d008504c00b900d41e92030040143c0000da985205890041c822500c440032450158109607044515913071040c1d005448032030400094100b84071078240b03440c1100800040b4000c8010003580100340c0036640e150440303000000c1c13109211000804600c6a44903c804a4460880c0300a20942d45000d6460254881456000c5a0442c1440d00580030020b0800e2001a840350b480e1125003030030b59002184e5014110f0680c1c14000c0c4510811810341c0465582d050140551420300890248988944040001540e04010908000d10604213911804000342241d80300c40d250240000104250250076109200d00e000d40d0754401c0302d2030324661051002c0c0d10307800625a201800c0c024481505075018454206c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 987358965 1250 987357715 987357757
    0x6050a0b0f190c03020610050105030a1d032a0d0f0f0c020a030b01090b0f13090201170a0506120109020d021c020402120906010503031215060405042d0c090b 69
    0xa180d8640b9401081e82d4404820882604000c1d06100014013500290250200107010341d0742c1007400c47c1e170405095100092200000d035103007001c0071481440b8000e0b50000141d44100413500c584082c41074500000313010344c4034500d600c5069607001041c1006010400b201c00e140b003600d001f07033f4000070426030900f0512880d8880c0e0703002a81c1107005400840d54043c45a006000c441258402c035000d03050103071f8166100c1817191000542112014202c80344981d00d4001d403070700b1a4407520f001c444110016562401c28100580d194000d0201115140e024415120384c3c1b03d540c801c140181d02d80540c02030305400c3c20843e0340c2c0034081c0d115080620703070f200380c90155003510041e1070b18401031002d0402100d40e041b090a00d80c03ca01d04010040e440b0078807983c01481256441c940803208a50010300c44c8260082024170071002c6409805568441ca6101d8075200804940540c85d181003140080d04500d03428401c42072510150071070340c0c054400790020314584024801a41d891008203800e10b914007115490384 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 987360215 1250 987358965 987358987
    0x309060c073905040c09120507050a121502090f13110c0304080d0807090b0a030f021602030c040614060304051009030c150203010e06040207020f09131506050a0b0f 72
    0x10102c0e038030940919070516460038000328800030340081c040842c0c0510400010701d000901030b00d0980030303040b81090076280341000c1101c2002180000c0002600c01c3c1d180d2a80d0f01072900913040289415075104603032094001d001d00b070610840c5e0071000c0003004404000202001c0c81241d201c02404403117081d903030702440650320b08800007a29203442e5442c0290788e11070600f0099400c2c50303c100441c00c28452408180016150003121507015200181b2185841d902c800c1021005441c0c807904040c40c0390710014500c9125034100080c040070900a03800c030b0b2281454002072000b22802c0e445a01e5400107010320136203851400c203004540050044049500c41000410f1140460b0030b035510403404a0400042e40081156508401ca404400d56400b142103615021640e8800240280010303c03032503000589400315500c03407a640c0302004d8003400d10704407882c2c240c0c0e080c06900582070094920300c1014040c0c000c1480c142c0980002d403103001d448500e1062512555051a42000300400700c03e600c18020810781d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 987361465 1250 987360215 987360263
    0x70302032203030e06270606360112030f020c060a0c0203100f140a05060d022e0908011a030307170705010c120b0306041208060a0803220602030309060c07 68
    0x5026150020546800d41d000c0382c0b41001b18181c032007005800c020100206662004484c030020440707203d2040d10400c0e00851a4a817094260320030382e04000e502c0020606e81c0000b0380f103241c12840790310b0303600d88030100d071605a9654400064082d4421420445000414414403949000c0c6202a045949040644030b01505a80358821011501507944034030281000403081c1e0140c110310440c100b0411410920b02007003600540803400790080c18583c035103210005102c0046468038880c481c038026140100c2c000285012801c1c8100b0340690308041b50b500000584805080050100a00862500c1c2d0f01ea07481c40e110001401020094440030302074000407d8081c0500003d207007999445526414419110400300c1d1071842a40e8002c1c0d00060400001452a041c801e52030078280c14140700543d22000016a280b900e80c002001c0d5000c0031a400851480c000201800415100c502d241203a03201c02d022656400100c4440034258071110108030980710342801072000a0043d41003940c0b81c20302c80514588 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 987362715 1250 987361465 987361471
    0x6240a0801140606030106080a02070c030803040b06040e12180604170c03060709140f030115030f1101110601060e04060f030b0a050c03060a06050c07050a0815070302032203030e06 79
    0x45030b510340c0098144607502d0000543d21403002c6459501395410414000d01e440401040407614a42c000b42c1801400b484000d808015035201c44540c0c2d81e072415140c0b544e660b55080d99818050f508251800401503404610400e003201200045800c0003580d03040040144034281c1415000102040b01080450707403043d040291918074070080910001000605152010051280c01002032845092000307001e0003004c1a5065400c9408a070340d8100100047d004141d004070404400f000c0c01400020400b0442400c005903008141418500380a20010341d80384a134a2110503040e04a900148581800b40c1e41c41003201c40c01800009a40e0b440d5806080305a2580d0000c0e80c42d551040300708011000c081c0611644400c01c480b1041c298249900813451407071450140009012005ca20341c1c9420108101d54801080010310180c002692412840d84441d0292803941e86546000c00040e180c1340680210ba010b03c224101500c409100c0f404c4100ba00041c864085003003507160440001c2101c001c01440340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 987363965 1250 987362715 987362729
    0xa08070305071d0601050d3303140a050a02090c0903152203050405041a0301060b03180309010c1101050d0c051c0b100c0507270507020f06240a 63
    0x1281905000c0b1071525407043d0000810384401e5a41084602c0e61300c0416144041160000829202c0e04580c0c90f00850f07008101c5d00003402140342d14401e80396600c0c400300c0202c9024080100b00740031540c580b10b032960700c0c100c0c010b0016402814804014100301c18501ea10145c02ca86003030610034400e0001c0d080c0740e40d524021010803104014011403981d14061805e05030b501c09030b40103403030119640c0503240340243d201d69445180d9440b5061414080500700303540801008000300261601d609212000350019038007024400d101a919180c1c0c680f00200300c072078060058503141a030104560300c1c10141200b0344c000d10b040010a1041104c104114082c0d140c0900a40d242c00703446542501405248100a09522203007600b441c1c084041a158010101090791003460500c41c800d62a0929510b4070031141e015141c5118060070130890fa2105140000e1102401c407014025500c810000300d0759060071051455403038000701d010070000c16640141a98600042c5000c1c4030703079070400d8001045006154400e807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 987365215 1250 987363965 987363973
    0x623040e0402010924110303130b060a09020c1b0a08060606070305071a010305060703230604020c03130603060504060303120e280c0e010602071710020d020c1e030f090a08070305 78
    0x909190b40101c051806e03180795000450071403401815041b2600d181c2000074003100c1c8007001040c05a26034001400c0500000342d0150f5545144a542c07607520100c48030a4510850040c11a80c4c040c13822101540840300c5000050195803103c6040203440d900c0001d0440c244030081103080d000800b4191141e01c04803454000030310315032460402c10304000d0000e00c107008140c640220300f81d16111041041442d400e07a01415449580c036000418024410b5130103500d85880041000044815100c0d0f18405031004c0c1d80d42800542e40d16001c1c070080e10014000200825420344003423552410a41c00b4280030a150421540090244405003402d075046004208110528081a42c28041c40c141124000c00048502e4804d5626100380291150818064280a03034001b80300c0707540301e4808002c2c02c420800c05c1e1800319030b910b10800c24100258802d0350a0109801024182c4514a15001d1805c0045018101179460165951100c100320b03801110816407061000d0b10208410f0380400030703000a14030590041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 987366465 1250 987365215 987365279
    0xd0605041b14161209060201023604151401090e22021002010c0e0a030b06150f03240916030f0f02070506040213090203070e070509190623040e04020109 67
    0x809005142d00721005583c010003110a00303c03480c1c00514080e40d03a811a008189031252403a80f442d62b4030145280e80a030400400b10040e003440352400003200c9c41114940c040407004030055403500c0e254030a078802c12040f0342c0042c002c00000007518400205402d0041d07426442c0e68009200c41000305862401130b0b54a07403000c89140e803c001003407040c040441e402c0750783c1859036413106160f130750082c4028091250a21455010066801600e0300c0240d01c4940d55124034000780c3e110400000c4040148050103402001f055030f0408035400b6014288143c0b100118640e680400d80c043c01180345c0b00c40c03c0a6554039001e0b000031591000e4074445215502a1455007014010408400420341c4040b031204d1402450b070005031303400141001203c03160000c40e40142c2e500c4805954038011031440720b401800a0414419200807400d100059401380d80b244418004500b500040c00e03008400c1c41c82403054108424050041715404041d0304c13620501d0301c0580075880f105a2805c8814082248007404594510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 987367715 1250 987366465 987366467
    0x102030703081510082e06140c060a0915021207030c050c0a0f1118040f020609030a0f020a060302090102030708340203010b12060a09061805030d0605041b141612 71
    0xa00d2108400e1202e00c955036070407401c006401c0c030301030303114807001d01042e1080c6d032230040d035400c0c1900c01d44590070007070b2602032800c1c42d80c10025043c40c204c21074250020884850105041c0c0c4207407009100040c0c150b0103241d85441058008100412a0300f0611000b840748015003801040080950340c03048021a900f000740345424080c492600558510900e0400c0e0482c801d80303681c10b26594069048514803040c0e03011400426074030710941d5805a0580246003001c4244550403c289039181c0c4243da40c1160345a60320401c1b812800340e81842801a0002c10624010507092000f5210400c0101a111502d400d034140d00c40d042203011105282100d18280f07090103601e000c0c400c19205010a0f80e00054800e0f2170181940c8a460042040300900e81c0d800c424010300c40c1030740c064400c04d031030f0900c488005011414103035503903005107518950890402c0404a070505250164103484249003c0502d01407108545c10380720302c0c1c0112228000b0b20070501846085c003a00410440b1418050300c440c111150400d04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 987368965 1250 987367715 987367741
    0x301091410090b070e01030906020412050f0105060f0607060635060f06011112031e100501080c0a02190804030b0915060f0f030d18060c02010203070308151008 70
    0x10aa41d4a90b2030700c6600008107020080c03580d03020856241c508070a142c07040040e0018041e000000e008144041000b040880705a03e00c241150700400484840b034a000c1c8070039080c1c400071184150080000c0511072070a046c0359000c0c066241c810800803541a0700c9440c0e1181440007600c07000b244006441c1c214a2007501004803460150303030b10002d4000e600d41281ea486040801520f030504002411240551151050058034500c0c00122000c07680ca040840b0313110001c2d05801365130b114804000020901200381c4c1c08881d021540c041e150fa400f69a40d82c0c16401a41d04032034007220650080c1045102085486124a200140b08000c038948a6007035042c00c01403800020030481c8168071100e0400c941c20720200b0900d034405411250101036032448030216100841400c11160548030383c0c0b03d07000300b0a4214840044090928100e010125a1101c08884081c40071501034003681040003e0b201084c469404940c3c040c056501c101000c407a440c01190a9608205010700001e0f01c050034081c1d1130301344038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 987370215 1250 987368965 987368983
    0x3090a03091224150305010b1c120e010917030712030b0f040b060706150509060d03080403050a1124070f1e020703171801170402010c0c0503010914 65
    0x280545000000c6030703840c44002499546208041a5401c074001d001c0300c180e4000c0c0008520034104e0010150762890240c2c080e0624128480c030842110b04a0b0a0703100c440071740da075201c1d500110b0b01050308098400950703c5001840d14541041001800402c0798141c600c0140e100e03e903034500071070323803410641880c5000e9070307070f500d104002c25084c818000710950300d02d410525082c8d02114002008003403440007440c1807103a840010900ba0400100884240703c248025085802c15643c14001e6a20042001414044410002c020903c00b40100d030210313220318003800c4813000038108402d1014000500702c0c0707000c600b09003e071070000394086403003000034242503229004441c5092200d07611b00c458201400045141c5036445c000c0260000d40c81031340d4401c01820b1b0055400000345592511001d460f021581c4c004a0b042d24920300d1281c500d0000d5100d02c8880000d908009174070102d0780c50f194011651030240c0b20054030782258000001ca260380c0c080c404e842c0250300c03414428203031010b58140641004003807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 987371465 1250 987370215 987370229
    0x20a140406031a0f13050c01300209031002090d0605130602030114180105060403062003090a0b07050a091203021c031a0901060504061101020c100b01030518071a0d0203090a0309 78
    0x141d000c6000003200041e00b111082400d0034072401d0200441c016008400440c00c201049200102100d0304d124098ad00401400800b0360071394035070194070125036069200c0c1032040c580000c50b55a40c4008141903078071103504003442e249907026200302620b030001660400c0e04040028122030000560a1034203505100c43c941d400d0a8441c1c45600d44030004042d0b00440c48050078081d03c50195880704684e00090b03581070a4091012500c9050034080d0302e0f40d8502060040312802d06001c003081c0640e00030b100307994841e0032a5417103508036420038808406200221401b10f05521407280c0b44448003440c0c010074200e18902e5540080d1000544184141659a03145214018071624005002c82980042200c00350350242c205440c980300c002c03801600a1060b69141e4a250042444641e810081e5400510802e50260703010b200079240d1030b00000c01d0112010501049a000b00400c110a502000b0031038254260790300c0e114208003442c00803d0907a8421039134030b902c5411441c40b0004040c1c000e4030f00005041d403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 987372715 1250 987371465 987371491
    0x60602032a0303330105030a090f140313060504050f0d061e0b0a09023f07051305040203090c1905120f07062c0f03012a0c020a140406031a0f 62
    0x41000060010707c009004c2d114507640700e59803c010b00850079500d24150780d00c41410743d004203242c450075442e5000100008120a4060302c002180740c840ca05480564030010f12000c080084a410851003441d0359500312a420340303e4141d405007078064903200c4072030100c401000c2040c039002000c110b9092580c1c0c00c048062803060012400c2405586100d408100d1340f04a01c450820711480c04440d5000300078450003010781054100002c0a170300c10003030200da40381492200b040c1603c400810090340030866201d4000c0d4003d0405134511714090301000d104481c212400d22105032118040380c00c1c200c140810303103040d03440034514030303040e5808100220040c0018030b85a0301c850042c0000051902d2003903031014044040002e03565440d969031100201c103400c024001c1052040d19074800e40b0080e102014035080040d03120400500c54002c48112004030b0340241070034007590602d81c140426840070b0351960b4000755079075004000a40c80e00071907280c060440f0b0940d00103292050800005010041540d071521300d07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 987373965 1250 987372715 987372811
    0x72001080f09150a14150a0b2a1e1b0409080706050c0903010204090615050f16051c0c030215090a061e0c18210201030f14180c04060602032a0303 64
    0x1050514854041c0e260b0746480d6815002140542c4c500320b908404402d5041070823591031300042c00096410100445028040202f1104500b00000c50700c0241018084640400c2640300007a42ea5200503804080c10011501300030340080803a00326045a01311a070f00c10ba989009112071a130014810540070041d02c1d0151400340c0344a24920903000d882005100100f440303405400308403050103d101d40307841c501e0402c0000e410203040145a03040103403003540980a4100710000d50320b86060000d1040d11a030004150030f80180c0d984034010f000c02c4405280a00003850080e405d1f00c1240550000980701d03a50707822070070784101c4070b0b940380e0038940d40009081c400c11007194041c0b02c460454042180d8090030b0014010908400c0c06018004004101000107261410000b610f002c2c40b8280c00b54001c401c2c11a0440340a0500344401c07203039907000d0380001d640280300180394041180c1c41b50000e4440c1c24902610780841203800c2c1d140d500183c41c101c030000c00313100c08580c3c018800c03644c20000c880a400c82c0403441c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 987375215 1250 987373965 987373987
    0x30e120901050c0a020405272d1507090f0e04020d0b06010e0d12091e0e07140a0206160c020a030201050906072001080f09150a14150a0b 60
    0x3209920300641407201c0400c24028004041c4009030440343c01401c00c0c000b9180082d0945013060740b40780f080d02e00c868581e4a051a0442c000b80211404150984c107a1030040c00d401c42e000c0d40c02111503804404c0c41604906135501071140c01c020700400072a168a5002820300c80784003445001500010000c504081c100310142c2d581f07418103446c40c1e41004288549031140030040301d043e903042a8070b54000c42200c05143c108036030708040004180c180c6c0e58001c000c039294011505808280300c00c0881c0c81407100801c0c804001e194000a41111643c1441c2041d0441c01e02c20100541051b8070410160308858100f29443d080b02034000c4410300c8901e0305000c00c89199000480c064001e000190411001087c062400c0c1c5494003204c204a4218142040143c000501d80c020382c1512524103001901c2d00c030103d800a5118000d103409456407401034542049602001d100f50203004100c0940c1c2900c0d401445030b002240d8824501600034141103074549400982800702e40c03403070780d80181d410b040c080010324008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 987376465 1250 987375215 987375217
    0x60d0c03080d0204080a15050a092a030b0c0405010207361e0f0b01111504020607080318120415030213050910090f0b01080a05090109170a030e12 64
    0x35992041a540d19a400e0000020003801145c10000c2103204408034002440b501b4a40e0201780c0400c00014085a5907140304071040e02c0d1245030090040d0b034803107003100e0302e2441c24649480c0c400d41a0034842450343d594450007001c00050310351150f103100000d0180140d5038148010700103803448000c1c00e000b03009076405140700260000902858200c010700d03010b00085030398011462007910085076684298034400c1410003040d04031845080c482c07520110040350b500401305081428802c6021b4602c920554800d90030007400100f0403640b040c030401010b000600c06da00a14001c4062001207501c1c440d22048071850300e9560741000044407030070320040203443e25010340c0382844515803a01680f1200b401c1c107074850a8246400c0039900407030b80700404c40c6070209605204200c40c0e1076402800540300c149100c1c4200e500c3c680c0c206000452040004001880c0b0ba0001500112081d000240c0e40000f61507600310844103018039868241c002418145040d414003a00d40740406a0000c1d0003000e5200d6201480703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 987377715 1250 987376465 987376469
    0xb071106030717010f0e090a050a030c0512040b03040302211603210b030706031505061809041103151e0907031e0c08012009060c0a0614060d0c 63
    0x40380100000241840b40304920440e03a0181c003003c0003040b0b50312801004980e50107409a0f4404941501c0014010380c4000b4109228030f4100000d840c050100c2c2d1000c0b202d149040c51700340c0301885102842810003040c06c000b48001c0c140520141c0c1c490505280090902c400340100b031040348034913a1228402010501102c0c400103035145d542500c24254a01656082c82072001141e0303109861145054000c240d4004009400042701a0703020991200390a5045554040403211010764140081c003180c14810020880c00040141c0159041075040c0018a81d4030b04482c100e5151300784183d441c6c1641010440544080f8086494101344d01d481c45e1403201e42c00310400c2c0c1d20030020045021805401042c401d210141d508003400740320030314a42110f80c0c503040386a030007250450384180d0002803e0106100e01044001d94080b070403410038544002040030f40040c40840d03031081d003c00100384807800030402450342505c87c0720003143d10b0300d00302003180e07081e0001000b45000700b0b042501180041c1d815a00842 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 987378965 1250 987377715 987377719
    0x3020f120c13141518030102030c1201060c0309061d060c0a03031116120c0b07021c030e030a210e0a0605061c1b0509130203011b05040311041401120605010b0711 71
    0x9221700fa051410303601012403124040e09940700206005000501c50028050100400d14035203160760303288000c5480100c44003000c0e00044c1d205905000c280e20402c240c0700495070f074a50105402d1954000624554010102c4000a40c8550b0000d010590140204680d0440248a4030b080110402002c01440502c21000340841000e04c03804454902620b05800080c0e01700b1040022440d0a40c4040d6035580e804201c00506200f200101207220710038040d8034580c14039980554140408000d0580d4010803581a0464455084039500a0f00b0203500c9005480186200103000088590a08200b15000509007900841a0300c2210004000c0c03040e602c20455400000c1d51005078500307004100360003185e0805688105103170244441c070141a06225407981c000c400810805040c141350180240345c000024002c28020721003007012902c0280001113031600a0004a1140e00762084401c40c4e4100340c00628100d44140421024445240f0445014102045004c0d140c5840c0d62076141154400c240124 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 987380215 1250 987378965 987378967
    0x403080903100207081b060c090d0c080d0207052706090c070210031d1c050a122a0c0309181509050702150103110103020f120c131415 59
    0x58003500d007001500c200082c1e4072000c40d12018185001c9104d42c1c0320b1512200e05283c0c8445040d0001c6012a43c540200e0707800e0456403420001505000320000c0321138080e60510301240001031224403e00144459001c82d50103002014200010811f4032100c540714810105441d0b034403625541c0d1404081a04a00219800e40c841d503101c4400c2c52041c07282940094120000800301c10500303415400c0444c030051011020442844001400c0d541c0303010380c400a45a00c21841c03403103048180036000801d150003140c50148004843c00c0240c0c4162a50720a00c4529080c60800c880300c08214150401c5008450b0700c0c0001994199480c021701d0b0900e203008609140b842c1c0200c40c01003070103a40c06a40c0644003030942420595030b4045400040800b194400058028103081180c48650100414180d0394403440c0382d0700c0b10105000440c000e401c449107820aaa000b0400d0028101c509002c0512450b81102c07201c0e903e0303400002032046114140d0001e442c91520005081c050303564408107031b289100743c00a407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 987381465 1250 987380215 987380227
    0x303021b0106030b10060c050c01030509011805240108061501110114042a0902030606210115050307080a09021f030506040e0309010c0303020c0c06040b0705010b0103060b040308 78
    0x19408064098038408550702c2d0107000020018418510751080329800c84a8060031b541e01c10580c3c0640300c800b402002c0e6008640c8200881d80203030b100541140c184000000d40d0310b4801c40000b855081120252543d501103c4070005000226616101944013a120b1914651400200d669240c401134070103c5005182000011a41d10840082d480322240b04000e0107842025118050504400d80b003d8403a040f0b40180c540c0b00404000301c0303900103040c400035a004a490061000001c0d0405800164041820401c080c181e580082200f6400d000c02070340781210354900001801401500304c40c1c0c90a00c00300388108003120750000c410a5000140e103e01040c126882d200066118502880e680614072904040e03100340e592603444140709500070b4404010801d600b050310b03aa03e000e10600303540084c00d05058540000e12a40140032050104011241150001000944c01d81c000360007401800710302060311000d02c4009d0080510009080c00c0402c070711810070040101c40d20130b44c00080c0071420000780c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 987382715 1250 987381465 987381487
    0x302040f1b110c09010e06010e01140a18030503070503180a0e070c1a0c071509111201021c0f0b040e0d0c03140406020304051008010513050a0b031608012403030302 72
    0x20840d4043d0000744141c026603124500428a40740035102540080d81d0f0150302401c03540a00031501c020003000c00040e08000700036104845007a0842c1085885200c0000000000740c1d042020381651031003000519200c01245450800c104c07098501c01c2c0c86a601d0307400400c4005095690317241c04c40c0e0546003d426100050800004041502c4d5400c03c0c1ca551fa00100308041c0d01d204007506080e44601880b210f6480034525080540d092440081c010f40c000391500c5096152901080b0300000b42d03280054200404242030070200740388030100d081020f0b220200b0140c000c41d280f05410716000111000c001700081005607907502d041c142015010f200802e4407410a02d4000d03200340401502408826949a80ba00c10013034890704544241070180f00c1510088000031301501d00305042e1400508800070a40b5002c1c1114041c29018002c030b0615aa101754a1304a1340f01401407504036020910010300061034811580c0c2103603014041c03003000c002404401611101c060008c101140d4140c90096111004061 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 987383965 1250 987382715 987382723
    0x30304420b0907031d0318240f041706070c110d021c0b07050f090f0d15050f0907050f060c0c060408012004060c06092a0302040f1b11 59
    0x9080e5014411104010700550303d45c00c031058805681002e22004100c40000a96070b0240c1d10b02d2a40c0852054000c03882801e0034846200d80f600394004480d000c101c2c2030303000e0b0410b501004a0b40d100302c1b00098140101c105100201e0004000c01e8010041e0f031900c0c40000700348203d0044001c010005010442001d40c0d2015045c101c4540c00810b4512991140e20320220000301c03e240840d01ea5480c44005035015020701d09031412408000b60103441c0c15101c00400150b082d03807640d01e50303010424004410100d11140000c51014500810000390350411042c02e907119000144500c010b588501010302040d00c50b01c90b40600c0b40010394480340c448807d10700050401951541c0c0b41e41103400030800048038071054010f5041c5185244004042c113540100c9141544500d0184001240450f074001000a14980c00211442c0c06246101c004005281071b50a020280c01102548250b01ca1002d00c1036151501c40c0348a40c1e610200100240201c00100036420700e001000394090005041501c4401c41040c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 987385215 1250 987383965 987383981
    0x90e010c14030723120604110c06070c06140f0a0609020301051804080c06070507030e0913200303040611060906070c0b09070b1c14091c0507060e03030442 68
    0x10010f4513902c040703c03d6803017030700110344c400d10850620f8010b16046280200704c0383d100c0d0740301020340440e507107119003a00c507600020002c0b02c43d1030740d5810845107080703c00740550140d10001e91210031818203500704820764145802001c1640d104100400076a610710b544161901140f000c440001e6580d400c110301030340500085041d8502030b0000b007118055200c001000c5c070074407a840f45007403e00b1000500000c5402210111106c5940307507520000303d40710240c1ca00c003105d100010507041140c00e60100c0c1c2940c12990000000c910013222210090400307116640c0e2117096100207040c02c1c9001c100080c00c0340c13149203010380380c00b5004001c1760301e180d000d00c4008040c05000c1c0196075038044043d133101c801c041d074100c03241c2c410780307000d00f40c00c08008100300e11405908500d00a00d03401c9074031086960b212031b82c0c9003c030b82030200420030440001c103940545924000094080d68507485c0604081c0f26450002100075010200c01a180303c2e003420a03508087d00c084420399001300e11a40e0f820007401003500d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 987386465 1250 987385215 987385277
    0xc02060a032906030705030a24060924030903120203100e010504020a021b0a1a03010801110703020d030f111602040e120904050403020c0a090e010c140307 68
    0x8030105a56010303002464004050102c802c0304001c101a0000e5110103110001d03801003040010801841c4100050341d00074620442c0000d041c1c1c5a000c4010604e1144406d908102c00b55540801843c0d4018410100a040c90344e040d82030450021701121202c010402e04c0300a042d5036101304000e2521aa026001f0748011101c219a2410240e503c061034102621407103054801410010910782414000c3c0c0c0d070492520740081281700540482c26201c180b0803020180c0004044000051107403100010301c5000c0055080d0710360781e50614000e1829140411401c20882400b00688000281e00103030800f00342010b40b400186a22209144d0406415840e2020034012004980c04100e001c0e01c0c510840310701d200722130400c0054402d111042e100c100000401402d40000e10030788603e400d040e040300f58041d04c248141c880e00c400c4600000d0b030f10895a0004900c10380c1e2088040d00300c1e0310034403c5200391182c41c10711003c20005c5c3d8030103011502c80100f8280800c2a001d44000500d0407001d8036103201581 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 987387715 1250 987386465 987386467
    0x1206040b01050c0604080f2104050d051602130b0402070b0609070201110f0d0f05010b0901020c01020706051e0d0908120105010c0f110a0302030f010e06010f14091b0a03090201110601060516030c0206 87
    0x8c1c5803201c03554800b518162024000d1505101805004500700c68508a46459400040e55580c00b0042d0441a5204c8110440e40742c40e03d03840c1503506d5200030300003544100240340309030400383c1c1881142d01000740480256807410f082c0f040c5028000090b00c40355813a45404c0344c2c2e100520100313480501501160b02da804e9080c0310011964141d0400541032040c02a400c940d03500618100491342ca0680c2c2c412500403d104200c03244001d00e620310300f03405840764522220310b4104075200000484085480030303102c00384085404041d0034091040540181424600880b2021107030300c481d01300d42d800300b03001400d40503131024801140e201c000d100802960002d0550f0380d0114101b990902800d40c0070700d5100355010382d40011031600410003600054504190152030750410480c148070314110090314544110240c0072444000d160140001c04000c0010755001c240d1801d0ba100141c0501840030410036035400c8007006000465011040d030b000703010031000070380c4034000c1c6003000d4604444116020f908154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 987388965 1250 987387715 987387757
    0x40309090908070605100f120203010204080d08040b1305103b100e070603020c03040e01030c140f030d230403060e160e041203020409021206040b01050c0604080f 71
    0x1d6000003405215008050a2010340c0c6c0740b2035545540482801020180400d2000c10301c490078507019459805e40c07014000528003134075203202c6445c2644c040c10b07810006229104010801030702444090300465030f80c10801c80c2d80c410750b9405458290021046c4c0e002961825040003501e4844081c0007611911045a01d200d072405201503a03800108842c90081d02c40c40f4010748294481c0e10841e8900e07945400503107541814520200d010750f1141402801612050001081181844000a00070740c82128004082490b000441d5214603807014541d20548a183d00d4185075180031401c41240501c03407074101c2d01907506a0084504440c4a4400350b4111004540482080304603441018000202400c40da1840c0961419008071516800344290420700394011030002003240183c0c0d01e0550142c240542815203030410780f000c90f0007881c034001070028002c0512151b814a8442d08503824000e01c0c02601d02007903c0c00c038a9640d8400740008180c420005800709414002e001918000700100a0000c0055 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 987390215 1250 987388965 987388973
    0x10020105070e0a030203060a020a0905090c070203072310020f0a08030f0907030521040b0d1e021e090409060606020d020f03042103020a060510180b06040308030403090909 75
    0x18044540c00089081544080010700c0d050900f28101d90340240104031580d580940d440181d0040840d000610202100100c0c860751411407503031003907080005164076a00b003401014503056656104281031584000c020b0080c900c80c0c0c035100c00049003641d5140c250040c54500f2440c0c1740c0140b2012600340143f0a000c030401c164000114080c5606015080b03140c0c1383c0ca00c06548414143c80001c14a44c03015009202200c0c68083c40e8030008040320307144e400c1130703a200020091750f4000000314030321503a542e10302e81c0c801d20220054021407400750411800c0c000000040e203842208042480031108000c80c00c440c080d500d503005050700543c030035010301a09a4540c0089e607140e00e412001c1001d8040c0e1200f540c03000900000390340c1140d0617250210211039401f00d00f00643d4442010a8086024045803100170a010b4003860307014083e05440c02044502d0030034000011568118020203e03070030180503520542d0f42c2800c0d5000d6030f0300308110325030ba070316641b03400d407003060701da60100c020141802c0c0e400e8180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 987391465 1250 987390215 987390221
    0xb090f1311090901170d0c14060c0a02192307030f080a0818070303140c06090c120f060a0c0c1b090b010f08040314130e10062604060902100201 63
    0x80d4070191294190b9980300e004170400c0803c0c0508074255a48a141003004e6644200002214503006d0341c81058011138000d070b107900f409001c039030703400404500040b07600c20309904002c015070702c440340105102c500e586c3e69605105140e043c0d042c4101c4024091192501130024030004000f180c0c010f0750b14020f8800340c034002c10b0a07001308146001082d40300000034140c545c2240d0808501049001404085086a50940b40f046080343c1d110f0b10004140004283c900d0200b00e01405a5800801404031280d04d0040101c01d41048600415a42112603c80c0c8010000200d0036004403262002103050b076060038044986410b035402c003500d100c10040d04000580b56400761031003030b200740310024840b0901080064441c0ca042d0300a8000003450400064003003803283c50340000074580c41d4181850b00c1c0d860094020b030801d5540080021500343c00074020001076102c0d0100040c007090506042e810541c1141d107090036900702c0e41810441c42c010000d01002007640c00160b544e540101490782c50310207540000d0007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 987392715 1250 987391465 987391477
    0x3080a1d0a03091a0304020409080403080a02070807050f0102060c0307021c030c0f05030606180609030d0905090109062102012001050a1d1f1401030f1505010b090f1311 74
    0x8204042808141904441c0080f104c0400020020703203961500da00303000041060850940f1740740014400800050444070007000c1941c1540d008003242420100450305220182e40080e00c514000705004109076004120f495200c03503110307445c80c2c4a5544600581c10301003500142d82c2403070302d40c1880441c5a0b403d40c1c40004020015074550b414001400004d448038441514100da00060922a02d4081400ca0007a40741900e0003511a0b0b05040740303c4e021a2401191a11080210348a150244218284025110700400e01003005102452418028403048c40b40000ca400c0d5902d40c00c03c1d030400756405800c0c01303104080d2000d840c4032460000440103008003025500390314801c4c200b04d109406c40031f01101180d504041c4001400300c20075422070004140010a008408098442101184140091301c00500840c00307804035001c2d850403454041e0000f4003204607900f01c58a048014030075240b000c0261441c80c04103540c6189201c2c80880003c14040b012800340318070504082842191860790f80281207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 987393965 1250 987392715 987392717
    0x206040b0307140a09140f0901080a11090402370e0121021318050a211b0210021614120712020f0a03170307080f09060403080a1d0a03 59
    0x81d00c21410700c2c81c0240d0f445001610400564011001d0056000005d0110020400100703000b101d140c03110b01090340410268001d054035040100c40c8414085d402000c0064000201d4100850307141540c00160f0103603044040c4580c150441c040031a0909503204a186008402021a0000c40c0d40e190f51408a441c04d000d0201c0030013c010301141055032020605052a500510715134584004d440c1c0074000f030414050101d1000d42d19140e000100f001407180c00c2865010b03100004c07401031003000c602c12000c4400e6040082186c8003000196000051321505003070f0f0381c1210340300c0500c0310185080346094250303c04041d01c42110400003400341e2a6183c0c940e201c0a0584d450400c00c405003110544641c0103115900c4803402041c05000103150401c4840081d020040c10b0501c2291680c56800e1202d003464450001d03d1000001d015000382c00c5442c5a03400f48201c40c41040c030345018020b043d11a180a0402414000403001160b01000d064100c04404e41540090403500040300006960304c44100d071080e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 987395215 1250 987393965 987393977
    0xa02030720010b0135060102070f08060103031b0503040b090d050f07051302070b0604050606070b0108030a0806040209060909220b010312020609120c0a060c0c0b06041b0c020d0206040b0307 83
    0x49030203c04545c00c0304650088840500f0000b0309075943d01ca645100500d150f0450150306004940d01d44200b500201420040000b44615811841c020780b0424601b1014000460310441e0400029030000445040e1041200011307100e0318840c0c0443c070aa10803003801061400365503031a4100e038000241440440380e0403100711011000002e00541240310b8402c0140149807075000040ca0303400c143d001309c0d801c4940505a9403801032161030b807202ca00800e800c4054140c000256a1514aa1081c5c04a0704480d080b2011490800c8880c00141144185404a40282000302c0000e0701c9611403403100040098280130480200d10310714060703038148024002190724640040403078200d075100007210751040d615440100312a4070514401c40b0b1903005410802e00500c540010500000c200c0e010b468109402c80e12808501c114518114420035030051000340214503286030031000b54000c040450201d201d604143d528045c4038008224006000000a50042d000040000380d40410350003c0d84983c2c4941d07104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 987396465 1250 987395215 987395237
    0x80f09040e030a17061c080c010524060f04060305040201122309030909011a2503030e06070206061c06110901110604080d05071205011e05010203040e0a02030720010b01 74
    0x80880c1058803000e030010100800706c0d16140305000b0610089000704480c034100950000a0390035520101e5100098000c07603180c10b0700d01c06071944000c0650340700b12841d40c02d02c00d592420b15664056803040034100341e2100d02060541e402041000c038508441c000911502103a5140b091405614a00892080d2044e0300001d030b51400c040290317164201c0090250070103900e0500000c841d044484a1003401d144200701d4000c21a0086211076585100c6c4d2000d111054501c0c1006002c0750120b03442c3c008030750008420800c0d46a030110741c0e203a0003c2c04985207101510000002c01417030f42001402000d0500c1d003800d40000c1ca000740c014001c0c0100c241d84440c00202d13030907034070b030345030042903400521a410500620052080540010b9840301d2145040d09100080001110580340d081e40480420650b42c43c0d144400083c021510300900020b0008614283c64419038940420b4020880c40116074040041601a171040000c3c3d41c0303c24454401d0010044900c89842c000c0030130350503480c04500c0040032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 987397715 1250 987396465 987396497
    0xa240e211309021c0504061b030203070e060a03063507030f080d0906050f0108010e07061e030b150c1005060d0f05190b160507050a080f09040e030a 65
    0x84a00040ea020303403100140c0d18008501c0040d400c100b50841000413900b040c2401e00281e0f11a5a108500540001c5400414100d190700c5a56220108a082500400070045c0e83d0780c01007000c1c5003000050380c00035590450320350210014481900702404151090040b001030400030800d03076003481c03e001443c41d00c45109080e070940e00c801d0b03440000c08075088403400784041030a00014020203030440501041000d01a61448100c0717408a600c4c4500014500050007402000d02c110b01d18002000020440070341403000c05045001e042401040c15095041c4009145120750041e080040028040c04280e18114070444080c0d0080c1c90f96404521410003401c0303083e41d140c040c3d14020b40c0040c02501c0c245903a91103003021100d000800351101d1250303040d0308000f01e2848034071192443c041c1000c0d0801d07041a003481d8030ac1140d906000c001b000811300060000c40c1c40410300030741265010b00c0b4140e0b54145200109038500031052010f034800d03c2e0055031800c42c0c0b008402080c5044a0740c0c5d4919002801d048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 987398965 1250 987397715 987397717
    0x90f0b04025512170406021e0c0a050d062315010c150e0f061501020105060307030c05010518060f0903012306060903011b1e020706020a240e21 63
    0x45100a11210380e181045000010a01510f140307020b080c0540340300070843e0100800e0361141d80a400168040d00c2070b1105e0454000c100609414401d0260981c4070f440c0002440840c601c3c081e192041c420704400700100b103180d80c80711032501080742d50a40001c01d21240c0d0411104101c442c99a052581e200701c594940c882c00300c01c510142d0040f542c1002446a0640800809101c2c14900d428810f03500a00c01408040190034030a100d141c0f1045801c54040307000a003510310281c007aa000e0380c0408403e000003a8142600c5040e58420b20300760740ca6160580301c040403452466000e503082100041c01c3c00b00001601c0050120030010340003400a2003c000e209070300600d80c0126649510003070004503815182c4400140f006510080002c118104031040000704066000ca0f10340111b003004c0c1180d448061016080c04108000740086d1080f107281034406174540b007503920002c0c41004510485140700900399041512120300341810040c4400c0700501e03035981c441c0c9090007000d000354403401503d0810405c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 987400215 1250 987398965 987399109
    0x10e0402120f0607033306031a1c02010215040813081507180317040305070e0f0a0b310506040e03091207030b0c0913090f0b0402 57
    0x141c010078255582d81000c60003000c0010708000c03000c10002c8003108081c4980900443d00d402c1d03404800800341fa2003070207030845040e400080c20401d80d45d1800c81956a4100c00b20501001da180d003160408105e00c0103d0401181d0103400030340101c3d8400f03000c14403500741d02508408030020910f00ea140e4880002e15034401b48046840e1404d8403502c0013a00c01c070301c64410340005403650030502c4103042c1c0f41e503030361410001c0b581d16074003110704045030400502004000b40801054045401189414482d0083c0c4440740001e210110250300d0704e024140944541d0165501d010000481207403542040b0b01414601512483e006061420540400e44a2405100e12580c3d010880002c0d440c080c148002d1000144a000d501a20390084560010220301c0142907588211240044665100342440402c10400140d920a0072560b26010201c000500222501028590000b500ea010399940e48000303100e030011482840190301110039460201c010b000818000040070f540b020003148100c181c0f031a091916a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 987401465 1250 987400215 987400243
    0xb060d050d0c033b03071511010b0a050303040b030c2b06090510030b040c080d0c1208040209060433090b09060325030f031101050703090b070f0215010e040212 70
    0x3641c4c0341c03455482804004034130340103400d0b110501ea4400400c10759201c0c61011401156050b4040b60f80c039003080c8a41c04565004817803600c486801d02e80865940d01a5000b14000c140000012807824071000d000c2c0d0f43c0440003d04941c0c80c0340c201c02101401030007107042c040009818040c0100e0000380c43e0007010b11502c1001180c2075854610b40310803040380d0014205403000607901d20b002c90440002d1000c010016446c2c0c582440401551800040060654440d0300801401006000059803080340946d0000030031640459440c80e81660701d1101c5c03402082628000707040d540008041240c50b00d100046034608501000030200a000f8030145200445080e1740c1a0040003586940b800f81200b1203003200012200104419200d0380c803603001c1c1d60900016004038404070503c9076802400d0048543c4845203140a004207172055031402c0c00d0a070050140824044800542c1403260b10800000c000480400110b982039659a04004041c0409540c164010034041d00c084000440005202c2c42a42030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 987402715 1250 987401465 987401537
    0x2090a06050f010f1214100806010509060103020c0f15090114040f0b0421022b0c06020a0509091e090a081602060909070e03010c03060807030b060d050d0c03 69
    0x180d40110341c0d84d0070811292080c058010008043c140c4a482500003200c4012004009414045200c40c81101d040e480b041c2d0710f0b0b12040042c01107071551214240c10040a080c05038039411004140b90038091303c0c1107030303031454410181c940c416401f89480060252042900801141107a4160030480703000032240509150009080d8100080000a20540c010700508c40d0032801004001e01803100f480300000c40005900c20130300d00c1c601d400d920b822a503404003462180040d40c004020058104100e00502821a40e80408c5204d000d9006038100c070309982000b446100f9502d0300481c0d6161141d08007400d48154090000001c00846c0c00040b200304264000710396a00b8541c20071f54141c102034040710120380040d03040c88007600302c1c0c649100d04c9000b440c42f5120292408040d00c1030608480c040c1c1844420142490420001d183c008209030b002c3c3c0350030010345106540d03084045106216100d00040042c4140442c090050b548081281905403181d6581d412007078407481300910f01030488110270038080d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 987403965 1250 987402715 987402739
    0x60b030c0d0e0609100b1813060608120418090206030f0606040308030c07030e03030f0a030b120a051f050f0115020c1f1b1a0a0605030601090902090a0605 68
    0x80c80160580980d10400400c0d1003000c00e01041c20b080d010f80b088140d6a00101481c01242c0c0f550144200036807090b108124800101c00c8070021000d80a4000ca503048911503205051142641081000d44840001c46500d083d0840d140802e42e40319109905441000b40140e41390841302780502607a440d00100a1815511101201000d02001405060340058200000000210340c0c0000d14420300d20310364a103440d5491800c000e03211340d02d1425842d2298104006c50485d81e5142d4003595150940c503e00011030001500118900c90b4092800034240e00c2610350610400c040052141070f183d54907115402181e152070166420b642096405e1001707081414010b11008000180d0600d41448510441c4c0c490203030100404c10918a000100c100da0014031985081e8680081c80845454600c8410140040903a00c071208458407543e064401400c00f1320100780c651070503402c01d1003c4d28005003030b0303451565900d514400074420200100c1c094069000041c1194101c0d01c5000d04950010b04100285a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 987405215 1250 987403965 987403981
    0x405132a05060c010e010f09050d020f0d03020717030405010510060801030f06020c0a060905070602070e06061602221407020d1e12020f07021c05120f040306140415060b03 75
    0x140141c010050f46650700c0e14461401102402414003050101000040c000ca0030304066040524450000c030135035004940032407e0260003e1801b038400c101d0328006803628082d145c00e2040c00200600b812000170084188801e00c041948107500070005e091031500e1569a4a5040d42e8030502480050441e081001940c00801c00540050101580050640c0c04c0280155541022295044026038055200160a0005036010042e8001a08031400075170014500100007604034483c900c80252a01030007404c0300c0854446100000491101d80102c4254005001e141c80050130003c20059284401c6408a006103001141d480c0d1a03201540d2110700440e210703101d9001e2105a0041031041201e400c0070007404a0711840a422035140844847c0e983e41201e0040000038501801c19140c1c0c9a10201310b500010400502d42c51004018503405031625201000c0e018540942e50024010605094145138030b5409202c16510a030310038108071128807840050f031803c0b11058007070300c0000081000481da0385 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 987406465 1250 987405215 987405217
    0x70f08040314040b180108010f240915050309010b0a120303051f031b0b040b071218060c0b0a020a02030a032c07061202030c03060f0f0405132a0506 65
    0x403081095181c5026a04d650030341c500e50049611410394000c3c1581c0034401d41c2e200001340c0c01840c2d4540c01786041410409080812140c8803540c1011000800c0e10600c464002d00c0040005c4c00b210641c81e4002d04414005001544102e4181c0e84031751170f00003243c80320f180015000080c0c60102d22884040c3c5034030f0b58190300805c0c0107410400704100281c40b4141c0040c02c4414000a54420510301c200d1848007031401d0000c0182d40c0000c0c00060051005000391051441907900303140c2c028050f03e00d15245520180c9040200140c65200244038000c0800d084e90840703001d41c0c0b501d12a0200d0003550303664914160881c001d0b200c10070010f030410401a1102803007608680d08001d0708030320080780e06800e0070451402d107040b44104400d40c0c000078000c1081603001664201011035448055143d441d0820469a2602c001410148078103200c0d0541000f684a660324801d0420014100f00610305040b150b0024030a03118104440180c050700c140d12000b0400c95135941c2c0c202d1807032105460300e81018104081 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 987407715 1250 987406465 987406487
    0x507080c0706060b1b0f030f250b010e04230d14090a0801140901230c070b07021e01090b0105120f0102580b0303040311010305070f080403 61
    0x2c10344070350001c20381e010098000d0030f082401010866507079940d8903020742413103244000003c44c0c0e0418820301c8101d200c1602101c0c1002541d040c6150035480703810303000c080d403012042c1c0a00940141c40000c5842d00c00c418502c0c0c043c600034105a1600100301d91120f40084a40d010030b03074190005e2009a40c0640185205051065003029aa0920302401c0205021030070f55400b5502d940c3d100d00426108210140080f5002161280207102d40801503140c03e0a16001504184202443c4000602d141028806407107401da40301101c1d14050a02031402982d9007401c6800c1e034548086a048d1301c5d150101480ba03080000d0b0300c04c050401c04d80c44c0608020698002c07c18a0038140242d4594908024080c8003d2074948204d009084c0f034a030210108050b80401049010740303a140c2c1240c4202525a920200c0c980d044c410031803090441e0601c1c0d504400b42c0350352403805c0e07054400840c010003041001ca5800211031420b80e82040280d071000d1080703a40712508003258001c103203c0c07004070707001c030b03104e0710104034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 987408965 1250 987407715 987407723
    0x3061302091309060c0e0a0b0f0a03061203080f010906050d0210031509050907150e120304080d0e0411070b07050304021c03051308070605040506071707140f010507080c07 75
    0x1031189941c100c18095411409040702e1941e0303a820345e5400107811101e0004030300007d81e540356040c1d0134801c6441c002d100d0a102482c5441010800e012000d1103504a600502041c1c52000ca0151344ca03e0087c1a01c0e40a6910f002100103400000ca12000c243c4580000c0340c034003c000b580804555003c0c401c01c078164100700020103481d13001c1ca05141c15000002001000e8912000070340d8a800070300c040c200380003600401d01c1102e042003224103103603019804451613101110b42c0343c1001e01e080d11039455032055900c03110390380c002c643c02c145510340c21104907840c5600580b0b060003c0004661801035038814044001c01e45849c40c07000c6882580b1860142d41d025102030940040c48a22000f2182040004138045001540000c1c00580d1400094000b100078401da8000304000c500303054002d00300d401140070b0b8500405000c40e904050180c0d40d1907454400c0c0c0b4040c051507482880382000c0484010902101180380b0030910b050600c01d40520580d0302c00c00315507540300003a882e91000d500d21940a410f06231 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 987410071 1106 987408965 987408979
    0x6070e060306010305151512010f08070e0a140a020702040c0206011a210703090302120306010c060902040b10030203070f110604060509030c0f0a1104020306130209 72
    0x2d800503401d007004502c959808000700138a412001d00240d100550313041079003010711150300500c0c0300d0b04049040d4940b40c2c0c88007a4480b00c03140d207106980080d8000c4000304110382c1d222042a401c08000b030342c003040c0342d8610b65926001540075107854207415030010300407045107481c0c801c41c098002c03a400500440d41c5401c101d0302c0d0408a80700c00c0048803a0005030129410010300803014006480e04000300f02e4145200010000d2445c403404402611906182402c680518007d0780d106000595414859680c41d80e90b8501500d402d141c00c0381c00c26260410444c083e07840c50307802680c8041f155001626481d021200030820b00031040380c0d070107104100480c0600403101181159000344c100101040f1500c0d40d01086195200341e40200b01940581040b203041c1d81d1010400e040035601450014100c0d0154030104022032006560469004006001e04106a030054002d0701340144014440 = true := by decide +kernel

theorem cover : BRFrame.Cov 987230215 987410071 := by
  have h0 := BRFrame.cov_init 987230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 987230215 ≤ n) (h2 : n < 987410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
