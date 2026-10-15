-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:39:54.241973+00:00
-- url     : https://prove2.me/submissions/e7383997-c2ff-4941-870d-08a7bb1e7d97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 912949640 ≤ n < 913129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 912950890 1250 912949640 912949643
    0xf19050d05250e010806060d1407030c08070e010e090a080904111b0d030905030d02070c0b0d0203010e010b07030815030f01150519210501060f030317010504020301120b060a0302030a 80
    0x41281a803603c581d094003900160041e64480d000302d024000543c490740d00391082c0603800400d0204080c900c28000340f4000c00ca0f4006400801b9a032400503105e580842c03c84180c0b802c1c840310340c103980c0e202d81504040c8413060318180f020f0741c020404000420b0400c03019002400c0d00820200b10284100100e20b0f181d00b04401081c0c080041d20b911074903044013004003540303a00e1036003001e10903012503840e6030340c4034003070b600d00d0620194000521108001284601c00050700a031000c2a40741c6507074850400c02500240120000c0c8000c1500114040d6050000d0b1495603070325640b1168941d5509648000f007040309418507406126081d89017910300405e0081d200f800d0b0182e4456034505142c030702040f030b800791032040c513601d9034003050f1041c000e03030a4104001403222001409140100c03014508107005045c0c030f80c02054a08946100841003650007481c0d08610043c0d030a20109990726403040004078803003031082d0481280826a460005a40000802ea01100c020201000184c2e00e8002c20708200300c4090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 912952140 1250 912950890 912950953
    0xa0b0a0c23100c0e0d0c0521010e070b0f13030501050106020c0f06120c0726040312080906011a0705070b0a09061d37050f19050d05 58
    0xd074441c4050701086102c02c0000000010b0003580c800c00f42c00f505108401d05801c0c012248140f610060002d80200c0f0350007024068101401810000e606440050030300114480c50750038850300c02d00860001a0000030350fa00d22000c54604500c400e20301c0303910303480810b500b1540f403903589000011810a2081301d0083c03003507801400a4441c1c08041200f00d330581c40415215000c14081c12910a0300c040c807099000b481c07001103668402a60402070204107800c3d041280c0741d040109031425000070400608102d0384101d114403100354002c5001e98007003000b21030164503680660010041502603e403280701034210300c04000c2c5020781c40c2d115030b8140112a04180c840c0c51001404228043d070042c082c034011300d81341c50454208840210b4120798441001ca1080c4540d010040c0805144140340e0301015000340c50a200c2c440410b80701202d0259561489440e1141110120140345802d100480c1c4024a20360340313902d08124100010442d404003110401c1d11140302c0e4400c2c1e0000b000300807100c1940d00b0582c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 912953390 1250 912952140 912952193
    0x50d05090a12050d1112060f130912120c020d081315020405010809070807151101050f0907060314060d0821010e071b2a0b0301080f0102090a0b0a0c 65
    0x42041c405e460040e02d00f081042010001c002900c07405143c400e8000710219102c41c0c00d10850000120107c402c0c4820740229131402050004000180300700610108080c1c0b612004d180342c0e229140100e442c40199070000d0381214103841c02e507a06c1580081e41c00b0308050a000740562841e19852000d010741d040040c046a070025081c4155030300b0103c401d074440721140007001c245081501e96a00d501641c403130000e012a0340302c4a030700214000e0b0800510605001c000b048949081e824107120f0080540722500c145c040c480010800c0340c40303402818081e0610440501c4141c54500500000113803828003035030450350900110100510700e056800100100040c2c0102c1d43d41800d01d2041400006000781d02884041c1c500c0f4103080c0b000038280030202e82c00c02c40c80689122085001d401e0b0340c480c0c42c508040518108804074207111070b8005541a12501030840e0401c84c2691003440c01c030f100312031101d948280140020400148100c00800070320507149040c1d5040b42e480e0b0f0f950b09080205580d030008006002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 912954640 1250 912953390 912953407
    0x20a03050f130c120c051c150e1207170c070f0b1303030e030a230f0a170d020903011e050708010609151403150a1401050d05090a1205 59
    0x18400503420400204520808980b10303515075004824034450048407101c610125010b1000c3c06001800511002e482c0c04400503070112000107000c04080700721060861a000c140044040f4818002030340c00700001455100601030705605a50030408d0101c82c8030a008000944580655014001403c0814018601c0d01c0c140180c00e035011005400c030484000050019040c281114800030301200c0e054284003004036410340200f4200340400300090805520b868040c03107047c3c0c03000089407420201c0c800703071000c003a01c00e00b161b40c1314055000081e02801440b0414880501c80000401c0100b42c10074006141c15500c00c040b9083d50b582400c1540b4400b0303024542c6480c0e40a602505503c12502e28142c0710540c100038002e081c004060098071a4069200c280c0c48400340540306114080c0d802240f82078503894040d0401c1d0b181c0250030b0000340255500980000d03540003080c118000018161252400e0102044002c4001d01c0001e00640240c07150903001c2022405010217082000740710307950542c1e510520b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 912955890 1250 912954640 912954661
    0x1201020703021c2d12110307230304020603070c0605070504090609051911040306110315060f0702040504061d01060f0f06120b0411040902031909020d0321020a0305 72
    0x3949690f5091004040038410019400800184205444542240c0b24000d00004555200d201030340e01040c645001c0082d500d45040c640a18410400c582d0380f103c8a020064000e0310a1054802c03403210b0100c01e001240043c988032000d543c0c0b06500340b800041000150b112001600c2094070b15802060700060140419812401010064686504280846e081841210325621610140c00001e03c0c2e45003001c2c9004902d90003224000c40c0c01c1042070017038024a0b84000416801914000344403130000b2903601003410b040d0251002c41d15100552410b02c035071602840094100107000311005591100790300a94140c00740c85011040c0b02800000c5c00c0c0c1d0403c0c8464181c003940750040c0ca61004005000c003c01588540c06507100e5402c4100031482440710070200340545000203962000070b502280101e020826540a988038030781441a031035180d28101140e004548003c000650840320410078100407c1c043d004030328004d2526204d107030f801005c01510804a070400d03100341000035110410300086520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 912957140 1250 912955890 912955933
    0x7021003050103033c360504060803070305070f02120a0b090105060d020103020706140403231201051909020a0507022806110106050415080d180b09120102070302 71
    0x118000d031541d44242c0040c4001d111070703c3c085c0c500301c0c0402e030303101051081d07116001104089402814241d02c00500601e1031101b030103613080300700309a1102e1500180310700d800d024a0003100c0c00500a90301c0d0203c2c646007203c8a9109290660360b17421800c52040060711042c1ca142c3e03841c440c04014203613030540d518010511101c00740610055078145401d0180315a21651070a41e0aa4242401a0b0310744007841c01001401c203039100118030a8000b01004107243c5c20442440090044034a140002c3d4050141d01e400f40c0a0400410220040d80d001404507061128041c1e903854244d40b41e106006d070b40c460841c2c0c02d0f03a00103c50200007a802040c82c1d011410240e440019025032002038402811100800fa5450403a40c0705480412040d90160717007500c0c000394018405800090414001c4000066090300518001c0c030910709580305603011082c000344100f520b84400380080c1403400c03150345001e02050154000038615a40f001e00317a81442051a0244001c4c1001d41c400e07000b4181d04804070101c40c02060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 912958390 1250 912957140 912957167
    0x3110a0c031b05100c200c03060c1201090902030a060504200411030f041407080a0309150c02010f05091e0f0111070e19020706060504060506040503071503020702100305010303 77
    0x240180307164002140418083c018402005001408024010003290400c503600342c1b60312590009a00c4400c4480d000c80c9034001c020341501105c1c0349440e4060450090320580101401c0481e4083c014418002203030480c1c0c281078001821280600c0b0180c489200302c03030381964121002d981108640302100ea4881000c0080e80e001c9804005048020794035002c42d21000700407001c6421040009420005c18804441800380d0100449154072707160744006070f0300c1c1010b10056002c91840c05e0001115071000d5008000d940c450390350002c4d8800c00b9030054800b9034203140d001041c17010a1003100080d4035901108000c400620303c0d403c8103074900405214607000303010843e41c100582411400300403100054008209c450319006680c0550302c201d0420b442803401d00460b6011030000030054184462a0014402d41d541141c04010080d5540c040085503c5035100301905034001003005c0060008040840003241103905000d85448a160b0000310802000010354011030383e6a0014801e0613404864403241c00b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 912959640 1250 912958390 912958427
    0x80a030b15041d041a040605060a24120e030a022107020d082512030b030718180f1b0b09090c070f0203030c01230705040b0a03110a0c03 60
    0x1410290765825140304002c000c0c01e0200c5030408101082800c1c00100310b10176400760541820300b440e117425030181106407000b5124209001c80828000c0b2041c40403401c00182e800d801892070128141a03d05008403103180110581d10381904148a800380020704c03260b00558043c110310b910301c4080b103881c59070010030b040f10008207000f0480180c42c1c0341541c070500c9401c87c1c42c040c3c0340c6d82d908036400d40104042041807140703400c060361b440810031107a492100c13210060301e040c032008240760f00f03160ba660541d108003480482980c8541a109460707034800c0b0120014070011200724a400d4880c0040445014411a1600302c2005c07041c941c40800300c8907101802d0710780c1449261040c2c00c0c002400c80440940f001d244540c3c0043d08804108031007000d02422580601079036100c4200e1002c09000305650110908452091101900052500059540708400b9070302c9940c00c0a0030a0088034240e0014110300e81855030743ca00030001619007e010b88910b110a40e10320744e4151451400400c00c501c00c85821510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 912960890 1250 912959640 912959647
    0x151e09060907030f050f0d0c1e0201051b010b0a080d02060901050412260c0301080d0e0307170312040b2e14012f0c03060114060a0507080a030b15 64
    0x1041c0307022510004894129000c4218106503041403130034016283c5000107140302d407041c0f00310003542080004040501407100011a822459840340c10480d20300c5000780000c50030442c007a142600121315103007030455580001100340440e008a40101c0140c3c00c5088217502c0900500c1206038100441540640103070001d004c60308141d0341c0c140790740c1940c422a0b01404594024000540f860366100e14004d0700d0402d036192a070600120100030f0748d00a000d40b60080c041d200914074090b00034046a035040078040c009060503480c01050149030529420300041d54001017098105140085001c180100c2c044d20f50044542015001c941c40c85520045607507886c03040c01a10040c3c040a8001d540881e450a44401c5074460b01c030004a91458001300a03092060090306020215aa181504c4840281d40000c490740e44400700c0c201541c4400c248135403100080151542000c0d401c000d005001ca0407014105642040d40d140d40311800381e000034041500080e0351f20843d0780c0c60301d00391501e46540020805403d16 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 912962140 1250 912960890 912960901
    0x4020a06090e040807081213060b01051206040b0f0907110c011b03120605030304030606030c0504020301050607030c02041d0a022103040504180b1003150209060d090302151e0906 78
    0x642c40c00208003808504020030381c1d10a0080400c2102c0220f4112035503900985011031364503403200c00c81101030751054030380b0320344203815401034040f02c4040d8040014424030f40d41e0041048054500e16128075004941041d03134034000d03120441e0f0703103024001640306d403420501110340140c81e154203c03503241d0400111079132041c240e158a20b910085c440d098901025141e207104420b10141011b0350042d90113120028001042c0039203071b0f2140781580e101c1c040c4052400d03036075403c1206a01080c000d07158084820810000040c2c05041441c04007440940081041e01c40d02c1c104500c6842005201241500b10450b00350451505100b000030604218208100c8000b80c000107983d00d015071300500e80100ea8401c564000501c6017028000e030f095005071080958940803040200c0840d1510040350700c049460803454040150f4003d03600070404c05011315003451004071503078029089100d4160f05501808001d81c5c1d04030388800c50725100b84400400d51040048100c001345400340300500046003034102409211 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 912963390 1250 912962140 912962159
    0x903010f1415220c020f03210a230907090906050a0e0129030a0b0c1306141204150504050606120a1e031403090a060f02070506041502130306020304020a0609 69
    0x2002d18911000068004d001d01c0301070b03240c0144103001d45180c0c4004100341412075110100340c1c1c4060b0394142c4000d51a1505e102c604280d50a03d401c003c4410084001c083e41140610015035000503154100d98a2030758501c4c001b42203c4040c2c0341a038880d13442c0c0007044070b05141da0080140f200c411500030402104e43d6400c20540f061003c20326070440502c03109200c007580c0c041140d921116004001e0f103406007040708680c4041d07400a001d40c600766200c1800003a41d03c2c040c0c603a0307500490a201c0c0113444c0c00d00701c040c03031206000c00610413510450b000464003240745140c46503503c69807080b00101142e00b8220204041c4e8680c00c09615015070040600c00001440200c01141d090007511105c40020310f03d24082d10718440408480415030400b0007006800400021807509007401448108840d01c008a454000ea114119010388113603c190f011400240f005d1003082c0c4200041c250060400c0c1c2d481282001c818882c4d4020703502d058011090005601c2e06690036801070500381481404545007280c060b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 912964640 1250 912963390 912963439
    0x10806040314031b0d09060510030b070f050706021204020316140906031c02060402100f17060118030b041103030406120e0c0d030c12180b0903010f1415 67
    0x5003901074010000c10001250341d07aa801203158200802c0d40c48805c0e011128005140540d000e451050422000c40c0e07048510200c030350290780d0040c0d00180746649800c1c064524266038000c06d070800108000d4880481e074a4800f6012041c03030042c02540c107013010700405141c80700303550444010400702c1c0c01c00c010074003d401d81c08001200941d000c0010303a5a240c00241045081d81580645c0582c2102c4441340c20f0740800e000340b0540c0b0031907a1607004c1041c4042169204d100d44054000304080d080e5040c50311011101d011b03408070741403500c5a20900300b841c480036000c600b030713204540140c048824003013003062108818108641c103500945c1002c0c5440d80080102c2031a45054940585c0d4045c0c5039102c403018054603001d02c20203009035100b04100c0c9001170003c101d005081e03401c01d08402c5400c0140d80328825560b0400c600f00d02881d40c007070030706e00e805410b0b034426460a681996036108080311160381d4010034030700070001c0c0d4504155140c5032402c0142440742c845154031507400c601c90084596079406c2c42 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 912965890 1250 912964640 912964667
    0x80d05091e060414010c0f0e3d020606211f0c0914101416030504030b0a050103020a180f0516090f0e1b07140105091009150921090303080108060403 65
    0x110000f512141c01141050024070342103001480c0c050b408441c03840444001e0600380c0c11032130500d84d50f0b5803000e9042f611107000b5140341c1d03408000b03401c0c1a04516519841d41d010120001c080c0e4115041114942c2010f9407401c0d01540416102c1344207202c801d400400c07400040c85410303c0c41e4104003140c1d00150442c01c1003c030840600030401003014454801c14140d5204408048501504440d84d0902400b190040c0c8411a580c00d0f0b00400101207034510b00901e0b04803a40949481ca01600344940001603104a964406d2800c1d940c2c020800780741d070030703004250080d8034550380b88a4a08221000034002d85864102044522a1a40030400c00350254001980990001ca0000108030303617003000c3e6028880c1c0c0c440503040620348013004250070710641c032450084003120225080390314000400e00c140c0b2170340745020349240300c3c6002c003d0307082c030440d044084418414059141c0004942207003000c0611159001c00000e20030403024810190000405405009507200400031031400355030040c5240c400304403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 912967140 1250 912965890 912965897
    0x50105040509040b13050318090a0905060103140114040c0518090d050f090303070506072303060d06230901050c250606081207060c030603080d05091e060414010c0f 72
    0x24006002000c6405c10f842c0d8007000380d9541e6140200700410600891404070b104050082c0481c0d80004c8a120390449180d10501401c0b0a0f8130350b40710408451000c080e00801552120400000d05524140300fa10a82c4240450080075080802344400b4242c1409005146802d20007030003550200000c101020354098986039507140c07001602000e5a014801e07019402d1320000c1074880400801050b1342c1e21070101039443e00188030b84110382070a5a80203050070000c0301000c00125829007031030596021a6809020046a0340b0705c1e0303428114040b042102d91550b0b0102c030000307001c29444207018441e000842d0200b821b040425410802d5594002005440c10014801c00c166003000b8040c0c0148004011000c15110000d0300d20b8208045540070803070031034500e03151003002c43c076072402440341c6425079401c19105800d101d0f00c0003c4c4c034010040948003003054410850448110b500c2003503080c200c4102d01020701007070b003424a0319403c076008820212110b0b0341802680303019907a11036514002c0749100d24 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 912968390 1250 912967140 912967163
    0x14030d05030103120c060203040803060301051005010e04110408070e09060c1809041703100911030c0f0c01060f0323010621150504060603150501050f0d061b110705010504050904 78
    0x54040d179080903006401044d00340080304100038002504040d62103440280c000b8840c0ea0f070f4150f807241013a070a501586010802840c1c01789200c0c1096801028244400e08959140540325a0082d242c03542503030040c20261400b1003000040c00742848003540000405a4090900d0b0a0004c1c048841340195070303440c00380403050002000d1002c2100f9061403524517680c11540ca0038000031004d200049402465565030525034101d8180140c4000c8030300c245102e02c04d8a0401c248046000301d00d074071003451040d4540d02c504021860305482144480254030602ca6000302c4d040c0303115007145810303041110000380e1b4904030040015410031441c98800c1500c000d2408040e4405140c4140c900740c40e40c4020441d80e00c0c1100f00000c201007030b800281074030b010300d49043d151005024404140d6400740515a00b00008031041a210f01f01a2140244944100c070301140c080d0340a10f60101211014040500040d5010001940e900c000d0028070050442031078054542804c10010820703000001d0402000e04840d82d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 912969640 1250 912968390 912968423
    0x909020f0f0d1b08010503121e031f0b0702040f0504052107170304030810081908090306101401020c030303060d0c050a090c080a0c020d030c2714030d05030103 70
    0xc0e840140c5500c43d94038409143e042d1040018082e038005d000d054081c0c030507601c403412003900d143d0a0310310325812218041394210542c61140e01a81020f0001888078000d50781c2c503800c10384906601009004070011140d03c419450042000b65010703100301d80d0101c1c0c07070003040c0030115030301150000c4805240702503010301c8102065240428800d501000c0e0008480305001d0000d10070f0f403001940a90700030341e504803250315880006400904d031480380003c5a480b10125513580c01c4800d424104880c01038191b01d040c030b050b8030f021038149002201d1701c013084440c0f9417041c480c026940240300c00c020800c0c0700410042040b80003099807444040d101c43c0c45001401d40700e00400407100a414081c00d4080c100064241c1d6a20082c0060031240d50240046000345000902c800e0441c402d0f807981c116968000c002c203a0030098140c00170262180540c0030000e40100144056010b50401c1002400900203400d0311403804000c01d006102400551b4444e400103404030030713020780c45010ba90540f50040004900308815 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 912970890 1250 912969640 912969667
    0x1005040c050a0e04120906081b1e27060d020f090a060507061b090b030a1103072703170a0e041803080601090305030d110c011109010909020f0f 63
    0x940c1c030041d84111208030201d4410010004540a140300d800c0c1d18160601e808021354a586039401903900041c0c0d0180011503035094072043c8003a040d00080074034a4a4440e000c0c10807a0750500340321b00e00442c4005000300281c901c07004420741c07607282c1e01c0b1240000c10603000050303500c0c41250013500c5060340116030181006036007001c035510786000500c0c610603655662005419500074040c10743e00340f0318145182080800c011100c07238545141d55650903405003444030504580e0000b601040c00a0343c1e40d400c0d450107011407001580941610744401c04022522881d0741c8880100d90004012550040c00400c00512192800440542c44841541e210b03410700b40d00311100000401501d0f840f27410300540f00161410180030720030700d50180d0f94200b81556410015100d40045200050996004201c000e400d41000c1c1d019509450240031503c2c5010303582d03294503003034519030510400c02040c0080c09a01a40c0c20144000041111036420341c181010260808624081d80d0114554500000b0f0841d00302c004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 912972140 1250 912970890 912970913
    0x180f02040b0d2c0304030305030a020c2508030405030706030b1212030a110307020604110d020909150112031407030504030f11010807052802030702031f0b040608100504 74
    0x80261040d4481e1a0000381e000a0f001440ca030041a030864500c0c005804160000c035440403032030300010341c50b092646c0d60440e0103070301c002c00000b81c00b0707400d00010702039650600c00304041d201c0c191943e8250003614920002c81c20710303030707489143d0a81c0100320802c0305490210321542111014100080c410610201240c5e4100032104d82901c54050102c882d42440d545038080c50188060b150200715900b404010341000e8881a81c0c100096407007a000540010314200815011120107844511120f40941c042000301d403050320b0708080d40e0010007402440b001407240d418010203091a0b640c1e01c841054038042c1030300000e900c0c00104942d0005102050501400844005550102111001d02030609040304040300c4056403c0c0080d08203004034070700d503100300152401e504200300040c0a29031408540116162800d0b54036081d40024803401c000740e41c05000c0100b01e0208002020302c60340c40c0c481035604480c2600c150b18402c0749022410b100e0460000f41ca41010340300341600041d140c44508142a8200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 912973390 1250 912972140 912972149
    0x90608150607080a0f0207140f1e1c1a070804080a022803030f151412010c020f0105060a0b0d1a1e0a0e04170a0c02030a0f1a01180f0204 60
    0x110005440d0071960f400b4440400c5c00705d1a5081d104030f84d80301c4403e08041c142008545501505440c8540ba03640382540007003e600085400d06c101030700091001c41c00013440e4105500990240c100c2200505c40201062480e2442041103031505103058000a000071001800140c8190300118981040c903000308983c0482025140d90004501c1c00488208054800c240041340000e0030224183c100305e03847c1c0104001421048001c518060130081c00d41d9601c2c1d0b1a00d800c80c3d0051524954694044080c80343c400e100000741e000d42481a11a00140d096400c0607050b203000350014501000708000d03007030513110b4411142002041212240385e0b4192042070364101c0360741c00b90301000f10007180c441d900048140307554269400f07558550741d406521644038003218050021000702c411500320400000080010324401d003400300000547d500072900d0007484120441300c0b180d56900c05000c0c0403803406071041480c0e04650101c1c156041c440203201c64000f0051703c040e031396161000407585100a8050760040c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 912974640 1250 912973390 912973403
    0x403090302042c0d050a050c10050a0203041e0312020a03090507080616110c0603040f0c08060406050112020109091e050a0c030c0203040e07080615070501050f07090608150607 77
    0x7001240044040a600f808803001000c01c0d0710b600c2072034584045201c0301601640d40300c00f03003002001d84080d00d05170b00613484140ba5000315414220040d840f4461140201204280141c4a24182c60186201c91001c4482c5801d2403c4408100020381c1c0b24086075041d80c4046400340c0c030394405c180103034040c06100d10020528001c40401084004d400a01a8400d0011450804184115440c1074031850424420a0b803207400c007104902c5d450501100441e0401c1c400d840511500d40e554460000000c1a9003294107030f42c0001080c80284006401158003401c2c0407580d030303031540b00d0550000c0c000c5c40da00c3c455130f0740094813001c40d42900703074010304c0041c6000a520303000e209502e45108200b00170040000420302092901012180483c800400d40d030540d14207a034210f03003a0b21801000d807104070000344180d51000866048405101340c1c030018040640c0b00c0c0c00040703841c0c2042c01c0c01c05505040208604100001440d040000581c00700312140c10850201503166030020200208006100c1d004025005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 912975890 1250 912974640 912974651
    0x80307020616020619200307080c030f030702010b0f0f0d02090a0e032d0901020a110301111204060b122d03041e1d0c0318070605040314070605030f040309030204 71
    0x302d40e80740e800d040f4890f0031503581c2a06e2580b00c51051046c500121080c410641c0203100324000641b402000381004030b074440850b070600030410b58140103030b0700c125007050041c1d44035004a5001c2c00d0a40b42c0545008089031070148440b2000049074422600030300180c0300348240740200e01101850b90129050f40100d01c10380380c0c0c0c2c88580c00621079444500071031612400300c1c0704103100c45900500a650266505a000c2d00c4180301d981c50b2203070300100344102240e26550340c092422148403102c00410601566404044103890507003807040c00c82d58070260241c00791000c3c030002070f50070802040f14650b0b03005078500c0d1408050456000a0401003e4920044d5807000041c082008003840c02c002c004040b400d1100003880743c54420100700d86802d09a02400403500c2c4005c41c02111514001d96032000a24050803542c4070b0042516203444203035801140440c6000400f48240440040140c103400300410052514910301100100f5070300c402003810030341e03031280e01c0440c042500c18110b41e03008580080c0203121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 912977140 1250 912975890 912975907
    0xa080402311d0105011d1005030604030c26040512070b130e0703180f030c2a08010e0303041e0501020a05280905091008031b0d0503010803070206160206 67
    0x508940b0000e034807520306006500e04001c07050003810306981100940f240003100706807022000d104043d1428195020f1400c1c041a10b850030000140b055000c1d64803e11800300300d08140f40300f00c043d03003600320310004807209100d0701da01a0011a002c488003900c5a8102006031005541000c1d1582c0004140240000d40094004107880980c0180c42e0407461145581e140c02c18140c0031118a9109a099401000c100704049480a446440240d000b410000105d078020303581c1c0c041c011101219480c400b9114000d0000101481032850060210350008014800f10420344035543d00000b0401002c2100b20309850781c4da1a024a0024143c46d4408002e64480826081c0038246400400100240c141602d100c0d022044940324208443e00d9991100300d8618104828007031041802040b503140094180c2000a020100f08010080d4450000310a512070254a5009003030000d040004810080180014050030704040f0803035010b90381c11968035548030200380b84d2540c8001080c1010f5800480421102c0c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 912978390 1250 912977140 912977239
    0x302090a081501050d2a212306190902120705040b0a030b191b080603070602150109090c030206030f06131b0305090c190801110a080402 60
    0x10400600107940c003003940e8940080c4403040780702d00b1001d03000e00d07050382c2e02600c0c0c0c1603500540c260311549568106046c0d03880d9001001c402411501900e00c02c80060307a6003052141d002e107901820009615101c0741202e0034503450340e0364003001d4056149401452400050072103d075022084841d030280048808542e40b403c842d4a8480921030701d40554101109901a403801d48603180980b80d209120007030b2610b641514a03044c18108051103483c5640b0f10380080082550381da29808200b060b0b68020462500e003003807508000140d8000f005540c8084c12214030706100c2c41e42e642c1034680800002600070514201a480c1c042c1c85d0340b010303400140010600c00320303681402d10709101d03400944501c0d51440d440c00900c1d04507807814909210a01d2171980219480c0c0c0309812030303900080c1c14411101c0010982000940c0188520841c07030603130580e48010014280c081c0583c0e406000c0128005e800d0407440d22024103490f00050000388a00c0d054001e40804400000e460005003201c8a50041608011030454 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 912979640 1250 912978390 912978403
    0x230f06070f03050105060a03090f15020403020a0e06010816301805060a0f020d020a05041503050601140912070b0a090b090a0b07050a0b070503040c050306040c0b0a0302090a08 77
    0xc00040030910104040e5009000303d90403204054040340c40c03c0c00d81c1004400a1090072021144400c00076000c2002c0f075020655003031000085007005039034915510400182d00c009600045841c4c04450030044241e80102403d50f00c909446a05040e80074140422104042c00707401d072010340c03c04040c444641030003010300c0c03482100e140c1204220100c5940d40c1c612810414010042180c0d100900041c042c40a81e0488010500c0100c409420441c50b070072180c00b660810550400003da003c1020020780f1020340e601d113100800da080800c001d00300f0400007087c2d2050070340345499107000021800360544900c49941c8100701171405855620781c4075040070350a070b40801d02c1c4100040e0152004184003148500301d0780fa195000305121101031802c0d46a0000d900480301c281d03294020385040001007800104454490f50403613440c00d07624541883c002e4260f002036000240070b0341c82041044001010840c4500079110440a8581c55449400e800c4000c7d205105030980c01290000d400100340800240b030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 912980890 1250 912979640 912979651
    0x8031501030c0203120106120b060d0509011404080315130f06060f050a2f0f0a0204140402031f020412150e210a12050708160f0c230f06 60
    0x42c000c01030049800c9982e806203c0603249022900b200400c4102e00413641e5603240760342803d02007844501280000c0503074000800401e4090340704c02c208500d4190a10941c9a400301c402020242c03400c098407040f4403400010840001002e0901e8407001d035560340c0c070038411038900f065011b0011103501234415024010070b20804020543c502d8070102c1c218011016140c00c4420b6a90700c800001c00b0404007404c414261100d0007501d901d0102480c11014180000703c001c5060345c0c01071111509510500c170031200c00200715090103854205020050354081050076848491214485405900442e4400284510751140b551522101c0d041410045220340e04c202220351181d04111068200d0b544a481c1c40703400d003000c64000505800078070341034882000313401582c5841c5000804004003501c404100c610685060010408480400075006510315406800c100f0034541148000003982c0d0192010041c0b650040056510000074581c5111184070078900180d801d0495111401c0300b000d82d40c640005550 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 912982140 1250 912980890 912980897
    0x30c0204140412140f070b040206070f0804060807021f2307030c020c0405010f03020112060b040f080c011e031d030301120b0106090b0a11031308010f0b0114090402031308031501 78
    0x4d2400340000440a03541000000380c0c01c1450401141c0d00c90880c400014404c0340e10200c00d00413140854403407550320081c18801e040c015992428180040e020482c020400c000b1580040301c4641c490080c0d40c0c10010645882c90045000c002100d045580c1413200d052044a0f0114501004031065140d00034821030354954083c0c91510210500b4042a11401d000e45250103902c0b507020801540f00d0b650400200d428070000084480e200c2c0241030b5030fa84240c1c0502c00a0400b01d1060014240a001990750003000b401d1100e00c019031000912462062410004c081c1a40c0e024101d000d503c2040500565441c0d803000c0d01e0380e079070711000c0d03c8140612503101903402c640c0e40c80011a50501410210040c3c502407500b10b404d010000d08215080225800b01001e14002840040b508041c03141819000c1c010b540b0011441d82241080e590450720b000c03507080d04200481c0702660b003812111003181c03926013095802690301d43c1c4401001c04000b42c40034000307007130707010010400003484084020042803003001d03603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 912983390 1250 912982140 912982157
    0x204090f0203010b0307110a200f06070c050f01020109050a051501050a210206070b07120e280c050d030305010806061e0409020f0a120b060105070f030c0204140412 72
    0x40510100d0109004e0014846802c001045a8601441c410a0031130421021980a044241c1d00d55a1401000000304c022003046500301c1c1076031a200c00c141c541d90106a1b00700d0b0500d204c640311150440e0461060034001d180e4a8408001a40700390041994a034003c401c4039101101460031603660011340020006100d19007001003440c5c681260703403404403403402110180c44146000281000d01001c0c03400c0364041400c01503400025214010345100717034402e4907003104408245032051f0a44040504100da15002909000384d101c00301041103c40d040d0103003000380040900c0c036014000d4042c5030000750b88070004818040c101545030300054180c03513081040d503a04d40c42d19020301503500b0440c00e142182130031002611402d410594002c1e0302d0715000810899070b102c914404940301c00015000440c041c00b20a0500c024841c540042c580c02a80030710308145898695210320201c1c4041c01d40042c20010350703441c01c40555580b038000c3c00c04171110944031001400d00e03182c0500b440c1001c607651000320748910f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 912984640 1250 912983390 912983411
    0x10181a0d0b10080a050c091002030903010f0c0c080c010f050f0a0b090601090e270c18010608070f0e0901060504060e0906090c0a0306030503070503072604181d01020409 74
    0x80c031811502140ca464000d0741c4d464200e1207402070030000303080d910301c1c4101b484415043da42d100d040c880a07589503009140e9500d10034042c1030030b541810f03800000e4a41401255040503512400600360a90041e0665441e895500301d40c6002d440301d0481604042d0500c000d011014841c406014095801c000c8200038250001c0188900384000b120400c3c04548089000c2004070b130300303d11403a40900000071022071121120450200c01b54414140e03070403580840700744405800e040708400311079480d1407450051585000c600400c0755500900e101c04010b1310030714001d001c4d1700440d105443c41c40000d0441070550713100c000c000d00c650070921408001503c01150b902c59401c145002c1400b0320f0002e003c07101140e58414010455078021100f00e0100340d070340d003400004602e0a0010b84900392203100a95650034542c205644101820f880079509507541502c806414010b030001c0f5011916090010400064200ea480b4018007603103042d04d050a0050261440f1000194010416540e04840401104168 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 912985890 1250 912984640 912984649
    0x409020d0b09270706141b0105070f12060e06010c02130c020d0f051201052704080403050f071202040f1b080a0e0c13020d060f030516050f10181a0d0b 66
    0x10300c02d40c5d011030346001000d010a4181c4c80140782c180303c840a201480001507654608640003101c014002a84c186403400040350b000c9035028501103268418050306040c0515510301348005400036040c001c042c45a4070440d1038124400404211004d4100510161203001940f6101c410003c03600042c5c034a882444614040c1003079945044510004503001d03801d0005000d43e1a8485e000001c00402240070029121410001203102e113110302e03400c035103451075444d0061174460008566a440e820066013441801284406a00066011100032640c180d85902d858001c0030181d48148150a00c1c07200300c0045600100760502454900e901040340c031151a24664841184590b41075010304135450100c0e184c01d20f50054100c581c1c0003180000c0080d0303556080429000183c0c803c40755600082105072540280c21003001c0145419641c400031501c060300001c1c0840d1074a0815001d001c4400006a144400014124040c0000b01040e0001a074038502c04500b0360460fa04291059062507801d0800f03040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 912987140 1250 912985890 912985903
    0x1030611160212010f02040801020409110a0206070c06090b04061401080f07062a0507140414190605030f10061430010204240804080409020d0b0927 65
    0x4401d503048000011035400c00000d070f0b403001800980c0f5902d90f1008002e5a0b02032000300010041480010380d118078017803180c4240d81e400c48900161001c24404110301c01c0c1c011800c103503c00c0f01490010705a5240e481c08100030000650301604001100c0100410080c10b039000c045400e04803203403091070303a03030754a00745994814000070b42205800c01541004014010344c140d1000f110b842c040c600454040c01511080d0040c0721030184d48a51109601700500c44000900640011050300c00b4011900e8821002480b858040c0c841e840e041c0001030a85c9106d00350745c0c4003c000c0c180083c20355044041e106081c81d550002212440e544500e041c0e0b00150207408600352003800580644015120703446102d80400c84409070040380246409080c480201c010280700030b00150161610700150451101c6100c1840030404039148180312120043c4004540c4900948045810700343c000360390f40d1400300208c1302a080f812200e51300400c502c41840008452158241c1c50448113500b95020030390040f032010350303601 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 912988390 1250 912987140 912987157
    0x3080703031a120d11010207021002060105130501080d050f121005180105030613230303040605010608090a1b0506030c040311010f0905010c0f0503070c09180b0a0f090c03080301030611 81
    0x34041132001d0410340c040c1380d40c80100544039000600306200798000c1582081c2d000f8640006805c420300502c124605900c00e900071080925040102c1e41c10240301e1a80c070026000881c040c8100410806a000c40e800d0464020382d8481c28a10b005090902d05082c0110389800b41d1403045101c00041040a00710100b450704135040207005102540360391204551280c415003040e15010f0320300309040342805528800100024840c4000c0d40e40e4985400c003942247c4041c0c0010701044018001d000740f0410014240d045a42c05c080349008840c0d40c040f5402555100e9804250841004030401240d8449400a401201d0045c413042c000da910700d0004603005200c071641d80c0003151782c84000b8012540b00346070901034144251203c040f01c07061900c46a02d16080240d044502c804043c1c000c1c000700025000c0e140341c101001540d01c1c440e680030354132190090002064010015900e144c0c4140c1450305400c40f04640741c01545a0b02210f440b42880b40340c81c2c1c000d01058600d40c1c14a0030015501641e60700701d1300e110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 912989640 1250 912988390 912988393
    0x2062502120d121d0a031d09040330150302040b0a0506120601120f0b040c091a031f06050c01151a07051e0c09090109030212031003080703031a12 64
    0x24a00f4050007401010910560328644401c0048941900030030004058910b001341c8030000010001110324881c909480c07a45801510090140400250083c10402403030240300360909070f418a1031400c0a142d00c81d036094501d501e00389404006054010951001501c0c000d40c2e003440002c14050034080c00c114035100709a0011000c01c400c1100e28007080900b40c01c0344051500145a19285000d8000d41c0c0d4141c06441e070080c0c1d101c154461900d86845050400d40e01ca00b080320240f0f1904c005140c01d0700c0454260300200078004005500408000789605035010400c20704162140c071681c000304581c011340342456266280241d50401200f10511907421600c0b000b0258040c003901c0449460380d6009603c00304d81511a038202021114004c3d00c01800700005107008111140c0e0b4402041040c002c003412014041e49019200c1003c01d50106480000b1020148a06e80c3c1c1d4856110070000c01f44254005882d080011424034209507140d042a19034814880248860003150000c104981e081da500074600c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 912990890 1250 912989640 912989657
    0x10e040807030c05010f0b040b01020a08160302070810090b01170705010c0302101407121404020103050c070501060b120106050a020a030f0512040c0504112502062502120d 75
    0x152003034010041c4610902e0049084009569010f00b0740b1401c9200591068440d083c0480742d00b0907105402c2c41c250244000c0c0486000f41d2a1543d031441590780d1003c110301e061800c081494001c0004200410a0300b0032035075041130705291000204100c0008544803160580001102e02010300c400e660040048054074011f407a1000559000e500d400d400c41c1035026802c40800805258401c120604d4198001000c0034540050000c141d6180646450380d114a030031501c21140a001c6100c6610550a007800035842d00c40c44120070441c024290010029800d100c400708070040c504014200300240e12400701c000303036218001a50507000b916011001079215900c000d000c13911a0080082c00328141c2021460038030045010106018201d03410390781c1d8801d1440800a0f820944541003030707a40d20150803810107501d00403401c21240c150350f134002c1c0700780c45001c0c1c401559948001c40b1184085420504041d480030411400301481582e01a48202d40300302205c0300c02100414070308041e1200d81c1c2c40151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 912992140 1250 912990890 912990893
    0x7081219030f0515030c010903150903020703120203040906050d0209150a05030a061b0e060f03070201140a0b0112021312421104051e1509040501090203010e04 70
    0x50040c1200004082646508001c08042090320506015140c82204410b0360008841418600031075045030f40e04000f09403d003000070804948101705120504a0080780069081c103089141401640001e070056014801c0e520400c0d0300040104110b031500c240600070070756200100070700455a4100650003241d0940020020740e003030840f03056840d0300146109031351915180824a0142e540c0c03400c40f6078a65803240058290718044011100e284070b854010060840e14010450314050810907005c01000403010030480e9000703422004425009900341c00b407030b152920b80075000d044403038103049c04070b8040c0c00c05840b04101030084429640b2080c02e00c2c41a5481d011800c2e45105040c88103950111104500e070b11a00490b40c85400c80340903a04410564500c64504540041e41c0040d038114500e20b0800c0541c99070742c501041d13030211801120700684547d241d503400c0301d000c100c000c0000c1d070040407581d00000d85c801da040682080c850a0b02d0800142ea00c0d515644121b00c030a0123412046981800000d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 912993390 1250 912992140 912992167
    0x311030a0e0703080d06030314070c030b1504020d05040201202a090106050a08010b160f031215171911011e080a0b1806060d090f050f070812 62
    0x154958040c1c01110b40c00c0340d0369140c0c4030180d0050100e20316000d44414041041c1980802c101d51070040c1600000d16040255468403000449440020200f1400d034000682c000300c0c0b500200d04641d4003400c2996115130440402004000803241203002c110021100d0780207951004c0e00c2d03005124281c005011004003800140c0e08009580e0100350441446680d0317032003a44800c3c2506000304580c2d216140c61b20032400b0b02a01d1000705800402c2c1000040c80500300c40407940e10b0155a06030410041170003c00641401c882070b10b900d002d0040c3c1071b810240d01d050b107601c0902c0c04002301c40307041a104d20400d40304d030070715a224004952103460061200b05040c0100d80304000706500b1110504280c81008075150304002040310b85800c0344041440441005942e004901800d9850032080307030347d500350f801e1b080a0b210490f04040d007542d0140b01b0104025000c80c110764020018103412400341000d108041c500315903075030080e06900c195401100f4001486081c0002c4c8642d070410300c01c10503410041d000c14100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 912994640 1250 912993390 912993401
    0xa1409011218051e07151e090504090c0303090506090f0f01051207080115030608030d0519151e05090a02030c1308030901020d08071b08040308040e1005010311030a 72
    0x44800d00c0500d040c800000c004014031103810a010b86448240c1c46131600007403d119996200049150f02898a103c14540c441c0b0a410540358100114048100060013114892440d400c030f56001850703c0c140d401440040080d481c1241e1190340c4d500038241d00c52040c03100324066100b945800c9000b81003817900f20b1a01806004e40d1580c10324009092007803440d03240824100c240c481c50041801c01d0018010421056010b40e01c00540d030134180700382880c1c41c40207a6a44607040c3d036030070b00c0b80c2d2350000703d121070701e1000d69442940d009541c2401900540c0038207819001c100c0c82005060520003c411004103440d008440807204001c0c0310701c6c0550340e040780c0c5c04c0c00703540018030038200b05c481080380300e00030b6141075054800703004054011512000300c1e000180c82c00700c08c04001d40601c854081000116940b00c0901541801d094840e568003c0252420000c1c5009980000b024030002044c04100c4240c1001040e10803001c800100c0304480c3e03540c005404403a880c0c061060300440410016a640011386c008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 912995890 1250 912994640 912994661
    0xe0a05040218060304080a08062d0a0e150a1a0405091503060a0b041a100f0908011d0d0906050f03090a020d051006050405060906090c0d110a14090112 66
    0x4118400520400041160380100d608640041b40403034218903080c1d102051640c0000240c881d02542551003541c02d0160300c80300f200d2100034503100301c55051903c821720150028014014035220a00f05035503408484011a030b8040c0c002c1c100b0081c00100c10000070801103500c80b21103c0503207028244014070052040c010300070040300c606030115140e581c8040010611035031140d8400150011014200b02c15191810540c40d001000744000b0302455548007400108000181403140b130300058180291000000b9500804d00b075460a403101103040c40c0d1310180c0241072004016622503110300b11054528242d40d0003984002442407100c01007545601c0300441e0000300c104111005502e82c1e500090403010340340d07002c5440b60400e659191400c07185005101c081e000446050105280c5180403424101000301518441e00c0d543d4041801001c00c413044640502190b4410f01034581009200130503540044000d40005501010548650004c00150b409441059461042d03801111a990014000b030042c0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 912997140 1250 912995890 912995917
    0x20417121206280518040209010b031e04140c01020a17030403030e061509090706020a02040203040809120d080a020a0804110f1306051201020c0d081302131b0e0a050402 74
    0x1c002c407a0320f164140015200403610b000c0d40c10b050501040c456810ba40150151201d54424280b000503139034404928150f07428201d0306a220341d244c000d215585510614410300300720031407086c00180203015080d0050f604c0241c04403111000300070f004a0b620f580c0303240f000d0106003c01021660341c1407508021500305001f40740c0803d48109808419003401c1e010f5803207040c00c2d450501000101e04004442543c40680d600c003a00c40359203040d80180d01d520300040002d200301e500200080c10401b50318165014450301070b10710039041100d83c1000750b45410000b08040850392000001d4134070300042c004c64600701140d0348c411801b40c4465880903082d00070541c015511200c150340007034894413482100015118a41804070760306182c40c0c180140c0c0c0512765020304042c0d00421083c09111000252800d00083c246040c6003103a4422000703103000e1040000003507201000d10070720250f841164001e0207030102050140c01211100d9182034502d6100d54800d01c2d00071405140402207894643d001d0003c1410850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 912998390 1250 912997140 912997159
    0x1902090115090f093e030c04080303040305030106020105090d0f0e010207090f0c030e0c060318010212070c03020d03050403120903090911040f0e0408160203030d05040501020417121206 81
    0x6886003c0b8036099000951003aa0790310a00004406540280aa181121610b1040c600130b17064003400005040c001203032508000008601c000d2030100450f4020100b103401d0f60380b242400d241c014100d500a10079400150700f880f0124200403404921001c03112584e441d8403004c1c00141c0300079519015010348150550003803100c00503d00706540510311039000b01440c001a42d00e0141d00c05401c4a101d030300349000540c000040003500d520340d40e00f00e03074210301e10064104c07181a002c0c210601900c5038403846c1c01070117039000a215500b038000300c200c904503100303030242c400712400720508808a130001c45000e00000c4103641013881841043c0d02015010b802441c0440c50b180d15004000c0a4813083c080725900003400207410002d2900c0c4ac0c0c41c00c0302a1050540002603802c2a40700c3e0806401540d014130980387c0341404040440d40d042007111501d0351134440511071031600e4180617000350000d20400c0a0b144c00c03c142e20355800800304400301f4a030008990503040c07007140b0048134602d003001000140c000011b107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 912999640 1250 912998390 912998399
    0x8240d081c0b030d080c030109090c031203020904110711190807120507061103090f01052205090601052b060f0e0108010f090302250b0c030c190209011509 68
    0x88460032850300e045440442d01d03214500515140c58250000c07101008041400d002400307070b02c002202d04540801c0b01c04034504900f42000381c60600301b40d000401c18034070410b9209200390140c01a1001c1e000c12581042030b22586144038400e4401c06c0001405c02003020520506443d041c100d8210282d8070301e10001c109910340c140e140c81e040c5580c004071100001031451904000c0300f08241005480301d8503200c000000c091800030350300e014410600333100e810108050070440e446a000d41d0b03007220416550700d15940302000711030704807031150140e45d0281246500145255009c0e908580c048a00c0348060740c407030280541c0a044603440302d05070081d0709464000015241200002c405d02a1840c19079404c12940342900305421200030203088a003e030f04081421000c2500440d030748850000da5002401c0c40c40c05040048448262508803084400000c00c8c207601c1d0341400130103030031590608d000702e6450314141441c00c0c1031140c408400a50007456000140425083c0240b1031140003c2d80c180007442e651035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 913000890 1250 912999640 912999667
    0xa0308040c080d23040e070e030102120f04110103290303090907080a0b040c17250e04060806040c17010207080d051f0501050d0e030d0204080a0308240d08 68
    0x40b00035280c0003070203080513030650360306a416038007480d03140400203464540b51286501003024000c05010501429220700324040d1400e404441500a5a4613055802e1802c240103800304401960150307402d040b11340c03e00c116540644030343c040a403080f8050f1000442560150041c0402100e1081d8150005112912154444004190088010b80c482403680d01c0c0c4844014110f0308049035180c407560a05040d9640d0f08c0d040700d01c841040c010903000d010282c1d00d64241c19000608186410051540e800d482050103034020721107510700c042254140100b80c2e0314807841d0b5803010151030290811440d00c00811048503a00c0c003c2e81910030010016040c40441c0e180d00c119a0080300b000f02d00261640200303c0c42101c00007024403100400e116188101d4200b1000030150302030342910000303845d5100b6008107004d00c100151a00d048400380159504c50712603400d191514030a500807004500383c08041030440d0044101d240c501090a0445908a6000c1081082030080000d080d0f441e074074200b1041480e48003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 913002140 1250 913000890 913000903
    0x91e0904080912070e04020603150a0314100e030a0f090e150a0b0a0f032705010207030e1f05130504230601030b0a120203030f071b05120a0308040c08 66
    0x41c1401c0341e11181035005112400414050300207290700b00e00030901ca5031541c81031450300070350103450326600d9555080100c000403011a00c0f042d440078541e4400002c022404c031134205d4401840003658000d2043d0b02080c002c1e5032100d84501c0ca190400d004425a6900c2404201c0c581740c01458100070a541d03440d450410180305403038980079007a013094214030780e05082c2c244400070304d900c01c11107203804043c8400030950a403501d0b0399070405440c0c03140c1142110b11503500300c00440b03446942d07440c80481403400b94000d61120b28210003141e50000c0790380d03d620b800c0310680c03889000640500187e42039010200c585600801c400b0031025040440825140c41e2841a409000b030000c0b80518405101031541490820062144d4105820100c03440080c0d1100c03d1001d045861190908010050510009046014480720601590390100704401403000c0701c0e02000800c61880c40940c4a55180c800b03003c0c811030107000a651070780c00011804d0020344144000381d8401d016030400c000d02d07611000c400e402d20300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 913003390 1250 913002140 913002143
    0x301d150c1b0a03110d024006050102030f0d060f06050904050c0405010c08030c0d0507090312090b070b100315140c030108070317120a060e0703050903091e0904 70
    0x91201041540740300500010007042582154484052455540c450941d40318000c201070240d908151114119241e11140c0b01e19005015034001074000d100d14802d81c17100c1244521401017046041001841c2413130307c40e503c01e980069001d035280c20007400d2407082c554008940424110707500c40001844260f150707280c50190040341d0311f080d6140e00c0b00c001c0105440c405403440d2900c0d50200000c00883e178108010806896200001d15120b642c3c0c031040038000c0c01008070400000b410072040040107548001d103d020f6038403070300ba008540f0306004400c488030ac03890b000705150500700f00600801f1844140e80c1d594081c413140c440b0005940c883c1d90f4000742c8020040c0e13450100e138039840e440c00500018a0131542c41485c400e0541d04540c5003006803607440555200141180c07044200d074220f00e50064044801e01c210050182c5c20505200984e0742c003d00c0c15102e00d2290080d83e10101e80b4962080c05607500459041000f035041151000410248012000d107807403802c0d04881c8025465103400c44032600c0386 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 913004640 1250 913003390 913003393
    0x30203060c0c0114160c1a1008062208031f270203041505060303042103030b010302091e0102070806090303070806030718050606070f301d150c 63
    0x102e00b01d90140d42074404c1100030f440c2c041801c20400c42000d02440503050110143e00d0502c0c661051800c0400045c1244400b84400c0d80d000702c200604210006000740c11203c10307808035412946d41d02c440301216450001003015012010114002103401c03074001d0750304025240d0390240c0341176403400303000104007180e413040713211006407010000052a100c2d040683c4140a61040d851407030036644403c1801c044458150055a99201084803a00d0401c280c0d40907100b41480c60404521026030700505240058007180000e041087c0000d00794401d00944030411800340c120368014010b80e60310754aa09000018030b0440c4aa0700c8001078200c410091503004440080c095966400c1014000b030003d50001c20090107a48003290400800b8030360003810781d01c142188030001e05500d40a00040052182c083e01600e10100005c8600922858504290b03d08844a0042888803189801c03044501d40c490186004191207051009049022007100e040182c00100081400c083e0129040015040190382c8241c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 913005890 1250 913004640 913004647
    0x201050f040b0c10051008120304110909010207110d03080f04060209060d02032d0a1802041b0f09080d0305060d020301050f010f08210a0c02060a020a0b0c13060c030504030203060c 79
    0x100305032881440d4106c00c0350300f40100c00310304200265540d1740004907048007032000007001500b40151783d011540780304401001c40c1d10b00e00382171038414080d40103c0310070703034403440260344110451070300010078004d5a40c0350b100d402d4035030303202c8040e90f1100800500070780720140c08125a00072a910b020050000c144039050060722070604003500710101c0c8480e0002644031210f09040000c1e0b428805850342d03c200f0480300850541c034188500c41b08808410f0380250032905100c80c141c0c0d50f01100d24002d0440b60320380d803284580e600c000800c5841952900c48e01d103160304100503034a201031113030b0051640450060101c0310003c8482c1d020034212002280c1024501c880d0200620035020a0508680241203020041c54803e440e038480300b0500315004005006c01c440020358014460043c80d03550201500100300715201c01c95282d0103502c03180795000c201d52100d10b803000075581d900380500b49c03050108a0954001c0d82404d0000903191a87c681405605104040c000040140d9080040c0d80c420038403100907645 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 913007140 1250 913005890 913005913
    0x14040b0c1603081614070b18030d12020a09030f060912050901021e100e01050a0b03030408060c0912031611030607020606100917250e01030201050f040b0c 68
    0x40141890040d012802a0201000802c03e2001a10b034501140c1d0960240c2c0f403640e251104004450070751900c0c2602400f0b500194005c1d00c1409020621600381a005a070f203003413400c141d1204500c602c0a0f0100d88a800011001e40180c6d0140c24030440c2801e20480c990307140e840f400c0d40c41c1d00c0294100c035843d865078050000c0100c203c04120031404a400c2c4542040b1600001035203030ba0425000c032001040700c2807003a8086004012412906071548030800c40c07000801100e0340a03080490340d010034075090010365001c1d400c0000c21203040f503040401809044c4c44910881c90241c0c40444502d030300c071180c20000748224a00f407004180c0642a0340903603858555038504052102c50803c2803600c243c1208003049103887d000f02e14243d0103070046031706c0090324200c5601070325441e0964000c11810038800350381040c05040000d2261090722540b036045021034440c1a900461000c3c3c0c0140540c2c060303140010001540120f0140a040052101352414907032680408900d54001c409844540da000c0714a698 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 913008390 1250 913007140 913007143
    0x1020a0311040e061306051c050606030a0503040315090507090f050a14040303110c0307030815060f0a03020f0f12240a12111801030b151c020114040b0c 67
    0x1640c11241c028860400c0d00d880c807960151500105001c2c01014401604124103150760b0106000d07080041000702e40f80b95102d459007101010f0701d0116001e12601000c61118034000925401b090b611070003c43c41c250945d501e041591381540d40010683d619680301400042d0140301c040f000d07107084040000c000b04409410015a0000313030606561910f000740c0011f01c103624681d81c0d90310540609010a038006d0106000100c0d10500101c1c140a00010a4940416030300c041c10074000e002109909403a039603004200100c5104280301c2c900300203810041c1e02045402074010b0305110f07000d15410380c18407a10076840d20b41c0307600001e8802d03139901d0b015040040070817210300c0700740c4102c240031382104400c0c00c0400401d62144032801240b902196001d031120411810500700003004002500c4400c1c86150649500300d0160203000859248202400156100c0568140c440b1080002000309081103c0c40d151550b030042c503900c0aa040210250258280c0307081000180f00419440285981e0f40c0c8210707914a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 913009640 1250 913008390 913008401
    0x23071b0305250b0f070c18140915071107050607031116030206031306180c03030f0c030e06070302031207020c0418050606090c0c1f050f161101021b01020a03 69
    0x10420001c140014091541d1035016201c04101c0d6030b00e016901c0466052695000e4055449180c41d030101d107e207030010000a802c501d00b14a0041c480d03030000d4441e0052240c0322410200101c1c0c01104400c0000e401501c05e280b61a041000c030401d442d14292108041402644001000da000c0303a4001885c0900c0ba1041000000a0a40d01c40034101542958000b600c1403201510101c07640e00411425401c1c03140680c00452045460b00d28480a00c40a25000303081c803000d44810340c04240303000c0ba0310b442140564071803508540d056466a1840c2c8008040000c1c94000140a0b03045201c14849010300c90700700000c031401403005800030842c0d218098100030a99241c0c8042d40d8030410091294400070b24000780c180e81140d02111600c80a5a44800c6200107004011035030520f03200d0300c0303c0c1005010302d450521203641c150500c1401560f9650700c2540b4400010b9500b54076002018245107c40351043c01802d800c030b020800054900901554001c03c3c2034806c00e00302186035800104030030141d4151145 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 913010890 1250 913009640 913009693
    0x70611160b0609160c38070311040f03030804080712030e0f0304030308012c010905041a0408070615090911030d020c010801150302160609021023071b0305 68
    0x1a82c100001000300414044240b640101400c16460404c42c06030003004100050215010b01b60740c200389611000501b4401c243d50700400702e40742843c1700d1901e45502c02220300351000d031074140030308501e50307682298120340084c81030b1b50450080c06600001107843c0c1c40003000900d141d4010500b000010341c440e05003500880c0400d880d600411041000030382110b0580e044803241a4440c101c1e494504502c00d8130340824114992001421001050350406540954012401a0412440e00c1e42140c0220441a8180c0300a000400140305a40001d14540c110000c4c648900000307003800b03642c0350000402d90b9507000046810712031200d0980b246060400c000010703141d4520041030001da500e00068646881801043c581c0400607407017044407800380d011243c49805110382110b880c603880c14000c00400e08004120312a0207103502812015109424401894202409241d81000c08015898165100d16001c40d250303a04000d02c01107269442030418000e50059001e4050b070026a0420103001e500c0456 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 913012140 1250 913010890 913010911
    0x31611040b01020f0a0303110403020a06021e0102090127030506092a0f0d06060f060306090c020c092410020607170408030105010f030e070b090a0e0c070611160b0609 73
    0x3141c4c44101c0300103609a9450380500300006c01a68040c05e08500e0301c076940000c1c0d0030402c0d1784000a45542d00041c45094180348483d60151041d01505050a07031140109990010f08a10096004003400c0b14030741d41540d814a60913410183d599413030a0801c5011548101c054001e040034500b540c03940e68281da5000d441200d654401c0031a040010444450304c0da92a001c6d041d18480501000841c0d030005000d00041e400d0301c109d40303985000c024094107881c01019400c4e802c006100340358500000720305180d247c009280b0485903030740c400b4150010100d01510203171159a25269552070322150040d0025407035603405044517103020040501002d00180d0020102009502000702144004050b2415100c003442e010444921145003140a0140000340041b2030040d1000050310305980001032030945416a04c150320769a4440814181000441c2c842c001d44004011032000584a94044145400280c1c1c8050902003006500c1c1105800c00070101d604001501c14803603540750584103d5440340d813040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 913013390 1250 913012140 913012153
    0x905010606091d0f130c090603120c050619020706021809010b03010308070b10170a03020610050607060c0c080a0507060f1e09031413090501050306010620031611040b0102 75
    0x142030490f000720003841c10a444d214100400c00460810320501c1c1c0c0390b41c224280c1066503482c0e5074004020082c620080300c8005960705070209141c001d030341144049401030043c0201e136071987c40c0341411144881c80144041c0e07080001d080014502c2c800742885605c1c1310752030101000400284620304d101a040804600c00c1800108005074211003180c0702540d1040da540c07000e4558041e0302d1440800d540011007951000d80c0c008242d014000744500d0351501079800c0701c0442d21185124002400c940c0030325034000104001e0320000c60b1040c0c1150a14030168600000d1501c241c1c1c980c020305800404140c00080c0c8001f802a0600099010340030510540080410552864017284281c0150040070b40800f07a88450300c1c0000e1501511806201c80d8051468036960861411110f80307441d054081c005503186030000104080c00c001800906880c05d0b61140c4564585000c0c4842c50224100b20421852000308055000d25407500300b8880d00d0340c404c0c1070340c440b0300b8550780c06c10040d200c038014914110762115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 913014640 1250 913013390 913013429
    0x1080c060c030a030b18091011130302010c0510060b0309070519060c061d03070506010e09061b090a0f080d0e210a1707021005040303090b0307020f01090501060609 72
    0x1000710f504580880c28001034503060780c0085030910000c6a0a4600211030000308203d800010408a00c2170000b101c08024007000e0b5225050b45005214101c5c907402c5c0441070900c01940501812445c1c1070044003140c0107030710048540410750382c8035000410710310340100078441e440d04100300c01b00c0541411104803051051403032480820344928400c0404001c8408030603030600100c2e900101d4a80d0800c0d45c604851441205007981c0d0380d07c005400c680034480d840001841d2184281d00a014192000c050601c544441d280a100c11004100309072081c2c000b004000c4403580ca00403c40010500d94071110f0146103070281c01410030042e0300c0c0c09070901005201c1d8405e140c2c0c0300700300d500710f2140d10701c80502a076400d600c0042c17806407407000c0109000d038080b10441910310032030060484c3c18800c0300e055140c0c1400d0340b01103803d40543c5c4401408145220010b01c01d29615201841c0e0091aa10499880035100140d840c2910413640040e1501d0359105c3c0c082c4a2580e000b26400040c25404c1d08403107000c1d008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 913015890 1250 913014640 913014643
    0x70e01020610180b010302130f0f080703110f011710060327120201060504020d0609200d200304030906020f0d1b291005011b110613060801080c060c 65
    0x3d020540703401c540d03154884401343c0c2c0a179060f902d21220107111581e01036100e440c0102d2240b5203025a242c6043d070700c0f1000940100c0011082c080ea64804141e10780265203400b0f00000c01e584d119103c0c103101d0058901c1d0a030100092803a8402c24049102100113441c0c0b0744098210b54040c540002102c9048403080c0307042001c00030410b091680450004040c000c03a400c200d006088940109610600000e080c80e10310b072564204c1c101307942003030b0030410413402c2d44810701e400c0311000c10020014880502030791000c1c84d0141e00c014540c080c2d100c0729000791045480d0360801980101c4080340443c1c0104001e00c080c550411011580d41ea41c07038001e125202e0300c0900a480480c0047d500126112005d8940041256886404682820070545000302c80c015910310a0300850403621100081d104000010311903211350b4400b8090075000d07800142c0c07004107444180c420b004801203d600180d0400c03206441440c0580c400000708019501d40d0050350500f540b00307041445403a1031911580d4140900d4545280 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 913017140 1250 913015890 913015919
    0x9220b121b03010f020a020109150b1810031205030907093e1b10090b0f060406030b13020406080a08030c03130614090c01111e030d05070e01020610 65
    0x140d8151400c0d00d001079000901415803403072100722460000c10580009034054200682c0144540c0c5c54045480d18a40d041c401c41d003c000500780e005c00141c2c003044161242076907082d04510b582c4c0e01d030701080d0340b261503030641180d03001081d400291000040000c1e110040c07004e9005814416401e01036030400c86942c00d4420300190910550702c0441261505d408034045c20351030480281c031146910343c0b0541d50004280e09200d50700c0213890040301c588a4611006128008885500c01204002a1248a44840e40100003007125800a0b07581e880400864030300e50b031862117a03140da041507914070702c20b00c140410b075452640944500e5200500b03040c0091141025680e2200740e1000b065101c0d40c4a0381d0070182c200c2012000741840346408941aa081200d000c0d03940b05004c40c808a9100b0342440004540030080c068440001c0e0700601e0703042440498510b004c00f49a80a603044034200882c0558060417280d007502c444001c9060f1400220480d6014040c1a6200c02a100c21400d418900008200c5024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 913018390 1250 913017140 913017163
    0x30c141206150301020d1b090b190c08090d0804170604050d0c0f1707030305150a1a09130b0f0117060906060c1501081908040b030a0209220b12 63
    0x9048010070782843e2025416100c0300d601212007807113038925a0030b210782d00351981004400000c0c0a1080031840ca0000422101848885281842040c44c00d00b8125103c0345d002e101220f040c0e10400c89103003107a40c0c04403d004040d00a821096403a0b103080042c1009a0f40040b0b00e0f80d20790860390422000c10004602e02032030340e4107420304001c1607009203011109039000c0e01005284405c90741c881340346e4118060103031030500c1c07103902c003000359881d00c41c0110760707940d0760f2074942d139101c4c61011084c01512245d1040c4042c1c0161030340d90909089402002400800d152004940d94680c1c0380c007950010720b04411b00129030082070818509142201040403004440108041e02500341640800c48503250700d404c4a09003031410050b134070011051001d11040500a12500c005c6129020039042040c0002803d480c519038040c0781a4a8146003032800441504001c000c5980c0913401e000c1c00459403200308441841107120541e80081a81da030980c1802c07540c40107282d80c0a0f00300c88100d00d000c0c0100060380840b54 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 913019640 1250 913018390 913018411
    0x305030a0f032f0d0b030703050a02040c09050904021207050402220e0c0d0e070b0c060a0e03040501021011040801090305130b12040b150303160c05042c0f0601030c141206 75
    0x80028540440140468407261783d0180315186000080c8800840d9041d02a8400c41d001e006400304044100c510070008e00841e40e105c503208000c900189401c24060f0b0800301ea890640c0d040c40e0f83ca0000400300e8010740400c10511072040354544003413409000242c050300880d1000c4455080c403103d4030030f03a0300980e40c02d400746940d00c480c4084205c1003003182200034450b10f1b800719030310242c070355005465038400c0d104a220310b13003401150a01104080281c030243e4a041e4000c180c640308440321100602407201d035010601d43d0130400440d0006080c003a84600500075120300d90717500c1e210013240710440342c698420026000c051000f00c80144800415542040e00408044850303118499a04462030f04c010145030303d44800a000c183c40c04c42095a483c43d14050709600354016500ea040c001924151001103a0038020712241003050f540900c200641400c640c81110340c0041c40d600c0c00c62410000707800135103400b100c42d10700b08941c080346418000c00300410790f07420554084601c000d640d40c650103030004c01103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 913020890 1250 913019640 913019647
    0x15130c05031909120504030501050a110a0e040e06100819151a1207051311041203140d06210f11010e03011b020d080106020c090a060305030a0f032f 65
    0x111226400c032081041c4c00c2011078a92880b2400003400941c02840229095424100004c1d4200003c0c8608464800e10240ca286032100002d821203100c40c45c10300d010340c06952422040301c6101c1c2007256512070650b48011901c04c03402d0120449c42d042e001900c0040d6801c8000860000036621254008106086000030682900c2e41500700350b0740051011043e00f10b00345260030740c0c0503100011500100c40c400d58003200d944080d01d003064190307410124016807610040004110f00d5641ea040d00400714080e241c41e04147c0c4012420380c44c5036004030f10040415403901c41c18008000703030506480c001d180d42c500c04e0305003074000c0c1e4481200309032030840a40005110103900b441c2c0c3c3d01403140010300001c010020002c44c0c6000a003040b400394403501c1840103202e080401d01696010321241416140690003d00f0107010000030000380c200000c08000055441e16000800550104042c2c40211003c0d180c014940325031440c02412100403080c403412100d0124455a421010754461441080403800860303917 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 913022140 1250 913020890 913020931
    0xf020702010e10020715110307060c120b0108010b0705030c060c09010f090302100e010302090a061e08103308060118140f030708030c0a06111c18050615130c0503 71
    0x201f5485000401429000c0082d041c41000419441440a41c200d5143c10710080d0780c0540076401ca40c00c4074003080c0070641d102c005001c00107071803014110749849002160b00d403461805200e41401002d0742d00640c03185020130300001a41e0483c00303501443c4ea035031518040300d9140d0f40008844a010844035001c2c01400703000103045074840e40440c0c1e00c090f8050301d6401d40640c4c0340b400a11000410083c0e07000004840845007140d4410f080f2113005600c3c0b5001195550b04151000440483c8050071024810308000428420340741d4554aa5030720949484034501c0703150910014200104851200079503c002c59028415880c0684ca0f484007001c06851110441c0304d14404249000400e402c00402440049444410400000f8446019034030903902401412400c910003e903d00407074046104000103210104009402030313002c0803400100d02c0f216140c280d02900c640d4244541501c0304e034811802400400348a040010307855050a540c80000c000c0a031032814001c0140c00040d0030343d004402c1b901100710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 913023390 1250 913022140 913022147
    0x606020105430f0201180c151812060b090708180703020409080418020702011d01172707080d201204050a080c030607050d0f0f020702010e10020715 65
    0x20b04008003a00601400401030000b80881e0021820360340151309012030205ca0481c3e42c0d90810b40940d00600b40c00d10a42000045003072094902c04400c20461813a4180140340710b9002d5420081c052607110400d1200355080503020364100c566050300a0024005110040e0341c058015907006001ea0f0106110764800310105040901c2503102950103424200300d002404401d000800880c0c0d44481c60500202d003403104070050f4040c1c040c0207400310300781c81c80203c0c1c0720340c14008103584d135481403401801450b42003041c03820708403042c1c4054031050b0703200d105610640d54940c3c0c5082c50614a500601d555460410410b17554400200c0306410000070105a6442820310034500c940c008041040d82c2044d607103070580707e549820600c1780601c6041d1304c07500003c60800120702502c00c5540680034001c0c6039114101a10b141c0d02541e84020705541e52006c0c4001107800f8420001e05100c1a900986c0d41c0e041400014055603c0d088450321540101c501026039903000124182159901104421012a042c4094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 913024640 1250 913023390 913023481
    0x906010e040510050108060d03051206130f06031203140c0903120304031e0c08090405070e0d030e0f0a05090a2c1005070806220e150405010606020105 66
    0x50707070042d08140c140450008003e807100c0a4601c00c1ea00c80303407035a860b6020401da00445a40180c04217404202142029400707155031076102c50040c0c441d46003002e507020000700300c801c40f169118000f42c0e25007041c0108040c801400c01301d81e6491809000b03a401e40c160701d0301000c00140c12103072070b0203000650b0302d001c1e101404201080d80c078003050b55880349072604018000c002c4041c0c0c9041684a8104050807450042c07150300300058100c5a92410301140c030052100a09000d4104400d22141d10003224150b074480070744c19040362081d80c580340c154140c1030504c481e213204501c40510130007000c4007d00240d202d808810744d000d0300280010582c0300c0c0990644027903040c2d01c202e0002e100306511070b60111100025038a4102c840c4040100300c01c0e500c0e02030803106c03400d00340c461580c00306140f200001660340f201c11154000b0030b805000514901c21a00482c074001d240e4040c01e105448000412041c00000c0c49039400909290009004138a0180e1641e040000e000082c4508039845003d0420f1140da0950320 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 913025890 1250 913024640 913024667
    0x503040c12053d150f170105091b150d050705190206090712150203131704080604230a030e041a0906061b1b0108010b18090601 56
    0x1190300c0001d00e8204103850b140b01c1ca046008950710740140200d18006825501c000c00002660030b07007a03c248080401c060200080c0c0358100c04071500c4007080d058800c1c0e545400502103005080110100401d030349094940040010303400b500001942c0440d44070010255040b804210b440d015552240381007628070b400340f95050000140b9200402c070390f03190040020a16420401e40b40c40848003010001ca0761400201d5285c50117030481e41c0c04104d02caa4098008841c24407803051a114141a2001c82c0100d801c11140d07103100060030310304507003806800105402c030203c42c1d40041d45002d0600302d030b0310359641000c1c0004205001c1165900c203541c101c0600155082103020684454002c079003002881c0404036907120307100ea890305600c94840200a06459484a805412600700e580c6240030050550001d154940305c0043c1c10910174540f640a02200040d021000344075014402c5200005011401c140c002101c41c0d2804c020034203441600d0440c41c01c0026040300c8140c2e4660354100100e0301e00b40103c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 913027140 1250 913025890 913025909
    0x5040f0e18120702040501090e07030210050c161a0c0d080a02070209150108010510170c090306040c18020f0913110d050103060f02092206030209070503100807150503040c 75
    0x101445150420b400800c042e40c02150705019698a44500d10211032001000125980c400d41c01000142010040c2140303520041c02d0007810113126448444c20141041c00c050b491003541d01040c040b03403c07040014500882080616420403515169082c3d44150010f01c0d00103000d028000a0b000c1c0095070112600164064030390f1003a41070002416404810b08010217002c83c082d0800401c0c02e041c81c0500002c404459542c1a0b45010340c00c182c2c504515018200c414414001c11205048c0c0e1800c108080c040c0344074103c5650780528114041000c85808100c820040b0f0040200c04482c0d4000400d495145030211603250a0b80000c0c242c540c01401c4002125085660110302d208800300d141e0300050489020300000e0111102c00c4003994101d2050307000b02d83d401245c1e0340406851007600300e0355410045000000141850f01ca800203140c2c408101c0d4140c000800000030007080c080c08020100042018100502940303051148060910a882580f0001c04c60040005401c2c44507400c0c0c203c004082415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 913028390 1250 913027140 913027153
    0x60905030a030b12071406090a0b031e1e06030a061802031b010503040b090313091a0a03020604090f020405120c031b06040308090409060c051905040f0e18 68
    0x1809036140c0d0424416800030900c1d00c8a80d10141c02c1c100803034244680b900340505501810001c03c0061025800115608900d061101030400d07124210018080c11120625a4403441d006644a06000034500107000340c480080a000300c04204c0c05196400c5131980340443d401c0c0c0c1c0c80c82c000c01c0c640003090202400d40d5044c0400c18010040006041541500039000d0b02c1a1241401c8914080b000c22a031541c0052400c00010300498a6161016000f924650a0300d19180d46003469407034546031a0031010321a51354074084201d400c0000d203540c0340084182e8480b40f58a1071600007403040c3c05148140c522543d1100003040c80d41515a049030301034500180419030b1013405d0010559901001410140240328425020030000f60b10f0b40c24600702038001741003500c1c00b0304540c0c5048a41e00000c0c840354001e91218446400602d03a8010381e07040800781d96070103480d43c0300240c01418100c001d100346800d110b8104010310845842880110944848810700b280640340e515443e041242d0302000c805103409100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 913029640 1250 913028390 913028393
    0x415180804081531140a140f120a081b07060b130c080a1d06040c0314150109090f02030a0f0204061a220e0f090c270702010b1e04050a050708070c0206070609 69
    0x4000355840e4180040700c20907040c1c5009155503002c1030070311200303419040c014003d10911a0803140d600c00307146c030780c0915105803144145500741c0184c1c2c030450707003181c80340341084090414070303040710c3d0a06400c1d030300380400b42d00b80c400030344451300180c8603044480c0c03a00545151801005840310860588208580315032074541418600d81d0454007040b18081d0100b51240340c1141e0000380c400001504104808440e40b80811040041c2242041100d030340d030b510f498080c00350703034248480f030a00c40c02100110703a1f0403d184100400c5a60b00c1d040b141c03060b90b00f00211a80317103401c0801c5c1c400268103089106020708081440032090442940110307981113000c410492200c0c0310702415805080302008503904c2c4a942c50400c1641c46200f22030454464410300a070341401290400c3d29000f0f8054000010090010f8000c5540030004121400f401400e5480c102602d007080d00c14141e11081d0303004c041140303041000c030052407803101600000403c203081c9811019076544c84100c0308a2944544104040c0314103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 913030890 1250 913029640 913029653
    0x90409020604051809012301060f02121605070812040e040c08010617010e011b05070311010e030a08060402031b1e032d0415180804081531140a 63
    0x1c480020195007000c0350088403901c0c3c4900c403c0b01c7d5800d410080340ea6070803c5402c80c2c0c0303a488080010304600c03400e4050045440301d078005101e80c0490030404410858281412441e052040e03100352100e41c48182c00103070306405c54040e901038036429180f11840f6102c50602036401511a00070b002d09510f0050000b070354004850040380255440b100038007484101d01c03401400c95280e82c254420a4004448180f030561041c001024090310a09098080b408840c4100c5d003113400c0b4900080c515400081c104003072580211034a0761000040b00e080d895031820b40207181100d03d00c640840c000346c8010441c401d40391014000740c030440c2c0c1c9400c09107031079141103030615000c541c00f00791120144c0030007510280d0f400448501071784141d811983c8000d448020f00416001000c0341950301e80c0388400200840000f4001100500c028804a0028a03013103914444803641d10703074003910b10b9207110700140310070081031040b00d003543c0000d414500c8203002c0c54031810410103c41c190500307446940142d4000000f007044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 913032140 1250 913030890 913030939
    0x190b0a142a01060f060503091e060601120213450e1506012a0605091e0a0602030a090f0c080706180509040212030a0e040b0406050609040902060405 65
    0x114070400c2004041c40400c0e030807500300c1e010b81c8060711a11002401810300a500840e00b11040c2800c40c0c020f0000c00850f5110b86022824448443d04000d062002c6503030f011403a00103c1001070000c61903d166401d404466071042d1003110203110000420211074084c0c80a06e80f212850909120a0342401484031588103090408440da064034282c2c500070034280000c0c42e5a05403903ca1100c1c541074560400540d41d8220801b1110f2040140c07041c0020180d0500b1300901449108120200c0d89050121140d414862811001c00c0300600c41ca03040c442104d40000c0c02c42d036054000d50016500e880b1000380d00e018012580c80075049028039903170300302000701038a000b07011a190041a211065220a4200c1e80500341c942801080c807540c0c00b013805a0f14203044280c1d0002d10040034182545000050784e41140c01c6448850701003030501400f0019030615000305c88020000301c50802001e420170000961038056182c1181c040e0380d0703403000e1004540f42c80c1d04660241800912101407101c01c1c0428111249 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 913033390 1250 913032140 913032187
    0x15110715020d0519140904020a03090c06020a050a171306270f0b0d0912090608090a1505070903051c1b02060702090408091305040201020c190b0a14 65
    0x224180b48604528451416121003280220700203404c903802103070868104d1018219401d004a0410035103229036168030041124200907180031884014906168904141541c400011b541141441e8000900041030b0540815441028400c86e0380003031411032101d004803100c2a10b10b82040001082ca07613044210000c0c40c4810041e04610b01540028103085603110740b090401481000e0401d00c9944210030191001040c0101700250706045a1200300e420201d1aa05002041000342c003403088aa0103000c0550008000004222507009982d0301c074602120108403000d15640c0301d0105098610813070011703005540140c1120389032040311240c01340c088020305454012908403442600c00e658002441c00c00d0b00c2e002003240381002c80c650280b00f548980140304665030f4408218240541d52184070b004140d07450200001180e180c144006440c0014041c071851050b420203600f076804001c80d80c089000d03154012041d40d185d115507941510045007580c000e0743c20704004140c01d80c50900c031228012000c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 913034640 1250 913033390 913033393
    0xe0c030105130e06130f020303030a0b031002030105030319030b03060a1a04051b070309181d0307050705120f070e0601090f080606010819140a1b091511071502 70
    0x805101510b011540c41c0e1110f20944d41045002680145014010584260064404118022560340003e065074000c0704e1000000b90b46140503d5281010858410720b010080e40440c41c5504000c0040d540e03005038454180522814071001d100580b00ea0000307060300e480541265124140b50150300081c00c100c5401c115904500041c0c00100e25090203a07601070304483c1d1440381995080f88942400341d10071071023034042c4140d40380c001840c00c1d80180b00140c014110000019600400e40540c101031503140080081d941c014800361021802c0861510201d505c125141c4400080050711070b0b040c0504d550b03404020740602c0c50000b9a1048215006100f44404da0b1003820950311542420910700e0760f401107100b194800800555103500030828180c2102c94000c5d5a4004407a19040790181d442003000480720101ca0014445010085e02032002d040c8090302c4640b03940720440c0002051600c003032056581c0305100440c0503800c9401803101c4002402c41c0320a071000c041e1296604000c5940d44030340c0c034006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 913035890 1250 913034640 913034659
    0x70e010e03070e0a240303030903081b03060f011209030504080f0303130305090a150f1d03151b0a0206070206010501031401290a02070e0f010305060402060a090e0c030105 75
    0x500d40490309000781d41c0407107200d20075a190070b44c0810043ca002d458400394408142144c40c10500324003254401148641e40c0480e1005440c640109560800b42c940c2e4184049401518800300360342e01540d511020030ba695528000c0c40400484110308030ba80740b45410780c0b500000c11305040c1e100340240191041c6404440e110010134008036501d03c411034002c4003072240950b4203c0000d01c40c60040000354001400070021980780c0d0b450003100c42071038240c40041154808030011180d04902200322103030310101d03680d10700020000481c0d200e048078160f14601a04140000b412136105d014120040c0742c40d12804e80d02d484007900060341d1a14166400009072068400000350b41d1301c2400b030740d100c3d440020008401a46404400c0703299011907012010421244040999081a00c401900999481e54010510140303000c10800c80c000c3d01510303419461500c40018030204e9000102e0940007136040d28603e42d140250b403804c0b0b0750b40b240f5400108540241005004864a050000e541603420481d90481c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 913037140 1250 913035890 913035917
    0x9090406020913290307061b030315090603140601060917150a051012051b031f0209010306052b03180603090b0a050403140a020307050105100306060515040e0c04050306070e01 77
    0x40e1b410240c418180010107808550b00e501e40720486004907503200307003400706503400c200000000124082e00181d0701341e42d40705410800d015480340511004114003020300099410400c005120340c0d80350007840392000000340342c00b04150007006101480c442c45810311446040440c00d400c0608000d0319104c034140030094000c00e8840304000c61080e4141d01900808041d03c8407003001c9001350807200d14039032500450001d140c5c610302c0035000b40c45004a0079030040e941c503298800501100c51a07001240280201f0b0030983c0c4074041a40000c0a001427000020b070f0b020034034a011200c0102121181240100441e1700160464051b000230151300c0c401e05c0444015525801c019049a104480113400078081220b03544681745400b0091441c107040b0b1040d6887c040280d120136082d5107017915121124100c01408100f07114551262001620007100e2424400501420781852406540202c2d60501d00720703004602c040d40d000c02220020030000c7c09807a001c2c5800310b07000c0c2090301c00b0b040007404901c95980d01765 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 913038390 1250 913037140 913037143
    0xf070504090e0714181303030b090f01080607050c06340e10050315010809010b0402121b040f0e06010903020d0b0a06080601210501020c190314090904060209132903 72
    0x31941c690b0341805241c0c903a1000d0446c0301516a5801c2a002d1583d00c0011036030740d495020203244a101c14201500c62549410101e501c0c006004010404100381400703540c1c29014085011a00440d020401c620303e1240d005c840030f41079400c01c4c18101c0341030300424030308452500180101c40c2c082c002c80e205281c400144d207040e102c51004882c0c8903080145221480d0041d03019500c515001a507a6000080d4150340e00e0118040b60f21440c6600205d028507010018107c004180a203003900c0c1000c0403900303003407901c5070b0380004075180d0283c4110700798580005541a44200314040040d0b03001031101700340481508001c030443c43c0076240700c1889824400040380c0035800040c154120740d030a05c2e10300302c1c0040c0004d005101c00a10b40c000c0b070b8295004c0241e014403801c20082200e03140341016680d06000743d54500a00414400007482c40100d0003840344041950303074000b11030342c01504040301580d100718840c0003078079104068010226251038011760308030015088500e4140d941e418108488900d10500c10117 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 913039640 1250 913038390 913038409
    0x1b060105060412200a0b07020f30210c16030b0115050705031305090a0903080f0702032205150414010e030a0f060504030e01030c080f070504090e0714 66
    0x1003d140002a64440042e0500821203141005071503240c40c2d02c80c2d0040003c410391820790143c000c2a601080314029450b21002d04460020101c2d03a40c15011001102c8403e5500d00c00c2d108480d460041400d600241000d2128a00304c45140761034420003044450030801c02d4005400b04103030ba105584602210000b00300c09402a00d80260122145a2810044502c5080c1556084c004c01c401406400b0000d04200042d150101208001440c00d40c00c0605108200340700400201065007403da013400030941040030290400c2d2241c800d1200345d55182020f0307280d40305400998000d800c0c003843c6ca0b421540c801c00018240c1e0f0741141c1705414548080407140030b6004601841d0030710311481000098a40c0a5210010fa2880c080c00365426013072252282c40780611000015112a03495000b00801c041c3c2c000020710f160003090038100040000704800411104005029a40c5842d410300881c03011802081a2402844115814480025140340d03564861469100c2c1070502284001e94030040e01d40403524 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 913040890 1250 913039640 913039649
    0x9060f05090315070507080705011b0c0b0a1a100f0f0c0b06040e0c13050601080a0204120f03110f0c1807140a03151409060301020f0a030902151b0601050604 69
    0x4207009030030f6401c11010740a02070600030501c10700b00302c80000508020007030000d00d4015400001ca0526400c11888420306601079142000544090b0f8400620300c01c40043e00540094000100707214401c00c00108400020382003584022005102d0300029401019080814501d6440714003003420300c0d00a540311442404020407035a06800003030034070705285d4003120b4001c038110201c444801c0c80c00b000c1240d020440343d403440119111810800c0c0c0d9600121050307002800001c0031454a8070f030402e08512404035540060081c80c41c03080040c2403520910b54401c0103100407007912810120550719565545100380407501900c0a030110401d4101c0340c00019118078203541720511072030300c24008103400703030302c0001c4542c00d240e501d204200c41c1c8112071740641c2c042c0c2071801e04c1500c3d080344001000140707600240039070701c02c0c1e00400c0200650720a500541d0401181402c0200710741c1c100c1d200007201044c0a21040c41003100200b001c40001b20754928051200807034609554090340c03210107109072403189014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 913042140 1250 913040890 913040893
    0x101e080f0f03070f060f241e061b0f05031b0a0c140a0e1003021f0801061121210610180504020a03050412090e0424060b04050411071104050c12040309060f050903 71
    0x300045030081e009400d01cac144243c0308007031a20031039581c0261250a8402a070320740e440866040c01c4580c541d01255690003c1c00024201d481141c0e8a106c900495030181c04600e00040030b40303100e1074541c0c1d007012010b04540341c020406403030a41c0310540101c8861005a204241e070440720200074511010f11403c40b1925030714030540740c1c00c02c0700550b654140003410117041c0c0318842005101c40c044410b0710b04d014451140066840031522403441070080c1c0d00c1d580381003d41c25070003440102e41d552100b000e225003090400702c056038500100600001c2290341308d560464000030f03a44030703a0f80d416800706104910a0042080103e41d16404480c1c1c140c2c103000b50407804090b40003284c00b127040000440010804049114210010302c5203030025900307182d011941848012405201501d07007030140307028001e010305680d410700c1c2e840e40b900760000c48003084480c055981c50740441c0394050400215a2100080c02a40d03010b03042a14000f0680a0140f00c1d09000958483c0e69240c1548076074101d64501e0360060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 913043390 1250 913042140 913042199
    0x71706090103020d031218020906120d030b0102010f021207090b0c070902310504050108011401120206070c0e041a13030305101e080f0f03070f060f24 66
    0x20b00f030141d02d104da10010384c10321014000040c055400390241100401040410405030820b5105003c41e18030060800c0f4840c0c100e41e070b11000d1507040001c01d280041400d01d80403400d8840080180d005014a000310032440d400010900e00c13100e003802e0941e00a414680c4c0b050388132a030703900a0300c25600078003030f0f1500240c20000040000041c1071700030701500030000f44080d0242c5042603024480c0c2136543c460700d50003011258200401d00e46807054500508030b0380001d0210001c95055003004800500850450b900c038102410203549411003624440342d4010a0150440e888608000000750100c1d012501703916140146441c854562000900510000c401c010911500d964146c0207400010001e02e08003c0804000400000c0d00314000b08401c9002d03501c81545d414035480c4d50401d40c03845003400b1180c2c01100b2203019000d00201b224041604640780300031404092424002400780c04580e15403080c00c2220000c00c00c0648a410b0464409101210941ca0380d03624054203004050812802c02a060b038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 913044640 1250 913043390 913043393
    0xf041211250b09030319090f0602060403030f050105012003130e0a0e1207020607020d17131e15030b030109060f050a20210a020403170906030703020c0307021305071706090103 77
    0x12104268002043c00d0241d44a0342311440341c81e04520651003940142d115800f404103154043c81902c801c00792400c02402190704020020f030651005000c424030813030204500003c02d000c18010f54502d00100114000e4880d60b036030240440c044142d0311030f203800d813510790820014600001c45041d00080c00c0c04082c10040c0340d400700111908090780690700300c1e0303480c01d841000907103800c0b1005031080c2014110751140652595203042642a4025103000f90107102ea0307401e524001d5500b1000c41d00e01009015003900b504c00301710060b0001990088e05982490214420440b040e00a060081e030440000c03c8140d880041c01000c0d120700e00041d040c82c580403e01c0c00382c070f60104030080c1440c80c0520310100ba0490381700710b480005c00046418559a50380418103104100440c0301550f046180341002078145404900010790f14440a06000305041d4000386c0003420450920079076120a0700180b0045000385a0102140a4a812105680040d01c11000000c020740c8140d40e041c080c46000e00043c64903820b6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 913045890 1250 913044640 913044667
    0x1032316090506061e031b1c0b1f020a200d06021e0403060902090112151802130c0212070507030b06030c060c010c0f080f041211250b090303 62
    0x181580360000c00402545450a4003c1c0620715450710b009105c550301e152001c0040714004401d614040200c0b002c00141c1d0010100c08051103000404c2e40002400000380b4000480714201b07808102900d291b0749008007581c40c0c003c2900b25140f4002c2041c40c42c0c40301a20383c802d46c4243c600250550204c0c803d00c004002c591280d0291401084000121810a03488440144e19400603030081751540e07160104842181884118540144403030042030552002c00d80d101e01200301108262107030300d540c132032010300040c2940c01c011703a1072a0090500c0100c40c0c9011801006007105420f2100584a100d200702074102d1310008843c03d0581040103460500d0442d52013210309400079141590500c40e048001d009561035100822148031108000a031040d000e4401411206803a100d25081c4041c010130003e9041e13804100f02d500580c00200d03501040a199401e4581c22840d000422035403003841d008220010420b400400d800b0308520002030400d5407500c09107040d200d8045800d4060300103000b170202030190f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 913047140 1250 913045890 913045901
    0x13020c060f06040e0f0f07090c0512090a0c09020c1c17090f0316050105060d031b020d14070e0105060a0f120605031507030f09110105090f090103231609 67
    0x2c0040001c142d04200603c001e00d0321480401c440c0d002d811800c0900d141c142e0401c014030060501400900030308014250260650250b240780c038418040c0400014104242030019099099000812440301d03507c40b11040025001542ca006103489652134010220b008281b00c413007641110341e10f8032100107050011442841d00500303640c40520550031036118421085c4080c02e1000341c641340015040a031802c28500b942e2014003a14021041d0701b100c0e03004264040c0179405003010601c01e1b803e1a4040d8804140825000075018003122203100001c504c450022402c0700803194004c0305010a66215810462144100c0707101c070740410007113040100210301403c00700d035007004482c0300041d41c1540c0e00080303820910702742c81d00c0d0100b0000000b0060785640521912201072030600040264100035640d480d800500140c181b41400004190039860ba61084c00c8500c000c50b018218201959491070140095172440c41d00301248020146082e01c8040c000822402c54904694002034071450280048021306 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 913048390 1250 913047140 913047151
    0xa1701050f150d050103050604031206080325051f061a091c150c030c050c100b04020417010603050105090f0d03180b07080718080a020f01030e060c04030213020c060f 73
    0x40050002292115141c41100d001b50f0103403001d0b08551400389002802d840040c1064900c4625100003400a140004141c8251001a16192103e404440c070500d4004480842c01000d92240c40e05c0794081310040311000da5201000d84042c411143c48030110301c15000810143c5500200034024000d083c601149a61130006100b07041901c01c100300d454014001c2601019203031026200c00e0502c03125036044c441d5101c080d0480c039065003020031031101c890f120100034020031300d42916a0072107940350b5035540c11503005020412081c13810b0402441c1d4076018207681c1c84240c49952070703c00021066900411100001c0640d8005000c04072209801a001000c224035a890811011203d00c000a60210b0301e40e070003040e568454400314503004500800300140e0041b2040268540581006842c00005181e10310503811183d0000700085000100d000381103070040d01d405840782c24280140d48840d00020016070f4026600c1e018042614640c0001b0f87c85280c59669095114400242d100752010380541c1c4c004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 913049640 1250 913048390 913048429
    0x20a0503160f140102190c0317040507050a080109050c1c06020c1207032c010c0b06060705030f040f060503060f10031b210e151503070b0a1701050f 65
    0x250706440d080b039865140c0d0503030b00d4960b500060f600080c00c000c2044c00700310492032800c7d40048585581c02801c0d11a250b81401310744201a02203000c001060200c030002d030102030820500e0343d58641d01c0702d020300442003050303030680100301e00070301c19081c100c3e80e00c00300344802107440c0d4020034a642c8100003580a00302c151b959000341c50171101500c600d40000c108181c025913980c0510401d803800205040b00b010f01d004499500149000c100366049440002101c0c0c03c1071040340c1c130795070301004180140300d09040107020b4000040d4110142020b500a803080d503030300c0180b0440c1c80751103520544141c8025500d00d0380c00010700d0b0146000d03161440010858030781c0c0745008290802961044444212503c4228020030844444001c00558543c81071845101c03901080c03100d13000318406140c80364112820005844403050003d140f4005803040078880c1a000340c11559101c0c0d442032800c5030b681090f040c940000d09981d002c4c0b01c500f520701c08040c0c160741e802403c9541c00c61034a4200500544281d44810303d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 913050890 1250 913049640 913049663
    0x60518071e0302040f0e010e070e0c0d09050a0303060e09060613050402010e04060e330d08190519050702090708070c05100509010e1504170f0d0b03010606020a050316 73
    0x140c44078010700c9800202c1d2800407070000d00800005003580c2500e0079500701c95107c0c2c0d4080180950098100f0707002f0030500720143d52400c213100100701420241002400174030520010104140d81540304400b01ca0700310b0741002158071283c40740b40d190503043d40d5182d0b1000e004219580389101a500098006205041c010640310340c3c880030409681080d401031401c1140c00080004800080d01e48030003c0003c2643c0c64001041c2c0c4034920b409400c0c00c141f0354020000101008204020350040340c0e40d26160003040c1c1548200e07488014040d5015109c5180240780e21484103403418010380940b07910a0b8003d181180d90740e03da0000701c0711000020b010070b007000620071034031010810500014241e50540d02e804030702031a0082c010750945040849803109940a00d00381e50122164007a0079411a074011608003200d07550300690400360245507507407100c03400c1c0010005480c0c0141d50101640e00c909500038842079940d12010b0343c8071400d011000d0100d4000b00940d241495400040c00c401d0b81c07245568841 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 913052140 1250 913050890 913050893
    0x302030f0d0e0607020109021302040b070618050f060103021c021807020c06121f0b0706050705070b01140a3c09141e010518130b0c0403060518071e03 66
    0x2d0f001080c0c0d088000750755210100b00650800700149030b02512040c2e815480d2034903110002c2c000744a400c9010b400c85a0b01d1010710403206480c5100707070403144c0203800c60310701c50900c8039080d403555000e2108901c100c2e070940420035100840c10340030075415002414500c0e0303104a000382e82202c08001341148114020880c4d405a00d0759007101500c919401c02d40c21302d050340350001019581484012010b81c6605681c030003003080e0f00862003280c003607030b07884034011074180c64140c001d40d03590090f00c0c1d00a1200c2d4080001150701294084120a99172044482c0c441c22a0b450404081e42c45650340b0701e40e21201e0803060780300380c03e11200180102d100d600801107851656134080d04101e406c1455803030400003001c0c09122200362400104000c1b06001140090b10f945043e0020b4410203203801e81da1610101540001c0c40c00c1c18101240308425000007107030030280740480742c5000d560f0003400112030081c9020003148240740c021404880c907002000c020000d00b8200b8000740f0f41d84282c501140c4808805800200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 913053390 1250 913052140 913052143
    0x21f0315060906020c090405070303111603200d05280206040305071712030403030f0e100506012a0b0402060c03040902180103140f0903040b07050c09010609030302030f0d0e 76
    0x208641d07a00c2040060608000178100600d0151741c0784148141c0082c88003091021440c4012250716082c2245450440701d945030500d04000001c5200e4000300c1d4000040c4164450011030003200b6800041e89141c1e0f850401c80581514200681316500a408000262903044040100561034030505800c4c040075900090781c80d44140c0084545400100042188032144001003882d0ada07248090316864454200030115808000d102808058641030a90f940301c140d40d203c0308005e07e60405640d5100340b0508400041c18065400070f001686000111098809071446034031441c021038028047c58040351a00c10705020050402d9a05c41002c0000f200d61600030002000100901e0390056201c80c0c2c003810305085c0ca00720b48403542c10325080c0100f00350129000c1099582c000c0f41180400750030f40b10801030601c0e50007650491044c8100006440c4240b06000030b2000980c42e0813034819044e6030300c500c1d0888000b0799511000700507034018050414005e0100d4042d14204582e07400010380c5000d00c11074107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 913054640 1250 913053390 913053431
    0x21314120610172a0109090c02010605011d060304060b010212120f06010503090607080406060f090b091b160219030b0601081501020c060c03090436021f03 68
    0x403102060240001c1181c056600e0034488141d1050020344011004a001003101c41104400c07502d0410307a04c0c1c0c24003096802081403001821102808100021402d007001c0d0007080240181070102d10000c000480c00c020000700101d401c80d001d03100f541940c0f07581e40c0c0c110190400c12142c0381940511180c4e20b4802c1d0046028182c0a03031114603211050074a00e20206a405000d810310341040400c1080182d4414002141500102e5900c1c00e400c1659442c24181d008181030381001c0240c034000140007445030308640003a00c645404542d00c04d5291542d05941e100c10f0204081d24076809010720841940054503042c008415002500c0a00036034020340304209900951b030000c4500b00341d050240210795030320906140d0f104c2c05d05a00d90100466500000c1e40d110066445140724200010310110152018800e82c0c2c0014005401480340010802c0214484401100915201c146400081c52201741300103210b0307009900900b00c61052480484011050b40304010308200b4151180090724030450901c50a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 913055890 1250 913054640 913054651
    0x13050607151a0904021c05010507030e010b190506180402030103141006050102060c070f170a020d2f150c0a030e0601080715140c01060e0106030213141206 68
    0x5081441c00302a05407801c07a215522000d00d00981c102540c1d2030307601d903c4501500541c0444140036004c1c2c00c42d501110020711002c00500719400d090500410350f4054100c4084040010300a0005006e508148460006a144408890b5003490820400c604222004050411400305903140d01c0c217020000c24244e900a03802182c8103000e21070304500c2d0b50301c103002450700d040c440310040c001d8a28200000f035031900301400401c1c1c510400140c040810081041d07048034103600042c03074a01c40b150104c203c0348a81010341000094020440b240802c180715644e021042c01421070403a0703081c3d04c09043c801d41c52511404d41c5031030b4481d505041d00182260050b40d03205000403891140d0314412150010f064444140c3c0321415a400b91005118803000820110f05555004400b00a0503646583c2202d541d44100c003031415040700051070358000c10041d0071a80c03d5591011515000c2d980c0c88408400700d2242004040700080e01800a000d07118954840442d0130100520200b0380004111405040100071303a403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 913057140 1250 913055890 913055903
    0x3111903020a110402131a130e040c060503010e0a15030506041101030e0f06180319050406180503030319111b0d020a050d12090b01060c06050f01061413050607 70
    0x302d10041002c400c4180c814003206407415070408504c4540d0000245803801001d0402441241500c103000d903440503640000080520900426554035424058050a50303060307414881c0d41c50040348441c040c0c402ca90486040c200320807040d54410002e4002055100c044042030300410034000003044040015034061800313141e1581c0580ba4400015040b0b81e0b49801c003d086400c10b070500482503201180c0e0561145004648100e6490120207142c01c1d8414082c442c4003480b805261441101c0d80500035100b60344071a00ca0007000c40702d00900c0034a48915220307075941a80200700081c400b000504400700200c1000c4070104120314240c0a00059412000401d510707074a400700038a102c58170400070380040000c140080c14072000c2a0b00c400792a888480100dc0510a0302180c01c022100d40341c1c041d210b4190808521a07803561589070080181d12203034401e5841c0d40c00c00002c9942e0311170711401c50b8100c8110342c407041801110600c28031904e070402c8581c9a4900c0c410400081c5036201c040080c4a41c40c41401d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 913058390 1250 913057140 913057153
    0x2210c0a080f06090f0a030c02040209100807030c030513020f0a03061d1204060507081803060a050405010c020d080612210c060108010204030c031401020c10062309040311190302 78
    0x6412030f00d4580028948540ca501110320141d0400010070110a8160903141c4400d4640d01c07400840c0c0a48a14004a82c1048500706400c5289500c0403040b4022070035998144081072041c01c0c220203881d41901c0071040c100c5145001340041c03038200c411916001000d01441541c5079139031100822520103010741c003d07040040e00d018840764000e0264400442d80e24600a080c0b0781410380041c103a0148080080402c6000034902181c203c11544c0410103442c018100c911130320f4080303c0c00001d0320043d10100d98642c01c00700c50485860010030614034048460f07540b01c0c031640d90038042102149a01400d0301c0c240c024610b030b0082d04000e8030000000c0704010140301c3d9665220000701454400140d110151030b034810711041c000260101c02510071260048007d5081100303118441c0d00a1007083e00d5481c2d907104203000500f80780c0700c640005c0c0844280002d142c03100b800c00000c01030240c41c150031041c0d0100d6584002000a030103154840301400d690030443d40c6801d20000641c0ca4450700e02426800340c1c4c00007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 913059640 1250 913058390 913058413
    0x906090606031b06050c0c090403050d05011418090a02091306110c1c3005070c0c0b0405150a0e03070608100b0406200309130506090105030a02210c0a08 67
    0x115040f000030303c400c1c80c0c480d1821003078442d42619902142105d91054805038046030070300d803180050b51100c980c17103002009070b542c0d6030b0300e82180c000c90891094020070540e90b080304441c00303032000c1622440d64030000e00b031448515800c005909400801d401c801a1207904007902240203441400026400004072940d50101410341c030b480c201a0b031004034803900c68070746196945948141c0b0b9140c00c41d107c20740c044003d1401c44d0130107100c41c00700d0a2610200d140900b0464110303401000020300ca07000b80c0103100240c0c1c417420a02c2d0903100d40c0c080c190700000c4285c0e0400f14400300900400d001c405074034240001013035042c00642001082d034031040005400c0c40074400c2980c948050500104aa043c040d03141a180c442d010b00641072031080b0300041c01e0240146a0b5565080c4102c680842006100e50002445c0990550041c8801c0d90603900681c1042c002282508000130035003989900184860b03904410350007070741c10105540601200d94005c09602c5120b45d00c80f200080301401c101000b0b49284c1074130 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 913060890 1250 913059640 913059683
    0xa020d08190c170a02071502030f03070c06141605180402120a06150c0308070e151803060c071e17180d030f03020a02011104060201051909020310090609060603 70
    0x40003c9080c0e40003041090b0303c00340381c00241d00340449582000e0340c40000b50400b000e074194001c0120101e85040c0020400c40941c1d40000c500e0000380c42120100502201001d6103e00c082046079030f041c03480c0d02103051420080c0a40701a0a071700c0304e00d01c00c00c201c0380380820105090b42c00a0302c800f800c1c160080c0621050303d403c2c0c054400a08200002d205900305000070007042d081e1034160113000d02501c07102294100703108990080d01c0c0c1001900303400603a04441201859540403031415480802c41c0e40c1e0000451401051807409050104200c030b0408140f5252040c1e80c07004c42c0460203140c0e21000d1080c0c00500b001078000522210b0542c5152640000002c10140f0b8803080c80d09841202c181c1c0000300041e4010454040307002c0d143c81d00584035005008203174018110841c2c0720a901030003007000260564150407043c410440030254450b0501c90b2040c00c2c0964414100c02541904040d0415011559503800900c3d0280102400303e081c00807138885400f25841508240c8d41d00c0310044034402c43c0a0b6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 913062140 1250 913060890 913060913
    0x11707140708040801090501060e010e06010c02010e040b181e0108030a1b0506040f02130b031c210c090b040b0403151d0a0c12080301050f1909020a030f0204080a020d08190c 76
    0x2869110039402e280100000b441c0343f9490400905024916007100c100d40c645a0201050000103009041e96600e510b410071001c04045813902e444900321072841e106600d2044686040358940e10040d030a040350010280c804100e400940758203880fa44003004041803041024a00441c014030a1303140f00500b900511072042004642c11281504040340c403038440d03c000070745841c400394441011840040303030807086515000415084205100f031442c0f401e0074001c5a44120500211a22802c84035592a40102418000c0784184041c7c0c01c2d01380b000300701282030b130304080d00ba044202e800015072503201c0702c011345d0420b034629400e041e640c008400f500421500e886035070054004041c1070810030305a80c0e5402d009100502880e80280121300340c0031010380326610003940d84246445016034103600ca50001000750070800a0b500068201040c0d00b14118452080307506940c0110054148106182c007070000580c0d40032805c595051040210807190f0040100f81e40c4281e0aa503909902241e5a0601506503075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 913063390 1250 913062140 913062149
    0x3040902042606180c031f20040e0406140c0c0d020115120c09090b070314071707141903060e063a03090302011707140708040801090501060e01 63
    0x52400504024441c2c0008005078410501c44d401c8030064540e40d403080c1004034042c0210307058412001d03d0001104082e14928000242200170003294425880b2aa01e600403091681c4074500c042000340410b0582d440c903a5805802440c01161540000c6110b1104c0b100440724002c01c9c0344003150705d1010550a00201c4c407030088910080c40740508404403240c0300742040c490107400480d070000d080c04214040c2c9828006040080b4200000049424210030340c40c002c484480010340b401e00d00b103c21900790004c071405901d0954504150701d02030840c810b05403002818510600121080c1381121910f03610043c000316400100102802144181c0034080d038140780c11144080406004000b05a01c0b444400400d458413030014403001d0603110b100201904da0040405403c6070700b080348400340f580045240044138400e0fa55481d160910f8040d000340742d0416644480002c1c0d600b0143c051070701c0d400001e4100c040c001c088031450140c0e680a0a400c40c0d440c81403c80345a5100c40040200d002d110540e00d0052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 913064640 1250 913063390 913063439
    0xf0306031e02182203030b0a0f0e01060804050a03051821190812041b0902130501080411040509071e140d030e0d080f07050604061523040e0304090204 66
    0x40c28041940e2043c044440483e803000111404c20a003418800e0b00000e034802c201071310589249440e01c0b400740240d04940521030011403860000614148141c4045200e5500100504144221540c0465095000140d892100c107202d210b443c0486e81c0700d00312204002e51442d0541e90210490710050300b880070403940e02519440e100c6c0c800020600800854482c8100f6080d801b1003990b80c3c1c54116654201c41310040114031180071f000c50b8000b0641c0c01060805800306d14904041c2c0d882c2d0045440603400c41c1c00500d58140491002e5183c1403540100350412a49d1050b20b00044e1500483c5050600708501c1c424080b01d010f000f009036403404543d90b244510252500700f8481e034191805003a9400766075000e030168007030808a000f070000070300681d240c54219070070082d80e0391414101182c5d101001d44090b00c0c684c0c60100d142070710341f10001144040302e9050160076001e601fa201920b40300600e00f0311480d0800d884240c8600c0c2c0300014801480a4250040010388075400e108400181a1141032908488c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 913065890 1250 913064640 913064689
    0x60603100b360910060b090f0d02010509101206050f0603040b060406050d0501020c120306221b090e07030c05030a09050a05100911150702010f0306031e02 68
    0x40d1155001c0200c14080071210b001142200c6207107044002209051540c11a00c02041c4640b4202c045001468104045000e00010b42c58468804a5120340021268010655580c01d40ca5007001d01d2a0f18109005040c058140310500c00400c503620150a0001d001468440e070180c86050a80304807805040d086c2c40025003040c2d01c102007078003403002502c0a0000290080000d03019610b85d04001c01420003e41407141e0041c031860014045d400c2040801d64034083c048141034001c4d0310b00207a0b8400e00d001428017001c0d030f503007500301103011005c9520b10303201d1911010100c5008020105c0c48061003483ea8441a2191410580300c2004e040a0002420181014500c10840798008141e82c2c200703444040000d003c1d0340ca441c05520340312004030000d02e10f0045c40c1c0c0d00500100203501c000051030140d00c081010840d0101003041c0742e4106140c20681c2d40c820710025015511405c890702d94041c95080004106032a03403154400714407604003079030a0441c01a0b00104500b425103219140c010100e03020941e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 913067140 1250 913065890 913065911
    0x20405010f030b3d24020c0d02030a080708031b090d060e03070c03110301062c1806090105180c01020a170d020c010905150907050103110d0c0206060310 67
    0x1c448024000b08a20001c07481c0e1201c0801c3c03091034841380c158000c2048510344107101954410180f591203a00d1011000e1603010204060041c000d000c4e18440354058000d5840080c01c122000c02c079460240e8061045008603c00148411300a05619004610903034491409441105120309294585501d0300c4080c0940d40c0d683d15080454644664025800b2618004541c00c052440c019042c0203805004189000011b0006007018847e20150943c020302586894400304078007804082d02046204131544501c3c10602000310f0869081207035444035000c4019140c02c8540341610580d1924800c0c0d54038428030681500c658a59204036004001410845404c1340000c0c0d1038400411000c0d080314081429801204003d0045a1225440d108119100c0070000700da203000b041d00720001c443c584100b0306043c02552446921a00c50142440101181401c08004501600741034403d003501050500c40406450341d01d0040c911901403507401880c0c1ca14210040601d80713103640029002403468a0341111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 913068390 1250 913067140 913067153
    0x25081608241b120a050f1b07150204150306050a12050d0f0302090a080606151e0a0e04020d0203071e14070804081504140c090106180509070903020405010f03 69
    0x40e0700403594605000e15803002100c02c0c882d4469a0341e901e428400c032a0400c0110112035000310700803031150141401c02c1c3d56424100403142000d49030785070411410722044000402c0c980800440c0381d001040503042558641154036135503082c90444e400f003a120001884031703042000d030940003081c0c10000d03414402d0490311560344584400b040241003120a00500145601070b03012a8102c140c0908005007050341c036900b07191a0181a42d903184108194080c8440308440341d07041d10b0003400385168140d404103204001c154182d02401a40d0705028005880c003a00342e503640301510013076468060140c2c0c0e0785001e000003866155001c16800071220755906060035282e114904141304080e141c80c070703950f03010542441412801203a1103141548145251184442009440319025910880b60345505060102d100d64071180504400c40c1c02004240041005601c2101207030301c51189106001c00340340d181c6011440c05a003c584401c049560f043c0c040003107090900c596401461000103d0090605503964030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 913069640 1250 913068390 913068463
    0x1008011107030e19030b0903090a090c1e020c0306010914070201060e0703021606110703020f010905060403080703021e0318010204030f060510240809060925081608 72
    0xa8000e00310108001300c4488902d0050300074640005414403546821401d169890380213030700b907a0007042041c0d00061a0001c80c0070f0084064801d894003a0315010b22601d04010081d401c1e001421440380300c0200700d582e02d06000b040e02030300c00548080360b0091644450104088047c00001c116032611008000146a8070030040d0030a14624000d40e440c00c11310003c00c04100c42d05400b805c0c85260103412500c50301c290300206541c9100f034090312824014801c4e400d08850221002419540240c000140000d200e0821180c0c0700c42141401800c00040300e21500e9540c03010701070401c0b000c400006205031010100f5500020101c001c0c001c0d4986400c56035803226000c480d4100a04040d214000300f0401001902c0a5019218001c000070018091541e44407910030690070400102c0c0018000c01c40392038010030803d10640d058401000c0381c4060000e10041c1e03c400001d902d44e442801c3c10082046903060004520320a803420b44848568103004401c0d00305040e04c0e440f41c401c5014001c1d944a030400300340c40c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 913070890 1250 913069640 913069667
    0xd050709140609240d02120709050105070b040204050a0231151d010e0618090a0603030206070e010521061002010203061507021c0326010803070f06090b100801110703 73
    0x8070b031091139110081404d58003a0345502e0040c41d001280300d000b0600e1007006c0c50701c118038035603c1990040c1d0ba400151264403810f4405401566028005005424140c001c981c000c81c50178001807500c15a54003540302100070902481c91800b2810b10f0012401c0c1170317a0517074080e224004a80c0414140104081c00000c0b09149101c000c4202860703500749a8043c200303904088401401155039160f01140000403260560180e41c0b048080102240800b1041d01c180000e4950540042c042138855940645002c8800c01540307040280800002e07601d408900158480c031080c002c00a443c60070090b080121164201881d0411a8810300070003113a5502c5410300c000c150100303003010380d07a94014001b0540c200c0903900880f0003000c0c841082c804140d0b03c00c0c0f10090300100d1040c0c1901c4107582059401040800303200f651643e030b109105030000f080038061624a4244100d800240b040e80643e00c070160300d01c080300d41b500b800b0006a400c0080d50320a000d2440701e80c0500c5030551600505030b5019141c001c00010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 913072140 1250 913070890 913070929
    0x1504110d050916120206090a0303022118061803030415022503080715020406120c08040b01091e06030b090708070501090303050c0c0d05030d0b01090315020f0d050709140609 76
    0x244c48003951144400c44d2400c04001e003000c42c81c0e517240c0c10065543c0c48003404d0500c5641056500c06150307140841502c220204c0c882d18041072916a404001c8560807912040745c40c1c07180b5005290070b655007040108000e02103942041400c802106029080c071440100e443c03003c024400a010848014440c40d1007900e9000b100c868035002541410440080ba00400c00e46c04c80c400500410307600e403c41070007181c0c460345513000c2c4410900258221500340342a01c00520400060006124441c2c15402120050821031220350080300c49824060a4607020b46c01070307407485581d2041c4018286c0a2265101070030052000300007080c5000300003403980c2001e2001904119000c14542109603043c400c0d40004403000700001075118103410010303240e074003941030310044901d00901c061565001d000c0c40400c50740c015203000c0000803181b002801030b500c08025400300b00700800c000c00101c0070f107200303550007150386603960014181080c1c810b9070101549032406210380d200380b040200d19074820001e80080c5201c2c40c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 913073390 1250 913072140 913072169
    0xc03021303080f072a0902070c0b0c0312010b0d112104020d140d0f02280f1203050118110d09020a1d2212081504110d050916 55
    0x1074600d0804d001d5441d0040120701042e43c865802d107183c2003000404903408450682682d62010301008030301c26160020500752045e10300b0002c038401d0308054018400c408040d64904801c00701c03c4100d07528260040004041c02240c4100140168802c040e2458030810080c3d10303018810080c54212896244078500c4d5102c1040041c0864030b49036806880c10380d02084440010700034070381054850414609403000189845150302c14a8400503140481344686400b00a21403108403698482c00c1d0a00e8090740d41055445401f000298891940800c2e04140e5800051039414080101e10200304000d600442030308025082c076031403505104440050010310f45c00140e100740c5201044524402e980b15211390081200c0211451000c2011079220b1b8030f105080880002c200d929080c0311003106400a1700354104d6035030003a0381c94001d40986400070600c10b116542c03c002400050f00780c4c1d8091003440034861001c5908480302c0d40394043d940d00300801001400c0e4207110002d926800b60914401c80c410302c060311 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 913074640 1250 913073390 913073407
    0x3060109030605070305041502040f29130812041401180b0d0b0111280809040507260c0d0f0e030d0209090106140f0919080c040c0302130308 62
    0x1030301140000c680c00361051050f4600601c0140013000112000e440d00e0202201c1481c80c2c1101c2d1003183c0980702590980d2520908040704400607044545103100c501c6800d01038518014025000303420401c00070403401590904085017182002d41c00e04154110b98024801480300501d84a2190203a00b0280f03081105078486070301410002c2000e80c0068496100000ca9982c0e81c0d0064100859004080e20388103400f6914840b2a681e03070b21403515285107040e0802c200840e104085a062150501543c580d908041c11000000d017107810941d034202c00b0031588401e0440e1400e9100c0c4000f00c11148500804051404d401051506d214500b81c2d12140c40e0781e101c46a0000007103601a0034046501d004a98868084034501e1009511032000d1030310514003900001120741c0700da04c01400c1e0030010301d4007d0508001c7c00f0a6000b85d0001e01309968000e07507c8510380c5031560500f5095000b0f259003802019422a00c0e401d20040b80c1544030f0bc6401c1500401060580c045035246090840307500c05032007603540054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 913075890 1250 913074640 913074647
    0xf1512090323040806070f051207080f010b031317070f0f0218010617180a060609050112110d081308060604060e0631060b0d06080708070b030601 64
    0x1040001000e142810003414590310241e0081150b41d402600e1910301a801d0020055010f180f207020500c2d8050740000740c0283c810391b80b42090211506085040c514038003002c0710f9114040300c01d080010940c4c02000029402d01002d00d0042a8940c203061a5042140d540442da581c0184007038142004450103c09002d06217080311002ca4200c5a15070b400180c91910194540c220300e01039103d496003075a000202d07101c0b110a103048582e03644071031800041741810003114000052408040010091003511402c1c0c050200b144401e2203588005681820800d0349012100180c0014104c040558040c200041c0419643d40310f440c4229511440c0c01c40300c1c54410603520a41c042c01da461114a040029200c20015180b8001c04003142c0034040f960315445648452541110019031203941c440000d203c0d440300610342c00803080282a140d0485009000101c00c1d14610303808066403180c00070f840400d01c402885150051b041c074902804440346803080072a03880d600c034050040c400c1000404610315131302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 913077140 1250 913075890 913075907
    0x60d2003061c0212030408011a010e03061302190e060111010606090b030a0b0a032411030606030a0e12131d0408130317030106030c0c0c12050c180402190f15 69
    0x41401c212a031b580e0311407010f80e0203000b240104240c0b1120004c42e115003507010b5868000b2480014005041c3c43e03031944918600241a49000c0e80c200d8070079940702c02c1d01c800f0205c440000e06860400c0300054241507000403c1d4510359000102664501201400782c1c5522035820005c4410807007a59407203440c1d031202c490003419400340c6103a100c40204000010000030442030b840022286030b000319049250040ea80035544101d1900030a500204000307455440c20102454100f100e00388000740d01034100304281e103420340000440d10444000b01c2c41d54505284103007004040d00700c0750440764601c44408030400e85427001800040c604000030464068401c446109040255000200c10103003004803916000a40c7c02805480002800c00c220341404a00039402c0c81c2229a1001a030800140b4100b08822a500052011030b960b0181814400be00d0365881c4110304006da000c200140035082c6803041042d05802c809198055140864041296040c041d9040c0200c910421615001e40d81d00c1404844588 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 913078390 1250 913077140 913077169
    0x30c0409030906090e0f06060f12040303050a0b01020c0306040303091a01060f1d150a0201020403080708030f162307052a04060308190905060d2003061c02 68
    0x34a444210824503a1140d00e1800b250255125044019118044540c20003001c442c0704000310016408500e4a0402000402a0140c0b200105003000c0c2043e504060203001980c05600298580080c0504007220b8418900740003800d00040208041c5480420744a050050002e010304d07070b44034000d006006148032091400340f4144850401503856107006403140440743c00c2c010020300000c00000e0b2402c0c2914506003940001811950402c0c6101d07840c004a070b00c80004881107540a200020004403440c006d081c0f00c42c17048180b6034036441d1650103008280e000901e190390941000e03144100542d00801c800d48400302c40d0458000460358852600018421250024001d10445c88051907621702c2c121400e031082411019218242c403010108001d07250a4000601822002c104103054540b0300000c00881c4000b0381003220f8001c1d5103000182e000c0d0000c40c00d90120507100c4150360b141108921881d20041903030358100e800d500b400400304c0c690b061201c21100d074100100783e003c81956550800542e840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 913079640 1250 913078390 913078399
    0x10920070339140f0a2015030a0c1e03090c06050307210f0c050715151401140a02010c08090a030e01140909010303030b012303070e030c 60
    0x104040e00c0d000307080b0b60320709200c10549042d030615009000c1a0b07414150400c4100d0480e00b992202c1502c600d46104440000c2c089039104200903105039440a02200030464040c048001c4018040400c12844003c1c2c680c030984901001a4240412510241525004030b001b810000e105208480305890380c0e041511800b02404e0303d0080d1550240e40f5400c80c00c3c0c602d00c601b201034046962400141ea1900080d1450004250901020541c01c0210405494861001c20000c00c0c1440c90041c00011500044401c00024400168940611080e801d001e00021460030041142034007503c408076081d1610f0090860460125840c0c0b840c07688200e042c4034429084410050b51202e01060180c0284113500c001f00c0420f4040c800210004d5012440c80c80803501600c40c1c200f8a100040115841d00d00d1a9143c8400e5030280403101864607481070b442c1c003841c40780e04e000648440800006d84620140d0120844004201040c011400720301c000740c0f40c00c0081410140703082e40b06000001c1c01cac0b80703c07000b0440c2c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 913080890 1250 913079640 913079647
    0x603030403031b0c3b160309080a030c11030903100c05120f0603010e0c180403023f07051f090206030a050f06060a21020c2a01030b0306010920 63
    0x10203694540c100d00345200908040308400520791985c0c445107240f0011216040000c0000c0c20b100d403103043c42c80610342d407031400207590b020a90721003d00b504503103083d03c0000c0e0350700d10082100350040c40c89290140f05000850401e04001c0c0080d45d1040c25070b800300b03803094454803000d05c50703401001510904554290581c409140051404002080880b5040c0c800d41c20008403010107107012991310298000648a10780c103001c0c0c040c400d662424094000c50441c8218204038014003c81580d84580d190801141041101110421545803a980c110b00d07483c844d003046450000340c0001002da8501c2c00308044051080320504014004200140001c1c0d0030420010411000c51690790041d441410090f061203199240c0109000c1c40703015220b4201c000c514034a40c8841d0014030ba07108100840c414000c05031510a00100e000c3c01c00b000500c42c4010a030300c0365051010250a004c5260f4001e03000e280420819050300300003580c4410611400c80710903594403110102c5110628001b00324860341c0780d26503030f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 913082140 1250 913080890 913080899
    0xb18090901090b0c090114030402010905061606050f01180b0102070807080604051b0303040603090206070c060c03020c031b0f0d14062e061805040e0f10050603030403031b0c 76
    0x60520104100d03010f070052000548811490402e0304c00030401a55461401c80b0080040301c1c440e44007038003d906201b452080013525584110040807820524a50125011700901c0d2a5082d40c0b070103010f81a18421f2107005000c00984003a1444511080400102d000c030b0921006034107000454001ca40c040c0038481c0041080d00340000c0050180c0c0c0705208031943c2c1000207182c2c8904400380b004403075068004020400c20240f20b90000b0304400c0c00107002c2490100f0030782c1c3d1a0155044d903400304001c6003222036480c0c180b54052100d4240180c00f80c01030319041a5080d824084040389016a500c5610035034a84100c54969507124051a50f004405803607601e080300d00c41c0e540c0c03601211016183c00c41c5250320462841c00d426200203000d2500c018103c02403c00006888040300e004184151840c00080000c40756542e0140e00f80211154001c1d100b1107074035400040c2000794181c148641c4504180c140281618000210740883c0d03014034141c0700342d10101c040384124420150000c0c118000484d40441c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 913083390 1250 913082140 913082143
    0xc0102071104020a0c0f05010b0d0b010303021e030d0c050c070618090b150702010c0c03150e060402090402060c0f10060f050405040f1b0503030409090507050307030c0b180909 77
    0x1041e025003005020384414608120a0344101201c4400080381401c444000038688074600140078030a0002155040c42540070900d8106c20f4581501c0002030380b001002030540502c004800c00c110310400004004001c0d2900e139132072160114055540b60303102c1c1062141e6110350191161443d0702000d544100d035890000520a0019481c108034000c00800d0024031070707080d40f1030040c1e40c400150a20100b1110541c1802180c1c00040091b41444546280900069403c40c410006984109080c4208a2011392503904684001c9100c80c2d480d4000800d200159440001c8650300550484a10382d880c842406913608141035034550029602c90f01c04011800360302c603003060060b80c148009030034141c1c1c1c1c1c0e001004143c80007034501400c41d0000d00700000115680c0d054000b41c4002025012290a90340c20203e85180c0c442e6004070710040da96060030301001028071400d0004d01d021002420501d0440e1600c00303a9090a218040005800190f5030b89079980d915490317580d1810051903014a45070544106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 913084640 1250 913083390 913083397
    0x10e090c040b032d010e070e0604180f150324090807050f06240f0411040920030603120c0106091812030615050906090d08040f06020705010c0312060503030c0102 71
    0x80ca052050a2803032113010b40d0781141a0490310090400e010710385800d4070540f484040740e40c5e1035401400c10003002c00c001480d420280b1850350800000961401c0d035103440c0045845200a540c04840a2041040800e04100544031404d088460460034000078190348001848080341c02080d9103404640c030340c2440000318440b0701c46600c45050342c0e11580c2c0d0045a1000089100b0848640d00d210b80620b4030b98180703120500b6000101500000b52440c00440c1e4a42682003640f03d40000354a0b851622001d51800c0d03445407000b00b503802c080b41903060400c0000e03103031080c50003020701000000c6040b244220707094010350010306036035030100105071200c06000c0e04040700660580b1090fa05211070403000d4824403440c2e0845d6414250b00c0c80c0300010940849882e4084907000750300c81401e001c203103c0b41d0703550060018924411034400d5078662401920300b004404642c040740564010381010081640c00050f80f01099030b0500d0070044110f03c0c203041c0700007403840b500469014400852078852528055006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 913085890 1250 913084640 913084681
    0x60a0f08031312020a06270b09040e150105101b030c0524130c0315021905030601090306020c011503050d120b030a02010818060a02090a1202010e090c040b03 69
    0x100485952102d0b9001032019110b40000d41003041c00344c040100c18801e000e84241f0702c03059102000403280381800c00003031080c6900a480c04000c0020706a0312842c0511901070b03101382000161060f102198085105d002051280300d000b000070078001c289440c440d421030081500c0342081e546801c40241002004180c1500040b42c00d840741d01c14160803140710400740d00104090020782c1c102540c82aa201240350303442c00c421181e03010001008230008103013030b0021002c0f07440b5a0005031210a0040031826150700e075005d11041c40010010322000e82da100e40c02ca002e40e074101c0320250b0790b2004400002c0c01041c0520080915004e140408800c005020801809a2880d0fa440038800003007825000c04032120045102d5056000c80071742001540260080c030380c003804000843c140076003e040840d040c480100d6860b031200b503000590410078038049240c10302500007990800506405640047c3c10314028070160751090005400046114040702c088501030b104400c40e840e00c0b2b040c0040c2e05030162204111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 913087140 1250 913085890 913085917
    0x1a09131103040b3601020705031b06070c0308060f010e03011b2007052e1806050408210f070c030623040f050106050a06050a020f0c010c020405060a0f0803 68
    0x3ca09440d000d03419500b091030942c01303a0442d0340015020b0b50601842d01d006214155003e12882011840500203040c2003040d010b00c105003004040d0b07400d400d140d00103000d10144030340e024003000440c0d4400c42d1036921140c2990075800146003500141d902c2058903013415072641c00c00d04040000e5010030307000c0c104420326484072031a44040c0c50640c9a40b034141c0240d89007503848100100840d140000c511942e100c2080d02d20a0803801c1c41d80e2030130b600c03c812054200820074100090241c900c0481c4410700070500c915110341001e0170408116224286040c01984078145035110240c1400e42c0c50171107541da281c410100d0741d507158600c0d00020020b2284000d64401d4503110100150351048026041d90000340c00c0902a19541c581d0b07000110700c205903080d600c0c1e41d42c411021a154580ca1490400ba08036900c2e500e40311080a0f200030710780070101c106540303240c0107031143c442e403a600325403c844138941c100d50115203903840c00d000c900f0b00c0700903900c403039030340e010641000501820220081c04207020990 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 913088390 1250 913087140 913087163
    0xa0e0102010612200a03030206041e030c0f03141c150b0901081905010e0a0b0f011e030b030303040305071403180d0f0b04030801060f08011a0913110304 67
    0x40040e422500341d8030981c07a4644a190f0102c0000b08030211000c120300450506035410308007000070071480e14040d00100c0c0985e120105100074090302c15510b04440011321030246458109940c004c100c0008440700416410004001504042c0201c40c42030301d0f079403ca10004e0b1a0047c0901040000409140300700080d46000e4801410342202462041640d0824007000d10703020480004441100c0001c0240d80e04074005004070055000e0b90007201d0003800311800000da2070500e0b81100e4112580b2601891098402c1305840c0c1d4143d0f00b248901300348544910250322058007039442074024000c800700b00c1d90f05000003c200300404d03420001414825015151240f082045012003641c1c83c840c4038020690002088002d106628260365072a070100e2003800250707021200303551504101003069804038081ba00802c0103200c10740c3d220340c40f185821600c0c6400c950079494004100003042000440c41c1a1000000f40c40d841c6480c0c03140244540b81201e8420048111020103400e10f0340c0060318112208038045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 913089640 1250 913088390 913088417
    0xb0106090801150b0309160602062211040b030102091809060f010f090b0402093a0f060513020a0905040b0703050702100e0c06130801060801020c0d0809031e0a 70
    0x144a000e001e06060240d02c52468180341180080da00003c201010f03174465987c005d20605a071141c0c4400070001500280705a050405000c0220703140000d03000d04090842d91541c011480c0a07004017a4650141c500046107e080c80110740a813044200043c0c024030b100345549031680d00c07840224807440d1410251101070b2911030200c0c078001c40030f2107a2610704411500900001c41c0c19440081911002040107203000e0030180416420410051200c148404641c6075404622852011201030f2850005110500c812990740c11240600c51038040c128a940348000358940401c0a210742a03da00140701507409a074480640014000c100d804450303107406a8003041101d0700900506000e10000c3c1c02030300c986807040d100d4500615810100c0e51580c800c010b00200b01e40ca440008210740b18060000b4a29581400601829561036902c1080c03a68410406035243d90004101c080c00c03110249400c4c0c48079118164a285140079880b240c980c00100000c0100440148900a2201d07201949610200f031511 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 913090890 1250 913089640 913089643
    0x20423010305060102150a091502030a0c020304050a1406130b18030a0305121b0c10140f0115020f030d0212090c10051b0a030f080c0c0c0103020711030a0b01060908 72
    0xd030340f180e025031301400c9251100d2941c0c44681381e1020791800c2c0094064190340310324100031302c80c200f801e04140c0c1c000140540e20105005416400603640025031610f8134020200d581c1003580c4c410042604141e0070182d5003940c4107400c545019503221b01400da129128607003401320340d21803115042c0b80c3d20441d1040900342004901c11403016099102c3d00c1c109051515481c03280c4100820b401c00c03c145440c80c06100d450440c02500030b9814140081ca4600344507a502001c035800038503908822020903041142c0c4c55000102c140c1074400c2c810344183d0000401c0016032500900030400311650102280d036008240d195806889040c0c06014400f69a40303c800f01d171901c54407009009600f1265445603484920b0040c001014215a00d414030200402c000110310704040e0071800413400204105a000341c1c980d4803403140b0f90009190828146449600c10419685d0140c00e035165050540100b0b02c1000c1c058100e00040c00340c071014055504160300703441c240c01d0700d500901462002c61010740020410200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 913092140 1250 913090890 913090901
    0x170c010b190b0301031e0512131a22080303130b0f1603050603161503140c121b070f02010f03360f05062203051e0d0204230103 56
    0x42400c451030f59003103865561140c640d15003090f041000c801070050004004101c0c0c8040540f004807241d403180d00c0c00b0380000d9805141c0c1d01550100d1060f05a60a03011003070380c1115011401c0010340c7d0f0840f005011042c1038040030340e1140b81140800310030003440002c0c1c2c280c0003840c035100e09024079190340c1d801c8060100910550703010703400c24100c0d1034a420090083d03120641007200141152441b06906600c1c0180401035081003220440d5951658056074040c0144245010b405c200012240740521440804e40202501c0d60001d241341c801042c264441d0107007101c01e020705000081d64451043c2400200f4080d0000101c1c001024594134100980c400d11034020038142c4c2a10800f281c110010361807028030882d1034960017075048003044c40001980001003080b00743c49203025218918082035069550003218503980e110340712600c41100041d9004088501003100c4c40490045a900d1280044581c0100a0115146440014003107240500070a07143c01880840725170700810018103004609460 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 913093390 1250 913092140 913092149
    0x1d1909080909060a120305070b0a091e060b0409060209030610062c0d050d0306050901030803040b090c1905031e12030405150f0601020d08160c170c010b19 68
    0x160500c40c01c8103034604185126000701008285201c015141c1c2c50214503036150074000c4000c500300080d00001c01c03140010087d48419601420486038805d030712240f03000f88605a2480500707036021382c41c004010301ca9009004010f000390082143c5e051928144000b50700c0b070400716209110308000165054000038025041d6205590340c0a60303001603102e403000050003040300ea040007101c64000b0b4141d0700c0e1408001c1c86c0e40e000707a000f001d10042c0070f8005000c0741c036150041c0c0d008a2400740103001245046044075080b039801309003c0aa951414022130901c4040c0d80c1c0f00381d200c00c00c8507410606000700e5991000340c4804030240c60344521903a851009802d1541c0803602d081e045502ea92518050100145074014040c2c4c0544a841080b02d0f60080c110804840300f00070444100305004495904014210000d8800e0820807644d0620394441c2000c440001220340c1041100c040e42c40c10014003050709044038030280d0000e9240c201d0751441d030780609401d420f420f0140401605034074200782480703c40400c59 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 913094640 1250 913093390 913093403
    0x5220f05010c050c060f090a0b0301030317130b0a020a0e0303270604091e0509031c0c0c0204110a080702150106120b06070c0303020606010203090108130302071d1909 73
    0x95103800c0c0150755000d05818192481d00480040c0c44058454030004c00420604d40381c259615001081006800341c000d40200b0914803040c00184002908118000c4148080c06010350aa81c3d44418100c00c2100b03949000b04800301407010b001e032440054001d80b44c0d8640d9a05d5010500d07040106040c2d880c0074200903c44c5014112102240c0929040d481202e03500307015100c0c900d450b481c0c50308c020640e84400c001c40340c0d15020120111a01581d4491203400081080c003461030040d0381181884145043c42031003860940e030b910200b005600a01000e140298050301c00e0142d0441b00020100b10b8011040c1b6034042100c000006580b90720110b01c00700c620012308410703055a400c100c411101c0700c900c520000c2001d80d44080905c00c0795190340c0640b00e441d00c901d2940c0007490461a0080c02d08070081c004a043d94014811505580c0e00207507007641c042c003440403000030140c850404030b14107001c2d603025021301790400b002030310301d0b222440c0c6441c401c03804001e2401e802d81c44049404220340210401a209 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 913095890 1250 913094640 913094669
    0x303070204021e030403172214030d1d0c0108040f0308060301090606080c03010c031802130902040e070f061716020a1e020103050a1104120309090c0522 67
    0x5103415806020481408000312000100700d2400e4101e44d032007910142d010410441d1900360003001034084550140000b4104445200c0c03d0b15522010408000002d01181d0000d1010710314040030804e4520700c5806210910515030050f04034004035030403000f58481070007120003211403540900c66003400380342c3c44400e41600300ba071600e080300c890101078202985552142e0f003110101c1c41a008a02c050f2450001801c00001b1100402d42101c0300041120181401d1665041c440c02d810281c840301240c0544241c800c44c101003800700700511084900a41c400d1070070070351943c410800251002500ea14102260800e1341f244000c0d0741004000300000340441071400000c0c14a4144003242804440c1ca004450721014181e0311492103217000b402d4a400b842107042a001590ba06008113034100a880c44200100840210800c41c50311982c080c0d00c04000d07490140a0070540308400c944000c0c02d241004000010007070400620700d920902c0e403220341e0130003008000040c2004120b00b500b00c8454201c1f1190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 913097140 1250 913095890 913095893
    0x70b1b010b0121110406120507020f1c050f040f0608090a022d12010509010b011106070f0c061103061318140a06061509060f0f050708040302122a030307 67
    0x14004440c3c0d42070602d445040e851010078003000500003070112034554038129410140400104c4100909500031940725020079a000301e408910b0003082c1c881145412410155180c0c2944c842c80f0361000c40042181c00240020880b24200c48a0140d603041c1e40c4002803500c0f070381e5186680d0825154080d510440304107111001c0da696140302c101144101240c0039050700818001604002d104e0300301403141e5180c0c01000200c150a104090300c80109081890004000601d060341c0d50900405000601210040400401e800340081c09003140c3d2011090018490100e42103c1da60010394a090040e108035440110a1020b4000c042d40e021007003039500802c1c1e916494142c03180710401c00c0000c09001e00c29404002c500c2a0007000050605064910200c101c0b00c2c60003050103134154850300800c10300407414001164004404005c07140c0500e041c580302d01050401030180e00c5264402035111881510581c4c01d46808035580c0129540480072039a0010b100501000400d000740c102035154204014800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 913098390 1250 913097140 913097177
    0x117010f091d0d020c1c240213080a05010c030b060306090c0912061009091502090f04020409090c0b09061204060f090311060901180609020102010e070b1b010b01 71
    0x8803400c807214021003000285601e60f800c04684800030300050b00100c001680300d08020340380000081e0240a0b202c044081521850301d640d0000082c454008420b0000300c0f9490703100c1d016114501441584044a5559564010b40d00c1440c04c404454035400d01d640660b50500030b2090481200020700708502c3e5a0301c0c80200804100000c00a0158680a10030301c11a92100328a00c0050182c4000414003801d0244421901043d294016404c050030942c0c0d9000043e80380c044401d5502c4803500158581d0fa0345000a40d1030071007188950f40007031002c980001c000c0110342040440ba4041c1502c2030300b00c2c0d00c0d5541602103114081c500394001200b0006040d40d2101c044031681c0c0280902c02c0020030b800070f01c0c030a2003910703d002d2068001500401203141c0554041c804650804000d4001b0800391003509502410701d0030b0814050b00045e0f507000350b0025a4000e4010400e108008001e4a2000e034035082d00c1c800707a4001404e60000c0c8130300b81210700030541e0148203281445005850f075242c262002034014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 913099640 1250 913098390 913098401
    0xd05040915090e210304030507030c081210090b0a1a0912010515100309030206010302090406021b1b01030506090c070f1a0a0c0c0c030b31020117010f09 67
    0x4820700e460404001800100390f202d200c0001500700c000e00a50000321302d02c40d0642d94505030040d11464100203210000e80c004080b64056030b41801c000d0b018032498100403e00c3c0c01400000e2441a840a0070400300d40103a82501040e100454010004100c0309410300c5090b03c1603010f41e0705040748140309461060012000703401001e1005211135190f5010316500f070300307542050350707022202400e0090101305841c11441c0b1200424441c602001030420a490007541c42206220107401110044003040a12201d50111010f5500e11081c0d0300300c209490040c05d5480f9941405540060065072103000c85600c24080c090003108000e08015441e1107443d0514072035170003c40c2c2204d8015480e1185c10001c2c0c50301010401001c8450380c4102c551030141d85540607180d45009071001c1089482c051800280285071104c203481e040100c44580360744800c0181da01601d050742012610340e944c00c01e070704480c0825641400300e40c400c1c0d03545028601004551001090300380100e0318840d02828041c4045030705030b0f104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 913100890 1250 913099640 913099661
    0xc05120a0b151903050307021017010902071713060e04020c030d05070309121701050a03021c050c1203190504060c0f110405070809011406010f2019140d050409 70
    0x141004051040c0c9110750102c0f082c4d000701c40350703000414940c0561516048440c5600c4c0681050700c100c4a0350011201c4044c01400740245030356000c54514184140d4100c0c40300020040f443c82503a030380d50001d031520207202c02c0c4140000034481e90041c1125043c0b50094400d071544035801142407100c01c00000020b050010f018004065584004601048120026405021940c1c80c0c140050081d40c0d03684003a11016080640035a0b11480108016200d80c0211301010f0801c200c80400b07500186401c505100220344120b40c04003000c1200d281c0b00601200511030401200b00c0e62118518405003034070766010780d00c140c101040a40180c0340116074109c035a0410b17544540f0040045200090025044481c26104000002c0e030704020020106001d10800341c50644001000200d03207000c1c0c00080c11507000a00e503808012b1030580800c0e5002c00c4007101c2d4040d008010542d41640d1407588105019001c0080a4401d954008240f50071b101022501074001d0340c1e29980c0b1494a805c0080610190800101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 913102140 1250 913100890 913100899
    0x5121b060c180d021311121e011223010f150305070501050a0314161805131d07031b2403090515070518090c03010e1801090c05120a0b15 60
    0x1c2c1c005c0140701e42c85100e444000d030103034168030360030383c1c1101800b501c0c4001c0c40e42c29018150700000e81d42840324019181141d4040e5038501000c003051501241c405880c0400c5801020300941c058020392040d0003000c02500e01500c2041400f40d807901c2d05d6141e0300984005080d0b6040180103100d29482040101801c4074203050205250801135040d0600c440121003a4000c55580340080800d00e0340880480d0100c0e2007a2242c40c40c080c00c0c180000e100c1008080301c43c501c1c55480c1c401c402c11070344552042034580746102c00d840c2101d03030fa41071480009182400f0358420503404000884c842c40c17100c0c0d00208144c82044100c0700840640f00c15402080381640951703052140d4500a102c5482101351144201c2284e552503032906054032000e007404000d4442a0b205940c01c05c00c019010010b8015a411111000c0f400b054a880c0d00010241e41c068140b01c0d1203803075003030107407600511013901039420031144c0580700210302c81601160952150b2024000424031444017021914004580c80d280360007220080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 913103390 1250 913102140 913102159
    0x602030c0f040f050f0103021314121603020f0a12150212070215090106050108061c0c230a0303081503010615080a0f02071e05121b060c180d02 63
    0x101d041005800c00ea01080c2920350000702485603040c1880e070b1011400b000c0c20b055050002241c148650a0f865000715102100001030405a543d0b0b000c10080f84181c0700c0040c0d404804a802c000340303201700c1d20301080c1d0044100c10740003201424003010f044120381001819800200e8950360380c0c00d0785004038401c0b0140f581c080c0701f0165101780085140d402045a500142400d0914007240181000c0081c601040f41e454481c04000c1c0b43d81001e9015803103d400c655003003100882e07286028250881e040090044401c2640100b40580580285810b4115418098103429042020003400320803038000200000d0204000c64039000300b106d00310000b410010000b140850302c846051070003201202c440310000b80000d0502038000c020b031280030552015068150300e0724240d0b8644040300000fa58006001e42044203130041481000c2c00703c40c42d0901601035103a03480c007540703d5200c40030585043d00b003818040d0201245040d8050303012078000100c1f69022a000e245020100a0190541c21081e41c0058445 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 913104640 1250 913103390 913103407
    0x120d080403032003040302010c08060d1b03050f0a03031a1302281805100f0507050f191e02010905061b1501061e021e0a05010f0e010b0a0509040602030c 67
    0x1a046501e40418424004d80740c0c600750a0003425611110802070034040742c0c2d0f00340902d5454199601e8240b03074000754154000da107248081050202d4580c400b4003030303000350b071650000b04030041a138540090080d5001c0c03049981c501a112603110014146542c004028030f0103100e031040c19000342c20303940804403109a0b05551188a0300e090500794802d40c00080c0e090f1150440e0001414003480038200070313560800e010741000f50242031510380c260aa810b10501061460400c4000c00c450b5252081c000309945030000106a00c20849100080840c0c2181c4030441e8180d00a4801ca4a2203c43e50140c0d1464034040c84c00091101903881310003c00c02c440340c04071203010451000c00c01c41905400708081d804140d8074000009103c00c02c8a42040ca0510740c6d200c0c1045940e030f000498801c1420f00d40e0341d07041140c0074400150300d0720300c80b210024815402d2000d921040d075041d90001c0c103400c4050000380300000324441003014505442c0110303544640c10401140209103158042c56226140c1c01c0c0d003038584500e5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 913105890 1250 913104640 913104671
    0xe0d11030418180c0f0f0b04050105031008070b0702040f020a120c180b07050f0d0f180305060f16020c0d1b0b0316120b090a0c020c06040e0f0105120d08040303 70
    0x1d0441510103049504c0e0030000010b00c60841c0c0001c000c1e10104004e03190400005135a035200e0742c400e6604028000c00452250089029a880284401d404954100340d4501780441c3ca40c00426050b4883c52a20034490800e958a000300e031024070300c50745d5451403108402d554400800d00074280d0000c12100240f441d0031000c503c02e006010380052417000d070711284c40c1d140c42443c1c100d40d0301244081e900002c0d80c43d440160013007001180a041e60520505d00b5a04000b02c01124500341d1001c0e02505c520707010b000130f03030191407042c40c06102c2c0100074802d1101c050f4001e9941c0c10100d52040e4014040000034000308103c3c0d03030500c2418001c0410948010f0f44c49030640580c3e0000d45540904c942a21040d640303107600207805181d81808101d080c80031020070300005201040c010035181e1203e403508000700c2220b00c244006a000c4400030401d42d142c5171103440c1e00f030340c9071011583c2c101d80540490011078646415000030301400356100040000c100340604c00c071480840581304a060644928598410701760 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 913107140 1250 913105890 913105931
    0x1b02041b020a3c06231b040b030a0504080f0a0c0201020c010807120203091e070e0f220512030c070611131a1921090809210106090e0d11030418 63
    0x181d4111405c1c0030304002500d4820300030303059044034002604120811030203811905407903010588000c0080d1075aa14104074030700c3e1240e80700c400000c1400041080308181c0102070300c4003850007a800c880301d5102040040d12030750700070f86a40780894081c901480216425400a40e40032408005480c5035014501040c1c10200d0181c85104107508051828800d64010182d02e5a109a01d180288820304000450303040145115800101c3c04141203050300c18024104494641101c8003100d146c5d403071a00d0313500402a0b800440d400c03039200341400700e0400914400015602954502c0001144031407820000317600600b9a25043c1100d008144080002c40ca25450f9052400c90103448000001c448092620b00408600b54904445845d00c0316050110741581c0986051810517220380301e0300920b1440d2001c0c008080740383c1035010f60030715002190b0012550001305c1c850158204031450940301c088150344100d1842c80307040e0550b10921042040b022806210014a0008480022092651115400c4482 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 913108390 1250 913107140 913107191
    0x6030c070c0504111b010501270b1908161d040c080304060315061b110109121103011803020c15040308070c061b031b02041b020a3c06 59
    0x140049000b885c42004500000300c84c41421000b00415814815003070916034580310300b90b0050210b001180310500143d030101a40040045ca010900425002d0451201d0f07400e0003142190301031704a11161606900103d842912131410812001101d06110703c5144440103000340c1c2d1061052000183d0300b41d0600051000e0042541d0109024690f070a6580307940d4241d6000300100040400582c20300e4201c003002d14000d40c1d0015590324007400380070049800c0387d0300c1c2e007198200da0020b680300400c003c401c10380341500c584c00ba0028041008030381400d03405144403200203005600101c5500351546041810394000308105082c0c00d007016141d440d41403858010003001c496826101c030307041c0461a04210700c0185001c1c030206100c568040b03543c00819074440c50340c515551881020b505800c65031140c00182c41c402402410030034001e83c2d03220003550368802c00b40c185d80d21103007400031080740c8405041c1d089515075284000301401641c2e0740b40c0c2c01683e0303c0c1d050075540607503501d10800e078410603110510801e1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 913109640 1250 913108390 913108421
    0xf020307120b042306060d030201020405120c040e030403031b051908030709080d02030421050d1e08011d040f0b160912050607050d18080409050a090206030c070c0504 73
    0x2440c0034078124080c10204a40c0c2d0054445100a550314036134002011a880303003040d1900c8411002514003079029001710b40102d0703031190908a01d00101a00007a022051040840b001c1c0f1511700304807249520b074495030001600041c0d20728000c8403c01c3d0041101c0c1c034400d20030421218005100c80c00c0480203111080c040f10301010000c188001c09034804055409071a001000d0404040c9542010b592803107140705001b401d06101445c810307280c40c5100302036491604002959540545944010400c0303c1100041d032541030301154903c01a8410007140381610f488546032072a6507030118100705c101c80c004104035000015203000c5800a40d5860441c0e00452440000c1c040340044400c0141200495030440d0400c29200c003411404540e0002c0d0050300881c00c0d00b403040e40d503aa4148500c4c040c00326000a006c203507045404a40401907654020004c85241b0300e000c00c042d0b118503c14106980382e501d00a03621480a002007840250604014550280309080460741c1d03070303902c0000c02c003500c540c02c0700c95005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 913110890 1250 913109640 913109663
    0xa110f06070c120207260c1203030f0c04180f090606031b0905040b01140a0906150305090f0d050d02040e04150c0f0f211b02101104030f02030712 64
    0x1007000070103c0000003082da00141c40e800e4100801d04258140313450b42c0203d0010340001c100c401c003209004c0360042100190890030f001d45035800d1207a50b940f09452801d01544010000b030342c5c4032001016141035030303c44249481243d040c00f0042c405040a05c0040c501c603581d0f000c82a0010b0b180e4450b0a0086109a040c1040d0f01c14040d038004503140075902c40c1a0090620b000c0100207006807603a0350640e440c50b00c03c0500e0b500948085400340c1000d0b00b280301070078900315012518180003501c146512440d075400b031020382e44d204c0485440321065442c1045580c00a05c40c40d51150042c0d02411254400d00d0b03005050030356030b00240c440b0f0740d4295015252800549000071000340f0600411710f00855a08151581400000004200c0801010380c0710811030189010760301e4109528200b0800c241c240340510850380e48100c82c42685020081c1c8c0e0002d840b400c1c2c000c000c1500b03070340903400d01002c03d0b0030070030b050034515100d0000300d03040850202d0345405081c9000c540c1c42051000d00100314051424540e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 913112140 1250 913110890 913110893
    0x9010902100f0504050d060207140313050a08152d04020415030b07030f02121611121b0f0d18050f060f0706141504060b0a050a110f06070c 61
    0x2180c100124a10704110300c0e450514801c0c1d410004490849000f40d400c10000c8070301d4100300009000e00c180040c0340c4001440203409074175000000d080304d00032000c030a015460f0707280304000380d403040381c89118010340004140c06010704c0f811081582c00380b1200e000307082410b1040003061204069102000e21b40c2c44110500c402d50400d807250031180c0b80400c0e00d00c1201801c40d21080130000c0018081401c05885170641031032211540c05541d40c1802c0182c8074115800c00203495008003950b074202900040041c00008500e410001c1c01c034402d40c061020301450001410120748a50341c000882d0441d51085c240500d491110801100e018044180e0301c0300e54100ca0061b4009000201c0d81c44540300d510104e4100c05207503900cc00721401c8040c40e6609581d600654685140138012021168035940d44807002c11500d0103800a1100c0c0e9100212400c001440d1a030b280e11740a40510340d116400110180000700c159405110480200900c0d103085400c8040c161401a02d024001c60b042c1d00003943c440502d10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 913113390 1250 913112140 913112149
    0x61d13290a09020a0b070303090602030103060209030d1e110f0d091509030507060807031812120207052d030a12110306030c130204090623030607080613020f0309010902 74
    0xa801c81840601400004000d800107042031400b80503640e100340e03000658000f018080e5020809c00c0e0340c0164103544960356030400000940010424a00a024a4030340e050880d10a549204101c40e14003c103a8080c3e40c0107000b20340400900003a007000b031181002503140014100000d008241c0a50748003484141840313180c88440300c0d40207882046c030a020006000060001c10b03598151222890311540d00e550b81101100a40f44031085e5407890140c808021007407168100f000c110484803500e8075040780c0d10000c21503040344a1848050400d41123421403c0b6200714502410b80b8955000c1120180403000000a60440d8000100178001c900f2a5074001131410380342c000c0c2924030240d01a050304515144011903102c0d49840b0700e0902c10081881e0313012084540c0d9068802402c0201d408122540c0c03107200150055000b090244c4000c4c1042c03080080924001078240d11070381d000d5582c1c1c1c5094940106205071070310803041301101070382c013400b00d031403583c101801551095640100100d02d00c9028014071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 913114640 1250 913113390 913113473
    0x9060d140a1b020a12030605060a0c061a0d0f0203030c250509010303120c05190c0c0b0c030a0f0507211706010507022403190609061d13 60
    0x21820000c2e641141d866008140320704000d4125000c040c105406460031001000b06400555203c5000b24848070442d6104804048040c85080c013044080031342544414005030140720542d0101c40026104001140c214044035010300c0a03003101d05081c503a4801030b003030403030115842c058a020140c28014098002e40303045e00826042d2104601c550554600a003030351005015000c03071a0301e90314100d4005100d03001703e650003003c061417040300c1c1e0341d0510010311030700802c002030350701102440d000318808244800310f461a070b200c84000e40c64084201400ea071000381c80410182400428802c00f40850341104010704103100010b65490266170880d4064a0207000c049400f480c144040100804c6903001000c0300c0401e501152450303030b00c060307444100080170108441203202c1705020060000c01e01d036001920890703d41140d01030101c1c42e03c2c1c000034000c956041c4220680044800d0011904201d500182500810b81d03540440c2c81c07440548a20b4070955000744081d507001e01310355020140100f103c015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 913115890 1250 913114640 913114661
    0x2811150c1b010c060506030a05030310060e040b030706120f15060807020726010204090c0c021806060406051b0a1b0618030b340905030312010b09060d140a 68
    0x203000c01074005030008140c40b2240c08020140e950f2030020400c03607541080b44440c1254070a04076540c1e49021600c0c0045035050b442a840880c03408120315500d460039000d4100f00010180040c200d6a26000302180c0201250103241942c1c0c0da50246412910024000c07480500f003500484842c85140490042084c1130042011045410090f01170007111851a01c07044120501c00c2080e150049110f0b0650080c0b180390f105966251811590842140c0c00480c005101c038002c640720400f021080a01001e005c0080b20010382c00340013084144a5240240050440c82131785104010034a04d00051442c07070302c0b05051013590701c6010100c001d100030340c110080300007030b0207189082d00036071000143c40200c0c07444a000c020250402a40081c400356020420320b0440c408112203501c2c900c40060408510110018052b000551388130804a1141000021a03650039035058000b0902d80c6041d01001c021303041403021a502a80420060b00d100700107004006112490218517055400d1101c00e6000b00c8440b600d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 913117140 1250 913115890 913115923
    0x602270f101422030302250510030902060c0a150905070b0a0201090b0c0901080a05280e12030a0e010c1403040c0b031f05032811150c 59
    0x2a01140c407100181c0040e001142044558500a40e41e488001d025040c441001106405014820014200003035070441e4001d4090329406048030090600102c1d0701c280442c0e50f05e0400c541000503041006214400b014149000100480160300203130f141c0e40b000840b9601750f030148501c4030502190445102002c505031305c0c00c000100f16541c4194607002d0301c0c883c61801c640c1c0411a07100081c000e4110a001070380c000710101162801e44c40d15000c5800c03080c03249002500c2c100008030010b00512a0b2030140c070b4100e00b104c03621240300c2907030020300e494161024170321074982c00c61402c2c2203030402c198140381400d082000c3e1a8502550800708030b509800c0185910380c10f000100c0c03001c40c0c0040c007900303040442952341603980e0f8541c10281d580781d90650004462840010404c41400c200210581c2d005007040c40008220b40d40b1001c141e61069054410881e82d2071050801d42d402c002000d146846611803404d03108403c1d44d85000440c0301544d5206080d42c0034000940c4e0400003410b0040310584401c052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 913118390 1250 913117140 913117159
    0x50a030614010b131a120f040501110a1409180907060e06031e1503060a020901030f1e09170c0a020306010b120a180b0c09041815110403060227 63
    0x200042540007151245040d0011301e280203405045c1410f084032020404181c00c1ca0103802d150101450180040364151603075482c1400021b035842502e0704850940f0181d90305e00349281100b200c002140d034001c02400307921000601d041c10f842100b0001c0a441011210301606099103403050145c041a000b560701032041000300b007005240c1c9a903040f0071175542441d0f0300381c14031540e8140c075101c0d0390501e52000c01c0c2c1c17502c1658100300300301c1c1d283d800808884000303980a100b42d07420107034210b00b540c802c50700b10111811b100d132611440e40c00315800304501c20300590100d900c01c40058100301040d445601c075820700382c110801400035401c00300806030051100070419071070920880c8004002000103048400e03003507126080300c0c2039141000c42002400d50484140e10090820b21040340700c0d5444240c801d40918200b842078166901540c00c41201150081e2414030f1580002c3c0c81d4400501c62308c0c0070000395072010b200201c0400c4c56840640018280030200180f070141c01e5074500042d084109115203d4580c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 913119640 1250 913118390 913118407
    0x140301020f0415201e0a0f030302130f0b041a0a0c020d170a1101110a0c020f01020a050d0504090b0f0607020409060b0409080d050609060a1401020304050a030614010b 73
    0x204121030445111140c40f011031804800c0c11030f00380060b8480070420144044955400000c08202071424110101701c14900e48034004440351a10580100900603c1182d0510000301e4040e40040000000098040308213035224032118241080d690008102524003040600044800000400040c1b0621100e603051101d41c0d140180040d0512030024081c0030100030140030481f141c44533801c240c06400e0304986800c030302c0b040100b44107903a03c2e00148560a02d407000101c04a1a804c846001030b003940c4042c83c12080c0c1e028058110362000ca900e04506c00c086101c00424014408012401c003207545407940d580c42c0c070f1480c0e01926040810548101548585070b200707035440c002190301b03981c1c0c140c030b0214500c00541040d40007820310704072060700726003031450020030403030404010428410347c01810001e50b00e9080900007103100c02c40d0038075000901d4180c18010104484000c0c1d54580e0148100c0346810749450100e101c04c016640111011500d411200341e9840d00c1e8001640075190890300c2e54144081c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 913120890 1250 913119640 913119667
    0x42a0915050a0611030d050c1324030e0a0f0803090c030601050d03110c09070203130914190917040e160f05160c0305030c070614070b0a2414030102 65
    0x1140703d104203000342c60701c01580500b018019524071034001e6404104510780180c540301c00f03034014020b0000c9174403070200100d10070001d102951940000c095458610040c600c109a0003410809805040c511a55036080d002902c1103001c802414410320790340b80c990a043c09114a842400c0d1040c41c400e82090380103015589840244105040d05481c2c14072003401012045418400c054941c140c001c1d00100c10450590b400000918030300099a001c05a0150740d90484821601c00b540c1d807050703075400980811b04610b60300341d0720030a8100003140004c00440315510741e0341046503091a000500070206041001c100d01107400c550008110315510141014010000c2845402c4820102030080125a0b0381c9102029180d1968603680b0801240546449046c069036031340044070080c80501c80c0c4a4003280241c80341504444609005892138101415941ca40c41032117001002411640d0b902c0100d402241050f4180013085440701c002c19160b241040c04040104400154450003a8010401b0ba05002031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 913122140 1250 913120890 913120909
    0x30c090b010f030209190e240a0504020714010c1707020d020a03120605030709050f06030a0507150c1505071d011d011107060e0a061403040605042a091505 68
    0x141890f005a584800c030002645043d150400c0c60402100400049901030a000026010f03040101d00640446001d00011100a81d00c10940b900001031900030091410a500640543c84c452105030f0303141c5041c10300c82400c50f0200700300c190004080d150034a24401c4411070f1186c1000c00c0d84090100f801c4014006035441c40105d900904106a94105540c1c1001036849400500802419102c0c0035a60b40041406400107076499a07241c4c0d04070300031034140c2c0b0300051040d485a6003d4068007190b89000c6403441072241441c051814018406a00b200040340c80d803081d110034204003400100da00f44504011304a050800d10704c080f41d0310410302209a6a004220350380c0b040e041d0521011901e4039480121018045c0e40503034a40f80c0709500000c1501504407528282808007514102e586550301d21048500c064071030003004020f4410800300c0e000c60b4a60704690f071b000c1d00454440c08501c0c00c4d0303030105d084051852905500660b0524041c090600d00c1c2c02595100d840000400500c0c82c05c0c00c1c0080c09054 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 913123390 1250 913122140 913122167
    0x30a020d18030816230a060b030d0f030e010b040e0d2c12010f020304080406030507050f0403231608060604020c06010608130501090f0308070212030703090c03050109030504030c090b01 81
    0x100340d0103140d0200306039050004d00d101c0000f4014038052070380b141046d94441c01100304650090404007038801b541000612050590341c565a280313001c00100c1000d9000706420340000c3c02d135540703515801d00c0d0b5032181c3c00b65904c603c8010004101080071008014181840e0050948880e014486100c2e50506210945590500111034524400c060000d0990041407040c1c81d0410031030010042005000d02c11010b401184c4031902c2c04e20190b40e90382400c441e0303407091101c40484200c0038882480840c2090303000c4100903011401040903030302e0350303503015241810121700e0036000da2540340c0c00c0c8802c000c103001090f000b282c107907015410212400036503911000b0500500c410130890000103148618018680a880e64100008010302040d9040151b00300205810680110300003501054040f071002171002001c1141303500d0305046882e0030344101c0c0a032122034420740da01c0a0003400400850020701c1045c860360310944807199500d186252018005259a00c1800304614160003500240d03008900c848421 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 913124640 1250 913123390 913123417
    0x11706010e011a04120b041406040b0f060f190609090b060d0b0d14010209090106020a050a03080c0d0e062a0909060411031905090a230708030a020d180308 68
    0x15800e03c0700c1e46450340913a510600e84400c00c18191014048010b00c03560140c3c0c042c20840c3c0a06036091700713044d5100e409440080980c1c43c2d40c1e00041418480c003129540004000340301130b01c810021000104148840c0b10000c1030522046810003c1c990050044001805800c80a21401c2420000588640149116100380544413040c054081e9119000300c41c3c0c0550040c1004103400d40d00c81414001d4203c856014016201a00049442400060a8100355a002d4002d0030300c2901c1c0d940840ea1010090541c24204c80180004e034200c4070140504410601414024807040c9440c0c0482d6001000312068200050a640380052a54045900300d03200458261444015030300c0b410013240042c00912108540b140001c028000d0100a48900e0789098a44032010302150b02c80d42c2c186912101088401061403814003181d42d030600c5000d1402420300c01250941da04159202d541c5070541e4042031030080182c10507444070158640015002242c0c0c0400c10015801c5400d565400c80c06225844009541 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 913125890 1250 913124640 913124669
    0x513050606130b0307060c020310052a090315100519060f050409061203180b04260d1107080303040b0c0306040902060c0a06060506031608180114011706010e01 70
    0x91082c15080b20501c1c8401a00311000e69a50324402080c40c0b240c0d06080384240200f58102000c03030300317070b02070303a4004d00740c55468a85c03e00366844449000482078501d00c00d840010710682c42d1f141d806211f00714140101000025480c640741d03c0c064481c4040d80c004a1003161401054180801c1400075002170301e1507801e04508998900348141d590f40107503403000d4006410810042016100c070701110078264172036281c1000c0c400c0742c14502012070310356015400130301c041404100568070011480f4000c80c800c0d0701c1401d01425680074a02c0c1030004641060000c034800701c8040072020740412082d401801c600001d1070540c101951f922003806409040d2b403890712804030100701103036100e40c070000019500400c5a0740d500b400f0170039152600d04000091300c02604e8040c0020365400e005c01241d03c40c5900102005000349001ca040c0c44080d005840c90007104101c000150301c07a07a0900c203020701c0d1030480c00c0c40309030342d03141c11000c1281d0b0f1004048003005070080401000809040048141074035a4041070466 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 913127140 1250 913125890 913125919
    0xd0f0801090c1107090b190e060922032c030c0607060906060e100602030f161103070e01060914031203102111040e070b0a11070b0705160f061d0405070201050a0513050606 75
    0x1d90305034010821003aa04e6600000d04240d002842030780b00302c040c0600b03031001114000b0000c0034580c22000c293b4154009401c12030301e5240450051000c075200f60380c0001d4410542c0c541002300c7d0183e400c0710704421101030900000c007400140580003040b5074401986000320313032128140c0f940140301d0810320321005282602c04214032000e04201c441809000c46504560310b09072001c04203401c0c8940303408141c911002003540ea010201140d03d424014000301007241003811074401070b41c802014110050000c010101e2034115000c94501c0780701c00d588590b01c40307840c0c1d0b00300b1900310640c1703100045c0303d113181c018040c06c0250082040c02c11151a0032400707440300d48040041d2030315040d07080070101c50b008a20003c20036103079070005404003030300550854544038440000e51164000d07030300908000c00341d540d1007000003911403410700c6e644505d003a8902d1005040c00c80030800350ba2040d030388940940d450708200100300000f4482c0c142c3c0003103c9007051000c4000f07903e855403540742c09000503020300c020004442 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 913128390 1250 913127140 913127161
    0x1906050408071b03020a1a192105060102010c08040f0b09030d0e0f06090115210b07080f0610050d09060605120303090d0f0801090c1107090b190e0609 66
    0x2042d05070070850402c00d407800c0310086031020400d40400c03840341e40046e401250340d400c915510a0255910803220340f400303d403081540500360030b0054440400032003600e4081c03103442c0f00b1130000e02d034004000e010449040500019080d1407921419404011880040001003100008840c44047c5c11408901a644422441c182503100e00d40c02030003858201703c07983c40000c40000d06401091000010744400b0b481b406015801e0361190741c80c110b40401b0f90541440314a50b1068010501e030b501d4400c1c2401801d0340e1b80d9641c0701e66001c07544071000c50720010800c82090711011003264002c0c802c46000255074558240602036001c0e080c48030300310b107a80c0c04003402080307059407006001d01001027049000d1000041e2041e43d9600803260303000346001e40c0740b403030f00340b81d000c1e261074441e5610944403240303203070b0030310911a009024400421017080b040c480b5100400f103040c00b83d07034040d09090401003034011080c0288003010018000c00040b82160400403c0400d40850720290070020480d455647c0d138680c5890b62 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 913129496 1106 913128390 913128397
    0xe070f081c11070e04060e160608010b0f0403150b0337052d0c0d1109041401020a02010b0a1205070603020a170405010c111906050408 59
    0x500e40070b010360300c14690424400d0494a2060b0f641003500d481c4181500c0c02c3c0d41b400e55504a0710a900c90a0150000344050804c0000d1260301e0300700020f010f1501440b038500a010003040740800e02900d402110700454000c0341464440c8000c980040c020195100503034072a2154400800743c28041c5141e41405018848003240304442c0c0d91903040d180d086402c0101d4442c0a08201c0750703064a41020130304010410724001c0c1d28510703001130304185040d80a946441c07181404500300350000f003004250071141c007016a11006c40e501d451a148840100c140c0e1182c0b0294008596076100540c1540940d000b120102ca030183da00380da501401540300c003051000352468000203030912040303009030001c01d420025841c1c0344c0b83d0841e4001c4480301901040d10100d98a0351100c0c05a0022a402000100b46001c00750103041090085642c801e202c01c06108d0082c5250344941c00038081c49081000d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 912949640 913129496 := by
  have h0 := BRFrame.cov_init 912949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 912949640 ≤ n) (h2 : n < 913129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
