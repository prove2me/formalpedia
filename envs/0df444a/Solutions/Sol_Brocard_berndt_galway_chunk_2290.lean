-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2290
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:15:20.891813+00:00
-- url     : https://prove2.me/submissions/383cb230-747f-4cd0-8bdd-c7e498322a59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 411690647 ≤ n < 411870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 411691897 1250 411690647 411690659
    0x6050d02100c1205040f0b0408100c23031801060501120908070c140103110a020714150a1101150b040e1503031314041a010c060f0f0e0c031204 63
    0x78807010801a410800b00d60800c8010600031003441100c400b1030b9480d1981c403480d01e0324404100940e41c0200780c9032607081008001036900007a801c4945400d10f14001114030083c04281c40303602807000c1082c600c104040e1105d001c0740f140c0d0045e620408402c2800c2c0100c1081103101e03070880e05540100c60100f9903001100f50b0030440d6900202c585c600c00c0c0d080ba4503090300c9460b4405d501391564406504011044500c141e0755034180114058107001c0510030b821b1104401c0040c0d00d50341240504038180a400404580c1d607038820340e20441c0d1f01040b102c9c01d41e640c10b00020088c80916414800d030344540c2000880820000000804006c445020740001e0609060003a003d07030107140501000d04214602d00c512681c2d503010f000030004001c210001c0c0c2e445900d007600f80701400c0c17810035010344143e19102c08204003514030549081d001a0034648910700c484203203000c200038500c1103801c100f020b00d07154440d03500c1e6070598072845d100d001c64000c81d00c0c00194401010342c0d9108101402100c00c405020400c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 411693147 1250 411691897 411691909
    0x1f1a18070804080d0f0b01031404080306041a060711010f090e01030b072102032e030204020a0c05030706060302090f15010e010912062012070c0c03120804051006050d02 74
    0xd4072070041646003041c0c13643d4030f400f03850080500034901070783c1c0e004075511036800d4440e03040b10300070f07211290700b1a250944403074010340001040c01d4025600e4081410b40c11611104415819000030726460b11003e241c1070040a940685034480e02084414400f000700a004100710f1080314218541a05581c2c219a16049001c0b00074090030b0600030400c10030400d950f5122203111820080d01c40050311781c90641e48001800c9001d400751221100e2890b070fa0308a00041000071030583c0d4042d680540e0f038080641d4101c0f019140d1000251940c00040342c0d4070100111a0003443c2101d000700c03991225a1580018080403103815038001101c40800d03003000706503501488400d07104240504214403020341d030701c40d5452502164002201c040344c0e10114802800c03034001140120304c0c1d0309110581803030305e11616949040c1c0040c1100c0180b022604010003046080940040550340c0034074a540ea1007902c820141010d4030a403403c84e101c1c085c40004444130540c51007440d080700c0d0000c18405102620b40c082c804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 411694397 1250 411693147 411693151
    0x10f060c08190c05061f05061e090319050607030507080609041103211309020903030d1515020a140316022413140402040e0402040e1f1a180708 63
    0x28040b4000002010510070301940e0300c07496410400300100e10300b030f1505206c0c0c2851500028400e440c240614804581d54024000d08505480705175641c4249130000030f444e000e00c405131411110310210b064400c1203008160349002d01c1058906008586500c80c003510304400440300b0b0b50f00070303900000180100d00c114442540c05a0082c0a84a030a0208002d0b009404e994960002122000103000e00c2c481c20189404001000c0344401141002103500001e0b4a920070421800c607120b803500b0b84040d2000313000350701c0d00080a10907401d4dd08080714050282d00c6039180c0300290380300c4030305030380c2c07200501e030080111012402c1c266080c0c000005a58200840c0040ba002d10401696209081003074101d803200c001c09203241040c00c076040721485c0c1140c8280c1c540e15241d800c0d01590052204016844002100b075030800e43c1101c0c08070707005400784825860030f0040f061010b20504c08480b071402c84a2030b540403410091f480316050a06c04552001e11042d01d82e082182c1c2c801002da200095a414404e116081d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 411695647 1250 411694397 411694447
    0xf06030203130b0a060b1b0f12030f0c19030b03010b01030504050d0f1b0311070602011b0c0f1709040b030601030503040b0c10110316080f0a0c090e0f010f060c08 71
    0x1a2030f5203401074030802e40c010406007502e03804d0308031511f40d40d103000b005201e4000140100030240300000c00e4a0184600001e09111a03006504001c52480c011400580b2850140401051880b4100840040241c01522205402540b0389203000c1c0e0305500c64000c051060346c20800508461403400700454140d02460010010001003502c0040400508001e8041070740c001da40b230135175221902c01242e04050903680000d09581c5000b518440c1c0c20300b500c405440f003110703d00340101010484c0c108500c0a01660030010481844c07448000c500d00f00e210b014040740700d02039800b0032181d122007040c15500c01e000c0c04040c14560052004121b4a020b0034020302c80e1900038020381e040950081d0513682070302e40329002c43d0403050f800300800c502c1e0350308161080c00c15040f43ca48400307d410442805001d5400191400b0f103420340b64a8040c441c18003030380c4514001c6c0b00d658500c2003d85007000081e00080020f0140c40c0307860607070020024155119190a000a9400c14501458a02c4000082c1ba44000c140303151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 411696897 1250 411695647 411695651
    0x21e0601063f0f14010e06030d0807180909203703020a0303030b011407031e02120408010e0708070e01120204060b040303050d240e1905040c0f06030203130b0a 70
    0xc0c1070f400e0703a5005004038580044c110603103d504000401d000500c0c001e0080740654840e10003001c0c4250f22a01881d005071050510f20b225000b400c4c29840c071781145170012a0078500f0402150104024031020105c0178080007021801c140e849420410b08078000720042c01e1780707800710211141c89000403c42511040000d08a00d480c070307550340e012a4010049038010b8011036a0b0350f80ca2002541c010238540c40d2000074020162a003400e80e500900807040e41c21800c0d10300020f12042841150080000d02100510301c094030781c0300c940d11a61140a03210000510b0341c1e41c0075040c80000c0344200000c2c540191440c00322180d805a00f0f14000f5801040209002d9034020b441c0d01d00040c00f09074800082015500075980c040d510211984808140c4005a2901440e4450090180900382a44a6060079a6028104441da039100c5d07019000c5c070b0503001009480312341c0c030300021f100c1001030240b500b8044410790203403103840b1942c841c02501240000c94404022a20003104800041d50340030850707074045052580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 411698147 1250 411696897 411696911
    0x80a09060e06040b0f061003180605090c0a050a06140f1612030e0d02031c0225020a0e0c0a0c06020c10060906050604051f021e0601063f 60
    0x180810345445101c0948a90016014002880b0511032510b51000114a49101a00305400410003045011000504040d5224849080b15040b0f20090448a400c51b2080c0b2907401c0c46080c0c00d88540c46041d540384654405800003446040441304c813004c961142e1500c55502d08070346500c0c03800350b2100103100f600400400c0480d10000c11081307180d101350f0051a4414002502c5040901254200c0c48541401e6000100300200c841c2d001003111050100d070440480f1084103110300b80003038010610b101d500172100401904039209401c090040b42802110300065541d034a00740c2c410514020b132042c0a0500c400c11030080400d01445002801c00d215080040c580b59200c10014182582103071900034081d210182000700c000316000396000f8010417078009107054504000180c5034011104601041141c1040f0b00c20824000d000380040c5409a000701444095010855502c9420901941000c0340131440c590021f04590070b01006c140840040c040080501480465000310840c1d4102190310703140c4803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 411699397 1250 411698147 411698153
    0x305041e020303040315051b070c03080d06030b1302041104120b060112020309070503070801020a02070521030c030705011a0d0201030f0609060305010f06060e0a09020a03061d0a0507020708030a080a09 88
    0x186e80f00341d001d05c60002405042401c0c44500312585880d001000300c030180121070125602c04050000c995000c900f2036a614540380340240035103126400540000404010400b01c8080814001e0741540700320340070005852102000005030040f4024410b4051b40ca20401c00000e00001c6002d402200504100a15100b050307043c10130303a4011203101281d504031400411083c00d041100d1005042d15800a50500d819030303000a60f46c00c038611406101c0e01203a104090100c0d49408001418004007040c1d070358481088101695950103500202e0b03666181006000b07032070000344001082c103130004003120319695064004402401c040c1c1520702c44990754490000f20b00300170348240c10040d40722b80000b1400045c0d080150040303e10640c0070304280881310307080d080382d0381e03c2401ca103081c2c4400c480010b03103c0c010600120010903854014400c0c0c1c140e4540c006010213940e104452240e039500300180f0099460050880e01c40e00f41c1d1090240035813080c0844820356019000980c0d1203402101d0004101c01252 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 411700647 1250 411699397 411699413
    0x5090f0a0603201c0b1314071403070801031202070905161d0a051c230d0f0f1b0506040b04260708070303020d06180605010305041e0203030403 63
    0x1601400c0420364411680d405005120a43d03180c650942c81c000d418620315540072001031811010340ca12040c0c1c4c0307080c81c41450740d07150031500c2e000c0c951070020007000034507414214201605940f4800407429200114159072100390890303204180d20b568042d003903441c40e070740d6800000a084030702c010743c003034a04041140082c5110303031441008445596200c0d14400714001d0841014480c809280042c007500a000039241c1c02c0e1010102c840668400b24500490b030203800748e01e190740c2e20041c62034036180c14204c0c40c501403000441c400c2400a0a4402c08000300b01e00b90362030310707220640d900401d021990303201d000382c010882c02c0002a003100d0181500382c0103688490411030100c80407030394244811f00f0f0006000100c00d000c0100303d48e011115003443c036140c40b48401c5010301c803c0181203003800208034080604c01e4050342c011524011003402025113444000400c1d040092514090500d04540084c03150f10a000e07080c001c941204110007403000c0340043c540342c0804540140d03010b1208110000c0001c81003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 411701897 1250 411700647 411700649
    0x7031b081908011409010807030f05070801020a03330303080c0714150603061003080a0302090306071d030115090b0a0509070309033f060f060806040c09080d05090f0a 73
    0x195925402d640c10f000042e2400381c54515540d000d44004e800502c40340c0000119002a6604401c50b408421030701e2418a251014580020056500120359100070b00c3d059040300c618050314450f2592040148a8444005844e01c10356005841000d50b0800c0828003401d40300f50860500c0d481d4030318003100c50300c0708a0b9427280700c02d806d8266444403d55180200480794100d401c41c40480240c00c080c01c0009003526441220301015020b07142c00100140018041d40c120f5400b150b0240036241d070f80c40e140d01c01410b80405582c1b0065600c50a114000c00c41c07406124130a5401c0c01701c620203903024100211341c0010502441103a800900c4000d02080c03e41e25890400c2c40303110607030342c0840c64099a14000384070b40009040a951171100382c2e40104603150302c41c00c4149606900540c0703400c0244450010f400f5041d243d000701c47c8040f0188001c190180d10807a05c51140400351014400794121103002c603070100300e40c499500d09400421158120500c250020303c03100c9402000c1c0031100d100740000440b0f180c02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 411703147 1250 411701897 411701947
    0x70219032a020a1512051509040b0a060902030106090308070501060f0b0304110d110d030e0a09090303060e0106050f030a0b09010b03091b2808011b1407031b08 70
    0x1082000754218601074030401c01400d920480c25075001c80e08035010342040046960026116100c400280c80e1001d079140540e00024010b003460300798242807d010300c0d509010f607101c644084c00d00b60085141c450340e0086904850045c0d441503420fa01d59150001c454000e140101c56954071800005140c50140d8070810103030404500082d0359042601d000b2862443c1120b11381e000300e0302c8000710400700307040e8805010f0030241030710007014080142c41c0880e1103082401143d5030204c2c54040205280240341e01c5040d0142c4684c48c10401940c86506104400300c007441a40000345003003003074a2000c03200001454111140503000702d00d04150200088100400341c000020132500841003045181c02040b6600ca04528082d240550903841c1c0c0101d203170503014a46004100b5104107800110f82c1c0e40505d030074003e114020003041400300b00c2d00c0200c104052891070800050f4000418046031711410704071440701ea41078941c90188101c00c00e44030440c44180c20107070b1305a0300604c01400c903002c005481040d0030103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 411704397 1250 411703147 411703217
    0x50f1f0801170601060207030b0916060302210c0f0a1407050d090b0a0c330e01050c0a0512060d1208010515040305100509120703020106060906030507021903 69
    0xc1011103000825001000b0203449038802e0004020050b000301c3c554042c5c9802a040c60b129543c0c000318940341c9290100c1040e25819403400c00918541d055015140c9408616400fa481500c003041c0c0c11030300641a55032604018040061084070026100105030042d401c2c00c0034800729659141c040b04941100a0940c0d007500031205818180d0752100501001d01480071110342060a424001000c051a20200900e018060011480d0000c1444001c0c118050300301012940c8403841c032444000b400a020512041350f0800001c03071404801c07101900c61a070102c0d501d660800809681600112030058509908070043d0080200401d8400d06001c403000c100da240c8120325403510741031048100d100741410f80d9036a424401400000c00c04581c6043c0200d100c234000c46c0b15119108164184000c41d13000ca10308240002c1c1c08000c068040d08030754116403481d10398514066440380243c2c03c0d02d108072000b0300107030400d1106c0320198005007498400e80307009240444403c034100012108001c20001c0b04040b40e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 411705647 1250 411704397 411704399
    0x3040f050a08040e071e0c03050d020409060e091c180315020714030c030a08060a0e0112050c18160c080406120b0618130b0904080304050f0a0c050f1f0801 68
    0x300701307419180c201000b80b400c84401624030310006143c10071001464100201003c00c0c509140c40786086c0e81c506800113100315030b00c69a940016009206910400000000c01030004981c900c0104028002e004450b15a940e0950328600803a00341c400602c6840811104d0500030012801d2221049014006100010b984001e58202401110801550100107510030860580d0003035020003515544443e50509052a40310000082d00711041500002108240c180002819a040f41c8440c4070f8103001d030041d103a41030048020702142902c1d00da1104040398105010540a02d0544034448562030030b4600315191080696510405911941c4801b00182a00c03a9824441c20b0034400d40c101e02d0011602540703808402d5a80d048100000400b03588500c20340b56414400001070381140440b0714004028000074a031510f004070b0a90800c1d0350945082c4295100030100c00c500142d40e00310207400400440803c2d10340002c0140c000302c5881829003190b03070441c3c81d03d4019012000750800082e2a145d038a600c3d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 411706897 1250 411705647 411705659
    0x31b0412080a080f040c0513060b0f040e0106080c0405100e090906060406080a02092205010e0a060606030e061504140a05040512030708011a040824010b040605030c03040f050a0804 79
    0x8418040d001104c1d0813405800e00000a0401e1401c1c01120303070a07035404400110180c50840103141c40d03406258804400103e58800d0420310b0002c0c0f080d200c2d256a0b000c842d9895a0007128608821103a21505080801c018081450800b2400b011200b40d0320340714160b04402d10125006a5090741c03921800e900800038444c261515020309006048482d00030b0030154025000913400300030140012480210031040494422100c0031004003803070300302000384041d01015903c10750703a41d030f1240c080e540d861400d4404a070f05031082c041c0031b80700b120040050034541c03190041c0500e07215802d6482d66000f076885028a14001d80c0601861003030144000010b21403074a8142103041c000d020354402045402003041114040d00011103030305540c0080d00c4030000b40110000c03c030451156422929403842500d00030341200d400c00f0188200b2459075110303806940d90f0781800d08a42d020324002c4401149041c0002a414042078003d154480d001b940c0441c241c1003180c032030f0f60402e10203640c16901c4490000e010b0200c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 411708147 1250 411706897 411706907
    0x61204051c020a080a1106070f021605010c110102210403020306060906010504090c050d020f09040b04060b0708090d2f030c0d0803042d02040b1203031b0412080a 71
    0x2030500d00c400101d640000c051009464401e01d000003003840380046540f140d000d10031451001d81150090490741c1601304008086c0c0760015140003980140714200c1c040b480960324444250842c0d0041c0c4036410036008130b643d41902c1d1684600c4481c1180b01d8448239100d00d40b00211114000002500e00d207940707a0460041c1030520f80c00402690203551100b041c0b00c89664800e0032901142c294000001d150a41ca5070122024440c1c2420344d01140e0010981e5072481c2e0607103000b0041000110390030000241c0030010300c02503034214452208032900500401c00400c1103a070041400306002800c100803855503984041c0030b500a10340b00c0c40c0400c0700b0503020400350320098a10750132000890060562440d90000280045061400240368101c0440403a041110b003001d5801c4c40f40d5181c1040102c80007a100b445035600b00400140d00c16401c208040b1000d003440c030b040c07135403103000c50b0081c0d869079a40340e10114956003c0341c0306025542082000080500300d44401d0040c080c810000e89a442055039030040c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 411709397 1250 411708147 411708163
    0x180b0a090506070b0402060a020f0327010905060d0b010302041e030c090b030c010e01020109061410120b0106050307090902040f050a05061c111b0a02040e0d0806040b0a0506120405 79
    0x2000302c02c2080400c01254010054650040e0b04849040e070303601c96410200e0030100c0342c20390341000344008640b41c02001d0186000102003241c00c612b4803205401d00004441c040402d22400d60060010407000a1101240d04010f81000040c1005860541d407240002c000028556a407402002012018402c1109910544000f8501c60308180800220705000940b51034940511038184000e001894065900070b401410149401c03000802074034103000380d4040502c81c21265150071254055010414004030f2018007100b6800144003201a0b0a00030140c44540c800342c030348001e02c8102c0d240014000158001000a04804041400c0c183e160109100c180c0740240c114034802c550a0085800918060f05484095850302c5800704c3e40e001c4442103400a0b100e54092402c0c0740e00001c2e1035918544c8005903e00315584251420080f0780e02d15213080c0d032519004801800021141000701c1c40b1440d298101c01441c1030024002c8854554a00009a881e4024003801c0c0b03a094500080009000c02440589 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 411710647 1250 411709397 411709399
    0x3050601081f20030f011526070e030f0705031204060e041a042c03030f0103080a021c0206190b0310020d0f02030c1b071d07180b0a0905 60
    0x1140b0154410001069a144245402155480156048050704040d07460f084882c2010318594901380510020b616070070900a5007070300d454030440303803d00c0c92043c088001d40503003605040b0015241e60307099081d03c450203080541040000b02d000561540c0c14000c0031101d90340c1400400c1030500d03100a16042c8240052030360484a0148800c11029401890305860100119030010b82c8907401e154000400024903001a002403502d41c1d00b170b5051003407010010003000792212003600c0b0245c882c43d0b180e0701d00c03045500801961200700108002258000a044441064019600203032a519228400d0040280300040140e22081c00c0c080d650083c0d2002c0e40040580500900c80b14039104e02180c2d1350b1403000c2c40b003c1c21550002c0c607507152031040d601682c5036003e01c0600755900d0410084206254009070105600e24405140302400c661002403a501118422005455080c0071a00f41803e40c103c0101038809100030803090f01c5c485410060744070081e081c00702143c0d864034a1036100401d0944d40350405 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 411711897 1250 411710647 411710653
    0x2c0909071a0f03040b07020703120f081008030405150f03070e18012304020c16180b0109050111010b030718140919080c0d03091106120402040e0123010305060108 71
    0xc00740c03070880204590340180c10a80001440c6c07203141e0101d290902a502c0a40340c9d10002002d0082c1640c80003800c20f036070042c1e6940052680707a48518202c0c11000b40300b070b20780d682d0080104000380e0500f040341200d8209215209420020350f040d00808540c001c40d00d400001f0403030b001006e624540880002d0709100b0141801d01c40e5070616420b19591481101500680e158020070f60b40c155455404075040100707458280d414420b41030740d0021510000c1d00901501d0004901d0000f0200c1903440f942030310140c160340d000041840c0c04019a800300580b4030340356465403500d0807483e49440400c400c50041c42e0b0100e64010b01b8400140020031192040b0303c09181001501c140160030600003008640f0303400d84400a49140e4851030b080b011403144124501a034001c4d5803851618503015404864424012907554407a124a0000c0108a108003102603409002c40c00109016082c01e0380050040940f0400000b0f851240301c4031101c80d503406001481807081c1640050040dc8001d206450040c0408001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 411713147 1250 411711897 411711907
    0x20a020306012318010503010501080d1d04060b0c0a03080702010e0a020f010302041a0403060b0103050702150a06050d1113110a08090309100f020606030606012c0909071a 75
    0x207403240018400d00c0803456200d03480240302d02c60145804903100c801400140d04001c007803030703195960500740705031807217546803400004090b080821104e0038011503a9071140030140420820481c92074200144da0132698070750780411014458001480c2121401005240b440c031607140041045034014040c000316414401c0b50340300f21000082e22080310f94110741241c0c145100e0401240240107a50048074a0100d030000e982280c0c002d0002801528040c00d81403202d00700080054003515410384600c40144d1011240215241407860380541200b040c07080465510b070340e80c0000c0c036030742d1240c0e00c11b41e090110303200440301e075140c03c000c549042c1e1424201801039210340062600c5502a004082e014400701d0000101075030401e10840c0e0311020000c00481003481c8420008003550b0b1032b01128001340c4038480202d03006140c0040d4841c41904143c2d91069400c400000511090540040005c0e224540c0e0717906a1040c0c0d24081d0661240c3d02d07040c01000c0c2645050301c0c001c400034510301c00304482002008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 411714397 1250 411713147 411713149
    0x14090a1b030506041103010e1006050403120513081b011106070e0d080d09032c060a0c060213141e010f08070e030a0303381c0b040501050412020a02 65
    0x314640c0c1440e003400a41e0307603981c2e00800c01500c00800041c02c2d0550000002c40c10304031084080d8000e605c000d07820551103450f008260340c0e40c422800060110410030610010040c401c600400820319040c4010018560310800715141c2800b842d518402d5240d160251011545d002040d0050403518200524103410114400340841010f100c3d054003855070800307000144140c20003220680c206902080061880c20b0400901d020b80103031000781000e031501c03030740d03041103a9840400110b04001442145010805a41940e4212102000b01e41c4184c09105283c1b2104c1e1412020008062031352601030b035040641c007000008603104018048483c034603c0080c2042e644241c90307441e100310b18103014180b500c90308000c3d2204013590000e1981442207010010030103905401440040d5222400360720002084c2044100308800b410036090b408256884041d001d14050502001c0b1075142900240744d540a9141d041f0341140480e020358460391540c007071104112002a00300d102c403840b440a010701c610503034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 411715647 1250 411714397 411714431
    0xb04150b1c170f3403020c10090801020f03010911130302040f0f09120905030f1908090a03030c0302070509270c030a05010b030c090708010e0709090614090a 69
    0x349020700b0301c080009100c001480560200c40c14541d0f01c3e045283c0f151034071000c40400d0040c1c629040d500c0b18100703181100c00590080700d402215803640243c038680d440300c0c0500c16500c0b41c404010f8100300d0034130f81c00542d011083c80249181c100441c901c4d562581800020b005940c90054084040c0f80700300b00703101c2901314000b0002c0c282c99041b07c0218045041c112100b000d0401c1c14140d8100e98500b1861310200042000701420450a07600d0700301d07032950344008043c1c4405442440e903030b15420840100511450000c040b51200b0300ca031546500341850300011810010040c4c000320013040d042c60184041c980c0410001e002813004440b007189502d00116080f444101c1103410007a4210307025a040c201c0c1209002c01000a00003400300c41981c0000e00b0881d0103000b1b002d45050003402103100442480c28200c3d619403140c01143c03210300e940d0b4604400032888800042454040080c101000300746060300d802400c0040c031880c17500c422500c00300400c001e460791025084a494914003901c14021080321 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 411716897 1250 411715647 411715699
    0x218010803030a05060d060606020a03140f0a1809060b04080f030f2a061905090601060e10021f06150f0207051003060314030403200d0b130b04150b 65
    0x100c0d0003c41c0c4d94039003001090006215610042c0028100704010451039800a480000389000b60b803203d1050318005144a000d1088050908030501c080040f8900b183c0940c022001d646c5400c1113900c00c41c2d64500d511000c440d060b030800d03240043e00140800410b28100010403800404c10003442c64541c8040700c90010b44201400d44408508940020303d080c00311043c0130a030700300b0500540d801071a0500403074001e01400380c14a40441e143c0310104410000008540f4169807540e129407040100000c2085103641c1c0014002c1c0c11481569040d1020f03c290000800414010000104829040484400904203006804000c00030b5100222f0589940005c44504403201914038000091145004502500b0705800c06044480020350300003d5032070010041049070b0290100d02c924020000c1145000d031035003d001d5900c86964100940480c1084a4968019110308145100c007010f0766508207207412b0480d019204801040303001c1032400e40c0b5006800c501c2030704469445100500710f00e107800d47c042c3c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 411718147 1250 411716897 411716911
    0x5060c1201060f0c05011a120316030c17071a0115021f0f06030809100810050418151b0c020102060406050702030c0708010b0312030606070f02031018021801080303 72
    0x54440c40103c41802202c0e05a111074200d8028441070024822a15611910078038040c014102e580c1c1030b0445245c040143c50603140c01514030340c40d141e1680c408484440c0d510405950500483c144290340401501c0140540c1d44038500e03000042244a40482598034160306c15040700c21440b03240c40d485a40416030391004d6480e0801084001c4d88005624020b04141d04e04a8106141410210911118034042e200d0340c4011207150b514036501c04d0044500d5142074983e0036119800c1c800520492405400240544c81ea00c1c511414110740c0d0b84130f071030711900700103101e09120341c0e14000c405001115000c440382c401e00368201100380080c02d0380003d40d10300004001400c03050b40c0d07001041c0098400c0c0704560034070410388120388074182c44400d00d9000b8034800310700030b04c04d22540c0d0160000318541010340307214400c02466941041c0c03903500c46803483d01100d02c08a03498050410101a40c40603403040e0b0f100d00704681401d107110705c03540c17040c44040d41c0704a0180d401081071500400641c0b600000701ca9110030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 411719397 1250 411718147 411718157
    0x40308010e0a0626010b190504060602070f0311030c0a0303081605031603150510050406090e040804050d0c05091509150a061b050a14011a061905090301020f0705060c120106 76
    0x201c130044050040455080e40b0364040d101140700200b45c1e0107016010183c0e40122410801d403941d03442e09aa9841039132040c22101100003504001003001c41200014466001c0c054803007030084c10001640301c403840d80080303004c61a62001c1c468a03003a00c41d0700d801c0340d008070304200b80f40d410071424034038000c80780302d101404164a8000c080b1406841c820b0b103000418010308218aa88035400f00904290018001d0b0000102007240c006003110041e44118019500300c82c155240605010a000c51079419490a4518107109040091b254848404070362040105402c90503554483c103080101c40107004d40f00803403c10782c902a05440d075642c021500100c54042c103012240482e0003c400c24039083e4a0000741041c06a40490700602c01c1c2d01a80d0b680a6208200070031000c402c01511071400e001d1061925002401842101c069480407400400e651040741001e134200015900001d007a64009001103d0440010a1400401c801040016000000f000c411410311403042007540c41c4071414031402c42000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 411720647 1250 411719397 411719459
    0x4050607050703050a051c02070302060d0225152f0c12030f041101080f0a0b01020304090f0f14010b0313060b120a03020c0a081902030f06040308010e0a06 68
    0x804108440b000941c0d114064031400840ca06240b5241e0300c0d5072100c2442400350300500340d8041e03c04200350f0700f925402000c540c10310036035443c244029000703d480201c0024051040c042e0344100402d054203114803c00c4883d0781f0341d00c0d01d401c10065454915104c04101000f110f554055020440902c00030380410004036101d0a114840501d01040d001595440340c0f40002400088401e0f1500148501e005801e030103c01166000111111002182c08000c00d056242c04502c03400002d0b000003404050500c1120b040903288c100340b0b41100c04510100603041c0c0e5990010340c554020b0b028403030201e803640c0400c4506615080d060710340361000510000c88580087c403e1000c0103100d5021100391a40545144003a10000500940d40c2c118031505502500c00c0c19807031801890590244070940c0c0e0f01401400040d0001d9444021a802194049a140c01460141980da034001c12280f4459402541c0301c0e40c007540b44c2250390a004102410340514241803443c00d000000550510f0b6442c1400b24141328a20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 411721897 1250 411720647 411720653
    0x31e2a090a050d0215040b071e08030a050421051905030112060e2b09051509012a0b070905030109080711010c0803070909150e130804030c092a0504050607 68
    0xca40008202e9020004200803662540740805080c0c114409c1a500c0070041015258000405070b59600074a440c1c0204000b5140459a41040b030b003091285640c460294604072000b120703001012035040010350302044d03c039030959221032174a040d0340090070f00920710350515056207080368400310050061034071a0150200c80c3d40c2000f2a00c00011114585511401820510440422906110700004000f81800310302480c14555981c00e0242c01d014451801030324000649003441c4451110b02d048011418260b4a804612100e004041c440c05542055142850001c0d04010198000c00c0c02030b0b141680004c0000c3e01c8108855500790062545142c0402000040300c500100440041400c4404000e0105041d007120b83d00041c2c840c41902400340300d070488502201000c5600c50451a0007400000c40c1d0b2004028580d00c0500c3c3c005d0440c18130307060300c0303071034140c005405644007101e2540d271101040345501e00700c070650744d002c4501c0e10300b003203080914100100680900c0c01100e200b82ea0002e000410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 411723147 1250 411721897 411721909
    0xe071d010501110316060209030c010201050c030a09050a0f0305041d01050a03140102090a081c0516030c0f050d17182d1002070209090d080705031e2a090a050d02 71
    0x80c010030940b5640c3c0702c00611b80b0b0001303500b100707500c18080d110301c1c0d01c0f4440e03643c01805840d1103080c0d040d46840c11591190001e2003d8070f0114016a1140605038112020400f51045420498002c2d03c03029900ca150401c041264000005c0c40e015030100d010042c01240c1d5283d9800c41101e8201071111400c0c1d400e00885170085c4035404800e0340c05400380f00c0014840c8804241c0d180041c2d0010800076080919040c1900c69204007820707580b00c4181000050006030084a0310389820b8003030000d00d880c0510700c0c2d80360f51800081b01303e4000482d540072501122060f0161880ea44003400410b5000c0343e1844000c01d66480e0f44407001e02403400845003074683d104005c2e40b8841d8000c07001b401200d9040ba41408220001d61180c1800da0107010f0740400220300480011b9402c10030502e954070b003501c44e9540b54080726190000ba21110407505003c1250086003814a440340c02103d407400225025641078462200b46c400440314035007255418032010207959504a8010f04903403060b2145409034a0600c00200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 411724397 1250 411723147 411723157
    0x111030901031d06040b0a050c090a03021003230a1a0d0233030105030708150a0c12050403050c060f130b040c0e0f04120c02060403060b03071502010e071d0105011103 73
    0x3e034600c100d40403c418441c4010340e1a0140c401080d0402c85a01c030003100704010f1081120f0b040d00010f200d103040006047c034000000b640d400d503203800070300030364a407c85401c0c00507034460308640409441c051002c0100d0b0392046104085440011022200082c1e000c1030100a400001912900107040000300081d45007094100040e0110f18420040000d8440368501e50000e010f000d02a22900b0000311740f0311000078090840d50003111a040c1c096480900701c101030420408001b04200a04c1d02e180591010703400789038000d51098403050f40b903400144000c0d29218000b40a0311040b0700340c109000b030490601c0910700c07050350846128030040e41c40e0b05080c0c03000751603540906042000360080040a80789036981d140218030a01040a00009061084400c210905406540004104801c10000d81154402123880d5006002e5131101a5121255200906141c0095002d0703516410603000d036140038440300c0d0103040b100c41a000703007855206001032000380c14000e10f41400294030a80b80c0707070321023007042e24 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 411725647 1250 411724397 411724451
    0x120803090120040f0e0c25050304120b0a05010312050c031c05070809030f0409020304020d20011b0f0314070b01060c0b010e090a080a0302041d090705011103090103 72
    0xe0811640301c01081510382c02449800c0865040342d4000c10804440b442c05c5028100c8109010b05211440c18543e82c09030194903a003080e1a04400e490300000c0c424000b901c007d002d42d00c08000312210783d0901800c182d00041451602500c1d000052000900d1085941c0c007900240c500213495841a10080b85103101d0340c0c01003050250300d644400c00c0f122140c1c002ea84602081d07507590b04076071504146d4030360344d01542c04400e0840380140001e01c44490f0680c051580240003d048054032002da8841d05441000580004c1540d08590000750155802241400c89072284001c12104900c2e10f88482c40b1422500d00c00804020058000301c40c1c81c282c640960340700903001210a80c455a48580c0903101b442900c2c4101c810041400000400380342e0205018452210603004d01400380441d80c07222904e511440310502416420320010034007000301c1644200007084851610842d0030030f81e099920380081c0364000e50400c01366032000003c034200441078402c0b103142030a001c2050390f41c450075001000f2025200d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 411726897 1250 411725647 411725681
    0x703020405090a03020114090d0e0a0b070b060a06050903060f0606070203030310030b1e0f07091e26121606090807020405090d0e120106050613080f06011208030901 72
    0x1004011a003c148900d00c144260003c1120341204511860074410403680c440c441c1c0c00c911009109640a41c09005081000500c1c04c0042034540d07034080c506800c40b2101b82c4003040c20348100102418901d0f20304020304548d0034201e00740502600040c0e5036610060400d000105100301045440e00da40080d11502c0b503004064030780703030301d0810744510504906c1e100a4402c001e0100100c1c01c40900d41d001c40815020640c0954025600c9807604086040c0140c80a4204030346440300081c8541c18880c101d12602c1e9600c001d00705240340070040500310707080d00d048623096907000c0548c0010a030006400c04a262500c101180c59a440f11207408286000c03a4001d81910300742010001001150030082c00c1403072080b1010007603a11222003040d91038880e440c0e82c0000c100c0c411425206403401c0c2d10103040c030120400012810b1601d4801140c4190003e1020382e48062490106011901c4240207054559000c01d0080040750315100d01c480070740720103803009000b00000001041030000c00790419a0201129405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 411728147 1250 411726897 411726901
    0xa060e0c1c1208010506040e0712050106090612020a090e10030602030406051f05010518040f0c05030106023f0d0c0809010b03070e060105160b01091a01020a0c170703020405 76
    0x111040e11030790780c008885510072410000e001c0c1d0b01601185050301c0d806000c450800b81442034440628501078803490610903580c200d074030300110902075140038182036070703c180c1400d00e49107020b022104007030f04000c10303180140800b4207020f500c0352403003003118408041d0403159140d0109010307054015800240910740000100302c1441341d135412803030040d12002c08459444000c03134004402c0107414040d070b600040041000003680b82c1c0d140c54800e0b0820000303000044122000417483c00710340c503440042c07000c03074804001002801e4051200c08a40b0540c0000448010729002c903810031710b02c1c1c0100e181c401c43c01c00c0d00590100301d11501a50060380c1140c5040090f42e500e05000741c40114100c0c1c03202c26075030801c4051002c42c1000701c1d5202c120789046004010030307201c5100554582d0001151500f42103203100c442c101056400d2081d41c000c0081410002d041940b0300c4c1c1903100b200104507d241550b001c2441c0c02c001811000d110001c441c240c10051109141d00380d2898108a110b6001035449030411003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 411729397 1250 411728147 411728179
    0x1c060f391125060507020a0302150c0f010501050906090f040b10270c0c03021b0f09070507050d0c0f020d0516090608010506043e030403110d08090a060e0c 68
    0x155008801e1140e801c1420700b036a1058115001c2c8a282c000a420407540c1c0780800060070030160444109070345110140c2016401c4800c186010440e1080c190303660344401c0100283d05200c2c102a410242c1625a000a07240c03a400f1824003140143c0700800b5025050009002c2d2a000d00004010f07128807011001e6086144e801844500100403004814a00c2c05a03480a26400345043c022840d41c5a000f41116900f0302640580070f00c07613001300325007002c0000b181c4540f9585001d00315104400c02c2d00c0b290340b1901241072080c94103425114000c248451104604041340d00301200705131499048030f1040c090800351810600f050446c03280b500710454581001300e0b062019411040607542d8400c02088207540e842d0400003525940c420301071a100d40b40d107030a81c402c0c901000c442520f0080e16142451025164515074250340112030690010f0012032070303050011400c0c42061800c010360700d0129803505003482880d843d40c0410500620703159940130300000b640000d0001211070040180060f0721220821 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 411730647 1250 411729397 411729433
    0x20d02030411150a02070506180307060206040b0108010902010503152805040e2b030605091e0901050606180406150f1202071703061c060f3911 63
    0x1141d6a116505183c8451503074a080400d842c04400d00368020120545000103201c0c0503032154144810000c112103441215480400c418402010740350b0080c10540ba01c0d003018000030070b0680220311a64105030400703000d40e0707100040e29040740d00c4000c1075541e0246540014030f241001840454442d481c06120351600020540c104220b41055506028800c4600c8840f81c0f40c2400038003900c02405a0810240d8022805842c0c2c8001a0641000640300d600c860009400380821140e0300054002d58031003656180c0303801c20181e04020030b80000d00170b034144032001600d14000c8103c0529400c0171081c031000c065031980c100c14002c000300d07089601d2403902200000c0000c0c42240300c1d0b0000c03402c0440781c410f918026108130303001c40c3d4100303034032100d020032000020102d6440600034541c042540c1e801450007440a503500a4940d00c0b80000040001c02c02da42c100594020703c41030800d2410001220740e0417400c1b1500b0040110f4440308005245641820680d110162014040014402c5402000ea10347d054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 411731897 1250 411730647 411730673
    0x30309060f030b030d08040c1706040204140609040204050603030f03040524040302150a1e0b0109050f2202070803040b0919080d0c091a041a0922020d020304 69
    0x5941c0d800502000c001e00b9400c1c2c81d10100c030b0039019400321100e0656148902446c903001440745030041a000d0f0381f103180c1401d0201c84000700e103494110384240800c6103880e10a00d030f0750703034010310600180d881d0080004282040040c80607004d5034803500000e42030f41e014003c0b103240e00c2208120503281d00305402e0030355840c00101c3c1001c0741c60001c1c0d8021040104d80c2c490f100d01c42c0340c0c10341c01044030000c0c880e055540902d029201e00111030f100d10800740c008628440036143c5001000e070003c1c010940c58001065528154080ca006010603500c4108a440f403001d20340e44080b101400c100702c0c204c03644595001780300d0290302034210b00780401440204220f040c8a1070081450200f150706040b03064013980042ca642d010001d00350a0708014885000720581c00031240181c2c5030400702426541c0d50000041400c1c0c404908803507840c001011320448a601e05030b6181102d07401c1c0d11905001983d004039140c0c0c205458501080c0582e1851303800d8085c3c294040300c810b60300e04102551603003481e01c0d1039030890000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 411733147 1250 411731897 411731909
    0x1809020f0307180f0209040c0203030a0516120209030a0206120907081212100f0803070b0a05070203040b2b05010e28110417070f06020706020c010806041401030309 72
    0x104040411841c0004a0380c041c0c8032000e040da002c003000c2150107001812030000810750a5000e00203031342e582d9610303c1840c0c0b41602d650003441d501d281a4102000300c03100209190007501e0f13002440c01c071081d480aa0250340c0f1000c4840140c0d61140100024500484000000d6003c50001820302487c8003c031682e03070041d8011340444180540f2666603d0302c88a141e64643c0101c50705020886010440000c0b4039007103507001c0b005890700354849070601041a040c1d000031038660f03c0020040d080081a150455010207140400c101e2400e020320000d460384103610030781401003000303d142c0450b0301c0b0410b000f4081040321a140c1117044c89547d03910780540424403e0f028000101c0b000502c0c01580d158901c010310f010114441c0400407980c4407800104034030743d40090002d0b000d21021440120360301c0c000d1080c80c10b40c0c0040003400c0c40c14111107644080e0390415000c6400c011400c00ca4103400240100150000342404806561014040740044c8101c00150061509940c000401d26800514800640304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 411734397 1250 411733147 411733159
    0x1060611070b0a120b061c0507320a0504171501050f0108160309060f0213050a0e0a0218030d090510090503030d0e0a050304030309060f080705190504180902 69
    0xc1d503034801400c140143d0000c0d20110f0382100303d58666500960205109034001031059051485a10711003010460b01105c01c0607407981d80e020b01c000d00d504159000c0c10802e0012615032420f1034071805032000800105243c02e045404a07581400602070000c1c1d40182901003441c00c800d001a15001d941e45030141001c60341865440300128050400c2c80061300441010b849082d000c1d00c0d401251031881c03221100e4075041680c0c131140ea00024190f40501c050740c0c80d85880158807030f4101d03061100142c02d9648014801c6100b0300c03040000504003640700354050b081c01c4005880708064559800c0960781f082c1407a40c5800755010302d04489800424490580307200381e5004c03c84403900c0105a4a51599000d20b95056000b40018070a03d2501d4100d81850102030003038411010060703440d40e02d143c000703800c1103001c5242c010090158692000c4030340030400c41ea14207120130741800800030f0014400d10b81078440b1089003022020744607014404980080c0a1001c400300e03902d8a42d412503004201d9450304901c212 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 411735647 1250 411734397 411734399
    0x50a06052815081512151906030b130201140c0f06010f06170a06030204050c1902032703070f0603020d0e0a05030412030923030c030a0507060f030e0106061107 70
    0x1080719003a0409680c2e103500d0300c0c24141c40700e07413030f916010482c42422a030040e880d2203040d002c6142804400003a820310080203620381002d4500540440000c103064244614107841080814644604150401c0750380192603083c00b41d070300040b1100c49809800c26180b00d0005030103100d180e40052101c481b180508143c03059030344c03521000c203814915440ba21000810540181c44428004140e0f541c005c95508000180c8a5899001c00c0a40740c0466503103804036070108484440d031940c5401c03903000c509184041c5182000304410b2010f00003180d000c0100840321006214000d450070040c040c00b810420303d24040c0d031075403524000d02960240100665071410400340240386000000c0384400c8950000155007020b08000743c000d000a00d090701902041400c440010310380e402d403911046841c160122400c3d2000c24041030514081d568690b2038040c0e80921014001300d003021880070140e0384646018021551381c080100c02400006010f083c0139440c0c0385000900c40d070405551440300e0404015102d201e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 411736897 1250 411735647 411735659
    0x120807051b010f08070e01050a030f061502060709120809040e0a05071707030c031113060315050c090f040c12021603200d030c050d0903083304050a060528 68
    0x81080d1888004a4986c4039580c205601441c06011000942c4c500080d81048242c42242500ea0b107a00c0300303014214550004560560501000f075014071581800c0891500c0c20b518042c5000035180c001d0003100012400c41c6040c1da840d0000320081c1406c00031141079040b80d003082c507121503c0c0d104440c0380c5a800e00011502d801c002c200501240e402006444540c1e1454444600d840e02045040d40c0c4041c19564643c0c5c0d95506104110180d400361111403914503136418100708569010300440c01e082d07003d01078466035070b5541407124151002074a0102d01e0840c1c0002c02d82e101841503e035002c0c694004520030400f03003a0342d007103c010213009641740e42d052041c0b002d003442800c031840312404031070b0070006204d140c050003500701c2d0522602c68034101d854010800c0e100383c222450404111300085201d0103025008200c0802142c0c90b01100980d140c08a9048a20308414103004808a01560305c41c2c0c001103005025902c132800814000d0078401d1041001303182da558110f0805400e50848840000205403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 411738147 1250 411736897 411736907
    0xa060501140a08190c080a081e09060714070512060411010c0309030314070c061707050f070b0a09050a080a0f0e0a060c05210405040b04020f04120807051b010f 70
    0x22a03c030480130b48409940600148034154013803405948541c4035000020f0960307010081c00d80000d00030404180c9490040c0141c281c1d55041e16403a5001020901201501d90307503a0045030012a4000302c640e14445803107644600704442076000940c00720180c00d21a200d400c0102c0e00c2445030f803090281425065143d0019034500c2c20701c100c00340c002200c40c0414000280503862850190380b90380062814040183d8a1071394011590f00140c000403140c2c000f150036690b66009240e0480001d08007203003410034080074401329000d8828060921b00f50700005c0b80745e00c07002c0c5d1321400155400505860f1014180e007041005a031100c041400080c581c2000f01740300034401c1c4280031800e44014800840f191810000304c4902c0d120700341c2543d0501800c078003950840e00f02c14240c140c00c040c901040e91964030b800c00704022180c00d20038a50003140100458a500c4090008440a07920041030362010004142010001809541002062440b60010071140740c8040928510034402c241d0321f181d202a000103088034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 411739397 1250 411738147 411738149
    0x20c190609051201110a030b120c1f0306080d09030b01060c02030616021507020c0f04020c0c041119031d0102070308060906190b070309170c130e0a060501140a 70
    0x1034250109002902e0010121000e0724220400071074011040d480d1400c01c2d9104c01c0d600300201303580b20200c0c061410498a5409c0f0f01c11010098400100304001260034402e4511000d49800068030202c000c290183d40654080c02c828011200038100350800a841c462042c0400c0d90311813401c00000a0703540c46540b415407200c1d4042e0140182e80c079055907890440e80d045001c0000d40c050b190391108c4104602c126a445521107900400d8000514424060000403445015004500420100c10300d9140010b08103030f0a6400e035000036050b4800554404180610103410f100c50341c6060490201070780c190821700e020307041c10044840c90300410749114201d00c1000d030020081201c0c81c0000c0c02c3ea02e02105560b51010024100d8203c200d200c0c0c49004919965030080c205044010031040d05040d441800d840190a449204090660b8440e24081e55200c40301c98441c4241446240880c407044543c0004a92607040c004440800790249000d002405007400784038032001038440c101d2118a4100210b01c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 411740647 1250 411739397 411739409
    0x10b03070b04140646021506190f0e0601030605010e0904080c070303110c0a0503060f07031b030e1c05091c170a0306050901063c020c19 60
    0x340b400c0c0c5003014500f203219400316025402841030004600c1241414483c0813602010703907800d000021400034030042007982142036080e4002c200700407501545c00184102c10810004a201c069030303600800031b408480c0d02c03490701e480031410110000307540540b80c0003075084d03c80c52141c020155640d0030044003101c106118149c0000d0a1042070049401c001c0300c0d103500316000700c9030249004040114180340001c10342c41200000c000f000301001004040c00400003050f421510035401500d0070000035130b01c800c081d00c44a09410300c0300110b402035000394000b9008924102c0a54a08018110003a00405011826484070300071a49844000c400401020000070300a4a509080090a50510501d070f40c0d9044100300341a0048418008908408204407100303d41500b00c43da11550030800a043d00c13050b80c0040d0203158040c00607c40c1d0354100300f1142c05031110f01d0050340fa86180c682c451110304c0a0a044401c1c070040c8040340c22a10ba40401c200e07412110685600700c041c1d640c3c04d101810030510740300e44c0e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 411741897 1250 411740647 411740669
    0x3071a040b0a051017030723030307140c160e160807030c050912061e060a03080a0c0b07050d0617030301120510180c091803050c0a0b090a05010b0307 66
    0xa00c5107a095845142c01804480c500e226440c5c45440c00682d429a10402580c00c0e0301c0890900104040b60000c00c090420b41c99843c1c0c1c0c41c0080075101c0c0e6407030102901d2402440103004914442245000a0724400d103020002c90b0340709000061240c91224103402144200540480001e0303621141c105042c8001202c7d550b00309850341d4509044008010744051402080010803a4a07019500d1141c5a451017480801a04403400c0c01c120a503074421010450241c5da20480003000402d40c4c1d404d60450481c0d0b0004d214035581c0c4816002250300e001c0c40700004042c00480818028401d5104004d4a81c05200080030044181c65204002204000140102c0c05520800042c0124007240c181e020070303148078004840f40c0080042403101500c00c41450702c0368091480c1011803d10044005d0013000380400340c41086809001410610004800c0d8405020b0141c00500080e03518010441c01034100c0d081403444480e41842c44a42c1d40381c0a11b0300e410b0700c1c65030900c1d81a51440c0740201d0078008481c04e0f8a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 411743147 1250 411741897 411741901
    0x7081e07150506011b200f13020d0510030c030809060f07030207030303050c0c12090316080a15090f061104080106061106010e0115080405010f0207060c0201050a0c090e06030f0f03071a040b 83
    0x1040807180418003d1a0030800440900c01f003a20b440c07002c00b0402501c14005a140c10781d1840820445c0c800034840e0178110740c45501040400d40c0d110045090300c1e0800304c0311f691641e000c0c020a581d84503d0540d002610f00c0001c91400380340d40812010142e92103a9000d2000c1c0cdc40c0d0803c0c4400302d000c0c0e0011801c0c1a00301924080440c0d50303c1c0e00401340680b0282c141c6d11418040c2c0034a044c0c0800710350019520ba000800c030355041086800401a12034400c10040024011644030100040c0302d0364001880310b40c0d99034aa1010300495805d40c0c0041c06200300a001181d06c42e100104480c040d007a4515543c4501e00020840381c08403803900e410303240c1d41d55103595131000c902c0003180e0007480588141c450b075507105d414100c00300e25030004048050080b203000c00e41d04442c42000f0308641004007a903000078039142d46105c5159010014408580403d80c8500240d260500040c0c142964003102d41c0c59840345021010b43d001012000d401c0300d038042c3d44514007018581e040e00795036000c00c0381e000301040c1041d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 411744397 1250 411743147 411743183
    0xf21020c060612070e06030a0506091c05190507020a0305030a030f110705030f0a050909071e09380706051b1c0203040f05070e1b07081e07150506011b 66
    0x52299006c040101140d01441e4140c84941c10048150380480085c0c101c000f8034a4190768800140b601c100b401d01d0110300d011141900b515001c40b84050300010401d0010b211002d540e92a04000081c640000c1501e1f60340000000180040143d0410245c03a03e00301078218110010800c10b840203d13422401451034603001c514910342030391100c0d54102c14400d080c0204200b54483d59a094421220b035142c070070308602c0d908000466280c2c448401400c000701e60905000c10841109603030140c9481d1030040b10602522003210b41c0041c00c0d000750b002800d10105d1b40000b40907032a08554000d00e407040d1080b844440c0746890120511400038090300140071030700c0180d03035801b40d03900840d84135000700e1543e40310060f95a81d190070300c44141d0248046640c0c401c21b003d004c2c04550350b4002c40e9140104a5031a2842503030b60391225000b5642400703044880c5071a81c01002c0c45660844031580d40c0600c030040d40c08040d42166000f42001c1d42ca640c00100c00344c001075901d28000d10800c400c0b6410040c03034910110161 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 411745647 1250 411744397 411744419
    0x20111040303200d02012313150906151d01030b0609040821070801050301090f17090604080109060605010e01050913061d01030519080a0f21020c06061207 68
    0x4404201080d800d2a000101500c140710b2200f070041540c2c0081601f900f0b083c00c40b4008240c0202c0c40c40503994140501000540300b45980403602d82c001202c11146060b081020004d04100074082c00c1c02d400d010a0603155642e5000c101c06944408c80300149003082c003080321540e00ca00740802481e11030381c0c1d40800c00d2031820610840e40305202d9122945000c000c2000c4007403040018844451036903020080c40f10301c540110b0b907203000d40b50613030081100d0728982d150201d0035011414040c02001e81c4c0450802c004c3c101c1000c071468008064042e07a5600e0317540e0821402405100810350b1803a2030801c0200d82903200b06200c2d04405016512642841d107400200003003060782c0d006100209a54103000980060032020f02c0d442200c0c1700d8441380a6605d50308015081c81e40702d414884c0084034900700000010841420f565400b003943c54110118804144143e685002801100c044040362108010030b2201c2600203101421101060700c2c001d4031080140b022403070258110b4041d580003d901404281c08032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 411746897 1250 411745647 411745667
    0x30b1b0d15030206042c160302090f03010c05040303080901050c030a0b0a050a1404150312080711030f0406110c0109060c02010201021317070b03060a0608091e01020910020111040303 80
    0x1c4861480041d41d01e60001c0c1c29a40280e019000d503950707504c180b80701215102085011120441114000362820344480a16841d0108070101803603400b040c01020303919030303403144109404094000c10001d60b5800001d056500207200031030019442c0e0000421040c03041c010103008030b0000c031405040d92100da08183c0984003944003541c200c00e01083c0001c241e6114041c550083c00305020702c600300c0190405000944150074042d042100f1000020400070303d100c41c0081c20185a450038030b20700e8861324400c4640c90b02c0d02072013201134800400c441d088103000303800406c1180d4142e224104814003030801c140d20780000e501d105002c86d0204004100c840c0c020500820038038070510006141ca030414001c842801c016400031035801d003c20032800e40080c0c041081d84090100c8598940c1180b8200c0001080c910080c0600020080401e001c100031410070809102080c4c10052107200001c600c0b88024004d400401e0b00c07038400c6402038441c00d0118010311900c1e580035143ca070514038003411510151400542c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 411748147 1250 411746897 411746921
    0x5041e03020a0320011409070605030c04140a03050102030109152705100506160303050f0c04051903050109031d062118070303030e12030603060f040201020c03031201030b1b0d 77
    0x6400c11101c60040a11032403107006c04460700c80b126070400d004100e192800c80c2d00600140907081083c4500108500f0540d030464869480c140c0b0381301e0092020440359209607000034080d40c0044004100301c2215000754040045080c2521100d640e600e03c0074040500d940404c000320403210403083e01c08034094000360391144268071440c09155a49000c1011540490460b582c280d8048004604056250003156000b1108504182550500381d070300c4201e0744100d10881e841340170180c2c44040d030046503410340001182c0100c002c0101c4801801c0c080e00600b04581001174005c040704003034440c0d01c0c0c4802034440044481544405880151040e0301d03500030061711048030b0782c0d01201d45107083c40c0300b001900050762027580c02049107071595084500d001a4071440324074051040c4100022a01d00150700369201100c660580d6841d00c860005030305260024075242c0d010f010008507540300b0130307041220034100c3c2c0c468074940e0031960780d02040c448044096942c0700903d41c07003003094001c001219000840900c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 411749397 1250 411748147 411748187
    0x30106080a0c0203220e0a0b0108010b07210e040e071202060706150f090f050610120b04020c0d08090a0305070b2d0609092118030d0305041e03020a03 66
    0x22070802c1d00101c1030240c000045160305e0883c02d2002d403901c200000d40007103070b4140500034001e44c60b001911410701402041c00018004c44d011003032012240365088160348440307111850140c0e032040206148000001a4010380c200988494450400646141140c4042d010f04003820a66420820541c0c00450151080f98a5a15040c0300108406030b03800200002a01511414604111842650405601080898607003010051a40c440d8680c0041945091420300110416801640001c0c01203101c42900300c1e2022441041d48040000d5001e0303c40306a0301c0f0b44100e550340000e400d9413001000401070002d5028003014000664031101d50750400c0c00c4005512503650a440110450300390603040103280d40a000500c0b40030b04000c252241c00c0345004010b86508000811100d0002c800e594040c180014002000750107440b041401c001d000d44001e041d0b0740c0100030707514010702030b11007590300b0f4594014140303003860940d2094a840182586c9071300904102c041940702501c1c651500980511185 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 411750647 1250 411749397 411749407
    0xd02090105010e1f030504020915150d1506180f12060506010c0b0f01030209160906140d0f020a18030c052403040b011502150f0c07150605040b06030106080a0c0203 72
    0x4e07081504019540e1003a03400040c00e14140c010850340c002d014040494488040c6d10300d080e5621784030915122040002030241e510a031034002a0000d107030f900d61120408115403000300c0d88603030226040d203070707031b0000c2802e130301034545070005009109170034401c01c140c20100c242c100d80081c650f5000a07a0080c4141030800600740700c0c0e207404030425811100d510b9501c10900040c0304514101c0181604814588070300c40e484501e081c40030f031245103070380209000e02c000209080d1f000d91390141107904911148000f8050710741480248400f941007441400041040201340d0101180700b1410b034012260080d00d420301c00f80c0f0305024003407501001c3c0c40e00784440d545c0091408242e0303900401507000ba4415546045958034003003c0215488010104900319000258080038071003910080f9600700101c00041c591549a0700c151054a21900c18028105100385801400c240055404402100c0096905000c0c030b054050800c4400c1c4000d008407000b14620b00c021640c405207590048000420070300481e4500f03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 411751897 1250 411750647 411750679
    0x6141201140411120405010c081303081b07051c110304030f0501110c2a03031b0a020a0e010806010504020a08010e191e1109100809100f0501090b0d02090105010e 71
    0x55010305806454100304c03c00b030004004c1d09210307500102c40b00b407030300500c58140b9140c0c1040400c280900501080225004618003a0000082510303103803d0654070350307448105207070040d2240400040c03c040240c0c10541d111500c0e00906803110034858041c042c41c0b4060856944441180c0204029112990f8908000355011641402011420712102c0284010284c54840300c0c0c10302c807060040d01c604c0c1800341c8210340944002003510b640c9401200801007442030741e8625882c0c04e860410295000d0f07960b1a000034030003200c2200a050341c030500300b41c90702d40ea00c80c403d1000740c1c0300342180c000004070300310f00400c495000c0c0500300c5c0d000000400f00d1035450036215544800c1d1503845003154001c0b000f0740c10404c1c04001a01c1040401c02c880c40049080c40a00f1b00040e8000c51071180c0302050045100015601c0c01c818813142c44080a040e0b070805c100740c42e42d00528000e0a0074007031615403525140303488000d854521407240816078010007a807c0341e800c010044885040d038658a54102182c03105103452 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 411753147 1250 411751897 411751931
    0x8040e010b0d2306040f0f050a0c09080705060f0903160303110d0801121e05010510050f0301020c0715030f090f110d0b0a0b0a09090507061412011404 66
    0x340070a00c41c10703850b12910001d5808071a410064100e001020038585481001010f030740c01d5102c0c0b401c8a00040c1c015982001401078412400d0208185151104010340b4481d268480d9560f000700c1d82c0e541c2020b03034869211079580c3c8501d0107041d138801401e02907107400045600082002e214082d0030307101a1040e00c1da4030388040c5140c0d001140825070000114014010400194000c9000c44c41d00d1810340d40342c50359000030035200780005006100003a02803100310b003c074454003101c60b82c000020400c519244400c0e10241009000b003e108208920071050186414000d50b41c00110800c0a0904285010741480d40c900d03407500c00d0f5003803507216007190f00c0c607402900c0b42d50100c034051000030340e41c408245400b0040b4080c4a070714511400c00544080041040210fa15502c43d00002d80090064940300c00181c516600354032420300170f41040715610800002103040c20894040da20b820300c138030b1041404002180180c040140c48098040c0c01080711000138600a44c8564010b000055001c8816a43c800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 411754397 1250 411753147 411753149
    0x507090803030a09060c0e1f0c1502092d010f2f0706020304030f0b0403050409090503180109150c08070c12030e03011b08090f0319090f0506030c0708040e01 69
    0x240b80d5503a800e01c013440300a0207508040c81580c034010f2032a4601c500004d001400d403c4030040324440b009441c3c40114003905180403615002903000485180c200602ca02a5108100340e5014840d42900150309411924a16010003003942c01001e00199370001118809840104502044904030200c480d100d402c54941141003a0343c2e42c0d40c03041d02008080e20b440c6c04519441001154010042003000c52184e00c680c4800542c08418020702c2d88840c182103c0074052501700072070b180e1600744d0f00b50402800000414540103e0380340d151031440484010f40d00301c07040e07101e2001351010300e4500e440b08500c1038407484011440382c501c4e18202041d5031030740da000304501d8205902d403107100404581070640240301d0702243e40044000f40540000040035202d0f044000340068240034040003c584441014072002844c510300300212504d640c444d12614003038080a036800c20101d0554400407610301d13100b0f080e88050b1180038101900d141c480b0b0114480701c0d84000015184c3d60000d11000c100c80c0741c040110342c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 411755647 1250 411754397 411754411
    0x40c060e040204060c081e0d0c03051f15030f021207030c080415090609052d061504020306240d2f030402060408070e10080c010903110102030418050103050609060403050d050709080303 81
    0x71071103801c10003e40bc45034003900100040c08100c0401071200b034502d8041c029203080b5140341e00d85400c0c451066000e0125044c101a03903600100300c051031035103020405072080010b690b0031702440ca8401c00c241d451a10558010b4070f08800a45102120b4515030480700c112489110005901017442c1c698500342044a1111400703c5080e12884a0114100120700072004020001e8400c50404d0070744080e80c0111551020f020315004000501c1a075602100c2c140c5802080420742860f40f0b242c0d071110805c1e44018940074032685840f20740346880c1070f0102d20010030390140c000100d401d20129154080d64100030401c80c1d004500b040301060404091118200401c60b4181d1100c0c1030400204003400783c0156044001c16038452000c01540c0d030380c001601400c8940041100d186500590b004034110310858221613081d05454a04280c0c151541d4081812240180184c42c01c980391800501c2d25044180e0700074000410601108100d4141c3e40d2050360080c20604120b04c105550750f034078a00759001100d040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 411756897 1250 411755647 411755651
    0x3080c031801020d020c10121d0709020a0c020f040908040803120f0601020a02090a1104060804021801030c0e130609030f0306080609030a1115040c060e040204060c081e0d 75
    0x200400103030a51a0700c20341c0024005002c1d5040780c020025544c26102034084d200d03000a1580705400c601400d605a002183c0c90803e121030414400095000c69004e4520b0b074251044020015000c4c44607c2a650600034540d101c407500400b9800f0046c41504608909902c45d684032008000100360340001c1c0010600c000c0035544540110381c1a032170256000f00841c498000c1c1d0000c00900e60381c08141103414603030440d222041510344100c2c1030001c0c4070a0001011001000030081400d580052020380706601c2110004c104d62081c06040320300600a1200500950004005000007800701c0f05d03281e0f109188400d5a00741c16080e4880354180c50f2803690236000700c0d2400c8903049500e070f89402100082e200a900030012400c0003240703143d40c1d00c42d894042d02040043e0020150300401440180880c1c80341c0700019045040604001c17191a1551103440080f406c440c2c652146801c1a001303071422181075071100ea0a14005440d40012944144524a002107803001c0c042c2500c50580060140c1c2c0d81c040c400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 411758147 1250 411756897 411756907
    0xb04061502070504060311040218030d02010b190e0c03150406030303060303110a0206031b1b0d020f01140604092406140d020904060e150405031c0e0a0602030c0403080c03 75
    0x1909115050300b1442c012802c01c2c00601c04141042020f47d8149000d4500517910540c581c0c18000344030400359151f0b07044c01154450300b43c4a5054024815a0808440da15000300c0c0c03090010000300c0c02e9201c1d0071080d80020001460300700d4420f015541c04903100c0040ba02c41000b001c00501221801e81003280801d5072030405000b8981c3c001d03d980010a4054010201d1045540002d80da0f80002004100d0007204040e21004500040b130650f0000c00c5a0f11090554044484500e600c88805611100040c0700d0b01d5030b00084403005010701510300480100007175480d00c1d031800340009800c031010251a07018049085106040e02207214108070b5072062400200c203414807882c84071402300f1154040c0f10741c141c3c10414015035194a03aa40d009607010750000345070207054a00c14203001512040309074050b080d50401052080101c0180700c1d280010007052050080d0b81e0844c000c498148000c00c510750300180d12080001c0c895401560407640b840e81c0c4500300303a920350b070f8500107622907100b0500d60741010030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 411759397 1250 411758147 411758189
    0x1120f0506071806020c0d02041a0a030804090b0a0e06131b0305040c09020405060313170706090506340908010903090f3017070311070b0a02070303030f0b0406 70
    0x10004060704c4544080c0042c2c44401000038201500d8000c0648115520381a0b403000d4207041d5141000e0302c001802c0c2e0690346580342041000340c2c001e441564019810300404c1c80c00c91419400d40c00c2035400480444007991100c0d0300f44080d080405000700421503545290754809000c0b4000700c40814190b99010400b458546410400c05240f5400481028014001070003144d480501760395100345943c0754001100d40c50f04080c218907c5540031940d02c0310f00022048207000d0f0320f03003080e0049401803080320001e460751901440c051201c1106000b80410034078484a030f0b000900103582d180703e40b6150482506071100c10450854900f0801107001c55512102042052000204400140100c0c0744500711001d000341442c1a02208010903c0200c94034414007081000d10700401c0d40344c01003041d1440d213500c02450098101ca4000510308046d02c40c41c100000d080812400f101c0c0001c2c1c41d5809881080e10315078080c2c000e85401c0c10300c1c030481d54407455a00100d0b11544910b03002000c540d1020b114030701d0011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 411760647 1250 411759397 411759437
    0x130c090501020d0522090e1b03060105011e02100515091b0f0c01140109020d1401030203030a0c0201020c06030705030412020c0609090424020405100e030601120f050607 74
    0x203804603055401480b074007000c00d0340040558941c5c2c810042e40c9280c800b02100304d5030340a5195088109401d290544400d815240000e0700d02c0a1000a0007164100d81040100760381e4030b00900c9180d002400d02100030b1840d07080d0f403421214150090045a90384a0200e120205481045821301c4640108191219451070311001490300a07040850141c1e0141e041440400113100d00c10402205001c00a100450100d09510501c019040101000d05e6540c480041d100039501800880d542c603410704c005101e400180451090480b075008000314a042c490200a81c0c6444a4804c16410350003805414000b5464150045208010a94400340d8a2605181881e903d400310f07040c1c4011548855900307802502c400c4202d07a0b030f9035130884054240756198170b88221640741e50000e4558000359000001c06a02d999000740054500440c1c07083c1c2440d240190440344030b0802400729605620103001003242d03203044604030800038012040c5020001003615003e141801c1510800b00080400c9005043c4010710 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 411761897 1250 411760647 411760649
    0x30b070e09060a0e09100f091205090102070603110903070803070c06020616201906050603010b0904020d05031e03070207061427150d050703140403120b130c09 70
    0x12502140745003040d10100386181000d0040c08440000d00c0040f8907510010007401e69850706044040c403810400160010150500b000c04540701c0350060b402e4540306010710706855040406a0061105600c2c240084000c5c15001c0320f24515801e003002065070b252000e011840c06409524010355a0320280c0c03421886d104c1003a8000b4003150450000d2000041d801c004560000249180031512617403880c442400c0d00b0300da034a00c184244074034101c40c4890350300010700340c40c1503000f20700810040e501d9006150aa44588144540c040c8400c2c0c00280180f4000c482d403075116016000b180e080c8248a0280d81e40b040c9981c14052140e94003204200c84c0a504010702e1010342850b25008120a0021000d86081d002e00c0c00382510820041d40d4010390160310f881c1c080a840350003800e400b641340581030078041c9507016807000200c2e039090000051640d070103406403000148000c40d12002c03a07a00d43d10f0484028207110100300384a07031289100e010655032881003400b03507801110009004c4000310005080c000c00b03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 411763147 1250 411761897 411761899
    0xe150703021308031b032a2802120c060a1110050103150e010209011b03170c12090d090510030b04050f0105030f0604020a06030e0304090608010c0f020c03060c0919030b070e 76
    0x1008080449403021080c400029240800c003403542c0c03003c903440e0741401c01d8246e0700420050a419840d0808d00845480d031708050007a13a40389c090740080740c1481d40721005004d04d1508800308000c22145588142c01c0c1c0403c1e280503030141c403403401e1001c500c2020ba440a81c0b0540388c4110810285240a44a105141050f081100214074140d47c40c00007a0480f1203ca28003215a421181d41006060040305030f1001d5071110215403049103030030040d400300b54000514110443c0c1424001a04030180002c2a440c001c240f600e130365031064a01000c0142d02284905103e08042e01d07041c40da901030f100c501406000c1c440d41c4003105220360400b024140380c071854a010030030683c080d00c2440b0240e2a445c410000340c46191601091180d06659020715612550b8410086680780c07170000210380b8810342c0300c075030200782c517903a0004000503900c401c903a652946a21540d040d002400442e00c400c1c100b10040012503c0542400a9501c403880c100842110a520568144004508008950354010b12550400d84 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 411764397 1250 411763147 411763153
    0x9060f1a04051503060612040308191103010b0a0212030420030d0806041808070605040c0b03091f06030f03081f030b01210f14100e150703021308031b 66
    0x220b00700010340c0503041d8011800d40c000000000c244191203260842d509948460400165410545002001c03880110340d003190010f03034007040b9130411a05018850760340701c4805620782140d0030096420241d42c00803000b141544110b2500b46402c0541c140910701c581c1c0524806032401094a51a1440300581c6012074485d412010f0810305003900310381e02c160080c0090701c000402601c400121a131000f03c0d21800b07044143d0100740ca02c100308240e04150712543c441d0741c40000c459076803000038205000c1a80c513050690001c10300d132070341e90301004c0f01108410b10500f0081801075403902e401c1450301441c4c00c16070010f0130440400003003164000b000310500d04200700583c0319914507215044102410f0044a5248210b100380c41c4046042d4130142480ca50451800381e9014200d28050103440c00038015828140182c15505288e4825403080d8400079100c4405418182401d80340307490a054000c3c55081419424092440c942044c000004080c01080004507692805c100b04950101803c1440320401c0d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 411765647 1250 411764397 411764399
    0x13080a1709031b041509061a120406050a0b0a120b0711030a03151e0303090605030f06010c0314030901020c07050d02150304060f09030f1106010e07051309060f1a04 72
    0x51000140300105200c415542100f0025000008001d02640e10301030745080074124001c94290304c0759011508441011030b00007405003a03948422485c0c050051044200c030603420000d40841d4082e00219800050210006403901400002461105e0580c22004008a02c0e85400040201e030b4812140c2143c002c0c10890020101049455900c1c80742c403c074201013607221120340c103114200d075044c50040e003a07a110070100d0282d1003404409012403440b00341c000580c500000034a8030f0051044902540c42402640034543d140401900c10b070540c44012020000e10307100c144202049540035601400003000056a5030035880b28042c90260140c02c094802c0c00c1040c01080181e40380c0011181c5481034501440d00c0781d6441c20404010302c0c0014225102c030b0309040074101015071000c030304290b100240d02c4450780c08910b01401540c034002405111000c9030b07040c0104507032a02030000b80141210100020008a882c1c513a1101603070096407044d14403000d00300003446183d03100c9600418040915056034201 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 411766897 1250 411765647 411765649
    0x601050312130905090a031b03080a09050c091503070506090619120204090510060c0c2601140f240f06040801050403020604110307030b040b090313080a1709 69
    0x4408090207900300c0c400c0042c003140e184012040590050908800c200f2407442c262503800e44552001504038002204960000005071318080304918a40d01a5a29142551a029000020000700d00c042e100c0b807060f01000b02103551008802132092100c01008000610200d00f41880c00c0e030187c001a109000030b100e03046640c3c44c0d501c25100d0b119000c42c3e424109814584080da00b01101640c05103800c0d00018010404406d2500034a00030702003103c000b95510354a860807500c255510800074401d1301000e108128070801d5415242454000e00c80c103070415840710310800e08607014804165540961002000b50103414404465031062001d0a0440031643c00c41a81c4c14a42d842e858aa00c20850ac1c100341b402034030b0354025030b805401540000c128506007410041d41d240702c02c07034086900c40c1070350313004009a0401007501c00490b0b40c8100345ca406030725565650048ca19008240e2141c030710050018040741200310741c2c03180040000102804103032046040c41c2c0c810b01112055200d21003410010800b603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 411768147 1250 411766897 411766903
    0x50f010c3c05040608060d02030d1d0406081c03020901020312190f0b0907110c060904200705010b060304110d03143609010302120a0510020a080906010503 68
    0x1400e14460084508281d0030000d00410068008080d0141601c5410110070981c0120081041e601c039621402aa50354031020049500d070f040000035050b80002c0211a0b506000e000c076a420f500307641c8103c09004025a020404640c01c90380718044650045c00031115040001e40c00e40f412010701d140961520750b030080041e54038070404180d03200030b00c01c40b40010080c400071221404c2c0f110030f076141444150050b101c0100a05240101a8401e1309400041500c843c013910000e907030f406030031000c0c140407800700c420000c5075046a01c0e61508149c03030307000e20740300303050340500c08a40400010041034480c0705a05060b0308441c40500668000d94041007800003148031007a0054100c402103a2041c680c01c4945402ca84140b06628a030f07040c110003103159840c0f054840e030300c3d0b42c40d030105031480b164070644146128840302030300380195040402d110050015042c003a032040811001003003207482c054456035030207150101d46285013954560210350040e4070b80c2c3c840c5619820943e81030080600e07504040019807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 411769397 1250 411768147 411768167
    0x60806060d1401020d0207030302070605150102100c02010e0307030903230c0904030507020406060906020d140d020304031b05060103031106100e06211011040b040603020d0207050316050f010c 84
    0x220502d032020390300281c00d8003501201d00550030410705644840c118a8080c010750813032041151011b0400300044d543c10805410f505031200c050780200600841040c05c1c1c4020101d400300d4108554860242c06500f000400007880349620940d20b5420517865401e01030351806c450382c50601c81d40b03490503a00c0f09003080002e8058042d042101c85c41d04944030743c0b40035215440741340002908981803c6c80060300d190017189050403110181c00360f40723500c01140c0c0c0460703024030340b4039140760000d809200c0406d59010560145500c03900c00e0609050700001075446861035240b00e0380031902c03940030200510400d58040041d03030921038103800405541c02d003208406810701c084d0180700001c8015100142c4030303540e41c2059895643c4043c0c00071030064030207c0001e807a40038070104d0805050404041d00445101d000458084032010900c190030f050030b00d4421130113503114400d06480c0c950240504004200184000d00c88426a00c802000d00c00c09071a06505104c0c6410b80b089540c0d1424900e007901c240c0194240c3c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 411770647 1250 411769397 411769403
    0x1061403070c02010f09050d050c031b010206150604050306041103122b0f090c03020f030d0212210f04060f18030c021f050315040504020a030312110a03060504060806060d 75
    0x800050a0004460341800790344080c2e400558603a61209205000c0ad0030b0a10b072906905940030300d07580000d5451510201c0e40143e00607440301d00020b03d40c4c10f080049031001d000043c40249080d5680f000245800e100349d80554084100703170aa090b0b0780c6010030080d07d10faa00f40d40040d00b00008203181c120540000f241030242c030391600c40c107003000d04da895206420301c03039a62608000d40d98150030f1241050040e030004078029056601d4171070752460300042d614440406030780204810314424020700c0803034020b01031408003410441c004100404480c84400d11880100c101c07900b4a19003414036900b5500130a10780c0b00190f2403c0c4840d80e011907100b100240c120f405050803c161101c0344045484810f9129030500f410f5058004018070760350200055010342c1b8041c00c0c1d03242c8455554104802c603007096400a601200d000f40030400607000d0904540c2140703120750002451342c0ca0544d01d221170f07485440846c00080c0d43d220180300301d1800e07128410160400e0001000249801008100000c1143e070f405 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 411771897 1250 411770647 411770657
    0x6150108071b06020c030403111509010c03020f241602030a1404150e2b150221090f01060e0a020c0a0501020d02040e060108040f03082d01061403070c0201 68
    0xc04100454502e8800b00c0d580c015821940d400c41e8a4101d500c9030050300084804054500d00950580b400d201d070300c20060781c2034002c9841c1c456510015258400035035812015401000105078240100b8415020188400070b09410b01803000b08001442c00402404001260040762401040320360000a0310840701f441d0501e9544254281d003000803a000d02d600c9241401c82e9004a04d0050381d125440b0201c4c410b0590b44886007411240c2035102c060507441fa82100c0300c001d202000049040d103c0081000b56911800625007850505403800c007021412010304030708200380c184080c0c07010400914080c5e00d10803000f0464a401d013a064485450090300702e803041030b00482c44903111001409401841603000000710343d00c1800d1201080607410902c10020415200d00c0040c550794011002244500d0303004003148a8170702c803a139007929607000c0502144041c0d01ea54481c0c12140d8441c4410b04080400c650440c251503250000081c8807491000850300005030510501c503141d0340081d8194a003d6090902c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 411773147 1250 411771897 411771917
    0x305070c170a020c030a05030f030606040302030129101b05070e100302010e01110607120b0303070813090902060a051c050a2a09050d0203010b10110615010807 70
    0x8111280d03015003902810312222103604055078000d100040058020680070f440368100088201505c0744074004010b01160800c20240e0b50b8603002c04000d50b4400740c010310003420b09440b034000c01d086a0792510301e650640141d0307180c402c1c044555801040c20600c200c400402c2d00440c0207009100720350140101c1d220f000744940c10010850103001e80f03009004144801c1e4503038607103910865051442440301303a010816407070103141d59502c5964148000c19108004109603110b44404444041000726122002030342d802900100d44d0701071000348000c2e400f46003803903181c0360500036858517403003141c1c41903000c203180850031001600d407801510803580d4107091064840c001d07000c00c04013003080311845655152801c010404c842c0d580d03911007603200244800c244458400c499060640c4c0d09032058203030216030220010085490101d0346003080b03d00c00340010906d65110000714000801d00b9584d9008100400c0040101c03c47c00c01006900c50903181d031515010002d200060031641e0080c2451080000c5240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 411774397 1250 411773147 411773161
    0x3100528021204050706090807060813030905030f030a03050112030e06031009060b03041b050f1c1b080d050f03040816022e020313091e06080a060c03050f01060305 72
    0x1c1642c0c415691022088014985490510345543c10b5004101c045a204000460316801c00a02d42e030a0b5581034403000c25580b40c02089102a900c41c680803410000005004100390b1010f004040801841500131511020b404401600342c59050b002000d11425076001032020aa1114a07208158000c0d1180c41c2d0725105d0f003260700e80a4280781c11050f545414007400056840f03260000f548141d005654603003400c100703003000c1d0f1850701070b40c80b42c1c076805003c44170400b44914260f000d42d103404204c00f944000780c071926a01d0324450100150071003424003040c0c00400000d0b83c184240d41240d13005203081407408200d0081084c481c00064005007a030180440e1010960401810884200303400070700040a10f25100408003e880005420840342252003d10040313080c00002560540602a090400550b06000b4000010b00c4051010810303d030421103100b140440078442c12000c3c018100142150b6a2282002425100d41d02502410140b601d401c000356200011320700e07815540f40c0d02d8042429203d0303103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 411775647 1250 411774397 411774401
    0xf05121314011401140609010e060a02031b0c12120313020a031a070f030905190c0b0a09060e0604032a0915031a0c1c1e02030603100528 60
    0x180003001d55880e002d042d108403548045442c2c104c03095107214800c00024201801401e008007607580c3c2c042035060a80038000e1400d800503003102c510a104481c10111055200f210020081040c0c0c5002e800100302c4259a003040d104007501d8000c3c0d5401070010304550000d5554a100c0107007118195462044010119903a20780c6a0005640044800054004d6182e2440703583d201561340380046264002d0820155000e070203109400382c0c200000c1c0c1f1001081000c04041c2444004003141c10210182d004185201010041c2c40110400e659a00ca030b81e0030840040d2800c030f004044244201000c0c4010000500b004901011656881c0345800000011008011000c141604a07801c1c55003801ca40803003403030060b046181181d01a034980c02d110f0700c04c0303110194034030070585200303c1c013407010841c5d8484800741880c07140311000702c443d000a10281c08102440910242e03031454160640000030300001c0c0c9020000304000c00d06103001005542405280c0c007044a84880e8100c00502c45c054845440020396 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 411776897 1250 411775647 411775673
    0x1080912160c0b0307090807140103050604060e0c0d0f02030f0c090d0209010b120f0c22030203030a080a0c0e01020c0103090227040b0f090a020111160602030a0f051213 74
    0x2000c0807100ba4441c400c07420036801c00c444c01e03030000340c4c071100008042200007061811258202854980d94144d44011006003d005054681194440000040e8406d5440c04503208a6071000c0c200d80320501142100d095581d040f4a0303058440c014020312a0859080075800d811402c200722855440d01480d010690030140c45c0c1d0007070352003c800d000006404c880c400c02080342000c80075200c58103070303100d501c4034880c0724007694402d50401d41444540c4a000d5400b005250324440e41d54000b45296503580001d1031640902001000500d0480c14007c00c0d45003400386901d0f000b103c0c140460410071000000759074040780f080f401d04160301e840c400420b64844510040503040883c00b4103d18981c0740107101a00c00007901c04135000381788a070014011072030707102406021354a0000603024034060f0350011503800c0c89801071040c1c0c0b0300440c0d00304040e0300400c001d1080205201d8015648401d50a02c01824900000c182102481002c00208070f02903840c40c00a6440380c1c2c000c1131000620580d003081541e1a6403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 411778147 1250 411776897 411776903
    0xb07050f06090f010c1403060103020903071203051b011b0518060304140c031504060908040801020a030b150a170a0905150f0c070f060905030c070906050a050108091216 74
    0x105402c1c484260b034042242c3c081c601400d8020b000805840301e0890303031b006144600100c5450144040307080c0d507102e40c008106a01000b01298941c0342c6072647c4804c420741c56401200031030301c0010190201c0c4021018011480b0850008002c2400d07c801c40141d0b0000000106003001400902e881036603058020341c218041025003003076280d1410b49070500d100307445846000c065110b80100518145000154041c0c0c14500715402e880350749807640c9000240c0300700341c01200c600b0001e010225060030244050150406556804079001c19104240000f46c0c03040000008000d804204003814503030012821000c0381e10700600e4262550b41c00c001480141098030000302a0300030108030301e014400491000e40988124400d0002075194050b083c610741c460950003d00a4070f406016030302051141d4020070303140d805642601d250071001070380300d42000f005400c6148a22350340c0d40240828201007040001030725081c24003203250b00340441440e503550107402c1c60100451000400d0400300080540d0308240307582c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 411779397 1250 411778147 411778153
    0x5060a09060b040828062703210623030705030a030c060b03011b0e03070512010e061803090d05070f09020301062c100516060605030f0d090b07050f 65
    0x20302e070502c42856038018407980c030440c410020f4070000c402c030324520903d981000103a010075010b0705a80741c1010344000e154050040038070990100102c0903400c0e034803d05503c00e0b60351655442c1c0c4c1210b016850540c1d489101400c0e0f01c0c6c9901400848480714511142460900003081486071600c0004d103010f0f4650081d0380c144c0903411491081580083c4400046403260109000806440041c1403c0f41e031560030070036100c40120544510303c1c0c021141045140340146c292101e064031040070800411040d40f114115a544410748200c00c402400420b81046803581080154194509116a00d000380100544104000b0f18040104401040004020101c8016900c500355a40c00c2c424000d400c24032a410100f4401e030110f02044001c0f40001440300940d403c0d01070742c42c03400ca007409080c903e00403000003444010048a505100d0b40360340010320510642010a8082c1000141800c111a09070b211000c2d07441f00c5407060071240c000d50070900b41c03200d41854079109d0310641000c0c0d2a005900c04000d0706c0380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 411780647 1250 411779397 411779399
    0x705060912190f150c051e0c07080f010b010c02060405100203070510060314030909222123040608070e0d050105090708150c0703030902090a05060f060405011205060a0906 75
    0x8501d282411000d005840281d0481110a0a441903440c4030085c1000900d01700502803600f101800704151518800042074202401707000001d1502010b80c00c42c55595216413000c0d401540240a2403180038001e190940f03c0551940c042103050241c1c0c040c030352040c01c03c40742003039240c0c1c802c009136034240b42c0110848074000b111040c150001d2105020170b4a403a01420aa0704100350b0000407503c5040e000f8103c000143e448100c0d0043c0c092510581e1541110640e0341c0d0b2002c10b09400b05280074203451152046119450500940710f42e19040c04040c1078160320348a000040e02d8501914201d94040c14a100326503500c1d5021203883d4803d8052076800003a201420381401030552100d072103244c1c41011510165147c0c4201580c138004045803003050b401010000f105081c4140141a090788a4200499803a10342d90003d004514110b480414495032603041008910f07202108040140d415503c09241504080000f842d241c00ca01c0b14070035070f0351680c01240c8251590341c084001090850000c00c40f072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 411781897 1250 411780647 411780653
    0x50301140415230d08070b04031116080c1002030403060207060f020c030a090602120901110c030303041a0114130c090510030b03010e030339030f060111070506091219 73
    0x164070144605011003e0801c0086a80c01c1402d589240d45400c4207010b400d204840d0740b81c84008030300400032030030028400a0342e00e0040f4100484006c04040390142075005044c0006103141400d810411341c420b1002c404094200c2e50040110f8003526088800982d40300c0f1310741021005451360746100041140b00051100f0041d0000c8080c00300b1106a544018005641d040e01b01e03908d070000d90b11100042002c00c2100c520b176000d80070f80c10340b0b1901c1c0700a88180804107400a42150011a82611010300d00d00100d404040b102030143d0240102902100f6451b5180300416200d0740780a02400c1c0155440442c050318901604c860001023400410b00d07408000c8010f0003e01402d041c005c103034000d42c00c100d0764a03081600401900e01c5a070640c0040584007190286175440b105034030250503c1c00300e0700046e460000c01e4840c02503209030883e200701c40a500306080010700000c10130300c86c0d40c8580c00c04c0006128556540046494025003240c0403510040c1960803a800e1800410340038414101c460003031020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 411783147 1250 411781897 411781919
    0xa050c12190c170a030b03011a0a080a0507090b1c0507060201150b0706022808070e03030307020705041109040542090a060302090f042001050301140415 67
    0xc0d40303900600c5941c4421800400b80c91400624100038a00c449150b00d000ea60fa40107805405038103e0703458003160790069003012a00f180e81000340b04200a025040e11412170a2581d5a400281181c1009000c60004d07031b1a06500d1b14424080c491410b6114600034180e50303501e6508448805100d510745103250354602d01070b0340d00c500600c11a8059424000700c050300c4e00c08680031078111621510003619110701c581d1040700035407203400340d0341d00c0c000c4144c03a2181038020300f5485441a1240c1c1c44030603050802190140c8526100103005210354803c10400034040d9000c1881e8088540035100410559009002c00c08103001d500c2c0179a8001c0e1a244c00c100680040207500c0880c2844021040100e20109405484020700c2c0b500d000581d1035461041c100e1420300349003580e8864010b007400525580c482c0d0014003400f8080d40c0c0c080b003043c8000300388004d0085080010381540490403000b071070b081142c03001030481c0c00140300ea40000d5401504032125511507030044540054102c092400d07003070300c2d0390080c0b813 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 411784397 1250 411783147 411783157
    0x81203070e100c1a0f07050901120507090b070f1502030702250b0c01020d0c0c030f0f1202030a290a030320060c041d0f0a05040204060f080a050c1005040302060a050c12 74
    0x5d910320045c00811322690203030f000c6030507d81c4103a43d44a01c080358480464040d0402400600402000700d0001942d0203540c00542419440f0b002c1a001c2245213003407001d0b014040c0303030391501440d10400c1440b0700070360009855621275912003554032440a82d1501c06401c440190f2000ca0345010014603150314400c103600910201c2c80308141001181403500c0100c60401180d2401800b140c54815000075440c05942d10031100034403441c01d00c929403030b0340740f2610580c1c00503140425601d8035080b84c18031000120300c81d4039020f4545200844c02580d0400040c903030f504503200c0542440011200300d002084c0320309038000c42c0300300b03c011141d003402d01c14640580341e4090b2080541141c465000d1200e0740d440b0700c031b8240c007815841502e04015100c2401c004010440540101d80c0f0540d02d900000d00d41d240c0c00d02480c02420100f016101390b5100c0d0400a040a0030000800d10522a00c085203d0050300482501d05581d010744405c3d40740c4d4001d001c00d4400f8400c0c800e0080300c030b2003240304041240301c41000502c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 411785647 1250 411784397 411784411
    0xa140f10050c070f050102370f110414061e0301020a1e030c050d1d0a0b07031a0d030e0d061a010906170a0b01090b0d06081203070e100c1a 61
    0x768103d40c0e1048000320310002405010300603040702c020f601c201c44100c9419000c85c1100400300d4281d125401d10b80da0003981c41c8404a9810300010400414030070820007140c0d0054007a41c040c00f03030f008a41403c44441e040242074612400a240600d1044030644482800c0f45070050000c41d80d4110782d00d009090204d5041018482c8111903d041c81c0c0240b090141d240c2c3c0b1071640e2103031402e100b8800360a0b80548a8900149050301a40750188002c035010441608054010390700b141355820700c5034000701a640e502c08101030303420001300d545682d0380395441318481564042c58540c1d183c1c50407600042100d0000340c0060086410314000140c0c00112031180380c0c8030042600e5207062150b54403001c1e20106001d0303030030440505a42001854601c03840e00940d414001c145001c0c7c101640710102c110041d0001c0704002400d41c2e03288001e02520b00100310058591034401d018509524013800f0080c900c0c03605881e42d50089140c1808801007034043d6040c9060305a01040e5030043d90703000e10340c418401710111510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 411786897 1250 411785647 411785653
    0x50907120c080c1c0308130204050f01050906060c0304121103060f01060e010c0506060907050c1203060406080106032f040204170106270908040801090510050f060a140f10050c 77
    0x20f1622072510029100a500d9400a450f4442c403e0303440076655040004c0455025106810320300005a582d445000d02c580c1c001c4942d070001e54100010700c040400300610444c0103450801203d4140300e0004182d0b4200c511204490440018625040c00c40314a02490150148985400e0000d00e10450b2a1541620301964480480c8004240111032508014902410b90781040000c11000c2c285101790079484000c9080035407810311310700310346407400c03900e2a951441c1d50404818015a07150034020b0304d0003020790b040240309003420b546843d0880451030f03c02c1d1030b2480d005050b510070b240104407030b207440c01d80090045407036a5035007001c4480d40c01688080c07a129403801d140400c2c1d804089038205840a658080e0500e04030007c450310000b0500c03c1c1060303410000078000015a00c400340980301c07105204001074040f00c018440d040069070800b600031100700e00001c08010240c3c071040c2d0300c0c40c1120010002c901014030100003064002e2101c0e0060307074000c0305d4011180d15040d00b100052948008000403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 411788147 1250 411786897 411786913
    0xa0c170405120f0d031a0105071721010b0705060601120b031c031b02100f1407020a1205120a2307110f030f0306041d160e09010519050907120c08 64
    0x13045007210b1021484080116080d4880704155220304050603086200e14410301d03c0003500203112100390001d113098010318030004100c641800c2c0762210b1034014500c1c81400785c20310159641d84c64171250001c02c0c0074100004007110a403401010b812610007608064160307050030784c20409443c54041e0410b10003012a00301074686403044045045e103c8006180d9016050680304000503d002d407c4a450015483d40c030f503920044807100c0114007500801040e0001c0107440054a0489803801c0e130a00b8410a01c2810310030411079800c0780700d07000c0c1c1c401ca00001c0021003e5211400c0082c4403a980151140003110300104000c00741c00c60041050450381008640c0d80031202c464250340ea00c0340c5840101d03c55802d102003039050420740c004001c219000c520401594011a8106243c016055400020090803003020004200c03900302141d0803121010080c0312030b00c1c08175000410b12544e000072034603069079400050891202803003260064032509002508802c0b007401c04d014000e0843c000d4108900074400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 411789397 1250 411788147 411788173
    0xa0e1005040b061201090b0d0c090914030a0926100c090f1d0c0405151c0603020306040b150a0801060f08011404080d0b0907030e120a0c170405120f 65
    0x1e4451460031507880c014683c2c20400928047c1480c00c0c12580c11048030800d800008000850300401380903100c40c000350005103814020b0b4140042c1071100d03441c0d0020800d0050996003d10f41c44c0684003040403d45610107981d02c0290b0404040102a4907070041041c0d41c0c035112038a40054002c003101f60f03158400103486281070040e40c2981d21603440d0301c0d451602201080d009031850990310101080910303090070780d20004244223a850f00000c0f801280001000500314440080c2922402c0004200b0403102e82198042035070380d00050000340c501342c00034001500110965664004204010302001c0744150f8601d10540603080600952065001c8010040fa40381030500c0b4882c011891404044850384951b00c030388005a10074909485483d1f1210480f1000d0344410107440d01600c0f00e550001b03082d00c91040c0b03d07030605106610304828008100070400440c2c3c1d00c03241524101d500413403000e80c1d1841609030080944100c0d445a500312902e140395003607810f000f180c58401ea003011400e441d00301460803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 411790647 1250 411789397 411789409
    0x11e031406030622060e06040c0608010b1809151507030908030903120d02090402041706090a0b06040f09021f08090606010906050304030c0c0807150309110f0a0e1005040b 75
    0xa4134048042c0510044440c109211108205103500039400018070703441010b03019091150440d002e0391005003c00b02082800e6001d10040d004200301c0080c07906140d4051901709890b10001d08007071041d84010082140c1e401c006281d04210300000b4040504101d03039107400e200c142c108040a82c0803e042d01c0e000a06e0840c040300302c03000300d00020058858628a07118000441d0048400d0040c09542404201e502d41c56900c01480504a0203144180e940310f11300b0218a0840d00520959141e00441132040010719013403084c54100c1c03402c5601040004103210414000e0205141c081c0d403100040e00403181c00071103d942c0c85144100f40c1e0707481890380c2d90405250b55442040e0b50940c001120010f04002c0d103803066020b160800e00c0303862f10ad2000300d0380342c64070107050b005c0d5000010250400001000303100c030392036081001c0f009142070600942c14181c039501c800251011000e8061094ad400d032600030742d00c0882103800342c0300d4900d01100500b40840b0812441e02c02c0d01a080c0540d14080241c2c1641c50a2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 411791897 1250 411790647 411790651
    0x106230d0b040f0f120507020a05060c100513020303072a180504060204120c170705060712030603210206010501210e0c040207030e0a061b11011e0314060306 69
    0x30070400300d241c0300e5580320702c030403100114160b0703036213000f08810800034600c181c02e416458203030342d580c40e04c600303c50041040071070969022a115400800900300c3c050000f0030075107240c5003a4080040d4a5036001c8645e0448690b0000007541400b00191003020400604000281411040000700308055480c0b82a07102c11401d000f00b1514116840d0034001c50300182c1c00c030320792091040d140503007010742c4c03010507410f51f0850f00300442e1030058042c801d1100c85807901700003500c2a100380c010009a0300d0200400c0b02c40c40740322805005010401108091140240c1002000310741c081c18020001e4a0700306500300041070408070500600a02000142139845044031004c6030300007944960151452800c244001c003c1c0001a40840c02071803980d1540750754034400740012a0094862248601ea103104202400074940c00240500c06070302c1320065800c1d011302c1c141039425404410343d444803c903040141c5d2100d074415100440310780300140094019500d030b0401815209498600f801d50303220442007607200d00003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 411793147 1250 411791897 411791903
    0x30b09070b040b0a090e040803040201020d0203090a0b07172a0a08120901060f0902040305060604050106020d08041109040609021815150c100507120b0a05010815030106230d 76
    0x240301c03d00c2896442c1006241207040b0341003d10620b0740c0c601c0e01c103103c080c04031000d03202c181001c0104020b45d40c045c011410321900e14409103242914034000169001d0b440e01070040d52031000715105042081340c6c0700c010742820480c6c504945a0449044201500f6503c68001c190040303500d0201c0c41d000b030001941c080c05503204070000d040c50843d14242000303d000410100c03640d0b4841c14005401482440c21000ae0000407401698803811414914544070000d0a014055481c20004100c504da002c80d00c1c4607540c0d0b907850705540a4072070741071007854458010756407940041420700f44000c1101e90341c880c001d6a80300703581560301c803a01034a8101071010700f110002c9001d041029103810614002d000c0c0d04c0c44603d40c414260030f2482c40440c1c5464024068200100140d0310800c2c819a207411100044014907140030a2200700034030000708044461910506040c8620480030842c81ca030341519280c0d01d114080c00070030203986c3d02c0001e41e001d076480070001446040981c1c5203440c45d0130028455100160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 411794397 1250 411793147 411793169
    0x8030313020d11043213120923090601021b0405090a0b0f0703060f06140d1b03050601080c090901050607021206100f050a0e06040c021015030b0907 65
    0x144980034400390442d030b000d048404480b9a40f03480341030755403485201c800002c0900b1000a08201c03000c22121000703210310380046140e5510400034800e07034000d20034050035402900b00404181c1400295902000c82d04900104017020440944551000024914410301140d4984407034030348000591f150f100303030820f46c010f10070259454000303400c0541100c0e4000c0800d00c12501c40c440941c4848101c0c90301511303800800c500d00d00500089079814013421000c0e00c250078415035058038084010700324106800380d19032000030100f8440300c00c240d20f038040c22106944c010701c000703078001c0300d20028010300d401c450503804119204045416040f011007a101016030180c020711242e42804200245904030500407a072003c5601512070070b244080c030070b6901030081c00c446040254282641d04180013402c0d0001e9004501584042205825102c03145400003000e5800007454000404102c0c144a1408900b030fa4090800202080c40304200c031424007101d0050752200c0803a00d0782c1c6c0d2140e8840da083e100f0030300001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 411795647 1250 411794397 411794431
    0x6020f01110f2a1f0b04140f1b0703020f070816180603020a0b19081302220213180902090123040f020a0305060406061b081b0d09080303 60
    0x101c004000c0520844203880c450760f0080340d6404152401d920003a0607000919038104011004440f80140414844c0407142805001c0b088070b240000039100074841c1d05440600d101040252070030044600d00400801509561801d0b80e00b0080e5807401c1040154080b4840e00c41c0c00a6601d101250004c1102d04088107428000c0c0b45c81c580c20f0001030702c070300071903201030340d0300400401a0b80f211003080007824034239000e9454041611074410040800780c20310040c0811802000a604040c0c0100d00c4000e0b4101c0d1420180304a12050b01a00784011504804041c4002000074821800000741012207400742c081440d80740c20b1505187c251490002c000303400401e1400140b1001c00c0582c0042c0a032024a5100c1d903081c5104c1002406a5111001c44841c06600080d190b05081c0d25000d030b01d43c084002c0e1410300a0038900b8500810804000c00b20040d903480307104e410801c11104208440300c80071341c0d00c00b1455041c0c1c903a0640d0b03180d8614a8600b8041915000c00041c008000700c181e0f8499800811251145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 411796897 1250 411795647 411795667
    0x90408032e060306031a0f0c18120106210803010b0c19060f0b0d1205030603190b061009060f05070204060302040e15011205031e070c06020f01110f 65
    0x701010500001810078122407000051404405100141440e41c1d01141032851410320310008403e992402058801c0e050070000215150b0072070603003003040d036580a5680e030300e000054000712140d244d100d030340021b00c410741d0401001c0540200b004d60b40c035061201d0810f03888402c05159050601401401c01e5010304c01040880b15650142144044860541d84c401c01c062654400e050709010044468996174072000c01040e0240c424004485000d544030f03002c20b8240d446000c5070b84041e018070300400000200140940e01c0600030500355180605102c240039400b17242180215604640301da000b10030000303200074001e1041a14404035000b64455003810070040c81c1c1103403168045201a40c0190725101c00000603143d900c141101c80300e200d0083c241000c910010650241e2040c1d1090200c54020280c0001055000c03045404a05c881c2403080b050725000c9001c402c4901994601410b50207242c2800075055401050a0f02119200e100820013200c3d49143e10405000c1d03071368402070044092045a180c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 411798147 1250 411796897 411796921
    0x60509030c240c06040302010b040e0c0d0203011e0e0f01050f010603090f080c0f100b10050706060302030105160201051609060e01140c1e070e040f08070b0c0901080609040803 77
    0x41c50b048140e45250882600b218090700381d100140312080755216108010a040d420303c00d510340020111003e0000c03400c196402941e95440d140203070f10440030701002d1411503500b50b20004154200758401c0303a10ac544001c16000030011181075001902911990704030a50061103400c0c4510380400100d07003280d0078607104400170030344180300b111506007110110340852160b0000e40402d00c03c038001803583c1503101c40a20304162011404160322070601c0040c2e0b030b00c0d0f6100c00321603513440074500d81113841d5249400d05e00701901031640f0194055103481d080c8645a07807041112034000705160002e0107a030711707190440c01910b40003c00c0a40050003900080c004103204a10180d581c040500d000c0714030761410b030042101d80c0c0c400f500400c0554025100009900448007040710119031410140001500d42480c201e040c1c200200001c00e10304c12040e00004104014080d541e8890b0008030003400e601d462501545260310000c1c0c11801701d0f00c08000200e107468046126841640c0c0038100f581151100074030004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 411799397 1250 411798147 411798169
    0xe0403050f0f09030f1614010c14030c070e01080a08030601030b03011b12092d0803010602060105041802031b04060e160f05030c0306010c08090303130e01060509030c 73
    0x410040100144000048008080c0000a160108030b0b5910f8a4000805190140181e030a11190700001e50240e01203020141d10f400300c903150a0603845201c1d80780300494040000150082c0484058011043c0c03c0700c0001c041c0c5840000e0030100e5070030350b484900c01c610b002001d01c80c60036268010b078200000102550007440c0c1041d4181030110382001c0520009081d140c0d0301101074140c0c07400350100340c00746a001740504811141400104542217854032640d1001089450b040c0c0d00f01d442d03d444000240e40c0505009a03550400c281039142c0d40c54120003502e603002032042a110314100480c1c1140f04d011503007085221640103000788428441e240003543d20014002280d0b40c840d685030000550b2034112500c082c4940300302c06201401d9056840041c14500c1c0310500300041040c20300810a40c0c10a04085a401000909044000c050703070f80381040b5140301791102e40c0d0b014040401c81c0400560b0303004500c1d0075a81c200724413800e43da0300c944089034217015218420740d041c1d00045081c0300a0030011039081c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 411800647 1250 411799397 411799403
    0x7090b01021b040f0216050105090106050418020d0203030c0708010506090703020a1e0e040e0a06050907210c0b0406030e01060501110c04050604060801110304030908120a031505030d050d0b0a030b010e04 89
    0xd0b0601d481506d5050b040d511000f801e940a94441c420803002103828490350001c0e24040f6000c1000e1b440444520b200c0e0140168001d0250b01100900c0b015942d04006898540c0d2020007241c0b6040d48603520702c3d020f4041624040e010310150404a80058028000d44400e111695501c201c0c528031000071110303c01802c80034030180500c1c9400714607103440c1d40c004c00aa4240300001064403009a2410108a0f54002e2090400c0d0300721100074040840b00c514503081035a0b032500103112003002414480540c2e039507544540c807808400600043c40c107406030860603050050070000c0045503a10001551400035040707070303028903422207280c41d0301514156200a03001100036100190745910b030802c503421106400d0280085030400710820040640c0500d51b80090840400644442040c50620a0381d90241c0c10848080c1a1100c0144120043c4102414024000241102c5948100820144c00c503030040021800184c240302e800310741070500b655940c0450780e220280843d503a2030102c01e8400808060030072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 411801897 1250 411800647 411800651
    0x1113090b01231b240109020f03280513110d052a0303040305010603140304060c030f05091e0420030a15031a010e01051c0b07021e07090b01021b040f 65
    0x2841c6030610800481030701840745540404e000c2005000180c0c01241607200394003090042118444c0d9101c25400d4139002603114046a107003200386074104140900000412a01600e443d0410a0614000fa050003641e80907800104d01056001c0501c103090200341005400380d88400000315000441083c00400aa00b24800c0c4402c12883d4000030304580c0554020340e003e0b0b444103400d0040c0211b15201ca500f40b20888001d502d40b41c50000c010308200d01483c00a0184210607000c400d000d40204101c881c5000b00420a540a1017001f508081716207111032540d00603460a4246020440c0e40c11406d030f03241c2002c01c03940d0b0542d5182c01da08005008000e446500410181e00d000000651210a001da0030f803041e03032a40410742c1801000f07045c0c00f2050b40043c0c4151804200318482c840002d01003540d0b1034200311945c1d2280d40f00c0206074507001d40c00303e6111012451010040c12540d0210b50031081e030b140c4401c144003181c910801240d803602016240075130341590012001c13091030254015406440c1480c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 411803147 1250 411801897 411801937
    0x1302091504020d0204080c060a0e01031806050708011814040803060321030910050415110c0a0b04060605030a0b01091a0d1a01151b061113090b0123 65
    0x4202a604801c20250f08250007040038051188284402d011000d420b55100f41403403c140320040c08000c1c8005018141540e03007000305151105600b200e0072180e08140c052103241084030b0300070401c8401748516465441009000c0d0b401b914940a91000d4100c110811442911642c0b182941c96002800c45d980c5485032000407084180d100300b2180f41e501ea1911401c0c3c482c64005c0c4000d0030110941409400945030608010010b0041648220011103411000401500c1c004056089105035040c0301c541e8401d1201c500104105000e002e44078910803841400100d50f10740034180c0e0345141c0383d402070040a800005012009066121404498040403100e41000c40709020400c040c4e1038070002d45072242000d4075151400301f16403801c0c1c0180140c02d4200024900d142000f0084005900000f0021108080784421304c10950041040e511104800c00d83c0c42d1710411800044898030320581186505021620a6540c018001c0c1d01c46148000030129900403038959a80142c0c2c44210452881011858 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 411804397 1250 411803147 411803149
    0x21807030f2009060d0c080103050d08330303030a0b0f03011a060f070f0c09050f0709050d03090f0b04180e0a1401090b04060e160f1719080307090e13020915 69
    0x90f0710403000e1b65132100104c45d415400d00c1c80c101030b10b0f403120341d09000d141018403842c0d0091081c803a0b101c40c03010580f11700d1040c1e01c070715900e104030220003015454803010041c07000c1074546505c4441801c504441c081402c1c3c9030b0038103140c00e8842803500a1540e0b00c0207540484141040e1004020394855222010f207006070307d940701840c11000600540715008034040600c041c1c030807403041035004a144044062186414207001700440000c1c011035000c4c0d40d40c0307401d4404141c010b85803030020b0048200180d110540301c43c41b900241c1c10500c03420105c210f005640c0c400001844c071801500f404c25002601c01d1408030f40300c4641840410004401c29036944c01c0c0b40d004240c003d01031a014030320810001c6004146030000d0383c50b02c0b800c280004450b1002d107008100e0924441c10704021224200042c0c03c000340703208602402d01080720100d51180180a1031b8400300004c110081d44201100d44038080d04640311030540000900840f04010301003a1540b40001500c0d20102c6994800ca000000340380680c0464 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 411805647 1250 411804397 411804401
    0x706201c0c020607150c0f020a0507140d08030a020a020115120b060d050d020a0b01091e0c020705060406020708010c1b0b04050f030c01050402030d0f2a021807030f2009060d 76
    0xc660080c51566030301b802c51507980c1c40782400c00b440350039200401c10454541c0750103864602520a1020150002e03c0d5200310b40c45020614007a950820002131b140c0ca0700043e80303c06540011140390042d4600b0503001488c1448034440d0042d500143d0081e04103e5059681c03502c0307007002501c078a40c045038183c0c19600046042080e01c44c1c145056000d0400341100345003810351540181c00983e812402c240102d080880000c406207503c1d1744a4402240158042c40182d0422411b90452908000005800315000d600010201c04482d14640200310009803e01e08907a900300d2030840007000c00a90740f54002181102459541143c081c0c001c0d40c540e401c4146002c5c0c5144e000d00d4000706241d46450401041d031400f403009082c0395001e4204201c0d001081100140314400d40541c2640e1440340d61101400c00c603030410089030090380a0207043c40032a81e015884046202107400c80002030401e0740c0702851600c04c0c0505400b0400c01c2d1007050b4050f50f02011010283c010300034040d005002404641c1d0005030394 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 411806897 1250 411805647 411805673
    0x20304090c030b010809191b050904080c120a0f0f0e031f1404050d0503071701061707020a0222020702040603080405011139030706201c0c020607 64
    0x7507100003c0d0060010009030081d50000c089070320359000250114041422200e011854540c451a110030623410600801c0201c29990040c5411100c0d1404000402041c0030060001c1c070b07104421207000200b901c881341682e202d0184d240d80090f488002e1845003601961364900103a005003040c034190302142c1c000c0383c80c00b0a00b24544060506040100100c0c411910584000850360565802c041c9040d03105c0c90b640340c2c0138a42c1d01d02080740010000e01c80a2140c1110662520765080240c0d035075135550001171040c1c41c0c00085640c58035840000c100c01d0707400003815a40f015030180070340300c641c4205500b0702e440808010f00d198110340c0030813903980142e507036105600c085d5209045c603070f440f1410031000412130024a500401c00f680218200100c5d4101c1c0c9029404180c02c02c048060851210135841d041030340141201078251045d400d02141c15604244d45044000e00c884111610046a030388450303480594103d001c0030048a00e50016042d4803400805c00030303d00184c010f41c900441130380c48100400032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 411808147 1250 411806897 411806921
    0x6090a021807110d0f0f02030f0a11030c03160c060f0e09090f0313060e100804080702040920091003030504032315060405131a0a180317010816060302030702030409 72
    0x68465401801782c1c0001c2d000069010b04d100031818900315034240015403103920001030030711400861000403100c04008880036111030344c05480e1140e042c46070b0000030654022045075042461100881c600f40f2804a004000c880c1e690344640c03508485080c000542c00107005401c41d0300900c06d1a00c0c824908000801c12030440b214018261842d00100900c00340300341402da1301c940861080350700600d43c814215500316400c0046166200c140d0300c000b030014803070a80000c01e030080700003e0701006925410481c101303000c103403022031b000d036100448540755142a000040105a05200c103002007140c1420700f044001045503421100b10310402003601d80900c4007039051401407210100442400e160281e5500058010340039041d03100a40d80b03280c0c82e0b00300ca50103501c02284010001d4402c0701d203030300700819104c1400d408103010021410b0090102c100c0101104000b2880c0000180e1031078006181c007243c01480300311205403420014120083e6101520180440c4000c1c40040341710f6072148a14448103032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 411809397 1250 411808147 411808157
    0x101413030c0306150b1c0207150504060c020304061b1415041203050103080706181e05071403030a080403120c030e060604110316050c0d0306050306090a021807110d 72
    0x11035403511400b0f443c0a00c004840c41c00d102e140401843c2d10400c2681c1020f206c00d40004180380c09852040000e0180300000340c8400165005140c1c51801980404d0107a0b00840c5d05224010000b10166583d12542c0310307081c006801d065008540100252000f030005101d46a40d070910408502664038147c0d06140308608110424103200810050106220064086040078040c940c50b40d01c03075041a00a10300003602260300c03101c0101e0303410070101d1110955544449034520701540070019501c083d4400000315001d100340ca09c08a103007180d480c24190485002402180307001c606102c200c500c0d102c040d200b00c0038013401c0d0100151800c1640117022918400e6070340043c1407900005003d2070008003410b070324082e45c50700c09085801034126045980c40000a140031504c01c40c440d008480b03d200315190f400260246408104001e9030681140084543c00c4084030038030340300c44c0c20540d1540c4030041c0c0254010444603159500070040a035099100c0000e0400902440600040380d05100c0400c4c85000050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 411810647 1250 411809397 411809399
    0x3080a0e24241011031b03040f08120f07020111010905010516080702070603020c07050604081501061119061407020a0c090c080c03040606030206040f03110d02101413030c 75
    0x2e10142600c02c5205800340d82c0d0714510611010641c850030a6002d40c0070802008115070101a0410031180a908000192504041031000c015220340185c05041241006c0740000116030700e002905d0941d0340c525001c2585801032030441075100358000e03113049040c007024000340075040c14207110315404e0741d001da00082294a01491900d501c0171040c5034002c240310203881808515a030010320401a1062400c0c0142d41c1d12190620500d0310300b15034041980800c000802007041c140109228200840440d01c03080780b640c03101800c0e075005500f6854543c2039409030f0440c2c0d2914420b0140070071054069480010480c46044e4540b1150404403003d90140e03101000702000c028440880c1d00060003480c40c00c00151282010082006101810304030540300d012001c0750a00c50719500c010021940109500d5a4503030301c07903001002d4403440c401039a01e0116424000803a007131211b050001c1c1d45d8010700107265070041000645c0e000507480c070144a0010144604854144040200300c003840c0a03030360144180b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 411811897 1250 411810647 411810661
    0x71106070b15060f18030c06070305040f05100f21050406050402010f210e1618050c130909060e070f05090c070f020d03050d15060f0c03080a0e24 64
    0xc0d00004050b6005220402000b0801d01141040e1505264101201c44680c94000006032030419003501c041d50080c00080d00c0c808041e040002441281c0100c1011011103075540104019500405d04a001143c809801080301034801c5951465082410140c0b02d507207034249210f9401c58008850460707900340e45405000c10f540e08200f064141203c10300e07007401c0000f030620720040e614203020005a001c981320001100c40d0311003413103071b150340a0608903148001980c0d41c5181d20900e1603141894000d40c941408602c841c01244102c4400880b5842c044101c9031803e40300d01c00900813103405844c0030303035685038400611006009000c000c00d042800c2d500c0310380c100020846400c101404010710b6650411403400000c0019403400380e400d0301158090980802410191094883d40e012664024645402c3d81824030705014001d0690b103043da240262480c007120140c40445c45404041c0214a00200081c10b0300101d4000a200d040c401003a50100c4903440c240b82c0498008801d01e1058910b008204144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 411813147 1250 411811897 411811921
    0x218030d0219063b07031e050724080c040302090c09040e120901090f211a0109061a0a081603021b03092e140405120706020607031e02071106070b 64
    0x2504c043c8002e031401c13610b19602c1509a000d00c5020314014203020903090148081070118a00608189404102c00740328800b0000c20004100d4412000c510305001080c50011100140c0f000d4944c003a01c1d1603000d03125149000200c1c0c100c0c0b4400e80d44292105404420f08900348501e2441c048807900c82601e40b8240300015003414400e4001c20517a0700e00e00c0d403c0000b43d9480400d00c0c0443d051000e44890420755080021404c171814070050079004140c000011010126400401200c0003041654661207440365807102905c01c94284500180178000405d080107600181e00c150ba0703025042c01454681d43c10220074081c584071b1200941600007143c5c415541c1010007440d0610080c140c5072240d00c600710905280c400d032000c55070200f00001180c1d001c29a0084008440c00f60000502d09000403005580341640c0300e4881c044d940040c010280410a901e00074040e0354220301001c8071078460040003180c268020b4002500548800c5110b1031485850385440c0c1c01070101501a6420880c280317007054035030351 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 411814397 1250 411813147 411813251
    0x6150f130c08090c0303040302040510030206040e09120a020307170c0a0602040e07140301090203041b1217090a06140f0307020f150103030c02060c0a02090a0218030d021906 76
    0x1a41d0011a4120026907006c802c5805495044400041c10345407100e1480e042c03500c5400007900004006408514401030044440c071801d210812588507684401c29080180074144c1c140740580e0003400080d000500128004001d0700842003410f0511151075820b614206010b8402d4501503030004050141c1c0101c555a02d50150041c2010224580c4007a0075035050310051240000703150b804400300d41003044031010051008890080b0720042c544a00840c540d03149054011100d0000f1542e8901d41c02c0c140c2010344294150080484020340c0c5486001d840841c480720344507404203c2006217140600250300603501401150340144801104482c94626100d290071603098104101401040026440030059801c1541030391500e0b00c4400b0054000c1c94940b800c500298080c0080301001116082640540501c40741c0d152507110f00b0314210107054440b207a0740b12120058020b9010409030b021190036100208e0712640c03000402182d000c1e2981c040c10035130710042082055000b940c40a4a01100d0040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 411815647 1250 411814397 411814411
    0xf1c020f040906050603010e01211b150806030c040b04020f03040b04050d020102390a050d18140f030f0601290306011220040902040e090703030206150f130c08 70
    0x107180d541002d1071742c503201d48144507074a52103000421484081d4040c0b00900c0d451903200302058210f12107902c10302d1406041e4001d14334100301c003032108004203201e103080038080d50b005006415640340c01003c0c08054000100683e40040d000c0022210b142c100200541c40740b0f0160001501a0505140c03240c03c2c000a80030031011680140841300c155181e400d5000f502c101d0401600c0440c441c200e80030300710b100d498080000344e0700550020005001012072441c1030301c0c4d17841d030311840d45046408a580151030b20b4000c7c903040003104680c0712a0303030610041000083c5d50040031a004510722081491800b00e00741c0110508804584502e880c409000c1c0700c216107000040d9455040d45401c9000820400702e441c80e0341d5040e44c031000200c03002e004450100304280444656999215240c10082019600621646040a40080002c2d04607140032038031006595041d4061304983d142c1401c28461105042c520503840001b10014040640e600e501d41d200803910040c0c007150300010180050400c40d002840300d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 411816897 1250 411815647 411815659
    0x20117040c092a030c0f1706040f06050604030c0e0c0a021c0908120301050a09020304121101020f030106020a0b0603010e1509010b0d1401200f1c020f04090605 70
    0x2020000320742461003000c0e25201440050080215508440c044840100d805158400e51032840c0b5070704e43c180c001d580c051445480300c3d6401c0072400030441f4401000d6010211030503421000ca1460316082e0001c42a2550800000c140c40383c49800040300c030791041e0700481e000942d5050804c0651034041040c2d60101480b015a818880d6048029407903082d04480001c1910400c005500750700d0240744100c018008600417500102e03810109810320341d2003030181034401c0e040d0040010b000c240c503008680c4030300d40c007000141001f000c108003034803003494020380c1070000e5400b482000c61510004000d103000b00003560090240030040d00707001d402c0500c041c0c8000e01a90500991000e104c00004401d464403079030400300689940c9800c0c101d40103144680d000d5902120042e490b1091003c1d00c612481d62030b01840c000c00034400300b10700000700c480c0b111f4030451092105200f400c5048040c0000b0303001c481c1e20101c480325900320156610080b40e0120081031142c800214050100001d60722a4801801c015160 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 411818147 1250 411816897 411816901
    0x80f040b01050904150f0c020c06040602030901110102041805060f0a3005060c03010e0a06050102071403100f02130b0f091c0f081e07022803021c020117 67
    0x450284140500030b142c0195007283c0410100201da0240e9600c81c0b1414030200a00d401c801c03100c00140031000c1030b0000511580b00010501d181c15070843c1c04654154008504d0141c40ca001514190081ca2601c41a03541c00c9c000020f0800b00b012001d00c04d51801000054103140100c01c2150090700784140d180182030748001480314000302580c850740300c4002141c2c11170020400c41e075840c94007000300004125000308002d00c04803404000103117041e95a104002c40c2d0542e51009004119034180c8155401039100c2ca05c04c016400081c25000c1c2da01d40013906440000041c1c4180109541e600c2102c1903070180c0c0021a4410011409031b46406080e94490145c0b03000b000540c180800d00842503800d210707000c0803050301d00f01c00c0c1c0d0000c0005502e80c0903200c201c141c4114109800a50090b4040c480b088072244098600c540d034a000f110300441c0e005104c51581e15058882c41707208174400301111607800308210003002507030703824540340c01c8c24034520a54000b000080c40014030084000354440d03202104401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 411819397 1250 411818147 411818153
    0xb09030606011b0503160201350a0615110c1012050907080a03030e0c010e060d0518010f0b0a30020f040f0c2706051308010e0d080f04 59
    0x510a80100c02442d1401e030100140110610720034440100030598840001c5003646c2681d03c03403180424a0003600d0f14034299001c48044c44c805008040c01c2d400c2c10501e20a0865500c0942006030b40004c50314200050ba1a192080d40d10f031698160500b401007500d15002c0392090b07c0820440c00d0841060382e01d140e52965043c4041c2072403c1058941c401c1315107030350010710584c604108010050607404125040701405060181c024005521000c010740a0340200c10b80550045068030200321010300749034640003000c0d402d0b10080001070419508014881c0800510000902400b02d0117001130b2400078a11242c542004030080f299800041d000304e980200800001d21a281040003034462000e50345583c0883c400102002d403258a620760142c6480303056510250603038130014488640f038841603003030403c002e0264841c1c1d8a06080f801d903592b41c0401881503a10580c040d000403c0809038a04089440b88281c81c2541d016070040880c2d1351000205008440d400785482d41c00580c98690b0403d1403e00e51 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 411820647 1250 411819397 411819403
    0x306081522080a030b04090305121003061505040e0706020d05130807030b04120305090d0c0302070807120b16050a0507020f0a09020a02101104090506030a0f06050708010b0903 77
    0x5a05030310980c01920000300210340d20303161030190100070020340d00e9080c0280b8065a140d0440b030031440000307150540c082d80341c1c101407103808403140d0151942820000414421046041c00a0490b01c1b008103074000000011800d0140c21454a040c2c1d452500403400c0c072052108440c10300d4a039a502d82d011200800c100e0740c000c150307213914000c1e81c505140c1e9000d004040b024258407691207a4800d11821030000240b1401d02907681c081c91103100316070400f0005c00030440607640182c841203c260008429200c00d140110582c551903032003030060b05c070340075501c064442c1004070b16070000010769031404003c4100920b50607043d038400c007451110144600f00110080ca01e010b240c900400340000010b2003015580d814040150b00387c8020709000800b9103415001000c1d4010013015000361040c0f440c44a1a41e000d405000c00c001c800e40c4d40306007018034000c9a1320241c0b5014014942500520003190b01042030101142c04080c041e440106541c242610010001141640015248841842070310136580e004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 411821897 1250 411820647 411820663
    0x20c0d0209070c0206071e03030b01030207170903150a09050f0619050a060b07150c0f050306150c0d020102070c05010801180c02070b0705010b15090a0308281e030608 73
    0x83c68011054034051000c114288110381c4042c090990f4035012019a0a007a80c000d14039034803e640a01c01c403002c2c0001581a802000c10080c030381302d0000c2c10a0581110300001e48041e450040441c0d40c090000141c40345000030540700c02034455241d80858090100800c2203d41c55004080106058a4411140c0000c00044204411031948450201703c1d001c6841e00500d01501070340c0042030b90303800d403480c040314520810090f6485850600804001e04c43c081c00e0f0741541c00d42562039541c80c640e696002c000c00080c12190361059504207000040c0f00800401041d03403080117640005035580c000b820810b2880c0c0311035000c1c0f410014a0001403180441007100c00381c7c098800017010464004008003681403650642100d19419000f045071424003005411402e20484d0070748400010180c0f840c1e03860558854084040d81008601c4001c02c006005040182803009010740180710001644950000d6541d05000400000769010f60503101c003451441a205102c05038203007000258a45485140c4528003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 411823147 1250 411821897 411821911
    0x120f041e0602041a0c010c1b110a0b07200f010507080310050306090a06060902030603030406050705071d18060709140604090903030204081b0904060207080c150601020c0d0209 77
    0x480a44080000c0c5805841c01340014006440d141800d590a882044c0c00600307500840b5030a0800b0302c07030990300032402500301d90789210034031800c011230303444480c0d110306018441074204124000c0040d28030b030381a0103070101a11492080d0f541724003080741c8200080758021076a208002c8090807140c0c0d47c0e041011605c260b640507030610307142d50740c140348101420002e9015507003500845082107444680407420004540c468017081120329100c29082e8101e002c11103850ba0141d02c00c010030720880c0e0046002d04800e61040b400c8694403500c605910f4050004104060006201d0006210803070140f1700702d0021b035942d280c0c0204080d2a25900c02000b41d00e02e8410000c100c40c1d252204c6005840314011079024010024062286041c98540200258014030940009020b0b440f107851a6811300113140c003400000900e8006182c5554903000001d41c8405803c0b607107183c04201100e0ba000c000e04c1202103543c1c5101224030306242047c006410241e03d01107051144089000710b00041c0c0e12900c0c025000b483c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 411824397 1250 411823147 411823193
    0x80105040210140304020909100501030506061e0307060809070902040303021b1c02040221040b0103050708070602070b0a110a030e03010f0b06030a0902270105010e040c0509040905070f0803120f04 86
    0x445804027070501c0300750014070714801d09120022090240c00100e8a0145030306842d0445444c000300700d2840d400602e1085140e05400c2010b0400415224861494110156070266801070b0f586540da83c0803a40198011400340e0090501080c2c40d040084850764820b034155411560140e448007030601007259104000c0c80781da80465500e02488046111500e0321990301e10703c444070304150810b001c50040c01d1008903058440d040d0b002c1001800407842c10200d82c4985c00411a1134200340800226802c101c140400b00700010781c4040400100300003a0100783d00a407900a203095020b0281402d4807140171210040c24144502000309444d0b01027101d03445070040c0000a814400742c03001031000401000c1d0f6a8103c1e04131500841c00c05800444a03040b0f883c2600c60742c585608200500c016150407403601c030046101401041d0071410103070401e01c10a4829070565001603180c504d03c4100541c41c0d008a40e4a034804260503103030001014102c1d400040c092092101d42c40c060781c40240b10020f02489128042c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 411825647 1250 411824397 411824401
    0x9090a0e03090406030f0506100608150d020d03030e060a02030c07030e18091b040908070b340207050607210c0c09090209070c030e060c070b040801050402101403040209 74
    0x1014400d442d8a000010300c188590350381c03810f0401c0561400caa059440b070185002003244d00030144281d0003112180e072507041c1c0d665034078070a4607400b60802134240d400952082d0750743c0060341c80002c1d40360340741d00c02e031800036105034000409032034a0303401806052a1481001801307015817079501510306099043c90041122000080498102440e6207403010f9450044014441c14070400f0420314805040a00250724588403141008107441c010340000e804104108001c0d00410071010080d6402118552403810450a110b0203030b00c1213000441402114030403103954004142d060010000502080780c0290412402d134480344901007200e8440d5404400143c01114824000e088080b07080b50800c0c02c0c50040f41c7e4600981014142c00001207110f0100d410000c2c42c1d2034060700c14481640d030142d85613009045010103002d5594000d141c006c030248210b060001d034480402d001030014214071400400e160038584144015111188000341c28030402e0030f00014428007000640780e1080d01154540415 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 411826897 1250 411825647 411825671
    0xc02010207180b0a0f080d02060106121a15040923070f1808070510180b1608030a1b050705060703050a0b13090308101a070618150c0509090a 62
    0x40000f603602d190020714502c40010740883c0c2d00c003003200701e5807400309407a03516001c04001c0f03032605000d0080401186250517a1a8503144551240440c0d0195442c040c0a140d020070016858210f11402c413400c0c0d4030001802d00070a101c50060048445802032010480d6001301c500e20546d420041081040046840500c0c040c103225098032619002c030407180404258a0b9019203449200c1800345a00461403a00c950210310310900240c001c00d502c6800750260307142000c0801074964842c07004200e0b03016401d01c070800402d040000031400360181200019102406141840c08580000981e60030306c08184000390100350013080d1281d012843d40360000f82d503683d11000000a01100c000c440d044440e6892022020380140d00524000b1f000c1e80742c143c3d080d502c084102c000d48085005078528086040c0d0030503035030700000c1c01400380d031441800d0100d60001140845800d86000039001e6410304101160201034330001e10802c1703a180070b18034103146005441d03c040f070329204004d0702c2150b48030740d5214490700c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 411828147 1250 411826897 411826901
    0x190623190e011a0705031c021b06010f060e010804110117150406050406060203070b060a080f06071d0a0e040609050115031505040f020d060207020423070c0201020718 73
    0x156800e022011031507070300c429141e001c084003401850015800300b84404000c03a542e0b0180d9039180d502600844c41c0c0703459145204140e90203d841c101c4025000d1050101c86d000f5440f1405c08070034802d00620180d0700d400a142d20700303541540107a00f404801c100d161400d980c04104164815089038980c0a500c000e40012105524141407240039100c0312030a005629014818203180d2440c03c84003840241d4403081008100c0f60107118080160303008001c3d0000003004151490f81c0032400a22540285503203401d0107091100c038444d0240160001d2003000703d9103030805004444202c40602e0100003074501c901154104209005602c040100200050200314594020a000d164400002d10a031030189110001104860108640807818804494000c404910969120307a8101c0095203024a0580030311030b41c1404020284c840e660204000005070304c8a019402420300940352614550840740b015424601000d018481000207110408003d44e9001548205441482081c0c0d0f082030314696070040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 411829397 1250 411828147 411828169
    0x62205060a0903030806010926011b020d170610080a1b020714030109050613021f1d040b01020606060d02070b010b0c06010b1611040204031a190623 65
    0xd4804030018038101c200b03910910032800c603072081d02c034aa5652528030064030501d41074011042911424a082500c200c203000c5500b81c6d0103648800002c0c0c1440d1540e0030400da09102c034101c005a40214181c00e0196400b48803103101000414440707015061040000c5d0140c0001c01c0c5007420069a1004112001c10640c48103500081c000d0417580310342044e0102035102c0c8828424a05843d231041152006820180508409607a0140203032178955076a1891240d101e000341c030140c1c2c110092000505045c83c0c0c0d030140d0764142d80c00d03450750704a15101c1004408044503d00016000340c1c03c3c252480c201341d80000380780c0d41000044032526140c4042c3c000b004000c1c0541c3c00041c00d001940310001075040003210017002002e880c5c00071b84565a07218105980c0c0d0344a40291482d11204000b101d001040c03141e440b840c5c0c5018000d01c09490195a901c500c038201d240c1c0000e10120040e281b042c0300010014500f202e40c1a00b464406002c0289469074504001c5032407981b900550001001c5c020007551048030f035034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 411830647 1250 411829397 411829399
    0xe1c03020d1e2604060b0a0803070b01120812070302030108060c09011d2706040f0b03071421010213050109290c0712060e15060409141002090906060306062205 70
    0xc0079628141c1000c2c405801b501441ca40502e00c940c00204151002208a41d0001c1d00401614482d0f40b8000102c103240500440551f0307200360612030b100076109031001c11070203400c4950f4050780769410704022a003072850141210124070780c1004203a0060b42c02104d104c1c14445141c005400800c1540003040483c1c0865000d00e142a031220801c03480024504032450040c0815201003200421300302d2480704840c0d0420039954103910201c2c00b00030072130304094400400803000d042002e40b02005103c4038010b803880b11118050345d40101d050743c000c0c140314210000401003441e1201c0d460345070800705078104d40c180d850182c0240507600101190b03403501048900b174880203411144243c0c0d41b078a81c0c4143d0b81c2c02c00380403a512400c0c0913186681e080001045203440240b5031504e5000e840701c2082100a02480c5e508a410412040d82141812420301c50880101158000541e80d10f90740340401c2109a03006010701c1c0700d62070500510410344c8543c2c0c16506407401003200320041114028045001c80b445078080303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 411831897 1250 411830647 411830717
    0x303023901020f072309040f0b0a090203061005130501210c0503060f0f0c121302010c0501110307230412020a1505130501030507080a020a0e1c03020d1e 67
    0x2850384081010000445409901d5045d401a680c10007a0407042a5130150007041d810b0480e0000c40c0183c1c000c2d42d0414465100011082020b0f40482d003400c0f0b04a40c295011412071000708a14140003d01855030100320900700400c0d8100109e036141460104030043d000d0743c4104140c030230800e0061741e84000e0030004003251214a484584029000d00c220303a50a007000804021030221148001a03d1100c01c1c00c404003901c070780c0d80d5003c81002c068034000c140d0410600c01c4a14000c58400e1043d0034200d030400744c0381941c0c0e140a072405401c00c0881c41c80e1841d800d40c0d19145286003a988410307103058441040c050080b20840c1d000080e080314142d04804813070b62000c041500301e182c1000040600420280034807084559882c01941103071000c0354200046001e400004164296a600a00000c44503092850000c2a400041918255211803040c16401404410018140c04010013106903126181c0140c841039028444d8400c1c441c944079842c207101303806200c10b0b06d8503070803641c03c1021040d62400d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 411833147 1250 411831897 411831899
    0x70203030f0708071b0b071b030c0323070c051509150901021c030605030c0a0b0d050402040609020c030310080604051207050705090a020d050f28020912070303023901020f07 76
    0x1040100d03420598034030300408c1800c40c003621002004400100d402c0e0300758451038020201920140c400408100e4201800c2c50700c0f048080058040501520f070603401202010300351400c0a0078041c0104176180c0000541105120015403030341c0d58894281ca00c80c21701e0000341c03599003450060f031411080407010420710f086c8a2036900251340c580e0141040350021412621500040d030300340443d54041d030140d1511607030100a00e40c12140d07140c120070b410030300c05840010f01e180d889800c04101e800100c91007100e500000240019594500b505da0003a1202101074801c40c1030541d05d1990f031317955016901c40341e03210209510051103000d01482c0000e00c80604460082d26140108000a500c40f0411074503191506011030b641031000802c2d60b1052162186840c801c94050302c6501030800005410307403405400300304c092041d4917024441001d0601c03800c0202029819890082d00340f1814811011181980110400c0c040404111f202e54100c0d11603c1c1c0c06c4407508000c0100d0070440300e81c0c4007034818810490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 411834397 1250 411833147 411833153
    0x218040603050d1209030e06030612071217090105071203150f0303030509070803092209060b13020906070206031e090d02070b0309152e0509070203030f0708071b 71
    0x43d0005003000d01d0b540c0c01506515590044100c0d8024100074000907646200c0206e9410507100075500003030f0040010310303202c2507004441d180c20101c2d00101c1c0d409030040c0900c42000226182401240c0d100701c0802c0c00d1003800c400081131070040350b0020300b0007919030f00310a00c030600981c0480b000540f54005d40781811303190160702c0012509848104c0000b443c110004000e80d5001c540a400d42d552103020714034000043d401c110403048441d003c001440d41446041c4c1608a0510400030b0461050201060500c4603900b004103498040c2c540c1e50300d07580100f00c000003c1d0760f00c100b1206420ba04807405034480c1c42e0b101600e504d44054a50541e4801c2c44881448500380c400200410003030100c0d4210781c501903d03030328138170380b207000960380c281e101d03070201141c6201c004001a40c03030b511201d410303200c59803959034602e02c038200290091102d440c00d45605d0140700506007850a20782c049420b00041d4514181107201000c0d08400401803820012103502144c0050310500c0712501070046900c0070020000c01c0e003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 411835647 1250 411834397 411834403
    0x13060308180102010c210608030d05040318060507030309081204050a050115050102070b030c30010b0702091302030106081209030c030d140a12020c010b0109050415050103021804060305 81
    0x1503500d4950032440c000c408158414013607510910241d80c1d0b2883c0d00d60a188143c40603400d40034001b41900d844d5913010031303001c2081000e01110107039500081901e050034280500001074070400e003c1c80c603005000c14480c07260020308541b181d5a00d80360004003a041400c0c00307486d50040f2118411888918028003042c01000181d699065024000800c91418503201200ca020160702c00c070390150300803c0c0200460f40003d8081e591010031502000c2ca03224a0402240c2d113000428410340c0e800800d80071101c85403a041d0079160240200b80754503440c0003003903000542042e0000780b841202c04900d0500c0c404549003074201c18001c004502c00c440c920104e40b00d0f009080d4000710045d41c0240310700015078600b4900082c52034a40740441e16140048004030018605607800220400240401c2e0b00304103c83c40c14510041210a565800000f0140d070300000062100026600040c031540c1400405061090fa00e401002212400d00f030060390303030390458000c241494003c02c0050f8054905180002408004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 411836897 1250 411835647 411835657
    0x10e070e13050f06040b030705060903281b0b1b070b03070309020f0319200901031406060d241d0c030d05070503070b13050607090611150408030613060308 68
    0x840558030304e0303480000b4841100c143c0b12009615500482c4100202c2c203141009103444400502523031280350300905200088032128a50030320112252010005118122410948540c01c2d03800d00d03519945407812840d2503025400d03074040031840d0042c1e00102d02c8402c00000c0010484102502d031a4500060082c0051105030010b81c0a2508400303950f140749000718210230130054071004d1082c1d01859441e40105081c0c2c00200d4000590345884042440d9100401b95000314483d03951103ca0300100c550350b82c18000d000e0000ca01903010245807030001211914043c4448411a002080090b41c00902030007030a42e9802040d4000000301d020329101c2800300390320b5910342080e012510310b80096041200d0a208405014115400500c400e00021300c010303445c1608101646030480c810541c90f01c41504001c1d0030346107400070458080f4104000e0b6004041e05140100c900d000d002065041c9082403c400f10040006181040000003d4201d13a10880d031002d080101010401200c0d803a03182050143c0c2c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 411838147 1250 411836897 411836911
    0x715020d110408030d020f0c01090f0c06020a0b0601032705011a0901030804050607060605030607020d090f0602150c0f0703050909010504050613050402030f0109030e0a08060f010e070e1305 83
    0x140301c0342000450340700e0201c1d001c0324818001903103003d05500c0c40302c00079000601800003a0780200101c480500d002d000b0000b105000e182c0341000390800f464540c102c0b244e161b2008081d074000c818003c003c503420207112075210000f070134042050401c02402c1c01c20003401c0c2010708200d90644a0000c01c1c000c0541c00714a0b00c0c1ca6002c195002c4002440030829640f10034403004010f800100824040c17400c10314040c010040c46020003081054407000001c2c141002165203400681c0146030307488a041e4009070300e17002484e080c1f009200f018100302c80251501821a841680e0162820100340b01e640400c00321111490048486912602e0318a001480f0780c0c0b007444410700c2044118004601898180700f030360f0203000014403110005048030400e1000d09002001668540240e0515610101080c0070f0004080c4c4240d6400414500c5c010070020000581d410811165210804210b1078000043c0002d0558000005580040c0d4980d001110701c5410590707110741080d000000c0035040c0b0707041e070403440c01a10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 411839397 1250 411838147 411838151
    0x201051504050f04062a23040f090f020706060b271528170a0614040b0a050406090917130e1302100503010806130803060d1401020708030402031203101a0715020d 71
    0x8000d0000403540200d004140255070045007c0020b0105a40706e808902e1038102f0150034801103440d83c0c0c00726850382e0f03c5a81080d900042d51030180090f0826a03140401403048505c2820300c0401161000910300580ca0b0107070000251840d0041d0b002012010405e00c14510451514001b00c00800c10341c2d100b4901007821002c60b000c00d03003d411074080c044c03d070350480041e58032081c41007080001500c91812110303042504981c0200d40e41d11640181406402c0c1180045446c0441d49810026200503a1082c90400c100303214071090050b0503841c25044450a0f411980c0036281d1058039264203071040c0d002540000c9001e27003911a41d03008070181d8100e501a00549400b95200f14400034520740c1c01c0c0d4001c2508504000141d2246040c40c404c1c43c0140c0608524a85089001c3c0d4003400c90b07009403020ba4030007d001c0100b008514081200003007000c07503212200d06600306010284208000c40c0a03201180d0403000006202696803025105200d41094000b100b00c051441d0150082d07001d160b071221154 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 411840647 1250 411839397 411839447
    0xb030114120d05370915020a0c0311060f281b060507050c0114090c0111070302041e02070609030212041a0f0f0a0201051504050f04062a 60
    0x5100420034103039506064443d40d10b0b007405202050062800b44101c0b01d1804820340c141c8101c00c0a2601d070304024005500d03044071160400c0700700c00ca1420f89441c00001c5521122403100081c0c1400303528003c5035807110400c2d804030100c00001e0358900030203010b8002488045280144407a0305c0490440701d40306080e075800c0c89004a013007141d00040107617454441182000ea10f000181c89540076a0340046545032090a041c55a00c0490031342d15143c1140c1240c6014070140454841c0900051780c10b1070b402d080200b5030b81d64440c80c140e00d40700144400307441290354030313071640c898500e24042c51082c0da16250119521000e0b4680030005005040003030700144500d40b040c1852000c4041101d040e2108079a0714400c5046480403480385600c80c0107034020054050042e45200e0f100403000d060000e609400100d1507280c82c40018103403800000c626171145045c40300780030750500841c03901034205400290224a1043c4c2d00c40f210b150071001ca54081644000040d501070140c2d220845541102484140c0c0d5004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 411841897 1250 411840647 411840679
    0x81b0a060c0201270f0909170a0f0503070c0c0806070806040b0315040804050301091a090111160212030d0f05060f0102070512072714010f090e070b030114 68
    0x440700c094002804510102c0a030602070910a943c40f08180c9150340303400803541c40b420844006016688140c056684800c2e00204101c0e1800c81c043d802040d032015142099034030500240700b60741c64000e20003032040000200d000e440c82001c482501c0b58100c414102c4d03d9554003a0f82e40c6da12000c031000e40001c1c40b14004100289000d0043c0300a600b030080003840c50440100200ca001c0501500454400100300000220341d10f0070300501d62102d007c0c030741c1d80301d82e50064104001103010041924000b64036010601050a0903c000d0b0350ba16400c10584614000c980c0c40410140300648440e0500761102140c000a02540398100f660034902426080c00503840f03100030b1101144124802e2409038100d40400d00c254103083c0c00d240500c03402c40741150900390740d505140000114680d500c44020704000c15407026042180280c694810800c100c42040d58034010002d0b18240190040c3c3c500d2946030500c200f8200300070000203000c0c04e8644050766503540c2d521480c1c02d030030268440c10390140c01c0906050145c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 411843147 1250 411841897 411841907
    0xc0c02030c01032f07050d020105090d050301030308070e04021c0605030106050105040f0b16060203090106030209061f120204051509040b0d03080402010e041803090509090115030f020307081b0a06 86
    0x20000400304446400d2a210003041c134441000b100d55980700703400d120b840c005c5802040700c540814095000003505040c46011141040c0802803800240b1000300010800260301000c519488981c80c9001802090f983d030000300a40b25076413401860040111040503540e03000d034800011258100c000b001256581d00054603540218031510344821480c820401c90f130081003004046502c12034240384a1421503079075040480e00b080d00d00ca403440e95660303c10300460801c5014290001401c03100805241044c80c402d0b4802880c4060000402c514803001c204503820715010f031009010024071408451000f004403100d5600300d804034911941c103222280320b0750305000d040000ca86425540750b80c01359485400649400342503464103034220b076560002c1840180110008551148280e444620581c905410004114005800c0031440c0e450b00860707420102e44410480c040704c0c3d01020441c05001103000090500010364090308543c003445c0450640b010102442940045088440035803040d240c10702203407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 411844397 1250 411843147 411843161
    0x30709150c08040b0702060702060409290d170c03280e0607030804030e090117010b01020706021f021216030e16181e0b010207090506090126010c0c02030c0103 70
    0x100c9004100b006201040303031013006150007400500070034601202d0340e02144040d80103a1100311407556401000380d01000b42ca8004456414100282000484802c0081c2d00c00795180030091980d05420038112214041906940000b260001500d0302c4c1c2110358800642d48040c019017901d850110010030608a000300420808098041c004600b0301800d40e41c26500c0364001b41040d82444613148551060340e4492480714083c10102034041c5c26841c104030312600351240d2544c0f55040d07400c5440e061120543c0000c88a07100604103503003061107541405100e00a116103120b2000e4203512500b04841601c039448406101c035800e903410050007010448850b200c2100d004a02000101c0000400041c84900118141440030940026061041c0000c00007154000420f412101e6103403900a4803035031b01888400000d2048a9061009203000c13030014160300c1050040410340c5812a4128000e16142001090b17003980c1903000b04038900c919600a407034408106130485c480c2c8a544c0500039154480e0088003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 411845647 1250 411844397 411844403
    0x110d2a0803192a0e0a0b03130f0510090201020f0f0d0f050c07061d03010b10050a091a120106021b0f040e030301180b0904120309030311030709150c 65
    0xa81903445000b081e0307024014844800002503102d5035061410140121500074a034070b6402e203040000d092000c0075210f1009201c10500c20258044108107040c1c0c5c440449a00030000740480c00c2000c8145016800726101d000003600340d11500038102c00320b4220303a000340c2002c1d001b6002c980009441d8100160b507490081681070150708168490a238840c0102c00d03000300e003c480d05160b801d000101084074501006544400b0014803041c0c4045011034000301c1d14812110294001d020301c80490f8023103007034810342503451010420001551070b4568400c0340a00d026003188090b2802d03010043c15811281e0300010214003603024214000920b15000040c0b04007414410078851620010440411051600c880d00540d0015102d00d03240e844c848040c0015400b030010061224181d00c7d092402c1021203080041c03160040600000f44404980904030601104020345801f04015400c1d1800310050f01514040c03400301a80132050100c142d8000340d101c004e03140101151030280800180441380d03004124005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 411846897 1250 411845647 411845663
    0x50606130608220c0504050a09030507170417070801050f06010813060f02120a110c030f090d0c080a1a010f0b0309070b031305010f200703110d2a 64
    0x1c0284030300460003154403086980000302020001c4860034501030b01e01c0d00c101d5480d1803c0c40244100d2429124040e0081c1e0548410030904105640141c424884c0300c401400b1520600c41c01d0742c00192034811200504861160000e0255080c00d6084e0380d600315000703c8425500340000a6400c00005854520900051303540492507258290420b13151080c800007a5090781d10f601c401e980dc20380070300003045607084c000401d0566180025804003201c0c8241c851103204102004009180c0500006a4405400b110800760781c42c064000014038031000b407900100800ca41c10800168480045031302c0b45094010150365245480128144540f04424050390740782d60b0f000c26040c0401c1201300d0180d43d1058801d01180c1491380c1f20a411801c0b034000310b80003883c3c060761030b03038020401074280128081007601e44418400400541c0c5980d800d001495036819100b94003040510601d40301e9207a052440440320207480c0d0139614000028043c84a0740c4058510940f041840000c00c0042403140754181d40251032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 411848147 1250 411846897 411846899
    0x30f0d14060a1413020307090e0a020f0319090c0303050a031b12020c0109020916020f0309060403020f031c0e0316031a0402030f0f03070308010b03040309171218030105060613 77
    0xc01c0342d003c0a8458900d8010f030481460100c24800c0b44029400361900c1d4484044051030511480c1182500900d041151401072003000300700c00d01d8206807500140f1148104103076011010b4420000c006100b0007401d07400702680001306068101004103a03911441e5401e20003031950b62000d144440b4880e000e00002a605420b200300c0d07001640c00307050440202800030661000c5030b000600000c03816141c0d588604580d40e1210400d5030100164803400b210703140a10704101c01c90b0005000d80c05079120107802611141d001d150990780074041043d890f101143c00c040d16882c2100c008050f030203041000343c0248901d023092200403172a1002e040c101d0b0340c491041c000721034040003038203008400070b0012a010300ca1410f05240121047c407501103019242e20045031982039a041c020701101043e8420a014a010020700001c00d0344440c2810545215525854603245070f0081c0c1450040c064071100c695110100c0c000405c00542d01e440c1c1c041c020124001c0c82251604002c01070180320356082a190b403101c0180c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 411849397 1250 411848147 411848159
    0x80601050d0608030f0a031401030c0e04060905010203091b0f22110301090902010e0406050f04090c05060a0905120606130507020307020d05030a08070207060c08090d05030f0d14060a 80
    0x34039601d0090700300441c16a55590801c0c0c55038203c0c840c2030009a40104008850950620405441c00c0030000c01c05115403664480c61840380391409040e801060300c00004003448540d42140320385642c481300031035030703071501c28035aa46900b18003560504039035240c100080f841c074004d160a81c82540007482003030300c038443c154480c3c0c1080082c898800c6043d1a4a90701d64450b96000155009103c1c6003001b198030f0503503200062414030040e0520303114502d81001800141c5504600c2003281e00c05071400038114080c0c0c00c148024001561082c1d500110000700d081c81075910500d898100c90f01a0750500d40c0810105846860300070031240150048004050f5600e107c4554000c241c00c10031b64010303240791001e680c01007150898000c10558a81d80000350780d1002c80d03071184071158449958030140414a042840c010010004050301030300c80300003c01c480400b03035501003007446019840b004403a9681030040d0b040815030003c02c0603810f26450b0030070248032103101800c07a81c868000148900c8049040c00c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 411850647 1250 411849397 411849407
    0xa06090b07020f100207030c080703031d040608190c080613120c0b0403031e06080309062a0115090e0727050a020903211602031f0b13020a080601 64
    0x340070ba80c080303030084464100e9100e0038102205450f16601810b00c00f8210f00700302d050120150702a1031598491030081000c20350250714861900c034842c2111440490301c2c00080d001d0700c0310b40c0204101d4000c010306211805480c038668101640b14440241c0d06d19900e10b10640c442e0704c201c031031013104d0310400e142d2800034050800000100916007040015030700c0b140c4035010030041c1102c00b01c010030342d110700c0043c5070514982100c3c846400c5280078095103080c44a16034681c0a58074100d80961404154445140400100540c01c0090280b0300c544089040340214040d10501c040010603051804005c6100d0801340981c41151a002c00204810b5140681d0104598140100d000c00c416040d10500c2100300c40e8040c00d40110043c110150b25210104101400e00e000000084048a030310340000c07202c03015507070546007a02050b840c4030880c0010784c000b19007031080600d0a00c1711400f0b414240455002c1a034091002c40a00340c421800c5a2000b92085c1c08900c940504140854640e0000501c03944c07140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 411851897 1250 411850647 411850657
    0xd0f020a080601060302031509132003010e0a030f170f04060b0d050d030606181401031b02070801051602100506040209060403060608010f0504020d06090302120a0804110a06090b 78
    0x5814540361a6a640d0401e0510b0300a03088080000c0d00002404031806d00a4801207406c0700850361102d0500b031143e51100741c04420340f4020841040b0910300c1070f203a05200303914481d45e44058000c2c41f00b400c1d41d0840390345540034900120007040000703490031450361040c1c4144043c04000c5103140100c1c0c42d54550320441d1440100100e90301d40c0c4070580d491140c0c460400d40350b90180305000500341829010006010788900c0d4100804000540302c482080c5c0501c0600a400c552101d1001c04000b00da180048001c1c011003904128404503000e111030590b98001071039012a500c3e00002c000f40e8940580b8401c5842d04910b01500580c01070301d808150308203a901407a000704c0003d00040c60151400041500d6030015030003540ca043e43d4001c10494101c080c01070355070284840300200900d04c2c1c0340d80002c03002d110044000d0095580c4200080c00c143c02084a16004c2c51034401103a100c55210320010301114007280e04070f41c4002c00c2c8008000505145040d102501c800f41c6a10f1602c50410301041910b400c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 411853147 1250 411851897 411851899
    0x504050307020d1505011512020c0102070b010e0f070302070f11030f0d020109030801052b030e091003050d1403160903060e0715020c1302030a0905012a0e0d0f02 71
    0xc00c100150050b034031104400200782c030460194140f803e100c01d40d50100c0d007059010a4911104008844000398000503000320548200e80040c3c43d84009904240240140300c402040c0840c42c0b8000718010903180d28851090550074800e8039240d41d542c0040782a0300034400000d00350988408214002a5084d441c20301e00b40014044078404a210b040d210b02d0702d0400d00001c0003507551420600e06159100041501400d0305407a48078807113040d0002c000409080018910a00300210000307000c240c416282160000c0300182a0840390a00b01c2107410910801d02c0222a9403007a4051508214015480f02c103003080740303d1046046940300a0910300303c4088801100c100a140c44001c4001159031140e080d0314190b0318000e05089080031549880d500104000c04299481503404040c00e50b00d200e0b50108414a8120141e22030300e4041c1c81c040031f4904407074000c06550810300781c01e000000f0502c0c00c0c2c1001005503030202c420041428142c48580e0b00f8401395810000fa6468600816111a40b0540c0544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 411854397 1250 411853147 411853153
    0x20d03031119050d060608090a0803070516080a1d0901030b0a09050a0501020924180a030203010c02060f060a210512030f01080601170303150a080703050304030b0f0f0406050405 78
    0x2032803820015080d034040c40e00400b00f0404a05078800406070300c5440d020340700500b04803115080c12149a5501c01c000c0720020486800040042d005a219000f40c0d40c008180c3e10503c2042d8102d890034201c143c00c0180349038000340c1034080c2d6031454240004400922030018060b00005c1e42192105500200c000b013107140016120180040003910030803001c1c1445000301c00060311441040208a200c0c44c1240401d90346208a9031a80094000b282c101c0d4545000300c02c21080c40200c02010543d40400e40c0d00103585540ba002d41121629008680c061184504038940289540d0300e400300b0442d110b0500603079441d40801c0c00030f000d032400d01d425181c1e5124040c500b00d0341c003104541480c420551085070107406030743c1c40e90010071405100300300c007a000d820101c0e0001e00030240303000d200340d0f2800010a0060318001d070f450842e8843d240e861610000e4021501540c42c10390b02c0e030503c1aa40c0d40184000c0314450740c1d4200040154086001030760284000d481000b0760350f00c65071104809408040c2050310140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 411855647 1250 411854397 411854407
    0x51c0b0c03220516090f0605010e10050a020717030703030605100c0b0925080708280f14150a0e0706080c13091a0d03022e020a050c07080a020d030311 66
    0x1c4c1c008026002811400c3c800300c6c40d45041800b910549140360f0015061101c00c44400b50241d4070360750b80d041400e041d49040e94640c2c0740038500702d2038400d00b5480318846107070000294802140200007451030310700903201403001c281d9034400d000c6a4441400e4560004950002c038100203070020082a4004040c5c2d400c88401814082004c0403200381c0726510b034003104891400300301c0150140222002014002d0107805d1080c000540d60f0001d6880c0c5180442c1e030b031a40c1044408210b9001c407888201034000504085c1101200d0702c01e13a9829144512140c0704009600040c00c61602e030144400f0084090003402c0080e180003400e580ca91005050300c03c0b00340c81402650904072050304000c000300301c07981c030100e00304400241c0d803134215940c851054000c18a00c0300d4100426000155550742c00c22985048002c10281000c034214028954200d49040b800001e11020443e40140a800406055025190035540e940a21a65104130302002034105400d41030b0340c80401e0003170307010b101ca2205402030705142c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 411856897 1250 411855647 411855673
    0x904020a09150c0302060912091302072315090a0b0705040b0c1c080f0601081f08010b0a06110c13020c0105070309030e0607020f1009051c0b0c032205 66
    0x494103034982c40001c11601c00c20b0245541000001e030800785444c00390a1401031001141000c0c4619081c0c3c84c02480d04104940d4a00300c654101d4490340c0c3c100600b0600302640c0004c00c02c038150346000003007683c03041c004da82c603100d110740701d5441c0520044801441d008503c3d03601e030b9507520310040540741800b038140000036088000310010300b094040c94001c1c00e0362000310368210440d08914020802080351900401012146011001e41c00075000d0070275034a0303507440344006424900810044102c5292507400000c14050540202442000c22504078100503190142145c980d000e40c800c040e00c540c81032420610034102104099800c0e00b80b540c015160410f071400741d07030a4440c00d544030400a55a11400801c0c1980203001540d00c2070f080740d05921300846034001070385079106608a0f5100312078204600c0c1c8540e001c1c500c40c2c030003024064480c6031921800424a078030310115a030107071280c290407000240c4030703c0900d048a11582401c844918485503002081840d03c068940071581841607019042c80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 411858147 1250 411856897 411856919
    0x306150414040f06060b040b0904050a06050a03050c030105070e01120504020f121e010c2c0a030b01060f0215070507150e010606030b0a03050721021302030a18080904020a09 76
    0x114500606072405040410300e4013408555003503000340701c0888140424446003900204480700400d003150080303029200c5800510042c642984002d9005244803400410888045603240c5008001c900070026035840e05003d803400100645920300060340c40e941401c441810340e01142c0c0260016101d1050707102e583c400311340803003002040c0d00ca0a62010800907041990880480e107100380c9039000f0f200f6048104006041584640c11800b048030f042c41c01203544421207050440092401040300c01c0055030b03401c2a14201100b03000f03450002c0e002881d00c0b40028000104c14a801c00c040756405e92541d518407046172a50801c500480303007810035109515a6445500851b540602c46400010308945011805812515600040360040300c1e002810404a0340206190044414521000b02c3d510a00c41d003c0b41d1090001d40c0095104004443d0071601e06e0199001c1c6100f1540c9060402c030500d08080c0032a9440d02c406401003044004100098082c18036402070412040181405007031982c44440da195 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 411859397 1250 411858147 411858151
    0x1203020f03030c0d0b1008070509030f030708070b010905090601090c020307020a060801060f1107060e220501030303180b011401050405030708250e040305071109071d0f0306150414 79
    0x304011010444c05845410fa115100c03600008440a2607201404500a40203e1000300785000b4054049030a00154400388000e21482071180d060f2580d0389036928100041c0e400c05c4100f96661002e080c00420701c3c0c510b5200da140208662401001c3c0785c0e28210143c00a0104001000110f0009200001c01a110400c0840207050341c0d0301c035080c1c4c4d5030500c100141042c0c003170946c101c01c00040b00d11a4040d0403010800b10280c8249181002600b000ca8000c00e020258013404e00380000484c04c07284601c0e181c0d03680428143e0740b1955050003002c0d00c1c4800c1002e0b1101c412400380c03c03041c1034001000201140d441441103080d041c1030590809a880b4006420108240d2141046412a00c07010600040c0d00c039428030389108141c0e482c440d985c1044001c00080000510090910000182030002c0c40219085481e0482c401001d111040c640300c1c900904552607a1103140b0301c460f00c0850580c49181640700500034030030103802058aa5210007a00208006409000d170304143d98150b402d240c0c0100d410b0b46c1d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 411860647 1250 411859397 411859411
    0x60c1902040908280c02010c0615120c05131116020f18041203020301032402040f090b031203090d2f0f0c010806010e09070e0a14010e0405101203020f0303 68
    0xb0003445206071031071211803054075104c1080801107071180142e8100300100c0c88030390801000100c0d480942c414a00f80c040ca0340100d44084003001943e82003000c0c68041c90292041552220380d080010f00c002c00c1519051005603a001038184807220107141907003007503101c2d28002040100e5012091001c100400e01010b466518003022900f04001e1003107540c014201ea10907444d0451840d851621543c058100203045070785202e461141ba41e41d015034640569016001d04043c0d179000710398680418004003081f0149501034000c4108550a03400c003e400c3c0d0f41b0035064a8090901c20f590100c00f200c40501c10008100e21160000f00c00c0c10b041030010300300c8060b22120b4014004400034403d01d510f0900340c0000d15040201c010108811640d001d0107a00c000c1e441030f12080c0312030b00c403840251500390843c04456040760702480300145001004800d140c004c02e003070300e468200034401810721003500c070304a0308031801098610007008281801c10040040b0703802441a00d80c50f444d03c460321419948260348007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 411861897 1250 411860647 411860677
    0xf0604061e09110f040b0f0c06011410020105070e040207020406170105060a0b07030905010509040e06070207170106050d020f01120c080a0e03031603051003020901090614060c1902040908 82
    0x14000c6881d03074802c0080e0465444521400e041d004c01c82c1c05101d10641c040e201c80302c400810046e10f020190750903500d6207038116041e14000d603150700c01401181c0342103000318400c4402d404d03490074090040c0704041c0980c5a69955050222a5006001c040e5200070300498002e07039a110002440501c01708841d031800158000844d02d13080072010402400000d03040082c0504041090a00203504401c02e0800c6402c2803e205813a1080200090700500c0c850046018901540007045400b540c085240030948400b14103d00d15400d80701400340c2203c80c28008c1e650007258240540e40036180108210f00e601130149080d419042d14031042005031504a04c064000c5168001445081200d502803400f00490005c029030861803d2001c1200c5088902c203d10141690381020400190301040c4980c0036580203040081c41b542d507450110000d1015200b6440301003140711014038240341040854004201e00402000c6485041d002c3c0c0780b102800320700490340142da030310b07405c8006140300f0054586441c0f65800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 411863147 1250 411861897 411861899
    0x7020a020f060f2d0406050d0c12091406100303170a0915020304060f020324060d11030a0609090203070611030d0f02180411070b0a0204090e07030c0e010b030f0604061e 74
    0x380c07184c0d840e90742c183d00006030500060240741c1d400000d40741410702858000c40c0021343c5480544102d1104440b0031001820629060b040c055002c19801c800640c180c11162a80d449201d0044041b007240001030018001c2c401881000b0101c2480d243c00c02d4401c24000f5181c0b0181d514084c4041d40032010b00c01c1190080108014080144034002410b40100360a51641c501150b011030020504540d030307480d80301e40c02c210910b10381700c81066841c030006280b0300704240c0c000c0c00074004481e0011101080404d04200020030780300042d025003240c01b503002d002401c0380340c05d00c08261004804085031018500c02400540301600040c01184d081c0048071000517075500c02c29404000440300000c40c903002d50704024101c1d000d0b001c0c0c2011218002e8029a041c520760f01c5040100c006441240e0022090908001e906001031b0f01c00708401044038403030381d036001c134044e9140312444d14442c092141c40080034080c00001c80030b881141c01d503036200c000248000343c1903880b01c504000c0e102498007500142c070f102c448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 411864397 1250 411863147 411863197
    0x71a0403020a051005010609050603130206030c090f120d05030a0207051912020d080619080a06240308070803040f05060c0d060902270102070b0f09090105040507020a020f060f 77
    0x113400c1443d07203001d6041c096036050041c003074004040c0c0d1007014042d500010001d020181c0c8000d2a034006075004100d0342d5a400c00525201c91074000c10340c00c0e4424020200b004940c0d20748680103c0d140301d01c510190131100e466000907605504020580c48a007502007142000040c01030129040b04040c4d0031403950b00950f030b41802c02c100c248040841c029540700011005084e80c02005c0264400c404481380e261600b45003001d12480300c03059101402520034000c0540c1006103e4000c2c082c8484050404410808a01c003048604095440701a0454a003042110701050800009560244c09903c1e075030802012030765002e10300230003122260020440420070464800450044000034210200f007981400ea901c08a2140400d01c5000910059461030000c4003990007031107070200414242c1c89040d1510f00c83c041c081c1d0142e0040740c8040c030490410b000820146041e22a241c0a04402e600514074400c4550a01441660018480b503100b0014040c0228890680f0010301c4100c426442180c4203088042c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 411865647 1250 411864397 411864403
    0xa121a09010f0b03060f2a03010e070f050a120f2a0206060d020105040e07020c06070501091703040f140c15071b0e04031d0406150801090e12071a0403020a05 69
    0x2500080c400c0c1c005e942030014840da1654135a800c21401c4a450400701813031319031300403da1000540c25060f900003200004200701c49285041c07140c02543c80d034030f9861740b074800200c40d00c2c03103004540800b0401c01c0e00d20302a00f502650041100c10f44079640015004c844884110855450580c503006443c1155290f08103654113101864000a080e94012403070b209960018180d40034500902888144090000300c0300c610070041880d03043e0002e4031103940e07843c031414900e001c3c01040300b042c1c1d500e001d034a24070b80061014030100c9214540080d04485150f04070f5032009035103154485942c0c40713031251840c0032250b907840307401004500c0903120107541c0d10340113031130403103c2c18030041103003014030300e40391010004001a080c8450780980e043c900b14031901c105c00c4126190340c07a03000c5040d42046c9010070106d603180340740c940c52041250716111032410f43e0362480940c05460241c00f04000c140c1140d017498018541c1100a072500e688600c4142a0320112400405181b17031080314180e0060740030142c0c69050040034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 411866897 1250 411865647 411865661
    0x1c0b0402181201020301080705130b1c03034d180909030f070f260414040b010e10200106060906030c02030301051c0609110102010c0903020a121a09010f 67
    0x102c0003582150700d413185031901ca41c00c0780b054034000c0302c030500f40c0c1c50015015404040303050b20092130282d081005c0c05030404000c0c1c542c1c50407400319180c14502400314507640102e04661240c2e800c881d01f80e0005a1950014154411b800754400f003400e0625056009900060b15202021100c1104a1081541004040c1502829480d200e0304204525000001d03500100e4948680200c10304181e00c41c20714101044410204021000201c01e5103e450718030729400040c001c0b21250090018641c9400c02003004840c0e181d815240404c0c084003c451103405d142080c554102a2824035412050210000b108010512204064a03954500c410701449400440f02c030003600b0140303404c0021130070046001e552444103010b41440b41d51100190311454030a511282c6040d50b00c00d400b40710190940c540140b04401c0100454059400c10000b120680d100300c03c118100ca80081c80c5140a03403401005421a5941000680c1d41c2d020706000f40501e030a080410758000d0012000024241303110203018400c46003c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 411868147 1250 411866897 411866929
    0x30b041d07032405013f03180e0c040807080d090b03060619082a070b0702010603020d0b04060b09010b181c260403081c0b040218 57
    0x590320391442208000100c000580398072440044610610385501d070001400700c28888445801c2c000003042402c8520041055100050300d103244aa07400d00c0d10100f41d01c1814101c00c1018103090300c07403021a01c0f90300c05180114607405685861071f265480d8641002d012640e0005405000804100101041002d00014885072024201418003040c0040c0413a0540c4117007490500301201103021569910100d941c2c00d40710019203101009c5261014140030000c540242142c60103115403c945000700c1d02e14001c03080e00304140351a100503542c844801d540c019100800319962a00c0200c0161a98503c1c03a0845004003100441c40c0390030300d440800c0e115003420107402100300710010044541100140ca190494860107400c105080301d02180e01010903480c51848004091f031880c0501c000080c800301000011484204a26aa00d515800501c91448001e042041c2080b1082159101c1d002c2c00f120110080c00104058a0b10f000140503a0003141d0480312203181d07071400c1c540c50319104803664807160b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 411869397 1250 411868147 411868181
    0x40215030610050d0f090f021801060230070b1501050702060a122009040b0d050c0114040e0c0306041803080c0d0f02070807030212031303050706020c010c030b04 71
    0x50300354003281002d0741c0b0300141d00c240103001c40c114078005201d800042c002ca00c0340703000700b12045150821003084507883e4801c0c0d0082d910312518503481c00a41c0701007030503540f86030000d01d041c2c05000d0049045070300210302e9408428180c1110f40c1080e512000072301500d8010f440c250b107141800d9003104103218115255505219082000300010f807640ba090310305024460904a905103039402c14a402303060007140c409001c0042001a501811013600908440c860a072010403111103035100f80580c030004031401400c150322100e42080725601c544080000c44a04a005a0415903070303140c108a0030301d05640c0440e105102004100b04d80c141403260180c0000f41324182c85000315503031800f520800001c0c042400038540014900c980c02c3d0380e034102c0c541c4524043c0c000c40d40c40406040c001000d8001040031001401801c0e00b40c09210100c4042d40c0c00352021144070000f168255038191440d5002030012a03070150217020f81001d13900b0a104640c1801d14a482c0402c2071111103003048211b5524913941c5400003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 411870503 1106 411869397 411869401
    0x3050c16031407080303040807080a170906070f0c0312052707051005030c03190914150903120604020702040b030f030a090e070c03080720030304021503 67
    0x382c0d03040035a075a068440d88200d0b103d110a45025056031070a01c118804111f103038000344001e01650070f1180110841d1200300c01c00c040101e84200319a0800002c1100468204941d1000103416107050208040a581d010300703120400601072010303540e59070001c6c044240504c01250f42140c900d07810107141910020155569100c2d00605001e5800540104140e1340541c0603280598491074601c0c2c119a02c22011080c4404002c602c401c00350784032001100401d10310203006223850040d0024090448814016105a01000e041c05031a903004115030240340703400c0f450a41e00b214003154050707511403650000030040c207404c0c810316615019128042c401c0d14000001030a15010a44503000c10701da48000c1168080ba049801314080341c0031181da140000d1040c0661613200020781004030856550001001c0300702c0800300c2c05000c0c0d500000501c020340c500840c84940c01c6880d104064558 = true := by decide +kernel

theorem cover : BRFrame.Cov 411690647 411870503 := by
  have h0 := BRFrame.cov_init 411690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 411690647 ≤ n) (h2 : n < 411870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
