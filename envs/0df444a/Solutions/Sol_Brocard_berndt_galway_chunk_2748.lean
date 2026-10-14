-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2748
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:37:56.592976+00:00
-- url     : https://prove2.me/submissions/ac947b50-5a6f-4816-a038-e3c7fc79c103

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 494064748 ≤ n < 494244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 494065998 1250 494064748 494064757
    0x60f110406030509010e0d1719110a0215070e0405090703020301110d0605120616030e0115080d030b1c1a07020a05071a03180c0d0c050f090105090106140f 68
    0x10010391180c0c14130190f803200780302d0030809825000013040b00c40003003d406032041e101c0c100f00072443c0303c0c41d40001e41144040103c5c44035002c0e00e03510400c040b801608c031607801500849071301d01c018450600c500e40d80280c4141140d00625554942a248040718070402002e04130052210f20075003c0d00d5400001a1000d0142c01c4140103040481c540b030365a8921414110f405c6980554441c4003071402d003165200c0701040d106e0b081005c00640712050405600c083d40a4038003d400048550f203081d44000b205120034400006540010068500c24420701000b2000e07601903948030756101400300740d1005258400030f0020802480340e240c3c0c1b10008540740708001c185504807101005a00042c0d90300c0c007003140502c00d1034080c3ca040e807a406000d04045070501040c1c04002d01880d00311300c030031580c410000c404108030306e4204d80003030000340b41986030303e802e13100401d03203102e03072400790701000b8ad820f445240c0140c00e18103031040540300b10b406030710f8583c0482d07080640280c0300000c030780200600404043c9140040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 494067248 1250 494065998 494066009
    0x7050606090c07060f020a0e0402070206030a0b031606050d11120712091a150d08030403120b060324100516020402071719172403010204060305150d020d060f1104 71
    0x680310600f0700300c040e14510b05c0801d101d209c0e41c410444840180e545400b500e80020400f40c00089181400c0007181c5030a0f02c940d040001225005000100e0300d902070300400881c12030712818032925034010014000c500603e03081d025400c26400024403000d100d031041544001e039614001c150826070303441e07180e40c0001076a101c9201c03018030401c0000d4014420188054143d081c0c41c03064103080c154865110724000a40024100300c0c050f595001542d040c1d4011444624006101c2a5a03090082803a20b2001081a101c0c144000c3c941d01c0010525001084031003040c41e64940600d003802c981c0101881c60382d520022030740127500f80441804980c100c20400a0004000c1105035150069440001c10a42c0b4011080412510090510780341780401621500090001c4901000c0e0540343c141c041c441c1c0c900074406800d584003003800256954036402103030268010000b010300c00e40b561030a01428004144e0080c0d000003030302d4403d00005500368066000c103040c200e0002902603002c42c4148207039210790710a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 494068498 1250 494067248 494067251
    0x2901021e15252705010203071b210b0708070c020402031009060f03140703020112090c0b0c03090a15020607050a1101110319050114040207050a051c02070b07050606090c07060f 77
    0x1500032020f0500032800c08240c140071101c2985241c00c0000b50340b8810103100912040b518108002c1180d5032000b403c02900b00001c625a40c2419005408080e805042c010390322210f1460100300c882e40200e911500892440c0d4500c410070341e0540030312000c0d50020741480350480c0b1810b0000340d11150b92180070041c29903035a480741d0207481c50174003c1c1c05442465880034240c01c240020401030303810030665145404051004111225176081c842800d40c0d00b5030114290441c0050341170101040131005000d010f004a442840a4ae101d40b00141018910010f84001da0b00850100321181c0c01030000d8041c070b0201d80741000c0c0c0004800550717030a4441d07810b003028450380080107001c0300110b400041404141103803400c014540c944801c00440a40003400700340030b02e500161303700c148070382070066005c03032030b0460201d980352480f000c020002c40400c011410300500556502041e0100d40740e040b603544030b4100300104081d032a103004200d03020350050030030a448601000008009003071401a40f0aa8042400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 494069748 1250 494068498 494068517
    0x230a090215181008040b150604030609020d0c17010606031a01081b1c0b060c0d030c050f03010f05010801051c120c050d110f030901020604152901021e1525 68
    0x28902446c00d0080c0950419104020000009807940c5d0305690481e83c00c100c1c08035a0210030700124100701503010b0040c3c008000d0f4076000c5400c025002c01c00940d0105100204101603a50b882107044a8941e00c000c298150003000000c6150f1003111150b401404814281809000d04400d03202550b000c090703c184074403645d800c210403c01d043e2180403030582003a200d0b1880c14110b11100754036005049010b005243c0e0321500f80307090354450401c1c1c0d40c01803101303466141d49584a50a909010405128450002d442000045458201a00c0c00c3c51100240320000070501020f6450340b2006e0400880c45041044050031080420010040300300b180c202510b800405d845411401da003400e00c41141400e1580c4104003200d01079a00207032042e4062303080084250208086c84044000e0040b0034120b0701d954808110030b181d203021250000040c40b1090302219440158031a4078801c066401c1104e000d25003002c03444242c15a2001c41259200344d0442c80c0300c002c442650025001054a90043c1c00003030401c21 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 494070998 1250 494069748 494069753
    0x40e0a12080604050106051611030d091403070b07060905010209090705030a05010602070b1b030d02070c0f05010305150904030c02281221030f230a09021518100804 72
    0x76a00390b00090240c405104640c14114003919902c10000300c20102e1605141040602040c1401c607055400d00800341d17051a584050028907204490041a00da002000110081d5180000c1e0314022102d13580580d0741042141c2d158000207244801056034155000c0245002c03e030703680e882051062004c1c0c0c855580b00d0070000d10075801c9a2058200b24255403244406100d20b070f44913000c0d02c0f040d560300c42141c4040040d064940c0d00318003c4501c1d04d0f51150020801c13070b04000411141400303544035184903401d950380c0c5000440c195101030798181c544813403030300d0220000e040800038507a00078020304010029000a40c04a51010340409402006a03100840c603e200d040c00a40381c401000401d0010b000d50003c0d40b50054554403042030350412401201100410500980010700c03a103000810411058101821b4404d480c1c13a50800e81700341030100e0b00015800549071143c069aa42c000c0d0000d0a096182158103903071b9400105404031903001e880c03190760155507100c040316014629940c0e00d01c1505003071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 494072248 1250 494070998 494071007
    0x1011030f0702060415091e060c0f02070b0d0b01020a02120f0c01020a11091003060911041b09030204050a0608031b0c060a020c150d02030901060303020c0a03031b02040e0a12 76
    0xd0704110864124205100c08101d5901e0054000c080580c0006003495a501d001c0d802601c20300c03840000031003d5000c0c0d40511100e58042a264090f548a4610105101c5022a2109000e020300c644d10b44090000140c0da034002c4d40704008410b018011201c1e007082a40000d044a55a41d01043c49507220307a200e075a52010601c100a2101d07428002032542009136a80c074003011940700c0d8110300440403840001c035076400d036410150007540c0081040125811a00f0300381c098207000444140182c0c14586002ca9a1007e80b80040e81c00381942ea66544840c11136003084040c2c100a440c2c502c0f10745d16268041103414013031004003104d281290481e90401d208001c581d05002d9091041c4d0311440007806041207aa4001c528001b000b00308683d5074460072001a040342d05c40c007070054100c00c203910101c200080d01005501c05c100742c034000c0d021600c80726020004c00c00e501c8024040100000c0310340b0b403080300c400222046960304030320041000c01c03050742441c182d500c0d18444034000d882c0f034203044040f00c00082d0403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 494073498 1250 494072248 494072251
    0x51c02130f0f1a090103060e0c03101d1513060b0306030c0105030c0d0f090f050c13050114090405010605060f120606030402010f051b06190510061b051011030f 70
    0x2081c00d1030681c1440c052580c031124041030781c50310b110390700040c521a04c1ea220f80e0051001e001c034903903100a0b0742415100c5840c04d4204a41c800c00d0003107c1b8202007402c54100303064003051041e41038440c10595945405500580c5491280c0781c02000403550049070a1060080001800c0650780b500e8984c603101d820503183c054150711042c14020708005001041003040125444008941804600c2050709080900144203000003d40640724110081d8108013010640480e5500116161450001072083e00000c0b41c4081c0300b02512001d010401c111030341407088603554064020342c00040c1007580c4102050441d4813007000d00c08011000201e000300d185480c50311b1a008007058500070f080d4034040c2e0010f4030642d103410b03201050103008144002014401d04c00203a06810307500556642d400e20f14154285030b07000c408246030040c104030024040c100001c1c81c8500316a015512224ac0c40c80c10742c003100042e98a660300341d0352405210104101c84845000d44c00800d295056040d43d80e16180176070b2200d5950 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 494074748 1250 494073498 494073509
    0x100e01050a050103080405010f050708040b03040605090105090309010e011806080601121a01080c07150b030c04090515091203090705010e04050f01140d050601030b040b2203051c02130f 81
    0xb4290051010941440540303003920028200515070100c08402647c0c02d01620350700422042e00090b020488003480340183d801984036520074044c13a16442c0902c1d007079420440340c00c0d046d94010f004004940d03200b581e2010f00c801c4181172840701c00074071940c651024207880d0880c4001c1480d11003400103a5a00620041248850000c204103030071510341c0c01107034042c000222a04101510b408145003071103010494101170340c04842c4c00c050710400000040079005140c4039510070f004a4000c00e8450406005801080350710202900b104010080c10625034030024041e200b07284100700c07002c0300c4080c006009602a02d00e040c020008549054001440500307100c004a0165042c80140000240300d043c130300381074507400f14140344c00e19070301408941c250044a401400d1881524000828080d4801426004a0040c030101c0d00c55a503240d00c049112946903181d2050f1031080110f08042031064000e0300014141d80d4002e404580790451a0059800001d508032840301c1c050410490600c0c03401e4010000c19 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 494075998 1250 494074748 494074751
    0x1d01023106030c031107050c040b0f061218060a1a04022a0102090a030606170c01080408030c070b0705130f050607020f060c0a08120915040f0f0203100e01050a 70
    0x255108080c8185035900c5030009040d00c4000300c0d03a041c1c0c080c0d000b010203922518031064413202641040c9035561030f14007200340240d1614802c030300c86080001c845001c50602418881c80c000901400844041000309030b420400041003c80007018014400e090007015400d1001c82c40d01c4101405419061441190911440c41000044d0340001100303210f10140c0c91800f0394142c0d02240e0b0115070302900c0b55100b410b0740401d14150203c10420a40c0c844010385200c2c0c0d500c414014441901d40e6a03c4000c41d0105000c80d094100140000b140b160045a0101203086001c0c20480f260baa43c02004034151100c3d40030603c0429101000154014480000d21051418121591820340400c4c100d2140ea08064080c00110003602100d0700c2c0e92003102c4489584d5800c41c0c1104206040541042d0042d06040d038043d08440301096901e0400901c0501440d180d456410544e21142c0c1d078046d80c24a8400101c1e154a444001c00026981c203104424900c240d441001c100d8842102a003030850300010251241d56 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 494077248 1250 494075998 494076067
    0x321060904030804020117091e07121e05071d130209010b0904020712090609090e06180a0203010c050a0201180503030403180b030126010525031d0102 66
    0x503940c001000e81c00c1500340c20a43d04a844600040301d4020804000001c003807807a01c188403140c2000910701c5240c92440100170041d0000040b0b107603c0390342501c207504080c070310890201c0101e070300c50102d011440451010380c0d420985c1c0f035960300e0030008a03601c0341c0448036405c000c109005125440443d4082e1002110410050160f40001c1400006000f032071180c1401050304034094441e94110303110141c02c14079010340007410501c014081c058502901000034014a00050320603c00d008895560000307130050a41541d5040ca031070f2503111016400840c074410a040b080243e282071041003102425035488941d2032003610b0340a800e45e00ca40c00c1d521400350901c0a01c102013800481601c0c0c2241c0e1514050103014400341c5c040715900903c0c4c02044601100000000f101d030181d0202c0760f500c80c0e400150a000400f40c000c80e900b00c9100316031b01ca24181e4819182d112503203130b003c5101044151410300050f002c2c0ca158410b105081c01c6421010107070350000c0c2e00c2003104403810718100121003500e11078820 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 494078498 1250 494077248 494077261
    0x11202030a03080705160506010609050303031e1005100206041b0803040b0901020f0607020f011d060a11041a070507150203120603150a2405030a141009050321 70
    0x541e44008009400c201c0c80d48042400503201340304031105803400545404100d601c905009464010070b00ca004040341c03540c080041c40341004402d40b44038114802c9000210710080c2c4038290706a0008024410700900780c04081416559040f4140700103a15034000e24161070203160052054920407162202181e01000c00c1012840001c200c1d400c1d180000342c0140c072030629400607840c01c180301c0500d040714081c2800700040b0603400038586902010b603000034406807155103d036a0340354214403070680d02a0043c0000400107004d40e00700688546020441742c2c80e180c2d407908400705540113035240020321040050342009111081005202821a590059581c00c42c08203003c1e40d01d1081850304800c84c0d15203400640656400c1c45003400c070b6580700040702e01d20700c2e000d603883c002054509482c5001154910214585d103400d011f4010036118007030018a4441c4c1d0607103543da0f07050090050390341944180384904c1c061142900551a50500c071305c00554403407100b65a000c1c1001101078580c000d0103910800c0010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 494079748 1250 494078498 494078503
    0x30a0803191a0307050f060409060e090d1803030f1e0201061802040803070b0901020d020d020d1d03030a1109030304060201150b160b070201140f010f0501080c07060c02071a1201120203 81
    0x44803002c80b5030703901e0b007001c03100812600c4c0238036440480d0143c07610304006100d000144903144201d0310b520030343e1281e0b034050400340c840c2101c62040352440b40d403501080c80020b000d101c40d600200307241d003001d400ea2041c0204407501f40005495030310060b515400e0410024a610f09842ca88004000040d404c03e42031420040e81d038021b001016200c3c81007003020544100d802c3d4100c0b5114450f0200071340d962a0036180003006580200354280482e481c10300d00e80718550103410381b2951962190059490b54607000d014001805da0115031007154042003000e040655801c000620081105030000b0480781d0180980641007500d40d4420401c3d000e0420011030a0049403083c281481c1e84507514a115846e0740804a00500c401c54504080031140d805010700c0420358501c05040b154020066400c0540310801111005001c0c1c511002230390302030003840b00080d1543c005405170a060302c121122559580d200300e8a400c0c082c1e900d035904400000d0f410007202d15460742c560250009451410400081c1d601103035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 494080998 1250 494079748 494079763
    0xa030914010246081e030709090203070201240608180d2003030708060a0503032b180c06021b101404090e0606102a02030a0803191a03 59
    0x60f0031031040c031a00e890604480100d07008102084200d012040305524155031320794001040b142d0b403e01400c2252030349a0010341181d201d80d5a66441c40b0031350740343c040c501c0080c0d000a4002030640d500c0302030b030740100104900c40070154002c02c0c048000d01480c017039010301210b03405807400030320700c03007110244110010004445602400616040090415441d1240c07a058000c1020814034000003090018495201c8041802a03d0884801801581d81ca04141ea0784c80740f403003034044619105005260014814072404000e011030500490305102c130308a2212401140c010454a500b2000020f102030381e81004000325900325410075001c00d5401000084400303240403030302e40c10080042501080316140c071081e28020b007172042c0140801c2c04040c0800d600c0380c1080300c3c1603003e003002e10300b01e0044a20a00154408400e0200014840f45090b00e003810340403e2120309170b07018032505550f0340000d10303104011440380344c1e1207244260301e504050100e01aa090140e145002d2154428060780541c1d000c210300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 494082248 1250 494080998 494081053
    0x2603071b03090e09010209030106050f030c1c0606030f060b1e2206060f0311070803130812040804140f031b0a0b0a1112070b04020616050a0309140102 66
    0x280511a14a41150100c802e6002030003e0000c240611550000540142c04104400c074000d21420740c841042c041c0c81c017082c0203025070550100318001000d040c0f80d50b51100c5803405d041003884440303042d183d4005076001c0b03600840b9055200e07040c0303d06000c154401d006916104a504402469255040901c1100403100a40c441d02141074450000d4611000e017030a0b50120107014041c207503413090b01030010040c445034075010074100012504180400c0702240c2c0350780e51042910b821902c80c8004210610394401c406c4131014030411902c4190310b00720f2091840395125402c07181d034440c24001d05040c080e401d503141d40c0c01351400002d072000c16a0045205c01c010562055000310482c03044000603482c03007155014461889000980d500031700d0b8094138541d05070707451400700c4898005a01c0c0c0d090722071217210b5016050804000c0414018603014000b0b01c2c5500c4180035004011582d610383c141040d0118600306c0105001e0f000801007041c0c450650465140c090000e8103180d210349444009031002d20a05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 494083498 1250 494082248 494082287
    0x30905181f14040506060c1c0f0503010e1302130f0f0b030a050c090703140a0c1403090a150603081306090803090307030605090a0b070905030c1f0e010e0d260307 71
    0x1410f40d483c0c41c0240c032030340c0c0c03900b404075002420980e2a4140b448c6240414070001386500404880483c000c81c101da04a03504e00448c3c4010395900380b000f00305a0b42501040fa030000c1c00c403041000b010b0031801802c0c0316045035800020110040d4000404a4816210850081e0064a90840850808210002c0c404d106a8489446980300b4900320010041500f00520924440742030010400d01c0790321810201809840e890a401424554000d13240001c98144040703030302c2018400001166031204a1003003440340710203d8a075441e643c403018188c00030145900780d10340c1c1c0300041003a960b0148480000701080d0004d0b501c0c1404003008039031a00144d000291a850310344d8085001e180d410090084e1035604004045aa424055001440150b5034843c0038464492000b50f940580323040e81c0a80001100c001c010388100038000b5003034a40b00c02103179401d810310501d80307c125015154110020076861044941041e4000300e0000800030340c2c0c000070b02040300c1d00305008100205030400807580940294110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 494084748 1250 494083498 494083501
    0xf04140f01031a01030f110d020309240a0c0e0406080a060b090709050d02130e0d1106100e06040b030d0507030801120203060c1b010f0504050c0d080313030905181f140405 75
    0x20380c10b02801fa020501d07044004009078082c03080c005540030310302610b0114103035400e40045900640740c1c0200c0600442d81d00c1455008510020040e5002c121740c140141032840c50181c454001070200d0b00d1030752000046800c1051000200704e002d00c9411012542100d000b00325042c06e420090640081d0f00a05004414481c5640c1c29075480000d41000201c40c0030007400005500c00c103054070780f01020400e0020070746c8040302c99020074020030164404c103449688a8162490f040c0091000310000d0044c0b0380082d41c644038008107407002d208204d0782c01c0711515965641c1d240d44c40c0050440405a104205405a0011400041e607011403400e40054610301c210344c460b0202d0a00c1c0c0e107084404082d12030250b107080722420016031f150b080144034030300510075501c1c03031060102071002041c040a802803076100200002446190011b0a1900f82030092420079807240c1c4070b10201301c10184541c11a0a507407411020410304442180c007001010f644016490310880c50402201c6a6240440186120310388440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 494085998 1250 494084748 494084771
    0xf0d0e060409060f03050d262a0307090f080d030504051006180b0319060c1b080c06070f0c0f021309030f0305070903030912080f04140f01031a0103 65
    0x3010703540070b000c200c1c07010040c042ea40c0e800d0b103003031121301c1c4400c0b030702c42c000c40c64944da02d94000c0d008944401140760302000451a01081d151580c01d00030540c2107060400844031551a489146001e15034000b00c060a42e203041004004e4400700650340400e1401d0007216041c000d0140c041201d141c100701ca401c004c1965290b0340b52403401c000c402d501506000f4981a00002d00b130814001215503020042e070b08001042c030040c103064540308000d0a825001c241001e4601c0002c4440d03101c090b4000040c034080c91018201654880a03020021080c2e521401c0401d10750a0000140210364103c0e845043c44680e00c11380010140c00180c1040c2d000e002c0d00915090441551074914102e070343c030107018104000d0b0602c1454081c01b19482c07145d0110000b0325240019140078002c0100001b56a0141c91789940d5a02d004032802440c00f41060440f0340d9201848145402241e28004d8000b030301d0001030402c00d10126400340102070482c0c0d0440c40c1014180004101e4250754044040810013082c82c000c5880802c46 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 494087248 1250 494085998 494086009
    0xb19030c09091a0c09150a0518061b0a061b020a14010902060a03050a0b0f180402120312011d010b0a0507020a03021203040e010e012103090509010e010302120f0d0e 72
    0x81e00803500c07840f8680304002c02d10318040c2c014001680100e40c501c858400100c0703040e400d0b0003500410004620108020001e800c425000003040220040100f8906600001d8816483c000860b041d5142c0c3d01240c4903a0400c60300d400740584071700740e01611034031400c03083d14000d581c1d550040e4007600741d40b036418401050041c20741102150301c0e005411a6a144c20310400100101803c8502046403442e01814101c40d140910305840444801441c0ba1105a56900903081500c006402240d01400c4096207280001d000d202500071640c0000b07180796150300d802c1e0682070007102c0c680e031401c5400c800c100600203c855002580c081602c41d01c2e00c0e0b91941564408100315014a0300048d50008100743d00700e241d150004001d10513584820007140459036074088000904e607080c00740490000e426600b250205210b1441c0d071141d50b000e0310b4015642c3ea80d84021401200d02a0085010300300b01200600650802070007044400103000c00400c450090001000d8960490388100c0042000c04c01038069a581c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 494088498 1250 494087248 494087273
    0xf010f0b03100e0d35010602010f0e120d020d0f0905060708220305090a0305070f060302041503090807080d1409030c06010605090a031a15060301060813020604080102030a0b19030c0909 81
    0x11085c07281104e00e0030622110000c03400d1241400643c20600300301c44070b05041c002c40c0c40c0609203c000307146047c0344440d80161504141c20b0b0210070740c0e081c4500d54004040340121010350104100000d2a03d43c0d0313040960401c8001000502802000d00500c00a0854140007003105aa0040840035150303407031600f1202031258401c0f0030380c40b5100c00d002101b400304c046919002c41d8050440040c01554514058060b4041c0b442a44140e09042644a0140d40241c00c1300c09000d00c41c00b80c40d441d103009591012079a420140d2000c42e21551030726409034190310860b0103034000112600071400c01d2000001c0395aa6041402040704128005c11201d005032500c1e210040655440441e540396071010020843c1e50740421502d082c04000780a41801ca542032042c1101d0595240707603101301aa84d00c00c0b03481e9a08840d0041c0480e00480100310008078080284040e5005040c800d5000c92901180400c014601041c082420f40c1500944030400002da29240c01d00c3c1111880513000c174a40c40241400c40d0400760 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 494089748 1250 494088498 494088557
    0x203060901050906060d050a12050c03070c06030b09060d0201030b011b050606190e0a051b040305031b0106210809040e0d02070807120f050f010f0b03100e0d 69
    0x54001400203a1606400c0b0601c90f585520840310960784072020130a4160015001814581001ca1a4404242224941d900e50b909a00700286422602d0182034a90b90100f00281c40e25540030105201482e4980600503a4000c1113882c8840c81c00c0040004420740d101d020000e042c180d45140d52880c40c0d004014818900101c03000b91440c0c00340320b003081e50301e809084600c28451400c1706000c048001c00506007109a84889242250903640c00c040c0d14010704014120140341c50181862024211606000304041c620800c055600d072803400c0c9030001c0241d184501d88080e41d04240041c05240d01c074050140c005141d61a60800048090405005c68441c60340d42c142c0203404c100c105921301d1400120b640c0043c6a80c2e003211509640d81502980750300f618051005046010100d9030b01180040d4140d00d1064020070503140404100105d4908541c20009070901c3c960322852200582d18040c0206c03560701c05415028450b40c1605813440791a40c01d80c5850500b0b204241e4110b50307960100d051140780b80d50303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 494090998 1250 494089748 494089753
    0xa0e090c1204020d1403040f1e05150403021921020609060a11030f07030f02011b0e014103090303060d0c120501090b0112050703030305090f030d142d130203 69
    0x5e4a071803954499019029500d814042c00ca00002c0b090343c80c01a06100d412404200800613040c103082050300b603110000600070f11030910010000d69990305080e6519482180d0031038007603140c2200f240d0040a84030071a649001145000e00150300d441c0f00b200c0c00120300b00d5040d0303600c0040e00000d692560280c00b000da1503110200382c50702c081d940718006001440c007076101d81528810b1b50700203d0a88804522100844440d011510103850241001681540050611f000d080340c8128806040e4808580b0704d403420804526110f070541d0010704004250154030862030702c2c42c5001200c0303a0742e87c403002d42a103014042c12305140062000483d204000380104074a04c1a201c142030408601904401405454080302c40c000000e545c1d2940340f040c64202d81c400040c0410500c0d685050300142401010000e0501034060b24542c03040c401d000520000c11604c0000907800c40703500b0300c922902001006401905280440c050540f054035800e120041c40b549000640c543d59144000304040c0111802501407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 494092248 1250 494090998 494091023
    0x30619110c0f10050c1903110d0c08040c09090308011403120c0307022e08060f0409031205010e070c080c070f030305091008070e120703080403080a0e090c1204020d 72
    0x203402c04101000c1e4014000b10500464035010200701140c031030101c0f003c1e01d00d1007040b0081c01c214040e401c009510441918014140020380700c2071015038412140c0b0038002195001000301b04000e400e0b042000c0d00c0d40450410581c05959005806860180a4018251015110510705542c108010708a003c0710346981600d90f4429401c2d103070350b6001301e0f00480c410401e0091001c000c0c0c598605010040031380e4191848200f01c80502611b000e48060112343e0000c140c040c051850307440318003c0d02090351082d0364608410a6540e400070848106800c001c044442220a004406a00042207000c280d0030090169031180e41c10500f515220041d8031490403552050000421715401801034084500e0684981c550b06880320302c1102c0d40c49080703d0501c08a016851107a210741402c3c4500e481801e110000c650f2800d07125110220b440d00136900458031200c0c0020080041c0e80e0000111801a0b4240c0b10b06440c0e0404000c1c080250080109400c00c1c00418000582556a0050a500c3d2a0740150088412 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 494093498 1250 494092248 494092273
    0x50607080406030f022110080d0215150f060307030204080607050901020c0103050907090917042c04110d1b180e060402132a020105010303030b030619110c 68
    0x15504540b0a420100c1d29221306001001868002c498000c10020380218080c800044509552840078080209070115039002240500c0104503980c01c51035940c0051441038144198841700c0c41c07009000d140c104928411098058613062030320b020103207045400c0382d2a0755480384101c0090040368032030201ca00c11542030004294029006109541007a400c0d1010405103000650682d90141c8203072680d903024007401c200100e09075003c05001880380c012102c0401c02c440080386076401581010001e0140b904580d40056800540501c139200f020892110b1868103454908402800c4000640119034429a800c10400c810012401d1205515034105685840d10001c0c4c101a8185010b60000e520302052240100000a0021b2060740d00070054228600300ca900d400141001c2420030520b102040000303101c921103190035034a64609035000203040e6146040003019200d00040841c003030341151084c044401b00b840910942d6400b07400340031805160011499886114100aa407003c1c01801260030300f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 494094748 1250 494093498 494093513
    0x1d0c09280902011202070c09050a0207050102040f06090e01080316031e120606020312190605031b0f0409030c03030b12030d0f0b030d0203070f03020304031a0702010617100504020a050607 82
    0x400038002e0341c4d1195420045901902280300300b210150911850b09401c002460300c5030042c6078492094407016003007030700c1640c1c1c060076600240c005500016043c002407142c0d0394003a090600034910391749003080e503514201c442da40702d100d03031000580c0c1642d548204005050040384070100c26010f200c400300c404100014020a0116140d0001d2503582c14124001803030340c07000003954100721020b00100e4454960313110b00c0618141154031041800d460b2400060703039a500340031080f001031145220907990003400e8108a1204400c0892341d105a180003c0e010100c4d03400791011544030390608000816040d20000076401c9058880c4581d903074400010000500602034010502e10050386e2401d0000c0b103a010100f40d1151384508a940040e4030521032000460b54040c0c02d4070016019005a07403900e6200d4480c060800d580c506101d55203011001444050365091064074010700054084000072a6901152910b8078480b081c0e1380c40c0180c580e0042010f41d5035803001e8400401740200550b80d1101036190480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 494095998 1250 494094748 494094761
    0x9110d050c100815013f150b03060108041a0114040f06050907051b0d11060a0c05040915050405040c1a031317090a09050a1d0c0928 58
    0x34000c035240300030460003d003e03c82860159010b014821400c802030310044179030350150b1400b032090610441501003042001d08200c565802004900e42c60369159104400c107440b2046034202061f88224010007001103408203581c0c03c00070920344008142c890f4200071000101150315100c0000040d400020810712071205a01d0710701c42524180640c229907000b540c1111150b22640380c10428000005044c284683d00501100345003c0b00a0054a0400003442c81d01e0f810062050101303c007400c1500c070101c82084050b500403003648007840b2000f00750308024168040ca1144208103a191400312403040c0030b00446e04041c3c04040c10810041c0303894240000b01805030322400c2080ba40f101400e1800408035402c80c0d00c1150f0540d106c4190036115a550086c1082d420b1304175581001c18443e0325035641d40c05103018000c00000002140600300003201c0c1007140c040b090007542d036411035403501110030404900c1e4100c04204842180041da1000c42c0103a2403591216580d142406010342c02c00083c5659102c00f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 494097248 1250 494095998 494096023
    0x30c10030605130603020a0618170c09011e180207050307060501090606020307050c0d020103110703030501030b0c130b0f0f0c0102040f0510021b030c0a08011d1f09110d05 75
    0x91040100e070034030f10002c4540300d0001a401c0700005c074040c01114041d0356151603000c0c08500e10340c4501e0365101c2041030002c4941c1c1008242d005144100114a8100360503400340a0101256a00580488848004110714851000c0d2101045e52189500c200ba5060f1003103540c110741604d40d50801e0785030240c0140024064a18614601940850034034400415540e405512500520001d120001003046264040304120304160700c03050204041c502c03920142254520030b48012a45504502c1e00c424083c10003400313000c2905051200d0a42141140440000c54a04c040c0841c1d13142400c41d845803192056058100c82e44800080c02171a100d4158001c0c0103d600d500b401a070314a071904c08000031403040101004c010b81c0b185180320840150001842b008030002400c40e149008203a01003004042c1c0307584030f04a6070b50744420381451101c0b0500b04600d1307454140080d0072400c0740440c0c03800400402003c2545026526885c000400001e02900810301e500100540b074210352500d40243d0f18254400344 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 494098498 1250 494097248 494097259
    0x1020f03220201051204020a030f060c1e0c0f170301260105040c0e0a09060513063210051306090c0e030d0518060c01060618061d030c10030605 63
    0x1080301010815108070001e64160360b2207290441d40c0d02002c03003003038000e801660311041c54030001000440308034002944922620010030060140e020103000305020518800228000c05240c469044e403102158984550191102212501070305015490344003000140c0c0581c8000000800c182c09402c048850305d0000c16048809884c13580329040c01d0f127030f0540d8010640d8881c40b50500980304d944403031980c0608029000100d11446417205401e80d00d0507148055603108140d1007006000c1c041c040c0701810006403101006003800308140c1014648020209400052036a0108070b0892103e84460010100242091160001031000c60002d003424414103266a00c1c1c1195200380601401c04120907410040182c00009200c500540b0f03d603008000c00c102011410b02011010395402c0040c3c1820041e01b40005501760600700c001c0c252800c1403003055407400e800380c010860154044111820b41031005020022100d501f00807a00e4120320030380071a44202c03407800d00040e26038164805001c440d0304a58 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 494099748 1250 494098498 494098531
    0x4060e040c0812030a09050c03011e0c051804020a0903050609061608160305090307020901180c180614071a1909030806060a0e030a030203090910120f060e01020f03 72
    0x2c1da9503464143c2220b140f4036110034070019003801e149600c00c0035141d0081040d15194441c810002c0d003142c411307841d80440c0c40c004d000344070748045c071512901103c290070b1b0410900d00003520440e194142110b1554030308c103540008040d51500d2181c00c1e810001d550010440d80d803402d080d0340d01d54841004550300710150b050450000c1105201d0a103003401402d855a0384d2007902c0c0b00c498101d02418000b0080a00340c882040074800580351142254001d14061100c00c1e50354403400380c2002503d80c0d5203040f0381004101c0c4160035001c0074010904046580a0070090340040420840c0c80c8240140c0e0710207000001c1254806090380d88910503248907aa014211800501454802c40200c80000c0406000588824001111820030600034016a0983e041c0340001100101c0001d03d00320100d00210b0045e00081650440d03424803d038004e8000b801401740c240e101d81010002600d074201d040015140c941c0c4c2001c8001400b489a100700c01d0942810001e5588002390400340415500c1915205019429000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 494100998 1250 494099748 494099759
    0x30a080a0c030b060306040509010204050d0516060c2d08180103200a0815060a11060a0203061309030e030118020a0e0c0412081201060c031b0b0112080904060e040c 72
    0x3c188601a103000303200d90f00310746610051000a0800901c03186a0b90750800c00428103907143c401c01c01c0094071440051454078034040d039120001d4603d03070000c42448000525880000e0858034140d0a030040006a00f1580e0031115418820944019002d429078900060880c60858400700c600d40300032003a20180940c40410b54640d980c0d046080c0e95400e4000b0601034452824400d107511500803412a20700c4441800060002d03840d54000149680414500000140826424030600790b2003d2031400441c1145405004525410030b10f04016200b260b0382c01040301018010300741100c2a010180003040840416001c610200e15904810f0744907003012100003030001c4802303030f066125140d1360b45418280f078900070032042c0603101c01d50308842d640340c140310041241b283c3c2a6054000c00340d50795001c011054604005e40700402c5940b600b0b5844450410810201b103000b4180b5044500e4103004000207541c5007450f08403402580c00156000341000e40000e5101c800c2e13a0b050b8062030144070180100c66446 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 494102248 1250 494100998 494101001
    0xb030103060506012f010e03040f1502070b12060d0c081e01020304020a090902010c0f05100c020318220612052406130f02131a04050901090b12030a080a0c03 69
    0x111030250084c0b1740601068a81a000080f28108a07018000130901d00c143e19041802d682260b041450440c0810701c1c10804041c081144241c490100e0000d4010981042c50741d200602c40c81070222400c02e02500843e5440c0c44032110201c144d83c0100120b0b01d401c3c0c5601010b038a0b0702d12202e0b01c5007000c40d282034804100c001032084a0145a00a084033402481c2901c14000b030002010207906000c405a0440301184a075120003c0e00c0d4414000b82c5010084117081c401250000800c0a0440d482400540400c2d0720700c0d455042c640c0c0c400c40310380741502c484a5100202d8081a00e05214050400c4000540c0305012031030300d0300c554070032010348414800d004074249000b030040c1d0502c01c0c030040b100042203050400307400c40d8a203242ca00e8030108088115201c19403c2e82c5c00070383e05c480303140d6000804001c4d410340d040040e800c1118a4414030b04d480d2074940013615046060081681c2e850b40c485801489a995001048080040605607078480c880480d001d030122204031780041a0f64245035920fa1401d01c00d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 494103498 1250 494102248 494102267
    0x308090c0f0d1a0a05090712030527040606020312011e121a01080a020907030615050d02040e01060f0305130209150307031403090307150f050a03060b040b03010306050601 75
    0x15140c01d0001e1962010003000295070302040c0c504600c0c034035141c40c10f1041003582d0b9200b1401d40700b01080c10b0a20013aa10300c4d00095521030300c00140964100320010368401c084a2800e5004510720519035001200440300081e403454642c0d10519104000030401d030040090000d0000034103446545070707611075070052102c0141c8a040d807115a140ca060015426454803910f0840c0200c4d000c201200001d900300c03011034401c1e0011801a030004884038218507095a80726840f90003450309005c0c1701d207800b0f01044a078070405020b034284207001c250f80c1901c130f1450f4162401004040e03960901560f65200181c814040c647c40c001c0040c1c00d003c00a038100550b03007400b0b420303a503020f0014079082da100031910010002845c21070b5032501454000001040e0106881c90301000f03a9405144e882c4050410589008410303400280c1842c419a6101840ca402904e03da800170f029091580c0d80b4801da03074045000b170003d80c0018201040200c0d010a9200301c100145041e02d01c00c00042000b40c43c9c5c00c0056034000031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 494104748 1250 494103498 494103523
    0x40627062315070206030c0c0c01020d021e030d021210120203060406231005121504121416021309110f0315040b070225060f0e1c030809 60
    0xc0440c00c000c9982403003910a00c01c02c01e40200103003400320a0380003c010754400e0352042e112040120305413850031400e200c140514a424001046400140e50f07000c0d48500704c1003411f1004400e0040f0120105401380116410745d0903180c0301f155038403081d8006d29150b1070150741c1014281c086500200700001030160354a4080d800900804960b0354a42d03d51000d40f4070346540701111138665141140b803405c0c082034540124030b00712401ea0528100828000154621721071061036601000c41c024940d001a00c1103500290031040351606118442000d840c07844442c006071460441c009110040c50f680b000e80c0600d040c1c401c883c85528003030540031a0003900d0003041c004c3d05d41441518001154945000302e115603010180680e00501013071051040e035010111416220250804100080150305011b11500c0400003c884185c011001c001a104500340b409040d00b03000f0f44040c1004d6290013140d4412080c1c00040122604082d203920b925902c2036000b40807004a0507050102c2c441800124192500f0354 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 494105998 1250 494104748 494104799
    0x409020d091e08040b09040b030f151e011232060106050403112e0e040b0301110d020306010e04051510050306030c0607141501030506100e0408070204062706 69
    0x85c04d040300d0111540c00791000eaa40181e0f0f44001c420399440c18008562510910030207010b008121803100c11101000034103503445d011002c416031f0320000b020704069055890410010180c0e40940c6008409040441c0c0386044024060010850f44051000e82c00c40c0e00c0003007010707118280d986507015180341c002d0b80402030075251072894241860400306030565554240c400c2810b181911001c0480181c0394161504000403c140700c1d0701c169007468058120540d0b41079008001c0300c0301410300c0500c94000c1c000c41c00350f49038000010600ea6032103400403694900d8001c108100c41d0404000c120011101151018007901254410303060f00c6015800740c13031040368041d01030916108504100906607020031000c44402000491003080072000304540340c01001018504425541513003011441c21000400c41c02c40c80082c07840c14001107040442880c1c0195112220300c2d110301c198800038010346515080113007244003000418042040313961040e100c0000032001040f40680300c0b02110700c112003500092103200e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 494107248 1250 494105998 494106007
    0xc05190c1106130810090f111f020d110307020d03210507031d15061203070c0909030908010207050309010809031c1b03051e1009050106020106060305010605070c1a0409020d091e08 79
    0x60313800c6080d900e1a540050020640d40c101406107181d15110542780c00060f4810302c8045c04c29071b08030303255100803c039032401113042407030a90002d4510741c4060001410408540160759030317600d004100b007401d481c030b0381c5c02405140340034400107005000d4000e4020075058076900170041d03030300007041071104a80f0400d1078803055038415007805082c4034840e07407015035403004111b00004a0000502000034080e800d0011800c1c05071401c00070714127281034000500b44e03441044880d00040002040b02c1c2c076144203003440c5009035500d0b4086030443c06060446a58010008035a07480c1c0d411991080500c4c114403859102030700380e610400c40c00c44000b281c0d80c03070130b074070146503403410080c510b81c0c001c2d6000703d90034010b105041d282c401050a403070003a0f10400260391a50301c244280ea4150049501600d014035190f030500500383ca0b00c0404042d80e00c030312014500558424101e6461981c00c40f00680b20600c0301390b54400d42100340d4402440240401e455890007003280308901400c042210031000c2d00082c2c0b040c00c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 494108498 1250 494107248 494107253
    0x90f06020a0e04061203090e01180b0f03011e0e03071e061d0a0b070e03031b0c0301090f0204060807061d18011203030c05190c1106130810090f 63
    0x2544000350500a212200c100e8204595440c05148017902800100010908007840d01500e00700040d0801d0091414000060010103140204400583d0300e000c408900d092402002c2021011400400c071b41550810311406a45440004222481e0100d041c08003c070512140e0042c1d03c3c0e020b40d0744000c0540d0043c2c403940d03402c5140c0d020030005d02c500a610001e042001d05418003000380040e94441080c1c1c11040c246824420000c1d00703075174003162905001d0050251400082d840f40304841020781c94542802d46120880d40802082c01c800c10090000c010710310342410542014a420030040b4402c1d0708101c80840e060001051080c00c1740c00c0d588514100642c1c2c2118241d607214114000b1743c000400d1042030000548072040903000f070001c424541c1a410f42c41c14000d0507901d040150380180034040259181c5d0600399144014a000b003403609200c0300702c00b4a041550b1030110380a03d13030312603008030b0b042403803101c40c0718603108861414003103401c020344010b0000207a61104601405280c0c005480001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 494109748 1250 494108498 494108501
    0x50a05010302030613020c0703140a0327080d021f0e0d0815040c080613060b04050d0302011104031103100b090a05041103120307030b01090e0106051308070e060a09090f06 75
    0x100900014800c1d240241c615064404a0704a1074007540707a0341c020542041400103400300d001600f4034207009043c40a006403800f40103c00c1075900013705551000c03100d401540001c50f0300025140407410b6800c201c0d104a00203640fa40100c80d10300b000e80052140040d40fa0071849410325a1800c50702411504200c0401569041d900911400034407a9221040c141035032248105840490680c8079901e86007000300a10a0f490790309140c01049a10704241400140040c3c8155801c0344c1c1f044502900380480c62070103c0c003500c045016031590900205000c010002d400c0c500629040c026811900c14802c600c0850040c0c07000c0e80a030fa0f400c00034010201e4400360b0580c1019511070b00510030340c0070400c95a0003207480c044030201280c10086010003445200c40d410f00681e400303080c0900e041c1a2407410082a00301080e018401c0e034003402000603030781010504007a074840040100c00c090f580a075030b0340c4101d60740d5020304a070024810400030401107101c6e0024480c05510301e0b00420f50400c9410550b45400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 494110998 1250 494109748 494109751
    0x8100e04050f0304030303020d1a132301030503031b03010e01050103020702041b09030b090c060f090109030f032622020109050a18050a0203070f1b2f010207050a0501030203 76
    0x101c56000d01000500755100c100000c20041d480707941d0040ea00c03540c0128005c1101c00300c1d0701c01603141c03040c100c1656565440c4240c00194210302a00000e240c2c085200d01400040f501c058980c110038024000414800003001840c8141025805580c01403030040b002020381c03009000300c0c0413000c041001132119520a501620116201402c005075004c107030800e00204001c01c15800000412406c02132040181c507101071030700140d0b03110061141030000000251f10340240c510144100b640403d605140e61302ca00d042100443e000700c1c01c601301c02e8142c1801171680c00c2d5010007801c4003014a1100010700b05907081c86100702c8007054596034600300180c44941a1100c02c900341d04001c244000400c8036500d0a0000c802800284603030400e05215103500029204020801038483c2d1040c01007140b05600100348004031151071070b003551308408505a500404020030000b50100000000810146402c0c4005e100031104005150313107114030010049a68440300c1c000e00c1d0704030020380c0c01005154003903000745 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 494112248 1250 494110998 494111003
    0x30106150f180b3c030a0213120b01060212030103030513050621011202010e1c12030212062202091c05010c1d0612090a0b151008100e04 60
    0x510355400803010103a2504030641000b0740880f400030740030591081908541543c03207a210112000c1c0400f030240800000d00780c100303003001c043c0004006201d0140310350403030381c0f06450504c852002d40c1c1c031018110f4407540503000c1243e0703400130b110001c1500e500005d42500a4148400807a203140c0c00c0da41e04407205e806c120f0b603100c8042008c003000718442c2d4411000d040500c5404001c2901c07540b40640e02c400c005010381c0302c1c528002d50500c8000161340d00c80c0d16210958002d40e040c0e0111401208504140e010040018100c003240d030b007650300f03082d505400828040c40180d646440702e448807010094200f042d402c060050301d1040310f8050b101c1582e60090034400d00014103101d122a40c4158044200300401c1c1c080303075030317940d40c0100e4150755400c05403030003d2200344d24080c40441d90900101703a5601c40e000312510165070a50004103000000c0026680459114848035258240840f1000c06426020003c5115041a81d10038074428414280c5074806c901860542c03145c18900f03d80b03848907290141c0705 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 494113498 1250 494112248 494112257
    0x3020306060d020f090103052a0310020a0c0501050f010f0e070f110f06090a120503070c0f0c03140d0207060f0801050d0c030b1801050c04080327100914030106150f 72
    0xc03581e0740d43e140005c05008502840280440001c03c000c003150240e0495405a0380e0b0320780042c11000350303e0000c0d522000600e80000184c0c0c134424140d05031980d64111000070803540c200300410084000780d40a550484a0203407c000c5c1e03150700c03000000c031400c0c0700f240c061001646040d1312104283c801c40703c0c096004001000d035601509407900480c02c02008403402c04090f401800d024041020910441c22071071a945415811401d015034000c102c00c3c1040700c040d028440182e800d80610402850000085a02c044d112141130800440700c6c1d21183c50340011800340c022043c001071403a025074034481400c4003e561702c0281d03030f0030f10301089283c02e003a0302c00b65009c2444100220000b030420407007078000c1424800c4502e2a600745560035094580080880000000601c410001e0351303000400e4031041300307804080c84861034440d10681140c170400780800fa404584010030a800b03540000b11002a5942c0e10762914038112074800345800e80383c280c41003060100110818400b03080c815000e0050b2030b040c1386403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 494114748 1250 494113498 494113519
    0x2030c0d0f110703030b0f040b0604060c1b1503051b0f0c1509031207020d0c1203110409020d060b13030b070201110a11150f010501030b030a12020102071b03020306060d02 75
    0x10000390070b8000010440105e035565045986e079142c13500707403a102c00d48100c0d020300c10104603101151041c0140d10605007030000e01d40651003000303d00341048031255003091181c0d403583d80d9158070300c0e0107034001459040480e24120214803922446501e618000ca20010030310300d410b00341101c8404e1940650400342c25406510305115140400400d4103001d0641e6000654031070704011401c1d201010050008419540491f22241406807c0107440c0c03000d680040682900001c24041580600f18141c03110310812000100132482407400d40c0606031040a0040411541c2d84410301c100441c868214080001a03c0241c100009407800200c01e922907910304c004034001c960002282c2041e0000b04942010850010700940203031400c2215885000a8000403811414030b0060050340d0075060203414101910384800e500652410000d00e24010b6108080e42034403884103c000b4002e4022a000301c880780c440f1440080500f0300b0a00c0c5030150b94000300a00038603242d45003001442204035800300c1e0051b03540300c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 494115998 1250 494114748 494114771
    0x71d130204030b010f0603060302031221100906060203040503120c0a0c03060b1005030403120e030903160e01060207030b0105190b070c05272e23010302030c0d0f 71
    0x107440110712584509260354100740100070b4000703d5401c02d80800d840e1400800240e600040c41c000b405543c0c0c4071150741c034284410310030302c1d8249603c06064903680c014140142030072600206000c03103003015020809261210401c9171684214032945605500c003034206a00e5004407801410072400c01002c940e01d80c1d005541d040119805035109888055503580e00c400b6a0500700c60700c1c0c0c030791462480c00c0c03451403809686c0a000010021402d401969962003d001c2c072083c00c000711800c13400001c04a40b981c05200d07540c01070100490240c1c0d041144600000034080b4000240f0005490b446018030f40340b17a0030942441405000d0420200c004101c101c1c2c0007a0152100004100c8103000300c03045890542400244480c10b14198080102504103908507849410b00d01c0c106500a80100d0407551504004602c1c2003222400d000c44182c0384100360000904004a492103020301202e40710400501020000150100d02003150030080d10311041200280702146640f0204003903440040c009480314254 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 494117248 1250 494115998 494116001
    0x3090705120a030e2d0a0b0c0304031b030201360305011536110a0903050709111b0f01021804061203090b130504110904050f071d13 58
    0x103107030154a4114030010401e0640c0100348200044c81aa11000203407003c0c0d05442190400140703840b0b861030020140b6600380d0716120000024800020503a4495034031032003445d20391b4854401120a1410f490b05805040454407d00c1300f02c036016100c40c000800b60740c40703818548a200000b8504420081d48041507001806c500e00d0145016000000c2d542402c03601500103405140c00a8069440340c845a02141c100c5099448140e56030302d45e1030300307042121000e00c000391104005862007a48003003800c51003640d01501c0282103e002d841210a0142e0f9620100304807110b007031080c203e031581007080d041a1004100340c2004010803c040700c14411342c1e084003608a0f003080e121650032100d13034000c1d1085454140030703000c090a8035594a001d42d00941d85c000d0101071880c8200e42030301002243c42012803040c000d9080040c0400740041c03080c0d440c2040385a00c103500c0b80d008107220300d25001c04140ca0403165141a4420051500c1d43c822040000301c0482c0c40c800c1d06507825500c40000b030305889010005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 494118498 1250 494117248 494117269
    0x20106031203020a0e0108060622050603040f02010f14040501110307120909150b042c0709150206040c05090c070c0806010305010b030610030204050a1b0f0f140f03090705 75
    0x55542c01615220707109002000c4030440200c0034100300801042c0a81540e911044500507680300d150000280440d59625405e40714035488036502400100800c800d01410200100d0395902c01d81c2c0c1c000f10a010303800256009140d13204022080d490034002403141e5402021140042003260040300c1c00c044156a8180b0500300e10305102d40003600207082007140245901400c002d40d040c12200d07462130383c10040d010040340241d00c100d034416402d8900100e09120314500210b041c94034620a840145003460016001300d02c2407003203101c6108a2865903003154800700340940103644c000c0c5000d03000c1e413428041280c4d01e1005002200080010402c903800104d4840591006051a00c00380040f985581400e40c02c40b1280c81c8094040d802c07481c00c000c54914070011690903654110340010b10754440c800c0c550000c01d180a00340e00509030030085001625080400c41030a1400782e03079a0880e84044200884e8058000349002a0004d010f2003804502a5160b02170b40c0c0c0400130004459070166517000040034900c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 494119748 1250 494118498 494118533
    0x102070b040e06130e1b0103050106140f030705130602010c0e040603120305070e040e0c090105030109030203030703020706020d0f0906060f050a090e0c0406060f0f1704030f0c17250b0f0702010603 86
    0x6d104050400782d507010b0041c0c030b0041c42e0a05000404141081718080c15200d600c0e000d40e04448000001040140508240d032110124003110700d07040d50701c0e0540039000b8110742210744007003082201d01c0d4130240780c240554005e4a9101580c00c0e004081d1800c00c1e4040d060240c10101071020398510000703030741c50354410343c3c01545240004003031182c50784050092141060304980e02a904005140380469000021207411840a10700161340d0100741c10001e0090280c00b502cdc4103520b080095000c2c0140d50380c0c2150210b10301584080254030342c2e0b503807110080407030361040c41e410291281e1704200c5050039900ca648100000010343d0b000c110f00100040440fa00303600180c010a108240850540f0f510100704c0d000440e140c00d017210005588100001411300c0108020704000c0601e082456451241c0c55100c29158406c0c04495800c19406c422105900702d40c65801d40e040c41194541d104600d00c1458810042d0880400c1080d502c4180034040300b100c0003800c02c02550f4031142c0c0000000d1007400e0300e03400982c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 494120998 1250 494119748 494119783
    0x806010201111611180105091503071d1e01050f19090603031803020d0b09030c161e0b0306040b1504090219030c0f1215030c050102070b040e06130e 65
    0x400c586031010701c10058203812401917407403031141c400c1100a00503607415079a0840782120150b94641310752442002228206805001d114000030315440018540c1c1d54803200a24140100d654600048a45c0070030344234118240801f030301c010445030512175289010950040e02e00d925600031104201e20054840e4042402c1e80d0781c80c1d104000380b50f0720004010303848104003072205140c5e26580001720701100011015001e2410a03021580400c410011640201c2d45802910702c105034080d44001081040c0c403501d0091611101c0308115010140c003010b090383e60142d07000307003141ca81205110049c10300c8549150810641050032000301180d102800c0100340901c40035907111040d0141c180e004441940060a050030309000d00421a0420000103020b51540b4003446155042c0e86000090280c07120750410109803601d001c03062090588080c070070307181d00b038003101c180340c2e511404e550051141c7d01ca840c20b4010310202042e1546040d024602001e499080e02040480e401c2d66400d0415410700300704075003117 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 494122248 1250 494120998 494121037
    0x31a09042a1d070201110f070b1302030d0c121112090411030f0411090f07082512050f1009151a07021203090d0b1b030f010303031505010f080601020111 67
    0x151342401036451141800f00010b042c98001c42000f009800307025402012401100001030491201c1e4480d00f081c0740d0000d04445001e0311401024054a80c5040103580402d11010741101c4c4501a9803c4807a1080f42802000030804100c1c1d4801c1542102001542c0a5140c80c030001c06000a2000785000300d4003450b142c0528109450034070352041132064442c1c05640101c04100f40d110388611200c0e07105040b07080840481c1e031624402021400380d032002c46402140c030300100c02f01c0e0307611007404440440e0040c41040503445101c001704100e0022120181c1414400500380840c010755004281c08486103100305401540b42c42c1714440705c8148030000c00d606400485e0b03501c19460311080c8100100460700203075162500c2d010128071017485400c406088000f11402041d0f806541d0a100c081e015205c2c055a030b10ba04041c4401d003018282072000b5800642069a4802106441a544011a03505848109101da079100c01550114402490345041d0355a445400c04242c54040082c84070400800e80c86511 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 494123498 1250 494122248 494122261
    0x70f03020303090f0a120804060b0402030109020a120e0a290112030e090606090d081603020c0901081c0f030209131506020a081813020a031a09042a1d 66
    0x500000769946131255000d0b03603104001c2a00304840f410700d51814505010280c2d25410f0407030252280d120a61b402900c0000006a0070b640350380a09850001717540c030011090b1310804800d007a5001100d0b40e04070b03a00071a42e0305000405900101581440716100c01255501030038011201c048240d00035a051070401e00c8503c02c01da072007490070307450940031140900f1034100b12010440700c0c010084564004d4000401c000700740a0120240c6100540c140740b411151070f02468025200c04091501c14020002c00c0001b085900e40419080b407030401c00c454407a01161003100803a420701840140c43c05140e402c00c420000741c0c42e03184540941c070221071004204212101e0341c0301040b80c4664000000c5400044802c2d00084020040751040c84080e112910132640c201c000540d000284018080b43d5440014030501c51505070b0058201d01c03c55124900351004588184404110115002043c4044d4102c00c240d8400091250410f141044400341c00314a4407403408601510304081232200d000320340c008101c0c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 494124748 1250 494123498 494123503
    0x5120c0d1103181201020d0f06030b090f030a050306010e030109030f111b19052815020a03083d060c02010c0b040302030d0f05090106092f070f0302030309 68
    0x101407000c90080d482d1110142804054554502c002c5210301040c2d800707820520825015141c02c0700c0ea01804001300c5229100c4070004005c988800c60310180d1502c001400c500000c0740b0042600856000341d032414110800c1100c07940d100509160500985403001e00c0d154800740b10340d0301032a1180e281c41c080a903203484080e11210144051000fa580410382c440005140300c500540b20b45030030740f00f0f1020307284540d590a020700ba5941080d9080308491403030040c0c90280d195001c0940d00c6148101d449d0580354042d140007568401080009a80300483d1030000130310403000305501c1800c000d941c0e00703250800304102c100d050b1440010921500e0081102c10b8046550019034000d1865003406080c14a9a0380043d040d015480c00141280b903a03072001500b894007d1040b60040d181014081002ca029116410018601640d0b214820761900340b01088402051042c4000c601000c541c0d080a42e203525001042e421441c040c004000d48107014900016000480002c14644070b80c0107161a480d00208161 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 494125998 1250 494124748 494124767
    0x3090b07020a050c0a080c0906030307051603031101020403020a03020d0f0b070c0303140603070b03180601090f0b0301050c190311070303020a021504020a3302101505180405120c0d 79
    0x14032851040302c08100000380064218090b40d02500d03803230000d50380c0d040001d095002d4040b001c0d2407805031202e400c202c50304155079201505c1c465102d814441b0414520f0500302d00841c08000e42210091500b031000d80307405944024400d2003000e203010f0b14130090340c80403c014003e44041c0045a490f404510402d6018001c003440340f841d07550311318201e1500b40e00103a5640c0003482414856040003000c12a1000c1c030090b20a1081443c800720350035540c0d0b0b171114400502006004030800b61034501059407c0c03406000c1e40340500c161582150610410b070450042420a50112900b45a1780e941c000c2d10800f01b0b04003038055540a614016251006204081d003009030742e40781054044041d0f001c120060783e44209480c00d0301c1c5c0760000101c0140200b01d9110100080b160209112a502418180792990014035490b0b9054603040c203010480c075007401e9080c1140a4001e240e4020400c804100c1800414070b885a40140114201c0b426801c0e00003c042c001c1d03214240b903a60b41c0d0804403036150364640001044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 494127248 1250 494125998 494126023
    0xb030a08091e03120318010c0203040914131401270b0106020601060507060504030c05100501031424101d0609010509190c2006011e030f030f03090b07020a05 69
    0x2065481c1c1481c1c002a160b00d0144c03010340d444a004808a65004800d005254200149000822002d5800e180113540d0360420721821a1140c14592800d400c0c4118590040c0610180070030345048c0c140340e903035040e40c6114207000b01b82c03950360b1440c5c10b8030350a480030403000505024888200088000382400c226009058010105541c0076800400010354002c084501d5560410710010749134549240c00ca03000465128068050310070390010361824089640003504a0388980804201005041c0c0c006488100d040e00d01c1c00207484000c004102d1140b8174100951103441d6030f0469100a845100e0343c0c1003c118101c0c9038039140b040700708100684c03c01c24041800b60030304440c609420700d490b0320035400311a580038072003034525100d0040b04c4032907000e040440c03003006201c203952030b01e01068034840b42d807040c007481072600d49505c0104d0310300318200110840040d29005a036003906202503480c103070b80d40300c40720130040105942d0740b140707130080743c448440140500000d07070240c01022000e003040c9241007126801e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 494128498 1250 494127248 494127289
    0x11503020f061e09030a0807030f170105011209051c021b0103090c0306021b010e0a0519050618120d0504020306150f040c120f0902030f011b050d0b030a0809 69
    0x9415050b221070482106008288440e65a198607044c00300b030810190050080c402100824103801b0507401c80016400408103640340604000d151000d030800f22000e2090501040c81c4e2080150060304680180d1441f5000d6801c807440e440d202c881d0915500080e1a040700182c11000c00d280420740f00c1c1c20003a03000002468240040d55a5407503102e625a031600c0300503e11580054a9001c4424000351849400d58101c02003140e203050001e0780381c9440c0c280c00216800e004038804010147c480c0707083d17000703125000001800c1c3c95907950400c0c0354449420303840211621038801600341010f0b669008124100d40c034140400d190629105041c074000001c0d110301c42040d10000303600c034640c580d84140003001d0012900402c00c15006441520a03107220041c0f81c568078144403141102480b150003c0c040c89201f6001c60702c1a074000420942220407200d4080034902c910709074210414804c402070300340d1a0f1f4101e000151504c40d900068a000c0101908950b1420040b030801281e10304606400c0e1816a40f004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 494129748 1250 494128498 494128507
    0xf07080705180f01032315010908030a030903091206020d0b0102010b030a0605270102071a0c04032d0b0f06040b1f05130e060f0409031d0111011503020f06 68
    0x7090b026800303180d0400c1c0600111110100982e1090b00316200c44510100304800700c08402c100c906c03400008590a490411204042016a5118087c0002103c5104010b14207104400c0c03001c130060000f1401c140c04111003090049541c901c0c41085c0310f0b50034402c60b00140d58030303481240341e02581c0c00d4107012410341e4900b01b0313203680e00d0f00d0228805080a610110000e850b039560401c105c41d00c841025042a55451202031100400b415801008468060001d09190444004041240383c4045030799441c0300000340001c1001510a410602c4015411400c2149480a0401c1401c0b0841400e40550300d420f0040c05020704810003c8540c0c2d002241075034140b00001d4014049004003207541c513003807519000c0c80f034a84041445882034070704166580c65050702181c0c0e1400550160310040c0c2e078081c402e114a42c0382e16642c1c81c2c18800d0b0251540d058480440860b00340c1462880d01c011007042e42d051100d124440f0120716030a00c01c031b9a28040c58074223540e0040c154014880c4058250324564001c1e0f00800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 494130998 1250 494129748 494129767
    0x10303082811040317090a120c05090f180c060f03060a0f12050c180406050a0f0203010f030c050301020c061815040b150a03230a0b0f07080705 63
    0x452661005441011090240100030328510307428018540000c0e892034031050300364026000c00280202c03805940809580750f10381c0c040c3d00170381c4141d02e10340b94044100c0d48100070008601c2d80051a05000d4080900002c1c1c0c0c0380302165031040f0840340a21a59203030410040c0c4500c0d08500300040c50444c0000705003106100010861502c40c0c99010114040c0220006810743d4461b050440a05031068039002519610b2040d06180300241008840c030340540700700b16a543c10304090070240c0282c1c1181e40c0d1516126900d40300001c21010308546c1d4420748407944101600c08030300045008101c04008003804902c0e50a20100020054000c03034403d034010040c0c8a0f14000000d4044e400804400124010440307000c85285020030040c4145940e408600400c000e1201c42e00a00b4407641c080200e5040e025840c0e01004040003250000400d9a1940444210703503014401410b80a0002b0400b25022061562915140340741e04440150682d200034041294076640300d40d8050304050f05081075400c258591 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 494132248 1250 494130998 494131007
    0x1030618050d05090319080c0f0d020c1c0606080303070908060f150105070c15081303080c0306011b050d030b1e01081b030f0402010e010c05070306020c0313081c08010303 75
    0x2600d501c2c00c000300407070302c034101c0d9405000040754600008030b090101e01c43ca141a0550f03811003c488441c60180c80c004803c400c00214401500c01d03a96070290900100350000c01401c010010306034405802207000e8000040e440d0b20858019100f01c000a5489190016000f0149000e0f41c222184c80c0c2c0105062009100c0c4510507541c108000300413444009443c000100c5a6009211b0043c1c81110300400c0004c8407651002802c075106c1480c1d030b07905020340c2c030408094041601d1b0035006000407110300001c2ca21101c850701950300411b0502d407804640d039186541e04d0842c4090b44040d80c5075003003840701700d485035058403800710040d4040d10084000d0f01d014a0301c0e0040840c1c40b905c0340c14400e81e200024420340c290394004007203d040384596510b0b41806200002c84660494049011500e0640052203540c01482640c1c40c881d880f078010010707181035a0700e22000c0c2d04030201800c114801440000c609a0b1000d25103070142021130010201c000321405401c140c04440e0205a050140c1c120062010aa01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 494133498 1250 494132248 494132263
    0xc0c0e0a0b0409051b030c18041403030a0516140a18090c02010527031c0207060207050c01020c03120f07060605030703050d0806091608090f06071808030c1903051e030103061805 78
    0x100c102421083c1e27514105142200d00c0c0c0129011640030000030001c807500f0030ba11141c060200015108502c0c0b00c0080e00f92003a0003880e003100704103d01400522050703803040c1d50300000140c030803151600d030300e985040000039203140c10301c55400750351110100040c8414540390682c09071610742e440001811183e010a40300c0c0f164041c1ea0041422034080302003c81c103a90110b803c1da50744140c04561740d4000c7d040403a11090101d01c818018012515076501524000400f10303c190080c09020b89400b4101e100030102c2d6010303000880d0010b488110001d0f00e603030f05001040083d4001da0140c01d00c986e5842000702042402003e4a218000001c02c0c08200052580411055a45801c0c5100241c41d0002203926044401808140074400c0c68100428594041d140c440900400e04001604940f01c030385250326070146044d180426448010420808000003030404070042c00307428034070b03e00b240740c1350440d1030700750407245d800000c21000004200700201440b4001044c000b00010078114002551600d840e02e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 494134748 1250 494133498 494133529
    0x10f0e0111040515070804030f02030c03010b0a0504091505011d070f05030a1e0509031c18030f1404091a030c010e150405040504120f0c0c0e0a0b0409051b030c 70
    0x1402c60b16130071050f40c80c0201c600e80394102c1c00554580e0b64030700d401c00448050b40401ca00a02410f2450101c90030140a02201c2d00c2c1e0040080c014a03084c003040c03100400750300c507050300e414800310b2900c40c1d101e080d40324241c040c2c10600c0003200006001c01401d800928041c2c01c43c070030040741182c07580026034094140c0360000c1181c0004602f40380c0104444400710030102d03021310b01518020074000c0303001c0c00000400485116125029206400c10b05401c1100e600003001d0b107540000c07107078100c0028400c20380311070103c03124203041d0381c4000c0328100250f0a40050308100105d50f0789910074001d0b041e107001445e0400304220b000300400110000001c02800b200c010b5035000394200b122110b4004c20300300940d00903101c0500100600c0c0780c40d00701403c1c001c851b83ca020000c65034010560840500c40c00e10054420b4110f8001c5001c2441c00c001440c014000400062003a076a6050001040e41e860080d00300f820700841c020440700e1103024a103c8005907540000303100340e0203204a03132000e86440d60b40b1294000b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 494135998 1250 494134748 494134759
    0x1103070b0c120915180301150f050d08130806040219150e0f0310050a14011d0603010216050d0f212a0504030515040206090d0501090212010f0e01110405 67
    0x4089001c50081a50480e0103003040e2130102d45000305541000c69024a400201c00038803140e00852840310f2041024000d100310810f40c150144040c5c00e1150132804401d104001e0280740000e44140c0b03810030030094111101a0300502d0602c020f626003999003500d035030040c1c000445aa07280080c07441480b030094030054103102080c00038052139640d03081c214050350805420765160a10500d03904004160032070707030150342604c0c0c083d048070b4140d00174001c0d9060341c0840c0002c408408107590340b807203002c8008210a0f41507400300407044841800340812241c643c030400040c00528059140940103c0c042d20140081000800b4003130003030146072001d500355081e00480060400ca403000b041900d072110911141c1925092070040c0d00143d4414014421640034400f65944e285d4103030200e20340f421041d207010390310120600c0314090070b240c0800c442d10524441e03400011414a00d40c0491107421070f41051907420f9540d82801c004058540c0640302c00050719100130412001e5407010782c0d03000c2c0518081d090160 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 494137248 1250 494135998 494136007
    0x10503071107091a0406090e1203100320010e0102060402091303020102040b0c0304060f021606080a0f05150a080a05060a0905030d05150f040c27121103070b0c12 71
    0x70000c0c05180c0182880c1c042c14012040700714020101a4108107070b1601071860042d000075400750030700c108202c160040014040740c5c075804507500c034681c101030711107440150340120010000b001c00095001382c03403544000c1d4040b5013000c400034294010030035869066401c04410040165200b1362419030109000c040b03c1c24004c098101280240115041440d81c1e00d400141403074540c40c0003000d001115047e035101c008503405043c00700c0e21544442c4510001d215407a0092200b5070241410691054a440001682042104651065074826111060044106605500e07682091100740c0060100d5400402d01e00c07600340e8410b1b03503440c80184105105a540d0885c401003110901c200c80046c4e8030100c090240e4142000207151102d920300969114100888400c0254201801100340042880d1142c0c8a03d1284240c141202624042606c0b201d40c201000480e500c0300907025481e965014010464072003040c03100b030500c0c198180e004084100320600c00c22200d2030000030340d089000700700140c042d04c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 494138498 1250 494137248 494137277
    0x7150215060d11010503310c080a050c040209150a0e011b030206010b0309010b030604151b020c01120204090606080f0c03130305070222050702010615020709180b0c04080c060901050307 81
    0x203c1e000a00701d02051811100380d0030009504103141f0290300e0140d0014050300b59558501c580c1c0c1d103070300700b4018803030307017080b06088013516140c2e025100044000e070203040000c0820040558540c4103407046004200c07448040d00c0c0300d59019004240c01524859486130240e01a20061341c2c0e60014404c0c103125072000800169004005c0d084900c0b02d0102070700722480c03801c2a2401104440346c070611402c00602d002d108a00c221140c0b000300b0101c00c5075030082c00c89201c10000460b04000c90800004aa68003048009542c0c3c10700d1155000401050b5600071050501c402a0300c070003030025000d445a09030030b0040c005028050880002e040340c0c142015591250180b000c07403018a070a444040413503542c4591003522800c030b47c0250307210310056030003000a25282c20600a001c0e40c0100e010f07005900c9220f060045074403030b60201007040c084500200a148990f5075035104150100c0d90303842c2c400380101e01001161000c000e08030b800201240e00c40e0a041ba205c000908501004080c0410400c8040f0103070030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 494139748 1250 494138498 494138521
    0x51c0902032e15140111100e070b0f0901050304150911030c0a0f0b0f09030307060905060108030405130c0309021002070f170307060e07150215060d11010503 69
    0x80066018040e24824140900c4000030b44075002c6100032640c00c071a19010442060784075410b458a105160303d01c40a00b004c3c0b0506425041442c190305010300c05205c1c0000071010450100d080f1061040400c1c2070608120b1241800190350180c8600c000510441d40c0d1603811700c080c5c1c1c00948080c83c00760f4895039a800d11110440828104021491824481500b408070500c200c101c111301c02d80c200c0301c06404403400d105072004548264241e505000c0818428802c00314002e04e0407c9030420180d0a0000040c00282103a1001c00100c2d95107a655104030100304c000c1c407a0500421498001d98100b5107814081000c1c000180c9800c1c0b800350340d41d01481103850003540800c1d00d81d0b40280000580000c60f18000e580d901041c0180c00300c0c2d01400d840001c0302e251002c0c0410320045640081c1d420803105940c0d14000d00100c000490b40d40c0162100840d000010143e04052003a01381c0c01003030781d0f0986000139a1222000f41c102d80c047c80c90b0080d0400031415444100318803042c00c0c6002a540c1e03450030074600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 494140998 1250 494139748 494139761
    0x1091a0a0c0803040b10080d0806040c0302040302041a040e0d020a081b19020406050d0510180b0c07030909050106020a110a090f09060501080a0b040f080f04180e010c051c 75
    0x101950b5010041c00280301415400da40310390781c2c041805405a4450541c00d590310500300000002611140000704141003541000c02c1c081c00509000d0305183c0c07260300144c2650703155080d00e01c0300f400408840d5001e26141c0503d1091040610180c1458050040001c0d10707040700c0c0720050156900000da00c04421506041020700860140c03d40f08901c44180c0810404641041e0980c0b29505012000c952460701c1e003c4140c00341e9000780241602c04000116001501c450403031400c80202610500001c18644402103104402d002c600e0769803a074481c5000b5215a1568003c0003070f0758904801885400d0300001c0c040e021607044680019801c41030030001c0c0c0384030700b00d07008404180d0420030380818000d2140c11001c041d51103480301740210380e01da454043c1c0e12813200401a040c00388040c0454085240b4915400100e4014914103180c2050740340c0c8521181e100341c2c4034240404110440c03050360796a900c1416035180e000d50080c040010b04250080503030081030a481031046e0039105807101e1402651040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 494142248 1250 494140998 494141003
    0xd230f07050319050a05090d0f02070e04020307030605040503033102012010060314010504020a0302060a020c150d140c18030316060506150c071205011e0b0f01091a0a0c 74
    0xb48181e1500b0b000e0000a031031300350303041c14440c818002c5440a050282550009c0803c4c01d6008250083c83e10080d00c81e00400030744242d825024944c80400070482c0c6000310f1384103030f009400a40e501d00300301c1c030042103103200c1c075405050509010042d001d0521243c07060b0281035409103454541e800c40764036070f80c400e040401d140e00654400e500c000d1030300243d5500004100e0b8084d99155200751480b6040b24240c0c1d00494009601c14500d4100b40014541038010703158583c00c0d03204551540d90a400401c58990000f0301c20103550502160110000c0c0300750140f0488062415025031950800840c28150f501411180c050940b100b0922410317252000c1064403501840c4100038001d0081600b0550001c0c4019681d81c1d00940343c000200110b8aa040100e88100c241600100000b81c50464801c0c076060686900b22459500c0d011003071040040e041c00d050000b041d29000003210a10f2004206140e01c0035403106061203101c2004100c00300e0a02e24059200941010156031482e452200721000945081c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 494143498 1250 494142248 494142251
    0x6020c06150312311d01150e09040209060f09010f1a0f040306050a240e1e0402100e0607051605061804090303110d230f07050319 57
    0x800c1400e07a0148540840c16109806407100030b0f2028a08040d01d211301d1091084240b0749040842e2011107200f2502200c518031091001400e0b140e0b80303840311034000380014a0382d410102005001465200c00504003c110b1810007041c0c45290707202144c1b180301b00a002901c02c600305c100290301a11202030450103040d000302585500d41c1c4501c1c1c0c0f01000c03111070041900700700c0c0d0022a6400101018200c810140c201214181405d1541c1e40700000b601e00281700d01c28035510740382c440705d61405090429034444840025808800d06196029011100c014094107904d10f103141c260b5030129200d98076641003601078070480300803008a101507400c0e00c0001301440e08240c0c0011101e0034460f021401103040b0040808184e04142d83e5410000d0500030602d24005030318034880c0191091038168000304580b4860704021035421203000c0c500e1901c0d004280c480328000d03103d0208164038000e0b16210740040d203405517001c4075030230104100e01c1030100040502c4140710303002010030400e03029103903121100400307100c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 494144748 1250 494143498 494143501
    0x10b0402040902120702060906010b07110a12060c03020405150c031e1e040627080f070e0a090b0c0a050c420703090c050303030a02090109090605060906030406020c06 73
    0x20b400941c030042581041c8042c10002c61030151003c03e0302030184050038000c4c003040c0d00780507110714581d0054200300c450751307141d1010030f0141e1031300382c081d100500003664080c022003018200141030b201c0414108081510402062010380e81d40001c112840b000388044a0300c5058281615107103214142c02c2c1441550f00411800706483c07800005c190480b030b000e0b540d034818210540c01007040e00a500802000c1a909808040100d8040c0c4100d032414817020507030040300340d46004913800c1a10391070401d0101d40200100348010b0010182c04c88c0c120414030010400b03c0000e40711000107940c054151245480009076070340040b4469801e84450341900d1080d80c42c08644801e102c40c3c900d034140080c1e200501c0d0803400010040a1004c040c808061000790003c040c5e448074030490041040c0c48040310040316654004c5102d071020000f071072180c1d080c80c0f00141e03102c2503240050005105513000580307003820000107002e00d49846007610360b03406050b50080e8507510b442c074104000e0300400036030a00360b104940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 494145998 1250 494144748 494144759
    0x1b0d060b190906020a060c2105011406070f060e120301081c0e090106030e07080106030501060611160b030a06030503070f110d11060a02210a171314010b040204 70
    0x300104100944140400c000141030142902d0501240c814000940c201140000c0803a189070810050b101061514141402d4200d000e0303442c45e1100c7c02040c14a1359a00014003042c1c1e65802041c24019003103440d81d09008295807100802340c6992001081030303441e00780c8440d298404000c84142002c240d48a0f070303103a40e160035010365588007411050403403100c120f00c011100c6001e11421101c3c254041c0140d45640e007003110030f40180c07080c0e0039491624866900005104175081c490803025610403000440d0403881e0100080c040001c0448001c401d03041840300d80a5101c0d0785902004032303541c00942d01d80365901d1000c1c5100074001684007410a000c00901d000800a014140050780c500c00e482e0640903088110a00000902d0300d00c0003000e51701d240003c01428501840600760741580361048800411107180054204201000444812540030607101c0005400c424000c060a410b000c400d4698a8442a107240200300c099000e02604400041d0303100c00c8400790800d9040e03c1d0060825540c0750340d0b41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 494147248 1250 494145998 494146019
    0xd03020309130501030213050603030f1b01050105011b030f0e1c06061707090207060e1501060f03020711040b040f05100e010807050d0b2a0a081006081b0d06 69
    0x140101849605002ea410059020030b00c103690590350007402d8143c030807101d506024000c08014241c60f44c103100610452050583c20380c010080b80001101200c020f00e442e09405095820680000d41404001b9034042c0e54110511b241420040c1c043c504000c6000b0160000d6403040e07200100160080c3d06080d000c4200a89001d84510040c0310742c8040250303070365460340300300e1030920080d0b454580d8110b0343e410030410302c003600581034860040e4400148140d0a101862134042c030109440d004280d48001000b82c00c0e0410540f4603c5c1c0510b08041d440d000103a83e484c01c02007030a910091045540302c0c0441d026480d503074403403503c0107983c8008000900b400d0420b024412101d00c184602c1e580351200100d11017001090900c104c40c0054041c1d440802d256035040c6160000a2a04400a080d030400d003400d403003008072184803c1c507882e003007590340c100c001c400822001c0d0051010305c045222500c10050940d1224004d030b40311450300f15952405190201440710f40c4a48030b0b65102d42810010045080f284c00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 494148498 1250 494147248 494147257
    0x1306111201080d0e2d0d060b0109081b0d1b080c03010606030e07120305070c0e0a0f05040203120d021b010213060c260702101d04090b060d0503090d030203 68
    0x14441207502e02480c070b90040396101548002542c008604601303805104040020745c42d03070041084068a02850000b0215010141480c01a19410349451460600e560041c0759000684500b0019010380741d000c40d1101c0c0c0c4070711400e20b1a40141d01400c1c01d0424001100f4110119410944211445558070461140e48004d0000705912a5103090400103005009100e0042c0120700c510160912624040841168809000c010303000e0000c104115400155142072603405071040f11100303451814050002c40c11030341000e907002c1075145444180400740c1d40000e03105580055110520f84d0790440120300c000a40030f000c90f600502d10380c0c0d580025650300b0640142000c5000d240580030000d99900084070001c000d000040c0c030780d00e41d1700400f02014110b0206ca01c0d40910101085161624560100d00071060b01b013282800641081088a84100380300b904c050603032022141404602c1558031414001070018040c41e1180c0300c423407003c0c01001018010745002400080422030130500f24103001e0b440303910 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 494149748 1250 494148498 494148509
    0x130c02010b1e15180d050307050705090c1e0d060305011b0207060f1b1a04060605041b050c01140f1906061209020a08031b010f02121306111201 63
    0x1140c40441080081180d02c0c110b0002c00401000411060a2562129030701003003280210f51101c072406611911030030342c95010b0500c54001981e580c0701d0303420300c02d00342142d1f5044240f0601406045c84030781901d14080e540000ba178216075005024813040000c3c2c451007148410518507042031000401d101065120081c0c01200e24949048907030150422a26402035014884c040741c010140c0c019018800c506070901210015141981183d15131200783d0a41a1100042c1081c41d13003e0820040100038000c510080c14292000d10503207200465504501141c5108081042008140c0c403802070025045145804041d04160f40c550400101c00c94130504101c0b2040c0444ca41c400d0303185c90711300b00741c81010201c408542d10710044240c80c1c0d6010025058280c002e90b4809059200424404000c1c801048505148680c0304a035a076142c11540c00c0d124048141c580c02403040c00075020124a14400590004802d82140e00000c090300e020b00060440c060320400c0060007080001d0a440e040894505840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 494150998 1250 494149748 494149759
    0x201050105100f080705211906030506010506070c05151b0f06070c050319020c01030c030504080a050c210304020a05040903020d080a06050d110406050307060c11130c02010b 76
    0x80c1c8032024000d0b40506404030310700061955140601880c801c10000740c029081d480e1061608a0a1013425440010544c22a900880041c244002490308032075803c100302080310144080c510b50b0303c0340f5441c0c01c814482d05001d040002001d908214038829000050400105002401c551142410070305411240a051036041c000010b5a4000c10008000701c50703842040040c042c4d6561003d04503541040350b04111041d110034841c95000b510320205109040721130381d0013800808810300004080d508101b11081c103051600d824040480e0506084446040d00ca007030080e56000d10028452500c0c8071540901350f129203140342011034a1922004500860003161000c0002e43c5503010042190780851009015a0183c46c41c0320946000d0031031a90f004619513800180c00790360310041102d5110741c00003111303203003c00c5804400d00d2410b0710415025000980003006102e00f8140068040400750501600040004201400ca03a5941d45032034500e43d100d40f400d20110162010180c0030701800320401c0d1003036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 494152248 1250 494150998 494151001
    0x11401082407120b0303071103120a0206061c02150a082202100306050d110406060302090a1707050d080705010e0102090609012703080714060705092808030a020105 72
    0x10701c0e0862105070030340d4100400740c02644442c1000d40d948825000a11455503c2d9500c944d030a59060010b080454018140035030390080d03401c04c1504081c00c510400810302020b02c01250704950004000360b0008060324180c250f91a0302c10f99000384240e4501c001d502c00541014000c056207100e000c1c0485520325120007500341c6890220140e000f08010903e5903030312034401c0c048050726003140e403800300342c0740c50800217079040c3c690004c00d40c00700301c240d0300f91000c10145110941a0420b0701c145001414186400c506200b501000580000d00c1e1348a007194615802c3c0000440084c10301200c001494010700b500400451803400050b41e40008005840651900e001c1c1035401c0d4041c0200c991044000b400c40d45031110550041da828a41f000341c40d00c010410059900e440280c07901d461028500686065458410a01d0f0154001480e05070901854000340c0074040302030380007030a0302d10100d002c40d100340c501019500d05c032a4138038081c10300b4100005586000109002e010000b0140305e440d0340d009201c00d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 494153498 1250 494152248 494152273
    0xf070825030f050904150603090201140307080105060c070816180c050301050409050f0a0b0402190315050408090a32130b180c12070c0c06080c07020301140108 70
    0xa824103014022654600e022480184590000c04403210300070f000042c1c94864800503845050340750000404640c1d921001c0d429580c00004d5010300c0c800e108103003455407400c0c4400400b60300040c03294030701401c0041107800d04001d00b440340401070a444011600c1512111030030350070014961040302a04142c40a5910b06000d160040090320106a103c080ca10303460728040c40000c0120703082c155001d006403030f195440501c0c18801d41070030501610000035039041c6801080701c500c505020190000703c443c2010000a070350b1004042d03002140050004003036480d0300300b00016120700086561b02000451001c24042c0c180c41281003000c904602d9031f03000d198400c506881c0e0584c800d0a061713101114900c05445080d0940103140f002d03c000d00141800d00d1850240510050160341684c524600410300341b04840702d58400b035034030185500c1c21074080241600c4955244405008040402082c040010b168a2000085a0742180d0180c02006440312204074043c0d03420084c0a84a801e01481d02288403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 494154748 1250 494153498 494153557
    0x1103070f1101030903020c1c080c031b1f0b01091e03060e011107060e0109170c01110f0711040b030f0604050c030a080a030c0c0602120f0f07050409110f0708 69
    0x892541c1034001f02420200d0a04110b4002102903a40c0007000c0240c408600081800d409041e0409581c00110344408021a00c0a1202c4081011200f0340d80301106808030341c040c41c1100e60002012000000c2c03c0340240b40100d03220754058001e020080401301161a14030b180e48135542c1101d0240d4410402010b01410050036654a55496085138400340001b030301180081d40420000c070500c0c07000054400041c1d5810580712080a02c811003c0c0b008540341d41c0303142c1c00313014071014494806600c40c503245580000380031038000c015016005c201e030f407c146c900c00d8607a540469410030b130007000c0b14908101d00c0409a943c0e001100c040340d0a001c2c00b22051100d040000700c1c80355495201c0c55290800816010440092264000395801c0248406503400840c1407440104080c40c000001180c091034410060811501c010300342121151426081080c843d60043c19941606c0b00301c40d010a10103103041c0f401849000b10100c0300000700b40000c030001040140402011801c107410585402181031200214 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 494155998 1250 494154748 494154761
    0x80307030806270a14010803031006080408120a06090203090f010f06080304061815030b011706010e0f0f04110702280e1f0f083306011103070f110103 66
    0xf40510000582c402880202d1610662241807150300258116001d01040c03400c01082e0b000c0aa06d0b0400018400364070071150002014003410b007004012800c156881d20300d288a00303011456550507140214040c0f45071a00480020416818295140e040c200b10742a181d00500710008055882c141c3c81c18003402e00317800f4040444107410003540c01c05203000000d40710525800250310240e80c070340d5004550840040402a2404034a43d0002000b0300c2020000d0452100d00c001045442c02c000200010350382d010b08207409000303081e02d002c0115440c40d404550b0100c001d40380286c0c01404c21450441c421302c8103000d85001c50003100c0240b01205903201c1d201034201341421b01e004c00c0002e40d000780140c0e10205030168000f45403020707074081c0c0801050000351010590700300c80030706105d03a203007040f48020801003043c1c0031144240d5014025449a51200d050f04000c510000001a002c00922039a001e202d21013401009070007a607a40b1000703864010010032185804450f010401007440f01c10354443d11400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 494157248 1250 494155998 494156029
    0x901440603070b0903240402041d060a110d060311040b0604060507021c1407061215030210410c031e0d06090b03060903090603040312021201080307030806 68
    0xd0240b01d0a183c00d42080c0d900203c442601071140d00400201c1c07070b6440090b542c20000190020700c0074105441000165007401d01d40449000f103050103100d0a42000c07030b100d60048140040080c07600f016082410b0180104a06d00d8825840d000c800030512400c035114040305103044400304403c0c580c1008203d01c5000d54041c0e00c00003a4148000c07801410b051900300c00d584188412210449405d80c2d80c8503401a003240c0351485e030740002408004503a00315113814a01e000c1000d090094089441d01070000c0d0a061002070310917105d052a900005000d0007001169494081c162501d5001182d41801d943c80c07604800c0002d0030b01c0001004c040d0510780c0690341f0a5821501035132801308031a400a0a0303200e80da00c0c2441400c010081c200030711020b0704c2034000070411103201190340103861040504000006061588030303041000b14406640d0341d82e04a80d8050760506049481d441d038a04110001d00410744602d010b01084000072a01c45000800b500485200e6607918070182d40c0d003c107009071001c20040c207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 494158498 1250 494157248 494157253
    0x51005010e0c03100f090f0c020d1407060204090c09210b1302010908011d15011d190f0b032103180f06102103140901440603 55
    0x210703001c0b0303001c84011904071441c204034414440c3c550800100b08661640007055403070395508101202c0200b401801c05010003030024084a07091000081e0403581c0780c042c11500e20b080014038004000f41c2d07030706075800341030702080c2005904072401d00074000054a0041c604116082e03010b80343c0300c294100041c426190301809003c4961601080c004181000c40412070501034148004109142c0c2441001c2820750310120100060503824080b03420b008030705e410781d40c204100c200140311700c21703042034040800e00001c029075520360b4944002d01c0408000d144d41280681c284109000060415007148030fa601040700bd5038204915490304000140b40c0305c1d030003010844140005094042904011901d082036401030b64021009107140d00d040190484115400101c05c030824004440d40d4511104160b10f1014004010042c5480280004415105605010302c00041120140c0d100d016000300304c400b81c5044150b04525144210038440c900744007810086210b0203001c40c03404900c1e046034010b0310040c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 494159748 1250 494158498 494158501
    0x10f06140f12041b0504060311061b0a0605040b01050609010f1103070c03050d080c0c06040f0c09020a12050a140a050c27041109010219050f0304060c051005010e 71
    0x10680340d00d070040112880c04010034481402d0072101c00032154072036031156102c00742402051451811001142d04000d01079458644140000703141a070300143e0b254003c80340951583c1e10388000540c00c0003030640c889040d0080340011401c00030340341c010a00481c8a040c15071450b0fa2900140302c0301d4000e4403000342c0000d64031507070300c00c1c080c0c0286c0ca08111002d040050768540100b9440c0e410003113820340d000725441d41c803607061882510707485029136812200c042110392420a403910103a5803510060b00151015200000510400c06507034003070b03c02482100402d41d1581c241c16005010070050b0840036088505010000340c1c1090544140801c100c40e9107246d2890f0b1b22050307001c200400c8020a20198030710100000c0c0c0c44914014055074041090032802d03481c101c030311420300c402d030780900120034082c0405100c1d80c02640c1c2c020032445043d8000f0488041168900e0804903d41100c950443d501d50200003030120301d0550124038030003454055001c40d084600100100d5040b12024030400040500d90310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 494160998 1250 494159748 494159777
    0x408030601080c13060e03121303080a020304120b09010b0319030813021c06060518040f1506091517211905070308130210050f040e010608040b010f06 66
    0x4111940140072098114100080c1001c900801031381900080003045c00a00c108005203400c011002c0c45500440456050070010382460000d1a542e010050580a0206100c0200c51080050f100204108507000040c0c90140c24903412100e4103a550800c01d509007136040406040c00259410b2610035014410a00303682c80d1000c036a0b00b400030f020080c90340c604601410250782d1301000c410b82820100b070100124107452030248116000c41d441140143d0415030030b506a203080206075039226420486a01c021032072441c145450300e042503c02c0500c0361030b2020100310101d00341c0c0300c01100d0328214144101d90b6112405c610000342d050600c1100d40d4022200300014800784040a03403000144c07000d640c2080b0000c403079141c0d620a4400d001e000180702048403024140c0c00301310550040f110600516094210381c01003890800c100e220b000601500003005440d401b01c417402c542c01011006003024003940c480300c0c024034080064a081d5052204800080740c08010710440104480f407607140c0405040030071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 494162248 1250 494160998 494161007
    0xd02190e10080721091a0f0f0103051c0c15020d06080a05030a2312160507050615060c1e0c0108010f0302090a0603080318100b0a09090606080a0f02180408030601 71
    0x44640c00728017070b01c40c0316840024500d004242000325050b5854029407524002d08030344880d0041c00300311051484c0c001040030a07004036209602c1c010700c0c041e52200b0400d0070401d5400403100c5800800e02030181d01d500c0d10800140e4040c05100200840a20469aa03401215510051410b010f48607030002c008561880340105c020520309031960302840c0e020303c412003212282e42c100032882d083e0482104200000c40490090554442d070307040c2081400d1000644030503039103c030014003194081400500b000d4559440f1410340b4a034000d404100c50070074194005950003d2541d01064141d40305000200c190381d0702500c1e80da0306907680c4a4030b0180d0145180c080000781c1c0d00c040c0481d07a0659442c1380100119000c000111300c220010000c2c2d00120020303161841c03904100c0809011154500140c49001c0e54070258004c04031140c503100170410207094149900148601d92084011b841042401403c10120304039034900c040c0220342c40043c041d102092182045000c880041c00d0800420000324650f018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 494163498 1250 494162248 494162297
    0x30c06040b160f0302010f0c09063006090b0f0117070e060d0c032f0a1d030f100e060606070201050304060b1c0209090f030405060d02190e100807 64
    0x300d0220320102d01140e200c0e007110a00e43d01c42500142d4580502c048400300ba4050110340d840039150280c10f403460800c0040031002402c0304807071486c211a40e004aa1901000c4600139001c0c00e07001080600d95030040d010080c042c500045014040c4110f15140641c01441c07100356446540014002d86c3d9114082210300d08507440c000c983c808024025200001281e22808943d082e4541340002d8a4890706204100100d134503001c24443c40150451095074001c0c60140d520340140e9040810b6846030040000d003248510800154042c03040000d0b080f640c1800040d01300e04807456000c20803604d01c041648a4a03614126429500280c0030002030700154420300c02142d1040c0524400114100705000190390900c51003803480003040450740c13030b2046d8a01000d280d42c12403204030041c5882030300c0d1920240c6a000d5440740620481d40030541e0404513009404451102c00d201c0e405030115191408060400540807a04e039000360074608480c0c034081e0140404501910450310b4200c4034503000582440d15910 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 494164748 1250 494163498 494163517
    0x61c08030a090c0e010e0a050403021b030304050402190f0207031a060117040c2d0522060b0310090b090402040f020c03070501271101050703110616020c030c06040b 72
    0x1c2e98004540490b00e40d080c3c0b94042e21843c02c0d140025407415001c002884001b900c1e4040c07061400d014040002d40018804000602d4051640b022500210003e070441c01664007091f007041c0005403440581c00b2010906d8111080342d10b614450b50301c1e011049981c3d001500004100c041c0b503054551540284203401030384010145400d06100d120740000e0003c40400341c0303080700c005070301c40d00038050303060304000018442d450078681d940e10900310300e050340c1e03100303030610890340500711507404a100382c032404000c0c40c62100085828400355980b10824000c80c1d00880350007040c45451000461400090301440e40c200b100100b0480041d02d4503000c004c01449042c052241e815400c10911700040000d2028100d814041d400000c1c0e0980011000c8031094204107014244102c495070752000900c3d0300080304115407080c41c1031515144149800d035a0810400002411807081804011010303168179400318150f42198240e80c010b601582c28150b4440101100315071082040c017091016407030000c09402e1149 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 494165998 1250 494164748 494164751
    0x6010f0e0c040b070c0f050d050c150c0307110108130b0a0f0e12030a0510050105030a0905010f050f0907150203070311120307110c06040302090a0c020111040f030506061c08030a 78
    0x942e22034818940e40c4c032000044460b0380c1c41400403c48250101c04480081105403507810803192641d40b09a256804003040303900c00c1815100030304203907107020140e41102d80718a0840756541038508142c49000c6484001c1ca0001e040303c00043c081406001403003d07400c0c2e21910340841e0740c0f11242e450b00034001102d100c940741603480c81c0d071400d080400c0040b1003100b000d24030f406a50f8140104040191a00103003001c0316484202000c025a9074000100c96000740c03e04000549103203680341150140074180f1001356650f00780011701c104200c0f510a0705000340031030022a030080d0b5440c00243c140c0304141601c0400340c1c0080c40314802090041d0741c01301180c15200103503062080f800380620100d40058070007030001074120070030100d000c004105041b8107900c1100d801d82041e1440e40042c4002d200100140203007901c80400b5013008d8000d4000ca015690200d0b202e6407580e031030b24035402c0e251180e480180c865119120208990703040501514a01d40f4140300046080001ea485d540b841d68000f0345444442c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 494167248 1250 494165998 494166007
    0x150301170f070b0903100b010206040201081009090812070e03061b0d18020a060206090705120a050a2004090515190501090209131a0f010318080304120206010f0e0c 72
    0x1001c0c01d21a8101500c1c03002c0c48162900300c480d00340342c90310010300c1300341030304500d0300d14070700966a000907485501c540d0928004000796200c45e4400d03194540c941c80079044a003010044010850300c10041c00c00d14684a281d80c0c210baa03201000c440d20b10254220075096000000402c0f807440180c482c8505611506000300d140441c0503031610b04132270b1201c84070f5240c90b030340040c01c070210320f800c1c00c01d10700a0a03588000d20b42410200300d001d4a581c614400e0034482c3c140c0354041d2700210028480c440e0b043d6082410b0b2000307050b09003012002c10f40c40d04070448007a15020380080c5649014840d040e03103650000c1c000d0000b0300201010b5100540050004165400080d01c010850b05082c0503d40c0640030402015803951034000c1488103904440111603c0581030100b8400a81c0c1d01ca52004480882211a0900303103840c0c60043c6d0003800c000401d21080d2a003041da070740070321104500442c05144218407000507204090802c07038903010203000b84203902584c44000c21482404490301508181d40740d13092841e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 494168498 1250 494167248 494167273
    0xc0b060f0325080d020303010e01060f09050d0609060b122a0915010909020c1903110a0629010f030905010b09040f260901050c0304030c032015030117 66
    0x20030304001c90b090341201090000c2c03007030042c140015031509019000850440d4100b21001c01e904105006800c104100034000055007807059901c200102400351007048840024140703003000d40001c04c2c0a86141e410030000324824100307a0340d1225100042800f070804009451070454601e003a076269214004100664070141c1c1c1c0e0307107401090081c290700c121600070341c90380070024025050303951121011910510103071003410710104810049005000005040c0c8071a0328080e1804a0316011010b054840e4526110421881d6805030008031148013180d035444020354007101c0c1100c4c071102e000340040d09010082c00303400c3c0a0740150f410580310308000f01d012812100400d50300c0d0740c1218203817280702d0880c81c4c60041c008500800c1105c5254021104c18111040100382d1440c451451000d0410070005294120342c2420b0055401440c0d0103120342115581c1c03410300410340ba0030300c140880300043c0040080610b16100b41e004110542d0303104060300f51380c80d11004100448030f107610f5045501612010b00213 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 494169748 1250 494168498 494168533
    0x71b0b0406020d0f0309030e10030f0216050c0a051813020907120c082205070911041d1b3106020c03060c041403100c02010f0b010c0b060f03 62
    0xa04042d500a0602003000200240280c0d00e28a441052514140c2ea45003c2036000e809065000310545050420b5615188200c2c003e004078440c0b2011244089020b00d240040d910164030b10a0185c070844500c10081c1c01044035009851113403d038080c00d41d07101d0074280c030f421420710b070703032041200e0301c160410340e0b40c0c2c2c01003015408122034200000303a200c0e61544e410350142c441c2c0852100035180c85082032a0400c4846c241d0b04808945020754032646020104000c1c0c1002145c0c09040002c0d000e01c80f1501c901e030f503050386d60007601520a41e1200001e0118225801c0d0310014400c2d40441e1107800e1120414820900300d031f0203442018440c02142d148003803210080b200c0d1042c0a102c44c8815207000740703800c0e402030901d12850700d030a01c82d8110703009124916010708142d40c10b03150500c000440d01819040064609054003140304541d80c24011707000c190b19010761098145a8a100d03082c03180c4142c10f80110f50b252400400181050b504c1030200e4401e0074240c540340c01d2100050104d542400c800c0c0503807003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 494170998 1250 494169748 494169757
    0x10e06041e0207121b0b07080c2101031703070c021c0209130501060503011a040e162c070215040507091a030c06190806030304050a0305030309010c02030f071b0b 71
    0x4500110045040c04259401341d48004107544401841542c0074060341c8440c1101b00c0a847d00c03080100c00710200e40d8460304001143c080440e45030013000c0700c04260408490782202448182d0309801680e41c840307072107032068040380d104035407555130910101c4541d82080010070b20390f51550016490302c030400c401a01c45a044c280140405202e046140d80f051400d00e0a54a240d0415030190f41000ea001050348088480703602040c2044030049442c56900c1e203c01d10705481c4000b401114580c0c002d00041210041384c203007440003911f40809120901c83d90454070000001c2c3c0e640001031f03000e40c07009280c0c00c0c0248940f0f50003e00c2801a25006035448041c0010b840000c40c0300c0d038031120340d411400705d50300e01000124120350055440344e041c0b0180860700c80140354003401c81c90a000b01c4400080740b6035818000c45000d02401050103141503104c0c03e04680c1c98004443c180c4c45503284c4101e011f00d2600003c299800000b41e541507030300c1e10080340e6480071800c010003120b0b00ca40b240910003003140c820342c0e00030b00b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 494172248 1250 494170998 494171003
    0x30c050703120e1905060a030218030d0f0201140f0403030507090509010f05120d051c0902030a061b020c1027080a02100e0f040902030307151d06010e06041e0207 71
    0x43c4144200c043c20400085400c5441d5820345503507075010407880e21100140c800d0503090341001602c401c42e4840b524001004443c42c42da142c0988030610202c00d4000705200c0000d400c1c1e034001c001070b09113400c9040c0d050720203503131445401480c0f01c002000a07110341c014a510460618000512036542c0002c0b0b4114502038101c1c0d07402c81074402c001d004034100b07405068940c0031200e001b0301540c0100c1002810034866914112004441c846144081c02c10039080603800340c4d406000c41e06a0450390920301c0040c6805000304204150002d841c44039103100007515000281e0050004562081e5500c1c2641c551521010042000490104261940a424618a0040901c0406800d542d5042c1c4100204503d91120750800d000d0803c90290302516641106a98a00141d0300005d104c1141d0002038690b0080100080207502101c00114031107070290007600207440d000014980d00340300446102d40310303082401007824591807680084c00a00d89a0803004000c9041e03802e02c4070400c00c06038401c043e640084803e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 494173498 1250 494172248 494172257
    0x70602160c1703090904030c030207030c030b0a0b0103020c120306151c0c0c120807050d02070c060f0e011b260a1404061b03140d0504060e0304080a030c05070312 71
    0x10401408500d503140805402c840103903150560410024a14880180002d0704101c80446904105402000380001450b00820a21581507407440d20711404c50302100c005103260704000681c11303154003e009039440d0300e826101602c200c50a1006c0c080c40c0d41c0000341942e03401024841c049425039007400041581041044c0074850480308044040182c8088603812020070080039282c80c0844c0588074409210030892502070301c2d40d02e501a049519008542c20340c0071580c80002c52804200d40000d81c40c04880294450040340701211205840c01d01030b803519113011515044084071003150b40801e20031701d82e01c5009401c007507080a10300440a40c601343c1102003030600016415440d9900011648400d030484150140f070f05051400003010b03081d15003020381483c00e0780103c1008160250340031011402042a00f15254203107040c03036001614007520160b81042c0342c250500d0804001100b00e6041e10180c00080811003a1a0340894041c000110155910b00800703d01000240f20462140c40c80c2c103c40e902c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 494174748 1250 494173498 494173523
    0x905100e0330040311070f06020d080121080f1e0304050105130f140c060d020a080105040212010330080103050f0a1515030b092a0a0b07060216 63
    0x1640b2031908900c804911010480321851151018510000c41d44541e251030302c004031405107030703000c4e24008168008070391110800d100450b03010b5001840d00501511039035446d900341d03640c0588100d049030036100015803240710115040400d4040e0000d011107601c403601685000710004280300c80d40380b0003840c170011542c000207010900009001e4150001c1c00c1c03615070100781d200e50351072270a040c0c3c200c0310040480300300b0424000e440400707000c9078501f0074002e44019594202600240003d5220020701008281200004182810103200b0b0b074203c0d100401d681c084a9082d51107070419140040e24408421464142c944042c0c0720400c1c0643e1480001d0b00d410489504500d0000e003001c030085540340705980428000e0010901e00503400a00d01c03020440002c1407001001e101c8401d0149410142c169070304141407000c0441c00040d4514103030001e150303a01d030b074007856902c4417010a0000300c4254004007030001400640c0041d802025650300c01e080042c50800181d102c0c65400540c1202510103100c02032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 494175998 1250 494174748 494174767
    0x3040507060509030c0d03030b091015030204080c0105070203030715020a03050108031201061d1f0e190501080a0618051f060c0f0501020c0f030c15190905100e03 71
    0x801035014050340e040250400340c62038040b0350f848928002c50762058109503122418180250300002d1124070240ca00500707440c00d03140080c0060347e00d00c1242c6c075511200304020b450912a00c03d8a0544d041c44001c0c104442d681d000445082d00104010b0b0b9260104201803000150040b901e003404020b1050003688545120101a0403100140d01802a81d0000c001200b10010003a4509040d40c07030341c6c2058204522008148a41e0428219619406c0513034284079220f4841c003a6004890000c00d5a01e44100090940502031800c0002e08030100011301420240500c0d8042e0000e180d000346030a000040c405e0383d0314440c088071180e00c6062080280e45006203c131444580c5684c40d079659040c20031000b218a80480100364078000391000c0d000f90760800840d010841c0030b4044403011202e01c1c2c00c03203040c5590002d00a89030307401190022050720a49103420f500d100b43c035034454841d140000303400440316503107050071018190b404800c980c180074030b41280c01c034400544115814144a42c0045031a030721843c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 494177248 1250 494175998 494176003
    0xd0e180a020d06050d2001091206320916050612130c24050306060702040203060409140607021501031a10050312090117010e04033c26060f0111010f02030405 69
    0x101c140c6d604100740b01ca000d0040305030507407640b4115070707002030001000003105655000b850b41d09540005100c0e40741b4074213030010800c038a03a2409000b801058400f0400d80102e210710038400c5102c3d0a8000381c0501c6810340d4951440c0c8110342c400005001640303a41c2c0035640d0514601140d4102255116038440c070034850005800b01e2010090160410314510300707081002524500512600910860300000010703201c0c0c540b908a6120280d011401d5501d0301006800540c6a4404850b100014400c08161a80c2d00046807500c5048130b80000c200111060300050381c00d0250070051203131451030210080016103880802061281d520502e46082d01c030b442071170004060311841c0541c0080e0a000e403006000060011004680041e494100344505100325074030041d404400301c1d40d0341c0303000507100c7d8107018164000c0c0009a51a003030307a0b907040c640041200c801c1d00c0000300071921001106080001101030400701800705a641050503c0d05925540c500a00e094402c1400125142e68012040c0410401c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 494178498 1250 494177248 494177303
    0x18270f06010b0c0d1d060a0e0a090203090f01180308130f14070504091a100e0a0f0c03020a090314010609020315032b03050a110307020d0e180a020d06050d 68
    0x145040740c1d1000c016840207944582417140c49104500009030003103843d02848002e0840c45014025400c201e07510308020700290021620381c000350180b43e82d152015141881f074162a0302a10800880309038070340e10101c2c0e011900a000d42640d25201310a035002c00c030b072a12262882d512601c0f5203c644034006800c1d500b480901e9109a0089042801c504001002c2e60003429104086440c440c9160740d80d05c501c8040c0c2c410f1f82c0d0205400c00000c4080c481a0200e0341c000051a000e10300080c0b05910703d00504804920400e43c40e4800a0180c49080c00003941d1516031034249414000003007181078581180604a80c81620035020000300d58905600c01e0909000c860080c401d244410304c0c1d6400c518400030904c651192030b600815985200250824500da8006c42c068a02041660703100e103000300000e580d80300e20842e490042403001864500034540780843c0d19a80c400c400c0419600d440b0350706028040d40140b848002800d454000120341030702d41c1030004054030b006200328564140107900c03506a00d400e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 494179748 1250 494178498 494178523
    0x1103070f1202030c21070c08030d050705040b0306120c041a090a050c1803070312031a030d120225050d0f1806110f07090b18270f06010b0c 61
    0xc1404454040b1402003807661541119004445c40f8800483d904c506511038401c0080400982000218030158004040c05164103100000c00c810344440f04d00b990717030380114401c118800780300700005151402e20000c0e06e44076112000894240c52609400101911a4036400320b448021000010b501031805076941b0f40c00140704c030030400080c1896035a20761144121208841c1065030054010400e88080217010000c6811a0a440ca1605100c1004000e4580c1906002c5d40640342840ca00c441d20340400c1b052840c29081d2124890425030310554000303904421003081c44400d40c4059042e03200d400d104520720703544c46080a808011040007000e400c1c10850420340d07040085490306d0440112041001405a455038101030b03183c540381902e210303e099021104009070380142c55000602c5840e0381c002a0f000700d41107600307031980640d0f41001d10701076800b161040041e56030105c50844051170700c081c1d00c11410300c0c40e0980f031121140d010128a081d000381e1000c48184400a0b880c0341940c400c0c00003410306170 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 494180998 1250 494179748 494179753
    0xd09150503040b04031e090503160b030a0b010c0210020d02060c0a0206010e0a1b050c010b120303040803060a0306110d0605041406040c0e0301050405030408010c02031c09031103070f1202 82
    0x145520080c110300004100505183c0210301250605011740245c00242114080e100c07106200c42c14002c0196480c2d104140c040d02c94661106205039640a40d481a0b0b41c030342c0d542604564515055030003400c14904005d0510007400c10940150700c8244e0040340020f0142c00a00c016182c3d000001d141801c01808a448030806012054480c0d601048141c11101d018800e02116291190075a0080176541c403211230841c2c00031118640190450040e0100351030480081080d8071144003480301c0080340c045002d1454004000240025207890061500002c019080c0000251280c1d50401114103d46480e04130f0fa0010070311041800c01401043c01400050760700340801e00d007030361841c0b00241000c0c040764411529000b01820b4248200e40390040d0140c002c1c020701031401c01e410011340325071180c01070709020b500302410f41101600000440300c1c5001c4443d034580940e04026011401800303100c400f00c04000080c26121040603080000e403202c2c0d80902c0c0d011020003282e01e07117400b40f82d8285a12400750f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 494182248 1250 494180998 494181029
    0x90905062a0d0b0d060e1c02211b0601050901050406030f060e0c0d03091a0309071202030c0d150b0f030a02010e03150f01031502132106020c0d09 64
    0x840040c008407100388604801d075450380c03600626034024220f030041c65500400b44045590074000e403034008140f0076032204161840c0030f00201110000340d00000f11030016900642001410702400c01c9500302032001180f0705030a1000240b0200240120460007011680c070450060110340380980c071a40c0140400c0f1010080c2a266a445d050112a010800f400701592414100020703041403003010410700d00144801c0a000c000d243c0540f001d0003031b000f02c110f6001c3c5240310008640c130480440c0e0059482400628482d45050803130b4406d038008507012038140c000c428a440540d03c54400020500d4442c0700d010b13000980900120044500c4034150500c0740c21440d05200c2e140d2030203d08100290340a28112040c101307881c0100340380c183d25280c40c3d44281e079040100310500450803e0207050700d1007012100245a1180d24003003c3e8002c2086104229044905c200290061484880c01d18034900510300d60440140e183c1d00c013242c02440342481a03800440c01d110140da4400c9070f03600600580628120740c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 494183498 1250 494182248 494182291
    0xe0d080901201602031009110604030201090b070f0605010b04060f030501030b0106110307051c09060224091c02010b01090f0b0f031017010b04060b09030a2003030409090506 76
    0x944103400b00d038079511900022103184401192050a1105801070211481c010701d901403e00105140c601c29551104580029580703494080216001c4a405a4030b88640742d007410307050941130f8003100045803103207164039035030300080c6d02070298030300800181c4441da844c1d9250910140200e20707100454000c0514000c010b00c00241c0506007281075030480d1030000c07001c00020f61150f15500c624000613040e071240c00403e812181a00841001100c5a5a00c48584d00d68414040c0ea4070030344030001c51028280480c2a440000e000d01030558840302d0b0380d084540b110820442c440d032000d004200140182d44641e50440c0c0340d60803140d40c02c000e1a041d8000c1207120300c0d00300781880600910864400511000012420f9400030340a4200a003038013a08030400384e01c41d0f90600d402414101200c1d030286041000010f030000d84074058800042c1c1c050040d0268041130794510302c1e12405902c000f020458001d0321500340b1b841c10409072002e020340541c0041c1d00c00e2107040c414038090f4000d01c054400b4076004c640c03400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 494184748 1250 494183498 494183531
    0x20c070905090106030507030506010f05030601080a120302040e07090e10120807140d09091505031903020f0307031805030a020d0b10050402120a0c080c0405011b0203010e0d080901 79
    0x4469a8440c0058030b078548601460240c015a0700180051060b040044140540480c1041c1250080d00d85d140324036a8840506842da1380034800c004264021001140100710180c42003542c015584c54010300d02038658042c03650300881a1040400920503000034080302181e03071a055000302d1580000d080c0700d4038211804449803001c1e00010407450020600d0b00410901c0031804141111386020f4802d00c500500740240005114814100c00c9030404140c40032882801001009941c80a4050440341400b0485518080f403a07100c12000c40c402e88401900a60007440544081d600c6603640d041c400f10042e031007208498040d00158400e82103a00048010f80d0b8458100f40b409034450711014090361040c400c504103a40c0d9500c0340341c0007400040d90001002c103051083e0321944030010204840e044e4140221540d103012100c003000c95004100c248202c7d8000c403241c00d854040e2090758051140f07641d000c81d003981d0019a680100d680701c02400540640c002c101e17590b00c024000001c0103a41102010002d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 494185998 1250 494184748 494184763
    0x90a021813020f030a081209070608060d02090603100612030e0a0e07080403020f030a030903021507050301090f020702060d02030615190503070c05120a12050115051c0603110112020c 80
    0xd128043d4858000001e450a12a894000b50020340c215115806c400e0400c880000880e00742c000c83c040d1080c0424030b0b9003d210300c2800383d403010341241744a04e1541d0901280000140c20164103124205140842041e00d010308409032001c2c000d030b00880c41031031a010b08a200e43c03ea5003031251005100501400d80c00e400e9840d400b0307106291081e0b550725981401c2e0704091758900e41050a010016116103400d415030425043c16201e0341c00c4401e01c44070305a070900c80c0407082d1032200004400300300400c80881580c01c610218160b0700d500610381942c0764000348495002181030410142c021082103010f1500e4040c100710350706101031981c81c01d2040340a840040f0340b2940001b0900c000800030030407080c451781c40f09203c0c592110031a012940b24603803016448e00f000c55420005005e00b2200300000c0c01500505048414500d2440c03521001010b00380c0300e60300321000c4410303490810100054170a4460181320010760060b6000c40c00742c0143c00005207400c40a21415094500401140c0294000040c454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 494187248 1250 494185998 494186003
    0x60b040605091905040c0e07050901080906070c02061803030301030f17070b131a0703140903070c0e070509150304051b10030c020304050a080106080c01030b1003020918090a021813 79
    0xd4139681e506d00152140343da44c0020243c1a86c05c0300b044002500800100000c003170903250183d090741c9130f10344155507140071100c10002548844003000142419405011502858480103800075522008203145400991007907a0000e00c01d2191001c1c884061000890384200008152401003070f0b8036960103840002d803210800c608001d507040244042c1c2c902c690100c540b034034440402410440f00090181043d0300b41c22040000040214a806400208441503564088201034202d07140c00151050f69400a20080910008100c01d0f40123a81e00070819004230b001c51840c2d9101e092a041c2545401500d141a02408000448049595442000300282a030070352402040c001107014049040d405290b07c5039401849001d03000c174208006402000c1910b19102c110341c4010206070045050390a03400d04250045070038410b14807010302c01d0b0020070307410001500c03016202d5640451900d0405c01124515401e4201e201d0203811441c1140741e003251181d0754195101181084e1544008040351500300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 494188498 1250 494187248 494187251
    0x804030c02040b060a0c0201110c01120519051e0906040803060618120a020301050f0601140a1b0605060102101a010e0319050c0a06050a170c090a03060b0406050919 72
    0x120300310742d2590042c2004400c040d010310b442d4480d9880c05060442480001c1f0702160b4000108242008009000300b40c0304c005940b02101c04003510001c100400b800392150003080d000c0d00f40382e48800320502035240180e00c03002e1307040802000c061138104c8c1d07554040c0000c42150000410301c400300303404800f626088541103408503030318101a100843c0140540d2407858100f8038100c06010614030215030006028000c0e0004e00055640481c0f546580e001107941501141d440a0750100741250a4003034134220900d07041c01d0010780803030745031044812910402128000e88071400c0003011350703050207400b80e0582c4c0d0071414804402440345c03824a058003284003504001010303119031802d079000c2000300255400c500c3c0c42038241549007072490321b82d040204041e0140d48243c00006220784100100c1d00d10100030f90325291401140141c5404c403010191003918141428082007945681c0c0100c2c48000f140718a400040312600b0740709000903a24075502040c89940c2036010042840c171040110351081d05590700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 494189748 1250 494188498 494188517
    0x11011d2e0e0102120c01140a05180303190e071806030309060c1203020f0f03040c1d15010c030e03030c0105070909060b030604180f0b010303030b0901120b0601021f1a0603010303080403 81
    0x40d180d00400380b4000c11f01d81c0101c54070903c0079200c501d030b02c05030080103454143c91410190380490b070740ea884181c1703100e191041400301450700b0b48000e81c485014000b40c030060384c0c8550340d585003640b01b00d44101c044603446a6541c6040081640010001004005508100c0c0c0590415200d15601003449a02c0d0414150005404c2001c640c0000480d031001660344070623130b144e04007800c149142040500802080420020720b12120145000c04c4901c920b01000071b0300060302d00200110340080c0080303011010300c040d85000c8101941d0034000b4195002000c80000762a01e403840000340702c0c0c0e0680e88950392132440d02e6070501040324034004490344040305440114225400c0c10710070500701c10f01803000c4c004d0001c0030211010000d48120301130480b80281c1d030621902180317404202c0c00341000c1c07040b1801070010440d0f510000b0722001c0819880b82050054500441c06003010600e80c0e403810014000042e80c940040c882e00804e14207107090f810003030f9034660a6606550b0301030b0590902400c05020320600300d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 494190998 1250 494189748 494189767
    0x9040221030711040c020307020a18090803090627280807080316030605060a120b06031f0f06020c0111030712082211011d2e0e010212 59
    0xc0a940c25180c4140441c2e960b0489810701030075404078003490038466400d150b485034405200105540c101d81c1c0080c16802040e02e409600c0c1d840c00140d183c00000c0c3c41e2209070700390214220038003940c421003441001d0f11603454100b184448a25140e58140010a0700240d0500000b000240104132040b480702c0d003502c104080202e2094802d440e0a0003802c40100140e00d1003001200d001a60090225124070041d480030904241c00b541c0190048640082e014001819981d1103070510340360980000c1c0b400039814030400081030301a4801c0b10350044000341c64224071590b000d04810703040100303e12032118090030f041c400000e483c0c600c144440c0d41002501124404400c07401c0c0100e4000395403202c0c4804140300013041c060a03804d82101d01c07070740207130b9086110b540d080459050070749401c6d4440d00c817016845912005441d0b814194814a08c054a151031500468a4015400382101000c83d03125402810102900180400390000081082400200840e05903000600980601c034864503098a41c2c4404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 494192248 1250 494190998 494191039
    0x10b0f090d0b07020a15020a0507020f1c0c23030615130c02010b09091606050307090b040f050301110a021c11011a030706090b070206070c08060703020c0705010e090402 74
    0x1000d0300607541d0409000750f041e00001c0c6850414418803192404400b00340c0c0400072809014915800315204010407401071401c14510010380200030203940c0c984052000000603c0581c400450307a0183c8500107208880c08a07520701c45441d50342d46020b00748500365020070b441e1200506140720180c2d089040c04003d0740c440c111480ca105110008001c6a014004003d003e000d08120160140410740f020481c0d404003c940d100000082030b04c41c1300f841745805c800325032a40c001090703c2c08004640b60041051a14100240002d00503400300c40c030b82c182030a08141c2106e03504150026107040400c44403503c0340c0c004c01d00d584c4841c11050280f400100e42441502e28210403e00040294a03003105582401d081119004001c40260110307241103455250079110381c0344c0c40c040d00320090410b0280030b00625042c0300401c0410b102d5040d2802c4250340707060700743c90032205071051408240c010a042145500030041d2400030b010900c1c181042004040200c1c140b0032000c0c001a0041d8100c40400e16202c090707 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 494193498 1250 494192248 494192269
    0x1409031c0216080a020a0b010b0c0a0b0a110d05060310020c07270c1d0603011d0a06080106060c110901051c020d14100509060f0c25030806030f0105010b0f09 69
    0xc01d040e62050a081300a4545180c880102c03490403024001051281d400340558034009484030003040101c0c2151541810440010486e4640359268201101d100004030701500304c0b103030071500100709401c00100b090304100ca1099400750962050003110a0880c0000300c50040f620741c0e041003000d803405020001c3c105507044001c0c800c40340c185800d5003c1d0561114441c881807099600107140f400f032032020400c1501c4280308112122140c100c030301c0c8100390552a1560001448500001c49964800d0748070f00350f541652009011642080c204402d12000000041c15103100725280d4285c1d604080008000200481483e003016407a544800210340300c6030f0111a0366a0454a401280c40c401c01a11b595402d14151a003042402d08020480d54500002d240d4000c0d88042c2d14400310f03507180c2c0d6400245070005800074000551070003c1400b02581c0303859500300c00c0d0007070b59418101e14010061529103100442055103d0b0302d090b004006403d00ca8040e06c940000032440300d59101103800025018022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 494194748 1250 494193498 494193503
    0x20f16060f0612030e090c091504030203060c04150903080f0f0c120c010c080103050a03051e040807090b010f080103031805030304090f0605010206040c0e07211409031c0216 76
    0x50002c0c081651015640142d0382d061080d501d0094605050083c001840f009a0340c0003030150b400d0003070100b20310741091090420480b181c4a5401c2c113669030002880e04900792840410000c0000e0180400340d20041421703500081404c004154a00e541d5640c50184039141c90000121b00125001c4a0a03462100300d4594a09040c00c031010383d5203000420005038002804a03499602c0c01c6404040c242c0983c5482d4100c1c0e400002416022510341c07400e481a0b0702402280859a13840d000d0321001d1800c0c0c00181016100c038400604050342040b24041c110f8200c032501c00e051110f104030b0524480e41c0200c0142c1542c1c3e141c90550342403079518980030002d50441d08410b6040c00045000300e003c86072503220106c5510350000c14444c0701d5a40700160b844030800e43c1c0242101c2424107050210552131a0540d4001d1510f250039180d4055218054104088405600048640302c0080e011695081900315410100b0300015616050071180c01036100e89030202c4101e0115001b14070780d04426070011441a9094 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 494195998 1250 494194748 494194751
    0x30809120a0e06091201142a09061902060702060a050f150402041206020d110415030209030a060501080a12080c070201030906090807080309060a020403030509010e0f130c1101020f16060f 82
    0x8500d01700d6010748000300e101203403a036412000a6150383c1003291000d8203c0044d1941c02c5008408c032240b44140c1c06001440d07080641000036200214a010954150001c01c1e80a84410f0030502c1000f1b04240000e0240c40b0800d017403005002424100a04058211818141da000c07900740100100e0041d000d030364001c5130903034030001c0070600380004c80c1c000b46400d24040c07104110480703020b01c14818901030340c0500e1403c40c9508544540603800b0b07500600c030340c0800801f191605075441d610340c01565426000303102c4680001c5d00180400840825213080c5000b42c1c00d26a6007881d00e001144110300540b0b202904060f103800c041000e12250364841d036041c82c3c00006c150b99848072414440c2c0300341d02c2070300e920120388101c034006201c1002c140300f660292503056481a00c4c00d0140c00046894481d000080e0f80d0203160150441c3c12a9284070810b40d89442c40c02c0702148200d80c8540c0036000349101c4110300c419034010481000c2c085414011141c075024103143c0903440d0030031402c181004001100c0d0400c8810b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 494197248 1250 494195998 494196019
    0x2a0818060910060911040b0307110a030302070302011d2d070f0f1707050402180a26010515040203190c2d0c110d0203030f07030809120a0e0609 63
    0x31880415142442d4800c0e60091010543c0d68403454211145811424000d0005220510000c5283c134001e64000080c1e03e4610640da100c0f0f18003600f001c0200300101d0200303078002440800c258083c0035401c400380e50419000c0c440c1c0409100c01d03131211548420600c0d041e2000140c5d45480300a20101445419050201c8440903218190960010954010030b044102c0213000060080e00440c60f0b08207000500000d450383c540307080306000c0650050500035520990404006c0c45680341c0071607141c001c003001500642440c1c001d00c0645005200b0140b082042c0c0d04000c00c00000d010454250f4020240642e80181c0d607a40b483c0c1c40402d0808002c80e030503203640c149003007406003642c00042001c41c1054111400a80d000d4424040c00f0305421030000390100b5003070003071034021070310340200b0800084001c0e041080c05c00e2141e0001782146d01820b40d8011103040800c00313005042d84076418591100400c0000c1601d000032500709a610300a4108410800c151000810055241c0c10b00303072000c000003c1c2c500c2150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 494198498 1250 494197248 494197261
    0x21040606080f060417161e110d1e030302130608010503240714090a24050412060f060f030b1801052a040f0b0309012a081806 55
    0x6028140310701245072050030039158481002040c0c081c029648802c80001c0b000381d2951240454201800c103141e110b4480c2094400701d5014810101084d618150445401c00c55140c50101c00c01c2d0302403414000c61010000c68005011545010011a9140c40b020b07540d00c03007860700702c0180c8521140c3c02c04445002d0380001c0c0c05c5403c8441e403410303510210309a60284103004da00d40800000100c5e81c9040201c03000115031020b0141801c0000c05044054080c80c04140801040d011700841c0d001d803003602000507209102c02c030030300e603120f02013042894424130701881c140f00d820b01215045c0014042c691340c2c04c07140444180c1070f803201e0018070800000982060766800e02d41420700d01210f0781e070520701d601440e100582d1810710415218a0a50514a100443c4441030b1100c1280814030f14040140400000c11100c40c8100040e0003032418040c80c5a80303242c076111507401d417003503040d03c0d0b81c010306c00203d10580c083e204240410801c030a171414401a60750804403a408800c0403000003a60b0150400f403141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 494199748 1250 494198498 494198501
    0x4060f060e01210f150f0e0a02210303011a0d0501090203062e1211030c07020a080307020f0f0310111b060c0403110d0510090b0a020c0d05210406 64
    0x4859034120344030b90600c503054400c40300b00c0c0b45520080020381303002101400189104c80003203c80e600400000780704542000840100c40e031311008503442d40e11485000f0211715040c1494142100d19142881c0320802094200b50740c0d01041c012060f603001080310084603000ea603405e4030145104103030207000301d5035201002d40083d8416121240904424004102c0d8901d80d00040040c003500501007402d600030030b541c21142603000066000100b07444000e035082c0103900c04041c40c01800d1001c07419903240160f10400c4264621940b01107500d80081c032a00740540c2d507480c1001940d2609459500f4003030709600c000b07820a0405801c1100c414940f20f03500c40087c1103000a1f0201c08a248181901825200c0c5d19980d1003100f1203480703100c80d81c1044140002400d41300c040403c49009002800409100d0355070070300305901032103800c01c040e50b0b415900c03003030060300c0030205e42121500c4021440d150030f4890054a442803005140300340080000e041107807040e0340300b8a00c40480c00b0f040c04210b504051401740b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 494200998 1250 494199748 494199751
    0x1b010c080a090e13030c02120114150307081911040e0322140d12030608060a0c020601090905100e07050d0f05060108010b0d0f080f0a080a0c050a0905040504060f060e 73
    0xc1d2510403500004d25964403071003040000340e01501c1ea4944150305900300711044e010700c12010419500c0b2100d40c100e00d00d8814056018403000b04480901020f031405151503e403461f44001440d51140e189600c0c2040e00e015402002c41d0031a06c4402c3c3c2d04c4440c0089000750884148608041c440010400e4400c0250840000d4600c00800311105007075a0f40301152910702000c80c49030380864030190f40300001e5520300902150300803e040115100f5a111002c0d420704c0012101d50a815440c0c0c05a03404469041c40454050302d1400390801c00a0007544034280e41c1c04131421080c00c11940c1d0b01c010084280100901070040038001d004021101c281c0c40c00346094400312504075120321a0302c001044080044c091083c0350603018041801e1140c0780d440d42c0c0e03601c0d04507250a0300c20034001c0103188a14141c02c401070000907655100c034031280c100075030740000b2503200d040103004004080c45502030160744540461304a03081100d020420342c41e40c0c00c201004203241801e102d01c080c0f030480f0000b00741140e1351619 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 494202248 1250 494200998 494201009
    0x1a04030c091514060d09110603010b030703060609030b0c0d0609020d1d0c150a0507050d030b120706080c1c02070f0c120809100234171b010c080a09 65
    0x1c071412540c40501c1e4a0000c500040035030301c04e400b880000484081503000081e402d001f440309105003450280420280da000703030840021504008200403206400d401900001c000500e00480003900d181c9500701c11100c0541142c5180b640022042d102203100d4112030050711094800715a80c1c0030014100d401440980c0e81c2001001107541544200e050102e00741461410141004c001200c0465840503294400380d4001d05000c0c051040303001180301009041c03810340240d180014030a0b0030601300505400802029050744c0d1042c0e00a100150b403100c03a07180c010340d2491410303803503081600c240840c10245003222440f07540b012841d24180b086c003618141c8154000c2a1301055a070320f40c90354046e403800d0f072117028000300c808004251681c14001047c800185c45803040d0b0b40c10013002518505a290250301d04860b80e041000000c4440010800b994007c103443c4203d403010000588180ba12940ca28035900130541c103110000159034041e11400d9500c96203d04d900d580c0b20f00c5050040c20258050284 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 494203498 1250 494202248 494202281
    0xb0c01060b1215011713020915151615090b010f1a070f0f0609030e01030e060402121f050f0606040324110d09021008040c1a04030c09 59
    0x140c0d2090700300455503882d4011003009403541c0c8040d0000c00080b4040c4502d4100608902d9043c84038104502035400707071501c0700d6115403802c15801000034807840a40309400880782c544044d01e051340d4450003084003404407540c05440b80c001c030040390811040141c0140000700540ba0135104040540e000c00300140c0f01d1604480d0756621001b44140b0b0780101d008145506021650310030400f1480001f42100034450300303000210300d81c42e995490500510800072282d00d52114048000c054001d280c05420090030b180403c80103038043e041d1651076602a10181c050031001a242c44404424800708040038502c0c4110a12503440711403400050404540026410320048080f0300a454044211802c0306d82203103403038050100040c41c1d80c443c0b0075104c002c40c1c40d407036890a4071a604140035000d0a40c444090310005031049a50050061425a1050b03040400c00780008000019041036800d0040e1580501122017106000203403014900c56a00b02900c051454035000907810001d4101070f9020095602 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 494204748 1250 494203498 494203511
    0x60f042304151509020f0424020601080309010e130207020603161103040f061d0a06020705091e0415020f0316020c1503071b060603060b01110601051c050f01060b0c01 73
    0x1010220789062800300400d0300d43d0001000f16a4894028002480c10043c010785020381d20081080b03a4095410fa518141031780100070b07030328540c040c01a58011705c0410040c0d0300d03100300140001e00610701007094500c2072010070350051255615506803504141d02818090741c90404001784840900c500c4001000511100c1d806995a500441503904580b81000c0900c0d9035410442d0540c0c4c805190f5601b00000c3c92041c17900382c8655140310b20721000b0000da80140103a9410700e0180140542c2c010880880541e902604408495540c3c441c03c1c0d0168008181003480041180804080e100e1000d400d000301c00e000c03040c8860031241002c0c4286c00314090b0201c070340c0051120180304070001c60b194103c1c0c2c0c1c41c0e014000110900c0c0180360301142c0201d1000584400c4c2500c1d0384810848400750001e803400c40da65016043e09581100d503c00041c0e5030017008007402d616050001d250000c058a600b0b410400d40140e03c13040207030402c15007561211040007403003040e803544811081d036000158824000e609004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 494205998 1250 494204748 494204783
    0x10b060307050a03180c03021903080307110114071806090305030f03090a1a01051201050702060105010e0d0501060b030f07050403110409060b040207121d1f09150801060f030506010206060f042304 86
    0x20f8074881265404800307181103964158040d9074900b482c414010030b55490b605445106203510b82018403910b201c3d11012d40f01021082c070b0a8180019800040c14001103000c244049070b400000d56001240080c100c560301d944003441a801d00a8880004000c000107801c80c1d40388000d5000d00c00d06a43c4151009081c0381c01040a03907080c0c8030184e80c840c0160b08050014889540700b0012801c0c0303940050074000040c001c03a62034508440c101d91064003000c40c007105103d8000707881c1d00701d0341c0c00c02d105103000346c03c113410760b20340b0304905800100c84e070f118540c0d419250b01001165040340e400c483d40200308644581490801e45102204031512200041d15079800d640244000c2e0303d8900801805000320210400402e054110740307200c1322881c03060011745078001505403240307410460f0b81c10761951900c0d0107503d45000600b410008100c50303000d141c14041000b05a076270010300325900040844120258500c2c0384042401840142510060703866160025500400542c04845c0554421075000d002100c00c00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 494207248 1250 494205998 494206039
    0x1103010b0d151206020403020f0f03120c19050307050c040510060e0d3008220f020a08010b18090712150614040e010b060307050a03180c0302 62
    0x900912050800910a038103025029600a6500e102c00d030704490201030302d0f610301c0c0004a850140440f046500043c0074403c60420301b009005000003602c3d4542d18000c0c0034000b0740c0b50504c000c4145020603001c603014454a03030810a8481c03220142c0004803041801e13050860f01c3e5070101005450034440c100c480201401d01c0d106092007501c202101603400384c00d080c012205840e02082d4103910628103040080491015030515520500401100e4152004039060692441c07403429a8002e0104c104200242d045e100308101c2c00401200c40200d0445159103000d101280c01c6070406134100e0b40903a008284160305500642d0b0845080340c800c2641151668030099800088035114040d4014810400c26007805107941500d152060711030142144602012001712440c550200c0c9868460312104010380c1002c0c801c141c90000420000d2000b202200c0104039184805003109c0f00300300c030000c0c408c182d951199021150341103520b20714800710080303030520020200307490009911500e9070030981200d501c02c2d07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 494208498 1250 494207248 494207251
    0x1207180e090d09180e030403021801050109080d080106140706060602010e0c040204050a060f05040b16020906030c030a02060a0924110609070902070c0e090d1d09010b03040c0e010303030c02011103 86
    0x114500102d0b04813021040302034107214500a002e440b052101000507900c0340741c002c441d003c2c03c0c04025800d600d400001001c1900c40d51205440d42c210090f19698a584900301605541c554200380351001d0800000c1201c0f44640c0c0c0024024500c4c0c640b000c102140d0640081170300c8080e0328120340007591980c00304030492240d841020703403048034142d00308030702c40c0543c612950384842803c10078185503841c81044900c3e4011900881005c4120350240704610f07140080c990800000c6d0010010300d002100881d03034a00404501130701c03504010a40c100118445d080036805426a83c0032555800001025a20f0b00c01b040386007080400c403c40c038031039089400001c84920035080c00009268484c038100400000354003000741602c8602244102168880f41c110f442c0d802604060010003008400000042c030582150130b010a900e00c3da020292440c1e9982e0741d600303055030340000b40180c0e66116482c04200c0c0c0e14059200c105031424680001007415095440359810b8000340c0c00901074001140341c0344c60241300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 494209748 1250 494208498 494208509
    0x2b0f0c0f061d030109050f0f100b0609010c0512040303020a05150c03011a0d050c09040609020c0a080c070305120a0207060504061b1a0c07021f02031207180e090d09 72
    0x10844004280500019035040240708050000100b46851b03494050814035000f00364280c40d1300c440d0480ea01031000b006140d985040b0100d08100900c010000645284100d0030b038a8101f1010002070024024180488802d41a8035032100b99269075a2a02035210130440782c007628240a4a10a454030a00d05000da600c6405000041c40c82c0d0381c24442008400c1c0441c001101100c90b0501064805420074442c00d406408850302d4140c64461400800c02603502680101c400503006204440d00d038400010800072455022203040e0711580e02440403032400340c2644c0040c10768031810307080f1030300c02c1d9180d001800b140c83c0c50760035101820342358601a540d0384501c1c130682d400121103913a140c01d02c2e45800490134080748548031a281c40c00107982d0040e0710301001c0d280202c002c54002040c00031842c00c140000c000c603000c401c0582903000303416006500ca0080c03000b50400310038204000395180d813040102e02096440d01140b494001e480388580083c5000440362114135110348040b440005004058007012140b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 494210998 1250 494209748 494209757
    0x13150806090606190504020414030c040b060a14090303040f21020901030206070305071a220b04081b0d02011e0e06240d080a1b0c052b0f0c0f06 63
    0x102c8040512601c2124034004003e60044d280300403445a4440c00100300070f00c0354440510141420408060500c1c48640200788294581001280359848400c00e80c0c21784a00ba04050981072400c85d110940c6119800034503506000001c1c012440b20395020a40041e02e60100b11126a10045223105043c1201900c001e58480e450000400040c6404401004654424174016060107110740e1494070f1805054008840084400108041320807054540c0c030241900040b4010b03074a030305441e103c00d400381c0588090000c490010b11401d05c1c81074040e612010b00710b450111014040c01c0b0b04000d000f4580a415a50504144c0110302502005405207049001c0540082c00030354480e00341e403108001000400d151010300d007180010303050396803020401c646030088041542d07070511010010103810700c004d64924510221201e00e804184452005400d0301d4094034400c180c14401054000000240c075410412444051000b070108264288218911403192000300707015503c03038200c0c520204541c0150400103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 494212248 1250 494210998 494211001
    0x21c0504030f11032b0c08091006060e061e070c0501140724241e18090312020d0f15140409060914033c07060b131508060906 55
    0x341080002c5c0c0c500c01d40f034803072070542001e042000f03002903d150503225800b00750810100442c0b081c052040884400c550142040954181040540303511041114a4090040440d00d21205031410040090b14003174052102e884404070314241e125880c00b401054000789240c4514848200301e401a03c001b030703900031000c14903804400700c205400b2090307141510b803d6841d201c4101003422000a12407445040405401d000d0703041c281c07041802108a500c000740182042c00800c00b8000a0031580c900401006010851540500f0203c800020704105205454400180c107111a46503038408007020300000820b020594148100500d00f1110380308012128000c100014094a0300340d12000b0014070581c8001042c84207500c07100180783ca8062441195800059101c2010010308401040c03010301c1100c0644512948404890016440c111110a09404151070701000b07075981002100d1100034016110710146448408043c140d140c4510802012081000c40c040c000820000e11808507100240b019 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 494213498 1250 494212248 494212267
    0x2010c020d020a05150c010b0a06080f0c0d0c03020417010b0306190f05040308040b0112020f0409140d0e100905060405061b0f16080c010c1203021c0504030f1103 71
    0x4506031070700c040340e10080014001c2001d83d101c00300e0f1850004c510b02c0c03064803410091980c42c21502310100b02e500c1015120401c00109901c0040e06034851108400004242c6514401000502400700034842c07540c02c2061002c0007562660150082b9091104a12510f0301040300113800c8a00050000d1380680000300001e40c0310204240700f0600b040c0d000000940c07403800d100d005084900c1610101d001030300d204188014070407003075869805416044811354104150385e001404044a1618075030081d61200b04000070b019001100d44044141001560701c4100d030707410020207040d840c400c0544140c00b040340c0c02503910b100e0154401694405007006190034201010040942c01401c0102c10310484030003680000c1400b4060320a100c1d080c44000c02d8505212402420601c2454000b02c580343d0080e04070b5142a84d01403555603040f5000703148540c040c1703d442c80c1140684100000d581c5001c000381035100c000011035100c90f12030342c0207980c0e0f41e448a0401404403181200d0301c0d800c0000f98028802c0310131 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 494214748 1250 494213498 494213509
    0x90321021c0c0513030c05010801081501091a10090e0a111b160f0305070e06031c020118080d05090a120e03010f1e05180d0810051908010b040902010c02 67
    0x6003040d503401c00604007003503070004444044c0903400480d50200b50843c10019543c11500d01405001801d0280c009040c801e1070240901e1414820020903a88a01d1080e0150251011100301d107640035010405503508850041c068000912032540070041d0b4000050f06e0490300c0c824800415405c01102d483d020700f0600c0303030781203c60003c090085070141007240d81c055900c0072100780080002e0b00e08130080614604003907040c50f000e1b90011088001035010006680d4022503c0d003000410f2841b288182e00a00c1002c0340180501200c050550802c500b140082c0083e28000c0c0410b51070038032003030043d03a030741030440380e210146100000c3c121120032400300203c80c012000306410b444003500000310420081125810754001208034411081e0000008916075980d0040300d40c0704600c040d503424401c20510505540d43da5407070f040400c10130f0349004242c00d814038002140050000520038401c040b4002507c840e49146480340e03e91561174106c0110ad03d08180c003407440b040743c05848400042e82103400740070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 494215998 1250 494214748 494214761
    0x412080706060807080d030f05041e1406090a050118020102030a0c03020f01060b070210020706080a11091f020601060c020d14030c120408070b030105030d051b01090321021c 76
    0x44941d901e0340008644114100008401890150000c201015940c18043e00701c4041c20340060060741410100008201100c47e0034008502c4140e1088065050f41400704110f02c6007a41070b182409640c0070b002035224001360081079140280001c010145100e41c030f540b16080c040d9802809a007081c484101418000c406010129010340195201c0070700700e021041c00c44049401007241c4130300114900044d41404c8200c5c00c2d44200c1c3d400101301003030410030080c080900042c041d0341c0040e12620158070b9a4110320a0341c2180c40040e04409220a00c0400300002580f80380c0c4050052217820000240644541d01c600f0300310340c016000040f1070290746ca44020800c20800000c260b07200802103015812010000c082401124096950700c0b181080b0700e040c20403845601c03c59400d481480180706c4c41c0d83c04210841004100c1c02c1080d42c0b03205a0a81043e1010b29602844040d480c0007141002d0540099070706062086003028a104500e6112500c001c81c0904145401103d00201c048c0d44d808600c0d91091 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 494217248 1250 494215998 494216003
    0x60103030c03170405100f050f0411040906050c18270604060305150f0601030e070909050a0213150e090d0309080409150806070e01020312070c0c0303020c0f0604120807 74
    0x44030300540f07400560204481c280c82c1100d00303030f025458410344401103210340c0c2002d00500300180702a080c01d580c800142c0341e01038005840d0481018851006a0b2603a02c000d210b60342c0700c0020301c82c03032510001002a1703070024041141c1151f5024001c0712540380c0045003528501214021014a2094032149403020300001c0540b6001695540c0200c08503004010b021a081390040030b1102d03500d014440f04810700d00c0500024149824006201154035000c6031403000d40d421104006004c0d041814030a10b043d552a1019420503401c10401407581310340d401003400e51401c00c2d040c1c5440c0780d13a1a030b04021034000700c0d8031020b25049104044070031803217034001c00c9015000785901c40c01d01d80c84031600701c100c1c0e0f110100b240c00ad550103030040218030400d104107644174800e800c0c00310051002d01c001130344910481c24014000306107a00010521801100403180e0b2035040802007500d03980720b2502940c2d40c80b207598444e00c030b043ea1309450302003860451b0449050351101581c410141c110750350b81e50030b00e41120608 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 494218498 1250 494217248 494217257
    0x100302090919021c0b1e0303041205070b13090605091905070c061e060e091e10020d09021c23010f0e0106051215010e1801110a03061205060103030c03 66
    0xba200c3e1006945052a0700c0220000072045d010400f00f1000550001c20b1072800240c400c0944003c0c0d5001c07080e0b03000c03150a008402d0a04050b46085400c081d0140c01c9410f15501c017180c00040300e048640d41d103090b03482c0c07100c0810003a40c0755000c0094801c1d0840d424154828a52481c4500340402d811094210285c0c1c00d08070200f2440c0e5031910281c9102c4040d108008922000c074803008035240c0200d00007445803410711801c034104002016140d21440d80d8910340b000d280c04040b5200c1101f0048240d0b00726106000315104c00070541250043c20028074260f202d020742480c034410050380d030614030105c40d40c804040e03046d4041c20340300c02c8501c182061181c0c0295590300040d0070048031601500035001c01907030001802d1410a41000615203078038219180c6640f014041e828400d05000d000340c10741324100b55100c20b42e501d04100b100c0c0c0803034502c080211035007041e20600391140c1b0300010b814509035a480502030b40d91181264106000396100c0a0702c7d0f81d00c040d0041006c2402aa1814821406440c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 494219748 1250 494218498 494218507
    0x3021305010507061803120c030b1302070f050609010606300e01020d05040803090d05031e0c07080c07050a090207050a020d060603080316020c040b1806210a0210030209091902 77
    0x240240c07081030b621303002e8000c40d1450801a4041f8034500c500441070b0380074202040070024840200703240400401d0083c840d2540020250f05022800440c01038440e0f000c422a8440d16102080c180a00401d108981c04207a100d100c0645110304550f41400016400b881141d031020407149a40143c0f40641005100e0755003044510312482c4940281441940030b0200c0c2a540c3c20030300f5040c0e14099101c841d0400b00710080c0184100030b00441c1548000036071f0b1803801a0181c88240d4407841601c141d5400030300c1c107400000c008444003004250704085138801c0b02d90b40c0b0180e948040e9171059226162004102ba0071a640b50001444c002c40840c060f940204800102280c0341ea5880e01a83d001f80c03050300745003a00314010741d0141c4c0e0402180c0304001090380e082c01056058400704a284030814200f4140c0e21045000547c250fd9507111190040441c07000714a0039218400b00988803000c00d0307800ea0203401c4025210032050302900881d60000805441a03025a41d002c444180d21000b50915202840d002c21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 494220998 1250 494219748 494219771
    0x80a0b040207060e160323070905040b090f0708030409020c0c1504140a030b0411180709030309050a060f0c050703061e1b020607110708010903020304080d0302130501050706 76
    0x2000d0540b09115010019001842d40e003c10f207007881c0040950005681c02c1400c0c0b002a200245a61121902501001c45d04060344c1e0076508110154001500941c6020100010701041c40030090003016410265084c0501006003903484150500030f10540c0d5208001c100618500c0313900030074420411005480b0f01c013500000142c000300400d40c00001c80700c804182840940821b00d80d80382755100c101ca81c4840c4038555078035112071401c000c01c06055100144c40c00c00141d102c600480381c0090400f0600011482c0801c0c000d002b09006000c20340018a2165000c501ca0900051000503600c180d160a6002c100044048400c4501c1c00d50881e440c0c01600000400030301c00c5c0c00740800d4803420040390b02145c196039902404850700344d030754803280100c1f054030760040b1500441c2240d04500ea40c507040d0b0f090099251410303d84030352540070f508198a8070100500385a80840030f0800da59640c01910390f00381900390704a007a8021841158010608654200034541c0503030020000c00d03200350300110f198104203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 494222248 1250 494220998 494221001
    0x3070302060c06010303170402030d08040f020a0906090b0301230601110307150525050f09030703150b090103030219020a0b030a09050f1f02030402040905070902130f060c03080a0b04 80
    0x20151901c2e16480030b4010b104150f0041c40722843d0060b4091032528a14142d00065500c90a10a2000500120340c021506000500c41d54202c8142c01a21012440d9681c640300001005140f142c001041d140c56102c910525040c0207020350040100300c54050300251100e41c22220802900050603c0501441c815000500f800074014160046c4030207000208144002e40c15220700602c000b55600220b402c0090001c0003c5040107050030720b26000b17031540c040104241280c0300c0c0503002c40e810b1150320000010410141c00c0e40c01c1c100c01d15681801100a0082842602c850a000050140e009130361350900e43d881443c041981720740000d1030030030b0856403038109000030f52064502040d41900c0d10549801d0141c00c001004030940c005d402451000580c540551151510380807088100d900003021800790741d59600310591040c4c10030281c036280da98a00044e002584a0300d0100032120311185d0000c4c030b0900e580e6821040301e0040d2902c45220055640849a03010001c001100d115541c803080101c42c1c545 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 494223498 1250 494222248 494222257
    0x210f06020909100303080f09070807030b060f09040b0a02180409030c050c060c0d050c1c17010806070e0103090303271a1302010f0201020405060a031b0201060302060a0e0307030206 79
    0x120801691411098288114914001c000308101d8081e400704000203940301c1c42c0c155201c550b07820011940e44480e90510704000f003d81c0080d2091103180320110038007404140c02402440c044801861180b40300c0e040c4007000c0000c1b02c0143c02c4030075140c00101599900d40050004c10b07040304000e4100e2900c5c80c000307800c0311004441074000a03521444482006000c02ca002c1c0109811502c2c03a06204a4a0020356140a218904000c000d0041882c001640c0100301c80b40784078035850321001c45400001801803484103410410fa9403091958000a81c1078000f040240c000d40ca10740e60404015400d0006501500e03c8200807410569542c00800c040c0031070500050055622002d5002c10b0071003400c000d170f09a9542c002840408003510144110920020320088031203138282082d840c00b440e40315042e402405070786d200301c0c0c000d20b0020790600380d00e078983d10028907103091070001d000002c00d0060482c02c850103400001c0d0005000c1243c84403007401118200e200300710050403966126221f41c00300c0d009400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 494224748 1250 494223498 494223503
    0x2030c04050103201812030c011e0c020604030e120a03030606020c03070518040c0b030108030a1b0507050625050606091b07061d06151504050109210f 66
    0x2010500740210340e80760098a444004044814581c004101c00c089110703c680180d42d4004101d8203076603a95034640f44424a4038026034819640c070b801d0f40080d03580c0130300001a2aa1044c1000f4051219905001d01c959040e05029900403e020303599641c0035514900c4810810343d0199200914080d103c00c100b142c0c08525200c1d03500452a1450800060f240c0308035240428800d4016041c280240d882d071031041e405000c0e84203640d80041e00c640c1004c03441d251541e001729010180010005c91999400070081070a5400c50b0f590030058030f080d1018846c03582806030020101e0b08095000c01182c60001c01400e505c4020403081040307440020121a41d200e81c402c2c04803005d400c59000c0003501d14040e00d60a03441144022540c41c0741c0c240c10303000c076564170030084000c2085076100382d41e40350424007101003001c21201c1405c842003424616400c118100003110480e1203a0b181c00c2203443d0b1080200f00351011100183c480c0b0782e01905100040e01c101c414205041d0a08810340c411202040b007503035440d4551b90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 494225998 1250 494224748 494224771
    0xb0705090a15031b090806040f03051603020606030d050304260910021015050303070b090109140a0b091b0f0402210411030d120515150a4107060203 65
    0x10300e0245211122010740d04c011051110f001010030000f84040340c4980e100d54025034030700218040e0b24040c0e40c1360252098002c0303103a901c01c00803810140c0000d003640c004e43c02281180da46094589040b00c80d88001c540050140752801c07582c1c01c0b0341542e201070030714603110303d44024100700350000441c09901c6d0483d0400300503807001002040400c601c3c45054100c1090300350800340c0c6400c020100c0d950b44904400100410b00f0840001c59034082035000c0a01c541d400304464148600508115503190111031090f0b07114501007001c240c003442d001541d40e4006403c03428020b0b61481034800c005900007000c28003500241c080226020081c0c044c3d00b121a88007a50100300d80c5410f007401d1100440c24910707012030182d03000003400444c00c0e400c85002c2c104448040008541c5940c0e907542102030b100c10400ba2600221841243c4000b524a10050641562250f440f14214112103480d800614401800c1c01000900750003030702c00c1d040000c2d00c44c00809460050980c60300a07a1380e640400c991088610300d03141d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 494227248 1250 494225998 494226011
    0x2a05090a0510080103080a05040b0d0615020a050d110f010e010c020f07060507110f0a090b011206050f060c1e070311061e0307020a0b0a0b0f09040b0705090a1503 71
    0x2480d20245040250100340c480141203161020040d20505060001501d100c0b0b001c981000e49a1003181160090094244141d4039020400c80da08041d009600485100000c00c840a42140784006000700c1103035005401404e078001422002d13034141c15502e98644250103500b10241c01d04109008044802044800005000010300002400c001c01c0c8a0401081d40141d0010482c0a0b48101651500e40e0040140001e0868107000510308405006034a40c11070300304200050440001d13404078510300400e803298280c4940a12002c000c40e480b40c01003030b500000c24041d039100e5040c01005440d0320880c5c0d00484400440e10440d414440340b104a0b82426588112010301c1044060b00c41c008500f90203681c6a42071902001482041644410000d490264003100241c1114402c10109252f103070000ca44c0300003030611040000282c2150044180540741c8000f0142c0181480140e503882203421490031a156150000c08071270581c040410131341d01040823903010484482c1429240341c40000c035280003030007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 494228498 1250 494227248 494227267
    0x60f04090506010e07081b0306010c0b0403030c030e0a2303070f08030a060e07051801091a0702030d0e0303030403030f0b100f080919020f2707021009152a05 69
    0x80103000b822182000105000c3c81082520070321461030007c464400c250701d03070343e403540100d13103101402c10040c00d102c8006003404241038050303003c0050003400303980c203011400441c80116036540b9488001440e11801340e00b02800c81360160a1001c0c00e0820b10142ca00d00b5000d0b40340d1412000c21201c05540c070400000a01c4a60700c81841408001c2c442070030301825a10700b8080140260150070b02c1c100310082c0c030325400700041c1e00c6182d480300a04103440000241d21181c3c040ca010301e81081000300c0c0a88507034034604501c07074042daa65040390b060040c0214507554542d90200c014104181c64172220640300d0701d2411050b0788840e2b401d0007500e05da5403110710f0076003101c500600d02c480190490312950804214079032400b1a80e01521846a01a20689540c2d64420003244410544048482044013a8160b80703680032185207005020781002e900300c80b100400154010700f240c0c0740711001440021440c020007103c4007950810020102054040d44086044805c3e2034280052014820700081c03000460004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 494229748 1250 494228498 494228519
    0x1f0609060b0301151e0e0d050f240f01170304030209070c030807080c0a032304050c03070902130e041103100f0c110703173105010323060f0409050601 66
    0x50200f03840c2c03045c104245402054803000c070703600c1c1c40b5040080941814550707848816510320701980c000304841c0d420600c1c911054440ca840c08207140e40051819051100c40201c1080d00d000340051190341042c1d91a000042c031414429619004640c00b083c4400009652910040c40c03007620a0703110158500c42514004000c0c02c0020311410074403041e42c090021480c2ca0074143c0b5004103150a000a090340e006600303080d40c0e100185860070300b401ea40e01300001c101c2d0105180c42803070419800c032114180c662000c031313007a0700071a45181c1004a415004101040d20260000d41150141e20350351428a100c9010900300240b02038000181c0d626901440130700d2076a0300c280c040c9001d0510300703010400c800100003519064940b101404809110300d415400c42c4800382120301c9000403a900d0040010b20314105001a03c404000380d40716402d8510001e1694007a009440c80405039076801c41001100040704200d18202405164006010501c001003e071990b07c101013040e0b01890041034107602d8407184a5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 494230998 1250 494229748 494229779
    0x1809070c15090c21020405060316080a050616050a21020d050f01080a08030f07020708031605190206090910180b032e05040f12050c0708010e1f0609060b0301 69
    0x5800307052481400c0003130071403da55040f980c102c40104058881c2d10020346041800108107030800c0a41c480000c1410b00007540d40702c202d118100f61040c56482c2144001c809403100d0002004c503000700006d0708098429044102019018024007441c503150700c8440080b6040002d1958610390340e002481000c5901402c820300410ba440010004041d441d6070361004ca0002034140d0421101120129521500074400c0001404800c41140c0c2c403009406412880c298811200f42d6140c010007000044031120101c24086580e000740c0458a442c81ea0018040d010200502202284e290b40310003007041e01d030105411100c8400c0e5480498000541030401d403c01c0c030402280d1500c00c400000c0b005a0404170380ca41e40e411001d0540000d002e58072424500c01e94810700000030660395010400c01450b50301300c1c01810940ba01c0c00c080f5618580c0314038001d400c9900102c0e03000031030f0b800307008841c00c860011801c0d40b010003407180340400e00b10350300c1c05c10800340c0d0100c3e0000380c5089800300040c4a603554150486 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 494232248 1250 494230998 494231009
    0x30c0626060307091e0e030a03051003020d20040c02070e0a1503021e031f05070206310c0902070b100e1b1207021b061809070c15090c 59
    0x10031141c100400066514030b46407081d0101503460300b0401080b40e112840040c914039000a082c82006c0c25805401d4484e0302460b2000042441d09010501462220b4070703460a0320b90161000e104441191201d07403103038074200d20f0a14445071005203c0407a0b02e0780c3c06140310b001710700c0e00105905070514030100c6001f1402400d22280c0e500c0c1031041125000780f581800112501a16079a4005a03840d40c2d4450003071882c4c0f032103500740c45600f41d80c892040004580c9042c002070120104455114014220780307610003503903002da6121302040d186100d058203e0219220707400130002000400071981d1402c40c0c0360041d6104060455022886c031003030199000a50342d03c00500d000b0780d00740600703280c40040c0491001e04600c117203481d80c3c0b44000490425900b211038600100c0d80d41c0311140340c600c100a507600025100c45001c40401040d0413500c0c1450070681d001c49481c055115044403044090101101e4000d100070200215801da010101c0c840455441002c02141030208541c1d0860402c044c8822076075000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 494233498 1250 494232248 494232317
    0x1a0112020f0d0b0a0b040f1a120a02090a030b0a09050114090a1214071b060309021810030c030c09061d1306021306030b0f0627030106030c06 62
    0x11400006070101c200e901c0c2491540c0e0001e402c2500b400420140145a00514000040007801107251903400405208442c50843c2100101d02152643d0509015a04042e0202c07481d0720081084110300782c003d05404a8040d0000349903d690341c945051200c0180c5002141643d596203d03c180319080c001c40300701d150041c0e032000250601c481c1d00340d0f42e507a00d464050038062340c0c07203081032105204075031310210456500c3c0c0c12a12a500c50502c034034485080d13a1741121a84510300001101400f80c001e03408441e4004140c0d2100105d0440d440d414540c0042050f0703914020681c01100194040c0e2500300954082d5003048106401c182c2104200c0c0e606400041e20343d0151034000c03400c4900c2c8408243c0c441c810205014605800e0719054000e0b004449066100121040300425181c1d4594800c11060fa401c40e10400b0030f00c103d2060104901c5081d03031845200b107005200203601182c108a850000f10301a0001584039540e4a544c4210200c030f80000c800500d01c00040c12440d007101202c020b038040e000a8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 494234748 1250 494233498 494233507
    0xc0f0a05030304123b0901060c0f0503070f030503040b010605040b0d0e07181e0b0306070f12050a1b0207080304050d020103060302060d0203041a06010203090120011a011202 76
    0x300d8550328040144010051000c060100b01954891018001e601030b215040c00018a1102061040129203c014008060040000e07220502d0508586412500c440c1c030b03a0304a22490340c03114080000780f00e0080d646484200710380b600007078003051941050b134045e0743c5489c1c4a00b0246403140c1c0190041e48030800b0800c06001c180030302a104801c65400011b800740c002110080100c81340d0411519034072060000358080502c46080f60150445089400d8050966041d0010360000d0f10407610240c00d0380303801d81d200e5000140014014401e17103000610906000703001c0c1299061010035100c0031515075515548402c8440f1120b00e600054402098082c0090b01c002da0a001501c0d0340c81c060341c4205807140681c00303003120959010394046409140c01078036450f646c802070f088142c00703580262805c4a14a0210402c0114000b400025902402059001e1441e101010b0300450701c09241390251155000c2e1220211500ea009101d4554000d007042c04225211903074400141c0141a4880c4000d041da00400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 494235998 1250 494234748 494234753
    0x191514040e18100225061e051512030d0c051e0d1b0c02010f050d0e0c1c150207150e011d03041d1314010b10090303320d020c0f0a 57
    0x142105805100225030391a445c10b04d0a06002030300f00e50140c88900d4030110398140002ca4990007032880b030052031103c044081003180501400710222040030743d0a80041c000c82c002c66110740c00030048a803052601d1030130b0010303007071164414020000c0190030380540080d00d120134050601488240030400d80c51303003034007202e030943c040e01d07400c081f00000341040400320031492030318020010340e8612964941d04010340110404007960b120386444d4030720311030007006c2c00300d480d030ba00003032072400c0450351204141e02003218001e8444080d400898040f02d08101400621407601c0f4207128032030408200300004107036100000e80610044054068000b00ca401c108000c2c0200c0031014000100380c00b14101c02c440640ea100d48100070071041c00030003040380004801c0b824507003c05400480011404640410010002c92400d88000b00031384401000701d6640251002c29518140e10301c44010448161000d85291030f444403861a07004894080156901051000100104000c030b4030082412030002e0001c1c600f0364 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 494237248 1250 494235998 494236027
    0x519090302010e101b0c14060a050708030a06090e060a0f06050a0b0c01110a110f0303010609171c050a14071a041a15191514040e181002 60
    0x10715826001382c00d00700003c4480b034400d001011680f04035110003000001c0a14101d032100c1500e124806070341108250701c0503940760031011180301e52610303118149410b10658544005030001000c02103019a54100050000c0603409000e00d01400000688010b28146036040c048503142d11940c10824a0003805001c43d0711040c0e420303003d45e0500002e240d26a41803984c4b031405002c100e455000e4101d80031500808094101c500f100c98a440e540c15500380070740348041203680c2d0200b40b1400c1c00040111808015000404449482e500b85030700c15602480a0b800c9010603c0c80d1201501c2c3c005807000803150749044e030080300503005a142501e15840c26486807141e44c041c92400c040401c1420030b902c0420100a100031802c00d80740c40d00f600c0c0042e14036265440f0410303400b01303a00c070a02a40c10607130a1240d20400600001c01d5a03040404c6180ca00250b62080340d03e0101100700d000b07229001c220220345e140241c000c0501c41c48586001d0159014121842404d1541d001104d4194070300500054001d034410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 494238498 1250 494237248 494237267
    0x210f0906121d0601150e0609100c0c151d0d0201030c120c12050f09120a05040806010b0d060b04081f06050607030206040203010c090b0d0504170a051909030201 70
    0x54a01107420219016045005003007591040890740107404078803010402c003041540c101c40804a0822a00d8191002901c10404207101680d11210400c4151180e2511445d01d0314000c040f40f80c0429035805503656a44c00400b143c0224038010181201c1001f001d43c800c940d169402c50403559001d410a0314030100b001c0c2007402c040241072503140c1a0400000d84a001001030040c04032800344106510701030054521707a40c07040c0e40b440c10f5040074005200c0013084032041e070081c40108000c01d4072801d000c1c00358060350801d445400802104100000d9000c0c002c000e0340d400707032001000740c136610380500d2289001c4408aa204074130469051004110340100440c501940c00d41e0511104940d80000d046c00d001040300341c100300c1e84120301003204005d140c0d0001e9941d100741c0c8264003c000c0c40200800a032590000c80c8584e1003050b1040041c00e00720111600031b41c1d04940302e5101200e40c290404000900c58000307404440000d11702003048002400d1003502050318032007600707000c42520b0440d0002040048c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 494239748 1250 494238498 494238509
    0x50918061f140607081201080111090303070b0415021201050a063f050103050a061415060d020c0a1a010918030509030a120c020a0806010602060403260103210f09 71
    0x200c02000b118079031560001c4900c0c040d407050405903504d000b00000701d2003000038021a0711944ca418880400001d09800721810350f60000d004505201d803d03510101c150030014000c940b4686a105d9000c04040c050014140400303040410610540c100018082d892001e0f5020004210401c1400c00031040c0f4070700300b980b40ea080c005070511903a0403071a2500e1721001007001e004246e880c1c10000410b000000c03880e500c0141c45058203001550300f04061075043c642c151400002e48501c11400c856600d4404028a83c003407141102504100a20190900303040c01280c085d44d091312402c0b00080b82c506000a868050302100404215940c50400445900020503200509211002884000e1550100503121825910020140310000c026000602204004000300e01410b240d5101083c0d018000c40c405040c0c44950f03004005aa4594030111502070304556103e441c0000d04030310b502d90745c0c011002e4502960155800d07100715103607014610943d00074400100200b00c81499001c043d9035100e070000c8100c42 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 494240998 1250 494239748 494239769
    0xf030a0813031b0b2e15140a08060306090604051b01021006090209010f050412020402160606120b0a09030f030c02030408011a03160b0f0f04050918061f 67
    0x11030615081d1040c900d28181d564035464444104000c010003c1c003110710852240340ca03221840c0c85980c094424080401c00000145e2290b007003407060f020788221400580c07241c1c0c0780801c0080c0e0b036408408207075400500c1c6400000d858804001240c04c0030408a80c1001c081c000a003902d02d02615601d48030210f12a00240011440300043e92583c401c00880d204001845001c01000b030750344c60b10034020f51004088a002c180022521111307280070310217a4003162040301c0f516a07000c4244d400c000c02940001a9910801151041400412024820103010340448141301550030101d04182440c0c500c0204a1171b0b02c68100901c0c2000280e11040c2201441c0060801044440d8604016421070042e5003100c95203610340510f0901240a0769050300e4008019070566124005441d111210f07030080d8080ca4042c26010001940c411210100510040d00114211801c00303441e1000680d401c4003e8070020300c070040b9600c040100c03440520107036410540c50401600381e035407420001185078046105004488 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 494242248 1250 494240998 494241031
    0x60b0301080606011b0203010f0621080f030901062d15050a0f050c0d0207030c140a0b0906040e010303031e02160204020304020a1e0f14010c0809030a0606090c020f030a08 75
    0x202e01c00c0d82851715007035008000f4441a4588e0b6603031001004070b44108040903001c45c0e41c04000c80700000840706442e800c01909490300d040c0406a02d07643e4400741102d101f80d9070751a800104c503070700b10501900c1c00103989410006003207000c0c0300c41c0744900342d604141c00c03100c200ca10300c01899070008202c40000c015824140705220b00b4581c20b45281c025400780c0c07a00c0d40604040300c94051350115144080c0c903c100d1a09841648034480008401403904180ea0001101001032000d6070446c2c0151040da007004005500d071a40321420030544220a0348220b0100ea210f02000e003001d44010865546225407460442c148250060f103d1048a08440080c0c012540040410700750f45518520201a00400080e030482800701402600b2070012403154a40e4850b500e1070110b00c00c16032800342c0041410580d683c4400c07040340d4032903402d02c3d070100560952511038a02440001103042c091080181b83e030302e8000500d540030000113030810704031680118468004010480d10302d5041601c1503007051541400c603230030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 494243498 1250 494242248 494242277
    0x15091b10120608030c01020403030809010b0913080c070603090201021b0f04020d0e0102121909080a030e01020c0601090b0f0612010e060102030f0d020403060b061204060c270504060b030108060601 86
    0x60826030440369144c040002c1c005404401500203200701e0b0311079583c14034540c0d2210042030895102c800c00c41d81c8000e07180c000c15120381c1d16450b108a00c5000d40b611a24000c0d02940d000e161038656409140030075203030345044045d07603018003103d084134601c50030000030f4448140003d0256100301038140c1c421640440d05000c0c03407555030310000c28100901d008541c1e41e0030b880ca900761151022587d961440e20740004800103100a07000701c0303d2455100003640d08120300c10100354050300c01401c03001000c2d9403c1c06a2402d402080100e14000d004000380014000051004d1090014001070001d000700e5040002201c00b00082040c035044582550b91441591910b50040342907224842100a90100104074600f00024950081c81200c1c420803081100c0c54004060006c11b004001500003030000b440001000700742141c1203049078004071300d0320380d07620015001c0d180c8800030300001101d11191540403d1145092511841003d0b04203006c2141c203540c905614070340d8646d0b00400f1071381003202c903280803c00f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 494244604 1106 494243498 494243501
    0x6060a020606150c161802250c051909050709030b1611070320150a0c020a0b0d0906050a0b030a0b06060c15091b1012 52
    0x34280e540c0c07001c002107001600303c0031080702010062862a56400d00200c060106500140c0340070b80d05140342a4044124220700d0280c640c8108003111800b031109502900060300d40c11135100f1441d4602d44911144015404150003114080c0705440f030400f44501041a0b0321a51010017080d61050000ca46000792888040c0c00b544084010441c4004200d204000a000b01d040c4030122585030074040340760440d1644141c545500b05070208401c0c0301d610303c4481901200b1104000c605480400d0b0703094038030400c1c00f52014003508030300d20402c545551718000d0052503541c64941d1070740c3c1c58a545801801c80084120380f07851074480001d81c008118840d91443c003130054000e1001c040d5540d110259090040e103415030103e81401540c24094080010020031071840004040302d04049460cd40f40c00c0340c071800758a044008a044844a4980040000a5918514007401350260a030403150 = true := by decide +kernel

theorem cover : BRFrame.Cov 494064748 494244604 := by
  have h0 := BRFrame.cov_init 494064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 494064748 ≤ n) (h2 : n < 494244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
