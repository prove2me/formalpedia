-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:40:05.722914+00:00
-- url     : https://prove2.me/submissions/c51fa99b-ab13-44f9-a701-97358227bc22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 379136690 ≤ n < 379316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 379137940 1250 379136690 379136699
    0xc0a03120605061227010204140a0e150a0b0a0507061a01120e0f030f0a03140c09011b0b090c030c0103140a020a091d060f0a03030f030e0f01111210 65
    0x30f10502243c1c1c04880a0a80041c1c18400400c403454801c012a848000035040d0a401700e5011750014055200840d0700002c00c0006400d005000c1c01c102c03001012094129100c038004051203503140d58400d50080306c0e161010444d814600010564481c040d174504d42c6e03441031814039500303d803100d2660441c40407021700e848800e0b030b90114104a854a12004c0010803041110314907140c40100754200c44540004281034600d0070442e00030381a120380d151018400c07641d5100f961403410b80d088a88a030240414000102c055101c0c2c4005a0104d610071122142c20b441d81e120f401a01c0000ca070011220b51044060603464182844540d08120302070a06000340004c80c0020115601d0080040d048140e000c25071032401441140f5940c0141202c82d02041380746412507203000c00803404c40b0300500900a06090b02401e09010306103400301c0e5055514640f58a02d103070720403000350440091070141c03403003050010040c1c070b0b80a1241c8042c07001401521503841e22040411115124020a20b505100c4008000c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 379139190 1250 379137940 379137949
    0x30c150503090a02040b12072d03080a03020f160501020711061306111203011502070f0612050406060308040602010209031510060c2906190b0d110904020c0a03120605 73
    0x101d00d84d8101c0300411403401c000042030043c40e035001010794501c82d4130750000300c884c804106201008a014000a080c0700703400a000c00701521440f008090303c004000200c0718501c258003070480c050254030400c0c5061840e15241d2240b4010940c280d40995000502000300800f50025414400f42a0740d114100070100c41c00c0104030321a84a0134080c4a292580400407410910000c0404d19072650056203039619024034440c0d205003035419402503c100303400440c0000034440082c0444000e6a9500070b80031907121044040c100207007044811644901010001895510160004d03002550006851310700003400c140c9000b140604008507400e40c0c030144101c80c2001c618680980d0020308050500c40c8985c070b8004005546c442246021000c07108240c0c0d04200610b0300c150180008071b070924098101d1459101c10307103010344034038040710004100c002c1d0f407503415800c049084800d290746c00c0e0a1000c06004241a80d000b004000307002e0308050300070401c0540160030300c01094030080c0b00b0001c4230704150105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 379140440 1250 379139190 379139203
    0x11180405010303051608040902030709060801080f0a0314090d060203071d0303030105060c0307080d060311010315050906030c090a0902040509070b04211b0320130e010213030c15050309 81
    0x100c3c144000705c2c2041030040342d1089400500004000715660b240a020082400e0080d0107501d0004010000020f2210f600050320000d26000d14080c294104c0311b40d0f019255540c07507131078408900c10300784001e151954660740d0740061036004801c00b599070b282403880248603e414214190081e41e1a904480654800105690540704241c1c0c1c40c7d075503502c3c080f0121b440d5019001001b013010100051030070860709582c0100c021284a8051290400d0707d4000650a88030b03040350f10107099074015002c00451500900351a041040601074415034a400c0e408140408003c40d030450b40c40d0340300c202032821410141302d19039015032107801429001d803e10503440454460307031107002d00407018640900305100e42c20324500c00150b84807125000b4803d44100c0428650114132081e10341090f00c004a5143c174010902c0e0032020303500200802000e802140c0032000409031400030301000d40d424460102140703000c1050101a6000f01c0342c035125145801041c403984050100c0d41c05c10481d0500c1840309403000050700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 379141690 1250 379140440 379140457
    0x304060504050d050c130b0a05010509011220070503121303050706020d02040906060c1a15090a09050102042916020909010b040612031b0302060c1308011118040501030305 75
    0x5410340f46150401c0e030b180c04809031007141c1c41107a451250108a03400d510249000c00142d808001d0249d60b84015a801d0146e50040c80c046030a80741100382801c0b031075109402d4065012002140d204000c407001d012600720310000c5a040d03100140400c05001135083d41f690000d200c0300f460b141c558075a50000c3c00b42c010103400620598001c10307200110822901645c3c090070701103504020880c0c1d5500010403903c0b20709420342d0000540c40129142e02340052500d48511110115203124100e290140521090020980104250b4501d81c00300014402e000410080401c3d000316510002c0e0807001500e20078200c0b482e410f00010801041a8a400080d5030780700e0a0303011515080190303030f0809140d015101451003e03a110345000c4e0080b8016207800465603000e8000d03551526001210710800104259100018015130300c800009008114440c2c02007941410006190003030300e40da550320034295101c4030700659500300003140c000350801c51301030101c080701d1084500740b059501d5600d0261245c42400c50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 379142940 1250 379141690 379141699
    0xa0e09070203040e180a200d05031804020d020d14010f030510090312091506080f0a0f020d0606032f0d0204020901030608070e0a11030103080a05130806100e0702030406050405 77
    0x140b21140742c0741740e44a50702146026504410380710302c0c0071640ea034181800b2401c1001944040207003414032006441e5215407200c011454000403410001800d1603032015660300c0758003001275100c1901140090701c540c4400f407801044081c03e085a010720355405800c401010b010b071540801c0850f00000703110010010084e1700185100107824201c401600d00303203000d10803509000d0313a1070420009040106c21020858070401560351520f0190307848468000c020b42c85035100c2c008150201c3d01c1d1075000d2103454401825981c03070b05081c0c2e881006491182d070042d01e190f14611440d8114202c0110f10300903141400400803074000c1c041c0d002035004001010040e014580c04612543c840c0d0003640041301601d616412103002da9512000300f144c101e0100d90b00c50300c05050002001c16800c560058034143c070350080503107041500e03414003104ca5810071130000e00c1d203150080300020050310901009000714005200020b280341801200650181c0140c1024219070041000b04541d540c08419201524021035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 379144190 1250 379142940 379142969
    0xc010212160c0312200d1710050a03050606040510031a100f0801020306120303010e0a091a0108010c080105010206100303030921020d032706092102030a0e0907020304 73
    0x28148025000e981000f46003c0c5141004c2c41c101390003c00c0040302800354528011070a5203070a03c55101e13504902c400012a0540420005259001c0c06d499800b05558007170030300c01c0760b4a00001c0c01201d0300303030703c01c3c2c1d540c0d00b04006000a5040c50b000341d80d40800c0c03024014070a01d14580c1c0d840c0b0b07181916400c40400c00000c10106025107514003140c001007270340403803800302c00340c541cad02c454001d500541d206031140003208a070484c403c2d4003009903412030b00c0c1002c070300f55140d95800914029161282c822184011030700d0421034450f01445149000e0a0303221b000041031101410040c10b19a01038010f9810341d40310381c0c20010003d1042030840c00b560390510b070100d504650f52420b800000c0842d18064102c00d80542c03403204003680056030345800b42c1c09540502c24100d90340d2034840c480c4405a210b241c0794a0716104140810071039081040314a01c64004038495a580c043c040c082c400e200d00c40c5500682000400510165201e4009100c2c0c80c0d0803904601075062440010350750f0f00c81e0348100d990080c08032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 379145440 1250 379144190 379144193
    0x2040c080106180b07020405180f0d020606040504050601270c0e040b03010e0304090f02070c1d01060314010303030b0d020a0f050a300f1202060a0e0f0a14010b18090c01021216 77
    0x14180542c49da134200c046841c1104062880354032403041480600051083c0c20000c2c3c0320385007601815009680260140081d40d0030a00300b0305100311b0070754412801c3e030841c0c2921454000f1070310170250f0208280d503481c1d601c404881d00304000c0c2c83c0484282d61280c0c1c1400384041c541040441103500b01c560103000040d282d510700748081c001e4011008050a03400310414002800c21001809985845103444001a07507a00c9800076811280046203113071071800c481c4010b00c00039009a20a402d00e82c3d00038813071403200300d5942c0010128441900104080d6003900000c10060520310011000750100503200300103141d40303104180e01d8490b161f200070420001d403c1001c2c203114450104540e199044801d0004140c440900030b9030b0f600f0240c445810032480d04441610002010402d002e0320807184d000b07440c42c0041901c8900300c5210304a80822555078501c2031298aa407195841c108810070b003801424030381380c602050350506404801460564102c0c0b0a45d03c80d88007104102d41d428402940c0d0301c5412180ea = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 379146690 1250 379145440 379145461
    0x703020a030f0e0106090506030708190c03140c0a0503013608040b031f0b07020103050a0f0213090c2105040f080304050a0506012108031302040c080106180b07020405 73
    0x4195801c0c0a45140c03c5988400000c10b41141003650508801480b03a521a00140341d95a40984528007a0f47c200142607102c00180a402c02550b501403400c0c8030030a9180d8441425416a4910100a6521814203100c0a003032a03542d51009010807402000f0041616500346000003601700c1d940100c51200340d45150010b96195003003111a00900221303103c1d03446125107a5180c0c020303a0404460100c0355000c0390b071038041103080b006031081c00340c015080003259401540a0301c0c024198555103a1511042c6840303168500c0034010044070380c40c070302a50501d40a0710320304648074240c03448200022040b10105041842c00e040f00720f0520320500280c242c2c5c55091080d81d0030300c4580c0042403030500100b80130900000140e046c141c20701a20a581040e66201f098844205408904000108408204d9000706c1c2000f000f81d9400840c51070100c040f2403599002504540034403280c400030035a11001407065941c00b10865880118250608075540c3c203004203031034240251840248119101d074009458040c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 379147940 1250 379146690 379146701
    0x10c050912100905060a05010b0f090603190c0203070204060803131e0308030708040b071d010309021233090a020d050c040f021806070b130512030c1e120703020a03 72
    0x800c0e1820403c3c1c1d806841d0080d220340c01030b641201e01700d0500001046085849084070071207d0040360051514400000f405415040200025003a0280714043c103102502c0d80103a0307030020000e5020307555881c8240304001c1110207540054442d584140410036465001d103074481d095410f07880b1042d0290b03040041c805200d003d20b420041940001100744440d031504004580d018074801d072200c41c0709a403035140c1100d040c4c054400f901c3c5d00d03108981001460b540203521601480340081c0151a04900011103185010403000320010a54a00341c0d1400400082c1600715102204481043d03140d418038158003540c800e04420007178030a024081800c01080740422502580c804060300900041403015001e0b0000d4000c050650514030031200049542e20b80003040740c105542c061100d400c00d40702c140540350300d4291544215601d1180d4046041c0001d545400355205016100f481552800003c1600015502d0380c84030380445c0d20144000003850140310034040d480070b800e2800503195450084200c2c060b02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 379149190 1250 379147940 379147963
    0x405030c03040b030717100e130f140c1002060f0c042103030501060306230102071a030103050c0907050d0c03180c05030607050306060a120b1e01020708010c050912 72
    0x800014005008040c031000703117110340c0b1640c8415003000e095100010400c80102c4010301c004200304010f002070b2010506d05a080548102c201e003520354581e650f090301104000707050304e80e1982107030f4161180800701300d03030001c0e04070954070a8a1440c83e034101a5a0398405444084210b01c10b0f00052004c22842c1c040c0d90062802201d00303806802a02021030544010748401e6000034203210001c20420b0090044000b100c0b05000302400350911102d807102c0020f1170300982d50450003404400070b01c0202000609401500c0100456900d514528086150034009251a4001c40300a010841520b800c1800e48000c02d29040001c140d41c01225002c03802045075000700416282105440c00500c60346840b01c00650300290100c5002c0d440d000400d8070140005c0703981c175a014008002e0f411003540b06401c40b81a4405000c40410800c00c2d80e4006141c2e8481d4007070052a42502c413520420035039040003480001c0c00801c000308100e1610190003403143c85a0001f07180101ca1144009140c95030400070301d05441c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 379150440 1250 379149190 379149193
    0xc0303110d0c21051b0c0106050405010609080c0901181a12150a020705031e070605130b06120309040b220e07061106040618020405040c0501180509010e0405030c 71
    0x1855540006019000383c0549500354480300318510a04885511901d801160440b46410654030a615030044980c05004584429502c807803000455844600805000c0d11458403914802410440043e2800c6032216140c0d01c41e414580040206030104650b03a03480c54000c10b03010030400d03001507250240c56020440c00f40c000c1c503407091542c1218004900c0002814001250070155210301252074241e014850000e81036400030012a401e544071030f070b100600b141000c0100b9007403605a807075440032940101c804680328580100054200480c2141d00d80e8000720441d04400034826808120741d4074060701c56014015652140a80303502e6071b0b0400143c0748015511502d4507031285800070403019084007802100c261060103c04034001e40100390241e42c0500400c000d0445a0319a01d50307101410203500c00682c2d40104603034a40250b01d8a008403417185004036000d1032039a2601000510300c0208514888500031000c80500c4075583d10100d0f141141c1031916400e04a0705c590810354158440c0c8403860506 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 379151690 1250 379150440 379150451
    0x9040203150a0c0210140106050a1211210f04060510090e1606090e0a0c0c1b030308060103060b07120e03032d121b1306020a1b060c0303110d 62
    0x20700105402400c0700708078a50176102c001d40006022025140c0c580e1340d0700c131406c5c090001130100a02c5840030b8a0401101d1410449070600d000d00c5004a034101e44110f013500400040f1115003400608070300540920003402d4068074a0300d21031011840102803c000d00254807036001c141c00c1035000c05d400c4060f10405000300100400f09010b16990080d94081d402c80d81c08000c00040c2403802007a50300e00716140c40c00e40395120f0740c54007107403801044200d170400b0501800717216482c041044510a02d484000c2103200c044038038110f080c050860480241068101410000c043c4098109801582c0090b0b511510813948121400c40070343d5034004080b002501403101040a00f10b6900f100e01d1500700840610302c81c5c40c0e4854025003e540d03441060120701d1980c0e91800418080c107200e903004804024542c0e001030404100417034401400d04194400c0c0c00503400a0200c2d01030150300f901d11352800030154840300100f450550064000c6d07149220181c245941c40c1012002075900360700316204011030003c200003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 379152940 1250 379151690 379151701
    0x3121213033608030405011704030306121b09020406020a030503060f041b03050609040b01271b030b180705161509031808060c0705070906090902150909060904020315 73
    0x10b495158201540e88000b02100049040300070040f1030a031803040e55480b203c5a508851000c0d9080050030880030199254000a51507000c110422585482a041180c0c0b07443c1858204991000746e0b00405440c1d40304110400640d42c0001e101040c1a6140c1441c540780c2c0d81e21000130301c40e10510000207800c0b504007102c603d401914016102c05120b0355071000c01940d01c4d0318040c03001f4104111402410092a080148100030580300c0c1d05803c9401c40b2414010b280f10040000c0940e60000c0d000050a40480462240c054043c0585829004287d64000d601c1c4011141800c1114005c0d01d184180040020819014020b0a000960968100288103100c0d61412008401046040c00c19030000c0c2c4510259030080c03e0040c2090119800c2d40000c10242d1038141056400343e1281004442510840300005170b010100d0042500811040e0720004844078180180580800700d0391142070801c00400007480300796110220710341c015105a5540303c1035601c81c408289410110000041c1603406c2404018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 379154190 1250 379152940 379153007
    0x40806010b0c07061b15021606050601270e07090b0c0d080106230306190909050d020303070f0507020a1d19090c03060c230304020312121303 62
    0x541e01c600351045940103942c80b00100c0b4013100850752058131941075152a404555806c0c0c0000c189034440d83d00520303001c00216075071103d03a0b448a044910175120380c2044030729038002060040110030700b9011442c7c000060140d81202d081405500f13650100000401c101c68416241c507006010f054101070f5468100940c06941c5ea52a03403a9200069420000460302078880d018241e1009041c0140c0d100b840940200c95407250401030900703800c60051510011042c001101a00040c240486d002515032110309200d800e0801003115a029036004205001c001a0300810410340c5000c2440c0007a2103000c03510000e14464034a5200f198030b4019011800c1c000303066446c840707002d6211010050152181c12070684143d50041401521080d08400100003003410754018181d10f10a070326042a0310028180c1c82c40780d036400d00091040a07440441000b0845c181042201e0888580320412400c00e10348108510081c0341c01010321111440302c420101c04c050141c0700411680200400c0c07501c140c3c071904c80d480d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 379155440 1250 379154190 379154197
    0xf060503240a0b01020a02150904090c1505070f0f1704030302060f0601020c03070506130e100303030f020405090612070806091b0a0302030a200405040b0708090105010605190302040806010b 83
    0x104900300c1080482c500c52050b00c0f0701c070042203040c2c014114030103d80d020052a1013152805160b240ca082040390019501c5124a5050b144142420314202e070904808501c41550b102c500c8090020402080b804a42d80b02d07150603e031540981d1105c5130341c07107504d0100e40c100c45620381c0e0b0340540d60104001c410540c02040f1548240e18550044416a441c4801281d84000001800f130b015040280c051010741001c5000306104004400d06041d59070343c032074022030b0303440040f900c413000d84c00045414420940d06020311410203c06c52019404d050410000070804240074149c0d500c20800441944c154040a029141c01044c03104282c2e80c181c80c007942960f032a440481d0b1001a0031404028403001d51800705900340589030041e000f020f2110443d620f0400c5503c452100e02c00c81300101e40410603568072405501d1041d8443c190385407890811101c0036040c62800307040c54200c1d904090051100b5030780076013506e15030700c04450348000108520358280c009200b1508800c045004d150004149104940c004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 379156690 1250 379155440 379155493
    0xd11040e060f01120b01020a020a03030e031b0f0607050c040f06082e0506010504081009032d03020f04030f05060402100f0503011806180e0706031a040f060503 70
    0x300c0d0694480c0304018044000c4040b00340441d8003203041400c54203096002500c102c2041c0104d60034442c5640004444180c0ea44c8200d001610007400c051146c101440050760300d121080c202c40d0104801c500050b6100401e4807200e005a0010410009000d030030048905240c80c0600100100340d00482030801600b154019000148506080603500900c00142d01440d11144001c4840051120174150087c040c09044241002420301c00400c10003807d008204401848040001e94100945800f5040f582c0c0148070401300880704c051a00d10003ca0303446022403040341d15005039034515030340c0a101540150b400203030640965006e0300c1c1c00c000002a000340560700072a20900b6a00d0030721021140e01400ba851000080e02c144010401c4001c01700301d000800e106c1c00740105816880b001401404243d030710524103515142c2c0000e006150080c0500c80241c10189410321618403e20000003003140b0400502d402207545030950300702d0300c007658000d130040c0c200101540d41e1200d00207100c1075010300083c0c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 379157940 1250 379156690 379156709
    0x50603190b030d0816141902062d27070311030c0a0605030a09080d0c030609060b0a0c020d0b010303020a03020c040b0109090203070207150323040309030f06020d1104 73
    0x2620803034600015800450801680c60444c555290b0005043c0305c0780c00e80c840014005040700711107801c0100c4001d0310212500f809038442620340b0a00007407034000007511800340143d90145104d9481341c40c2d070324900801001c2c42140d01c240c641c10501e014101c603416080c5140a00c45104180a2601140b1841201d01558041220082c0d8104150721138004000159121864980412440e40110f01440d0f2141c091800003503a02410b84440041d9032000d0164bc54141d030324855544556090300c07812014042c018000c02c20141031041000061240407180700a020341403808204569a018181c00f005074090469003265130f492170007079510350003047c04130301600510f140700030541854810350100300c5050b0f6614000601e040c80040080d40301030201000c500441d980881c80064007103880101c04815a000503c0e5441c200c41404964980b00005801c11516000d10010950001c141800d8075000400c0701140d9005181401c001c2c41104a81411181002600c80f0b6564511000d0b1084810106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 379159190 1250 379157940 379157951
    0x702190506030103140f0109060605090f040c090e2b110105060604030305090d050105010b0a02210f2209022107021e0106051c05010605100e130605060319 68
    0x16194006404140200ca400640c244010004541c03055132200b920b2010f0070a451840059404503425925420015681592940d004000f82e0521000c0d140e40034020714006d10060509075a84410452507214404040742c0300d841c65803a0507002d00011a0ba0480882800381800c25205512040b45103521b40c603010980c443d00410200606009440c03141c0c0004156919060444e60300392401d800541c0d2903900902000c1d5401c0001d0424802c43d4041d05030440002e482c0e01307030000003d241114200c1030707561241280404034240d541a034142c4071183c070256812900c5080115032800e8424850b0091030084510060005640e901980113100447c803078a1118030b52403400320880981755060769480b0069125200516070200306a03049111420501c0c0041980e958035000070308004820107441c02c0c2c6115610396442081424403c0100420003a078280b20340c1f0540000103008400820000b502500c1d141c82031501e44c589aa120340080c00c00289095182e0034420003d030b1807c1401900030b0649841c22 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 379160440 1250 379159190 379159219
    0xf0d14090d09061d0915040c050901080408090111030d020304020103110711040f020405031e07060207061709070909051e030f18040b060f031f061416060c050702 71
    0x1281c0d2101003112501c648180c0c900d00b0390200c5000360310740ca61400101e030300f96a4444540c1c403416024060003030603458040e200b9881c0c0410003210360100e803900c14040100304d03081469800c203000030b0348a908084025100c00805005071284a003c03001c01c2220300002400c40c0040c1c1c820703806980158000e81c1d040040e08640c40c1201e803944140701000e0540d400300f4000502c1c0741703080c0d004141c0d81c0d01c1c070074800b60a081d91040421b00d0610311003181040342c075a07203050101e440c500704100401011140f004000c11071801d00e000c4c1100082d41c401d89041000791002a880380e104000203c010440da040402100c0003c0c10400e8440c49841c05a114107569030000e031511030400010364083c6010a142145041e00d0701a103240b41e0031082039101d41160b01c40c0010285540c44070b000c1c3c590502070807890396503860700d0041411641648d00c110703081b140700a0b02c14003185030f0103940da41c1a0301060401e00d0703846982e0300c117031540211101c030020001c5080602007280280d02a02070181c03941701791003009a41c5a203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 379161690 1250 379160440 379160443
    0x3030307080c09030a0506010b0418060515070309031a010806070f05040915091103010806180309060d0e07080304080f1f0b011b0605010609090b240f0d1409 69
    0x640c0d00c0000141d00d0404150320070300600040c0300101c401411110074603856036070581055001d81c8100d0601e200420200040403a00604541100da15181040454113100005801d060044078140e0104400301e10602094014048503001d550090103120050610554ac0e4040007424090f1081074041d180c082a5020302440110780800215240c142c107042c01e120342240240a01003d064203010b01e0080000c11041c94030900d42511a0101c603280e0380e40c10002e105150104c05003c0501e802c5c10b117401604004008001c0d501045c0c4101c2c0c2041d074a000915444014141c3c0c1c0b0315a040d1030080010001d01880008020021600680c042c0d402d2805041111500c40a002c80015002401004441003841c22a4030001040c1014100900302503003040001d402c900c8001c0302102e031950b0300d400500100f03402c100c0d850000d100000382400708031808000b00d0001c9040301610b0540d038000d040a15400001c410036038641c15080984a500d94000c42c081c44090509110303000400b036001400329101140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 379162940 1250 379161690 379161697
    0xf080304021c030804260c0105060a06180302060315040c021005060a0305100509011104030602090102100501062712030c12080108031e09060d09111906050c16030309140303 76
    0x200744d11400415030343c0e500c9034502103c0e640d60702e03141601d54070055613251080c10003500c1501c2c68100005898a084000d1140c01c80c5150088000e115000c80f801e010b14624000003000d503981510744d02d48a4407400c86484d003840000d0041070740b042c1800c01c0c0c090083c0e0f0005650810075034081c024003580c3c440e003040c4180081d0034040940540c0004002d03981506064000a80111041000103000f5030480c0741000310350000d40040720b00c00d0b00041c031b060f83d45d03034100422110300f241c000b000c1059526000014158410007500034031813084440c8407003050140441d19100500060203000001d03000b81c070340180440196102159601241c403810081e1030310170309445068625582c015860040b84003511020403404080844820004200850b42138403440003034a0810360340c40700803035010003520344121642c10300c0103100d0041001c0b901040e00703200c1c071071860001c0310074904000359122210f420b0396050ac0184002214a81e00b507100000415502a05070400c88000710300c0c071205203084c6400c0585034030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 379164190 1250 379162940 379162943
    0x405090702102d0218040501030c0807080c0105160510050c0c01061415250303090308060f06160203210909010b070506040b060d02040905010b101103070605130f080304021c 76
    0x684414000b803004103980200a9800100a180035a00c0c82c0c83c00201507c809800440b40c00b010039004005003c010070039040030385003042c00350881000c1180028154090400502500000160010b082c040280500d800035880b02c2c00a100c0303444c024902c030040742c0c82544801d86945c03a19000252704181d46901c096000c0c00200340031520501000441d105400400607001c0d402d0700c4280105030b1500c0306030b8505100344a40c5022880901505015107c07010051a04c0c0c00383c00b0035603044025031f031400e00b00e80c42507020001e000c0c00c030b134140d0005c00d103081182030f042040e004201005440b1550b0040142050303032001c40e1441580e81e01c402d00c207001405448001480d41e8405408140001e4021440641c1300c0c1d0007070404030541001d900014255180c140c401d64040c1d5645103200104c0c00c1499020300f0551981c145a40560920003400e60760b4450044003a0005039100c003c11180081d1111480e000c0750082d0410450300000e0416508a038030549041740f090f02015001d0b0811a00e01c43d905031a607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 379165440 1250 379164190 379164251
    0x1050c0c0d03051005010809100e0604110f0d0b0a0f05101401052b0207060f050f090d1e0c08210f0f0a0905160f0f0902032703040509070210 62
    0x51749000010f544c281000b030054501401a880c189200321414415036104420240c0207121504041c1488031520034450f800300d02a090000d04505036440b21103282c0c14295209100b0f4060741e0b02e40e0308200041c403e05400f40100c50030071061001d0599249401026145010b80003c1c2c8000303078a0054079144031f24103540d003007402a2103031683d44010081e000141c0000b181805480d0078501d4cd41c260444151009200c0b40326a200c080c05941400b4104003a481307500340f0000c280640034108090318403003042445085020003103607403041d000d01c500b0700c8c010020b9100215548580079821041c000c6036440c0000c0140c0c4103110001403801c03420b03c204034011401540b10b52480e8441c0c011031400f13861040b0058845208001c030180a00e1a900c4460000f4841d010040501d1400c202c440e035891002e48d0b100011260044c4103100d80d06289480c07030840c0500d055206040b0100d02171b690b0307040d40155404030364403400352010800390f1500030031810b0240c42c8140c810011076410f15403c0c00c0141001e91440d404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 379166690 1250 379165440 379165471
    0x11030f0a090f020402210615091207170d02162d05090a0b04060e070207051e0619020607020106030b0601050711040c020d110304060e09070302070501050c0c0d0305 72
    0x1091100d6000400d058011142e10741e6802c1c00e900494140da000e05c404043d0b807661101c542c40340c0c1d2003138800302c2e070032010071200c8520b05c014850401905000d030804091080d4040302d4014001041001800010041000f91403c405540c1c0380c2d80b5150503540000c0000340c05601001290544c3d49041d11007520110080303008803402c01c00c8100f15000c880d020281d100c0120319170102c0c5650740e03240190320442d010003000c2030031000f10051006441050340000c00301d20305c07801841452500410310030166002955544511403034242c0006000d60303601c2455400190003d404072142410041c135030703040c1d840d5408a80d06034483c00c008900300c480320b1101500451070040170580b10362040300100585030180e0144a0015074038000a001c42d42110704007030140e0f001002e50442c80303400145140c0040701c1030b0301846c2007a2800002074800c0951460880c030618500c00040c002600a5059030042c68200008100d1498000c0740442207074040760002600b403085a240307040b160704c43c0c09030500c41c1c1140a9403110707 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 379167940 1250 379166690 379166701
    0x5030708070512040c060f020a020906040c020a121d01020a030c11060d0204120209010f0e0a0506120d020a03080a06141309050f01020702150301081504080c0f06060411030f 76
    0x900540280107402000b40801501d001000d03401482400b82d4000d00350800083d15004014254a07845007042080d9003140d5407880140e60380d8900740390302803000e036004a15400304c01c00880c00e0100340c071001010035021100350070341554895126600907145800d000b085400100041ea41c445800304021300080b10798001c0c0000a80740780d4030181920026015504041c800f00e2400c1c240d07001904000001030641962000b5071420b0b0400d1801051001c0b25010501d040c200e510a00280060001c8082c90f21040414030589404a014401d4408d48043e51401c4071130070802900d1b60b4440c102600010303128404a107035440c1c64440c6a04480c0346a0701c0c4840c6e04041420311070a5000491500083c4d0ba40e4010040890b07018841c120200020000040e40d521513481085280c3c107840c0f01810146509200500c2581c1e0009641c40c407055100c55159074907684c074a4042c10328401c14039404440c0c003c0c0008079040580000b1094084c0804603802d110107003071a40030210b039010440f0505031082183c0c002c642c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 379169190 1250 379167940 379167947
    0x31e0c020f0d020111031204120c0305121906080d120506031b030703020a0b0406030f0b0d081309020408070314012f0f0a09150e0a0501121d010213060e01050307 71
    0x40b0000e2060500c49441140080118210781042c05d1100802c420302041100b04544141c2c0700d00c12050f00c2c2042001c51603241c500603d80d02031851409803140ca01804200e441500410143c00000e40c6407040c0401500e45d10600d4484164403001408944000780707030f0f04c0324041c50150311720552015009010a6450903e240100780030301252540602a240001c80540c03608603404021303100b100c182585d250300e000303c01030484d0139074041e04480d035180c4202c21202e0b1b55a84400341607240c100c04616100c140c00090300805140503400110058800100080c0030780c00030512000b02d034028003040e41c810f5030800711582620700c00c0c1035001100291007a03c001d4200111a03070072140c040810b8207401c00d101c400c207103c1aa4040350400c004100711440030051803000240d01000c0700c059251080c000d000700c902044544000d806000d0502a891040d00422003065000d68008107401e0050780d00b038000e86c0c4909000f1342c005590400402804400450540d0203091507000300c103410394459155a5445800f03c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 379170440 1250 379169190 379169209
    0xc030a030e0f0f1002330408030a1508010605030d0302090d1415040b01050925230301030c0f0e0103110108040f0501051602010c110a020d03090b07031e0c020f 70
    0x355402a15030f41d40c001c1030b4a5458600c110500c0310780080c1061070b042d80126202004501401d00010000d251605804005003405500164403035211512030b10b4050f607c0d400741041c0e0028126030906c0400000710503105401038800c8410607070985107980c007141d50440a03032150440e182d0704010307150454800110080b500805802014050b91690648001001200742040c0c03010fa5a190a04005000d6840c001079200e402c2002400080c00340601d000111040222001ca054144441608a81c1c100074402c00802078101c01d03030450640da580c5900d002c1d2040040e5000f81640740070941c0010504400100286042e2500051042c0041e202d01004407000c00005000f2102c42160424020004a00340281801100c8203c200d0240700d15240c4001c4c05c4643e6881e5107410410006403c910381140030030100803c0d90140c942080600c800e0a05407407d0000d54869081c08000080803000e1691182c180850001d00e0003d00304c0381c8902c00005c0300d540c1001170011b94403507900c0421035103e00e070440c8007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 379171690 1250 379170440 379170469
    0x3030f03040f1709090609160e03070f09060f0503030705070b07020607020d11030c0a0f031728091508070c14030307020102070308010905010321090803040f05030c030a030e 76
    0x30b8900e009240d50f55075080c09140b100040583d1000c034400718180b0384030101030351010040d034030007000f8a00b80d101000740301241d02c2d0100c1440380e8400c01c08899201444800094204510780220303855079241d5101c018105403142080b8844c646c100480d0a2501100b02c481d1140c1080090540e141801100e0a1700d5106400480e44032200300400401a180d549201c80c16a0082c14100da1400c2008181030a241000c40c0103486039417014018046d0f000201003000036240c01048100c00b00302030444038000e911400d90003c00420060440700b407041c3e0300d611054402091640d4080e000e80d07a0760407111524090714418008140484000b0712014403e854841030180074884050001360000032003070441d40281e50000041c0d40004012082c550050481401050a084104201d42c51a224a0180071840711030907240741a15024540c06403145807004054041002038a58841e59140010b000502a00c07a41b0b001c2d0041010300c04244ca000b240c031001003601a15031030096a140e1003000f04c0681021035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 379172940 1250 379171690 379171703
    0x4080307082206030f14040b012c010e060a0b070c12050a021207051203040515070228030b09010c080415090501060902120c0304210c05100501030b060a0503030f0304 73
    0x10880030103200400000240f04580f0002801155074001c68269480201204501c003d250140800034803034403041ca044501030301918100c00f400320402450101084030311030000c240600041040c04649034210f008103000c440c24128107039140e09031110742c02a000090040c0300107a008004c0f441c0c10703c2e50401d400c2c0c81071007640e101c80041d600098011545102e64039403980074140c144071500f404002200040c0c0054000c5050510307110014000340008810786202c0140880c800e4110b4a803003d9008020094550340d440350702c0c09240b5843d03882ea5510003135500c0d0341d074000800c90b025018807806000302d00c190342d408030982c1d8540759141050a1011601c520755680d50708031010820a00c0348070050280e28102507a112481d0f001134104240103403100720801410424000003a00410360591004100c2c5002005000d0015003030b00c940ea02440e02800a010b0644200c0851105078491410303130340304c1c0d0344002d0a81c48160a02c02d20000344d000e01394141c0d20070020368207180c0c42c25014541c040c1c405c48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 379174190 1250 379172940 379172977
    0xc020d020303070b090d0903051c0c02030a03080405010f020a02060403110304090e1006060207050307032a12030906090609062d0c0501110a050f0d09200301110408030708 75
    0x502182ca950300540f03065494000b22814031859071003e101440480c002c0d0700e0080710803419916a1a200c4001c0c0304450083c1c10082c0c2d040b01c105014841c45200250001c0c02e84c1d054407c41d0070040c050940844084659501c0c021941c503a00140348250389140c10980e00038640f45d51140c3d01994684041c0d5000140c500c000d00000454800b203001310025810900060030002e41074264038010748101d0f402c010150b4204440501ca0703910002a100126600882180b918424104000d80d140180720040c14000150f100081814003110354441d07441c80c4030342d0f501c41c0301c03e668820442c0e51008c0b5000340300001da00c1c00b408100c1d140c410740078500c2e40d01c030b4900141400407a110003290b45c0303880c401d060408101d00c1d0b6040c005011080c0306e40d0140080c4410140e1410251580007400341c46010b12082044202048490085880313902504656038010320600603601d080011108070356100100d0f031706c00e600f002c101e02c842d0300c4c829040d83d0845a818004500340402540c40070041d4001501d280655070090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 379175440 1250 379174190 379174193
    0x20301090210020d02100e0c2403010f031a01050108150102030c0f15090114070302160506190f020c0a110102160b07060c1b06050c070c0810060509070f0c020d 70
    0x20007120b0744207074058004001c5403026050190400d159011a11115441e15020651502002c1840d1000c0f000444149075030502a96681c46190704a810346002d50401000120f61444012011400c0d80d00a1540242d0703213840c2d0346801d40400003400b4250000701da81003c10614038282c4000c10b141c00301401640e00382885114207620304103841d0340d441d1955010300c0048120445121030b0700d404c0b800500c000d20840c054502d1805000d4005000c400c205a40040c801c050641c0210748510f0807944481583c2c29410907803941c03c03084011040d110f50551401103001c1009840c0d00c21103035004500307000b030a58401261100c80884ea284a07106055000da03416025881c4480c1d15407a003d030103500b40d41c030b4403000b203414103104403051f104010042c0445011400600c09940c00060340d1755a0010000c14199560503419440d0700420340700600d4040314100108203500045140c140d92807860b5801c02006507a1410402d40400c10346800f0003040c2e000c64400a404e128282a1159500141071648180000e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 379176690 1250 379175440 379175449
    0x1c030c030f0339020601210212010e010b0301060803040e060f0a0e090d09050108071b060f1a190e1303020c0904110909031c02180a0605030f0c040b0a03090203010902 73
    0x61100310254140c244103c01c070b880300026508240050f0b4030050a01e90b042c00003440320000d05003400503a0b810b91004842c11581d41c1c054014100c0c02c0c410013480380003030b04280c050203003034200062403181d42002400702c0c802d20004140c0b000c48142101200407600c50b1004d1046109492105c9904a4029600030954860403100c40f801484080011301ca02408880700400f240480c0e0096070410140e001840040303988000072010340c5003540c0b2942c600078403a2415400602e2502c102c00c83e05414401021141101d00184901601e03055400c6441c01403809584c1410400f6801040c4502c40080080360780e136040d00c01100c484034864011a90750c55aa0000524040004c0b14100c03416075464013681501e0500441c2182c00c441150002c5040c040070f280310075900e045215100101c40d0303007c1110030107102c0110841070010805050310741d01c60b1300e0b810000e0081e0300468800407005444000300340720a1a020484044400300b10036036081070810070046000d00b003a094107a902d992100d0040b00541d82c1d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 379177940 1250 379176690 379176731
    0x181b0b21090c09010e070e030303010f0302060a020a021018080706080106140d050f01031a06130e1e0102130b0a0909021c110a0914030709051306060f051c030c030f03 73
    0x14204a4021074a0036031b60060101640400c1507002c1d800500042082c2e480781c00200c01900d0f03044610755102c0d151203604038035001091001960020701388240c0d60059421554030100c1403940081a50483d44400085680b18114420400001c107064010044280724020000001982c4507085141000b804410300950342c0a903404000038107114010804c00240310090314059020800400c1c0381d14041c00020305140901510b05000e075210f0b020160707000420300c20303488001d10b0a400e0300e001c82115074859000790131020001422641408022541070400010345084144640d5844101c608040c01c10000e50401c801d8070f00e426400c1c09222408030540c3c0a104003036440c1144807601d40c044101c0080010400f81d00201e0409000c80501c1d15948011480c00140e542285c408109a110600780f41003044281d00f000d406645843c9001c00d15940e520801000c032442141c15043c0440030b81c0c000080404201c0008001c1460054801c0010b0702800c10782d1020303604c41c20002001080e48072000c0f99280c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 379179190 1250 379177940 379177949
    0x10052b0c030b01031404020f0312030405030304020103050f0f0a110408061303120b0901090203040206040320090f070206240a0f080d050c070303050706181b0b21090c0901 75
    0x161904031096034180e15104100000b50309280512541c403040ea0200150840900701034003c1411000e98806ea840070400d801d22403003034480069913480c190a085850f030f001550100c1c0028101000710340c8107100418241d00840f45d000340c0d00b400380c8031b45075000000c040003c08806c80103c28080094140b400740001441400000300780e6561403228a4010850354060260300c00d00303850510410019107036072044030b05441d1441d5006030750752128000180d17280a5544000c000c041001664000341d03002c1082d2400d040010b6844080b1902c1c0c400341032403038000440302d07840164040c000240c0d00801e1030244666002402603c2e04200001d04007181c6005055040143d101e0800c0f041000256010408907000f84218a446401c0404440c80a82c803003a00d4030000c0c0c01c108000c141c01d4103100741a4802d09014003070300c0204000841c90300c2c288005020103200b08140c07200f00308000a414508a0841c0c20b096501030044080040014242102420150004c3e2291060707882c05507454a41501060280 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 379180440 1250 379179190 379179277
    0x60804020f15030f10230301060503160f0614090f2e080a0e071a0d02030103060608010b0d2a12030819090201080c0a0c1b14010903021005 61
    0xd1420864050310403074090107907100c59885074800c0010440503900d6503c8054440c08889100050034000788c09002c1c0d9820050b40341c00b0300d680d17640300c22a100913070104980178a40d100c0307540c50343c501e42610342044002c9600206a0200846031145c9010701d6120326041004224002007240402201d6200780244082c01c06030242951100e1001d8000c40402ea001103161340a010315811400070b10707102d500501ca000e515a150366915903e0308001c005484d00484203400c00c64596940b401c182001c0c2c0228490b6182139480c01c6509506424080a0316800680103040c0e00700809140780140740d038a2506400104a042045005c80c14109125441c0900343c026a04c0d0442c2d400c025010301e40c441701c103a82d03d00c4100c4ca000c80711001031342c0004910b41d001d040c0d0b1000940794a425032040c0c0d0a81c0c044080185850644c00540320401100756108064030203280c0760442030f040900056a45000a000180d40004103aa400304140c0c844d038000d0203180841800a00f8000710001c41440401c18807a80c40e065 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 379181690 1250 379180440 379180447
    0x1d010203340807140a0507020a1e21050312061813120903060c080f0a18170f040305060603160311010e0301020c10090b0a15060804020f15 61
    0x160085030034250050420940000c007415605103a000010700300e14107907001d10039041c0006101c5401058107620050110200d03503528103054400500c1d640c000c0c4400ca04c580d0890402140200950708100300c0300454130745203a20541072029048210001c400e01d44022444000d50b10005141800500b2128800b000000c9003800c00e030f4100207071071082118280d00d04902404020000103101e41c204040758004103442000b214a9104844c42c81207a0009001d4a081020f0340d520300d0342c0950702c3d0b8807130100072402d441c080d10741d61060b00a40f01100000102c0e1006038207080c011440081c840300b0341413204d46c001485c011940c0620112500300343d006070340c10740000040144508052040322a8441c480c104440c941c2d08507526139141a003200c03c1c1504000321a40803027030039142541110000c880500c2100c0101452440110203022201011503241d07a1242c0030803c9030105d070080003c214a034030000b40090b420004101c80c0050010416644040b115108010030f4a0b0100c140540050140030b5a98 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 379182940 1250 379181690 379181701
    0xf0e070906030b0c0906030a020c0a0b010e2a180315130501060e0c0304060c120f0606030b04060b030417160309141e12070905011710050601020d050c011d010203 71
    0xf500d407001456000f4415040000030b60705c0da03c180403240d00c4030064800503250305055040c545002d41c140001000001410008607a14803c5e0401034800c0c40038145050180780000241c200c80105034084010310001445040c19000100701040519040a4201e42c918408059070141d1501e080d5220b41c440380028105005011083c020707807014001044072000c0030304000d01c500701984401400500345075501c40d10094003e21403448110301580303100c014026400b400c4000d600070f000300e02c02d2402003450400400c25500309400340c0380456a141c9500c90450303440c1d80b0307480703000e40400000d4540403c00304080b410211100b5103501d0451b000359605411541480882c4000e0160305100034450b4143e0800414207014100c480c09100c1c1043d200d10001c40c103454251817405100e5007010010354100400031601100e0400c900040340310304000c64040281200d1580c044031000d403640d60058000100c00ea00090260004104040c09580000380181d07000121880504d860105042c9a075000810711a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 379184190 1250 379182940 379182953
    0x1e1201020f0a0c1a130602071415090721030318050304090b2806110f010f0b010e01091809020609040e0a020a0b0405090f0a06030507030f05160e0a0f0e07090603 71
    0x35160002540080c0d070701d0503d1000342d55003117141c04005140c0f40d00000c1500c2000315800303a458003800321804540e01d000c034800d0340d41580030701184c00d2500e0344603264002800c44415000c0d9041000210107400120500e610300300c000e04040c100500015030203021903400640204001d00003080e4070f8000207100740440c0200244001c4004100d18040c1074042c10ba04000e00111103e0101c65845c1440b505902e8126a440d00300501c08049200315441d06100759000105074110100c5104240c0c1e13081c40d50314000005561690840c00b549030459100040e046118285030b02c0b00244900061000f414a01d03c88001003d868004614510b90b03004034000f5011424501e80d54030252040d00318060501e8148408140100301c010824004c4e10302050205000344010b6010344061341e000000c4d01e140d56140e05045d5401d0140340340440700d5119115a006210301040f0381031065604c8590581800e84905543c03201400e8048001c0718400da840c042c0d9055032000b04055001070803091808a82c41e840c5090a8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 379185440 1250 379184190 379184213
    0xf0a03030e0d052803061205010603020f10080f1e04050d0801143001020c030a020d0503040b0114011701090b030f060609010b0c03130e151e1201020f0a0c 68
    0x601c0420b0080040c6804c84550750280c0c4080307089242e050b091035250450140107039a2081d2088400c2440f440144901034200005490081d901000d061111200380310545205400a02c0020303070441c041003185c10503904e003a800c510b001d50310303140440540d02d04041604c4140ca0031102c0d80d00c2190b661a401c4d400040d03103401080b40329070780003044080c900401c448003000c40c2690b000700c0d00012a0b20b0010302140300d00100c051260000c6460342e4001099540d44d0b4008088100513203d0880358160303840c0b01d041100c0c411540b01c0c2498204c3d91801c804002c204444040b0b45043c0710040480c40070300d03a104c10429000306054800403c070701240405150610b1150380c00700d2016040079042000549607040113030f0442d00030020a41d0354032507400103141103005a903030180200c68410300014004187c85071103070280001150002100b2404070411082990b1314a0007415060309107031040151420201c0c0f140c040301900009850305401403065141d9a1001c0d0490010502140400703041c00210002c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 379186690 1250 379185440 379185463
    0x20106150c0201080f0903030c090307030c080a0c1a090d0203011e05011707030b15031207050102030103020f040e0d0f050405120f010c05030106121d0307140d0c0b040f050f0a03030e 80
    0x8583c031b0074002a495182e200051058840c0c1800003030501440c3c074100150710085400c504640e071070380e4490603241e89808404c04182c6040820b9540410308851016103102c074030003581c61842ca404c801c0c9040c849548080b50040e03070f01d0356070b42140c0303d80040c04106880300b44018540c0003c1c0303981401014008004070540440300d5070310051040c000903140740181038100c0202030340209003040c124002441c01d010031042d450a02070210300c0600700300054010f54140c81c400c40d0307054100006001800100d4001000c00456503102d000907024083c0a1900702c2c04031000752606510306074079240450080c15045480d0100c0d03901903090814594020320034a0010003240c54021b1465140040040c0194180600c0316402a62101c0d402c1c03811131014020341f80082da10041e00e450700702d64148800d180b0414a00c02606001d00702c003001c11107104a005904403603204400d405140c556460741c0c4200c00e1104030803a01ca00c03c0d04044002240c0800003914030a200c2d960200d1075000241243e828039425010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 379187940 1250 379186690 379186711
    0x2a05010224040204150803180a060c020609010c230c040b01030204050d110a0306110c070b0a0903260403080d0b030105011809060f02130617040c0b0a020106150c020108 74
    0x2901840d140800d00c2a8001d41c040b140440e002100350506404c1417103070781c881141ca00c000900c00c0c11800c0b8000841d0004403048800000e21030303607000f041d2001c0d00c00010080d40102c041041b1100c546c09030360b003134a00c2070203100320a41101003119003a0140c4000c03540c1c4940b40d849001100078500e8a4050388003d00c1c42841d0550a1a2400c2d002c114890080302000b04080041c0a48543c142c4031420440015a041035090028810f580010007059225000d0000e45010f815030100795403034030b84211024505560f0b03481000d2455501c500b511a460000f08502041041c4e000c1603d00741c245000e8006540640151345c0c0e00c5002840180403181c6801030319000b641400010055030820074983c180350f001c00c0320041040e00b16464880d0003020103810580c0703800d20200d00e905036078018600420a030342c1152511180c0010b0031050715008001190001c00b40d021092003440b00303407003100c0a0071400f813681c0008508252552810404200b4032000071001401c0f00d0300380c0c4159a4860301c1c040e006218081c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 379189190 1250 379187940 379187983
    0x309120309050c0402070c120f0c0f03030e030a050718020c010c0e120705030606090618040809190b07060908040f09140a0e120c0717060f0718060c2a050102 69
    0xf0740c7c2215414840c414806500c0c0056168402d002d210713615000002e511219006030151100e240d80784009080c082503001880c0c9007120701944c100021074445203034000004140c0d4610b403c5807500140ba00340f068016054082c00f010100b003509025801c1501c02d40d40302c0750601c00e007403800d00c020044c0c5c04c001a5000d030301402003041161401b082464000f00c094889128030b5403030b81c0c0442d40401d03254522455088988017000203100c0106d010702000c600486520314040032041130003503149198041e403005810f080041c03030001000d9600c5a0110792150248a080640d64210101b80e4940c2e50f00c1440342d00c0e1108105c190301d818070101300381c3c081c070002c004100c00d6000b00c211503998803400940010703c94000808a00b041c40410001d03004007005108940e82c02401c14841d901e90300c0aa540c00c084112100c003091210303008040210303070080c5174030a92032014070300981200c80c0a29070105403503040c10404440da00c02c144070401d80304640d044403c038942520f40000245800f0304e010001d4070090303061 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 379190440 1250 379189190 379189193
    0x90d020d05030a0507140a08041101030911090601090b1c0b103c0210140c19051c02180a0b0417010f180c05060301050a150309120309050c040207 64
    0x1d41600d402c500c1400000075240d54051040d03c0540020300320003100302c00810000800c85d0b201c02807a104038440c5501c0385c0b5003024400190f094802d1544000c3c00c80450107011809410040c0307511303038071005c145006201203a9404e8010900e40c4003000c81c0c0c00c4400c01481080c144ca1413402615051202600c03098501140450000c0001003200111a24230348031114408819aa024485145010a46040344414406e92029580f5041e8074404002141000c10204031211492496032094004540762071410414a1445054501c0c444508051081c28840c0d01205180281003068490b900d4100603a01e100488680680701e024032070892040510800070320040d270411064808894440e103004080e8459014041e02400c881098048003524081140e80c55071010003e20380c0540c09007001c488515100d00a1248500c02402001c4d0807540044c420003020000821141d00c0c610940740014800e082d5035101004007000107803410001b9102e80c61541885000c0c4034000010804036011858080341d0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 379191690 1250 379190440 379190447
    0xe01080d0c08030c03060d0c180b0f01050406080703180305030132040f0e060703150608011d0403020f07090606090b030103020a0e0702070f09020307200a0b1e090303090d020d 77
    0x90030302444d40004004102c03e600c8445a00700c800350701c01c204160003900c0c0c1007000880046103001c44d40d80b500b0030a888031541080c1102c649001e02c11303900d044c503150030403006030340852010340044205a65858012460a03041b20041072003440b07940c8003662940f500b4050840d0781c82c0340c5405542501d032041a00d80340e00381c402e1642d181301e00c1600c01243c1c03990f1041844004002c01204504540a92003c000c195503140d842141c45c07900b06207042c4280d40e120f80d8211f4403030703200b405089541a014120402036924110005510500c40d00c1181d0060b458254030b1410241d403a440340d00e10300e46900b003c0c00a140c0201d2900301905015042504640c555000100d0050f0f5500c6030480340090407003c104d02074401c0c0400006015811500466a913803810882c000358000c6440000095807140d0f00707010030b0041d442c00808405040300a16024400b40caa5119140007e45440d552002100080100502d0844098866803140019580300c0c80c0105460b0300300402601800700315040700c01003082d10f680 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 379192940 1250 379191690 379191697
    0xb09100516142b02070602060f0f040c05100e040c0309080d05090c0d030e011824020309040e070819020603070e0f1807090906120b060303070209010e01080d0c08 71
    0x108003046210b10104880c0150030140035041c1c00200c803800c0c0003102000e0b10600a0520908201d9080701c01311540c41d1400c030380b20705003a10a400c20303020090110300100c40c580c01d6a07070080e0107542d42010b420b80d070f10009082c50200c003a0300408038001c20141e040a251520614801240c0d0341014401c0c0802070752001d8513442400846116295a1804030300540e80802010723080396030281c111102c4c044d5a00300a444c6007112008a800600d0940c0316500141d0040c40340c0b42192809070162071512612403101184650024096045200c10b1004201c0c50b40c2c0e078000c6030340d030480f0400a000c4030750801c0b681c582842c450204070b0140d540b8060041d401a00c903031b07040b282d1080d90740c50214108901800001c201800c0c4000702644011100d8090588a10001402e409902a9210003000c965640501d600f910305600c500309800b4030310007400e00401c40803032105e44d01640c014243ca1409865a0001e80414000e8015803441d40000c0014050b0900801890170000380c1420440300c50f070229560301c00c5910 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 379194190 1250 379192940 379192943
    0xf0e040e07030b130501090302211305060a030b0405070e030c03192925020607090b0a020a1506030320100b220b01030f020408030403020d0c0b040b09100516 69
    0x100680d0024001014034000841030942c464007d002d11105828000e54440c10484c1c3d0f80702c3e580c00f071580c83d0140d428401c1210705800800008042f201d00d07002c100810b58004801440a054403000c1d03409442c1d07141c0c0304561041100b9190044940131031400e040c80e0041e00900319010303a21041210704013040c2c0c1d502c4150015480102503450404034907a581b003965240544613070007800481400000302601c03062080e0198240e4240240d01440c0300120380d1641d00b035400101041d15a1028004032402d040101714280c200d004070b0346035841d00d5480d030f00d00030000401c010580f96250002e0042603803000100c80700d08040001807032489010880b00d03071150040d0380d07809801c9a540030010181e0711044501011f0250011200e411080500005005010f05c4000f0b180002e140045018001038240f003520144d440e0b003001142020304641c02e000344503410300b009644055004000142c4003400000501c042d207013041c201522500b000c020302c40810601a104014400103119410310b00d560900243d07000e9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 379195440 1250 379194190 379194203
    0x501020a08030423010c020319080f07051e0310030507050604030b0a051b03040c0e06180c0c030f07030216090203010302030d0e01050c0f0106080d0833040c0f0e040e0703 75
    0x70403040d9061341115461070700500c0d03a500b0001824103040d008806450401180c00c48000f2840b0324200c22140ba000403111880c00d01c241d1000f184016100b1409019400250a01a122010340d0384c10740d8482d4108032100c420100c1c400200b442048020f000d8080280001d5940904142c02c5d643c800c15072103002002c0e0002d1664410009440e004110011900c0f00345102150707a0728140380c00c0640c0010a0341c003850341040042d0340414041c0c200303480d200030f901010904440b6552140c400c8042182d11238100d0300c0300340c401408440d8001881d03500910300d0900c290000c00b5074102601c04600c2c020542c1c1d10441c1c00500c10b000400c05a1800b2900d241d40100a2403c80f124400d40c130f0050310107004010032080e0703a01c0740042c1d0801c513842c15407014040d1841c0c141121602d80403a1000ca0301e4a0046610b00e60b1102005007240072200d44094804180c41d0504030f000408807220041030445464000480005e110303681c424038480d03000250880180700545080c0484c0700b00c41c01041d51040103101c01804e6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 379196690 1250 379195440 379195463
    0xd0504180c050d020406030e01050702241003020604180e0a11010c06140a060501020c031b0108041115041e0f1505210420010e0607031110150501020a080304 69
    0x7280d1281e01101c00d0716400c0d03d030441d2a103850715001002004000ca2a500642c03800012a03803042c000500b42605030f00c02072401e1000c01d40300c0d1900c1908540584800e490385010b910201c0140d50303d0b000b42000d00f803003032100c840341d0400c1038400058510394040b40c08590070005540e0089a11041d15410004080c00d0243d8806103501c1d00390010082d0b0711428600408040034080481d00d0b42d04044110f4000341c2c2140e141040f1030303040546030f45020305000c1c000e400c0c0d80e0181c442c95000e00032003940a4043d800700c141114030306020801d54620507900034a04c3d0710024003400b26070301500c1002c07040311100302102c4025092440e003503a0480b9900a110442010b500030855162103042110441680d5284144c00504142c0080180c400241d408682030600d421501c0c5031040d100b2180700c0c014805a45421141400740309002c0d6590200d1400d400700503210301052800e0104122052420301e00c04c02c0000c004103402e004840d00707034181c0c105c98119044107540c400451544803d070382c4c100e50000c510a20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 379197940 1250 379196690 379196711
    0x910031a090c04050403230906070b18060703020417061017030705190302010605150f0901030e03220504020c100b01030905150403090506040b031303111e0d050418 72
    0x34110741c4002d9190300030708090402c404c050b880040d244401802c0702045481000716a64580640100310140381c000034203200e030303a02003404000826004192071003c106a5100c801c0030f1410204102c0304203010071b40000e000c00c0700d040307442903442a0000401c05484203042c90905420214035034400e410380c21410100304210744d6420310840f944507070300c542114246000712102c662000310601080e0095461314000280d14102081c40e800c012906200040c5030202e00e0103605019004410724504040c5d9489031000311520400042c44441641c000e84102243c18585503401400c850700010f000d1401403188080c001c030001049070001105040208000101c0c00048005000d030900282c40c622070b4010201201580010090050780613944402066442e0414024244036901c11011517003410000113035010310302a50707490040e22070303e41940d102d42a03861071840d1a10100f09902c801410580e140350700e0301c02304080700c0c00b100c1a0030100c0c02e01e841c00140010040064120740c00302a1034076028034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 379199190 1250 379197940 379197943
    0x907031a06041706070201050415111204060219030b060a111501230406030f0213060b0c0f150919060204090507030905100e030306060c0106091103060910031a09 71
    0x3886020303080d5a19a03036a614034121842c10840002050301442c00812442c91040c0242032180e03070400d1407030303c0f403491408c1c0c02c03030003819064200c0070721341414021700c1031154143c55800d024038040d001c0035807a40103460b01c450b110401c43c2c602009051422601d40d806490344070540e450360725a403c103003508404560a4504107800c0158954072200307582d0020581088120350b03403944208007819401c11300a10824881200d055020151101529441880040c0380c540315100c00c4a034103000108951342d8898640303916410030380400c409500500703824080c0340c0302081408020042075040384102c0c01c180c40c032a030711a00b184800c2181d045084006030b040c40290b40445006150301e00082010b80380900e402030003822040003c8415004074080301e05980600c0c051001c046440601462454890008200305907003d1000300c680c1e95218030300004c640395103118a064241c070031380c030179036a0386010740802528080061500c5a580100841800400d0381c50a0b08018210210784151050b100c02c000315 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 379200440 1250 379199190 379199231
    0x51312090e1609031b170303040c03060f0b041a180c0a030506010c0f050a030807050c071401091206020406230d0218030d120608150a020a050705030406031406040b090703 75
    0x717480811803104000101000403424011111046481503050300c221940584034841520040c0905c410700c001030010031080d0703100f50208000d55800013640003070100883c0c15295003d0911041074009480703d20b071824010321510080016090440462901d0805200304d0f00400419004041d0758000241c00351b4040d60048940940000102020b02074600d081940c44803041c400b00c002403d803c0214200500074010f440744c2c071460384060030b403043c1030520600f40c4d0225048014100040c010001800c4040450354644250081001583d0f031824490040d01c10f10412040304845003444030940c4409455a040e191240c2840780096910900315420000c41801c0d00e011581c10b010300c40418802c2508061070341e0941c69405414400c40d544e50310304580328071950382c10000c2c0599950000b49102d030303258010304a15405051450078902640c650703d185402c10303002139010030380d2805461080001c640307545500440444041c44805100004076070840310181c1904181600d9071406003c4200c8041c07030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 379201690 1250 379200440 379200443
    0x1032a0306020306041d030c12070b06090415060902180105130b0d14090102071a0601090e100305032706070312020903010b12030901090e0105030d050f0409051312090e160903 77
    0x146a120101c410343c0580325404250722035036274880e80121040282140701550207141d0010a50307085943e8500601030343d080b00510480b0401d0f070881d01e50004c05140d214000240c240800c3c01a1500c805c0401c40100700c00142500341406411b0185144040701c00e4814020354900030f00c842d860b01c264080e070001402c0d833652810080c1101c0020009001e50541c06083c000340105500c1183c4442510a5541d01d8020742c1c5160020340b01a000b80b26164824140d5608900e4112554100326030781d40310f0b00c1c115006000404880c25020b204056020104108551020710880703029161420644e0f001d001c0c0700d82004100704840d00414840036a50b42903102202d50751000e0600d55640450450464895020a451031b0224205400200e500b41440c0300c803030b0581c0c0015000380500350102e10183e6180e04020140728406100700808107004109008060068025a00c0c00400300c6103440d1504407000402c0200b0100603400d4410400f0f031000c040b040c0e40101d851104610300783c5070440b0031078404115800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 379202940 1250 379201690 379201721
    0x61d060706020319140c0c0c030d02060603160807060c15060803040603151203050c070f03050703210e061308061008070819031808060f01032a030602030604 69
    0x140d0340188800c1d50000c40c450194082e50488043d500410b07031080398401080324080504210010b400b42c0e07a80c900804208141c4400c440801d481040005c2c80c000c446d103001001a0010018041c281c14100440595800d0480b84e640b4a02d0500070781c9a5502c80500c100c0b030404c45100010001e0108481078590b1a03076000c607080c424140c8074503002d07942c2da00c140328030070000e803400c0d1411720303113841004441050384c139032140c13500b01004d840d01e088400b40c00215680b0564004e600c030026a200c06810f0070303402148100d000d81241482c40c2843e04c5410300a03172040201341c1c2c0540c40040d55641c401d1aa100d9144125182e54880c598032954455583c103907045221103104000501c003000d00c1884401c030803541a40c044410094440385101d80302d03640741ca01c0856040400c40074a00180c0905806105540300030740342c0110550300d6101514001c42a600d60412600420050061009407024105001e040c0b6074203440f072405205800f20721000a210140c0072660102c040341242e516500030f072014012461 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 379204190 1250 379202940 379202947
    0x300305090405180c010e01170c04080a03020d0f050c0a03121d101d10050a090b07031b020c10050714030f0408071505090409170316020c19061d06 64
    0x25140300307072071840701c07140f1649100c0c070068000190300c6030f001c4200f8050180c3d0341800c0303c0810402e21842c54400713400b2001070b4800b4000400d100c401009082c2071507010b54005d02d0000c12003607014040b12001c1d1903240030021b08000000c0b11040c001a0b11401c01d60501e0f0400142c00310305480e02c0200b10301d140301c44600c80c0b00000c0106c2c0042c0010a1601440d4220081068005a0f284801201c103810018801d030b801c241440310540134580c0c01a98046802c25002c00c640d0780554442007000002c66080c1c000c00d640341300605031803111150040076280ca42c0018000c19046d4800100d0b15440c0050910800c200016180c0800c04500d06440c1e1824095045985400b03105401c0b03021900940110062845041c0b400035580c040c2004020025802d9203c6601d402195820308c40941454101514040600e048031f40b100200c15004600c40c5880c2d00d500003400c1d100c004028100017180d0341882c403603400030300405120f0000940c500c0c1103c029040900d00482500c001200145c4001001d41d44140d010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 379205440 1250 379204190 379204201
    0xd170d0e010e070807051905090403090308030f0a1b1e091d06090906010e011a0c120301090c09030b0c1b03040b0a0809030a120b010e0603040501090606300305090405 73
    0x150403c2560051015280102c2c2c5500038000d800d2440401c43e9808010780000304071f6418001175950300980680341c001c03815500c2c0c1e2608102c0f0350050b80c0e01ca10700c81c07000342000680076407481892801e10745900100107481001c1c0b00100a01c81c10b20a841d6074403c00c900b4180564000e800140043c100c2c50b003010501c0035100100c207881c003002c56005001e190307c000015100c0c503001c619135059954181d6035000341d0b400c00040c2556a102e0081c81b80c1e00800820620a00d140b04101e403031a9104410700c255034960400c070840056505c07640d071580901120f24070034070002d1640c4109903071013441481480e0701c942485051a03010558401e501e1224003001901159200800c00203007032002c00fa4444c0b140513161100c1240d030340c0c4507405880c40090b409070400001017250360011464444140760020329040c108001480550054504692aa43d10f0407100b0422800c0c0c05054010001c40800703000f100900d0b4102e150540c103a00c4034002031420f09032034804041c060001c1e01caa070380700a08200054a4072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 379206690 1250 379205440 379205443
    0x9070e0d0501050106200d0c02130f0905010608011107170403021e0117090a0b044d010507080c1203071d0a050310150b190e0d170d0e010e 61
    0x70300a105c00210401e00600248515600c004413400c1820010581c45084040031225601c0c400760803a44030700c6c8050402c0d01400180074031030840302100c00024900400703103021421192203a0001c01107074140214000c800303039000181c0300d072075400c41d89202e03400c0c0c60084c1d007540358172840d08001d500803420b0100a110b110555240040404207803140320202041103a030003800101120344454590000107900c1c0004d0841c01060380062084849506c13a00c104981d00c403800381651520144003a0710320662100c845408540300902c4c0c041c540401480300c604000905074450000042c12071500024400c5c03c4010030070010700c0003041704107029201d003409203009201d40141c08104c4c06d54451104464218a052100e81040750b80090003007075801c1c1050030540240c04001c00050640c09101c0001500c21014002404a20000b0032000703003445884501402906004c0b0480380100e8180c0070140010b03c010640c81d00c41240c00b100e86840d4280300b400c00c4054038040040c1400b075402d11a041411050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 379207940 1250 379206690 379206701
    0x306020c0a030801090902060403030509010c020a080d1e0509010c0305042303100b09070e12100c09080607090303030f1d070515030c040302040c1101090b01050f0f0f09070e0d0501 79
    0x802d5440e14481d03645e4003011030542d03101e550f000e948001e00700410400203000307000900d200f12042c10585401c0e90795400040c48041c0729402002c0c56080b5052241f2000e600840300400309984c11079401c02908808c83c014400d0041643c00d034103011405407840c2c1803500400c00e440c01800e801010b21070301c2c90082c25140f00c090b8002d072094000d11a0b0701c2000f070070702c81500034030402280107401080943d40d041d504440c00750702e0a031300c907410111034510703002c1e0480c01703000030070960345400804101304004080081c075144080c5e02000c03441c0c11401c280000180e0113400a8122a010320340800d440180324088401003402031204214070060b019045034949003c6808811184100c61a610a0310440224442448100c1c0c01d1060703d0310411051006103000c0e8080e07064220350349080741081c140c00760000d003111004007042d28020038050040000f8034010421070103240c416200c0c08030a00c19180400c0415030a00780841c03040100d000000c070340600c82c1806040e400700061100c24114900d0420394002c02d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 379209190 1250 379207940 379207943
    0x50a0605010f0e0906151e0705071205060a1a10020106050102060106030902220e03070605040b0c0a020327030d030204030c0509090709021e07030e09060103110904020304020a0306020c0a 82
    0x41d41490300c1a580341c014a070101c0c1994020f088140c0300e6495178104a1050003064040030b03030b9003080c8503000000902c07004400008190300100c82e03980783d007410114501000c0b58042507003240704d415240300240c0701040c0303242c10105104020850310981030031304c01c2d01c40c0070070145904080e84140300c603902541500000704540c005c0e000e0394420f90701c62404405907014000d01031340122010400803a5500041d48405003240f90510004d04400304004450441e40841c50544455481d003003484140094a80c180d1780194a02c024680b078101c40c481c01035100c1c0a240c8172028541c1700c640403001c00002240da20005c000005003980c4281030313070b03c43c00b030001d40240c00265445442d01e1000b08860403d40c1c0f44600405c03a040060840c14034111802c8041d500c40091003242182c0070340c00e41c03a1407410781c000d40351051003070310380d481d0400300c0708103010354031800a1510f4105030400700d81c40c1c10b9070508411907000c2001a900940c1c0d0340e031140041442c030869680000c120a1000a000c0c0001a0206a800400303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 379210440 1250 379209190 379209197
    0x1b0c04050c07060e0609120c03310605040311010c02040e0303010b1804020405150d02040902040f06030506011e320c2e050406090219170118140709050a060501 70
    0x800c4c210321165601e080c101c4110015511000c0039000409001c4064580340a95404580c504081c240c101c001c0040585440c0741903058103540c04601c0c3c40c031610400b0181900b841c000c0e091618540344c0c910f2006400c00014180085a11401d055488d01e8211030300840100d0b003266940c0d6540e200d1943c0d250310007a0400a002e4140140c0040e41c9414004c4400311b1304020450382c80c0c0ca0300c00040130741c943d1143c504e00e1502582000005800901030010740020110021074034841c034985000502929002014207041160804c02280c3e410850b0750a03920250031458540c4c0051491440041003030480342920302c09140e44200c041041ca194401820f42d02c81e1001983d00b05005c00c05202e0000e5024001c0620688150100b00351034101c5a101e01d40c007500500d00070440c10701640201c4c02c100003032101031902032035056084c0000c00510091070b040c3d5510100030031420fa25400804040c1c010030000800c940c8075488019404002000940d002e040c44290400c10303424081507410040005110b0240072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 379211690 1250 379210440 379210451
    0x1605060c03150103060506092b05030a0f210f020d14180304030507061803060c1d010e0906100302070212011e14180111071a0603060c1b0c04050c0706 66
    0x1544a800f1741001c03144007408041c1000542410414110603080c0c10320404442c07400d00548403141107120300d90440c0250051941c68003690300060420560300503076020b102d411303130351450356029008124200302e082850000f500f8907031024803c00713449808000d540060415034020355041d2800721560203411000742a0180510584074152280a01e210151268010000401c24203010380041400c000c100c0d051504015260740e80da804441c1e0032041d103c00113840d00d142d01c0d407111072800344a60518007402c19003040624100003a000c0e0200600450040010f9000d140c2014000e4060781c0c0071641c000c00c2c4191031f0884007601070080600307560913010b2800200b450050000740d0300c910207c000852291044989c0c1d5218a444030a1150665003515075907590090360a040d84400341c101140300d15400c2080220402c2002194100541043e00ca0380000044c090600900307011106100031060390b00c52500d1134420711601b44810a0103c2d504581488108540b80322000018280140700325420001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 379212940 1250 379211690 379211731
    0x10092001020a05031903060315050906090c030703020d0c03062f1612140406020d02010f0c0801031b151e02010b09060d0804080f1f05100b1605060c03 66
    0x360381102880103400c50b00104140038085c44445040400c4210606000c1961a501e6840c0004a04003444007000315917a003050000802050115941200c10000181109808180040d44407005403200921030000d0400c51400c000504541f40010341d00240f00f0001807401200c84030030351500d0b0f150b032a144004140003002411002017074508120044200c0c80740c0300100d80e1745c00e12032201540d00d01c060242c0401c030501403645280040001e022194007910310131127103402c003a00b524a0064080721742418031410004080d80b0000460440750009003200821038000c402e000080014bc2048006801e81c80e01441074607044220710342141c04280c0c0c5000e14000300d5400701e080302c02030b1100301d03441101c0b400440c40600d840f480000700b1900440b6050302c0c0c40c0c2d9550b0201e182084c0d4050019243c0c101c074040c40c01c0340d0340440c1c00f900400b200040a0110f49811800c14601ea4098040d4500101d000304145d14210003601e030850310181d011040381e80600b0100903641040d0411034440340a5460414440c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 379214190 1250 379212940 379212943
    0x5070f0807030212060408090d0302030705100b03010612080a03050c1c060e0718030303050c210114060a050910050d0911040608150429070e090a020f0a111009200102 73
    0x244687c1d0003403801c0c1d06101d5024100503807140c071901c042d4110312091010a001c90f10903c07a480c801c114200700064000390340c406042c207441440d07012114080841d51301c500403400010846610308058030340011156a40d40c0c50301d03c0c501030543c540482c03c5200c20004180075040c1e0041d01500c04410750b0302866a03030b46108580750792210000d06460a0201c404100003806500250340101038045018184250382c11010450403000d109141c95440700c0d80104440c1c01c00c518480c40c08502500d003603160000000f0054a10311801220900448110302aa0349442c49541951034401114405109100c898104801c0f511100c00d40c2e648140d03d80b40b40041c00080000d6111440003079803100b000070343c2c2d40b038440419140c00107004030040740342d2080616841209000c10b6226803a030b40c0341c0389000303200c010034451a50802080c200b0402e2041244a207075807111400c1d251038039490b2419803421950040070078107081010b8100c103080e030f081414040c200311241030000f104140030b102c815081c2600c5001203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 379215440 1250 379214190 379214203
    0x20a1803240504080a080c1b0c270f130206070503090a080c2d03030310060809030301051f020f0f0102040918120513033806030d0c05070f0807030212 66
    0x200749000c1040380b03105e0b4901801c4000d50040d640c0d400d040c01c180383c0d205840f42a408041001c000d0b81c004508203035503858440d01c2c441456005180040800c030000d2070001e84840c0160030051910b200340002000031440754140e0034401d48c00361440c1d45400861920942e2130300810441392282544440101d558076001034400404d0b0401000c011220b034030211003c085c4030024242c5800d00300d115100d01d065450800c01035005284200e0102501e91402c6801041c0e514060204940c4c0c3d00300304010040340e130781d01c42c5800302c2c030840b101d000350301c4820f00314141c0ca42048114800300310300500803441d03003200c010340c0600b048982607a404e001650002502143c01203203400c00410b0a08000c10080e2044e01c148003400f01e8442011491170341c65141d44950701c00b481c00210544249056072000c9007010b0507040b4064a40010031a001d0b01401e200c8000303034035480004d881000b0040c040d001034003805800c01c400c600030300c40c400e548000f90b80c441c0e400940780c0d4410b00003079004034440900801c4202000524 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 379216690 1250 379215440 379215443
    0x40527090d080a020d0227150705060114011106040c06090f15050c031b06010311040e0604021306050a0308190908060c09010c150b03060a06060203030a020a1803240504 74
    0x3058001d03035070f0202840081d040540d218084607424807400c100202034101c0c40039041040321440c2000040501009030054580280c049001d0040c00400001000040c095064a118001452500c0845401280e50707002c0c2c030508480307a114903028003080c0700d0aa50f4840580c0e010b9503991b06805c0e1160b41d00001040b217807141811660484045083c85c2d40715501174a40c40704080c081d24602180c60508070180c40c1d09030a802055000003004100b0011010100c07001c4100c1a00e081c04040621a1100d440e580e0003413029002d088038080121103510300f81c0c4660b0107450000c1030340805907120306040810750446201e10805000c07285290b0394040c0186a01401c4542d0000240000e07030702c4040502058012000d00c034140003551685030002a82c20540c0d416a100f07030180002c0d003440500800d440e050700030341408810341c58180140310055020040303075801102104056903982402008032107040203400c0c003151111080c1004420070211040300c181204000e404180c180c440001c4580031a0810382c0d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 379217940 1250 379216690 379216697
    0x41e090501050a0213170708030a0f0806010f020c0d0201030608151f270f0e0a05161a0913020324100e091816030c0806010605030f0408040527090d 65
    0x1e040144e440640041c0d11b8249080381a2100c0b00d03a07400016203960051125000825000020f04503e0380d8010031099202c6801d10b00a800060400c0d8080e485821180c0158083c3d500c0240500542e4000d40020004107640700864000c0840340c10700d980c03030600940d0401401901c601541c40d15903603a594040c180d400c07002e0180c141c0301e105516608107040019a0812043d11400b0640084019200301030004174400007034448407080d07181443c1005c1030a1400c00c0150340b21001440407a0481843d03c02c0c0c03100d01c01e0078581e40c418290008551a40720520019100d000208104050071955802c95644444c442248210300e184c07410171214088450101d00050308440e1804402d10300400495000200c807084e5100320070340744c000541031025002444a082d80910360400400007800350440040c40d100b0044c05065041640c0182a444090040c1e0303ca8103850380440c0c24040e001046500501e0000c1130701030780e2142801c03204901c480000030b805404040c00700140103454040303034101d604801c44d0b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 379219190 1250 379217940 379217977
    0x2130e071a2a0a030e1011060105040c0e1021050403050910200d1101060807060c0c09020d14090604030c03081b0d15052b02041e090501050a02 63
    0x42c1c0284819800b60080840ca00282d08101d04007a0184004000d850080d40c41c4005100300100b40174030090001104d00820814418180d0300840128000c0d05461b4100c1d030100c3d058203052400c07075205252070002e41d480f00030252000d080c0790300304101c512540382000c5110007000e02031102204032402104c001d0003080c3c04000d48419441c029525080354809810421a0702c41c0c881e042080d451000070720809603901080c1c074612015040f00210259282c3c900007030003002e04014490341c946903079100300b4007031014211000702041000340b105c20140c80032240440d141c010030524400580032080506030f00c0036401e004542450400f00e4907500c1640c0540711580e01e034110b07550441d0b500ca0014014030000c0b0203d910241d47e02134180048c1030303295040d0000702c0c402c40a40400ea003441095400f140c403c0c3ca2b102070300c002a07005069020700301c41860101c06280152400807902618030500348240384840344c51410008442544041562805080200100e0f540c10701003030f0480c1f04003240800d01c9005074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 379220440 1250 379219190 379219207
    0xc060504020a180617010e0703081e030907050a050f37060509030f01050403020d08040305040e1807060f1b060207120f031802010504030b070c02130e071a 68
    0x26040590014409009400443ea0780c0355400d0040c080025940806900c505040012503164034840e00b0000003c4c0081044009041d1305660f504014480100030040200e8924844041b0344213a22200d608100c080ba901e03c1d15035049600c1ea01e0314050705110340032031080840c02c2d0400740c0b001020702d8000b07408566440b0004600590100450010303000385000301c1a0340d030001ca0040c1c40140200703110f0f01c54903144c941d8001018180010145030940aa2401d010400480e80c005003021000c207543c00d1070b50540d00d80341000c840f54071507030300134082d4004200280f241d850380b4011034124169402741076501054540d1002c40d9008407088110f0002a10368101a4054002035068445140f00d603100500d818120390b00c4030280302d011525600464680e95a503407015806020382d00044820088100702c0e41d08235400070b00140500d000140001e0700160000d03003024004e007040d004850300100302c84181d90711340e040e050250440d480707010501d004e80400092005c0403005074001e45095006050700f00b03101d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 379221690 1250 379220440 379220453
    0x3080d020706090804320108041502041d090d080601080a020c0c04110403020306131509020301200d110403020a140d060219080c07020a0303031a190602010b100c 71
    0x40300b550002e40e0346900070000350410008000400500c0c003101a0f051401929400c40408445c2c40440c14040300c2d65074001d607038017001e05030380642d00c00071038400401b4441a03000280241d800070410b40760700f00c4501000d18101c2c0000d611607442402144c0303401c1100340e0212114001650003901040e005000300352500070a0b0050300d0a601403104480451050b080010141d56550025400d0300400103401c1c0254182804040c1d8400d07031a54200590b06840d52760f80030b00e1158491555001d5a4400d99041159801e422009100c0d1045907203400710512443c003010365601150050b003620b07180c001c0485000c4403080540302180c0e0000c040aa40d5446c00201407040604800c0e096405090146d0400005442d84050064908084100034000007a0f08015010a0740a4103c070030010081c0200001a40d818a0b02c80c1520751500d40441c103c65100400c51105519452180c2c2c0140460101c2600c04149800c150880324541e0007404200c0b00d14040c42a0900b0344c050000004a0208a803004a5407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 379222940 1250 379221690 379221697
    0xc03040e0a2912011a040b0603010f091104180b01030b031f020705030c030c03090307140904020f010302090d111801060c110f10210614091b032a0403080d02 69
    0x20b0240040c901039070103d0145003160b404508040651070740041e0b00c04d15080920a40d1008481a591103107954107222071a00100850308c1100a0940c45082e000076181c0c21005480007020040010005080600c0500d80545600310005002074500b084682192800203102813031913500c94a0300300380718000c2c0d5403200650300801c0c0945442c401000030980c2ca0f88100002d02e20217000b0b030041c6807a82a40410076040c00c955a000001d80300709040400309954401c441a0340007641200c2c190282e01642c40168007034054154035a620072004030140c0180244401d4264250104032080620400395040e6041c02d40d40a000391000035180846038130010b9030025110244100003010b55540e0380705a00040c0c001c44108221030001074000d0120a2910482814480340ca0400c400074010725051000c46202c030f2403010700c9a1b2040c0403401c0854504603038804401e2a4640da490741c59600c0c03074540217585e00c0c0321074070300e440c5001e0500103078034459002d404041e902035036402581185000f0307916625001039003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 379224190 1250 379222940 379223021
    0x61b0c150612050312010815060415091d060a09080f07051906020406110c03030913090b0a0207031d0a05092701290a0306150b0c03040e0a 61
    0x156159008600c00318a4002c0303881c1c0c01c0c890b400455464403500d468500301c000681c84201154001704c0c01414004040c444558424003d8800040940e051042c00356000e45c154403441c8030078604064400d022421034aa200302c0c1e09004100c0d10a525043c0c15242150780800f0040c002090a00550015000c0200101482e43c091400ca03911061a8840b01c0c1500210b000101c45169000400b004003136000100140400701d00c101410007400e009001c85c0d160702c180c2114501c0366000341440d584001ca0340d4803001607030780c01881d41c2c40036140890803000254400041a004211643c0f1800862400301031254074006000d400b2580c40c03468a401d101c030f1441d01800003200d00300380780c5019004115000c0c07241d400425540000c9201d0481000e0000800c6141e034100d610705403100060b9443ea150000000d00b103940c418400601018140c058180d02c4103a504440061000025240c0040307030000054825a498943c2000c066100c050007a41101c04102901c020352141c4203441d002404190351500f000d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 379225440 1250 379224190 379224233
    0xc0311190e1807020c01030b0102010e070b0d110705010207051203010605040b132c01080309090f1018050f01050916111c0c14070602060f1506030c07061b0c 69
    0x11224075440c12220b100b140c400005074418078401144d503a01d4050604811020300007040380e000b100c10b4003629001c0501030485003410008800103884030300c0e0f204242000c40310360b1480c0c40300e84902d0814084e5110003416a944d00c2003d00584003912650708907030480c0c42c50346801e0b10302442c2c02503640c12604182c101201c10030130740e240051105800700c6a815103440401000400400400403284040c20603001500c1550040c801c4c1c940685880030503541141e801d0507501100d075034a642408262030190400d410084004034504d050101c1c070b404c00b50280180c00270f00c034003d07a00c440522041c404111124900060f8213038105014a01910018140446070802c1e03400090b0300b144d240740b13414801081940081c0920b212241808098546d4855041356000a00a100d1a140c1d00070f5031000e000c1c022401c803048117004100a445469503c00c4a0b1030040c20303964580c900a00d51b0001d940101030103803101c0d401d182d21341e07030f450103a018421003548503510b4041d007656140d21041480840f0100d02401d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 379226690 1250 379225440 379225459
    0xa090c03090c03030302090a080609030a08040f050f100501050108040816021908070314010e0304050120072304110f090612100302010f020a051902130c030c0311190e 73
    0x200780e442403240b01941c001d442c00b581c1c0d0384c40700d0144801c2c070030145e00c0400c01d604030000740003441c00c0c00b0040b5480140e41c0e10b446915074641c0e0800e45602d06003d40010003910600c10402500d500100e003848203a035103500100003680c1d031a40103503900001142c0007000740a00b005011400c900f41145010003500142c808124807107060162501914243c1222010f940000d40400030020a1403407002c0c0c0540b100001c5c0152a20090550380e0f27070041c0c2c0030f882d05211304202c468500b20040016182c00c80c4900c5d0407144000c0c5d07182e070006481c3c1d486000d5500d0081603019000301d9400c06015001040710340c4001240740c40c05403421743d00150410100154415403c000458005038510100342c041c0b80842e440000d200d144d8400074108807448031070b039415904080e42002c0403450104030a1031030445880c90380b69048907880001d103280c408c8142c418840d860220030700c07003060340b40d80700c0c40b00c9503201c1d00c0800070b0f410300c04050303125030080f440340102e203008201d0600e44c0144074000c48494180042c2041c0ca4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 379227940 1250 379226690 379226693
    0x20a170a0509040908040503011109090402060307121107060c05070b07111603140c09010e010302130f020d05072003030c09030f06010923060906040b0102100c05270a090c0309 77
    0x40d04d02020042d9010040420705020030b00d0b0a11a02c14500c0c402125140b800c00075a0108244090080c0080c0c8103600100001d4051401031030480f4524000300c408105e0441c241d440c0041c2608031400642d5044d01e040c3c0908806d6028008486a55400c525109400c0c0d803425400c94207802014982d1500380101680000d9480c050442c042c0514858509524440d9210084510b883e18040001c4c1c820300484d001009000900030900741960f0301070784c42007400c081d1190a4000b811040103074145643c400a20b161045000d54841809038113203075200010803040342c1e401080c5092410981400307802c10000301d09030f041c5190040034110006410390b80c00c0081c243c1001e007041802d030702c0f90707100e80e44940040003c07848844400c4200e54400b07106c55240d007404d501098040030003d003101d002e55650301180550384e000300030015070744040c52020300c0980e040040040090300240c0740200e9001003a610b0700da4460345044c44868000c00a080d2074801c91600d44280007500429010340140b50b82c400302c040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 379229190 1250 379227940 379227949
    0x30606090c0f081609170a060b150d0e0a08070b090708010515091f0303020f0c100f030207030c020a060f020606120604030f26071706010e010e0a0e071707020a170a0509 74
    0x46c081d418a41c0a030000d0702c84c40c02c18006a038011120315102e000807030080c40514022000b0f5400050010310000f89440c06a0f020398a45003101c5000b40c9245008140d40d804c020284503d01d100b41040c5090347e010030741e6600d0045c00da03403058818007610300c1e040800c0d100c1414510801d9921004880d040e4200441040703000c000304ed6590405d900580007010958a284002c0200c002202416101c2c40354001048000916011070100c9420030903800055400c14503120344580401c0b030343c000748030f40c100c41e030f8490010341100d032003031360381d2004d0b016200c0011703654941044e84030038402400700901100d03030b00d5980c00c859111400c2250401e2020384403c80b0a01e03d00a60000d10b40c200d100700c45a06800c0070301024003039240360076020740300710003408c10480140d91000c02824140800e0030a01c1a920895000800c4240700c0d4000e10300050b000c0e070801628030b40c0004800c0105402c610007841d10780312003e04a848800400340039000504007684102e02e55840d50081240c110a40740c143d041c904403d0014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 379230440 1250 379229190 379229219
    0xc060c21040b0115033201060e06030414010b10090510180e0702100c0e211507120203091b120c060703120c120c020705030a0f0807020a030606090c0f081609 69
    0x1601c1d59140c1a0506ca44d0100c0340f100034054207140c20519008011600058100d110040000f89000d000384003240d04140b094011901c0c80314010908132040000e500018025010f61184a205460954000880c0c9000b0120301c0114000d00c3ca01c0b860351400c11041d90881980a00100118461110703003070445040d61140c0c0c6035105035556681c3c2c0007814042000007000403a00200c0c164091900d02030034280000a21710a0f907103101d21500c51f1565410000d64506000c446103400340b80c0000204080b100000c41c041030071507070100346540b985d07441c20103100d07810703030b0751100c1500552141509a850345041009002468403d1601031510020213843c0d0b8160340c10518001c0119100b0002002091716500400035402346920051001910f402c0c00a5078407500c4c69809000c04000c0c0032170b0010300140c02c080390212a0080c10840d02c1c00d940b80b034050010f10941c85100a05898140301411036031140300c1340300c0362810395039036120306460b01c3e5401002c0c0380e1010b400005002103034000007040195145007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 379231690 1250 379230440 379230491
    0x30207151b06020a080627061c1505010b1309050a0902120a03020d020607020703030c02030312010f090c050301060e0f0d1509021c020603010312050c060c21040b011503 74
    0x3503203c403981341c800317415002d01a10891064224468030010301200c4504039580f050007080181c115102c1070003291a441d0307041d415280701d1000c21698402c0c803003a42c41001410302031882c00c010711ba0780d03500760301104d000e014030886c2080c50501040181e11425008180c00c08641400003408210031b030b00041c0210aa800030350b43d203801c014032200505405000031301d001205030001c0c20315031030700f4600207448901d940001020b20111201403c150b4030300708140d8034034180000403071025584401401074000180d00c00d00140d1070a2501100c3c1c401e01c6007060b41e04075207582d02d60134100c0c0070342c00422088450304004243c000d00d43c49030140100c0c0602c0e0030070b032921104040025154a01d80184244054002445030040c0a60b00c01000180c85034003c4a044907088201e104224035140000c031500c2c420030b50104018840c80381030054030800c00e00101042c1d50158044a8540485d03c400301d902e68007150003a2020700d200380108241002002d12036160762451400060115500f07090300b0b0702002d00c0c0342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 379232940 1250 379231690 379231703
    0x31009020712031808090d14010c0201050f0106050c0c0907020c03060c180a150e190b040e0117060a0e03090613090e0609030304080d0603150c0f0c030207151b 70
    0x4800c01c0650b01485501064a242108154600c84c1600c031440580b203610703d40d80c05104203550704014000e000d100300c202015050020b0181131118071000f40038000581d00500c0d0000f1741000050414040c10484140c03416490252400300ca94008000141c140200000c05501840d101d44034256400d0000300e10806905110308c0d00c84003940c030301a001c1c500340e01e0805e00829140209115200035240500490181807130094150781c415400301700e2540b0f0700d0903414182c0d0b201c00008140d414501c0003400070740b0545649200607030380c1d4a101306840c2c0750380c40030a00c082d0450008212800003a4028000702c41c40c5604503407a200700900801d0040c0d011074205a00c03c41740420911090326a0700174043c1c2051901d009190300e04212400c04e4a80c400030380000d04444c1c00041440c0440881c4c1c1005006580000480f1400761a0307040050140c03242e82c202900040d211048003006a0040001d1805142c05900414510741841d48020600031900d240c4428040c408450f010007011101103001c50710700c070301e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 379234190 1250 379232940 379232963
    0xf070c06020601080114010308030604020903060f040510020702010c111207240c080a08040c05060a021507180e1503030f07030f0f141b0f0a05121e0310090207 70
    0x40000d00700b95042e0044140c690600703107407030304804440321b0312130541c0d4021180541d80d844200000b8001d1260500250700350140e0010007070005164003010344250301460554003101802842d03403040b4803c0140081c041601d1124410215201c025507006051000c0c051143c118241c0124030f00d4403581d03a1040312200d03084100758403c5840c000c03a9840c45403081c1080580c0f525a0380d2010054041c115030041000b030340500040a20201001c0c01d002058007800040c1c0d90904800003d446410481c0c000405a10300e50228185a1040c4413040404540e005042511424000826003200020704075803902101d4050a8140c4d0741d0610007407020225100b009980e5901c82d1501a05849005074a4024041d042d90251425604401244485514010010703600e84151551028500c4858120400b900c5892a5110030140001d091490304d401001280c02240d000d0750180a81c0c803405c04c10150b0199440310000f4840c5a280143d5044803084103840d90541d00d403500f1900302c0e080100309a681c9104032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 379235440 1250 379234190 379234199
    0x9060513110a0b0a05070303110a03020403230606060c03071b06120b1f180b09150c030f0a021c02010204031131090812040b06012c060f070c 62
    0x1c1c40c0204984041d50100d030201d00d818281c410300c0c003030501180300703010000403803030105072080c0c0c440c0300303c07030079228549469598284005000f90044d010488451480e485607950200c1d80701c1100e041400c840000b00340f07641d984402c0c404503400031401017149100a000080c00144481004001240d40341400d028551030004024516110502201c41c0d251500401c40100c1c0c50f42c90020b00c20740d2818140309005120031404030340500e00060b0303c41450500385401710b9074000c008010a501902140c0c0c514130102c441c89640c24a00c00d61180525640c010444005000c1c42003018104852260068800068a40100401e0407140341643c1e03005075400901401007040c0c41040c044518001c2d11403000b54210102c104403500340f0b03034500740010b070201c584100540d8101e4002c6103516600c0a011034a90162807d01207841c0c0c000d8404a03121441c050000398207510840d5040d040f640e80d1210444552074140c44054016055060305d0b400034001c0200054450700440180101d6114601a02009140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 379236690 1250 379235440 379235453
    0x11103091615050912060a090201030f020a1b0f0503030711060a06030f14032203020301050108031201090507090b0a050c010501060203040f03030305101706010305010513021003020d09060513 84
    0x2240301d400d020711610912400001c03480042181225040c5140d84541e03403030001c1e00d07414180d52005514400c4108000c6a0501c075000800800d00c00e0720248003007035000210005070f01808004000245400c0701c0e41c540740c55034151001400c0e0044006031340c034001c180c80703103415540100c03108000f080c41c0000031403031030104204031540f0801654040103058259039501e0040314110034094882860302001c3c603440f0100303200302c403e81e403648948115401c0f01c0d00d41c080760642c04c0c0c0c070050b8401d5103010300010f802c500c04002c807881810340c550164100c1c0c1c2020204801404017030a100100844801c0c041030b4400c000e0000c0c14500281e0301e500d9150001c851800f802c0d03400581007003045400600007080783c02d94100b2442d00f178a605050201d00ca50310030344000403080940c1d10503141300c0045910030409002c04100541078078012002407049030b580d80a6444100b080000007904400d0000c0180c0516110364003610b184c180046011803150002d4448406580702a1030356602c0e1341c01ea00000307081088 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 379237940 1250 379236690 379236703
    0x717060303070f02040203310201120c020307030c0c05130e0d0c021c02030a05060a1d010e070608070c0b04062c071e030c060801090e0a260c01110309 66
    0x908500451404040360340e0412603400681c80240195004000700e440e403052009480c0744044100310a090000059002d900f900c04401c405901041c00000785030070001190280d100b1144498005520340794080d542100d020b81d003030400342d034044010304c400b003143e81c0c07030300030400d081c5000c08404203a840102c9580350612140790000e40600810086141c0144c48480c80520b20510f00c98404044a19234004079081050f0340100030805d0040f44204810007506500082d10311110a058010a009003008142260404010b250003680600c1d0308200315031282c1d42c029400800751512414085503540c8500341d45101b0b540c11078406031a0701114501d40c01c04042031180280e10b1240a140326000c992a503120804e078094101a0030110007042d01c1064600c410b41d008503031003455001c0607a66440000d1205100b13028000c075560800024602050001031006502500041c3c440111480c0d1400e51300304050044a201c120030090000b441d07500001e1103034018507016543d0382075a030318100c580e407400c188 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 379239190 1250 379237940 379237951
    0x40320070807140d021e04021c14061009091e0203070306051005040e06041109030a05060604150b0319060b0406020105040218010e1305030714010902010e0102210f09090717 76
    0x503504c1341e01c00144e5240c000c488805c030101003213059901b22210100f4042d108060018405494103242d1091060585d84445032040625191141980f59442000701c4115036280810005a00d850180444500c0781d206403000090406000a140b801c6622101a40c0003100c0520209a40750401c0101d8204032660038802c14240c6040bc6c03074981040307000902c05402804240c01165148158214660150101d034505000241261803601036031030310139078503007040358501e010768180001c40480400403c5480250f80512060300c0c1181c0e1100e400355040069500307843c40c441d85558001038180c00d2900144042d00d6558008512454a401072140c00900541500103500201004020b141094100c69400010002e40c1c070320850880e082c264a18050709030040c080000724900383c02c00c1307101540805103543c030070388075404420652001642c41d5002c4d64880c0122020548083d61b0320101c0030000c0c901c12414281d128107246480e00810f01d40720049410b580410140340108240010030300703c05910a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 379240440 1250 379239190 379239199
    0x24020d030501050a27111b03030103020f010e0a0f0b0703080f0403020a02010507060f0f1b0206070206070e03191113021801080c0702030105041101030c030203010e04032007080714 79
    0x652404010403c030030307078620490150200405c3c0688583c0a12002d039039440c0d100355400e0000c04c000d0074024059510a040f450340c503100c0d0002d100d01103640842640c2c100c0e5002000101039104007001581d81e20041c0c03001c00d500038000c0c2c4012401904e1294000090140040e201e03444504a150180124902030131700c08000050804020000342d001802c1c2c41110340c22320780b1b01d80307814280c584400a072218100488405040c25400a1304104ea03a02c500041c000c0e08204140103c5c052030141e0300e4403003d690100040c0c009400040d8094020508040c80300c60160032522100703106255003110342c0301c2c00780481e00d500b80d1040ca144a0303c0c1242d200c1d8040200c01d4821494030244810000c0180403044800d0f0612441500081680b250001611000e5030068002e02051400e498000d481205000366603012902c2c001030040f007a4071070300c2941c1c1a242d02510901c0c581d11240c400355100140c1a020b44011041c454999494841c1844035400500c0a81c00400c01c2c1418413016a03040784134090000e019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 379241690 1250 379240440 379240451
    0x30c0306050a0603150b0d140115080c0f1605031306110303010303200f010b0a09020c06271501080d17180f0d0206061c0c09020d020424020d03 63
    0x6580398814103040f2a0103040000e9040c801540f249140170165201a031200c00c0442d040400e01d503981c11501c2e4900c5c418440b130b80c6580c1ca0701300c03c02d020103a07030b155580010780480004048080c0c500c0100552821203401500f03008910411098250803213000300c1d45138001040890314103042030240d00180920703007002c218000c001c1c08903a0307480c00305200141c100071100e40403000300c1d00e503a0902041c12403014180c030166050480241e000e03250300f0203054003402c0003101c00500c1244610a5035021441c0e48050019078580ca01990042c081c41200d030b5441c000c0d0950350001c1140704011070308039200c1c1d1440320a0950316200c0003d00340700d403000f41d020034062030030010040d001307800341610b0f4048900010010003c004001452400580000402c04c5215191240700d40540003d5081e10541c0c2c01c41749d00b01c800c2e01110f1050200003007000028018081580248102d070036580140403220314071240103090542c2c0c0c40000e542d140e184a500ca8070b600004010006c166414401300102100a080a110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 379242940 1250 379241690 379241699
    0x6060301051f0c0b0103050d08070809030a14042607060203091c1502030903090a120b0402010503150a03031115041e020103021c0b2409040e0a1a07030c0306 69
    0x2c1d02c41550464004644030406a844218040c2144100c580c1e040701040e00305603103a180035075652860f000070b8804a6001000100c0d4140f244050b00d110b00603000107507040605500d0309a403814030000c0040c00c0700e40309020200d4080d8825541d03080c0e01880035940c00c105148209a07d00380f092580101046401c104100384090b20b0f03110403482d01707084050030345801030024140143c107144a0740c2800308590001040c040e2012000000e0301f50342000b00c0d010340181766a01c00002030350141c844020308100100c07000801641c000c5c0301940d480b80c900042d51561101b05800910b095000380c00840c0850058451a400010100704c51182075194000032405420a0341b514400c1c6a10000c418140a800c034400000b1039110360103880c8400b000800b8095411a480594400340152407c558041c482078004501c0d0034603000440d10300306221400003445c001c10102800040c000e0120382420a10640d005000081c05214410003410b050400070f10190400000040a85070803104c0f01041508090b000d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 379244190 1250 379242940 379242949
    0xc0603091f15050f1c03090609050609030d0807050705030a0504090533030c031c0e1008061327032c0f010306210b010b0f071103100915050606030105 66
    0x2c007500c004580e1000c514825800054401a621018142c0d84501d4544401017580000d07004d0252001a00c40722221503d031018030a541c001c02c0c51042d030550001d90f2034659140900e0003250003408600e40300d440d0014949656155500c003050441c001140001d0411144490740308254020342c42c202c4880711810a00c2c0401000200c07178694110001c0c82c0e041440700782da800c108860555030042c040d18200c2c03601150700d11441701e08840b900040f43c00f005603165949801100c100c40c0d2550391b10394140c1e5898441c11701003070030b20402800c2030044c1c0e100e907001c003c0354002100980560780e1034000a0520401e10b001805400c1c1403121400000d80022820785440c0b80c40224910000c0665944500c07910200048010344034660084800c4c0100c1c1c03019070703e40a441c0602859180c0201e035000c06a03681d4030001c0009100b280c07041c50b07641906100308400208e1101c03040d184441c00404441220041c04a88000c940b0240e10445004040d10f0b140010740d80107000305a44000704644190440d1716060204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 379245440 1250 379244190 379244231
    0x6180302030a081906030c05120d02030403240e032208030403020609150309070e091603080306012007141e090408040b040b0c011515110c0603091f 65
    0x110600071500c0003d00c0708850301c142c40e1348501d03006105114280d900d08001c120a001d602400740a01100800701c4000e00e400502001e0941c807580c001c62400f072031070303e070184148000700c3e8056548403011440d0880d000781c0e02a042c2c5100000c0090740c0d680308c01c10807000e2160b06c19580074406c11042d5404000080f404010707202101d405895099640c0c44040008003c4917002c00014841c110110070721602c4030b000507040b4244c0d0640c55006a15882d07169106a4940e50a02c0c061252110755205000080b4082d000d140c000320181400c0b3711090342d21100c4000160464940b608591101804011200c440614002c0340346003500c2070040b204040044140301012011007900500d19803000c40c0c204284001210000c2c10700800c1c248e210354440100445a034803c0890b10fa043d0300705003001541c03452800812080b120601e034000322a10a2070002e44175000c0d8462010064000e070340014a864171084011846a4446800b50681f43d80805079250120008200396150030300d00004518804400c1012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 379246690 1250 379245440 379245457
    0x81006050c07050d0c0503061b0301030f0303021309270503030a0b061c090b01050301020a170a0b040510240c030e13020d050603060a020f090d03032004030618030203 73
    0x4507070320400324111614162040d0f002d41e42102100d481310b03043c031118180d64410b4400880c2030f15a80d031559aa46038004600794100c1c5990241040100b0000f0030302d002c030700726840c46800c015003041a1914028102182d0340c3c8035141d80d07500d8860351600015608441000a400c03581c25940c49911503c855030b9a000040c0038080306076807402402030581d01c060503036400d0391000140130007410403444c61038003400c407106040711950342230030000c14103190600a40d1103924a60380c8114207461083c403a502140700141c00307051041da58019140c0c3c203817541d01900740300d103400e44207400340c0314502310000c41100008800c1e01510800c81c0c0041d1600303640051a666090342516001a0030070b450340000d403020f140d041a88100701d100203112040c00e596070308002e102f003504400b0744002e541d0b1610f0354000e0344980b40c010300c111942042202458034210391001003030380c000d25000840700b45000e0722540017005441314180240c004141001040320a006e0242c1140c2500c0d0a5420441183d80103035490056054 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 379247940 1250 379246690 379246697
    0x3030f04030e06040305011428050402010e130623010206360c190501050702060c0304080a050a0c120b0c0705010e060118232d1e0601081006 62
    0x410289440b41d0403000c1405402401c0d1692103560749416402030848403003c00715051003500217190784c81d207501b501201d01c121100404151000d5071114006000061089050190301c3c021100d4580313a490742c0344541c0b036a015002030b0160508000d909000700d01c8100204850060000e0301c1702d641e010907a5a00221000c0311020140b004050395000c4005d188602c2c1c0110244a291640362400003076440711082040e1201c400650aa9204100e046564003c840c0407450410410006003014401461420341034015a410241c550141c00d00f09200e03031400740c0e01c503804142110305100144501e440140300c2c1c2c50511210b915981d0303807031032009401002e01062110229240080c42001c1d00301100994031070341511015a16001c07846500390458030840c01c541c0c60a0310151888140e80c2c941d4030445404214144070340ea0310201e90201d01410321071b40205082d81c107610011a010101072074080c1c26140e0b100181090003004543c0c03c810010141c1d410400d0000501c044401003e0004003907564624 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 379249190 1250 379247940 379247971
    0x109060f1112090a021f26010b0f1905120f040c090b0f0a03031206080c03100216050102040f140103050f041103071a030901060509010810090204110d060810020c0303 73
    0x101058200200c44802a402c4000d0001b031401000640c4d03122107501244d81c882c0704201102000810706a2180c3c0a410f400d0215240184200d0b500880500503000718400c105140400114001e94034102e5044982c020513400300b90101101c468060499012200204455581c030f010348840ca00100144513043c14142d840c1400152500c502040028001000d001d80d208165686801170030300c450381410407480c40c50182d002c01e0410300400c082601c40801001400580903803041d41c0025840f012038000000c1003070088000158007800584000d0100060f0441c40301c0c507000b0700c4030310801e5650103181050b1070001040441c0d240340c0d00003a01f26400148100c1040002070110b0b2034061503400007104000305800d502903032000c01006502c20301e0550001e2002d16615411711410000c00e0280f079035681c00c104101084201c1d80c0c1d1100310a64001440807451540065405c2c0181d4407081d035007101c45884c5c2d242400786080c10410740c5c2005440e50000c5240c440c4100308241c0f68000070346122507a20300c84 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 379250440 1250 379249190 379249201
    0x6011b030c03030228020606011d1c0c0b0408010b0907050a0e0a050d0b0405010e010b0a1a0d020d0b090702071202090406020405040e070305070503060f07050c0109060606020109060f1112 82
    0x1e0741618001c980b17140e55890b034950203070011180d1800c0361307500d840181f26000c00603006504c6195042c100840c0c4850381610a1030140401c05c00c01020030403d502480c261400101041118481c54014031120300030b503540da802d011200382905c80381000240168681c000b07204140b54005d044965041c0e00d85001c2c6043c40b013180c0001c2e034800c000d501c0113500040740c0c0e07203103000e00002c01c4076507000c2c921130b0000f04060700004002500780c510003414580e22401102e810010640b48040402c2c151240c5c9449034945070113070310050100c1e00310340c901341545613072198452482d00f0074000c200d41003005400181140c924003500c251803480300e100000c1c01101d0760390200b81008000d030151409040000c000f031000c2e20a01443c0c1d60f07111118071080e0342d94070401000091504010810300d02038115401540911340c0c1d0f02c0d0b000c0e20181d118000d603034410740d6220340600c042000d5218800c094402540041180d441c00d04081040d211481c2c50b581e481450002d4407940702d81c1d404111400b03000d4007480040c050307a44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 379251690 1250 379250440 379250447
    0x30504150507020705040e010b120a050d1107081506010216051c03090b0a0c1a040215160209010303051902030f070210180e0a0609021309110f041d06011b030c03 71
    0x540e102d182c001f424650020381401c419004072841c90300136038403092005081c1404030782d608100c480162050300700100714100144100641074040c0c03030481c1243c11460351415600e10704000d22034420240c1c0701500034480950f0b41072098400d060020310b0600100c6041c400020806105420f500820000700d0141e6420140140e80707030300003807110719690380d181d01c035461b405000555210001c982000d0918081200c100c032146015001c0c40e0040c04d001c610000c240310315a0b190b030000e24405d03210411440c54400603600c1c9881d080c007862180e074a46031181d90001d4000c2602a0304c600d048295003044c0122094a80c0c041c1c283c0e03010540458040740f025400d11025204048082d49100785040607840c0868444404048140210700060b0200401d680c1c5403109012401000308501410301c448004008107007258020501000c0800301e19840c200c2d07021f85002e5164041d80c06819100814116040d0384009000d4165228400382060811607040002c014941d040492008051100e401c90b02400d0621 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 379252940 1250 379251690 379251703
    0x403141605160305010e0d080a0f18030e090a0905061605090a060f02060604051311031f050901052206020a02011104080a0b01170c011b1a01030c0603050415050702 72
    0x1002000e0301c0b4030403140c0d03060030480452404195419821b0904180207864002480ca0202103265074205182d2604070395580949410140341074826141c01000c200381c510074a09600080c401c0c0c80c0d0040c1b118001d014005180d0008100c44501c0c0d10304002580420340200b10603a10600d045580b842680c0c900b142520180141001e940d004080c0000114040741c000c0043e49003180c0035006c58185641300c0c400c200607100200e9030141345c80b03034a5400c00001845480502c010391401030a030348401d401c204110304108521108250495110070a000e0001000c2c4501a04100510040d080342036003a4480c0050651000c00107000b02d5002a41c8460f2500c02e512000c4040d144510280d62036583e01706007139031046814003e03200e941c0e15800005030702c00d941e031210104c4070811028156046000b0010741c0c4401040c1241642c800816462200080b205030042605901d0115103490725415428824503022440c0c1080080c1464481800b020a20550a0b181361000c950004505541e890342c040b8141070307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 379254190 1250 379252940 379252943
    0x605030c132004180614010f02010b0405100302040f050103020d0b07020c03030415110115180603020d0515011208030112050c090403091403030f121e040c150804031416 74
    0x5010958400c150302600d03000b0011520b1003004406024580703004c01c001c0350294880e00c401e0b4884842c1c03103600c9501811440880000e58000050310709140e40100e0f0030703030701b04a841c6401490111014411882c10f0710440c030b0408058002044158155804500d007034140c200081d021244280c0041c820170f101300440380c854030f401f9050303d485650b01d110400404180b0068000400e5003c903040d00042070500c1a10981030321000c8650740301d441d2010410411044144412000b901c841022015850310060b00074114070850084c0384910b1410740e00210b15606800003040c0000c08036480c0007090711503050324191000090364244d08045444d203e850311240900755900b18240908000616403c0841401152550030107450700c0801a0200342d200e22031503105c002070130401d1041c01c2c6001c10302040c96600a0402c40034503041c01c40c840ca500e0069034126070850720100c1d40101408503011580b00000c425005050414a030300b481d56018003110068102442d1444010840541c514094101c1d1403071305 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 379255440 1250 379254190 379254221
    0x12050601121514150907141c02070c050a080a0c051e030109050a0311030c100c0c050f0309010f0915080403141803161d04030203071a06130605030c13 66
    0x70344440500301c403003070b80c100c400100d456256107429004e405e160740b4061041d401380c2e8401030100035944a9003559007001100c040d131405000085c80003400f0510060151600544100018a140c20100718030003a0300d800140c1150401c2d900791001549140d11001624411640402c1003010b1200d10140c482005c0d0f00f5648c15030810004005010f80810012a29802581c811980c1d24160810913540c4c42200032100855200e0400100201e943d40d0002c550080c070780c50a64180072003034550901d41070448140d000c242d080000d0020345503802c19a0200107015506050500a1900c070b4043c40289040880c04144180140000c00701445618502042d00c80885102c0c0c846800c80c003034114407019580e2040c003074410000301d1444100031402c0b040c2101d021030500342c603a1860642e0300d25610f2000d03100318154801800008005080c080c48403541d0102c42900c140149491010400440c84810750b038800c0502e0318400384015200825184980c00d425280846000039440d10140241000d80307484412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 379256690 1250 379255440 379255451
    0x150e07120204110a120c050306010f030203130f4205041b0f060806030a080306010c030e0a030809030c2209080910020c030f0304050d12210203010807120506011215 72
    0x3e45e08600340d001582ca65500401c01d0302c0c0c0310741c801c1d42c09210136298180030403914410010301500c070750010f582c06045941100c5480f201984d41c03298451111004507084c0d1104c2d1883c0c1604184082c085024940340c0414903e260032042d2419842c0c1d402c86e00041d501c603251300003e01030000035018803248943c8003c0d4413505503942c0e03150441d209054010a00010324034000305001d85000541b204003150041096803450b2101d41c0103455010a0010450921403e0800845950750741c1e0301c0c003070013180074216081d540c511103407c050070300c1d00000c00e481c4100c04c00c0c520009041100301e01d480d43c4045a510011f40002c07141440c0c00300380140d2010b1a4460840790007010b0742a408281d1960140c1c1c1039003280c18805d00040d1160300c90289000c2d081c0c000d001c405190f404213a02c0c80b240402c20005040001c804254825102100d060b00c13000341c0c580d2500000100001d003400c000c810000c281109030603e00c4d0b03015070388054403400180709190108a60400c01800d0010364901d0788484104103008118 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 379257940 1250 379256690 379256707
    0x507030807051b1b0108010b0436090b07111b060c03130603111603050f09060d1505060f03010e0603010b060c0d080f04050d03050702070f03080304150e0712020411 72
    0x9813019500c0c00c890140d682200c1401c46035000c1d0752003a040c3e40c643c0382058105030500104440e0034200301c1904180d4200c1c0d510ba038480c40300000303003110300c00740b100e001207110b103418100712000c403030081c000504201d40408809245000860090300c0c040300c40302c0543c1d1b105e071000f0006105010f04101a00d0318040010030744c941d1508e100c2c840007144c500707480900142d44200c0c8040c04900407402d8070003080d180d01e0040c40c0001c0c071860092907031141e22500141840707258008103009400c1110500040d643d40c9031140300344281d030384031000146011103541d0320344143c2179140b00050006100b0888084010004a50259020f402030703220f580024244a485240c160368040d902e120352003842000c545680c1c0031900703c5481111341849150003100410001c019180120b00070000104110218045e000700400d00800c0c02103543d001354011800140c881c1060304111210075124240f10252914203440e000b0324581c0440c641e0300310303660b1000c034200e00b140e079002007006071504e0380402915a90003c1c0300b08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 379259190 1250 379257940 379257943
    0x81b0d050108060112020a03111c110301050a05060d030815030607480f020a08011a04150b0d02070515010303030c1d130b0d0809011e0507030807051b 66
    0x1d04940d010001c483e50740c1d0340c40d1042601d03407070088006500685400c0017070001c80c02e0307640280c1c0c2080000c1d1600c0d80c00d1161040561021240d40022213050101d10011911440c1c03d000d03498000342111800c101604103030002522106041c0001020f2150460005202070b640e8111084075074405405e0364101e00e410175004006000c140d00070401110100309003035440440c041c401485c190300110415208190603800741c090480020112248254040a4401a16000c40c038000070a4180004203c1307003441e829000503000304004060182c1e2400140c10440404a1400380c11160b0300120550303100d5001c00c80030064494000064114800c007421a4800c0c04030001d014100c900981e003c0015801c0005d040303074440c000b880d00a2041000422034401da02e0600480c1905401016000a8013076410300400c4075078031507650a4424000103c2c00c0c40b640d58101c404c0301100b0120140b02401c10714031040182c414040c1d4800039003003156100001c0d54490050381100c2510070310100070415065141e4400303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 379260440 1250 379259190 379259201
    0x30d080405070807050a17030d06183e0c03070b01050108061e060306012607080108070b0d0203060109030209040c0510030b0102060117150705030a050709060e01081b0d 74
    0x4a030180b09950b03001a402c5008900e16059078401440e07440d8140c50305c41c00c010302403140d4458100703d00081180a00c074408511400000300700c80c030504104012446201001c840c829401d640c03541c1152100120701c40042c000601418250001c0c2c101c0d00b220b480004a01800342405600f400e00c000205401444000103065040305e5099958001580c3d502d018009071640f495a400c2ca4003600c0503000c0d0840c500040a0341d8462410f24102e000c0701101c400d0ba021803c504034003c091070009405200103144d00c8207003103001d050300000502d030351803a09207210824842c15041d0403c1d02d40c04804107140303030310440406006540041c230170031103820b00317080075010070040d44201c500c9144202180700714a406405080b000c41d030142c0240c1216071902d4002d040c4a4482820700a56000315480d500c40b00710305000c1d840c0107001c10b0b6181070702c030303d42480b0f20011200040d01c0803060003c0c04c24200042035110140c0c80c442c0c0710a29000403c1e445103034000408000d007450b40d10442901050030700c560010360740f24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 379261690 1250 379260440 379260443
    0x40e190507181802120309030709051b19051303150203091005060a06080a0608030c16050d1707060f060b0705070504110415021204090e010509060f011211030d0804 72
    0x48000b48414a040001100c07103040468040d01e040d14919805403614490b0030740e05a0711503040c2c900d06000080001d052440715009150f00316502c0090088515044280d2803041d0403407040c0c649403000c804002042c96040400e01010000000703269880079110f40340c1c20000710f030302000381c62110002c01840c002079041114500c3d003030310600d0b00b9540705c0c002c280507a0b03011750130190120b01c210741000011602480d008101400b80317601c03684000744041c4200000c0620030170460107414005083d4411f9040300c000d541c0018840c4d11340415140211300c60b4180e41b02004140302030503684648500d0a03030042e000c15403001c99194070302140000c8101105008000e4030348603e0a443c1c0c5903072280100000c4500b0b141c00b82100e12000c0c00188040c5040c1c0942000b0074503180104e030759003a03500105515503401900b00e00e5031b0030f8980c4410144901d090142d0354000d00c4540203008585445941c03c0002d2505104403a0b142000307101c41020300003c5d00740304015020140a490388075140005c0030b000309800381c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 379262940 1250 379261690 379261709
    0x6032a0d06080d14040504230a0506120706080703050a0e1b0f060f070308190516120506100518150903060c0703020a1104060b1c0e0318040e190507 65
    0x66281c1c0144242d013081c039582078141416007858144410b1000a2120500701c41ca41c1c610125402c10213586845014841c0303240007400301d00e078900b400034814400012410742201d45d009410500c0300c10b41081c0083d40c42030b1246400103044d074401c010000540211024000103019098101d0011982c041c0c031001e00003401d4401c144040d0030002071182510915a07819091001809207100107071103880c0a03a00f0001002c0000e600070246403a44040364010b903a071030440d04684034807102058002c26050302c6000b03524403c0005240c07000c0807a8800d508071621a040100014006204a61000c00940022805005e00d103540241544090301680128030081c482c0c450780c00001c180e00d40380300c111030155901d503014041400740390b56140f581c614000341281c0d100b0303141c000118500c4120000f0308501d00e5800203c25944003070741c61860842d100d040501c10160410020071854100c400c02c040500142074600003013021a0600f030030304103003040d066082c0c0d100c0322010003014080c0c0041e600064032207010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 379264190 1250 379262940 379262953
    0x3160c12061d0d0e040b0a0e0109050702060a02160312020c0f0f010e0307020112090206090916030b040c0e01080c04081c030608070e04020607050f0d0f1103040506032a0d0608 77
    0x41c42c2da69990b0110f440e603400900703000c01802060038503402c4400a600060039405506481d800311050001d801d803c203409190303aa008115130b80b0b504002c0e05811440d060011850849101d901c410405450309028003400480014a83d104031a64102c82c000c403800b009480e05008030340b44c080d481b4440f09480302d9042d802d114150880d0007000c030840b442c2c2d030360585a292040d040a4100405844c051200380d034003030400c0c0f00c00351680e16000c0c24544500d00d0f00c814141050100c460250841c0c21075035607540107510784000da60300340341c10458001d40c0034800d083c9400241e80f08008130703001e48500d410041941c0100403c900c50031140c407040c5000844251014401c0641319916190385113882e00c1443c00a010480120303025040050080400c61700a4040d148101c04903042d20345401e46822a440010341040c040b04003281c0d1048000c3c51003c040340140d03103058a04000540d040c0805813402000084480750039500c1c020710704e1400354a18031942c2c015250800c0002010040c0168071038018035020745d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 379265440 1250 379264190 379264241
    0x31515130305150c09010c030306050a0b040302121f020d0e010e070e18060601140705060f09010612050309040c091a0d0506010e10080c0906041517070203160c1206 72
    0x114144149965138505081144880c0111071440b6101c8003a0249907603a10007040750303101c10981e40c024000c1c082c28540e5540c5580706108580b9040000f6101640040300183e600c004202c0b907907103413a6580d40300561a2484080232600400d00401c0a615640c40c11402c160358050104042044420480c40380440380c0e030701418101074106400745200380d60070400000d103030fa6000741920b1220310841403001c0d00341f4180c2d6a40c0e034548042500c5c00c0307030304690480800c49120310901a80001d022007610782c600000c410340d42d00d03540e4014907441c0d510440d100d01046c001c0d0b0388200c011707000611402c000b00861003a5500076500c0c5612044c200f81e4241c0c1040005412940998070389100e408000d4500d00c06200c0400301165001c1010340845048201000551003c0d84e410003d0001741502c01d64804507185020b0000c0e100005491002000c0740c801c800b0051426004815a00940403a11030001e03120910301c2c0030780a0442e60303000010100c400b0320a1a06100c4268042c0d0031003080d540c0526201c4880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 379266690 1250 379265440 379265473
    0x60f0905060d0c0308031e0a050a0b040908070b0901090b150a050109080c01110118030302211b0310031505060915030a140f07031511040b031515130305 67
    0x4a60b0090440d031200c010800004801c000155031045a1140e410755084032203040b60b482610540e5980340c0151282c0512034030b00c680b44101c140001c401c0354204800e066507926002c140c01010030140486019900203a40d0301403e41001c1c0c0c034103a100090320501d01d450030030000c00d1051585040e0007154043e6020132a9402006080195803402c001000c08480100044580c0348002c45000029500c80503440703160150400070319040c0c0e1090700c000d80c5421030107501a02c48520b90140c0c80c40240703003400f0b01c2001c018040b1809840840c119105699940b410f10f4a00e228196134001499090307030b17003010f1041e40803030f0f80014091402103070140a10f48402d0341c42614807040e80a102c0d4181c100c10b000000190048600301040d84501040e03980c01d803854620740d4184811036005540b49040c90100d020008140e10400c084505021005400c1505196040c1c42a020060801364400755010007900d4030340c0d0388156030001440035034203103039690350110400520f01c080b8802201e50384100c00020040c20305 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 379267940 1250 379266690 379266709
    0x30b040507120203100302030610032603060616020604030605041407080c0d030201140103030f080705040f060309030309200f04020708030703200a021f09050c22060f090506 76
    0x307950b011282e02c6141d065000070352016112540c0c40c01c0d02d040000040e141070100c0b0307205041c6502505003032880c60408884010514415111954151104c003c0e40d85810042d25001135051320400d80b15a00d00d0781c0c81880e0110b00d80003035880100854001300300700d0250022441603114100015085c03400c41c1c801c80d9203074124041c221542e048805084807504041d000380310a13600920000c5540c6002e100301c1880342100381c00075000560010541c903842d40c0c0000c60103411031107a181c03091400e0710340b460011910803a4007441c1d00301034030351042c07c00740751107034002001840d0010000120041d918031600c00004440480600841078090328030303000e2421b882a81c80700c43d0003003003103459656490f00c11001040e50002a4a181902120008005003072070040c0802820a400420300c1d030503a511003262107650218030000c010b003050a0a0700040011540c0c002100040c0c40300c0150b041c0090000140d41e040b50521203d840c58000d000605030243d100140031034844240070012a2100410b0095890 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 379269190 1250 379267940 379267951
    0x6040c081308250b090d09030b07080c042324030f0c07051b040b062a070812040e103614150910060e032506030b0405 52
    0x809044900120384440c00401c03c0341d80380f01c620980c41e04603030766030f003406842c808003500c03900c1d642420440034600030020558895042d081029202e8039650f5082e001e050700074503002c10000801c01107140d150f5010240c4010780449081411100c0003410590900340c040c0e400248100a04004031421144e02e031513082d20741c8425541e0304d00c8e554580e0a18030102602a02d24060b0980c10480c031350100b8000d002d00a440c0900c1c807034003905442c090301080181e583d007446052060b0001c200800003552081d280201d5060764440003603800111410043c1854181e501070705090150365880d031241e0480700001c1c0107994050568610342c1e211140c040614141ca4060b40c6040807052400d17038039903070040303405032582040d100340301d40003056805500080c0e407440794405450a146009100e0b64189084484d907030b2880c00e69000d42e0503d00036049903c2c1c034400748640814017038144000c0d14143c81c107008500c2c0b03154044904c1030011201440d0034880c0b13041c1b44101d90020703280c4007040c506d42c07419006440c000c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 379270440 1250 379269190 379269211
    0x5030d14010b090402130504140a0e06060d02090a060302090106030204030c0b070f020121140610020a020a05210109030905090c040305100b060d060e01150503091506030a08030a0506040c08 83
    0x165903c00c0c00001c0d4020300c007540b80030341c1000d000110b56907540904d4800c541c0d50001c00019080c55030010307058541d800d1146440d500300400700b10250701d840381c140300215011503221107151074907400e400042840b600040d4010140e24000b05030740f60103070020310440784149028a00d903541c40a4808041c010b6441c0102f18030000c8001c600950310452030025900c841c1d05010005450b080b86003030850b808400302446080f20213081000b1407804455141020300a030020b417805001c01e40c0010603184250103010310960741015110905200702d480450b2aa41020080100c81d0440c1400790034104903102c0d840c85140c5080010b01c4000c015010344046980c004d0007000c501030540c0711107015084001c0b649412910503c07018000d410340713000300002809140d171b005a50b0350500c0c02c4e81e1004801c640d11001886020810700603983d00002d40d018641c090021440c40a031200c0c800070f42000e441c1750026255402c0401400072041055000c5401440704842c1041882801c040c151400d90b070071510386040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 379271690 1250 379270440 379270447
    0x15100311040905041704180b01050a0801090203100509040b0405010c0203070807201801060e01030b15180904031d09160e01111204180203190c021905030d14010b 71
    0x201042e5006242c0152049160725003000480305440141d8000c1d5100c580d440c80480070f0592064800d01c60044410340a01e4105d00e0312501c0e01024014100c10b00c03852142d40d13400400100c000c007044d02980302078900140794003480d0030305040420032200c041d2000e403101d501e021404040b560001045903015907102d40e046040c15155100c917104914075480707540c410840c00309458455680e0043c1c007620034600d0a001034103075043c450000c050004032840141031618005407010690360702051000070005030014203a4032041460000782200401c1201904001c01c1000d0101301a0800b130b480603001c10340c800361036140e08041c00304410b59209444045050019034100c9101d03601c07494403030207400018140710102c41c0c03041c50450710702855041f190348582008102482215a01c28a0790902c4c01140ca09508600f840325203400d5241e034065010b2801c3d50f0b101c03c028046c9009102c410600c80000310204070110103420603d031a98072110740e888602e86000c481d104018800e102c001e050b50b602d000581e06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 379272940 1250 379271690 379271699
    0x1219030e041a0907080406151206050105040203060604030209100308040b04080d02030909060d0c0b0a0f0207080d052a0a061e05090c0f01050c06090a05100e0c01140c061510031104 79
    0x10034020240c400d880396512501208000000048c1c2d501c003c10440280161340021420a6800c40e081038101c03d2181d4010014410199200400d4809581d0101c2c0c0c0d1140c203844040c0303007904000041d03100a02543d000f140020781c40c104a0090412151030f01d003510040c00d040d4000320f031640300d240042540078807214042200340c14404201d01025114045212110b1703103810110083e6001118207000150f0340398030071b248190303040c0b11250007004009c0c006c003128110810040d10501a03031045204021070941e0b6640c5003001d00c4840d10540200d40183c82c1d9806060814501415014041c8501d4124101d80c0300102c503251b1040d14421865840070b40034442c00e51080203128135204c0503490400005020411959006020b1503004000d28401010503600c9498030a003050a00303469581218503141d9a0503111034042074400c0c991400b442c00d82450a00002c441085014003e01640188100010401c1d0713040440110016500202d648205106000c08100e040e12401881c042591034203020801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 379274190 1250 379272940 379272947
    0xd020f0d1b020105071a0901150e04140319230304020307090b03011401120b060604060e01050a0c1506170f03090d030e090f040c15020c1219030e041a0907 68
    0x540324414540207142003e20b807540c590004103030340384428400c0c01700d047c400290401d20800c0c0d42d030740120882c941680c1c81c1c00d00e005858100103201900380c5402c100c180c0928034040c41191040c40002c6029003800d240440000c04601c62a160028158844400031080880c0b9074142c80c03150381d0040003440428100740080c0054106042c0054041d929045422010b81c00c440000f03000e8000030840c2c01d40014030f410444c8013600f014041070300075141000306000003940003201070000314003800d08030750760300c200c0034200c401400c485005000810301c3e03160b4408410180c1c01001c2203910701003030340e5090b00c04401c40790348a0074140d40c03025465000b0400d00c072540c2410f0080b02c480b140641000011448000c01150070007200312041c007000042c1904110030401c007416860081d0000c4561191650000800655104080304219100d503800307642c4078640c14401c000c00820031082c1b0805000b1540c032840c0242c4407240d90040302d413140d0f00306410f900498548801181c1368202c0240301c07103001d45800e8400c0e03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 379275440 1250 379274190 379274237
    0x1207060f0e0609121e0a05070618030b04020105091002010b0a080f07090b0f060a090828020f0d150b1815010c06060807030f020102011a0f011419020d020f0d 69
    0x3e240c5405191001422003500040ba421301c017400300b02034031500b0140c0c0303021420320105070444010b2101340c4890440311041101400141c03a0301490140154840d400140c8950080c03c9010384e10011300c001e015207059040d04002594802074600d02e42864030340c80042c0c4c48014200342c0e40d226a024510410030640250491005040c0c0034291094108620021980d140c0c000454040800c090880c100318800c42000051001000c065034412125142c00540c0d198400c0d03008040e03c18040504105a07070b5803000740d24050b45501c040c858060050028260001d4416102d40358030551070300c5103070309104c500e550040d4422280010147c00040d1441700545002042a406842039580c0703640110b19100d04101d020003441c00340302c3d00480315105100090a407480c00400b942409120b1801c0346040d110b81c80190120002402e08002c0c01250240300002030141c1e02c81c0395007d1607584208401d09401052000929074258281d070000c400c00500c10340d0390301c41100144005101c55a0b010518043c50100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 379276690 1250 379275440 379275469
    0x4080711010f05032a070b1b04080c0603040212070e060a0b070507091e0c050304150c20030c060f07090e1504020f0405042a0c050606040207050a021207060f0e0609 72
    0x44202517144425070582034022800440e140b008803024031084016100130160502d03006044c0a207418100301d4190346034005192103d019180110100c0d0841d80c440d40503e42d6942800c08994905964014141d84c080003550750328042e00c0a082c0100d02d194500007250907103508800140a050314102d0400000d014142400280350040701c07141d84400e0280c01040a120015600c42d40c681c00c01e41050f8071039480500702511303410301c3c00b00721000158100d6030295010f91714800702030000c507000115504620944075940d105001e00000c01001c000141c1c000c40c00340805a07134602c01252100314108401206499526901080d00e0000310780e89016001042602c5a411849003010366031000710301500e605954012250b503002200c14219242c84000c54880f11440c40c080e02400101d032902030f00c801e005002c5130b01079600001c42c80c080c00002c0240c02c003159070107011103826585c081061501ca1002d8010140018400d4441d107034441d03ca40b00681e0859001800146850502d00811000c2d40c1d0b000003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 379277940 1250 379276690 379276741
    0x9060105090607030201021312200f0d06050a05060901032001091502010f110307050904090507050604170f0705010909020a02011b02160519030206030702070e04080711010f0503 78
    0x5a00c1c00d4403014090007440d031280e000580c50f4254045000810101600101c41514200041801081250094400014001020415580d94000898580241c070b07000180c0020312900075a04004080c0d2004c0d1141c2008801005207855480800c00c0a06003840050b05c189555242c2c27070b424150542000b5135001c1e05040516060760755103c004a0703c019200b00c40c000d030759940c3d02040710300c0a41c045c1c090320507101440280b4529100c02d029101d405042106400b540d07541c0c5000c02042800c000b81c0005e003000a1656460b147e481d4055114074200044040d1913014010031030ba0803490024036002030350320584508920a06010201c0002d40001c07a98030110f640b80c0341071060754048142010004003140e809404009807500420510f51019031116001780d186818401c250324841c0028419a03a04407005956500c1d50307030080307181100325082030a00411000c203000c2004004001421814072469260034440b1130780c4015228500c004c01000003040c0c0820020744140c00800110340f40094185 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 379279190 1250 379277940 379277947
    0x10f02150112030e01020a0308071101111615050105210316151419090309031e02090603011a01030f110d0504050c0d1106030a0b0603040b070f180509060105 69
    0x6040e24210300a90000c500040c102028009065206403e224821020300080070f001030340d1b6600a01030b590007001881049104611035081003000e411410000c614151229101c07038120100802e9003c030000100c40c0700082e181003001d05411801414100d500052004011545041c8071684601105140b1001030004101c045003002040d0b4118021a010b480024010307aa00307402c15048800240c00c0506040a100400a0481004c0721600d600048450301152010061509469101e040e410051005c040c41850309001c0c000e21011964840c02150031400b0f644451040c582207409801000e62416260102c45540e540030b03405c10b00d070840c502c840000e0000c0b281c600203249604200c140140c00382e200c00c117100501c0320410040d116003c048881034040c0c0383c6580c640c4044400041214000c1e00003000151801440c1c0d400500200b40282c081680c0740b40c60b1400310540c0c2821203112011560807400c8004607845041c2c2d280c2422401031542d4101d60909080007881240207000904100040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 379280440 1250 379279190 379279213
    0x806040f061107030306081b0307120302150106120f0b060306012001020c06100501030e1c0318030309060c020111040512070504020c160b0708030c03091011090f090f06010f02 77
    0x6100800c24140130303540004044d800d1981ea14202047ca05040100c1411143e0300303c030359900403a0718821218000e15071158482c40e07207020381c00d140c0ca038007107400d0008100c000000c4c20b5030800c4d05001818a1000100100c2022030412001c95010000b003641100301400050859405041064a901c02140c01b06401400c40a02c103820ba070320410b1240303680d4100d04180103c502a1021400c040e00003403e0900108080d424480d507122060300ca1440a04c4070f048000411038000d510001e0f00d071121003c4100d03000c0d0700f810050044c0c0402c501c02c07150320345001c1c11030301c80c5071040c4592408584c1da0303400703203141614050030000091080720215007180204600001c140d6183c0c8001e25102506401600034000c50603808401000e40340d2040d44202e9080142c0310005101a00700c0f80d0042c06a07a58030b0b103d44441a44a103401c3c200b01500301454904000905c400718140301074184c3c00c0302140d100d06100585424031805d518281c481c0000a01544003140180d802036034101004512403044524035841c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 379281690 1250 379280440 379280471
    0xf0509060a1e090b0909150403030b09040b091506130c021006030c03210507030503070e0306070306080111160308061311040302010905010e241c0212010f0806040f06 73
    0x40d040003007048020b403001006040200c0c0144e00c03a15804032203000051038002000c2e80c64580261503104800701100c00a400c060080e80182d6a0b090003a010098510b01450301008014040d10241c0c610310504c9140c0c802c403190684e00c01d100307840140c520201109400100d1014000d4403540c2019401407640c011040c0710b5a02c2400d0007140a0285200081d1031810143d2103400d0030307a5041e078000f205072a0b00300c0c0305420a0403202c1640d49450a2641c0340d45813542211203208685409900d030042c0070a10468950540120b8140c1d100308000b0401001100200c01c0c2e5440740c007124480c204c682d51182c0000c64050110290710a00182105081040e24010ba50031505034811600103c0008a01482507503070100020024103020b092416032018004001030b5008030b0f8410717104407841200322840340c050f4a4000d9031081880308442010b41040441884c000e5001b02180c40181030031800000342c58003469000344101d9510303101404040d05d039911040400c1c080c10500755041511600d401c000700d000b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 379282940 1250 379281690 379281719
    0xa060305250510090303140706050f041407080c040903090506030c07030201050c030609151f050c0d2c012c030d1d0906031914070801060f0509060a 65
    0x281000340201034000044140d03000000d9003002c0e000d000c1a0202298554102d1152016a41c00d41445e2880b4100c00d900c1d1a45803043c803100800042c00c041c04d100f03840c50304d1241d05004a12400c41c0880040b918400e440d0b45451074841d032071a40d0710000d0301ca80c03241015440120b14078000d11b1b180400380d0710b0f000842c1003541305552030b02076480001100000d0550a100c0c00342c004070780c00c01040c95420060001814450068203c000482c05c05103420440d0355512185002c00301016507050b00a60109d4020708181c0140d011071480c0d0240c03e1500d04c10320312170480101d21440400e90503007418a20102d03008148280d410f113a050048840980b5642003652250240031007528103e04e0070746035180249428a04810750320805e110080c0b503405468400c0f120150031981c015030b1a842107a8034440003c1c5488088401501d10b004004540300a20103c00030b28402030404204031510f4a6a90f81214200c4a442c4034100c0400b628020601084c07400c8511107410440040c0354140756515014004061003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 379284190 1250 379282940 379282963
    0x131515020a03090e07051902010e1b1806030d20030f1b0601060f110a020d0b2502100c200d0908010912031d0a0b15060a0f080a060305 59
    0x2402151070004055125a003100540141c0101c4400c0d8149040094003030300030030410085d0210400303980ca400c14802d622090907400c0c020101c40d13514401c02c89820311401180640ea000d00744201c00c540c440703189101001e02078103001d8010300740200e19550445000300106000d0303030380d00b824980c4600f041000304080c1980d42d1a111300281e0794900140c0000c0030043d6044054895001280100300035900054401d80003103490401c51994115213003da414005401c41c0254495410005041401442c20700144035801401c034115050400f8464464014450030b103400050f84800402140305801e43c00c40d04904505060003072151088402ca03486110030041c0355181d617442042040c2007942e121900c80c00900e41c0d01c000300014080d40d150114181009080d0303109143d251005010382d0300da0090041d41d990558425550180750b1450010302c00403080d2a43d00188030004525242ca04d018001c40d200b900c0b180c0c4842c900340381c081509a668101c01400c04c407141d5645c100c0000854414070411a442 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 379285440 1250 379284190 379284193
    0x402030c1207120e06060d12020709111e250303090f1506050607030503010e0702191101080a020315040e03210910020319020c01020720040f020913151502 68
    0x30f1103040c0e560446500881d6025680d1100060103a2600d0382c0c88000c01440d0401030019031183d0b00f10341a4a424011f0b840f000301c1900d041411305801030b2100281001028010403d91006d18440481c00107000f45141c0c0d8812030341000c5144840021b681042d04810f10030300f00490300c110992202880380010038001d03917008901180071501d240141c82480e010b0003048070064184a01500c1c01442800140030361041900d031040070400560082081200015413003942010a806070300d401c0b0369014005621358081403245000c515007904900030b9a2040207241540d250448130311080201030f02900c2502406030104004a04c800740d00b44204840215035800001036604012280d180b411507485c0c0c0e410042407052050010700340120041d8451307540c984c2d0b40581c441040020080c0203108145008000c4100c100140000c50304008801c90440d00c1200c04010403201c0421400591003501c001a13800180c419003170441200c01d600c8003a4084000ca50300710b4464641688441101d14298204090f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 379286690 1250 379285440 379285457
    0x2091012090c06050d050709150c0c030506041a0a0b10180b030108011d01050c03070c080904020714010b0a0b04120c1e0e090706021f0219030b01020d0c020904020402030c1207 77
    0x117402501445420100d41d1820103040c0b03151920b04422100580032407003c00c038620f81d240d400d01804564020186070482d0a0b1034482c1030902c0e041807038203a1443d80140c10540f400c000b80100c040c0d031150000c1040c0c09031410140480d0444110345509403502103003540780314203001141a422210145010b48065000000c4440700300340000003481240f407130b803038075a0304000c10030010311451800c3d2070700145c2c1e0341003502800c0305610344030300c0c0c42c05690f42d440d030810700c041541c5d4240458825290f080300f000600070041d00b031620051103c84005405a652401404c000410244000d0506880040c0c00b400c10105119140c00c074422503100500b01e0301c400054000402d11446c040003000c107400a00d01c40050a00a00d84440030751142510182441110140810302d0314100481d011580c000c5080802c01d44480290080903008001c103c40c0c0b107005100307460f1440c46242c000c401008007140c00804008850f41c4540c208000707588024220300001400b0b114045e81d1004105401c5c1c01000140c803035844 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 379287940 1250 379286690 379286707
    0xc030b040b0f0d08031b070503090901060f1d01020f0f0a05010b1f0c060b04050405061801020a0509090601020a05070b0702010e18060906040219090f06020102091012090c0605 77
    0x40c0c81900c05030920607251a60300b000c80799070b411140d241c4039074000c142c01d0701d0380c1c0d43e060341000200c0105034a001504000607030b8010002c02000906d071451040301d0852290f40c8a0900310781e00c40f054420500410b10103944c1c034400c504060202e116000051040705c58aa000001c03d50400c4100301800942c0d500081d59001004000c0c0189900c0380c4003540c9458a841204400d03141c90001c0030465400d06c0b0f40804e001007440341135080301c2d451983c0034009010505191800d90b503250000c459240a44007513280129a85e48103000311041d2561503071b04c03507050058107010006e0900014103034506505c03842c1c40c9040011000d1046400404803080300e00e03114071141c0005800507028641c401d02c540c8105050b10900d0024001c01038001c4025034007509596940404140244a0710074840c0841c45a1400c280c50290300092102c10b80d07a05a05110700136030387d0350b0203900b83e0056000d1140e0103152141c21050040c403682860740081d500042c0070514100d50780702c0c0840d01070260040c50000e8000502e120 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 379289190 1250 379287940 379287949
    0xa0b0f030f06101e14030a02060f0a091a0d0506120604120206090a0308040816150b1801030209040b070207150305071704080a05161e0312050f0a0f0f0c030b 69
    0x80041503007804841c40050301c07000d070558038142170042c0307000c0ea40c40600a00c0d40f41c60030040015042d5001d403007103540d00d1406441c550b41c0d4104130b0410700047e000410128540350000030381740708180e5001c042c50901000130044000792800400c0103400035400a050550704400f0801203000e6401450b90030b00903005104001d050190080401c040c070303800b1600c008002640010707501da1080e0010788d0540c4484103154251455143c064001d4692803c01c11104c22969096102441d0004c04844541d605410301c41a1981c1000034031020358400c08000024002c00ca001e05690351002461064a08550b04c405080c0272100d017082e45131f4000b99070b44d000c01c0085a080b0071120b403001011020041c0f903240c9a81ea5019600c40c026540c0100040031030036046586820b154402c015611065000300359203406a01200c4000307001f411340008000c2e19412204190a12600b40100510241e2640a84d41c02d49000086c00c0c1030702c500c0308940d40e104000d094058440c42862001c00090f078010440180440410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 379290440 1250 379289190 379289221
    0xb040f021002030c070e090a02040606050306010315080c04050702030f1809060607050c060f0d290603010605041e03120c0203060903251e15110a02060a0b0f030f06 72
    0x141950f1080110071090840020500c0496907400e00d07503541540d03200150390510003801402034110381041008128030703400c100914804c0d0320a82e01040340065220f0b040f06898254840c0c1c03500ca80140c00c0b40420f5043c16003000e640714811340112850036205200d80e6196600c288180d01180d00c141050010a182c0400c8894114800700c409500301780e101d0b160b480d00c3d401c1e90409544124800a004481900802d080d0360340710403440800c000140d030300400c440020615070042c101d032242e4228901c100d850002c0a0345e058030000e544182c03c007403c10350190410809000706440ca003001400000018640b0f81200d18844a03d40d15610640c2d168410316161074000b80c00c0e08413a4206020101d03d4802c503007004841c2c0f003610503141002e4591382c20316201780d00d5541601c80782200605a041c09008200c14031011000c10310b4030401858240e070302d0031900d6000d50704032880140c10040100b903501c803083d001982203110040c2031a0150501d0000030b1320348042c0104500441d000881000062040526503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 379291690 1250 379290440 379290469
    0x402090c03041a2205030301090e0a05030a032a030c0206090d0c0803040f0519050d03050705040306022115190305070e040314030a0914120d180b040f02 67
    0x1190440c1019550041c0c8065a01c54030404495401d00140e040801d2061a42d44d240280560ba040c450040c1811900ca90090080141c01c83c200410610f2482001a404400343c0e00000a14180500c200044000d4400080111800450354040c00041e628040c60000052480c3c0c600003507a414000c4041c0c00c0040007441c00c0358503041501405075294001035504103055100801c0f55603580e42e842e05041030b5411840140141c0b0030b82c0c00c840c003022290b079001040c040c02903048030301d4403c01c60713811401e03035408840c1c0c1000200140030402c00903105402401c00c0251b024001500402c440c0340421030080d0859000002c400240550302e454100410702c0da28503020b0820740860b280c110307160f40d0b5640300d15100d9803c032450b14000043c1818810b04c0001c01c40a01c900d4010781c1d80c02c2a50610019007601035003580c4204100000f2000c0c81800078001201d001c0440070142041511006070b80102000090018004202c011800000f000c0c400c41034400c81c8680240c0c80c6401c5503005000030754801142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 379292940 1250 379291690 379291711
    0x270c090e0a060f0909140f060403320708070213050709091b050a02100603030e0109080c0d0303110c0a20030a03052710020d0e0402130506031e0a05040209 68
    0x8091158410003002041940c030b6840010a4080d01882c024032400800781c5060440d002d64042000b814002044035805240030b5900c5045507000381c400043c4880841d201c2f81540111050110700311140100030b0602940500701c0c0605080c8640c01050303203500c0d0940d0310300d80240c1c1c40c000c00c110390350050400b0028226901040204c5210b08070540d420b001c2d60b000d11010711002180c07480a151007001860900410740006002c80d6689140280001d0454003886020400e0f0a0b4080b0310303450001464041c5800003032003207400002a48003a4024880303111010310b1007008006140003c841040000f0307400340310b00b81000000c0d20710103820640c65040360b43d141c4240c0050f85a480400c0e03118095034600c64010100085000101e01d10f004020403000407290404c00070b840d1004d80301d40106d00c01d42504082d440b1004103d90110800040748130740c10a03811031641f56001840340d42081e102859000004e0042e05510040c01c0600e03076460701084a500300115107840811007107040c080a400c0c5c01015114 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 379294190 1250 379292940 379292951
    0x601090c080a0f0222030510090308070c1704080304080f0705060a051c0e010c180602070603021c0501080a1713050d0c0911041a13270c090e0a 63
    0x2000189888000b07400400b00c0e648505140300340e00703c90780c116081c402200112440203100003d904c95840c095200548090145070302080c41103c1e5030244c05282907060341e90300182e90b40c40e41c042d52030044000c4141c9100ba40404c0481001507000c0080002d410640c0095491318500702da40c6207072131807540c2c1e40e941503040450100900c0e02e84800703843e44130720b541c10300580b1528159811183c1c07078102d90251701c4039810004010705428041d44620300c46a11540d0710280c52120800d01003090880b4800c180050344521030410050344203a014011281001294084104080810038107440e400c0e08049569040200e04108000290050602c0207001e00009402e1407490401c0c00c80b16006845110b02034888520903034200b10322101400080c0c1158007007045100385002c07210000790001c0c0076a10003075104001c20912581d00d41c042d14502054a5400c001440c24012601c0303604c481581e0381e240d402510a412160711259004076462070940b81d54410089140611402500d540902056003a500d0701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 379295440 1250 379294190 379294211
    0x7090e0601241b02040c12200a0e0a0510080709080111070311030d0908180307030209040f0203240f070507020a030b07021207060501060f05120708040309050402030f09060109 77
    0x10700c03058412002c509001200d0051450a8510442800d800035441850039902c4400c50b40c0080c5046500c5050090411103030350b48500180217001c04140c030108002e02170102140e0303e403180400307403407100002d040242181d9440b4045919150040128004620a80104800260f10408010060003000001c3c03251100c00079160200380314882000e4100080e00c034400c8141907041080b00c46200b040301e8208000056800c00d04030b035130001d0855604190100411410600d030001d01c1c0820790703800400031001c6859558801c0da600d0f100000c1240c00d40960085441e080050f81340e0b618203000e40c04424074540c0380201c2d0700e001c1d48000070052414018240030101c056100d03032140c3c1003070b20750002094050361030707240f0280d03d4060031607c4510303040d400103003c03000c1001c7c50b0801812211070f5240d420544055801c162950701a60001482c4035188000281c2410310800e11030381c000c0e0203402d04010040d100c0c030106050345c0c0200d40b00d15803420110244121042c0c100801401040388001c204442c880030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 379296690 1250 379295440 379295489
    0x20312010e06010c081306020d0302090102070e090c0d20010309050a0b0907120c0e09030301030f0f02040b090403020a05070605090a090f0e010c080a1a0a061b020307090e0601 77
    0x6000701c4111091039400508941d001d038000341d40316500110095114440100b00d9a0025102e0040d040180102040d94200601034000d403100080140c0191501c1d60800765450800440100540c056104098a56607107465041820000a01076096602500031b607291101d4506041c00060b81010305c2c001340c04000c900c01241200145600c400b21110365203800f072940b89000010703001003141078407a0b00354008120066a9507130840742418100c9480d555204031040d202e010034480900f036100d00244000010356011608014070f40b0003480081c0705481800031410f883c000b01d60850141c0d10404100c41403042c101301c19001498645045880c0c02d4503940480c100c0c0d48030344180c0d10042d44403501000190740c617800c0300300040403200007000ba000100c4402040c0c0902903904181c13540c42c1a11710000200620481d40745500702425480d501c0d0300e07100382105c40f08145d40741a000d5400c2061803600582c0d0500086c0300408110340080f4207240a404051708000701039202420842c1c1410f10040f01681 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 379297940 1250 379296690 379296727
    0x203012c010f0612060e010b07051e030415050c03040905190c02030a050a0e0d030512090703030203070f020120010501090e03161209080105100e060f090604110c010e0309030105070203 81
    0x785442d10305600d42e88041d000001d17040356085850750507603131000840c4030802c04001c1d00d072540c0140d048803a10b0410701d0840072003c800318040c9039140c20801007409520f1011308501034844462800600c0c2517448002039003107401c19005410010307210030902c03094951112030030100c0100c425040241c0c44444501135500e11130708a0010030311a001c5166a1118007810f280d4001c401c01504524048002d0300d401416944030754403c01e4042040000301d440ca1000040311401e80c1d43c5a002035282488584805183d4285544102d04010300e42000d242000607440c0c3d10360a480300d000002c54154100920901600e114403184039103a482400f54603d541031404003001c000da00602d03041043c9281550884e140912a08203010a42c00e080a10884050907404841100c420240240d0302d40c590070100b0201c40500300034a51311250300c60104000b881e1139801480c03182040e5844615001d0140f440c1400c0d00c42c00c0c61414007503000460350500714202030080541c4a10b0a101451502184002e40c0c010b029 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 379299190 1250 379297940 379297949
    0x26010302120a06090602190f02030405150405030d020705100c0b0604050408070803090a0204050c09281203020304050306010501140a0516080d09020f011d0d02040204090203012c010f 80
    0x5241c0400ca040c0306005200d1900129044281401041414105103000e503103c0020880d8006a00340d50181081c4140d04441d48509190b01a600d058682401c00c209020505c40b131100c08901000001140c0d6000c00002c00d9075119a0054a200d510317110070000d20400a010000c28000d40d0300f0b440f00050360502a451784400216000510f41d01e032418015280e000e0400e009011400c00803c2c401030720350008241010502c219018810b950f82c1104e540d040307010303000b80300c2c0c0c01c80341c041c200050b41c6105030300c407031660100c0703032100321200381d03110312206031060940d80c20380250304000f800740024103092004d18098134081c00c2c04036211051250140c00c5101e0a010703002042030100304028646d565004040400341c00418a94940d00c051410100030f0407a40412880f0b400c88d040c0859081d4002d450034140c880b000030207102c8000103e030604c154030303a84101c01c136030150b420000824444500d1014601030805c034048580079100d070b0320320001d210b04403107800550308078208010032503002210324031001d85 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 379300440 1250 379299190 379299199
    0x60512061b04270b090f0a0609140a0203040201140a180504020408070605131806150305040305031315020406080619030206040306090201030e01140916030c1a130b03060126010302 79
    0x400d01089035008144000404d40d0000c003010a0105034081901c10500071020b1040812030300e1355410310700d011240c0b02c408045c450160309000540c0007030550f01450744a80181800c078141c800050400c0080d51000350880040b420301400f051441030071108c0c0c03901408041d1003c40c905420040290b9681141e4490386082250000300e180740c0d8688022030344018403917181d44408103c41908100050200341c0a032882e4400c02d81d58140440d4842d0107103a004a80580325540743d51101d0b000804480c03002001580c00da6000ba500f1054032420344000c0c1b00600d910742e240c06071424640d0400030f500f80c001e46a03441c4900750f03800510260b56072000311390450382d00c05000582e44c50380e807006901401540100c0c021651030101c004042c1e800d40107030035100e800341d030341500d100410f0003051a407402000d00020f080505105414070400850340d08845104100c003850070308241080f4001400c00311181c100b02d1010b40040107004655030008546100d00c3c40310b43c2480000a400c10307440340041e5051001a104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 379301690 1250 379300440 379300499
    0x10e0a090e100f0c0314040b04150605180a050c042304091a0709090e0319020a1e2907030b211b09040b0109090501060512061b04 57
    0x1510010084115070b8110752100780121080700d5882001880d009808402190802040403901851611034500c034a174460030230b203000d0300d0b10f880f1034002021013440440c03000d607144004600b582d5038429980e03500321025505081c603d0585028002d58002822103007042c1002d11040c481d525540695140d03140307000c20312208070004400080c02910302c404e03000d460702d004010405196114150441c4c4242c02e140c5510128036500c0981104990b440f240944040c0c01c244002d8510042e81506020207001d148111041402191a601c48c4514511070514100c8921300e10502000305803c040c13000b050340c2440840100308200d003852003401008100104040d035602d080e42e40c036910031000000c882040304481450200c0f0300102507556180245492440e12200348101c0d035490030101c03d81c0310b2035200500e0340059290694800203401c56000840f41552140da000c00c0c0b85d22141c0020f00e074071500a0081070340e810b00d00d0003030301460752000d940d4454650400c401c0c48001d200c02c103001d1302a02c50070a100c19 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 379302940 1250 379301690 379301711
    0x904060203040f080d020c06010e010b0d050a0207170d180309050409050f070b0406030f06080c010c0602040324050601030e0c12150705030403180807060c05030c070e15010e0a09 78
    0x100c0e1014003c0180101c0f001300e180b01003040198042d03c03203401d05c0e0742112000c0c0d89031411802024002d1181c60040d0100300000e510300c2d145134211075040090560f002d1b0a02c9105c0da1242c5808034210362170a0910b1000c28440440c010324040c1d13800100e50300542e44801d0b001c50314000c1004000340909d03401a92a803103001c040040800041d040e5640a00580302c4c0c0c5a1245081c840035032091041d400040c0c100403900384280e060380310b8071040314609002422050003100040d160320900d0314003610071503402d02000000c5001d040090549100749800e10b0386c11b05000301e1b42c0c02250305c040c1960303041501d0b0500c1540124000241007000020888481c0b0510040f074846901d0f041420414400300140c010073300080703680041c040c60069109494075483e800d50110001c9c03e05001b4400c020351544501001c22070940220901b154260182054070719140040c400c10b8038101c1194000040c0040c650204660350704206542c040c2c43d1000d01e01100f4510b49400054580e010324000d8516403603807200d00c02d9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 379304190 1250 379302940 379302953
    0x90114090112020c0a2a08071211130207050a030f030e060f0c07080705070608090303070203030109050a02160b070306050301020703090e06030106081203040210031b0e01120212060f010e090406020304 88
    0x100c12035030005041086c2000101e40b084020050390b40861a0900c000011510680c0032820030140d44240b00054522004c40d15525110301400c140c1b6504813520413241e01415980e40001c18295014000501a4070101e03d002800c1d80d154041e0703a0109850181c0880c41500e02042d5030b40c00c126a03010010580d203452034501d6080c070a400d00208099000103c0380c00700302c00400c4480407140710751250700c40f43d6210802149c0320f1008443c0703080103800401c014400a415030b8001600400c80c000d0043c140b80c5007900b81c00860040100945101090908120320f4070307458058203016100503002581442e880b5038000d8041c0549006400889105400041d2140c40950114000381403c42c00c9440c2c0501c0310403550681d62082e07a09a0040815142d000079290181c042c003074040102c220701c22148080050110b03034040c240c040c10343c100700a2615100c103020b0b20340054800816501c00511090070a07004001c20301440b0042079060181480d0002201c0e07548400c126400b035000340c00540c0d2580d0354513000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 379305440 1250 379304190 379304203
    0x60f09150c040f0815070804020904030f02100f0b03010e12070308041406070503070f081506030a0e072309040209010b130803040b03060306090c0306073002090114090112020c 77
    0x240c01100003000050819070020714902815100005c06803243c45d480130840b079124046074080c3d000342200020400207845480221664060381c41690b03d02003541c41418295803222210504e0703140c441c21154000d00d020710030a2a0601300500072b12510094094601c51402880c0018003030200100c0041d00b0b00c5641c0208900c00c0510707205580b41403806040142040d0000c2e211a0009880d203c43c80241901640f5030b40e006200d80c072004000a00e85200304003182c2d0009148036007054039095400c17043d9104001d411301506082d4840d280c18803c089290894032086c141881c0b04410080034440903071107400d84039054907543d900f010b944000340d900001d4041c500703a2000c00b00e40f00014000070003801c0c0801560094a00320262000341c0c4902c00f8031660f07010b94102d80c9a05030440f002166240e400744020880584440040e0002c11142c000c60003089040a0102103000750000313078084041d86d00c480044102854414128142082c0100003054030140e80710902c0115800038109800b85810041c9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 379306690 1250 379305440 379305449
    0x20723060d0204230a1203020102091807020f0102032e150804020109080f0d1107030614010312021209010c02130f1505030307050a0809041b11060f09150c04 69
    0x665110581c8840308000d50151090004120000d06184c2c40f0300400d03201c103a800c003802070840c0b80d8a8141201051042c00740803007101135660030803001c1d02540f52504400076046160305500c1e600e19210030040d083c880c21700c0310420390b070344100200841c07029001f02c030300039074a0700c60a041041c401003501440c844685d42c0080d000b82103010f54800c000d60384040103d21442c401c0c2e840d85c0b080c554a00ca07007650b8401c400c580380016040512640d96452041c0d00890200c45503008035003d86960381c4070002100c42c40c1d01145000951440180300b48510180c80c4901c0002520007443ca1130209146c080c10b80c0240c0e0540b504018084a0682c190340d903951034203080c0342c680d95040000c610209103440041002d20803641040140400c00512442e0101c242c80c1c07845c1d00300001d4068121319558030941980b00141003039000d40e54501e43d003854074202490032130010781764656020080442e20111315041c4002e001c03202c18004941048030806012a44031415160100303000d45584401062079a103001d00d801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 379307940 1250 379306690 379306699
    0x19020f03030f06010f030207020310090201050d0e150f07080403080c0f03090a0c1a040504020318010507021e071212021e010b130507080402151207030e0d0f020723 72
    0x18840d00103075151650703000740d009880340e0685c004040e0098003a8021224060b505400c180c00344c48501300075401c40e002e46d0f80b05150080c0380c45a40a4500100c0d1003a0321a4010781d4800c01c801541d5490025503182c2101c101d0100140314070b001d03200204070060050004003001018408210491000b6055840d0078101407811901e1b403818903809a540e1241442c00c4d102c02c111400c000501c0200c00004111102012100c185003e0a02041c400a548054452440c40d4081c0d90340e990090403e2282300c0c06482c0c540d01804c451a5400c40401b03000001025409030ba07044100100311b1203141c072001e086400c1d07022104c180c0c01104084240e0404c445110241905089031400e12040d10041d40038284c4548202d48800d0000c240084d4001198001ca4041001c90300a001060140c5030003600d802c1e40f00f403401401d5280c0101a601c5803542081580e0b0000444c1d110060100240800c0c0080d401c83d02080c5400b819035683c658000f56610700603c10100a44001c003030004c039201c1c1e618191015882e0240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 379309190 1250 379307940 379307947
    0x11280b100e0621030414010210050108070512190602070b010b0901080613231920130b07061d0114150114040f0303030c21020313020d0f05010609020a0519020f03 71
    0x1444c1d40c0d1030b0741851b04028010701881c076a800e42401c0f07a10505040c1c84441d00100316584c00c2c4024003c100b144c240301c6003003520601c0d000c07503280780706000ea4060aa03c158400350b141c009500c2d19210742c280603000240c2c0d220003031000c011566441258503a100100f143d80e82019800440030100810110201070b143c3d40d020942e07041c18003c1c041e41c0307a02900c02019500310504070f18140c40f04886a40c441c50885800f4020b9608032059124050007207450181d1840740020758548403001c0e03a503c100b00c215209910341c00300202e803210b800c0c11a40041310340d00c02032026060400c1c1c50070f42584000c02000c01c2407011482c1c02c2082c3d02c9011100441030440104542d103d446c5c41244444901c0d0b80300486c0001e0402103421072480c82480942144680203c1c40009a858091250007a400007001d0f0070b404c0720074105110140e0f48038006da00120340a100c071480040c84608000b070039030300c050700280082030042180b03055031903002c412a24003941507000201d00c1d210720b802c200c0c18414404490300c864030022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 379310440 1250 379309190 379309199
    0xa050f030f0103023307081c0c091205060f0421020a0203100603080301030f0302010b041a03150709030809060409090b150d02060a11280b100e06210304 67
    0x300802d05982c02114421401e22402d8a880d911540800f4000c0172440030b021281d007101070307400160004502c52500a82060180005071121103004c40d4800051504c41019146958000500c0c10142200610400090b10748d034607801d40d1150040c00c504501c01c0d03480c00040c14843c0c1d030100000740c0b408a03182e0803085d00c104c0c00002d6a41c21031900c10b900c24000c0d10390a4150300000e10600013140d502204050541e0b1858071240602204102c0a800795500c43c414500103645600c035895901915a00c61250f05c070607801850314161020b400401c0600103001030089094125500000710799006913842d50741c045081c00701e09140195403102c0045421300740e1b00c8007000541140b86100b9043c61810304198004141000410004010044c9d00102c08110840905105840707100071403907488120f5810b8180d40c03890011003c040009040360780c0c1480910000c208410740815009003122034420542410a940301c00e081d90040c01a512403040c4008000303817807502c185030140d0350446030241d82d100c0755103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 379311690 1250 379310440 379310461
    0x52202031009060b030f1f090513141203150102012007050d0302030114012604030f0207060305190b0d08040b040f05060a0c0b1b1c0612050a03050a050f03 68
    0x16010320010076051800100340d48001ca4217891042c01e0f010011400c03500c621130400c01900d05d031821201024448200465100c9190103010b00984100b050440000c1807400c05441d803100e070400185658010a03c813104480300c200c03d5075001588019201a0300942c840140e0061812031010030222454511540040785142c1c0075082603030080c802d8408800c0c40e880308030704902c003d00454070039108252209242e94842c000001100060055000c00b0408110005044e980100c034120006a07a51403804003442e4140040d07401400642070522583c20001ca00030291802c449040130301c0f555510000300d080c0d440c008605092a003042d202542d0781d131507018140e02e56010340940018580308000014917410107004039419604a50f40e81c5c512000f680d6954401031030040c00005041460060006d41c0740480c0d8010200d405604038101101801c843c0e5807000d0364041d502c07210010f203201500c0c1002c00c01c0851002c0e051541454200da40300410001611140201108651810804010454621003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 379312940 1250 379311690 379311721
    0x12030a091407050f060703121503051b0f19030611160503040905010b070b040f030e030d080105030106080a080708280c0201081b040506091c0c0611060f0105220203 72
    0xf003d4540e242c003405040d003441120300c52001d00400040b40d09810010100082c3c3c010140e240107030142d000100d9407030701c40610f042604800244d0140e510040c1c0d5005180100c3c5110300c12206550004002404040c49840100700e4440900820744032082e5180c0100c0c40b034116245441c07540003240020b0070b03a003810303a540c0d04a40580340c5481d10344000411840354100644220070340c4002c00c0c1e90142d8950741e9210301540b00d610110144100c00215100a5909000c88050007070701d03694142d29585010101401d59140d58440e94058200c81c1140c400b00390300e20101c4403083e801868807990b5035040000d58060350030003401810715100c60382008185c10303401602188a54001d90f1404042d4981101c03140c03003100302044148414208000c10402820000003171302a0b0a8020041c09182d10a400044913804d1101da084411803c0c00b101401180d030414092003c8890350f034018256854080d100075a00d00c01030040c548200000e98120f012801000d500003030b00400e1140c19510390400040240e4280b0703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 379314190 1250 379312940 379312949
    0x6011203030e1c09081516030b0103090b0109020909060d03141e070305040e0f0105030705010e0102030f0c062a031b160b0106140f070219150203030414010e12030a091407 75
    0x42c1460201c0f10306c106070711280c003c1c1908a10300181c1060100142e0061242010b52414546c4910002c408500004200c078003d105120000d03907240a82e10400c064000002c000e10711a00081c000200801e0784002d2000161000c521401d64501041d010164040c41e842c1c000c0d10501000100f1000309503220001c0d00c112041201d407a08140c4910314032940f010002d005054043d88880002c000e207600c100d03a45e03158800c060050741e02c4c03c208080044c2c041c0c0d2140c030042c3c030142d129109100f08005599075403140c1614200d019240710a00c081c20200620003c0c0600d80711042d030b0000090000c0072003013220b0100341841501048004145480e01c00b80c0401d01c07400001c40c0400408500e85d402e5a4110b4112001c00f8856501e042550f40c00c0224218040c0105200c84641107400704000314003402554901e019038006545a15141c0380520380360941d01141551a41030241071881d6080009504864058009009031070740d5034000c043d0300604195102420020050200d42903a100200322a0300b9036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 379315440 1250 379314190 379314193
    0x90c010905040b03060601051b011a1914060d060b0d06060f0e060f46091d06030321061c0b2a030108030d060806011203030e1c0908 58
    0x203a94840402007151008030046400d030b00060001100c40d80300318000d08944004c00c8580f103074060081804c41c00c480303421854103d440c0d031480e4141c445e4034003040091000040b0504400c161404c0c21280c140d403030040c603601409004089121400210300f60070903005094544191519828001d0350300d00540000e214200100f115130325441081031007414460b04411003c0c03c080e00d0078541912195040d4000741410805001507620112403101c1a02c1e9180b440d150749401400e0385034809040d003401e0010300c01140900c6143c1d03404001c0c02d0145251014042094000d035120b640c2c030000864154480e1422008004c10000b841d1081240b030380450303038050b8809964546081e201e5204400c03c121a100002e4140d84000c000612000700e481141f1842c1030112960008000e1501e13a048115042070b0001138a50304049500c09081c51548110001818810001d041551500322507480c40149010050708241c0c070346000400c04a01088044000c684014204100d50f4400314014a4004a40a100001e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 379316546 1106 379315440 379315457
    0x1051809010605180703110a0e011b06061d090a0c030b1906030b0109150312050d060803030a050105090705090a150c0b07020606030d0201150506070c030b090c01 71
    0x5084901e4a01500d17400c1c000f1015007905c0106001e10340e041d60610440f030000c2d0f400543c2403c0c8000a00b003019000c440081a0804030401c031314007a00ea1b90034090300140d62a4038007402c100707100040c4001251612a20a443d4861040d00006003960050160520106580c900b00d0b9810809420a582c43c8040029025069960951094915007a4200104643c801a0143c01000c503106464800114150b60b9101251217280701c070750003003110104a1044894165214401502010702220344a20344040e103e80944400d000d40c1d40504546004280031074000c3c1c05941114000a104101c5542460010305031200344660000070011540d10740c002050901445a0181d00c03550f01a00a600d005000e140c03400e404140183c0c04c6a2520f10742400d00280305402805540045403090360369661414400c0c40c3d03880c4c40c3c0001c0c003800d02d040c0603c0502c6c0360000e15112400000e0326503240 = true := by decide +kernel

theorem cover : BRFrame.Cov 379136690 379316546 := by
  have h0 := BRFrame.cov_init 379136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 379136690 ≤ n) (h2 : n < 379316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
