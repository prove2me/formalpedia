-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1725
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:26:36.785977+00:00
-- url     : https://prove2.me/submissions/234730df-7b29-4834-99e2-d5e4013abe2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 310071942 ≤ n < 310251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 310073192 1250 310071942 310071977
    0x6181f0c14012a05040f030b0109051e0f10120b04050c061e0a020a0c170601150807030b0f0301020a0509030706050c0604030309061b0807080c130501051e0a 69
    0x18207803085120080041c070462004408510043c030455140c0000420380d5540079900500c00c031001740ca21080800e11480d580e207401c1c1022a024080c035030509082601080c3d10100d40d07103091110101468082c0100e03940d0716905149034200030008283c4d40144d4000003400101000c00018032b90080046030060314083c1000d84c50400d210f1009405401d040110103001e907945400714800081100c42180e807003d441e4800c91800708a13640140c07000741665000240c82c002c039040c1d1090b91a904050360a142ea85030071403580807540510240115800a0010302082e10030303408403a00d46030042c0007400000a140110307003240c0102c48003201003080003910004520341044a44000e01207850300600d04415030704400d840b00c0740588001c06068940300c8040c10000c0a80000288910500d00100000030902000f4400d100940c0c0c10000b091981012461803c3c51303e0031144800b8448a00c41505031400c00115920762145070074164110005500540040c01c0100501c02d150382551869201d40120045 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 310074442 1250 310073192 310073213
    0x82e020d05060a2123010c0207090b03030301051807020a140c0f0603130b0711100b041406030316080906070c0501022407050703021509011505040b06181f0c 69
    0x2055941a0902c4c10045000400c82401440b0b9115104c00744002580b0205a00c0d84100c92000116500703044007401c43d20f60000d4a84d04a518607a8107000f2000d042043c1500c901c020f008998001202d00030b60807041140d4462507401c44180e104450040308035807a038900b4488109290000d40e0040b0001142034605020b10200c4108111145842e50408a500319018031416a0003481900070301c0000741d006003d090230709085c1c0f1060040e601c1c680c405444010080c07071000b0f4000e01c16887c041071000106108650300e4400c0c3c0c0043d0007580b07001c1d2245030504007000d0341d41040320600000c00c10800552602c20207000464403d03240130800c43c0c140303800a400c205598600e41400021000c490b04030048059805030030070704a013061591a0b5060500300c0c01c000710000c80001205410040c840c2c213a5056109030200100e019000c105c0b641c03600200310a59902810059014105100c08074400b240c020228801010081c401440100320441d64280d4580050303030b010100c0c880030280c10234011068034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 310075692 1250 310074442 310074449
    0x131103010518010c030e0a1e080313030906020133050604030602070519150c050c060702060708070504050d06050a020c070b0d05060d02010f0f120f0e16082e020d05060a 74
    0x1c0c00c1c80716142d48102541d0b152000c50f000303070416200203480c6402d00c02c80110000c0d809c1d041513100742d4174a0145618400b01a102008500003401c3c0540003405030b1040c4074128034502e114540c40d40842c1d0307000d000c054004600481e40c1139080040c0e400070300ca0b83e4900c0140010b5214540140e122519810714604008407203030010280713005000c0400000741101c828090b035417030201c00068869401e0783c0c116440d000b081490a118810b05083c0450281c000407070f207109031308a5035210680e035100c031012640782c001e911407142c00c000c40e002841c0010761590860307a070081e140003006040c459041041450302c00240d1104200260020f04a0040d285074003405ea072100007942c803003420550b11350000341000b0000441004000003c05540140c1d441000144409610764105106102101e0f01400040140440150481c482c40c900d03514103071500c2d541c1104481c2c0760409020950803140c10001d20820740510807000d40e9030385102c42000714461003d042c500310409000100c9140420038030842480b20781 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 310076942 1250 310075692 310075697
    0x90b04050603280501020d0c02060907080d120e0313060503010618030b0a05090109020907211103010e09010e0d21151a04050a1202090a05010b03131103010518010c 72
    0x483c0081c80c120680446803003840304402500f568014200030380240540004541ca60303082c015040d030b880c2e038005221400f032136039041a50030f01542c60301043d50b07401c1030b4034040f00814056100141194071a03030010142680100540c1d06c1c11091444030079054405401410125401000501c074030303035220405c04848185d059000385228250f88429641c1500140380780341060f2150006602d41030290031005080b039025104482a050858000c1d00301e440c2845230308010700c030307108800502021a0050b81c1c6400f40e0b2540700c81c6140d003029580c000e4081c008024074002d40d01d812902c5102d02c410030034030f90b041485960381580f04140c0c43c038400d001c1d2030210200305e1b0f01d400d1007404502601d040c420041120540b0413103242d0304103150326011b881e003c0d980c01194055101c01d000250910308100708580346100310380305665039a80d40c020b9011207030203014102d40c0600610000e081c00ca00d04d1484100e05d401001e4440200d61321100082c2903902c1140e0f030588104100a8003900d4140901400300584401d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 310078192 1250 310076942 310076953
    0xa031202030304170f16030c1a1501171f150f08060f10030203130503070506071403040309050d030302120a0603051b1509180106050307081e06041a0a090b04050603 72
    0x40c2c020107460091b99045688162908001d0040502820402d1b180c187d104154102503c003a41c642046080304449400161082c04501080c544c0300b16881c00745081c1e40030302d40c00c60b925000c1018151031418040000c441d5411000070800207101c11132085000750a641e81d80c11015103420003000080c014100e1405030f00039800b542413595410900d81c09414182c0340c0180c4a980c0c00302e0b61205010074520240c8103000000d121401e100d00400c4480c41403250340c5502c88100065804403400c0d102c11035010380050030b038130001c1c40319150003200911718034080d103809420a02152100b0030110300c04e039607000c0d10700c0c3d41e02010030800400b03219141c0c450311420501d003030000c0600c0100343d002407d002d4100b91110005521002c65a5607110f4115604404c0402501981c4403540500103500036078190004c6032600e000507507404640002c00e445204c4070030003070ba02911400e044c440a00b000d610400940d243c0341700031001079254808418018150010046111030921041c0401c4560240a950094004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 310079442 1250 310078192 310078207
    0x705040c050a0206041101020304051002060619080706050c0a080d0912080c090f0d0609231b100306033306080322050d0819090806060f0a03120203030417 68
    0x118031258401c0d0046c0c0c0f46005140e15100403400c0d40f04940019600074090619001c6c07540d4009483d0303124034010303500120403078440d045c609010090b0f446030b000c1c2503101c103805025840c8640050b106406d520401c0344c00914140e5550301032500022182207441e80e455203004103008804403181c030303007201c282020582400d100c0c485110360b03c40c46040a0048405642e50181d617110101201c4202d5000501040a9686454403c040312491040c0040301c1c80007000231312400704080350f00d144540d010f00490141100010038060fa02000c01e11200901d07640d60000004a40415802c4450700800303030780010300b080040c503d0a0500320070030b05200024a4507505000e0080008101c89200f070004034640b0140441400e8080d04e0400c07500f041d030b00040c40c09400d0041007451000750101226190744080025558a411195a152449110526800356001c10b100d401c1441d0700140c02403020f010522010744039100d0b654107405094400005030710000030001400703040304400700103a00000d0214a080c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 310080692 1250 310079442 310079447
    0xd0b1e0709050409110603040302060613020427090c1502100203220f050f0703111f03180f08030a05060a0308030a0f2705070504090b0a0b041d0705040c050a 69
    0x64038090340b0b02407130740e074080a03061017034220010310b11502c01803c040d42c9107018a00291100c034292003080c014010558a442c0d9a400350003620162480d21840a2008682007000b040c01650140300c2c0140543d2444401d011076070180807203010f0300d0111298414844c641d08000c0c60880210b0311001c0711031060003070101c040ca401d2062a00c4000e0001c07a10784a203164240341d50342c4241a4401401c911458080810415010680c2e204032401010303442c078440d04c0c007800e000f40c142d1850001200d00e00c4035a05168a240a5072260b010b40381c1010758102c0010342960b408e110551024003d9400e40e0002c4204200700590380212a0310480075140703841154a0340e501c0d141d4030b010107404525034644804030b01401114980c003807403200540c0704a071241e03284104804c107242c50004070240c910380507520b0040b6250801d4020403004691100940500c0d58402c100c0310010203202c030000703030b0040e02c55070590840c8140d06a05409070b0740c6440a42107c51a042c100004c175601c050380041488424401e4404403034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 310081942 1250 310080692 310080707
    0x130614040e281101080103050618030405030f0102041403070b0703030b06090a1d0f07021009060209030a0c0e071d0105031503100207031107051507030306050d0b1e07 73
    0xda4012802468810600c0d06240a00b5425410703040d4030254000b15600c900c01400503140112940007a000d98100112a484000d000281141d80040007141c4844c0c8003680c0d1569038200001030b2400c040d00c4e8400a0b08240c07803c40c5140051390081002d00001005007403050590030114010098185000341d00b120300c0c050320a0140500da907809000c0c2880e02c6001c122010100010041e20302c65171a40c904c0c42502035400b220442c00081a40014451082c07503010300d00034101ea4008044026401e46114041c0200030401c6034190307001c1c4540c10701034030204500380744544907075818120319081203c0ca841c2c00074010300c030404105940701c10a448002d0b070040b1003000e0100b8604650380360768480441c1c0500c3c090348151a007600c01c410b00382d4600c0c201903014044d90f502c07954684404284159009544219074083c599222401c48202c0031600300b40001400c1c40c1d4460f05006c034a2640e18000282144031101c0180d13003001d400e00400859442d0071607548000b10682034604150304002a0080c41c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 310083192 1250 310081942 310081979
    0x1207030203250503010501030f1e0b011509090e0d11120a0c0204151403010f06080c06251214071505070302040e09030c0c030625121a1306 61
    0x41c2c40d601c00c0c2075100c00040700040203000050000d02036542d491405c40321034103d01c44155100c0d480881d440202d540008c003a4101c45400014004290342088482c180c00e000002540f02400001d4030000b03410643d50007106101100c80300074001c880003060003d010044121a07149142c0c0010f646141406482025035150080e5840c041d0b14a4406201107401003400d051401008041000c0c00100c0d0402c44a11841d4110190024001000503001d14003d990313a500410740642c011040c0e0051504140d0081d10007191103440c000e03003e11552182e10301c0c1d96a15981030f54810b40041107401c0c1550071189041c140c00102e079419207002c9080d00e911402107040003a4103032868642001c00c00c024800c0e0141c6000e071003403416a41581c200340040507601d50050040560a000f80003501019190105a2910a201002007070044020703590041c1c200b161980045024030940940c0d07030920701e249220795071040d00310030b000004d20000030b0704011108660019110b04a41803802c1448001c0c80c20050b50400d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 310084442 1250 310083192 310083223
    0x5070b0f040e100f0b1305090606130609030b0f060121021e03010503010506120307060b0d140303090609070b0a0c11040e1e01110a081f0b091207030203 67
    0x1140c800c1240c14009114551060b5564040a001d002c0610410324080b0210368902e40304003102507540c2205409070041e43c841d45000300100d00b041000d414019015580000d000f00610f18286440d00c0e0300c440c40405411079400680400802d00405c440c050b48180c10562a0749101024a41003000030680070403400000340803404008400010b5089406880040d0042d0030380c0b40141d0940314204a182e0800d01c64544203600b0000417803c24280100c1100710100702d64051840c0070307159140c1c2e02c06009903160150704401448030b25404111403180d0003000541000195a80741020f4090328039105e005080d0320007680042004010980a140803100b50364607605113000c4940300307801e00c448444c9030b02002c207400c1400e00404c10901100420508840b00300300c0c0e884140808101070f058201c2d17021204850040404018041c50a0f01685070300d40d0001004e04440143d015030356079403480a10325800300e03072034102c085014210b0389094690301200300940070041c606a4a950002696990f078541e05804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 310085692 1250 310084442 310084447
    0xc181303180902130506040303140c101d0d020d02030910091205070e010603020f090603040204021e04050a0501180608100f030302061e040f020603071b060504030908070305070b 78
    0x10180540910101c000c012000001d8403aa80c2200c44003039031000c06039107884e0700c0e080d80101d250714004007928107898250342c610b01c00a1000800c1c079070550040c81e03013103014810030074000c034603894070b0042c01d115070746100001030040c0094510a140c41c10000208055410406514290540c0007003518081c00d4200c60006107201c0b89041030b00c0f6016607420285848a10351003070740500c4000141c0c4021100080011501682d0f5144120221b02a86a40d4182c030070f0704004882803443e01070b0103940c200d070004000601d00042c04846000030401c54502d00a4490042003c020500e803005d10480104400c4c01d0100340b40114400303544c44199030303015141c28060ba9001240080301c1d8441228044d01f40c0b044034203506074507820044d5864000721030000d861142c43c460f10864900343d0043c18042c0d540b01c14034282c2850680e0800115401c0205000104064803003007d5055138002d62014605018001c0010b060810307060040108100d500070524950141800700005903001800301d00701e50341130307070900d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 310086942 1250 310085692 310085731
    0x201020c040203191803020607020f0a0609020105090301021b010b0414061207051005040905101215110403080d0c030c021b06040302040c030b03071e0603021606090f03020c18 77
    0x42c4c05005207191000c25030300e040d400e00e0000c900d01e0300c54081640290200c8095503980c4c5000c9a070f5409485003001550480c1070001c0c00110759805c4007208070300c1410550705001012010030308981107284001c00c00c0c043c036818020035070300070b206542d4094405d44003030101e203c0340010b1059018010f00180e01520880c60f074080071042c00d1149401030080140020014078504500528640007400344d08001898a8040f520781c520200c2000111102c040405540d80503a40b42d84000d9400342c82c0881031315444070301c1c1c0246034601d40001d101552180a1a0751500c41d1041204121480c5001e40c0c414149003209034a007058000421620301400220700031070441c110000310b0910b0040da0f100075041810590300e41030903034040c1c01c20540044103800311115580d43d42450112680280e4808800324003118050000c180319400401601040000b1446090526501c101c1101c0051000780c81f02062901e54404040c1d0600803401d029000301d9406036078550104500d804104040c040010b184140c48108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 310088192 1250 310086942 310086961
    0xa02100b0102030c0a0215070501020f030708010f0317130803130905130c0e040f0803070f0215010308030c09030705060706021e0301030b06100210090b06120609030406180f06020a0b0606070201020c040203 90
    0x88d004c0a900c030000f5515a0030796810046150801e950000108503076100100e4400140d0300c104080b40e402084941c8040c0707000120b1032241e800000c0c17182c1034881489003c10b60f580100000d14020004e0100f07042180e11b8400b910b803c941002e0165416010050200d2003c40c81a0064805483c021281a012600c80b0711340460300201030b00d4001c00660b008003c00510702e4202c1c0c100078404480fa001d4a0004150354216003541a0900004000403000d201103584c51304c009000d40000c0c400034040742c14440d160300c0080e0035a00800001c440103a00090100400c1307003194803940042c0310045440d030665041d40e450100c0070000400e2140a0741c9844a9581084e208000d02d04035480043c2d03042152a0701c1741080c840350301084807900e001b4078000e07251007154500041d081d032064200c88040c5040c01d090840c03c40b06407000031010040350310303800000725107100d400d80128000d0102c0c1d001882640464a08812025001004244550b409108407070150b6000f080d9022a07820442c1c0040c0d503581d901086 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 310089442 1250 310088192 310088197
    0x150606030c0c1519060602030313060510080304031b080a080a0e04060306021303030807020307020306060409080909070302030a050109230a0f0204030f17030610080a09080a02100b0102030c0a0215 86
    0xf6062050144140424681300c0b804a100c40d04008005010342516004103a0380e80c4015a808010f540e200004040800c125038080340d00401900351442909a541ca115031858100381c000b80c0d05612855240c0c0100781d1091703205e000800c0c0c528060304000000e6140c40209002e003841003010f01002d4901c544481e903487d40075001541d4000011902d0300c02d680c11002c111060307030104a000c10a144040307441d990000040c0c80e8800e900a0090829a40300307410702014088009084905644c284884a40c03642e5918019204c4e007015a40180c42c4e281601501050354010781c84001114038008920038180d02da00d82001c004c0700c040300e1140094441c124108010100003440911151002c103020081001051089044900815542013400b5200000309520701c010b6490700c2d448000d0000f0040c05600440040d644030016260005500780103480e049800e60100240c00c00681100c2c40f000f0002206105202d40781000f0300c0118148101c0203112541c1d4002650040c1c4554101d00c131000200289504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 310090692 1250 310089442 310089463
    0x90908090402030109020901090b090609041e0903050c0714100302090d1e060506040203060916030e0a03080f07031b0c0203010912050a110102090a23030717150606030c0c 75
    0x4642c3d0350380d07401a035402504010380c0140010803840e0005012a0b1001c1600c1b80c42c2401000103141402c00703c20000100081c010848035104140c0c0f46c490a1880c40c030503180214029200c499441c5140b003c0c140c2840030300d030000d60350440b6141d881541030310760b44580401c80c44e00d4240182d07a010420f0010708601e8000d40000c010f0550f01e40c031188030f0f40c884244400300368407506080c01962986401c10041c0c4c00210744654010481c900091a140c60800407071103110881d0070001891034002080300c0c101048808160040b800080074800d0042e2150642e40d80441546800c000c0e11070701148800c600031110084000300700205460b0000d40d5429440224419030194443c07a610f400a00003501680145500401040c01c011a80712501c6044c021100d140d44001d02d041001410581d2080d1030903250107200c40702c0850201034180c02c1d241003040c20054440304c40c1d45000360001100d541d240000d0b001c07640540c650500d050001c0c507100c0c542542d8100501c00310044d01d60f907001078144e141c0b0704200c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 310091942 1250 310090692 310090699
    0x11a031311090a0614030604050a06110d1103070e030c030c041e05090f0106050a030b010501050d090204090b04060b04020a0e06030703021312020310141b0d09150e0a05060109090809 80
    0x10912151400f2a48044100c4d003c1d0800b0807603410400c001c01da1030b0302c4111000703003440e000080c1c0c1c04005445a030007801101c07000c003c2c9a00f801c07043c041034070807a0b910b101d200900b01303000401d2040300b54200c07401e900741c140c0880045c2032030000c41c03002c03030b071140319030400d80d0300843d11303514002c1c0342095110840c0400b03d6050000c1005e4076045103156540c08042d214080d1551805c20041484e04020310500241d13904044803c48a901c0c0600443d00e0b90300120788038060503a104208070050743e0b18010108040e000f10ba0348a41410710f800c010003181c041310240c0f0310076481008801009900b10141d010241030407102d45480e699010b04c00d038040d1041d500b05440b904411500404d450611502c8120024000c0d01100c4041880050b540d0440b0390610050364010101000202032510440f0f81ca800c030800c1d007510b075041001410780b0300143d41c0c141501f219030f0350030322280510401c43e911400f41d000c05483c000389160740d4540c48458407480e040c0141c041c0591558600010300a899040310310705207014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 310093192 1250 310091942 310091959
    0x607060f0e0a0f0614040201093510050105010e0315042306100b040e06210723030105070503042003060c09040e2b020a0605010914011a031311 63
    0x3c1c0b6000080019804080740c0d07040c58990030302c40e100c54080c2154805c03030341078480d10b01440c1406414030881a60845540b0490b005901d48991094804a40c03101d940c4400020950025094030740c0c000d5860581105041024031002d01d0640c1e54000b9000703452202482d22980b1649450500010314610450040701e00c0300035691440d0b40b80d800003106442502d5203041201001e4441e0109200c07440b030b07441080045c410400c00b0030703202d140440317008000c3c0720203080c1700c0006100c1c00103150030007c65034040c20040960f5040c020a2800000c190031816004034020003651900e000301400700d0102a0001d8121403842d1044030448400c050543c011310300c020308603041c502e00300c96101c80542c40582c50724001c4e41840400075040700c001600e890b00b80044040100184032040b0507810008621542800318030543c0c96200c041500c0d4841c0602038181c415000c00c507201e40ea83c410b6045541a440b03041d82e640c06281040303445000704143c03078010080e0b21120350034901c10b0a02180700280ca01c080d90f4410000b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 310094442 1250 310093192 310093213
    0x1d0a0905090f0d050f0405041107120203041511060c03060d080708041d04050d0e01020138060f0d0b0d080c0c0316030803040807031e0201020a0801140607060f0e 71
    0x1030000d11081004111003041d4003c0c641156140035036213031020390b00300a210500c8107140a4102c0e05003403240e4260070313040c0b640b2601d9a4030100b21880294016820014061001060303088480c56052000d042c1114800c5103400d0540d511380e0700410400501c0c80102c0460055a40c40725010100c1b40c00c541107030b8031555241060302c000d610510503010803210b44294460341b150b104038801d10841e0032101804c80080940000d403480e07004282401d045545e201e11028030000514070321690f01605100c140c02d0100301d00b43c2d0990181b84441170a04c03900f424048080340f048004122000000c2400000c43c0401007a0007280b000a40540000d1000c0c81c0070401612201f000145c0708400801242200c00f16415003100d9060000207010140800400308006004902610010808144203240080d0480d450308902d842e00280300c480540182d4001408450b80c9030301a1a090140484403101713000c2c80d03120790000c1e4081c0310780b17000284001d84504000b01814034940c0310b4130200c2c0001d000e90307401c5890b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 310095692 1250 310094442 310094461
    0x718150c081912180b060402091207030b060102030f0406050903071802032e0b031f1205010c050310090b040e071805010b1204020118050d0b0106120c1d0a0905 70
    0x2c119104000070920581541c890800d409a420600601c030301c000ca4615090f204c0d111480c40062201b50040c0d02004640c181d5100d03022102c00100c51007018100345400c603d00a9890003002d0104c44c115030084c401c1290303c0e0460b00403502141c243c0d0400355a034030741c902d02090804007164080c0406880e002d404000700c02c0107400451050303e0703d0003502130a401d0b601c505034055001045000f054541d41a091004540c00001582c020349010000ea4060390245004020038105822118200340c4000d009000c200d800d00603000d00601a052403400e6243c4001901410a2148101c0000b1074440c0000409900e1340d038044032000c2100f07005e868203252200d42c0d4030030441e00018602201e9107841c00000f2020310b1182a181d00a0302c922120707129440341c0c4c0045583c0d01c0b090405000032144130300700040710740c1c94130314405510344035103043c080030b40c034201024040072020810710f51440c1c02c040c00400ca8640c8030360900800c0c2440b10100b950070b4454400304641501c50303004020841d16141c00d01c0744120 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 310096942 1250 310095692 310095727
    0x90303070c15020d020c06090d05180d0c06020c1005070b13060905060f010602120f09010302030402121c08090c0906040c021002040b040e070207060e15120f040201080718150c08 78
    0x3605080747c480303072560300c011941d403810041a030002550602894014600d07092501c1802e000080074120b03010f006032280300d1080030b10351125004d603008110101e0941040e0309115082c00c1c5600f052410078007240c503002c00b0268000e00600c0f003c0c1200c03c000d010000f05a10681a080d004011240700e854207070014a40e5601c20301850b405031061070000904060070fa0101ca440003106c1741401d090840120054019404c040c00403a0320521000742824001d0003004032180e0031044400d034050480518201405d611000f92003131002d504040101181602d0398042c490304248140c80025004103075900490030301071880f60b1520418000500080c0304051040604255200034507050340b180c07941107007660380300c210b485044049840036600e2500c46c6000c800031020710315008282c43c41c00c1c041410680e04044104c8030500c9441c000030900c001c2d5640481e44070ba0040f80c2d4200074005044034411002c25440502c10811940d0300000400d440034410707400c01150b160b100f4109a20348031100982800d01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 310098192 1250 310096942 310096957
    0x161e140c031c120c051b0607081608040f08090d1505010f06080412140307210b061b0c0d0f150b0a060c0c0e010f0602070b03090303070c15020d02 64
    0x303202e01059190781d0200305811070030340703100da4842e40e8401c07a0401c0204060400c40c0340c0c40c020300005000840c0c1d02102c0d59154250341e121800942a90700c0d02d004060650480a00781030f08280c0c007020040c1c1c24540040d2050340058011000c070f0049a1240341900707081c0b04e0b03184080d8206c003d14011804102002010b000b200c540c1c0101800142c1c2c031007590b0305140a0743e109000002c1c075818040780209105a0491036800c0491410300c54010f50003415001c1a40140c1e05a400100c0c00d10100440ea50800003d40400d28042030500401d000200010f455016034080382d1220a40704040d0142c400c0104a80c4042c040c002e468043d503442d00c4e0520311070300744270b906094981c0c9003810300c00022040300d072046407800200142258511401c0030001c44014181d441c5c22035000c1520000400d1581d10583c9550081085140042c240c0d03040c210008d0412180d64801c0c51081e109000744020102c0100540c2c1d404540d602e071041140000341002008210075400103140c0780d10000c0c00785070ba10290380041108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 310099442 1250 310098192 310098199
    0x14040b21030c191703090307050304170d031b0518030604061d06070c06051e010f212015030a0c140901020a150b041a0103050c161e140c 60
    0x480e003011980f410440710010f006100f05401400c0103d2005100080c0d034020610004507400d022582e907030107185a12a0f00007035000903000315000180e46082047d5680030815107802c5c003480381d80231448401c484c2401d101d44280800411285400004401402402800101218524201130408030004c1c000700c00350341c688a14582c00444600300000342c090185d0260b944011445026807100c03001040040c14645208901805100140410b140304501a0802c2c642c19001079103045d00704c5c0300041001c6580c070003121131941c0450210b03660017180308802c3d000e200384180c50f0442000203030020800181511000d000030061043c288040d0741311900039a103d40740da80b8005201e586c100f10341c0c002e120996006901032400c410002c3c4e8140b81100c00d0300c00c00d40012400903104400501940c0c51821940640d108140d02030b8260b603810b00132150003d0858241502d007861602103403440020052000d040300386d001c0d0504580350710284c0d004003110740142003205480c4c1c00c400030355100c0d40c2c1c06030614031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 310100692 1250 310099442 310099453
    0x11010e011b080c1630181a030a11040f030309030c060504080303072a08030a18021804030504050603091c03050c1b03070503030f180714040b21030c 65
    0x3c405001e0421551038507008003008000743c81c01d550700051a0000da03070140002c08103842880170f55200d224103e180c003600b512901e010f0700c40c1040c08507072505580e110441ea19110140407a924601004594010004400c0030802020500620041d8441e5901c44000240c14203000000c0c1a800a149010b903442128414021079a552007103481d40158015100b140e001080842c40705030154601a01c1d0501b1458502101d0000f030415201c004059101a203100c0000001c1003010001031060b000e50003000c140141d0410510313008075130941c444170103011103548000003082c185400b54080d1402002c006116a541e4600107403007946444c2d0f54007042c0b814203070342e06000740700a0290180c50700c59001e030b003040c5040c04886040c0d01030010600c401c11285000c10458000855814030085101d589003400340d803c0d40c2410300b40454143c2d480380007100150080c1c4014030610b2072500d59204248002c403808034054180d0030005040c0f42501c0c5869014451038aa8030060000c08400f400c10144158242e42 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 310101942 1250 310100692 310100701
    0xe0108010b040504030e060304020d05120d0b0d050a032a0f0209130213020d061701020403050f0a0506070806060c0706030506010207090e07030f15020d140109020a0801050111010e011b08 82
    0x410343e42c0585000300421101024590742d820300304007a5a22500040a0000010703060f100e4500f00300e003032014409800781c0010242c3c9003d00034021a05003c4040c1c91010b200e10300754907881d44907c0c41030802800c2015858640c01074440c50118100c000a050b141c05a0516140c60036204403440903004900a01070000021045901c003102e4205454015184491941901000400943c03204001d00c2020360740300004900f140200c1480c0c4402021a0001a5200d00b50704000d890032094003220f1178254001d86070440055001305800381c0120072810300007216200c5400103407540c01582d4040602d446482400200240e1541240e0701450081e002c1d1031900c0d84510310b01c0141c034004000800319601c410b0301000040c3d01c2c0200404a03601507401d4220fa43d000070303c0803090341c0c48400e140401d03e48901107060485403c81c1c030b042c010500601c0440c941840e41c1c0002c2e010010510400303050114034210100150400c0d04928020b03070b0840c0007081502e01c0f803103a210b004101801900e000032150000078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 310103192 1250 310101942 310101949
    0x3040306060e1306110d050f06090907031110030e0a051c050c030f0a05040519050315070816020708010c1206150c060c050d0e0d020c0306100b1b070e0108010b 70
    0x19004103d003400c080a01200303070b201c460241040000030300f00d00d00c0c10011707158131454502c2491f0103680107519207006d50500340e08201c0c060740007400608490f0080041040058250420218101c8060703584640d06403040e4000e9004120740700100c015406060b0500080110115401c91261350805040400c20103540085a03140118817004800b680100100c0c883e00880d8809003044204a00d40300e0300c0e20382c580003c0351000c0d09030300205200f4001d5600c203105918081c80004801d20030092080003616100b24000c1c008140a400c2c108252074101d080308045109000c0030000d089803a00130300030442c0c264401025075500245401c0c000e032800c90042032244502e10403000b480340e02da5a4508030f82c010b403100c1e4010004003e41c1028080100f004946048050040c51911304000000d0000036880500c080e04020900f0440d6100e504944208500c0489148404d82518410700d40c29131aa90200c182d8140c200c07041c1d00c50407040c8192800014070f00903182d15213058600c880000d019601e15102403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 310104442 1250 310103192 310103219
    0xd09031106010e190e0c031e0105010603050402010503040b060d02040c020c1906080c18030a03030225080a050c0102090603161815050306033f04080d05070804030c06020304030606 79
    0x3c0059401440c003451310302d80d01c3e421510a09140d40191548403054000083c80c1c820010803c840b0000b90201d8002007290a210752401808603060a0007140fa050340020814030000340014403041014000c50010380310b201c40c2c1c080c0135a0151040004010700400a9030b5a82041d05071071041000d8003032845413020364207032407040341e24a8880c0303290341e1604401242150030000e8012604049a004002150f0302001185442c50003500d006a9a40c3c200c600b0103002e450b40d030700080003802880404800500c90304d00302c03103111300da03880c049848000340340c41c490292182e8607a41e0b9000d82c02006000a08103411640d8155103180c2d25044020305180c0710f6810b0311b003968412010240081d052104a031800f030303802180d0240004040d5181300200800940080c02c0d00c0000c48045c10f042508035590700700080021015980c0c904205092514043e40c0e10f0781e0300e04048400d41003040100b2203608210444c0207940c05194000c0d0040d148a80b55400203540e6003140c03000395a12401c0c4400003c0030001c1d820b4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 310105692 1250 310104442 310104451
    0x60b04240b0c2d16030b0604050601090b090301021605070501020105010e040b22020d030f0f0c02060403020f0d02120a0605060109060f0e0307091404150c090e09030d09031106010e 79
    0x2801c00800c0f01100341c2d0050380c80c0418419800407112107101800c9040c0041ca200d031010340c0030b61036480d0441c00c0c2807212900040859004516100c00d001050b0303005152502241ca001e065a65a4201800480d02a010f502142c4422680d07220b03428040060100340002503d03001c3c1c1c001c003c03980c0d94440100b410001030b43d02034910841600450760500102076040304110341c00b004a06051840d0340481c94141c00c2c80300a400003181c0341410f15515510107412000c6d40e11910700000c070303a000758000072094855440020b20491164040d000b10351580e0310080c491a0700105107071914040410080d8694443e81d00407121185094002106980030348802d6095030042c0c1d0796070707145031100e60b41601c020780c1484e1843c1c0d00d03100b030f46030001d0741805a0180b2a0512502048600103050038034019181d010b600014400c07150500440d000782035446525042151035140085111391501c0c0c21450452051a6500c1b800c14203000f42e030414540c20002c9940100c0740d500480b01280c7ea1013140200d055402d56 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 310106942 1250 310105692 310105717
    0x3030a0c060b010c0b0c0706051015031a0d03020a030e04060f03030305090c09090d090e0705030f07050f0307080114030604020a12020f0d030e010f030b010f030207060b04240b 77
    0x201801241441d44000c00884042c1099071013540e1548405640801c110792284049500048810401901d4000c1580181c1d040b035000c2c000a042c1241038501c006075202c1641090381e20401001a10181c11040c11007440280004400300482e050085d00c85100782c0b030035408a01ca8401c944040d08041c81490200d40301c00502f1000c0301d09658048002c2c0c14007510046040c8521142400d650355010540d60044010800030300c6211083c020140c900c10481d4020040554420104043d058110341181d41c421259640d40c1000e80e05c41e48162103e000c0c03003085d441c0d82c100c00300805c02c1c22600580d603c1d040c0c0f80201116068410303488201660b072171045900940204c41c1d07403002c10400700e172803002c800700b03d00c01024540c83c280700f0404910424201c0e08160001030402441c42e6055810180c842030700d0301c440c03400380442151040080c2c40141507007000810594009146001d01016138031015000340c00400c00c4c08060b04401c000c10f00442140a6003132401c502020006042540340101c416024111 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 310108192 1250 310106942 310106957
    0x100e01020c04240f1706100905070201020d06090209040f0b2b0b0108010b041d0705090a110f0702010813030c0807060603080c0606030d030c0207050918030a0c0b0105040509100c2a02090603030a 85
    0x82188000b84c60003034172400032f541d028000030040c0c000320300071403000d0441c84c6001601c40d400300040005403195000d488280514043c1040320300c4c1c41e4951412411450080300080300c80700400c07030340c440f00c2c80e064020300b009015400200b28440190400030410100b00c130244201108280780b42c842403c010050032480c2d0100c0d008002904084401c264080c5902c2c900040c54000040c15400a03800074250f041101400907070030007107680042c040c541101800440b10600300041d54050480882072a01410290010440e074007008130380e0b0410001f6544c40240e02c1d4070b50700c140900c29a203034802d03a0810f2113030095805280003240b003441581c20000441d402402c18900c0d000c00c0c06040f483c094400421040c040030001c01d160710800041035411602d0b034400000e504503052a4000f107106800503440342d81008148080e0030b000041007518111000400201074002d00b800b580d486442040d00d08100c21302d5017441c890b041807142400b15690007511001156642c000c20182c691080792054804180f01c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 310109442 1250 310108192 310108199
    0x405060f1021110301030b070e032a0a0905040b091b120307020d0807110312031f0801061401081e04140a0606030f02100e01020c04240f170610 63
    0x7806907400c42e5054403500301060841c20b11100260707490500000c82010002004008102d41c1d070100d160b21402c0d80c078103806103044680000380c5a2204885041140039481c450392102e4080c40c822424152006082040c600e030749000c50000b0704012141500d580700c5100024081440208210032040100060000381040a0301041003c00425480e031307600d4803007404034500580301c0d00801008a80070750070702034441500c0d1408652540c50000e00c40d01030340003264000303010b00352481961381220007292801c01c0700d01c0e40c010036207100c48940c0c0200c0e860341c240200010018045000d540c104c800030f0b0b90b910959511140c3c01090380030050101e14650014400180100c0e48201c189016002d600041c1c6c1c1d0026842d855110070740b2020f800c01c0c0c420a9200303070100b0440c5012402c00e16140420300309240109440e0001035155100c1c401b0139401180c448010100442501c4446092808031000300070960b51240301000100b8654014500c407510540800380e10301a00090441c480c1d04a418205c012906 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 310110692 1250 310109442 310109447
    0x506070c0506072a08040f06020d0905061809070908120909041e05060f150d23070b0409020c010e061605071106031f0b12010e1b0304110405060f10 65
    0x140b499945045240000754a85130610505881c40254025400d19071903900301002c601100d84145d103c07005551164801500355504640303400d0807203034129481a161079000d5003489052482281395640714896000300100f03190001510340645407100122030920710400d1004c5914030808452580c001010b400040c002007400000c040004083c0c102c90704910a07a80c5c4003442c0c00c406644102c0500c0012041048012032606072100d10142122120084032480d2903403e81140c407143c1d668180185414541c5d8545000c1141c20014107038022416503903650b8030000f4000b074021044070fa409500f4050b0402c0c10300030009100740a101c0403012000514a10601606d540e402480700304c500104076107080c942507031144082c43c4110310b40090040f600604002c1410008101c0d0003042507800c003400401d03103c8e180c00e4902419100c0008a400301516859007a1203110410340c1d48200140001041004100e5282100c010404090314280440d45400c1c040155884207040b800703030010b0007614100c22462 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 310111942 1250 310110692 310110707
    0x20d0b192a020307140a0b0f010b0a030e01061508150405011d0415060b030613060b0f0c100c0c0b010f030807060b040e2a030102030702030909151801030506070c050607 74
    0x7102d00403030349460105c0d607800c09003501c410f0340808690080210340061100f01214190312240070540c520056040c83c0b1180164040e00c1030074000c0658518034501c2c400000d5000038050050290716007031010300160010b0004038100c0317000078030b1004044032001d1030409009450590704240c0d41ca4011a040d4103200e43d082c4030082040e2031000045031400e0340c0c1c0340c0324441c5030054121400d075940d0324540344040c0034040884a0041300d059140c142d08000d00985002038542d880d030071400e401e5503807002c80100c0340b40440c409080180145080f0003a081250084000b01c0302c607110b91408609683c3c1c494180080030280e100107008800d040020340c0005200d40d0283c0c040b203000600014035019114142d1380b8000d007580b4866854118040746042040244005001c0001d00714000d615610f00120700075103038007455100d50f014000d80c1c004140720b60f070303000143c0c04059400b070701e11103001e5050740c1c4440881e0000c1c0b0059419024440104030020b21500c0000021a00079000300200e480740d030011103010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 310113192 1250 310111942 310112021
    0x110406140403150b1801050109120201120501120201020d090315020d020d050a0f0e060402150c1009030f080105010c0f1b030b0c040303030c0908100b040207020d0b19 73
    0x3003080080b0001da40882824059580c580300015070b2043c100031300c0340d81e20f100814407401000c02c00040040341e90002004055803080303024031240111078401682e00d0074088020721905803d00c000850140c00034541c0a803030600076405c580c080000f044094600795503c1c04081c0ca032500080705106030f2583c94005040c49c10598100524000300c910102c012140709485034a821519205000c0c072688060140416100c0410050f1899091590002e04481f148100700300703100c213021a6800101d8000c0c4400700c0740140318107080c80b201d542890b005041400091060010684a10011440b5442003440f44541030b40181c90b80c62040c81e0361035204a08400c01c0700036850080d5414044001100d031034941c2c0c09822a60170407500d07982146809800c0d00c9030101d850f010030010704130421414900013010b01205010020004910540c0408907002c0d12404101075080b00a044409080103482358440b8801c1d01407402e140203c5103021280002c2d15161a0340303042202c00d404101d00701d456820540c0c40d54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 310114442 1250 310113192 310113227
    0x501081005091b030403020a0204050c0a080f04060917071704140d0501020405150409050105100210200304080703090602120409020f040302041b0809030a050301060c021801080f010e01110406 84
    0x1060940c1031800f407036000300c5084005070446c02060342141081e00409030804401c1030040c3c140300f103624000340070b00c00c01003c0c010050103050200e8240469640042002e0350040d103030032074003146818810b000e03a002a00c100d0342000c0e03a10012448074541010745050383d201114251900e42082c04004c070b095640e02c0d040d141550b003000000f07500d50360303040d80c8a40c10b14050206511a46040c1080003260016070005002d5911500b80341e100c0740d80480c2e141840c038080c04001070b418030440b001006407110044c088054010000510051100d003002926010384603a6460b104a40c880038120f85410503841c03002222002440203009001841e0060074010040c4c9420b01c2c107180d5660005015650003480b09e51a81c041c41d0203000b951030740201001da020070640300541c80c00310302400041a5204c1403150000300705120b2021011996840501e14020040108003055541c4400318941c55450a148d10441980703024410315600384107000e02c030040c1240210340c50400c5e01d0a84255115008082d1030300b0b6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 310115692 1250 310114442 310114471
    0x906010509031c0216090c020a0212010204091125080f0a050c0102030a06050901121a15041a03010e0703050d050c0a080a0807030507050304020a1a0d02070b10050108100509 76
    0x2a0001100e0420620f001070341c0100314112048514800703142c0369422440320715040c07841c20001d590b00098070b605d1055050700c25040e205400c01d00d4500a0055410104c581c81c140300081010300b02c0d00000c2c0c25045864503440b10b001c0e031000b00c0c42040740300e400c10040803042e0074803032000c55074029805400f45048500301300d441e00c20f40100c103500726801192510070301540c0700c0301400b0609040902c0ba02400180544000d14000781d190048401011603840d94011441d0000030035003000c607500740301d40c0c1c60050030511124000e0b50700c4440e00c4410ba1070150103503117042042c17281d0740c0c40002d41104917074220010704040c081e800d408403416840104c1c60356261040d100b0107000100203100a002084056070349440c54140550014280d40c0090592820805c0520601025031345508180e022990b0344040c420748400169050011401080c485070900740c404500308050000d0300d480503201c2d510418014100d151118015581075034143c42f034840603082c6010038002070800ca042d144c0c2003500c0110407070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 310116942 1250 310115692 310115713
    0xa0c0906050c16080d201207060209030d030f0b150706050703060807080114060108010602150a0f0e070302090108191e150f050601050a140318060702060114040605090601050903 78
    0x20002003c55200144a52040100d602ca15074043c0040e12a01c12642012048450b10b440c00d59851030121202c1c0c21401c03002400b03004101403541160030105000c0c007910407505c01c140d4003800409900101202c0942400e40c680aa0b207000f4004041503419408040c1c1458229100c200090100030800c40925540c5c4002103901d0204000c1c28006100400012681c1407160740001c0e80003102070b090b40c0c1841310950040c0300c0c150b004200c0107601081c8140701010740e910003002802070b10214590324a920310b08a4002a039282c0402c406042c0d034001c1c1e403040016680c232a081c40e13891101440e100401032601d4424000600251040d0811030800c40a0300c5021589480d0303101e50003142d080c6040b1040c0e85184041e050981c1d801084d902001c03d082c806c0c04d00328010303c05041c0c2d8004003540d5003640d80000008440c00c0403210300e000c101440c4000c070b940c1443c14010181d075506003070241d800d00c00301810b028100b51034580214000c0d154050907000054841200548075600518602c9506000e8103a620 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 310118192 1250 310116942 310116973
    0xd050a11070b070e220203040314131e1a0a020102120a090b06010e01050a23040803040602070b0304050c220c0320030c031303050f030a140a0c0906050c 67
    0x104100e5010300c249a02d203003000580900500a100307109030144004805c0c682c40300c8a1104801c540300003e040142e540d91b00e44c5012103101c604104409002d120104104102400840f00070307054030000703540404140010000c120700c901092040485400c1c90709141001c0107102406041000001d00002d410140a140c0108809004035480b042003550381040c4000c1c008200700c03140d0805000e09000102809000000f451441060420010720800999101c00140310540ba910820884030190382c40355103801286440c5e5100b0700c103180061080901c003049038112001201c3c02154071000a02d900d420180a11883c4080b1001401443c02d0a48a000c4020080c0c000c141c40d014807981e00261080d00b4002515042402d17200680b040c050a000300300350311001000700e80d080054a03c1010480700a0f1404882621030401501d14100f40803080c0428040345400000c050079980b00c02c80603d64071b0744842c03012200c02251410015600741001c0050038090b500401d030070a00f490545072440741d0328a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 310119442 1250 310118192 310118197
    0x82719050715120f09121803020904050304080106150e101b0c05091f09090809060d050901060510020309040f0204090c020309040f06060c08130e070e0102010b0a0602030d050a11 78
    0x10400b1030705000c4602c0890f4654032031042180d260a100b040281802c1d212004041b03072001454041c402c5005090703440b00da608484c2001581d005002204038a010316165880f40c02520542d5919800c000005c40c038241d001d10449104002503640303420380000e1314200300002e08006058414803500443d11200504000322031903081d4052701d82c050be4949820180400c41200402c0d69200c0394400e01d5044030000310180785000c075411a00040781c00c0002d420007407124400c2c038035000e40c80b0500040c0d4a8000d1540e4020030312507000c0f400208070441d80d4005010860b64905401c10042e01304010124079850190300c140c03020f90310907000508090b00c2d401101c5c126010600d150002d60b002140c003044600d030a002c0d580240b40040d205205a91078244080c01c8006001c80045c4168408298103da00d405800e1070b034000c15145108a10a0902c004058480010410708034019424202040c0060414102100413140701b507002b103240180780039104004100181503140d0458a40701c0b215200c81340c01c0302 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 310120692 1250 310119442 310119479
    0x19030e130c08070e01212304030807021203010620010c030905060a0e03090907110a0303060501110a1106070609020d03020114131106030a0b0307060827190507 70
    0x50015600100c450003a01d503180003070403a4104015060082e815980c09031b141041c04104600b1421300314140b0600501808819038000b081c1980950018000e0200c900480c0c01035000c1d49031400180c9496900b240c9440035a123002401410030030040214030301c10301b880d9a901c6002000c051507201b2101c2800d080d111280c0c800000030b03031260700c4a4103001c1d05201c500d0700080800d00801101090001c00c1e626801a09000341c4140c0d852030000b840c1c00c1c0100380d88000d00000500741c03a00400c162030041c004140502400c0d00217140e081c2001d00309400010000360180d00401c00ca211885090101701c419882144200d85070340e1101000c40040c1c513411607141d00d15210341c0010400844500d0340c10072490004002600d490401180300001c030b00821115071012000341d0b510b9036256280e51540c8050041603141e6070300341c481c1c0800007481c1d6512944660107003000b2000c2c4200c80707001220b00890b0500481340401c49402504401007103918401c0c1894105104100341c41005a50300e40c1c1c030000281090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 310121942 1250 310120692 310120729
    0x22502040b1206150a1d070c1a01060f0230040306060803041712030402040225050105070305070201090b01050d030c0b0a0e01200a0c05120708090f01030b0319030e 72
    0x14003e140c089070f03400031030003c410b8405c1c40e1405e00d0848420f13030b0007001e00d40d403442c80b01000010403685841100d040e01000d4110b60709041803107500c1c50040c03924a0902c140000101e85100030400d403840800c0104070203005034054100300d42481000c40c135614002c0341d84c00c44070700204030020005490b405004002c2c00548051a2558580704214070600c0c2c055415004907004112501002d02d850420303250440d40680300161145520603000f43c00c40307096030500b0003a000500c1d00303404002054100d0f520403092a60107020944880310243c0c00e986100100a05240e865001440f4a0801500c0c50b017446000b481c0c0f40640302195194103001079015110042a5610781078462143e601c00d0007691883d10f00101160a040c60140c048400c500070183c1d50000c00c65600843c2040c00410000e8060869200c0030043c0d0300c112074a890300503a400703101d4081c019860880d0521240d8000d201d2a0030a08015018090000907601c08400c07070f00a1135011428800024540c10540d00d0b2851007401c1c0240c0300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 310123192 1250 310121942 310121953
    0x2150708192c06010b07030203071101020a0606170115080705012f16050607110f180106020106140337170301090f0c02030d020d06031221022502040b12 67
    0x401d00c940c1001c070140c0000c101703c0c0c000c100135800a50700100302d03805941c104100c151100d00b4440100e0400c1c02001001d0041030612034080341e4507a150185514841821000f00540840303c3c00b9080c80d824948101c80d01c1d500300e01010009940151518080f00004182008401b60040700d10880300008001e910500e0307025155401e2280e60304a0540003510b0b080328961f00b81210b0795a002038101003c3c0f961801400daa282c003404548a000303441c6050a90321200740c100b981c4884000f8000d1040317210306e00e5030b100d41d0305101c02241400b141d0b40c0c28929644202841302c92983c160420301600c00324914200f4842d041c2e0b4507020178203141c004c045080002d40c078550340c1d52400300e80409440000100100c090700d0f01c0b414104003a0000121219482c0081c80035031141ccc101c40306040104a2503201400b040600b800050100368805c042031582d201b29400843d0010924036024200c0c06201030f00c0402514054020402d243c45c54103410840344000c2002ca2035807990404203030b101462486207481c0ea0f02c803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 310124442 1250 310123192 310123271
    0x1b0c1502070b07120b09040f0503070b040501020c070501030b1822050a030807030213031403040f0e06240901080415020c06060a051002152a0a0215070819 68
    0x4035045030750901381c0c14402d0140c07014100004105405c040e1000b803030400340f03506580400c078083c402e40e01d2060b000074603010a45071034104503020398011204941c0714020b10601107034940c02842514428071000d4102c1e038075103403003c2d0780c4c1e4500400030704442488280d41100e51007800c10b01c1400071000f4402d6020b400030030708600d4082d0100b2000f401c500140f600502000b111003018030070341c1c8200e0390448460f07804d000c409402541103205e00c0e00401d00000303e468020070540741c1007866038020b00080c0e9407000300000c2c0541c4902da001110307a000c511800c00f0005599191311440c440b54000340980040340c603d1030b140003e40c040340c3c0071031072100603a00314a041000620304001003000505050300d18145040030402c00035141c50404060b00310f60700516001c61002c140303103021000d00800d001105010400340507030703d01c259048041c40c00014403070000c90200900c0150803803030040c1016102d212054503091400306a5001d0b1241c0d11421603a00e2500303001c01152580c849034840300641c07401607403240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 310125692 1250 310124442 310124447
    0x270e01111305010810350a0b06030c1005030a0f060504021204140c2803020306190f0c0815010c05060a091401060503030f0a210e0c03011b0c1502070b07 67
    0x10010501c45540c00315003030401030400074501d00c501b0308000b0203450100d000c803d01840c6d0302603406d1517003203c00e02c1120f1040082040c0c2e1f608141c05030000310300301c0c1d252440340b408200c80021001201d40008205001080c1e001e0b03059000110340d00009030300480c81c2510380021600701d0b003010303c00110324843d120034002806141d0742002c40b0b10310400c015164020364200460708984000040d4110f1840041c801c031030b01010051038401035075009040d40d009090004d508030108030a01c8c034040e0080e1034200c120300100f130ba51141985500c81a2107420107641e500d4070309c0020000103100e29060003a080c890400103401440418851180e84000086c45021401c0c41c4540002001c5101c80d1a07150034010700c0280c1e40001a030711040c80c1c4800a0395100e88851040b030740d1001140c0240f40c009104031800d208a03039142c01040c40100441c1c2103d003002690b10805003614000444000c8040c141d1031201c180921401982c03050034000d1031586025802515214100d0b40103020603605010f26070144105079a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 310126942 1250 310125692 310125707
    0x1a360a0b19030309060f0507060606050307081806010b070f06060b0408010b1203030c0705070e0c070605060103090c0e0a06211a0103080306091005060a18270e0111130501 75
    0x719a08a034441690a41d0b4000c0d00314081401400c00380311004030382e60f407103500c500200c8801c140d000030203000803561014064101e070001d480140c08941e4620005240100403500d1807926190700009014503480e04409a0700e03588504070a42c0c02440018000c1c0104060303000d008001c090302107080366102d01d0815a60b084aa1014000d44100c20fa16017105d031002000050b0b0390840b03c4101002c0d0354081c0c03441c10300d04c0c0070b070300382d01104204281780104120a1a0340000d08281d50060f2070a014980d01c003001141261585c0d8030042c008202d0800500103400e000702e806610003103181c0006892621108209015581c5032080c00c1400c03922400c04041200d07010901036504070070340308000c6d2541983d4550314180001040e950007074200d0301c00101c200810b5285000200000381a41d55516a520350007001c15200203c1048400410400001c1c1e50032485031228088105c22000c074401d041100480300a4181326045c42c42641d03c414050744d0303200a000007000444d680709000001c4078a040005407010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 310128192 1250 310126942 310126969
    0xe2409040212070f1b0803010509090c131a04050c07030f030e071403100b060f0d06030b012c13020103020c0c0a0605030103050c01091412121c1a360a0b 67
    0x20491706200b000402c0f50301642c1c155942240c2400140d541c103540c0c5440c11103020105a44010303903004408007403030240c0c408d9040c07200078881c403040101403109102c1594801e40f00a10314582c10040300d03000c280304048082e1114050302c0c01055180d481c030391203464007a15030040c101d4150f881800141c28a01006888110303450500180058490b00d00010014000c00a103606800380000700803014030f070141c0c045000385600143c401460358446100445200300320030004c070000c19003d052000f5150042140d44100e05420301414405c100ea40118040e420404055110b40704400d20201c2a68035260031901800b04c03070351070a880c1e41c95800c1c2546080549141a814804004000d020b40340040890300800f460580b0210f00300c114060000d854240c094142c00090200070400c0b091240740c0c040b00c0c00071422206030902940d264500c4034004110301520240c3d00030401000d8545103034404101c0c118104100145442034090383e2081c0744864002c5980115060b502c0040002d280341944a48000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 310129442 1250 310128192 310128227
    0x1801061701150806070f1701141002060405071811030705120109050103050c0607031701140f0109141207080f0c3309040f09050a02010e2409040212070f 67
    0x481d40f800703080c2038550001520500822003e01c000d0381a0328010090384414411a070b94401e010b60390780861203900b40070000101e1140102c103c2c0ca04d12944001005400307141c0003005803103070f185480c02d161041ca004109808250b0348030362080c0202070300ca5000e0b42c45600035465543d9100303400c400115541038142c06c0011510714141c01400404e40020f030381c440c0600e0941d0f405680d0843d40c2001d9130200940f54000303044105600c00420038001041651018150588800c5400d071408001544d22545901421009194804030320445107000344483c2c2c4243c401c54195400c0d1503d0b08451420080c002d560300001c1d0748138070310704041424118241c000c000146101c52240e510361000305190000849030345400c00340c0100c2c03080c28568440e804811141000c1008001d00c00e0f083c036190f0f0700d4103600b04003607010079055900c00c5413500b01a01140300c9008910b814001038110100041030300d4115481750307a046070b424092090388034000e041450140d0038a407181c129600c001c0310000c0030314884481d00543d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 310130692 1250 310129442 310129481
    0x3140a0b06040b060d09050c04200d0b12030a08010f09050c03070c140f0f1e1009051e0102372703030f02070503070608040b1801061701 60
    0x4a10100240c80d00480112004600f000e09440080d6a501a00d074a013020701d440c00c100c5004019000928101885083d50280007507a0003034042c90096911291032010110708000821400d4a81c0c0e1224030b1541d402090620042460f05650786982c000300d400b00003103010303030340144a00719291024800a1022100c10310840c40c0c9855500075a0001074408000c0c000700e03400d04010000d0500c106079202000303200b243c0e1603901440c03d0558480014481030454020b0041d0700340890307c491056040c07280100700500043e048840d00c000103140c00301d802e86641c020064480c5000c0e4112a41e6030324101c90200240e154000700102e001d440c0d0071201000b5010f00d101c800c514102c40b50400280261006060288403d03442e543e85d07180e07411130440904001d001d221804404c06070400300300c071210696a4221102107440d2800d05039500041d0041401041e1400d000174006110201e420b580b148480207100114034280d0303141d07401c0d03c0e030640002d41c40800341000e8107035400c401d1040c07040008003540d901d06d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 310131942 1250 310130692 310130713
    0x30e040c051b01110d1a090c030f04170d060e0708150f030304050d060204030c290309011506111207020a0e18070608180318040b1311040314 62
    0x10014801e0345a8088000400420b90700848400c0d8440643d02d03180f01e400e03594907020841980f006003404040311a00c1150705c00303008020304081c0c0c1004c6c8100d240e001d0303ca2450710b0705e02444900003002402102c0d80408041d855500e025680040c0402022411011035003e003080c0c242c5403942002070080742003012040800070f01d00020050955500c0054611520300312458001c43d0541c0300c3c50b0012a04510395054100c100b02d820b90040c41102e001d0022100c1e07003030300c414089c00c1c0d0880301ca07881c4841030681f016051010000700000d6400c6103d400002540c01c404586107808846503a100401043c60303c00100306142d01070040082c480801c0114919112031640050450117443c02141015a038501c0011101c25060070303501c0040c61544103d400e003d9841c0e174000c0c050790046030b40081500c007095280b10071020001c25155503900c00c40100c00101444410f0000502e502c0c6890355200e91800304084d00500e89128803540b00302c090151a503039600318109107184100041c0004002c1d40312a1a01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 310133192 1250 310131942 310131947
    0x30307091e0501050a110703080705070f060203180f091006021002272101092028150305150d051906090c0b07031701060f0e151303030e040c 62
    0x880540d0000d09104c0d03102c44001104642090b01c910340070541b8420b1030b00120621188e00050244248210211043e4940300c9130500ca00203244c0c41001e000d60700600200103440081003c41082010107420541b0401e907280001d10710748d0742510740c500c103c856001c003402166414042d0640050450a043d4502207c4040d600c61407001440c486038240e02101c0c0c0400d2603912441c901c40f0034445007880c440355403141034a076402040311203004c80302c007409150348121465a506400608900c018082007400501030f409e650500001110707041e840344084404501c045008042079180c64140c1e0300040c10749003418003160304200e4101400d00c2100000c0c060800128001041c1012480c4047d082504441c41c1c54901c0140c030b03111400034490034030180041352007400c0501501890b4001d0343c594400c2c903100904001d0207a800c1c042c2c540016110034030b6821284c00b41409814071440030f801c04051000e010540c0b07a85400405010350611420740b4100f003132642c01202d111444404881c10081c0403281ca201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 310134442 1250 310133192 310133249
    0xf020a1e0507080304050c04090510050105090f0f0925090e030325030608030d05150a15050903280b0901060806130807060504030806012007171e03030709 68
    0x3c00c0302d0800800642000400d100c182c5803178070060404e00040c0014030f00142c03140f6840c0d0780c10f440a46801d0000450b80740409115014260340c04080242e61520bc2060460400080560050703105808100e41e140c809034407032060000040103a80307070035800c1c00c030080d00340c6041c041003207400d03802030080c0901800050780044031000800420301c66010540d40c02c2d0064123140d40004118040410084c10a0700075820051042c5541d40288203011415010083c140840303015551a09802c450400e80c1280144002e02c5896002412900f00700d01044811480c407a0f2580c001c7e0b03441c40e85110f000c0801ca00540b005401418540003800f44605202c07402f996558000c0100c0200c0780311440400900402c40308a0f06076542015051025203845d040c05041c04500351102030014202a451082c103020340f403001411b000c4e080018055244c075141c41450503135403070202881207010309030340d041215140b110310f0a80c4111100c086e685070700d40288040e094400c241c3c0904860007580383d0444080b90314040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 310135692 1250 310134442 310134457
    0x160f110714032415030f03030a0c0f1b081c02040f090507170610050403140106050a0909020604050907030b030609010b090703050f0f0a0e0706031b0f0503010b0d0f0f020a1e05 77
    0x4e136800c07198003080040c2c5043c1168a40e6410b9000020601c074140c0c0042d0000840031415072a51440050180c1d4201c901301113800107103220744440c0e801180080c1e0240010700c2c079903050074440d0030180131544420040b40d03c03a42c000d001e00f0031040c0080201e500a401465406410f03414062540c50385ca140a010b2484024201071283d10042011044240140203403405036030808603c468030703d60400003500920300c03801890b01c200c4142030b000600f0b0f81d440c000c14000750350144c01141841c1c501804c4c000c180401a101405240e10707a000004d86441c1081940e205000c8000049061280b003410b0141c01c590144c140000c05d4109410032910300c41340d850b600e4204211040b83c8240741d64004a0074000d2540c00ca2951507806601c40008800e540764000601a03000b200340086050741030030f015210800380794400400700f04e040c40100115081c07800a402c000c40c4591002c1030840c1400030003811103070342d214003011007075001c1001511290b1001e040136541da8165481864650b50080103800c9010b1103c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 310136942 1250 310135692 310135711
    0xa17010807060503010b2b090b01050a0503030f18040c0503150a1d1e07170a0515060c01060806011214010902010801050f1206010f1d160f1107140324 66
    0x110300d8491010081c101758842041c20207d5600c0080340c1c0d000c40a4040007401ba50f0703030100e020011803d0302e420410f400486d94000c00862810070120007000d0603802260091500501c40070140c1c1403070312103009482c0701607403942e1015980d20340302d052106561304a0071504c0c0107480c00d20b4140040491000c1c10b0401a01d500c50312240ca6944408402942e421700310b82441d005612402d100c1d0050700b004a0b0b07100e00b55200700050082eaa90f40b0040c045070400c4800180000503401c1048440c1001d04c001c18482911400120340030762185038103407a00500780d0140d0720100e4282d4032041400025580000c116554000a0004900c103400081000304180034043c45100244400607141d640d8040d03c0ca01f01395120155050783d0394803c0300c986030324240d00c40d40c4602e84519540120301d046000031580300f2800b290b0964461200004226845d51080750950f0a02825800074492554108050320080070900c484809115040c001c0c1400d000b20006510100b02040d03c004141150405030b0030703803141015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 310138192 1250 310136942 310136947
    0x51506010c080304051911011202090d0204050402060c070b0d0e0c010f03110d050406140c070309030f021201020d0e0115030c03020d08092205160503060114040b0a17010807060503010b 81
    0x1820300e00d040085c03041c8064140583c4030410010460700c121195002c2c0d47c00d884208240000c9140c0c40700364800d26140d5903121090031260700040c46c00b584815000781c0040d03c0c132410010032401d91860f022540e00b040200342c0c000308440c0c0038450503016868045024201070f0454110040c0040c04031801054120145500d0319800410201c800c0d041e20700350540d1003011700803418542400c500500501c40a82c00021a82c0001030000c65040102d900b03842e41603841921031455600e0b029038001c10504100d9000324448003003168001c0034005440c840500840010f40c56a0741c2c00c6031801c64500c0301d21010b102d01c201c00c0400120700d400c200042107035015248000300c0d9189181113107252255200e41c0d80d129a0cd500f0a40040081170b020311030301559040c0801940d19860550901224400320350740010780b0030000074249511174902048002ca410b100320f41460b44070712980c1d1203600000005c900244041c201c01041c903003d5002c1074010040600035191807802d0400c014182e2205000d0451300345d000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 310139442 1250 310138192 310138201
    0x6060f02060a0c0203131202040605010306030807140c12012a020d0e06090301050f01031104050f1807032102070b04290c070311101e030b0a05030a0c03051506010c0803 74
    0x7801100c0080e440c46c80c000c00c4042d11100c1602d034045009805a0056251040220380c5500030320640040e02c0d0420001403e080080d81c50014850a02038400c44ca401855446411502c408400250030b4004400205038458424403207580040e0442c1040c640210741e00301500c2c0719801241308645150280307481d03141401100d002c20707202e101e2181041d03015841c04081000c1c40030101c0c1040e060b248640d0449151084210412068031402c0d510015110050ba000c00d544601e03640d285941d100c03c2074261000682d0ba500c60400d00c81e852031030706600c002e56894004640303a050191401601d4010400e50810b41040c0c4848400d08012001d002140a0600b8001440a80390182c40ba0f0500c1481100c90300b607142c0c900030381c0b40041c0c441343e81d0007540e0038508540c0e010f004003203d42c0021042402c1c06114403407010f0445c041c0249440080e002101c515010070640c8083c08841103460080160344100b900d9803500307031b19100b0b0345c42800340bc2420f2401030010030780e4464501408181c01940f20340d00da40740c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 310140692 1250 310139442 310139447
    0x3010f090b01051e0a0b0a020f0a0b070503220507060e09040c050f0a09020307030b3c0402211f030308010e04060b101106010602030715050c040b0a080a06060f02060a0c 74
    0x307030540304c541c0502c4511000400c4404900241310362145a4299550036101d1481d0030b0b580d000c02100200020124000038484c584500d000e1503000c2d10008008054211484c130f0706501da01419020f0354281c120442c203000c1d00d07800100c51240d1107002d0314610f00c289090744454011080c00c0c0280ea114910304030b1281d615031707102c0d08030a000d85a03134441155242882a0040e0050980e540302c2d0303002d803d10046102000c00c010b002d00d03a01681c4010380401c400002c9644000310703402c4800e01c42d0b0082e0b0900400051407450010540a0901041100c200b8103040c80030700c003070803030000001c102840c40040a0000a600542e07032030440d4003002201c21261154a4020090001250781c142c01004200180840b03c0d40040e0f849901007000064807240d0742c84010403038503481080b4000c2c08400546000382d100da0401c0c1e00032588603040c0c000310f42c2841d807255921405640540c68800c0064080d406001e40e143c0c1620800c0c004250500f0a4403400c44283e001a40700c5100070001c5e481195242d083d50341c85030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 310141942 1250 310140692 310140739
    0x30b060312040603051909030206150a0b04090b04050108030304150c05040e0f04060e0f120903010b09180c0603060d060911120120031003080f0702180603010f090b0105 74
    0x1202041190b403a1902e410008004003c1120100c418202c99000100b04070281c2c80760139901c0340c140c0d01404c1c1583d41c031102c50310584c290401d000d8010b200884001802e104802c05000078001211001c0398411090042109480045e0803c8549402c10011f22000904070090341c40c0c8405080c030f022030142c01c0b11348151818000c551155440512042c2000407101e9140c010621952080204100f441c012440c00c40d5503243c44c0200c510b0950001e4034280b81e50003c08e0150440f80b900038000f0840c451583c000c19000b500541e0f00c2401a1584440c226401c0c1080c04008607441d07007980c060b4214034041c0300003950001c1c80003020301a65510040380c41445010080403410b079502a0410302c020280030b08040c000d00100d044905806280481c0c0c0440f5500c80046038082c01100461000302403c40d02d61204a5100d0101829000e00c10411100144c4680044079202c08100f0269032807460300300181803d4441207032296244915284000001402a100c100d043d2182580e582092000100c0c4481e40304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 310143192 1250 310141942 310141963
    0x409020307030912020606030c131d1c050a0f051c050f160206010e0601140c070602160501080609013011011803080d1e090c030203070501050f04030b0603 68
    0x900000400c14255050341000c05107504c540e8100c4440141403030203c2c1c035a50f06984243d45604071181c20300c2c561900e110034100d0349002c40320020701220325010441c01030080c0e603528003850300b08091182d00e032040f41c448044c5446843c100107151010300c03103005010800c9020341303005002d00407034400c40403513240a52104405201408105600341946a12000c0d44105c0340c3d1000008180560001c1c284081400707030403500da0f110001010744400e8010f44ac00700c0389002080402c1c20510203092811000c00000c0b005043c590003612a032140c5407420340c0034080e0b41d0030440c1408806000d21010703841e0107980c40c0c111201c0115181081444070320300441005030b04403a0446944001c622020300112030000e510004007603c41e032041145981c540350000d641480040e10401e414000c1c402c0303689040e0858a2440700ba1144a60100d03a01300820301101c08095090b42c2d0150003903818400c50a0400a05000d41001d09001d030501c8103404901c1d066200328003001b8110b00801700410480d840c10024818407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 310144442 1250 310143192 310143209
    0xa03020c011e3501030b15030303150d0b1612020a020c01032409060e010510140d1409030304050106050f15070501020918190c0f08090a020a1811040f030f060204 71
    0x4046443c0007a000715442800161400e9a2041c041951a1003200880d483c3e2503001d40a90308541e01c15404c1c0d40751b040300c5640d03c1d400c41ca090b090707100012022402c251144000c41c1c5820401211000003c0003400036184000c1c5641c8100601c202d03682e000102c241d5940e03424640401c0f011810b060280781c0c4070510851102c840c01180e00451008031a802030825105d0401e00d8040a07a0780708c04001d88400301c41a0040420304414007586c11496030401000c0807620942c001c1144002c1c544404c0740c1203001c607120035258202109000404c2028010800101400c0380c458601c119184000781070383e0391a070255070940b040025044104503080d0140c440e44d0304001c0445103000703c0001511b1410b1411141c0032100c5084030f04181e01038a0070310a00c0080c0a407603540111403596640c05480e811405032840105200e8030350400b006030348217840c2c440601b4003090700907012105e82d0340f51000e0f181045004405034500344018442081070154080403250000c030b01e111450100e0034480d00921030342d00081c02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 310145692 1250 310144442 310144517
    0x803090a0804090207050114132303040914060315160207080d030b01020d0201051521060c211b09060c0106080604020a0902091e040213080a03020c011e 67
    0x10740900135400760036840d005000a01c500380c0c0c4124402c02e11201150342c02c40000e640101500400d43c0842d500d8138480e50540c1c40c0c031036400001c038001e00c1c5802c65440400e015032101e50300c2516120f0b0740c1095400c040140c005104000c242c2044080d003000081c02030312101961900b00200c03a10130001c000c020a01142641d400f030880b44001000b40150750340350741c0075201e1680c2603c643c9105100b458420313004080c20303000c032000000030030015003c08000500d50f406800c140510151060000e14000c0b0501d0701200d50341c5500050b4070714801d40c90442d813a48001841304011240069010045404000c0e440e0303a5a1082240001b8425000700032400c800e5600e85040440c03090b100007030740c0f80103600845c0da462840782d0b00c40c0624142d200d054050b50b000400a2965200541d00540c1d8400304000200301600700709260290307442c0f2080c0da5000348016803202da1007030145601400003400c1c0345d0003847c00260f0318008080c2e60302c00705c410030f40131405c21a14448400980d00003c000c1d0710140b040c1c424440c0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 310146942 1250 310145692 310145699
    0x3060109050a080a1a07080406020702010302040518010305011a03030f07030201140708100f050f10030f0e100b010c051c1404180507181e1707060e0a0e040803090a0804 74
    0x40e031394082c00004503a00c8030709000400d00d4280b02c42c2c1052140740c160380ca402403036483d955444040d40000f00c040f030515400f4040807c280c0d80d050318500708103019400303881c0e00b036146042081c02d441c84601504c1c1d01403420302d00301205403000320850700205e406204440e9203c2c20b901e001c030f00410001d90802d03610b0002105004080e03500c0341119020365406120500701c20f481d1140031820203900d00c200f40d1702901c2d0244003081410300c03103d0b8940c0c4040d80d09001440000d00e1205209071290452803540e9600840e0043c2c40c000114030074118004028607040c28000300d141c6d1b460350342c4c066040500110720300300300c055030303040d485001007617010725000005545076030740d5131029070060f001d00140d03d24242c2414000f075512440303000802081220300c44080d410600e0f120318403031041001008002c40d02c0d814038010411781c2108201d0b508290085c0000c040803450003400030466400130218920a21f0240e00801c507409030500740540045d0130030b09059980e00c2d03080d03d040c5400c01414006080f07031804503000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 310148192 1250 310146942 310146959
    0x307050a03051c090b0301050909100f0605150301050a0302060d0605100c290a0c020307170304050d090e04060f090204060608100e09030f1c0e1f09030f0503060109050a 74
    0xd160401c0c4180f151038100c0f05039901501c629016014040400700140010013047c6404000c07580c104801c0f6040d80c1111108504c54016500070210614001d61100010406800c0081003174410b021030040b0039040d5418070000840504030351201920030600440d400181c4001a84000024040181030640210550708054070498030b20070140d59031007040600c3ca508420038050790914114241341c040417075658419005c001e2005449601c11132009208030800942520000c208034100e20220540b24078052411300d160405890240041200c02842004503038400100e0310340013540001d0110b400c4140142c010020b140c03040e40030754440d080890000d0300c60340001d6001c1c041c28650502c4203840762580300707031080400180e46511042d4401c002c5000d01c10001c0c009059107444191031003542e40560b82a08082d079204461036207090b0000d9801006a041441049440302d07240d91040c4a12103840e04c1c0604046103140c41c2909100002000034aa03a110b115003c02a03c401007444803184d866803110f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 310149442 1250 310148192 310148203
    0x1050c011a0f060c0604200310151509030312180b010905011d040615030206040f090507030c020d030c0e03100209030c01020307021c1a010b0c1c050909060307050a0305 74
    0x12501800301c5010500983c00c114045800d620701c164010301c600e80b81c0b60789442c00452000001c11808208401c018180c1c0d03000d224030760f546c0c031200d00c0c04035040e04c82481002040348a94404001f510728080c4c80c800381c580280724801113a806042951801e1662104540605520f214910035004c0318440c80c1c041100450050303058500c401c104020b07507a01d51340d0307900c1e01d695010603444403220b0741d400280004007580c120030484500f405e0700380310083e40c80c0e021510345e400542005240101c06802408010780c00d105e801e0b030022052070300b8840440d41c004065100c51130102411304250726884410700307071230151008241e0000041c0443e01043c2c8040760510082d00240900c034400d015805203501c8942c80041a641c005030001c1c040c40800e203440b0744e0910141001c0c201154403002c0381c50980a0080341e080030500030105a0480c3ea50380003c0707410141807950140b61206500030345110121119800400e50711803807802d6640610549602000078a0662994066a88800513880100800a02240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 310150692 1250 310149442 310149491
    0xe070b04030819080c0f07020f0306181501050d0816150c0914030309060c0f01060312112a0301020418060f091a1e0405070807090e01050d1101050c01 66
    0x4119810341e0350104211900042661000c0281009200c0101b540103040b0003000310a20052132003140f114141e01080c1841d404941e44095140981c0c40c2c0c07495082d0a20070b5581050144860305a02e40c103201c009030324010701c0c00d030207419240040703010150351040c00503019420f034000b8585543d0b481d460141c480074042000c84003000a2a14400140c2281502144184000e0003006181460040010710a44d074001130310050381da02c104041105030100a220310000b070760080f1130b0842000e00c14440540300000c03864408e030560740541040c2d0702f0500c56105000d03031001c4002c0303008000070b0184002406400f4a401c0441b4005480302182140415540080c044850950003c1031240da2015214100d440401481d050910020041c0c215440d080502c1511074400002e109601c000700c0000c1011158101c5020700460040d406000109402601040081c42ca600001c002507040601103071110fa0780d80c030010803199485c08001c50a038003440560794055049030003048401e20b80c1410340c05404d803410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 310151942 1250 310150692 310150717
    0x11031509010c11120d0504051609020405010f020613060c0509150a030513050607080604020d0c0f030f022a150709031b050303120603100920120a03030e070b040308 72
    0xf80035645240c0f0118042e584c0703924008240e0700303140910200f0000313058010000c4490b806090313850420300f210b40300c1c188064180c0c0180142c82d241040005810b81c11003080e84402c0d9031141e400c01125004043d00081410381c0190b001c140a08808003e98141c014911101d52120b915880c459123049034102410411010b039900340401c1d12207c150318031071600880e0103441d43e088507001850050241000b44d42082020340300624000d82c1401d503008413034511a4490003e000c0c009040c0c0d91560501441903000003800e070442c6049251010310300803950006541404e6002d600d40c078400e00e0030502041150038200109401030f031030890030080403000540411108411910b81c1060148580b03072428003501ca010f00250b1906400300c00500d080e41c0020409903052044403200ec01c0021507000d682100c82c07190180c0d4450b0b0416000c151001e6004d160741a00401007400000c01c0d4031070008401051642501307001481020a401d40307801c1003816000345420b5603001030008104502c00c00106040320100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 310153192 1250 310151942 310151957
    0x901050901051c060b030f1c180317160503070203060a270206131217040b03272a06030609130807050118120f050a05090a0807140a0b04050d11031509010c 68
    0xc098402d0105810a40102c00d009d0340280300099244003c0c0d1101440615540e00348000c01c90701e407140ca41400002c40f00c5400100704001141002c221164020b083c80c0c0f828007640c189081000200c0c1d026240e6400c900f0561117040065441e11400c4905c0b207290071902014443d00c410a410480300446800c4400c034010380e981c030403c05150009d982c1a1180a01214a5910f0300c02040b44014000d00141d9040d580f01503011605030002c110300d03218000644014144610303410800140c4101c001e0710540100410010009a0b0b80d445800a600c89030300c2000b0b08580805062450560103541c1009200350310300110b5590500e0000e501e5140c5070701c2030900382083d54105c0c030111000c0800c8685100030035130034008054298028006488880300c00b0b040d02a80d580d6600d00d0520300710544d4003031a07115070307010007009060503c10310b04405080c09170100ea1805190001003800010030ba200039141d00c2c08c1c00720420b1207540a00241c540e00c0c1d40100045000d081c0a016a40246440c00c80c41e000b04400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 310154442 1250 310153192 310153243
    0x1a0136050f060a09050601080f061c050708070f030803130311010606020a060c030c02060c16060f05090f0a120503040c0801021209060a0603030c0b1b1303020901050901051c060b030f 80
    0x1324041c151051074180d540d00601e8580c05040405410050601940980154901c0c00c4113607000745140b000500400c020b1146a1030700c02c0300c50800c0700d00d070084075495a102000b030004c0350000e1704490308803811003006000440c117801c0403961400d000107100141d50034004001460b13035002441504650060500304007603d03403c030003039040300c55440740e69000d41c011800280700b00f44800017901002800410052000800d81e841108031303088280e41100b029500c0c0107002e00c0030000c001d0488603201600c000c2c142c00d113903516180d2003c0402000c0800704080040054108854051305000a00c2078600a40d01c5681042c041c0c440b200080714005054441d400028185070850701410084940540365136400207015113034a410020000d03d6414601918011280b0070036001c40201034416200355000b032100c0c110720401004d0f07072042c1c2c001e0344140801001400140e561a424101c40300e42407554881880c01841e11502038000f907000c1179414011440f00880e1031001281040741c40d00c7c02142000c11842 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 310155692 1250 310154442 310154459
    0x60806090601052104140102210105090f13020d020607080703081605070b061207080f010c0203270d021e0420031911040308071a0136050f060a 63
    0x14408030000d064130080c0d40d03101d0b119400c003c11a00315008074400034501c2c50039038403142664051149004400c59900d0480c100c8120407000c0340c05050b0840c4e030000b040c18800c078140c1d195200035001929415003452501c3c119907a454448240c02c0c5c1c058070399a215041c078204040345405c40d20003603000c0303400c00340011000d00054800b80c034540c040740c0310035060a0054071240f1140c90001c220fa0b4003c0c5c00d6030302400e100b00f410040100100310140040119000e0110040d0035110101403040540d482440281d01c891050701d11201549400202c1140391461000054209120b5110113900074000002c0a4070000102c2800c0103103002c251024014901e04d19180c0d80c0c407100913200c80f4900c6c102800810540310000156211008001101280f451203100948010340e2090b44120345403000011103004009012511611543d0003088001c41036161040d4a00c000c4d0754180281c45c2983c2c1c40d65040c428288800e4185801800c4072400c10440c90329802c045020102600c0c2c080c81554a020002076500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 310156942 1250 310155692 310155697
    0x301090c0f0219030302040302030616021006050f010c0302030d0515011b080409150f080c1807090620100c0305010b210402040b030105040f0c060c020303041502070f06080609060105 80
    0x100b98010071590300103802c028040450740204504141d020040000507a8007003060380e000b0704942054909111603490040d2516080c443d944103071b1030400c002080303140e6500b804110358903002e00f4400106200751030300300d003903108480d41c80b55054600414040e494007219584e01c150202a2900f0180209040751001030b8850b12000800300e460422050001d008203800c56030f001640303103501000441e2500c1113619822016001000d4542c40845845024545260688403090f40c0c43c49401441c00c11a400a00c1c11040d805082c041c4520440036540e01200c000c118810410110140c581f001d8010f0440009802410541070000e400c0c81c0c0082904480501150002d80d03a40400050303680c01e007160342c4880700340200240e034007030f0381e80300c2140c0603460070b0141a2080b4071075801e000302e05d0840d25200d210403001d07401c20006c0000e41c215140050310300008850990758844c0d030f4000540700103c2c0480ca400d4580c1c20521609407802000240c042d007210b29140102400c81d008030850303031070000446490 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 310158192 1250 310156942 310156967
    0x70c0b0606070206040320040522021905030a050601091a01021b0406030b0403030f1d03121f03031107090b0a050402130f15020c0303030402090f13170301090c 70
    0x5019000105495190290060611500c00707400d003030815a903900c7d18900061200800c04201c1e4800140d0300980c6080c0c441c42341d0286081840840d000032140c032036200383c0c0b00404024041c910200300026030800703c140040044c8001030482e8408911880c0558a0300d00070711420701200e041c13900644a441018a0b03440c21144180d008140d80c9040c81c01c0410511120000c0f240c02c50307039602020020400d102c1c0c85520650090328082854002c0e1075040c012601048940050b0314032004142745c0f002c40100413142c181c40038444542654585205012031003a060760303c1c01c1c00d055035100c000304241c0c10851604c1060540c9040d1854503a65070764940c251024600b07016484115003100f88182d24060703024040a0700e480317000c4510310381c031b5201503440c5480a41100201e000d0181115034540e40c10803009040007425800b07942142000d40c08580c0408000d0303d1150301c0142c6030000f4668800404000c3d00e81d45d0000807141605240d9403900c0003e600a000d205583c1c0c0c10b0001c0480182c0c040c0b40d049840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 310159442 1250 310158192 310158203
    0xb0406050f091e0a09110109030b0714090306040b09070e1e0a0b0409112b06020f0c01090602031803030601170603010f0e0709150e0703050601030e0a0501090506070c 73
    0x903031048420000e072200001d141c8441640c220183e100843c0602a00501c101c8020400158820090074540c80c80b5001e80c02090402038001c405000142c80140c002c2e81241c50350800108014100c3d0001150f406035111554140c460b0b482008140f0580c0c03540c09000302d048505454607d5124812000d4480080303403200808081e100b1941c1d01c80607110144c40d40121040800503036100820006400d0700c00b298415662078801d80b2055410780b8000219042c07680c955218180d038101040c0d810f10b0840310842d8080c01055011038885c480391903010494201842c5000208030782c0701c40d494820025001944c2040b18484082c400134201200082101c0c000c010507103a81812604440b4901d10f0040014845a01035403074482041e50b0b800c41d8000c4040040c905000381104c00e040409910499206050401980f043c44034104140300052041c180c00c21514a0b01041c62745d0b0b4040180d0203880d00251411041c0b01d0081100d00b031140640c0310300ca5044c070a00550b2403e0700c802c0130803542c9007001d800c042c04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 310160692 1250 310159442 310159459
    0x7110901050d1a04020f03190b07051204060914030a1d0d030509040906271202010203040c060804050c0a120b011e091d0d090f0902130909030c0b190b040605 69
    0x15603003c03402103180d01c180f0041441514100c84800729042ca100110103140c40014800d0700342c1040301200741154008014030f4068180440481000802000600080d1040ba95801d0340f00c180102d0f020342d0144294524100c950301c00300d080c1c3c02410541c004082000d55450704201400c0ca242828030300362165059500c2c40d05050b074020410004004003142240c503180e86040c407000040c05800003d0001e00007104041043d501401c20040480e107040e030440459104004001c00244000d81d4001a40c1c114540860507903940c1c641186003e03500d560442e40318550840000d201a4940d403c0c2e002c4038401c1c1241d8460ba41c0c0d424092040740034800c0240540511054180500441035001c080b005041c2c80703100c208075100144480c2004a03142c02d840004900c03560601c0034890382940100100304106046207400b1420000c02441c0800e80510380e4140e483e00c043d031061611a084215105401086030800e50a002503151306500c00811002c0c403050400102107074610f0305116800032a1000f03841d010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 310161942 1250 310160692 310160723
    0xe01211502160c140906040b03071e0803040f0504200f07030c1703181920030d08070318020319150c090302151317010e010207110901050d 61
    0x40d4100c48200c032454600c0c0e00e44100400e0a01c0941c400130040784070b280b0385101148041c01000b40d4000c118034000da00b0011102c900d501c000a0070400c1b0340c000e4451038881c1030454404107007500998003828185c40302160100d50354032580c52070411500c040303c04220458544011200401030031240c03041001081c007281c100c0b10f04004c000c00303555100c2d141c4000010060342d40c4600700f40c4904e1808a03e28008010008100d64042d01041d051040c0c200a103100a0200e101c812990030007040141500c5010850310181c3c020b0382d80219001c600182a44c101c00e0b040d20b0300800442c8120350402c00207003404130032036180e448500c03450009a00940030304400b4600c07814840c01030780881d2040301c442ca65030600a80d0586180700d00040c41030310f90368000760305285004000220b80c10300c0341701c00528010081b00c0c10a21408101904031012074906151103081c11440d240100392441148105500010b03000c0100010074030410f030103800031070b14400940d880f2008d11420703511340040200901d0004410a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 310163192 1250 310161942 310161983
    0x90a02060c120403060207020a1a0a121e0509010c110c0f030316120806091302040917180a1706070318060f05090c190506030604020d02040e0121 64
    0x2484207207805411204140d036244420b5405038030950094038465401b21740c040861602500d01402480130f8013002c100d00442c42c81f0426540304141d402da007030005d80307011041034542540000341100030701c0010080e029840e0f0907030005407000319024401c0c0d5181070a100d000d44d0160641e00f07280040780c070041c010407610318140900c8240d114025503141c441400b002c0060140f41e088240240e205900300c00c801103050700c1c0a8000c810141c05035102d490303010200700e1b20300408004100c4454045501080326292400c0400b4036441e446884103081c1030000300002540d00001c4040100f100c199500401c0030341e82d000201101e04000706d4031005400c070002041d4514865001428403004580090a20298a0344c4440403a11424011200ca5807508100034182c2d1003030165030390386041a40c10f604903100c11124424540114064644038500220219800d6210f6174140c0e039100c180c0720000c541d40d688501c000ba59801c8240b140e00c00c0300345120034000201d0307107031035500400ca0361083c41c43d05419065981c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 310164442 1250 310163192 310163197
    0x1030c02011505061b03030115090803120c210a020a20030415020c03010c0906030f0e060105040f1b020a0209010801020c070909150516030f0e030d02070503190806011106090a0206 79
    0x170401c203403a82d0742803440020700030f200440c02401004a02c000618484101412840150303000c41c00e80c0e0414005100003e00b0040800c0c0c0c08002c0c0d00802e561608413070000c4041c01868400c9032060a02c07281002201c003041e41c001c2041d0b05440d10f40c40c0340301d501c0b69080b0003040392062007940580c0040c00701300250712206110080d4249140180da107850802404a42107a600004100c0040e05205040201c10b405100e030240c114042e0030706106090382c25481d259151410700c5005e000301d513a89016103290303540741e000000589501401134412060540025919258034205070700c1075010303400000e201101407086801070355a20b4042d102d802e00d045681801000d07170b02c0d015036101c460f44401145442c1a031280703d1240902c1c0c0e5480030601d0075028020210b655143c81403003043d01d40310001c0903900c4004191001160313918005640d8880c0e81c0b030160f0950141d00c40d185071f138801070155008500e80010040d031040d42e003a6940030540342105045603554006440090080d0021380848001d400d00000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 310165692 1250 310164442 310164457
    0x13140a0606091d0c040203091c080106031805070b091809010b0a080d09061d040507080f0a0b0a03080306010302040e09030c011506440a0f020f030109090c1d040201030c0201150506 79
    0x5d036120a2031b1549c9541411000184500006012000600c01c46070148100c1c01c1c40c80600e1001c10a0307081f21b50700c1c0c0782d0743d00301c50240f141070301e00100d9180da03281e0721300384120302c5280c05c540008114102a01c0e201d01900600c40f40c1032141c01f16110200320103c000078144c41081c407075910209040c0c0750420550310aa4501c440e0b00c11103010405207005070722240a03103030050000b551400b0142c0390980c414814614003408600b0003c3c00d081d41da40250b40caa0307100e07009603608606c0300303503494443c2001600240310301c0d40300420356510709003000015038020000e0808424080024440c138002030b0703442d94945141c0d0007501c01040800c0c159001e900c00c0b0500048100d000c2809810030f6105000140c48140c1c004800c1c00415041e19040000e800354a000d0380f050748040c540c042d41868140b251a4040d0f00050240710f0000740c0d1903411000380b04202c40c00c813000b4414000303a40c0103030344140301214584000f25000d80c0401e04080c1c0034540b19105101d14035203802401030510300c80e401d2408010995000d0750 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 310166942 1250 310165692 310165711
    0x108150316082e0f021204030f020609030906041a04030623130804030305030402010e03060a06061e08010e0405010906020f0324010503070509040e07080d0807050a020613140a0606091d0c040203 85
    0x7140b4141b141d1001c080500a43c0240c48204242c18106270081c078196004001d0f9210741c10512107069540c8461080d00c0a8991001d226084000c0304541a401030041342e1001c2d0070141000410f480d140003240b100002441e90b8841401e8039940c01c00e01410700d5211100080a5600070041000070078416006035400ca0300c1450402119812440002d00c0c042c02a2000c0744120b581d03120411405802403841c040030308980ca0980c451055030b4602400c0202c052140d0741e0000c0c500c1c4005810004203500c000c5600341d1001003191596510340b0889581e07041140c0113030f0504900e07240000e80e403014180c070010005050751128a16500e00a0840c4d003504070f01c1c0d0f40e503089034441c686c0d070030402020b0140c003018100c2c01d4001d0031141d112520023050410042c03d06420702104000e041d82c400d41c0451003581c8000600702d05188134169180000340c01d451801c5904c441d00900f00f9038410410703160409411501d05000521141594005c0d4400d40d03050109401c14030b03803011b6254181818250095a4400c2994 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 310168192 1250 310166942 310166947
    0x8041a06010e0f06070209010807050406172e06261920060c0c040c181505071a070e01030e0604020906030a0b04030c05100e0307020108150316082e0f02 67
    0x1d502142001f007013a001201c450300802414041420a4407500b0000e100c04106000a110340c103d03c1510b854029040d0384603545841850315000c01102c45a1a60740a00340041000c03969402030550100003820107101050150851300c0c240301310014031801142041409240c0e800216070b01d22000c401341c098030044403405000d24920641d1020050404201e00f440030304004101401004100d50350000c1c24030920400b40d8030061464a215003440c207403134400603c141c0c45075408038240d0701303401000d034000d012640f0b101d56440100710710000c1c907000d40380b15211290710480c800f00650550340c0d42880b810382035000c00c0018015182c07540b091a04518043c040d2509001c058071440b840d26800c0300c0540c003045c2800c4c00da40030040108190400441d42030008c01c410941c1d458466124499118007904104501d80803c201c9600030180d42038402008045983e03c000d25140c00c4c0d0340548a114500302406200c1241185014009440b151075442b000f0303007010320380c0030701941c1c0091403007000c5021070301c0d401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 310169442 1250 310168192 310168207
    0x60b1326100509071d0105090c03010b031317030106020f0d0f050a12020705030406022b0c0803100f17300c0a05100b090702010b0616020411030708041a06010e0f06 72
    0x990001400c0f20403900b0010f200d5030402041c0441402c015140124003102000100240cd0900c410b50740c0003180200282c8400c41e103400d0040c8801034030020982c001000000018407103400141c86641c0e041c040c015110170008082c401e481440f04c00c010341000c40c42c100706001c0f0144c411400c2c2e10303072222000001420120581c50342490741e000746d000710700580e0003c80740b018044100c50668103c00410001b0049800020100921303008829000606d071501c00f002040c801000c0315030b02d0024000480700103460a9490012000c60010a807201203030380213449d2040f54000560800301501441440c8207692400484050742c07080e400301411012034041d01d000840040e406100850304101000c0740440c986000804100c20a0700141c078041c01d6a150440d4841d6545488080d40c814021500c1480d40c41c216600224001d00a2400f0f42d0182002c000304000429401041140c000c5d1300800090070010a034250031090f401041d80c00a020503491003900070b40b0b26020b00054903810f40541414200540c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 310170692 1250 310169442 310169459
    0x60402210a0f0311070f051008040809180a110309060105010503061302030c03010302010e0402070203121309020403150b034c0b011b0209010306050a060b132610050907 74
    0x807480d0101d0005400d100e102008904c00c00c11070303003e45403560340460098582400107a81041140307200301030206500015051008010596804041c040c041403980da1042c0326031010f0400c00c5030441e58140c5024040381c8a1828071080d40e11903040140108034503401d00c401500d00b40c000509041e072240882c1910000400c4900245000d0400e40c20210b80380d505620006d8803a400f00028107004500c14403580c805a0b0740000e15042072030002c0b030216a104510240e0030b03144101c580103400407178000100041000720040020002c1c0700c0e03000041120b140c4007010141c6a104403a60094802c40c00c04090711400c0c203a150741141c41c0900c032a8108813001401c40d25200380c0c0c100c08446a40ca503902048045c039600b002c812210704201e007040f450106501d40c0050301611060001801c2159980001101a4481e9000a0150112180ca6512881803a182200091003801100c500052420340740e26800c01004246040c0c011010140c00c00c000300c01c030507034001e150082a100c058424220002051034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 310171942 1250 310170692 310170713
    0x50601181b180504050c0909040c0f060203030a0e0c060a05031905070f172802040306110301150903031d01141c0501050307151107050915030c03060402210a 69
    0x2101d4444885140d6407122002c410215540404e00031030521382040071140c5442e04880035a2070403101800581c50301e0030078201032000d540280c078191a2241e000b1814540002c0514410302c40c158041c000d100400c070030319841c0c0c0c0320303030f82c1c00e81c0c0024040c41400307021806a070285500031075236101e00a021680d4103442094900694a030804a0044400c0500c3c865000f14002d003920485d81c4e41030480d08016a4210102200e0b14180034401c030101218014203101d0340442e0010740d0014024400c0743e03034404009a003544207100d104e00311f4100e41c44001c0007034018540d19003101d030542c41c4d12405014045161081d0403040f0441410000041c03124000c6441c2c0e000645000d40503044020400b20302c981c08941200c0040e00118030907800b0310301c01c1010f0961590803001c00308691074206c43e8506503842041c0b4103140d070b81105900c813443c4420000b0119071040034150b002e030b0890440b0907070440d003014503488031425540a500720155503242103401c6141d0307001001c0c6644100446004103460346a025409 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 310173192 1250 310171942 310171991
    0x1120e070905010303030c0f020613081909061b02010c020108041e050d030e070b0f0c1606050910030507172814010e330d120f0c05060118 61
    0x40c0c0d0b4580050040c103034544641c601d121011f040c114403013080c42a01960b81c0c02e006000f0300b504403201c1c803200b040007101403d842010480700f408038070300c00340070401410f5550030303005040016128080104c002d600300c081d120320254060310f134816504510707001160441802001500c0c00d1034062041c80340a8207458440340154000c070083e00f00c00000c0c00009041c3d039850940140704d54080320082c02001c02d201d0440300808a4213a1007907507509003080f16420100c8a290a4000f140300a600040e0150030000512242000b22443c3e084240d810384141c00322070040c0e609000048228010040e1280c3d003107501900908102c400104d0701070340d2105400c610350318517003003240c054450b400304204010003c1940e0140655080c1140d41c0d2400904207811421050004916145008100c000001c401c1c154040b0511001d8103000c00620b503401c002060390002104100040c4803503003541201072144403c0c0303c0d0a07600c6006000a80d107020003408d829400f50300700c1c07085a580e82d0100d00b00784c0b14062210804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 310174442 1250 310173192 310173209
    0x4090506060f190923040203060f0d03090303020105010603020a080a1d0a0c030605330a151d04020a09030b1902040e0906060904020d140f12040503010f0204060503040201120e07 78
    0x440d20340000c00f100aa548400f00e4099030300340c030b20345c44001005042c0d018402541c00603103c0c0d0700c480004d089007240000c034580081d000c44030340081c1503011000300e045d00d020383c000344082d9981d03090031001c03132003100d0503a070004505e0320200312004401d82043c0003488440440036080b07400e500116040c00e00c40482101c00941c40030040003001000d0181c07a91200c942014900341d0940c24a4202011745909800744910354405079009071a40c0722103080002e4a601e000040c401e12900d400940343ca01c40c43c8078806281c1d1083c90000e0645030034001c94859550707030b030780b41818035107560f4a040540c080a0440000100f025140300308101092016000034001e00e180503945042c140e20440c140000a0205402080c42200f00009a00c03a0329440c4103042c2d1000b020209207000700c0c00c1500704461107850105500800600340c807000c0c000340140003550300440007005045540301029003288128850180070660500c009400f540c01060320300070803410b8440c040360040401c0440c3d0704008864024014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 310175692 1250 310174442 310174477
    0x30a0201020c070b0705030306210105070c050609061b0f1209030a090f060503010b0304050a050f03030603011802030d05160c0806071b05060105040e150109060303140f04090506060f 80
    0x281042000c1c030b00a242c410403591404c5c2d071075240d481e142d02c00140007600030801700381d21240e040c02590000302000e40f624002c100c9402c15440c0100420340320306d026a0140300f0080402d4448002250042c09295101c2900344580c000c01000f0a09411814960110b0f02c0700b4400404d0454000e281c5510034040c55001c0d41e40d9001d080e40260100500e0f42100c80c10198546017803000941010849056407500d081d000e49aa40f14541a0303d4020003a0000b081c5001d07031f0241c613007480f200102441c05000201e0003403041008540f4101d01d80c44480d2800387d80f55200064850626004600825541d801da807120320710114282c99280b2540919808044103034426010070482c00e034005c15000e2290580780080242000f107880390b550702c407018091284a1983d643c02c40b81a65002c105070b203259816001802c0c003a603520340c015001011180310590201e56000c00303100790305500c0030403640c4041c0c003852098149810442e0a000514006050a03040302c000c200c40c541015018000c0c0c400712034183d5091a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 310176942 1250 310175692 310175707
    0xe061209030a02010e1204030303020d020d0218030c0312090f0a0503060711100603020607030e061c050402100e09010e0c042409050a1202010e19121709010801060f030e030a020102 79
    0xb42111410880001d05800c2151400c040d00d80c06d000302c4084a0309481c0240c1c03299503604100000b4420000c1440300b00b4070000c4c01c14103241a04c103110502e142d08509940c0070344c00ca60181602d842101035024401d08040110b010b00307161595034445003140c094a421b0805460300e000ca840c0c00380545c1c4c440c020a551a592601303034481003250303010a03407035800c05005551070742c0e012810303174016010000d042c480d41354141c90845d201d18080d41e4a51a60011b0080d006040c0704411000705416241039000e80c81800840d03000030b010710f080300703a02c10f4050400d400307981c82d2699000703c0090241c20a1080b0a040200040301c69000450008040f040c060b41c603d4a00810400b510000b1a84e01c0030b40680341f10b10b4200302c0f8000c003440f125840b940a0919400a0340307842d0010719154002081e1500b044030011010840c001220011a41c5601c00d040c540c1c0c24040c407611000042c05600421400150300800510100e0700c2207a8088204207981404245801c6020540d815034219800103030050f1360205060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 310178192 1250 310176942 310176947
    0x20c011d0318010f090501030903032007020a2c0c0702040c0905010e240c0a0519150e0303150d0609030e0a09050c09010f090e01080a0b150109060e061209030a 70
    0xc1c411074004d007032100019007400400742120040748a0b0380e05142e0380e000140140340c082d030040004c511202030345c601d20180110414180e600300300c0c07050b4003a04081102248820f801c9620111000304070f60020000e10340900c40742d4106000a080b82c500000501ca540c1c0103880f039002d00303855070100d074440c0c0d120b85003000001446d104290701c01511682c1e0801e40282a2000d4061941c0317421501d98403a662101c842072003070318040404000518070700c920f142c80c9045103c28000c2c00c081c184101c4480112904004400303040e03451031041a5203507041000454408429010090300c0c0c0b01c400382070590824841c0e107600040300c0c1e50a005501040041c00c01e405180782c0000100c0c05828070b040b040250303041c10001c0b001c090041d20f0205040c8003200c5880c0d207a4a00580e03040d00204042c034403602c0340d50303107480c907845e2951a0b000301224041070020110390401170250301a00500c0c0d040c0d56a000592034640b040b1405011940e005030440810802080c900200d201c100e441908060000c60307503000c141000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 310179442 1250 310178192 310178227
    0x20240f0c280302030f07030504030e0108070c0213020a0801080703050c1e040f091101020a0c150c0f05010c2303070c11030102070f0b0903070f11030102280e0301060503030904020c011d03 82
    0x5038801c142c9070402700300020703804c628004034034182841c1080c030f5503640c1e6005076041041120040e50088030101e5074074108000e40c0081481c01c101c2c0d81c9004407071360b0310b139141a034800030350100030419080502d808529044c04071004841c1022045e43c0c01001086502050845502d480160500f03901c1d4240007060190a00ca40385007240300388010003d034403141d2100003421000b0b0003001d180c07902d46010000824420145481030680240042d5605505440c000340240030400e180b43c0810b1503141c04e1304102e000c4000e0b4940b009103001600d45982e95019003101c1003044100d0460360030041c0003a0b022652403d101a18810340718103500e0240d0041820b1031030542c030008080000990042080c580002c551130784100c14168020322040ea1200c000703000a000e4040d800c4100c440d04846401d00781290141d01d8404480145600c91a09031802e440525090341c03841c0c0503031fa030103600402c407103080c41c2026030040418600c00d80000801d540c0101801030a528240504d540c158000310301642079914421a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 310180692 1250 310179442 310179451
    0x1a091312090f0b07080c01140a060b0304080409020d090c14180c040303051b0d030902090603070608070e06070c080705090a0e070504050720240f0c280302030f 70
    0x5001c00303014500041e031440141140983d420034000481d500003000b03031410030707610700f2010a4024407035040ea45080d10b003074002c1225500b2256040c070200240e07040100c0c0469000d80c1d0015000340c13a09040440300d001070750180c00081c0504c1d81d11400240480c0c05295080c020701451650b81c00b22031208003c011140d0480c00b2049401c0048209024041c002c030001c40b81100e52506007107840c0c1c40e62080e4025008100c0d40005c1d058041c40740220304140e4990b000810441c400c5401440a894100c14103030f60345054040c030008203008a010131303107180c0580d030303440304042006040d41e141c10259550092000034503440505290b000b180e041c8014641140880e40c420b520240800009090b140f0a60751402d05103d0030380100d9071900407400803031080c400104403090440328000400180c0031020743c1c1d83c14841e102082c00386000340c402150401321520034009c00d903c11410941ea161401d6042040d1f11090604e480b4400c440c0340c44500d80f07101c0064a0030020340b0f44005840307142c01801d480d40e01c14010b1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 310181942 1250 310180692 310180697
    0x70b130b0c070314030f0c03041a0310090519020d050115050c06160504030f0c0602011505011e021e01060810020a0203070303050415060e040c090e0a061a091312 71
    0x44640c0398500003034441d00b1250403240e60070f0b01c0510720304131a0031441185040d94000c0300000388540c14140000061049803542403032880300d0034080c0550034180c001900d1104440b102c00000304130039800c582049821800030010320006200c00c0316180202d91206580581440c0c03500010400c800d0300c040d59107568142070601c01c0c9800b6001c089070707803254001002807240152503003480104d1071048007580c1c05954065202440d0744214249086152100d00c5031100560810b520562a18036042c06070341101d0f010703150b54480c010240000d1a04500300020f12045201c0c40f44410814600034041810100e450030000640b1400c0101071070070100f001d00594116070040241d60a0964008111002c1c1034141c68001400e484600c0d0125200c80d034410741c07102540c2460004144030591018080c010381c0f2a4620390340c00c1d07a0301c640740025150451008540b5402085804001c0354168100c040202c0001895100c13600360f940009821500039150b000000e251690000c0800c02d5408804400c6900c90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 310183192 1250 310181942 310181947
    0x50a060503010608131401050a0b060c030406030209040207120f020f01050417030411061c0509061b07080409050403080108240c0c1002030c09090c030103020607060b12070b130b 78
    0x588184410f119620030481081d0014a14a0760a20440c83d4180d111408500d07442410070903a010b0001580c031000750324a070176510100c52410200729811412114099410030b032030324009800075004904125001030b000c20841c0e000a00c1184820000007041d10f0750685c25011480007440c100c1c11192044040c0c3c5070070140004039a502d004406a401c0c10600160f41e56114a00082c9030301c01c0303a40352a04008045602c50301d00000c00309840080c10381307075001c0050b80d50b0580255620842031b60103507803006000003840b22442250005100c030324003922941e4986540d81000c0f030111041160207600103414080144040c030018014682c045041000310008100400600009408050704681d1444400110386004400c14807841d0301310384040c0360854484c6048100600980e1104105910401d2400d0002d20011101c0003940c1c143ca40140980342040030507500c01c40180352030652203030b1020f92000400684082000350001070030035404131940781e00c402241c1407803101441c0c10040a08405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 310184442 1250 310183192 310183199
    0x3020a1214040c0b090117092104080f0c0a090b0d0c0828200114040e04120918050411120f01270b0c04170a050705040c1d0103060b0c01060f050a 64
    0x1220312201e00520401f100c0e480c1d04c500026910300300305008814204400c8102d41a24440c4100144c030440f09460300340d0780c002661440040e20b501030030f0420f0ba44961310100510091107282c0c8030302b0300810301809102d40c030440c0c3e4071958448a19584410481d0740800040d1861002c440c00c492045003107044d41c8141c1c18500e50301d0f03841c080780407410607200380009110072205038441c0c800e65110700f004248040e56941c0740d003091840034100710f40a6030040804c50b4071386006803080d1402002c070349a0019500008214610f03680c007408024009072030034040e5085e404080c1d901d0203a004140702d2644020080321800c08080c80c2941d81c481135904c001d800f1203200404890714000005000c42e4407855800e040c1c1d0b40d01c00c0000280c040e580008070309000e64001405400c80000d880d92805000c0c8084076861903070b40c000c020540d0b01c00b503466000213412078111a598040107001c40e8030050b0505003c03d2041e22114409440e8001c01c19083d1030369111641003081408400000000d0202505e030715072481e08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 310185692 1250 310184442 310184447
    0x5220b0a0f3c02070c0f0503060106021213050a1511030309070515190f09140a03080a0c0227010f06050f0307140412030201050604091203020a1214040c0b0901 70
    0x2d0080700e20140c0c60340807a03001010411600d00c90000340700e88000c42d243c00d22400d18801840d142c0c02400c08800b800304001c21340d490005603941c12502140d005092151482c0c0710107007560031040302e0004c5a40c001c000410542d43c0d10302d848014040c0b1181c01d400030000c283c001000000c903401c0d000c3c0b55800c1002400070078400030500100740c80064519580880c000c60620701282b04010301c8402c000100c840142000e41c0c0944044003800055503030041c00360303c50207901d00c289142028254824001082040003820820103032501621034240107840c20f0b12900171070f084038040180110f00300c40141c403085a01c1821041d041c098410307400c0103d661070400c0c20180552080c1384525100034404000580400e2144501c5182c1e5900002c10b50344556490503004a08000c01c0000c41c055424000043c0907030a00740704105060380c00209000c0b40504030b1000b6070080d400a411b02c1c042084803941000c0003250760140c018074882100c140c110b640350508007040c001c40ca0f0340004c150b03a0420003400745540c0c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 310186942 1250 310185692 310185731
    0xd030503150d0c05042a020105040311010c080117010f0c030e01110408070605070215041e080607020d050a0210091a100e010302100318050703170903070905220b0a0f 73
    0x1513058800142c0380411b0214504209024501c07007845041d901c1444240a9040d080140075a2080d122111017000079a0000d00b80c4114800000004084200412200a164060352002c90303064000040d2a07607020f048000340c400c1e02e000301c400301c1d03145e410701111007200f44245240042500b04440c10300d81400000c1d510340380a403003014104200450410155a00c10300c2c0841ea80b01001e0505030b0f6150f6a0351050503444075130341c413003550601c896030004980001203203007446400a54068074101c014100155240e80101c100501184140c0e003070442034910a11030746000382c2c011518100c0e8028201940004803c004188004401c11540c1c00c0100c9a40b1410190642c0c0d4110380c80d520381d124450040f401000400128020300320f203501c11006104021030888160381c0a69200c0c840708611144050152152442c40750b05a030040034204459502584426000098100c01c41c0402603458000d2030a284000000e4400400b290705004482440f07201b00340444495034002d01c0000003647c800c034103e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 310188192 1250 310186942 310186949
    0xf02030d0f0608030406170a06080a060f0209030a0317090f10110f120613110d050a0e0313060305060901060c02192301020f01050c0915090d030503150d0c 68
    0x2030361101d5620001400c01e80080000d8910107040700c0d00c0341c1d43c4440c000d00c049525a1060401d03a030100c0450881e0711140140d0b0107896200e0700504801750103a540000a120880180c8442507082c0320104907a5000d001404000c1d019a8607400080c0040038000303800703036010b80440019030140b20301e551070242c080f40940c015510b400c4005901643c2801c4948280b140703526062112000003440d0321a100380c108070034007525081e21200b004001e00e2013014200d48106021418014040c0181c030385400841d0007090b030007000c80c0740110ba001d550400d56031542e004000a02851180d6040a011181e4540f26480c0d2014040ba00e6a816500d003d2002e8020664002c006c2c2c095084482011480526080032800a1014010f20111032600b025040c00d9201490a8280180107510f20076005040501900d401910541d403408e1900300d04904002404030b5174986c07400314500a00c4040350564071202542c543d540652103480d07803407504d8141c494512a140881038420500300390720602103008400c0c0941507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 310189442 1250 310188192 310188217
    0x1170f03071e0309080303070917070608180c09090309010f030519020726190e090f04050a1401060f060c0b1b09040f0b0406270c03020c06150a060f0203 67
    0x1c0070642c02c0440d502c03904d81e00f100c03245202c000288005d8a0740040742c2822512440411111201c501c426240c076441c0d01d00c112400204502d010a052100b0034205c203181035039003030403203c019980c540031a0039460201c445401c0c079003000c0382800313080d600500c0c00c0890740c800380f40410541c130308030042050300c00401c01001111039010600c00104100885019254040c1c08040a4000600c0c03001d1a456440850004040c041425540b0402ca0140044181100c801000b030282aa6041800310080c8402031003601c280c40307240810004684402d84000e8158034800020820034141800c40c901c1c0e5015511500030003a58903043c0c000f06281c86602c941103a4410141e491080404190050301c2c0203d01c1030550003841c040a2030900c50a83e400306d1107900f002d640a03c00c00303548020341d000788a07500e4181540c0300c0c41c80000b400741448a42c0401d48064141c1001800c4c9514020818a001d9017210080005d00b88004000a180744c009600d0b00100b0240c9895091031840400094407801861a000030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 310190692 1250 310189442 310189493
    0xe010e100302280611100b030a0b0408091e01021e0c03030d0203041a0705180a03060509030d050a02163f090504060e04020603040212010501170f0307 66
    0x114060030480031001140c00038094a5107401c12910a40d10030840f140c1d9003840742010000241d098003d40c0071150015444000d443d642001c108408003a00d200c8401c0c0b035143c0a82c0002e480001c03110443d00d0301550144110544520120b400d110090403146034940041041100b1680182c3c0d0002e00403003180c6000406034001a00020303c2441d0904860404e42d040c04045602c0345c070040c1c541e010798803550040c01e1000318809003203084981030b1415503000e00054000c200d00314000030041c4414485c1c68001e04501410380d079a48464044820559020000d60000100c40d100f6010038010580c1007031400c8411403400c03240c000e130343e02d40c1000513400800095095041506e0712060400c1c05903004c007100c218210b400302d841d071108440200b1341c92141c085240441d01280d2800c0c588101e100340d0788803603441d0030561150303001c0010f1500b00030b000700d0384000700c6c03052002c10ba4400e016050007013100350400e1b000a0b441c41c00d801d060450310a40d8006684c4140050004503185004000030b000f4490504031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 310191942 1250 310190692 310190701
    0x22214060301120f2a0e04081207140d0911032802040209100c0b01060801030302060f15100201020903241302010c1b050a06021609050c0d06030c03020108060303040e010e 75
    0x900c9001c840001c0c0c42c66840c022010304030010345d15105001e82c0c40d04500e481d26612203549039800e000980300070b0b010b030000b8010a079030311010703a0106401000038240502c0c11482e010341c2c5051030f4401c00c0318400c9203843d0b400200c100800350090300303074514085000d000d16100118102443c030b100302c84c450048001c0307580410f0964540340d046a48c104800ba10740003400e808040003808098000904454600074100005903840c460881036058030b52580c00341c031940c1c49030320054000500280007034041c6128a080d2444035550041c00c10343d00041ca0b000503848003607400425040c004030003403060055504000c2402500440540d4603407041c0740d8031019042c04418001200c1c0540b4a40d40148250003100c0c82c1c0000b19107020300c2c0750483e46c0c221400013892b07031905402ca80382c400124101002003d260b406000c0781c01c05400203507000405860300e9082031512480141581d91691050b205500850300900079941e105000c0c0351f1107802070300118507040c42c2410140b1010014881c040f05d0340035030000708 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 310193192 1250 310191942 310191953
    0x1302060901111501170a030f0302031b0304030909061203200a0b010803041a09060a0e030f07170f0d1b020105120a020a020f1c0507020604030602221406030112 70
    0xc80b41c1d2100000702c40c0c200b1489600300f20000c0d02030003000c0c40d121080c001000388840c00104405101d6041d030394000703400c4103c02c095002e500301901014040440e1a02c00c7c0d01002c11b0300240d84584d020f80d03a008469450145280e0440700c0540044140102c03c150844c0420340100358003407203904544d4035068a2009400003070811102c3c040081007004000000140c5581c004040e00540b440d4901c1c035000c0c0502441a0103451280500740c5401c804148110007100f40070f542c2c1d2903144400039064641c5c159422800e40d0a240c0c1a4128800420b0300b07108411070726204100946905202c180201300802509201a103261080b2100e603144a09824104046911a5050350a441d01100042016003030074604440650070602c4848014464064031850166000520b058032080642455548081090b400c9800350301c840780c140c0c0c00c403a08100020000300284010400030b60f01583d2030300015170034800410506810380c42800c000c210621500c1140d0b90340700840b4110741c81c80000707400320b043c2464007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 310194442 1250 310193192 310193207
    0x50f0615040b0304110a0312030e1b1207090e011a060702060f0a0311070b07300e0a020303070b010806010b041a0702030f0d050301050a0b0301120803070c050f0a17031302060901 78
    0xc460f0001200c1380004108000090a000e000548d41c4050001440e6505440c2c2e491000c030105c00a500441c10410f1070a00b404241e004c0704100c0385c0c06880c40c3c0c90309d0300017520a8441c455454015a0340d80e00c5412980c0c00466040c3c00201421118245082403070380000e5064000c41102c40c54003800003642c040c13510f01991020001c0640d40c038505880d510641015201c404003280c004d80451a881006401210310031030030000440c0701c000502d0502c8400f203420300144500648003605209802603c80966800c10107030210a1140700348080540c10002003900304241a8408040c10009000174088050302d80d01d005000c6521844040e11900140002031901c8001001400d40c0d020310907042946517800070023141a92002d5541071255a0340b48080a00c41c8001d105581d01006000500400a80d8000c01103070014282d140114000070562221400c0030b05808000e111a80080865000c00580d0700c1c13000d0070030400c1c0308054191b181c030b0607540c0c80f40d04042030024868280041d840645038007a001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 310195692 1250 310194442 310194473
    0x1e070f02010818060a060303030e011e0b0a03020613030c15170408090402030a05010905010f1406030601090509150f01050a0c03080a0e030406020c150f0403150603120201050f0615040b0304 83
    0x4c5032414200302200400a102d913000540000b414544825031220050003855201c1c0d02402842c46100c00d4280303048001c0032043c11250b800100c4400010140c3d070b60f00050100c9841104100d0a07a034610305e0b09081c0c480d0564060450303200c003070341c02c1c0e501d050300844250151400d07a136503136110340c0e65468a2070591045002050f80b20b0b01c08010f220108400b13510050603191191070411080c0d80b21400103144880320300c210000d810800c40703400c80e5400e08401070f40c0c01c000c040c100505440d44440008803280c0d01252070225003440201910813a284c04601130302d6884080c03c5c441e06e8503c4078200142425840c0c074015042c420020080b0b4030b503a50990001e07803c7d2910200340c1e5129600c0e003400a49500c00c1100c00e520490135818074a0500030784104440b0740e41ba03041c95030303403816145a5403000c1c440d1800c03e21092455031960700001040500450301640c58140e80002050300e4408860410310784d0240c05503002c1e48940d021051451100c40450b4184d40603941401d0b1641e031f840c500314800e4000c1c0b44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 310196942 1250 310195692 310195741
    0x803220501020702030106060e2209080705030309011a0609060c1c0c0308090726070e01090902090f0103030905060d240f06030509071206140c1e070f020108 69
    0x886540500c001036002c3c0079010700c210020310856640704800c64038500081d49860340455914044080c0750424088501d568080c0803020411140343d4880c102160010341c81511103800000401044200a101c3d1200c0705403840c210014a554110100301c1c68000c201443e40243c0000840c402e814400300a08450518074001000c00300100050003010050750710811004141c134100460b1300090042100000d9500810365034140d040e000c0a28864001ca8800500c5607001d00000403c0e49441008854060b002003100840c6d05500e92061004000d402850f0700d61511044006000081e03003c81d440c0d0484400300c80141d111489a10b42c20020305020f80300030317014151140071700b15040c00303050b40d03100315581c0c0348039001c1c40c40d51007074194140c1c1c000719000e44403504030a83c1802614081583c80000a004181c0001c2c2c2e140b84203900c03500c180081e03a00e25040c0f1404500c200003035040c005904003040007010000d08000d2a9520903444140010000f41448100400604403c3e010f10306403040001a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 310198192 1250 310196942 310197001
    0x311012309030d0503040b06010309031b0c060e040209010c02062208010c020c03071401080a060b0a0306031509020d0b04021914090f01030b06120f1b040c021204030803 74
    0x340409591540041d00c064020700031030f90b148007103602a4044d03e1149802c046411850340d0743d040110010b0440e020100e041c008050f81d07800c5007680c1280413840d13240c411070f01d8041e6542400c07005494900c210301010700c1213004018080c13507a40d00034417803502554166074280c3c1f00c442019910440c112085803507a40c24001000000c3d841d80150805089050140c0030359054400c400c0505454180ba0300a00704040d141d1181c8600d02d5110307106280d801101140001029078407400c051403940e022603c6040041d4440b08144280305001120f104001003404003004030548a50118036080305904000c0c0541c80e1600000f0155100c0000101c40060311440350351003070307444401d0039501907030b0a00e0484c01170494000048400420841960680f60030070403c07480c0d5900e120402003009900f010003961401641000c129032a01000701315503440c101d101012071b0710700b05000e200c00c0320900115141198410810b1401da020300320102ca003500d400002c429520380e100b80070143c040d03003003480d5000e920001c6c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 310199442 1250 310198192 310198247
    0xd030e1210020910080439031103070602070602070e04060605092a0a0c0605060d050105010f1a19050a17100e070c02030631060203190510031101 64
    0x50b030040501c1c400441e1038000c1c58010f03040842e9084c0d001c88004001054a0210f120003490145002101000d9295401c1d00b52134910748144e030f1403581d644100c1e00580204100121031a0501046010382403901c001d03e0428074091b8025500c1e4440c3c032407040c11800c03034004241480b8807034118001600d00030780f030b41c403160804c0035200107550311005400b4001c601800612640803400b20854040c40165510016015401c0d102d0000030304018140301d42c402d00c0c0c034003540005a000e005450082201003620040c0c10f207461001c0007001d04003080d5070003144003044481c80e208100c56692540d603003d85486a16000f4109058540384966004e400c24480c0d90000c01c40c128130111081070940340844012191525000030554618250300002540f54000d40c0c005084410040d6064468442540780307a01a41c8001420400300340d4405e00649240750004100301e00c9074803540180e8110600b04030308200520f8007036444803900045000041c0402000200c205840e0310421181c41c0c02400c80540c041001314 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 310200692 1250 310199442 310199473
    0xc0d050312070e0a06080a0b03010e030c010c0507350c1606020309131e1a09240d03050f1603090f050901120302010603080d090314090d030e12 63
    0x80040c000e40c8032055030002d0003541c0320721a60071064901514100045050050a40d95020000c0092120f25074032482400c041d6024000d601000340d0300710186035680b60001c12a402d40f12200701c0c40d0248402080400c00240c60250a180507494811405404020a0f503c416a80c490035124140350180818002e150701004503140908400b4102c1c2007000070782d1a071003a6100d00552046503803001d5168010110f940d125004940300c000820801d4110350002d0409004850320b0059070b035851907031205c0040c4107040c00c01b221608500ca00c01d41c1316104901070245d04214220492160050940c0340e25981010b00507416250180080d400076a01d650172607103039007031182c1580d20a03000601c015400068a445440d001070039078001602c06810341c0c0c20017803050740d15408008110119940c620000000c40c0c1c458001c0c0c078180c25285c0b40032031000c28504000b011000f9400c1c1c3d110030311108000c812101d50310000034640090381420013200307ca40c1c0702c00107041000001402d560901440a0020b181d01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 310201942 1250 310200692 310200697
    0x13140a11030601050a031109090102041805060a0806010f090c05040911070501050c090d030507110a061d0307050f01030c030e03030c04170d0203040317040518091009030914030c0d0503 81
    0x20030a80032110103a80e540100705c92003941e88070180c00080691440d00d0b09007130040c496544844854005072a0956030540703400d041420400c0382c1e1740c1a81c4c0e0340c240011840c068265000414100c1c1c0245150350405c400c0c00300b0740100e803061101841d030b140b200401c0c6a015000380d90091502580c200800b03c10018600c45070350010b202101c4c2d5501c1c01d800a4042032880e8169401d007140500322030008072042d581510140d100d09015100703440e400c81c8088a40c1c0e0383c040c075100a00010740d50300800548910808518030700d9204c04501c65000140103109589501200c000032501c00d01e408034051143c40820f40040c00e40d0910107003540000000c010840e4140001482107500007080c0c101076448100c4855101c21840c032000300180c104100030808100d0342050b400c80008010000c40c98203982c0e034000313000610041900e031140102041008840101030048c10036141449c1014450003c441d41c000744448814064910044c0b0100d840300c070240c03010000c15540c0f200180010f80e41c44003030b061841e82c81c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 310203192 1250 310201942 310201973
    0x315120d0f1223070f020d1b03021002031807080a050c010806041811010e240307090e01030606060801050306060a18020915091f050a0302030601120c03060501080c040e13140a 77
    0x10303d143c0e0b5245c994920004187d001c2c41040da49510b01c03903003403e0200e99255030a40c416011031107011111035507400b207803000f9802140144032000748505400121414080c0c598008140c1c0d410449003d40031500204010004040918015000344d0391900001c0c000d044076800a81d40c0081c110300e640400c8402141000c1d01142603c46000c48003041e0100858a12022452aa076031004a5007400c02c401c290007541e0080c040f402c0c40d4007419120b800c007441e0104242c1c419285280c0f10700081110981001265025200c198040c042610388076001c500d2071845849203100d80c0c1c0c603041380040e44a8403503050b1410210001d0003680040d08151450600382c101070450b40c803400300c00c008000e00020780f1040000001c455280d46043c07440044003500290801020141030140c09105041e80105620610090505588000688074240f80c001454650020240011102d0400040c0000005d031851141d100d1810050710b2100d1045181c5003230b0780440d03005c002031a8469092100c04000182d460300520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 310204442 1250 310203192 310203197
    0xf080109020d0e0129041a120f151b0412151b05070c05040204030203060f0a0b060408031305010206011805090a08070b0a0c0804120305070908030315120d0f122307 72
    0x11701680381044102d6910140048642d84411460301c401d09000203128144102101074520303e0407007085031410030184030701e000e442900001c01c208081074820080a4400300ac826a00c2c100390400180458819440b82c0240c00e00c1c5e010184621900419004101c080313141111050308007109210181c10740d001580c085540392a03080011420703042c94806e84003100c0d0014000c0c403d0782c5580260800c200c01c05005801d01a44034500e418030340e10707903100910080c0820f40003169103401d402c88a6500c40c0041d00803a0441d005030b00100051596a003400001c2000d00c0c4002809458001c1d84038540a070304c160051000601103a00001c0c00b1140380f03024401c0c1f00102c000d2050966007070b4102c0d55000c1c200d90082c0103104a0076030300d851a00c40d0340200d510508034100340010036203a800c440c1ca5504112017920300400142c01103002414405003031030500d03503180001c2c001c058450a01502c0101b280100ca420401d1068210003c400340342c10400b00020480411a40308200f000407190862040720310760302 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 310205692 1250 310204442 310204511
    0xc0f1b0b130803031b0d09050d0c03020f011b11070909050d0228201305011406070803150d1401050a052a09030f0313050901060f080109020d0e01 64
    0x74242c4011044030701c202c1d05a64800950008101c0c40b1106030092600b00c0f218540d038a5100c40059010800b11240f003403251120180d03121030b8603000307280a00045042c06a80d0420312426403031203041460301d80a5000d82816400d1a01c0d0076074861806100b6440081c1c802d0074050384200313100c03010445418044d040e03800d440c411140b03c024a03585040c0f804003808441c100d0344240c0b0128850f01100065031120000c20700048940100090204032840030500303e00c0c1e540c5004111446040e0800e10004105803806d40c1840901d4032a03607039038003004100345000d41c0070300182d402da65200c0200000c80344d44a0440107030780100d80100341c000d1408031207013280c1c1460301e0f020400342440003103021000018524582c4001511a004100d150490b540d0950144252600081600c2060026201111911a103001c64901c0d14042014407141a48400c05203c030040c2c00e0704513140d208032403034103480c0c11510142c1d4681d41c455240e4000c10750008540c007107520740002c40d1a005d02200d8144500d8906207050766 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 310206942 1250 310205692 310205699
    0x2a09010608090a02060f0403080a03050a0f090203060a052503020d060e060f04090303020d060909020a050103112203020d120f0f050403020d0f080307080a050f06010c0f1b0b13 77
    0x1e404040036900a20541d1007201d41c0e00040c81d0070340040c001c8180b0558550b081c559640d44184894200c1e0400f040883d40352030800c1602051803041c0c10000c0e01c240c1081c000008680c0200e030700c2d03007400380c040300000380c4600c00114064141c52101180000703508500442c1d44050300020025008820383c10f90003030402c01c0000c0c10340c501004450040c3c10080900441d903203e44204801070151941c218249030302840318049694543c41002c0040c005040049180c100380c0c070421a111140750071a50526240040103400b2030348040942e07509040c0c6407214444044d01010a12080b12982e20080d40840d1418a1070100b00c07000413021041001c42c1c8448500c0081c000082d543c171480c4010000015a090000300b02610b002641510704038010340c1120403040702911101c4050b4000c070f0711000441e8403002844103281c3ca42c4510303544022140d03d00c40103400d109000a181480700344010300303200384202209003808040e83d4803038100300700d040a001d4000e40e81c040413052500608155040c01d40c2950000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 310208192 1250 310206942 310206947
    0x50706030605010807111002040b0403051903170406021204030f08090d140a030908070b1f12080f09040e060105121216080d0c02030301140301021602060c2a090106 72
    0x80541d24142c40d13144042d516a4012942c1a00c2840107030094425501948554942071001300041c00c0882d6140b80c1d2903086007440d40c0350207503202520038200900c8035141d006c03940c0b101211054941404180040791142e00341040a03000d07514046500004400c01e00080680051100c10071b501e1079100e14a49580319a010394441034500c0141020500b00170000c0848090f000c01008000441e00f0001000f8032541c8506245400450003180e040c804a401d03c80c1071f4800c40410700c84a5042e01a100446041014660200c00c500e140144031281c00300b4a03072504070440f000daa144400c06801000136250000642e541d8890a10425000d07002e030201e11032420700301140100c220012682c4540c6850201c54070b2a48440020400f80c6041c2004e01041c0060302c401d02417802d0800c5d86038011030f125410101140c07465010310407110310980c0b04000c20300c4607481c604100b2501c2ca404540d40f17516000060801e03410404640080c10008801c1800310000004c251080080520243c07111200e41ea00e65409 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 310209442 1250 310208192 310208201
    0x1005011413140f1c03030c14030112031e021c170a0501030b0903090108061e0d06020301080709021204060924020309190b1801140708062d01050306191205070603 71
    0x554807000b40004c0d0840200e03029800a2281030200c3c0f070208600c1c0910340301048260004e810083e012404d80503a0018180d02c8003e082d05040c001c0c4101d4036201171000301135500c104030249041210703004408504094000d0320560b0b12680c015510100e20725080704a08000c280900086402071029030109942c52400000d0f41c00715001a11140300350707225501000028560100c00c4030900c0c8030f02482000d0741e102c030128400e0a134402c240140e00d9504059055040c25100c1e04680034a6106011265220b0b00401541c0d40142e0800301c00150540c850070100e10701101d83d220140e45044040c055191240b881e40110f200f0145041951101e922042040300030141c41040a4510090040801d04501d2a03010301588011051300004050301e8801040f154a0b00c12075095010039801006c20480c1d040040b038009200319508030340381c490a070500700d44588901d8032004a040000110001d5483c4c2c0398051034000b220301c6800c615545d03640da803400c4001c01140b002c04950601859200040e418002d00a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 310210692 1250 310209442 310209469
    0x121c050307051c111c06050904030f030c02070f060f090b0f0306011d0d0f0b0604060b040618090608031c0b06070807030e0d050c12061005011413140f 66
    0x30344030f141c0b902c0c412100251030003900b0384007003165035910880da4100c00400140020039a105a2000c4002d5264841c000c07900a50700050050003004108000240d02042c40c2020040c18200001d100107941d0b0200d00d4450035822040152010410100e0007076001f141803455001039a540c40c0d4460b032611121501406140d80900c200346080c000b24280c8c4d07018641400e0fa0139074500d00c00d8003d0380384900183c2d030100f00607015995901a00030000c18480c041031440c2c0d01100136501440300a141031404a21445684629010061b411020354032159104040b000182410003042c800035481e880c483ea02ca9014140220010f204000d48007484051401002154034004014904200342074546240070b0b48003101c21010401445c00b00703c525510708201c54061401038000709100e00d1131009221041e1281060000f142e4400e00400075a1200e606189080c0c075020310b00420101c030b4900b0f80d0b00c40ca00488a0050804205540100d80e8044546102d262540102e4029610703541c207005200000d4024007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 310211942 1250 310210692 310210697
    0xb0c0d11100c1206030f0309090e0c10020c06030109050f060d0c06050a0905090a050115020a051b030a15020712080f15220504020307050109060915050405121c050307 73
    0xa40340d5421040c030754816281c8020500f03200300068840c90188045036150b4200f10344803d0401d622500785540248460042c00d24003808110110302d24004550380c08607100c495100d000c1820016414a200340580c0d16084070103090325490f03585500044001d00002c488030902e10a80000042c070300d283c911030350340c10650011a414501c900748002100c1580c41a0700c40b9040c4038054000185680314508520b114110b0414006400d5051946091403103502c2501c05045501114014000c54030124040640c56506803106484003036100c0800d051145819014001c80d0414806121108841d0002d109080c81508034035040c804a4800342e800041c02e0350704e140340c24000c00c00940350003881141c4540c0c00e00010007041c410710b0504089440000103158011203961070740144000c500f070400002e40034020909001403e2410204001c5c030800441c4034401c44034440d40c98180c101405202224003404d00035280c82140c01d900c030b805a955074068520000c0c0750901414100103e8460b5042c1c034080c2d412507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 310213192 1250 310211942 310211953
    0x33504060e030412030f0306050123090f09130302070608040b010612240603050c071e03030608011a030d1d01050c030409060311150405030a020103051f0b0c0d11 71
    0x80e00c6890090240e101518000d220400000ca10100030b95622000c181c8250344100740d00003100002416125a0b901c02d40c14490454a080303c0400c500085224500c2000d2105032201c00060000381040a84107415801c0b010a80501c58901c1519000ca102a4003d400b164025540c6001c215510401100c0161002010300014401c0d0791280170b040c1200312a907640400e16441c0d03101404800354011041c418901c0d1007643c00c00c20640c050250740e03400b413140c404031401c00c43c4540750401a40c48a00c524117061824080e58000c0501981c000c2e4042d0418500811160351061101040d50284485051181c481d040c540c088582c447c065440c919600c1442c0d603009120060010b4405400180314100240010f0002041084241c0318200045014958200b620004103050040c950018150542c00c05d13400c0105000c0d42e140040c40001c0c0341e0703081c0381c001a1036542c1680300d501020083e40807030b01c40140060015020301c1c41000740030180c0340c0302e0a0302c2d14103040300d100755030307514450b0485903058000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 310214442 1250 310213192 310213201
    0x1091d0604120c031101110d06050a0b0a0f11010509150a0504020d110406030b0c030714040602031e0403081803010b2e030b0604060302040e0606030f0a11160335 71
    0x3030100000c00f5219081c4007441c0510030807031500752910040031070544003010a2258559056010341c9000b440c054400340407144c180b056540d060b210b001b6101c0c050140034450b8100c0709100b40175002c51409048020003243c20500003194543c05402c15450700c084076000031442d490f080b446554004da900070b01030580309440382c0d00e00d06902503080482d0352003540c503c00003022441c00c1c84a18071590070803540d90b07901d203070140c00078240c80e20917490141c00000601050203150b03000012078900d0a0841e01d46504a52900f450300c205102c1c5400c000c10324900401c64034030381d214407400080b800408900a00034205180280301500a960005c200780d20f814058407aa0602268134150740c43c0e0303551a020a107221401c0101d00283c0c441d520403000254002010400c020060a050350884001c564844c5142080e00900c2240c180250500040a58880c500c80341d07821403008541e000d4030075031041c22240d0340c5070901420300360355001014904914280b02c1d2090100e20048042d2380d862000190074a6280c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 310215692 1250 310214442 310214447
    0x105090703052e0810150b1606140711240405010b040c0221031017010f06060504080709180b1302060301030b04031106040507051c0b01091d060412 65
    0x4020b408407140318903c4450324003989141074140344a502942407100c0781e52a206840d441c0020201c1c0800d0ba0524042c03941351503a0507842410225810b10000030340345c01600000161000b002c0c0d4000700700d5807415103903400c40c1c1c0840030036500c51032140c2c98501d2264032a001d050740b28189070000e813001c80800c0b12200321003202094810b406c14002c50001a042e01180046001c1b6558140b40303401580c0a01000315181e10034590001051124951043c00e60400002c0010800300d6405261400c1e00b100f90300207100c4000f50311a00c90120520814070a0030795444016085038007500034046c180c0903000000c10300d0450341c050001108221000c1ca0154034150300c0b50400102c024110100c0010000701000240e81c5034400345011718014045026242400c1c54094050a00440d210600790061000c000c041b82d00070131003901301d401c2951070b004035550f80c026050407400c1c1c0c10401090210b444001140d42c20855101300e00c80a111454100001140c10440356994000c940c0200a041962680e0f4011072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 310216942 1250 310215692 310215701
    0x503160608070234030b0103061b050702010f050c03070512041503091524030b1e0f04030f02030c010e03040305071d04110a030807030c03031503083903120705030105090703 76
    0x104038113501d10303540c5940e1804130580d804c0c0d1083c0c4005032104c00f031260041c840403c00e403856905041982c41e0002503400640100800800e49040c8440810503507441c080900c221740344140c0c402e00340c90f040a054203a052160f00540628038010781c3e40507408550500a00c00e1000c25500022000e095003c0c40d00c000014080d1540d43c1c85031601c0743c3d4503006c1c0301400480341c0c00255100740740011031494034024000810303c0081c000000c2e00320508c14400c0c0b0340442805030345c000303406103003510f10002c085405a1440c4600d040d07243d81503180125180381404084080d000f56072140781591404c03680c4842001071112444424100300d03102901090029490f000b02c0e4121400c040c098074a10380d81c03601d40c0300c541e0300030640c142d000c038071082101c604041e031500c1601c1c0034821000742d03001c880f41543c9421105014821303002c08801b96040d040704440b0201030402d42e0762840031f80500c1000c101c0e08980707a148d0f0041343c1c43d548080508c001055105006505480c140e40000d8030000490303030780d10800c80c040c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 310218192 1250 310216942 310217023
    0x504020703110604030306031509230102040f08070e0901020c100f0b040906021809071202131a040e07030b01050d051302090a1d1501060c05030405031606080702 71
    0x410003802d02e02c4041c2c401d1000358481c5000e07031000100c09140d800e10f52048900c11080344809440c0658001c00907003201c0e8685007045d400207141e80040c0480103e603009224980200141001d8801c00180348800000c05d0019511150000c50781626042449400c0c0d000b0040c20b040c1c90b800507444035988150540c04020744240d407071400300c4c2e003441400c04602100c08062041d41d495400103845252004c0c10791240300c1840c0c2c00d07641c003a00c0b454441802000e010701c60410403101500050070b03214003600340d200207015001420036609581980ca02c0340c03141d5070040c40348145a045460004402a004c0d100c1c03660302c100b041c1c564516194420810300e0041c0b100800c02440000c2920616001d0780340c062402e8415941c80c0b0000400c8403091400a45000d44407c00001640c40381e0b008441050039211040e04644a5040c0240d51240038500305056004503004540c1610a030484143c054400c0c95504048503240c1d10341c1c014940703071400e00f2030311041048200100d100360b604031100c0d0401c10180440c000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 310219442 1250 310218192 310218197
    0x30c0123011a0c2d0d0801060e0103090602090a060305061c0305090108070516050106171603140a05060a06051806030a1202070b0d05090d1b02090402010e03010504050d020c010f05040504020703 85
    0x41c410f00c101c640c031400511130541240003404074440303059035410028034001c1562820315002e650300d041c100402d40107290010306c0c10191101107090070000d590301610b580000040c0004c05542d02da500060003414112201c1d0311440c029038000c00d140c2c120b50440c20701e8507015a43c083c5006c04085c0103403950f480141020342001010030091382a1100b08052a41c3d8512810001c91603030b151070307841503181401c049005041d8114945e485140107580c1d5a0204996101c0d2060b541c54018000c00c5003411501c14020b0f20702e001321800c010305128a0340c000703810b50f60308440140420106002c0a603813040211800741d01588205410f6010a8032842d64482ca401030b80304440d1080d407503a000010641004140003c000e07200c2c07007805100001030140e1002500c07a4901000304a40c6c1011200c10180541c40127402258510041401d5901c500102e100c6800040d00070f1125080c58540315544200d1a41117600501580c01e03a805158410315030f02c04560744541d6568149418041040025805003004606 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 310220692 1250 310219442 310219453
    0x132303121003060510050301060b040609090b060702270106050a080f0603010e0d110c010c03050d0902040b04180203010b06090a060e13090b0109050901020703080423030c0123011a0c 80
    0x1c801c4e0258601c41c4140c540c03454071417450031060500f5501035411110b1001804e20090003280d41c400d4081c03085400580010500310506004590103100c5c2c01006900a10038031400303c0c00c41080025030101541b00d080016241ea41d07005d04440d98001c04c2d40d136000041005000c241c1325003080811070b4100c000280009140064415100d24200325850400d011a4501c604e543c01c0c0c032000e0040400c5000d0a00b0034130078079403003943c000f0100e1003404d1441498550b40c01a000542d110355000c1c00b41400094020000d20702c3d003209562260b800d4190480c429802c0c414891a2420541d06444020001030f19410300d683c00c5c45015606c841d078841038150803112200034040d0180c1c290003607031034a6010313072400461541005584002d4803002090887d09a004101500c0040e50000c0b4040e0302c56009803c1c010306001245003650444403c0c0d40018240c8030108001e0090744040d489000103034150480700450f481c2c4901100b031201000d00c100611391000b20342c154000c00700c2400070f0003401030348000d858 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 310221942 1250 310220692 310220699
    0x2160f02040e06070c060e0106030c0e19060906080d0c15021e160302070e01050102060408031513020901031802060f0702061b0a0c08060f071b06051323031210 70
    0x180740020071030301180002c2c85c2c0345001d41440400d2003000c0081c803100340240410341c07e40c0c6030006002c1e030300d2107000d40c142c012000040c2c94440c1400720124a60061209203c025515440007010304098002c0006034003400240c03c0d110741c01250ba04910348da008200c010090704101c020002034110304d814964a10181081803403049100008050100010500e41c00209140c01c0080c6003550783d0b0015400325500f24010702450782c0010301c281c0c0c4154027140c0251b5a540c0c14140490540e200306010741c01c034040000c0c1403002051500a402201800c0c0d80c104520312040508406000c0540006900088204101619030624000034044240003503c0c01d4a40181188440c28100c54008100b00703031b4104050800402c089030407004000c00010000f0411820005516503001c5406002603041c0400c4003c0c610b034054034642010714043e08042e080119103424072610000d5040381d1000c40e2076440750744149039000d0781001621581c4030890020360801011690551400301c015008034401503031800e000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 310223192 1250 310221942 310221971
    0x40902070c0801050f01030302190c05030a230a080924130321270b0403082802030703031e0203070302071b05030c13060905091f02160f0204 62
    0x802145110707000d1460094a00034809085800140000042d0703d5036400410110b540000d0342c0c1007410300013140c280c0200061074000d488030b440f6800389070940103180c00c5605105503a5840e086c1c40b003800041c2074460900c0324403039444507003a0300c008092001c18041020981000480c083c031707410359402c0c0c58042d103d110101c1c1c40305411001000000040440d4103100300102c1c01e004c40401d04086450120030414000c001d0141080c1c2541c4a03807054425050003807000c20300b0000b030010507502441b26621901ca003410282031380a200408031645401c4052103030340300340c200319401d00c0c442d0764007135070804603290303401c030060088582c40d0070102804600000541c0b52a20055005403a036480c01603880302d8a01d01000064100c00446401d6803070000100119200411f0400480400b20b03001d034848600242c0c00001000d80b900020300d16441d04c0d0420845480c005500b50740c0b080c0912801075152070580c01441648115a1003c1c4092100b001c2c0c600000c5200403819081c900c0180301090703141d03440300003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 310224442 1250 310223192 310223197
    0x507080105090a1103070b0904090201020a060219021e030f0f131d0f190c02010908031317030403020c062d0904060e06100f0512010612060e06010e0114040902 70
    0x110380c8a500050300a03010408804840003107441d041d0040d01e2147d18152154016009607160540683e0721071a140f011a0b1080c0107607145517611a10840d00c601017561250a80c208801000c40980f00d102000c4206a40c0b00c100381801021500041d8504080c1d07100e41841c5801c00103e0303445165043c400814020386229000c0f02410030701c003d1040c00d0201c2d0450a0240c400907082c3d60394104104180043c0001070300300740c582c064416501103461030040c1400c900510f4000d201802a100100610003d0f294400306220100c0c05614224106c000d034814200309480b0669004025031302100500c081c80c28105c0103483c0c00f4004d0569140e811070140d00d20503410003100000b1100079000590072805d03240c18031600c00a032000415500e041c0c0b40c0034012038a41c1d07040d81c100c2d03002c1c0304007090a4000036100e0001c80e03910f003072800f0301400296510500585074806078004215943d041201c007040c0010411481840b41d0030581d120b2544100a01c0190340e51150741a0000c103800341000007160002c8503000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 310225692 1250 310224442 310224451
    0x19090203030f0a1b0b0703050703021602090702101a0102010b060a0c06050c090603041202010f090b1308090607050a03030f020315101412180d020307060e100e0109060509070602190507080105 84
    0xb000045c901d03081c600181140c0c8024000824144148009000400080d0000d01b0340780c3e050300c18200e60f0300c85000a03403800d120309045000203814542c0d9202c5103951408000b40c146001c0c7c0080c04242121010001d1030b001c1c454900c0c00044ca00d801c8100400c02c2504160b03000420744841510703144120010400c0f545c821101521014051440e40004650912039071500c61031440d020400141903170f80311504e05074080e020840d6003400c900104180040041245c00c880c2c0c0c0200034039910420b42c43c182d510ba030311481096001ca2310b480c11403400700c0c00900071280301c0c00940300c00341c0320824072008004008010203445401c01101768845441c0d0041d400c0106540405914940d4443c034152214158841010010684540060119083c803c0e000010395a843d50b00480100e030f0082542e007410f00d00950869180c61080c200440c00100701c1e01944000007441c000c0c0008c1c8515565800e01c6580d071603c5114180c0180d000c105503d9001c2d001c00003007511302e072003a0305540e0200c0d50740c0091401d4400545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 310226942 1250 310225692 310225703
    0x30203091207120b0a1112010e060a1202060a0e03010f0e0c0d0b010b03090c060412021e01081f091103100f0b070305070615030b19090203030f0a1b 65
    0x4000c40d840c500540d1144601040d580140040d90405409145a0004000003005490318070f02155120040e070708100d480d0002500c1c1191111405401d600c250f01080c4a000103408403000458400c2c1049442d210984080c01008040303281d140d030900c451603003c0b1440008116540000b04141e680a0250004101c21441c02003000c14581003664105041d50742d0081c4641c004c001c112000581104c0e445044a42d03188a16803a59180101c090405056420444e8040c1c800180829202110490071054500aa410126500c603821108100c0060311382c01310701080300880060a401c0d01c42103500c4000c0b000c1d4444000342656890018145c40c91903440c076564134000f00400c00e0b82041008a80c000f8102042e002c1c49851030000c00301e040c0e20403698043c007003102c0006d80c00140900c4d5000035040d114180c0203030b00703141d580b030503d10312044050360300751988401ca61160403030344d84c18015070b01c13400c1d0003d02031480e125504ec8501b400b6484041a00180300c041402d03c120700c8200c100030300a55000e00e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 310228192 1250 310226942 310226947
    0x4120f1205180c0402120424110d0b0103021201140103020702040509070302013f02041701060303020712051f0605060f120f01030f02121f090210020307030813110d030203 75
    0x20b1048038204035050b00b032140600d00c1441140203a5902c07004458100741c1028141285a10320090350b203d50f16415080490b03a810102464101d51048000300301261941d58108404840000118140d1080a040040e44483c400c01808a000c00b40d00340704045205040061401c080c60b404a000c0c0c0b841214180455000b50000300103550f044230420802c4441c2c1c0c41340444445000c4a608190f010314030102090160308000500030007016811030b406080174801611403010f07a2104640079041600086005020b8440001210710002d90242191640301019024041010f5036920158019100f0b591001c0d840b900c00041c0c0d1344418006284004a00c0f070030070b5a0382c01d0600300d49404603014020131070071a4140010804111045041042158120b94840780c21007140319140c54001d2000d000a07a1b14440801c4880302c581c1c40c0d0003410524401e1302c0c0150038001000f0260b0b103d0080c014040c010458000c00100034000d15400f03a40c400348a810070603045503200022034100305250300200c0150740300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 310229442 1250 310228192 310228231
    0x10b0312070204060b0909070318230f060106050405130f02030f18030a0c020f0109090c0f111605010f140f0301180912050a020c13050708070804120f1205 68
    0xc0c0503040140011485c080e19020090001c515103210082c101070405a90305c1d8a102d00e409100070b1400c16a070486009050a4850600d60a642c008460420018854400062502440884d07000d040f10344c203803103680c1030610b050f0601c000c8240d0000f010303001f01da07100b4000342c04c024503201940c0617510b400020180b0f49400300e9511801440002901841e90050202c0c08110354000032075000c82d907041d07842100c2010900c0040e00c099034903412494140e81403100054032281c1c0400b000d81084034590364240da904010050b1920786c0f800b5030602e00e0124504405101c59401018500000c014034a0b046110b030b05091044a1a5000100f00302d018a40003c0104074441e940c14020030754605629080100d007040f40e4030705031010b83c00f40c9208140a40824540c10702c80c002c4c003000d60b098102411410501d00b904c2c582100400040358101d001c181c0340f034045600d00f0300c01c0a40f0b40c0705035070203410451600d070404405e072502c0c04500010340c100300c6115100c1080d02007602900d8040d0900c0000c1c040ca2020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 310230692 1250 310229442 310229449
    0x405030102030f0714070b041e050d0f02010b0d020901060e030a1707020f01051c180506090f0d0f09090906110a09050306090a170a140a02030405090601090602060403030b0102010b03120702 83
    0x9940c00503c925080500141002c10388003030a690708944e10070109c010081c09417021003100007450700c1c003401900030002e4540109030450203922043d0120360003001b0740c0c40030404029503504514000382d005850385005000700c50080003140f176141001000c07110f5a84040d81c5210b0843d2000b00d4081c1c0d481e07130202d010001c42c00c003646103540d880000d00302581444a0b13003071740341c188101c8070005015582d1a61240e50208128480c119045900041607407240d180c0300c9103a0703a440c01c0e03219120030719100d04c42e080595140710b558012001441562144800c0b40b0f4211070390040d15240000780c07415681c40c1e04242007200400010800c981182d00c400c102c43d80790400309810148000c1040f9180d400444114000418400551207040d9000361003a03101c5c803400300c084641641200d00000f50301c00010380b1a900d07940020180040b00c03c11500101c0699a8100440d58504039100c1c05e005a8082d1020400083c041d8000300007908041c400000d142000c540041d2504450b2038a107144a44001408825400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 310231942 1250 310230692 310230707
    0x161a0406140a02030c03270312010e060a05010203030f070207050d0b04120e10030905030702100c11010207050d08070501090b0127020c07150504030803010e1905190c050405030102030f07 82
    0x201d28011801c505d055a60315001b440010301866600c10f249465004100c210803d1a14a06841045903115080f06c4003500c0e920200707002c0e0380351600c8604001400e91800001030400c2c0d0350103034059030640d20307500c42503413040b0300180c1041c0c10341c02a1035010901351107200000980a001c2d10841010b42400d040101c0c405502e83c414404000c40814a950b407526074030b10380c0d44029070603e800502d20f14a42011400c501400d82c00035808030b0f140107510f081c0c65009800800c000d00400c000c0441007103540040e17940d66110711800c0d801400715000c9602007640c0e00c01a00210380244000b0888a103036540380f100a43d0260014070103007900c0340e003041000c81840e132400b0200b888081f04500d41140702300c800340d88190510801c66021118440340e940b00344513505480042d41d010001603104d58489801c6201c01c00100c07400c0301c48822107080144401000d0055901840c601440989010a484044000750588005810034071404010000d03144d00d09100440c030030001e0780a080d2041c141030000a1550 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 310233192 1250 310231942 310231951
    0xa080603010b03071202150f0301030c06110c1309050f1609051302060c120d09060507020a1a0c120a0b010f020601181503050118050d090308161a040614 67
    0x90b80340c1070030780b20b00f0303100050042c0a4400c1a00100101c11441c800030300c03400e40c030100441c0101408100320744459640006903068a1050390440c1040303403110300883d44082760382000003260344011a1030f522801c101d20120f442c822040404110881c040d03c0355071503c04d40000300d40d203540c001145201c108080009220250132444001d121904010008414400368036501920440e400556428030190800c02c0c0c6c0307030485001104640700c03085c0c55140401050b2070b4105070307165414803002802c1c8074400310701c08528907031002d0010300c035031407100d90400c11000042c03201400f80c500f003048200101500c80d5240c401c1c000d12001088540a0100040002400c0c00440b015980580d0041c4003942e10002442a4010302c10030000d4078285810390030030018155070000d03080e9464201420360300e04114918121240c0280121014008081d0041303d10071101d1201034450542032198140d59601c020800000501402d03194040130140d005422190308282c60407900e0075520704400303441c000040002c40e0311 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 310234442 1250 310233192 310233199
    0x904020f1f031523040b030708060601020714010c20031002040906050405061c06150305031b060c0706180c270b01090501030915060f05040e030405010903170d020f0a0806 75
    0xb951a08000703d0302d903c140105a013411810b20903030200d85c1c40da9803280603144030090032070310300d1a503030140c10703490390700a83d81d20740180540040440d1042c850040030741c0359103040e9034000e03640080d030f00d444000b4202050f412040285503100014a940e0030880115400750805006075a01d20704107408003214400d0340b003240542d0400b0104038007940c032032000e20480c81079032072008150040391030301d02c1c0181100b0125680840083c1000300501c000003010b440b958980d0807086840c10341d824409940c1e4030f82154000041307070080143c94002140d80d04032001507884008505400d000c41c0c1d480000009c0da6403c54081c000c2882881e90402c441c4e240c88600100b201c0b40100034135041000001d11041c000c0c00342c241070548507108a000c204030000400c1c3ca078540802d00f0000c546d225007950718410401c2c807519110314100402950751701800b1040383c08840c4142c41d5184070a02c0e56030f07507080e43c0b003500c0d000059500c2c0520440380e552820703000038410180d100c040c0c0341da07404481c00c02800d00362014020600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 310235692 1250 310234442 310234481
    0x20714040c02032d0f030a0b03010603150e10110705061b1602010c0b090102030603010e030c0a030e121605100305091506040b0618031203090c0904020f1f03 69
    0xd01c0d030048100d40c0d400f210b0400b285551030640c01c1201d2605008294005403000014400c2032000042019601806820000b40f002e214508101030a036a52030101404241808003500c8862000f82e002c401e14080c00740c142c0c0d40c0c41d501095400100c50045000038092100000d4200400c90f06220460780286240440c10f142a00c120407080b0500510b03860443c20700501c03008000303583c010101005002d600250054452804001181c040e40040d58030754001e41c00e0107000c8a00e05000302c103079a03032450900020a9499542d0714122100400340280315000942c5102024214909110800d010010b615600002c03031300d00414030450004419003541090f01e0001402407040c00851420004000c4012040c0300d41c503864001002050309511450344010006504903011000e242d03118207000089081c0c42c0d000c1d6001e6030440e864442100d10410903013000340d04040c44d1a00c2d81c15203420500103030481d000c00440e03d02041800d034a820320321404041155181030b0490b450701400d4203a00c5174140d043c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 310236942 1250 310235692 310235711
    0x1206062205040b1b0a09060e04090501020a0c02030d0e01051801090e0c0c1002040b0d0b0a0f03143a26060a09110913090206040f1802091804030210060602071404 71
    0x811a01b03442c05444100440945c40c2856a13445410584a40d504100210b644480d100b101030050190360004030300071301424803500c074002d010704896050600182c42d450700c2e0181c1840c0031414031042110f4a0306020300500042103c82c00803400d10320032042d054415030b0300c11031180d00300d240000004880c00e541c0e00421061040c2c503052020744100301d040010205207218101300141c05200ea940018800328451354002051000d400540c0700d20f0340b000d07400d451490041254260740f1928068202d420116507002146640001118041d080340d034600d88607900441505403280740d28050105003407012480401e002c030350303c6c0180a400c001c0144201c10065191a007100c22024084c910341d85104007448030f40c0c0880102c2c03a4010710542540101502c1c0d0b202e44031081c182c0e01c000c05001d2017550548000320318010007418403c43e4020603000303000c0c2c850003040488110410b180204100c0450184580f441e078810742c103014110107000386401602c50b85041c2000c0e1203c0380e0509508503c928140360030785 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 310238192 1250 310236942 310236947
    0x6060604030201050d06051e0103050105062107050c0d1106090a021e0102010f020a2105010311040e01090c0303030507020d020102040e07050703170a09111206062205040b1b0a 77
    0x460840b9820300b0b00c03d13161003100b01140c00400b4941e000d45e8110f000f1041880c0200a440541c800b158405d8904011990302c450a001c40c0b40107039000e4000566850025015179170164041690040703091408918101e1040e104504000500f8401000306255505030210400d003403014035409000341000708044c3d0000e800150003001c0060320014007485440c0b5804c082d0740b003900300000c1200694402d6607108150b0200822124100345014501081c6451065200710a405414100c94211072016440070b894810003000b0003910600c82595035848000a00107403078103142000550003501c000620b80b42412020f4144020310301d048085910410051040c020308101181c6c1000340d070b01c2d01c56280d240c1c900e010f55034503001c4c2d0070310707084241d290301000484200c0f41c10004585125078141303941c074240b0100f404182c0c80e00704100001504500d0014501e810000c0005100e030b02d00100800644092034842002c0783e4040e0fa0035154001e5110800c0505034102072282a1072592603200d070324003004501d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 310239442 1250 310238192 310238197
    0xb0306060103021605070b0c06011a0d05070c14010603060605060708031314030d050a060f0602031215060c06040b070804020907080406020d020408010c032a1202040e27060606 77
    0x2031030625a0220b084084101c1112140261036404002c03510302c1601c401014190340c1040e41c12030020720609002107100b41d581c220290a89443da400c0c1810040b6402941000e004002c11030344c20850001900e80205080326035410030a07055400000f83c242c1103040c000261142134009a0181004210100000e240f100031640e2200e40c3c5840d1050201c11494400403103241c29804600ca3300c070200300503400f0f01030746c0e0046000e6000c1c5101000510390340c0e041070010741441c0c03140d07401503042804009401c07058082c042c1d070f211300148a2001002c071400d0001d103040e046429128034550040c0100000c0108601c5120781000b041e040c0b070701c001c1ca040d5001801c442402011034040200c2d40022030104500e50701a50040c0c0030300603040d92580c1d19651f071640204211410a00060304142d070034001ca200c64110240880710300380c98907003202d100480680e0f000050070716650410b503080100081c03c03240c10041600074625803540d00602101207444801e106079405075030b1015000351080c89203d9031070004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 310240692 1250 310239442 310239451
    0x204050f15060d0906050412110d05031501020f010c1d04060b0714100906050402100c0302030a0c0f050105100612050709051309350309121e070f020f040b0306 70
    0x500300d69400265180720003900394580024505c908240500c0704204941c82a0b181e140b00a580c1d088944103424015a515407000041c10045142000410450808980c2d00c0602c0074060040f21907161803641c09900b16801e4020540c00182a58500034114030000c14a550f5001c04690a11005040040040321445920001450085149201c0180700010302031030401c00380c910070400001905040100160200300e40407445000c00b00b414480d42401043c2c80a4241d4042d030080d810200f98078025901901500c405440c8031169021660014909000321449000d5055040b003500c1c3c1380003005071850503000f43e41c1070081e0802c0c0c10880c14030343c2318001c03104840b81242e51440d01007261040c54018088a42c010380080c0c17174604680380000c03030700003681d00005410000c810040d80c6024941240d002c180d40c603020a1300004908648541c0040c05000b191000c41c00745043d004401100e010164403034042100c60305003c6004070103610b01111902c02210040d0b90a000500c0040002615010000c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 310241942 1250 310240692 310240699
    0x6030f060b041217120f0105030d080604180f060606110304080a0807021f11060606040303081b19020a03020c0d030c031107080706020a0b180a080708250204050f15 72
    0x4054a0034800c6684030080c0c1d407044129000e40d170340c0b80b49088851035042201d8550154007500c00019481c1800151100e000e00b460ba07440c401c54075038030200005000c031007144000700302d0b0078071648012951034403200480c20b20581c000078200b131901c0c0000d8618004003018041ca900184010030910201103200a62542c4c0085255a9101544001036030011180038a00012216500340c1e540c09030810740c40c0c001140400c084400c907550302c01c10001d482c40b582c08020000391844002c40c61800e5004100f4203a5a8025038540c142144040030b85054540a0444c10059011030307101028150140585c00c0c46c00e03002e440440d80c0b007185807006041000e4044c4010200000c44611181000d0180148800b4020725801ea4401998502d4025a038440740311741564041a540b0110b0340e1400886907054080009901030b202e8031403251644040740c0c12000741510703020342c100030440205140c40d100d00350141010141c0618040c960040c001200d60041180d4903601540d0b080c031160b642c1d4041c031494240400c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 310243192 1250 310241942 310241969
    0x927030c010c0c170f1c0c17010b0a080a020f03040515091c05031504020c010b0108060d020f010c0804241715040905070801020d021b0102160f02010e0306040c06030f060b04 76
    0x840b0700380c0c800e118504459020440206680c400c1006d035030880644031002c0e5aa00000180c00005c01a0301d880a200f6540294810403008001034084c5076119800f4020020042c01c1403504104011540e004440483d900e4200190400114000052450708810180000c003000d0b48041394407880c1e2100251440c0601002100081c1c8401164043e044180c03000343c015503c80060041030f50181c003148080303070b0108211000084c11030900c411400c013003d0700200200c0e1003096801c01035514001106080c0c440f0b2004100c0890300040c00c01d8001070486000c489c0e07000301495410b00403c1218031048a1581d142d100c0c0074480d140408081303900521b50102c40000d824155803410510300b888644c4910800d5002003501c11500c8140d41c0a040c0d0380780c0c1f80d07810407581c1174242c41c0d0078200c1c80781ca0300d02d900304424002c41ca8041203800c01003244030740c0b0604003400302c0346103000060300e4200200c03011942ca14000c0c800380503490749030144200d100c018510a1007071505003001691079014500030f005124690 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 310244442 1250 310243192 310243207
    0x2102060f090307120f0e0d0c031e06050708013b060406031407060e03120a080c07021e0a1d0c130f03030332060927030c010c0c17 57
    0x42c03049a0110380e000d962805000c650768006002010749845c90004a0b0001e41551a10300709850101c800552018298107094115919280f9030381040541001f81014000181d0004416101d414000d1016483e05141e561620a032a11f03103c651074030030000d001c1c200ca000c08402c2c0b000f4600342440e0300c8824200c04d0684c2c5000118009000a43c000b4207180ca00319091020454040303405416941141d030360324445441c1105041c0d440031030b540b602c1c10600307041101c5404540b040180580203101200060314042c3c882e0001080b04030b029500c694440003211960742c90f890803c9001c40140446c3c03c0580002582006054a2030001461400a1000007502d601b10320340c40c10098000d850900c03a198039564503824010300900b0310b417002000c2d42400150000c11082c0c801c410303100c1005020610600396807a02d043c40304024000c7d00740010440c070105003440502c041e41490001008034402162146101800d0f00d081d111a01011824001352039900e03408a006903495031504001d480d4403603030700e811 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 310245692 1250 310244442 310244461
    0x9040c090b090906130f0b0a0504060810090204110d0b0a15020318190b030106031406100f0306050a060509090f07020a08071a0a0204031406010b0a0e04150b04032102060f 75
    0x245010b000081e00d19251340c46c2c59800c1294041c00e4112010740e241c1000035146d00501045507080d0284000d5030703001c4102080070340c07016009507003034504c05840812a010030500448142d080b810b2010781c811380300e000d45030717281c14040030400c024082c0d485c10148842011101035128420045c4180424480316003105003030310b031112a00110100c0180368005940d4481522440d50000c1c0200750010341426040d01c500c0c030b2034002c40c5028040041100101c504e03102c4098607203030101c100035001d160b2241000522075070746c6035001005150300c0d11040d43e01c6c013030842080b00090700180845418101001845120760780003070411203055001074959901d4955007072400c500c5140008a401140d10b02c002c01808010b1368001d0f10880784150b400c069803500512f14161201000d000e00e100701401480703c00700c0340e4440c10b142080c1c000082c000040701e00400a1940d09200385030001031902134000750400c100b044090300403110400000010718103681202d4003c0d26000302030552070003003d0341c00100340d2411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 310246942 1250 310245692 310245709
    0x10507030e06040b0c0d080403211401170c010503010b0409021e07030c0605060f01210204050d060911060a09091d010e06012108031f080f0309040c090b090906 70
    0x95000b0802e42d02c8668400100b00d050b400107120700c120303029038221840228080c00b481e41c025a850b840c1d03802c50700f9482600c3c404440c5148075803408143c0707581742583d20f5002104582d02070300c000200c4281c0440ea0001035460b080342030800c503040080070001040344070ba8210955081d03e0b1190070141e9a04501c603411441840900b04061080400040b4001016040032200200fa84500c8080c0465036030001000441041036019501040744101e40c1c03090304004106192a581d20000010304264a941c04070741616551502214201d43d91540305052002c090410940c0d04812078016250a14592004015225a1080c0e50010341c40d001407484509041d03020200c2d10090b0300003040602c102c9018165124420f104100c24146000c424082e0080d80d4503404d4041e5400007815032030740d1148803142064820700c4403130f484c402d014210003180d403039000c2c840342221164400c001e40e12100030100b00001c0b01c540d10840014400e99000401000b4000b00643e912118202e0f21a61700780d40b8400800c0400f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 310248192 1250 310246942 310246967
    0xc0807022e0504020120010203011404020a050a1809090503040320100c0204110a030504110307060e210303010b0a17011a030702120d06031a04230c0604060906020607180501050703 79
    0x1000917a06d00701c50440c1580554121598010710b0315040740c207507082c08220721500c140d1200007031080084c8540e00b0300644500f24000980c010320301c0c1003543c1c2c1c5103a40031540c298204541c0341e0030014041051018803540310405005d0625501c00700307031100000461b64442001010305020300300a00c0e4042d55507692268540d020408001c694941c031240006000b0141140e04842c070840300b01e0981014140022034409480403625070248654a0904100c501040d0500d007140d5090305c07481e40b2111020500c040d500806851440c42c1c1c6600000d880a00b020801004e00001c10955100400544d2103d89010050010740c0e05603960700c0d03e8000080707007030400d4101081010700000a01e080072092551020b0201c81c082c880104070300e0100340c0c003080d00200c191805030848040032944407189801214042c0d40f034840c0412110001d01d2200881e034940c000358060408a001060b003004850303011700c080c0703074006064503141e5141042d003081030710500c3c2c240c0030303050410402040e00c604060240721100e500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 310249442 1250 310248192 310248227
    0x12414030a05061003050f07030e0a0f050d09080c06040b0a0203090a150e0103140a0c09080d03020304021e0a03110102030d020d2403051005070309060c0807022e05040201 75
    0x491901d8031040000d044141c40043c0103400c241559183e00d0311034070500303020302d00d4200790000d103480ba02c0c03084018020541000f480c600030044424000760304032403181d94a41c071401c042d10030a2404003002d001804607030302001d900c0c0c0000c1034600f5503680340720446040d9a51400785039107640d10518120728501564400d140c12107002d22011415140e254000f00d075005151b41c1e003002092055004605991140b41e000c40d00700142e20214000350000e4004080c2e643d41740c40d0500748581c0e1940a01c2c41e14203500043c1011039800000c1c0300550400070347c0302620307100c4403410900c1080c0807400310700c2c810b00c2488003510000c820552031849a20030f004403580400d881100f55107038441603010f40018076408100c2c5104101c810f0415a007004888403510460317030404041d0001d0983d080c0c40a0282900034841030401d0394a070308103400902d02c0d11640382c14110681d101c180e40e10380b40c400685800f818041c84c3c2219103040d440c51144504024141e000e40aa0700360120b02d40c2c44910043e1015034984203880203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 310250692 1250 310249442 310249447
    0x302060d0912120e010b0a0506070203012c0c01050f0909100807030b09160b0a030504050a02120c0112021602010309020a080a0b0a1107020a030206071506080106060e030303012414 79
    0xc1c280c0c801c3c1a03510b400140c00041120382c408002a43c02c8600307114203d50410084081046185411000340c03c0141c005400071031000001c060042c1014501c107041c49188408101400785a00d040180210380c200070f00f4440d1404d9141203a50309280508001540314200ca040040d560140766180710740102148401c40d60550303140d15101c0c0701080125002c80c16441448000d44070f41480fa410f000440f00c1503c0014500402d8400443c09072600510590b01403040000c0e000050315005803030003141d040c84015000d02e024140c00100640c1000702000340c5a07005103c00c401485016503100300c0c481c0d09003030003d2250b4191001c2501d00c000303580400007078056240250140004841294851140081c7c2001403031760020355501d0710700681001035000343d80540c050005040034402010418041c481e80701aa1200703084400031f81310700b0307000705026944483c0d080140c0c5802420003074442000301c01441c00d543c14044608111030141400e881d00b02004110400024011901036070070f060504182079 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 310251798 1106 310250692 310250723
    0x91d060105011b060209060d09060f0c2a120201060e070521090a021f02010b0a0b0f0313082113030207050f03070f12020f190302060d09 60
    0x15407141c5c0c00c10564034a5a12800588881160500c012801852a280c80800d5a06600c5442800c070304040f50ba615150700005481c4a5003d0503149200d1010020b118801c1c01e41c0c020000f50441d010280a42c0c0181c0d8190400c41c242c400013105500980c07070b10401142c0c070b4410500210040e6070030300d040e13444034134071005560b8000300ca0314100c0e25268040c1d000122a0000342175481180301c0030907408000d968082c0646404c4440460306004814a03200e0031400302e106050408501b0071000000481c031208420340b5451007608000e203144c4580013403100030f11228410401012030708240000a01c04002d040700203131000da25a01910207640b0b800c0620003040c00214000344e0500070a80040365400d402d01e90702000340302000760030300c2d070000c00c1c01070100c40801d140764079004a20b075483d440c440002c01807400040301d43c113071202e43e5114419001d0340001d18010200802900e180003100d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 310071942 310251798 := by
  have h0 := BRFrame.cov_init 310071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 310071942 ≤ n) (h2 : n < 310251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
