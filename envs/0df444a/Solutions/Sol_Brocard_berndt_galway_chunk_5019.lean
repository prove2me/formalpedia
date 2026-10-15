-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:28:43.428735+00:00
-- url     : https://prove2.me/submissions/8b05c783-03ca-4e6d-afa9-2a89434c9f20

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 902517985 ≤ n < 902697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 902519235 1250 902517985 902517989
    0x180611030403060e030c0a060b01020d2307152d0504020d020625050a0212070e1b07020d03080402040e0102090f04020912030a0201061a0a020d0f09090e030c12090307 73
    0x40c07903071074070320310084d60b00b00b00225900c451380d8004031040c15000d400c00d240200041c200060040c0981041412543e205505541c2040808081850380003140102c0600d10b9210b41412030f80e504024441d400400081d04c280c1d02c03c60000002c88210701e01d416000e40744003142c44d41000120f85090140009a03c486520322000c13681524096921509440100080c010340038058401d50120016001004008a001401e07180709407030703100c20041e0b55a803203515008036000d48040e40d0013000c00100e041c1c000420302183d90320700c9000c0e00d1902c881600446c10350a04148103a021480e008144021418544140440c0c041050300842c1803090340400034225250940780148110303000303d0006c10940e40c03110300c120760740c000c1800c807940d84010301030181c081c1a55100c1c0d43c405107290804905094034003011921001440c0d40501402c00d10b000051398041700100d0400308110000780003240310703082d5120b40d2442c0c0707501000554440c5103030130820303180240c209010441c086040c007420b03616440001e18001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 902520485 1250 902519235 902519243
    0x2a032a0d02060c030a02010f0e010902031f0207061410060203210405070f080a0c05030c0f0103021e0307020312090102070f170909070507050c0a030c06140d020a180611030403 77
    0xc1262030700000b2040e00600c18124014040000c2e1070241c550158000700d03c11203082c6081c403910640261190803920b04190194260b000415010380480c00d200d10a40d600a507030340010f0404d10551504002c41d085030780007030020002001440f142d4a0130354080002420701d4801145050f402540d0603200c18829101c02c00c0100da0f8402041c1000418440903015094601c6d445503030360f40c0d411000b640c41a44181c00e80b0088921880420541000b10300c1c0c8020500240080303801c01500b100460081d404a01741c41e40c01140ca10441480203071312801103009100e0f036030003103071584011100c1d10031000e00604000c3e65031307204004050001e1000b2400c180040e8000c1281d101070b65195a6820f800d225811b002d991000c500804c00c0390441e0040043e144480c000c0c42100c40d0203521078240409848a4003007d04270111920040003d544240d01c020191184810b403142040d58445180003a42c004000d41c3c40851907180d00094000c0e1101c40136002840d2038503004c1c424503201500c00c0d480344141c0c00058 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 902521735 1250 902520485 902520499
    0x221d010609091a090702010b0112020c0a03110a0c0b04050a0b040f0317070f06020415020109020114130e010f030b0c03071b0206090d06050906240d052a032a 69
    0x30b10341510600901c400c3c60060300800180c5401c0100a000340f0750402d8050104810b841c651240e2003c0703100f88e50080e003001d40104150009030300c0c2035070108440c0c943d100c0c0b14031540c0201c0300001c0798180707018000c00c02c1c0130250b03031201d0074182045507001668004500c0c10f40c061004010381d02e090444181100e40017900001240c00114400016210314000030341640010300c000d00c2009440d40c0144215070a003160404024131405040782a43d4141d42e001c0e0004158001c040221503184008010071950390100e015900e540b11409003081030700742c0c0b100c007281c0b1011078100280404d012003a54082900505907256103441480500954101800e00032024203a5062604545400c0100c0704bd0160040c07407114018958074000f000380600312110101405250f0104106003071004003480054840b00791315007502410300903c01808207008060b1098880d041840e95000c069111054404035401c00310500840d00e107082c10700d4281080c581088126900d6100705200d0500d04104400e0036040b2141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 902522985 1250 902521735 902521751
    0x201091103010b030c101e0c150b13111c0e061b0703080c0f04120c0806010b0f130b2817160c020a080106061805090103080307020102221d01060909 65
    0x444aa1f078200211000401701c1c10041c08081c1e07080748841c0c0381680300d59800301011310a400312000b0344920030311140d04940c400c0d00d558052450f541025411468045100d814140e8090b000c1c410040840c10100c0300650700c1084103d03004081c07181d10b6004600002d0030480c01c161030481e6020788200d080140c1005039400105810051000c102d0321800903000205403903c2d03e03817070000c4e514a618081207810b110140d100044010002c00d00f14103e6150072074040c20049030181c0104a54489185107007441c080345800b040902511014000f1b001510326903a0001c0c0c01e10f820400a020004001400c0c0044088501c261050b01d001c03041c4e00034903004d03545c194030240e5502a60203000c02d140085d4045881000030401d048151701000840e4001d50300c0ca14106402e602c0d1510110b90380c05a50b800040c004010700101d018070b0001c41e0403078058400180b400c41c814100040f1242074011115806c1d40c40c007070400c03060400d007410b03031340103030540300070803055403502d0b83c050031134841d85c0b050900054803200c031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 902524235 1250 902522985 902522987
    0x1805040f0e241006021e190b0a0e0c0f04021c0c030203040c0905061507060b091609050d05030f03040503130b2a210c01050c0a030c090311012a030201091103010b030c10 74
    0x5a0900303004207c069003040e10a2409587d444011103491210604d0942c40000781f04d40022040705402e0050304100d200c071180c4003400003a50003e44900107a200c0304084d00003151b02c5c2d10822501a030269801078890415260041c1d030384074264032101045050130b003030180566030030043c0070944446000c060303599111850910302400106840c19484003044080000c811000521296032001a5595400c01625201040304030824060043c0440d801400b0515120030b035407000f19041030186040764103042884040c0e0307400c007042d608011011b00c3d01054170061450a03401d82500c040d20040e4440c2214071a40328141d82d602d03074030b000c1940030a000d4040c0d5117050b8030a00b2a07501942e482c000b40401c1c507002801500d1030740030349a0b01c7c000a103459110f00100d0301c1400e0803000e5990048880344000c1214004541510035445901141c1078035040d82900c83c412030403043c84061081d000441c821241d42003985854012240d002e0080c2d040c4040f001103540c0128010041100458452500d5440c80c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 902525485 1250 902524235 902524243
    0xd0b1f050d2a0810050307061b1b140f0f1c0204020409090303060302120c06040308030c0f0d0c02100506030316050102120f0f071805040f0e241006021e 67
    0x5541a030100201c8502c103000d40c2d1190b00355100f446800c030078000c0159035a080c1aa9004a84140c0340060715205c40d0401244030005c070760980e640240a00781515100c5c820301070032220750743d02c895040304540c0400350301400c1140d03182e00b000704115912600041c0040104540020480c01c886108807402c580000315a541d81c16500074081d506c000700306001d5240f40181c0100000c1c0403d038810368034005900000303540010b0450008201411041c01e162441e41c030310f841c50b00040e25003101940144504003210740c038503010f086880c041d520003003280032030043c020382049a410307600c0b0051800c00080102c0d584000040b101c4504100000c1030b182d6105082075402030207076400d042040c9919200303200c181b003464882e19005010703e03100c400381501c8401d800d072505003c000c0c0c1003038441c0349060304022600d001d0748680700989950300081421060007100a043c5102e081026003942c000100304030000003d580e16941c0040f10b455071078400340c10801c01942d15413001c01881420030350400d8011982c02c042c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 902526735 1250 902525485 902525531
    0x210050c0a0c050a15020702031912050c01111c0506030607020d231803150907060309300e0102070311041d0a0506150316060516080d0b1f050d 63
    0x31745001500c402d82d410fa8400b035407001030b00741d02c03e04c9011020107500d07229116141100c0d42c861040100040c4485090310380f84c018405074021550b0304c001ca422407104d00b0b0001d11441d01400c40300c04c00e0801e1000309404030345001d00002e01aa000301d040200d02500010000e10806050030485800010003c060050a8220781114030038000400c02802d00c1c107120341501d14640c002c40c1134411000321865607100c098411a1030301e00c294004201081702600079404501d5031802094030001140d600c0c00e2030304d120501e9525144010000807411210280d21115481c56214248040d1840e04e103541c80d22804813050311070040c802d035a10380340d21050744542c80743c51903030000325400e944968450341030441d11a401200c12042c185250601401f4610b00890fa5400c0c2c5551030300208051820100d04407020b4202031401d07500c001403468118042003403607000c2c0004815419001c20100d8401e014440480389180c000001d04e21060045040250854190b0749010702c800300c0021400049054150206004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 902527985 1250 902526735 902526743
    0x114280213090e01150e071b0c240f020309010801180b0d08070c0e040b0708041b2301080103031704080403020d050303061203090d150b030106150210050c0a0c050a 72
    0x10100c030b2650f0f80380640056801c1d050300204841c0b92036450250565912003280d03c1c00010300024504030b0052800500012610300610b07543d1030701e68030f64003410811140b40112200b0f03900d4220b14218403c0c0e01508801020035144040e5051101c0480060007401d410b004600c03000300355403020000c9030015402001c820600405ca0300052005081a0089500a100545481149440104019401d1641c0b50f014039404440c030f560300d0341c480304119055403000d017045444007280b881402645a21105004c003030101c2040d0f83c020b01d40180840081c06002e0941c0505011064004102280c0c0100c01c1000203550012070a0f05695203150001c254820303900000e5005410342d86400502000101443c0700e0b0710192600c44003a4034112005690b4020300700104d070310504070f40301c01d0000341103468038034007410185001084412010001a080d2145500401220444503010b00c2d0103550401586146018010081096080c4400e85c3c1c13856105d024650024003410380303004c0c02002010040030241a401c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 902529235 1250 902527985 902527991
    0xc0203160f050f0d05030a140601090e1b13061115070c1103070306050a15051c061b0806030d0f0e011407060f0e0f010e10090512030405011428021309 66
    0x44c0b940280c9690800c0e2030046840e85400203417000054210781e024001c0e40161502482546444c14080656074010030302150060300140c0042040c440390040d000b104596030141031214140140140f8a141020760340b01242c0c8400c80d2074617011b04403540030781c0104e0039160509845203d407e03d8032099416005003074151080c05000418004c599001c540030326410071003446042104002110305140902503154012105031041400114854440d40c00900c10800807501441c5e203c038241c001051001801c000c206041c041001526040c0507a04020000b420481484036440b10014104111b00d40e0b26418030100e45210640c03000501e00f50740d900c5510110900c0364144000860b03000e4014152524400c1c41076810000c030102040c01110003040701070005000080c600b10424014010860065626010703500650018044400c021b52003940200004650a0a41f1220b011345001c02400e21802c2c2e44460311608000a61501c400c4003045407400260b12110030321120105540c89600010400d46 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 902530485 1250 902529235 902529253
    0xb070215030c04090b031c030c020a0516060806011e1209061d2e0507030209030d020606130b03060f040c090903080f010b030c0d0f02040f0b07060c0203160f050f 71
    0x82d0420003401903a840440601522000000f85669a21201c2462102d81345160700d1004952080e44800403484092049800d410b0362525814180001100048818061050248040380c0c00c60300041d00281e0a2030020041d85c2c0c02001c1c444040d060504000400161080c2800d808505403c04030000f50801c104110483e50540c0800c03611141d03110080c454021400c03090804080100c0001902064111900049a8020b505802007900400580a2541c20311901509440821620400419a0300201643d040c0361040003d4507407003070380800865040a203101c540b0f88010501c540c00c20705640814505444038548014840001d8104540302840e29030030409140e8482244c90088405000c03450f120307621070780c0c0c1500034841201e05050081c003c01044d10740c5d402d40c0d031001c480b00c0883c0700c005003099120b0075285000801ca0380860700ca828049640c3c000e1040034416420144814001141b41500c207004001d83c14440c281c010f03004040070000729051000c00d011300810169100c003500d030f60300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 902531735 1250 902530485 902530501
    0x7030207050909160506090d11030709020a050a020118020f0d0201030f0c050a030f050108070317070803010f090b0111121303020603090303090f0604020f0d08120408042903010b07021503 82
    0x7540411144032410400c0000107446e007031900c119000c004003c3e010300b60740110394488480c0c41e203803007201030740502c180c01c80080d244100d8809000084050ba5070213a4504407030310001d007546c19400c004902e161b4104480d10050b1780342c0c1c001c0c140a003000da0f00b041211703d5500042c0d00615501c0e0700340082904005401e0400f50b406001000329940c3c84c1c604002030101c002015049800074003803421507a0185d042071002c6480a811560141e8604150300c1ca010301958132030030240c100303038070400d02200401c0f001e1082c400d103401070328044482880c0040b0f144487c00001030780c1e141442030b1640c14200005944010292000004000e541c001d09082e5490405140f241ea903548111039800f024050424010401400400c05502444d0010050074a50903070380100403c0c100106d408651100041000390540704510b880341d4419801074030425144d03803401100b0203401000c0c1011944408081119403203200110702907a065420100150380c5440f094800300f01c41900c14644484001c0c0c003c03080152107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 902532985 1250 902531735 902531743
    0x120e0706081b0304120c0f0f0308010611011b030c1101021306090e13081602040c02070303030e0138090414070f230406120609110d030504060507030207050909 70
    0x8a41080b002d690440b030700c0380c0e40c115501081d07400404800d035a0072100505882051013030000c030700a511042e41000142e88801c991080a41304a0200d00039100401480341c110760001d5400402c040240902400d42c07000e80c200d8501070b08480241075817001c0c19401e85106940908408440d031000b199100c60300900e60f100d4001900c00c001c001404c4041c0444c0441c03818103182d000d40052500c0303924820303040d940c000241e001204030011016070001145c015135164042c0301320803551500900402c40c15804c004059518004d0780c0c0450340e0602c10980a012070148a801c2108414610714407212250900d10001d030720840c1110f5808100c043c20700c03003484150141c2c0030218420800326180503560320312204a0440307511610600c90100100068800b400010700c0c60b000702c0042c0300240c4c894403010398070a03a842054064a100d66030740140760400c5210700c03108001300d070700301c03040c0608041c4c558000f4441d2144e0700414041000106604007010b00070044a8050403004180400c10b01d13000c0030303281e66 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 902534235 1250 902532985 902532991
    0x507031a0120011a040509030c10090201031506080906090303090c010c020a03080a090609050f06030112060e03030c09190e27060118050a1509090c05030109060c08160906120e070608 80
    0x1305c1c515000103e4106040001119048d2605501070b05103034024290030001004058410b0303040c16124508003105c00183d43c0340c540500419241c0302c0480c101042c0040c900180200340240c25841041070290310a4005142800c00d4024682020149907d10100d071400d9003503800102003080118000d201507030007450348010b940c125aa80c41d821a0340d50204103510115541d6103401c110308000600410010782030b008146400f895000c905908007140329403441d0b0044512031103c0f4008600d04038686040c0c6149400d03811048030211086041051420001c0710103840c41440707400d020049400c105003101e002010b8048041500c00941c1c4d02d060b1940a0301c240c03c041041c051400001481c5814148582c106800180244490071420720406600600c005030059a009107500d000081940d424011806814400c82000c5044401803034003411031500500584000b0b902c030202e6240241c2c0c421070a41c21600c2038503000c0d1b0030f0b03286140088010416034040c541503000326800420720917007140c06a40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 902535485 1250 902534235 902534239
    0x51302090708071d01030e1002131403061f0806040c1517011811030109023c250507080c12070b0a03150e0402040507031a0120011a 58
    0x5201c1d07440c00c0e8115a0301e54215480c001207070030540041400c01a0390361502c040003040c10001003203000f590710750340b810b81211a107070340703050700066016500181030366070038024581c802a00608209500019403111002401807072107114030042941c28840381c80b1007400511164080d1411360600b030500299620081c00354030501c0c0442010031603001d01c2200300008a403180c1c01c0c102a26400c211050003048041000c1791300060700c5084008042090400a60007800e450390016514030040c150105240c40301070a024030026000505100f08035503404260704941e03000c0090f980c82e504020703d40f10044100486a05d41c81400c0b400600300100083c901094035080c2c01141c03450503251003000700d10000c3c66900e00803900500c608002003182c510152030040c14506020951840c4602d002840030056441007001d10303144020b1105608241c401c45e500a00030b440c00340705500315007400c28a106c49c245200e6040000c5008001d0b0900c103040e29809003040704c207000344000070382d0603030049000781484500c0d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 902536735 1250 902535485 902535499
    0xa030b04031d0a140d02060d0f05010f0b03040201090b0918040503090a0e0705090d2d030306080d080c0c0705100c290103030513051c03120603150b0d06051302 70
    0x100e06480c02c443c0300822540516a003901303083e000b0f41480750300302c10080308a0700b0860904c0825030400d000c0c010140d08102001e8001010361401d501d000507071301607601985801d002003007800090307640000007600b0b0b02c500c00c4031523a44040c90700120304c0d5076200c445002007202d07011042c00200720f03000c00101024a0304540c080700e0603449459a081c292000d490200101d07038108a04136441c1000d01c0d0344181c0500520120460700080c01480c64400110071349044004a200c0000b410035400d4403410f80a003510000414903910705c114050034412000d402000e40007008180400002001c1090303c0213400080c18a00b07400449802c0540390507881c1d801100c2c81d1400400080d802040c0c0210f4000c48100041c2e800ba540c2d181d0f4400b52182d92014904840e01c2c8004400403c25888c5c100341d4407200d4414845c203003007000315800c1c0100010a18090102c1e11410702d80c040000c14400c910f5815040303c0000000741d22519000080c0120350185c2c0018141030404081008810788819405201d5009070303261 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 902537985 1250 902536735 902536787
    0x51017060f0105180409050a0516081207020d1103011d12070b06120703050a03020a151a04050a0204030f1202010e190b040c0803030a05010f0515040902090a030b0403 73
    0x285000d00780c1405002a105002d134000011418501c5608040c0243c030002e0320580c1e5885003400c000500000747e41136445401035180c00309595450900401c81c00014040c4041c040903030701d000e8405d1a03000303881071555403000c0041c049041d00f040c01c40c0b44020002c0100410240c42000700c43c07034100d0fa0581500804400e8104000e1080442d400350b940521130202c140d41d80d5003005680510407400b1038442c400d452010000501c10040344603c503029400500b030810320f524056020100c14050103c00c3d0b0704009616500f15005154804060001c840215041d5200d00800c40203025a40c00503010f0b5651004601c02c0c00324510103442c412604d9402403142a4030003198070360b1200131108111007003002c81580e4010840380c030000c1e03801074440c0d040151900e9689038454070f0750b082543c204c40007980c2c60004008040a041d03403113000705001c0d104208501c0c490103a82e013040c0214400c0384182e07900080c50352403503030f148035161018590000d003119440c2410306000f040d6010111035040941001402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 902539235 1250 902537985 902537989
    0x61206010c210f110c090f090304180e07060c02030a0f030509060f04081009020d060e0a0605160908070807030b090c04060803130e0103080702041d03030901091a010b091905101706 79
    0x1100c10280000703030072183d89032107030368600c7c40c12140182545824007042c000030821141c4000d9034545015034001c003250030320007400f0240c2804110740c01081031182c0c803050b000041e1004541c020a003500042c41c01c1e082d560900b0700791038510030201d440c1c4e0b10400020b03030103002034100f0020b40151040a030850f01c4001d00e03500d5200803100c0c40c000203944103c40d00c0d000000240f0981041e10300321180401c1e62078080290740c9060076600c0c00e440c2035402011040f003d001441e031229610300104210f10090000c140350425480d220402e900000c1c000751941400130750031644c20815114044d50107841000060756540c0a40d46a82000e190410a4100d00c1400204902c6100d0014181e0381c01007070399407615010380d0030003004116140c007641d15008000c000c0206036400340013071489140008004070300100e05280103500c1c82c000200342480c0d07148000042c4074100c150802e40303103502403d881d92800d4400d0080703210800703504c5030b204d070340e21030f0450440001c01703580001c8003a145886844407880c03a0b162901 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 902540485 1250 902539235 902539243
    0x5010617070e0c0328090804030305030a1503020f010507020102161d072c041e0f0b0402030c03060904150603051621170706090f0b06061206010c210f11 67
    0x8410001101503031007440001c860170444403210f00c031207500003000001555109002d82140d403055021503004420000425421f02865014258609992030b1440c195400611440e1410080d00d0400c10080b40907030859000f0070001c4c1c0d4040803104a48145030307840d44054203100881706c0307040042094a012480a42c01111404810345240c030b54440080942e4003203949418a0a00791940036072505000324103e01d50040201c0184542e08011401980d030010701000c1d60000408240101d104108112840340488240d9403c020b04a80d81262600c0718140f98074014140000d0315510381c54400f0000803c00d000502c041202412990344482564601e00c001078407030b0f40c5002e00904040c046000c2d0000c1e10720340c2104817100409048505182c4543c41c1e52040b50185202200c03564401c1c0362000501081c140c40c0c580c4000e0803a01c00b880c3c0b001141190104000240200c2c0c18484601d0b0300c4410040c49402100715a41c2c03400e40f40c0d804030360f2224028061801100d2070801b08030308100d60b4a000001107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 902541735 1250 902540485 902540491
    0xc040e0c03041110050306012303070909150509180325020123030a11040f0e101e03110d0b0a0b090702060108071205331f09020705010617070e0c03 65
    0x5219179045594040040d621600c0320703903031140580707424803d41181303035850805140a4900ca030b42e1861800d0401d983c603000c1750010106000c2e0381c0f042c01010001e695440514a50203d24000450020001e51108074a1805084008410f126480350b0b004030030309140504500da01c0c000da0325101419070308400d928601880742402c800c10340c010030000e184107010390060450221a003aa00d0300e0aa550342d170600001150b50041c0a440708c0035810f02c100303050104a1000a0f01501c4160b44400010110307413610b0f4a2684401408446203c5401c24956506450782001d19003010003000b4501d403110021005009500d501741c400c003491400b180680e44001030032416100c4000040100a0410051812547d80148221540d06c80e440640590031030903c80e0f0506101c024030711070320841361880c9604844200402c52022943d02c417031020b018844808a210445184007001651a0594100540500034030780000c0384071b040319403202c070394482c1c0020607904903190495080f40c1516005001882d51000b6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 902542985 1250 902541735 902541737
    0x106080f07080f0c03060a0e0a1a0f010e1311070f121718030d020c070f0b16030311070b040b07021203060d110a0e09032503170c040e0c03041110 64
    0x143c009045070422000454011200070403035142c181da50180c00301c10340d070122502d20005441e00c98886418039000003103009440e08507001c40c44ea213403110000b48000394809040c2d1240950345440d6504400d503501081c140c030721460016a90340038505003c4a494960001290103c801c6005080d00a204600364103211610749101b55050310340d0041d039812800518070350070a5000410440300d0020b0a0703c0289100c40055000c0c01130149042440344a07842c1c0366101e0610340108010703060003108105803060801e80d050030001541c202135038a062682c007500c0c200074090001e5200f80824071840346100c1c2d1060f0f40b980d08540c041d041d1103000c8031a40c0401d42c3da90f80c22510800c00800041c50ba00b007000c504a001401d00481c0c190b50300304030700c0d0102c410b031120350140d0000582051700403000c06e40012000001c403002441e0100c00d580003020302d0500709264080d6400c481c0421243d004034002c840c0200701081c46003420782450030280d034281c0d100f5034044034200d210014420141c2807003120b040d082030b01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 902544235 1250 902542985 902543011
    0x40302010c1d010c080307090e040b0405010c0507210c1a04050714180619090c020601051e0d06020d0207050106091b080a0b01020a020a18140108030f160b0106080f0708 74
    0x740c1d900c940286d00050050700034418001c8010541c00c801a41041c8030303900a0354019814205404d2460844213620b96010070010100440004280c14801c0c0c0c5000d10b41c25040c0880901d0380382c0381240d12140c0500010655441c000c640b001a030000e00680380a14021400e56807103a0b40c07101c0c600028800b000945805c864140703801c0c8054108800d00075840580a424654070b0350254800c500500344580104072056640c100781710003590f040080c0b90150006680c80020114010900f50044000400451049800046850410440f0b4041d10307081d00c81903105545480241c544903028003054080c1003100b40c50001ca1000f02005c81c0398480380040582c948041c40e4584150040140100c88009815840b6080d01c1034010b841c0e96001c3c0c401084040142c9083c140924000d80c180c038006907110540744004801071001100c04001c480c07080058210042e5110105440d00e07110f10070740000500030b1802d1400000388030380c1114486100d010340306401e1020707584080c3c05582c03500c0305540703407005144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 902545485 1250 902544235 902544257
    0x14041505070831061503030207080111031f0302031b01030e24040303140408091f0807050c070f0821040e060d050118050318030609030a0c08040905040302010c1d01 72
    0x4603030b01808010500b6410000e44000440c4c6401c0d0036204102c0740d00c400421010300030400c1c15411f206641c0508a410000d00c07000440554a14603030001074940c01461036900540784000303082280c5134004660143c2034400d5100fa4500c00c004100c1e1600e1080c1c0440d0502003100040500850410901c40c03a6110318019848003044c0d4500242c8010400c4083c184c1d20008404012500c0155038442c5208000d038564803940c607024040d10300c4800e40081a554a03d08016613003a42040c0c4007603001d07244c0d2038120b44818403050002e14000c0507512901001080103004501001c0101c0d062001c0500d12900d01c844d0840001c03440c546201d035119100d580ca401c0d0021071840c3c0781c1580c0074800a40140300108016445c040c0210161105000481d125070002400c10248007031040030005164084026154920700b410007a9160300c00c0ca034001c0100041c2815100401a003070082c0c501a00c18900200814505840c0c041d000b0960300b00040d0221b0000300781c0c560030854007200b01d8000f20040c1d5420260340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 902546735 1250 902545485 902545531
    0x1709030711010c2001030f050411090910020c011a01231b06102108030f0601170106020703060501150f2d09090606020705010804030f0201140415050708 67
    0x11288a801e41000004080a00401d807451604681c1e5028110480d10049004002404440343c4e402d800076040e05103804c11020460001624a19250940e02900d90341c0e18180314a0a04c1d8880d032020b01694808030340b090712200c0c154800702036602e9161510040b00d90040c015100c42402400c001c6000381c4403000d110b01026490054161645001001d00341a40c802d81845e0520004807102010902c40600c20000c891f018850000460b03a01e0350b030350300c0580c02030b1514074280c80f00034000104825080c1c086606a4807880404512040c01041030f1040e5031a10802503e650300f910050b29800e041a00108090a5203061100c07000495114450f107054044001d84112035850514000d529a000000340c11400d841320001070b646596840391140340c144100c02040707030083d402c840c0c1154818203040c801a60420000340d0800c2d0142051003032a4079012089000d0b04c4045040a81c007140d08003440b0800024101c00440b0303d402013828410b41d0b8690008413404070040f42c469040c00320b480e0b07104100f1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 902547985 1250 902546735 902546753
    0x1410030c0203040e0406020d0b040b0a06141b07080c04140613060b0406090f0b0a02030a120f020a0c02010813032f070b07020310050408120a0e010e01060617090307 72
    0x1100c1a8016030f828141d5a0400314074401046405407545500042c121511215a1040388810309040382d080149800003004142011618015642400445019584164400001c1c0c0d038080750a13403103011030b030003041040c00d0700e4070301911680741680304040d401002e07407515008072104420800e400b50902e645c2c0108001813030000c0159030006654070500414685050802071000c0c101c140c40e100900e030b20342480201080090703800001c4409080c08240d01c072942c04412508814020f14104025030403a5814800078103039846440040b070310006107098615007041c50324240e14001d0300c0d2000c1d03541d20000318418900085070001c00190140c070070300b6884038130344480071705e61000000c02094250788030301c41d1480d004064104160742c010116001e4114903082040500814000805100b00c0c107151b62503140c02d028041e510040c0ba21044002108003003140d0011018040b4070009114804a103146103009000701d01454000446c0280c155603810445004140a070800394011490b0003400d48075a0780c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 902549235 1250 902547985 902548001
    0x50c060a110703060b0f0420030c13090c090b030702060a020c0c040509030904060b0f03070309080903011503020a12020303070807020d1a0910050105011706010e1e040501141003 78
    0x14801c501d034048104580c20490b050145104540c0040d07041400c900304031441c01081450b910841c20030300713610084500c04803900c03980c8a00002058403621007103110780c882d004011201c281418600b1002403500f0040d0407042107076100340c650070ec0081d260050944180300807a01d40003d42c0c450004035204680c0781d401010003140f10420385807000b02510024042c0c48090320b680d40f15030310103e0036050a1a0030b201d107200600004102d50302c0d20702d540c60100c0107400010019403e0540e03489800040c411114211194007400038002c00c00078041d90000d0007240b03054042a4024098014046105010307040003040090300207006508003441591114429031003010200d0b04600e2201c403810020742d8040101001d42a1040c1d5200c052422404040c50118090782101c0d00f0341c2802d0040200741d8118080e441c6007881514854010703a54280162204a0300300781c181d0b0000d980e0317000407030900080302c581509000100d42c00c0c0041d03603031140e49121a03500f50744113a0740540d03842c00c8003d20070b000e9031245139 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 902550485 1250 902549235 902549237
    0x12111509100206010305060601020706091403161214010612060b03070e070203030a0e07050108010501050a090e161101050114060c01110708071239060e07061803050c060a 75
    0x3281048031408035881604030412040540e00090042c02000014484141e105500707100030700700d1900e01000148180524401d59500c0304100984c081a51814025a810901001c0d850120283e417000701c0000001e00305421b95040034284400d003081030040c01014100c0e052101c681b074203400a51910401882d02000c002c0d458031070310304001903000790350b00518406c1000780c014644914145041405403003000c0807010f025048820b0900807607810030f410380c2c19142d081c0f9141e5111103003410151101161600b01c20f1502440c103041083c200000c8081d181e0740582c95850350306006614030b4103420380302c0130b00600d90748440102c0d400f015070030a43c0141540706401c00010541d1040c0c4c0d9801c220310b85c07103040180c030a0100080c194060000781101001041c0091500f0400d101c5c0880031b030301440712004107400070b085901343c0c8682c80c501402d143c0d6004907013040041107210418604035923580040e10840b000310f5100040ca4010340703802a00807045941140192040c40144001c00917654020b045500c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 902551735 1250 902550485 902550487
    0xc0b0118061208070c090203060a0308030a0b0a08031b03093601061701060815010f031e0207060e03070507090b0a17070f21260c030310121115 63
    0xa80b02e80a0441d610b086806141e001c2d90ba0303030322401c25110140d07a41d04a51a0203004100b800125298a41050126034000000039103075182c42800c0300180000700380d003560010200801154044004c4010990078100c0c1242c4070503002c5030300019403030340142c0b44c007183d110302c181e048100078107005860340982d00f0001c03644039001040c5a0014440403c00c0e0001c0000807403044084400005860065001d0020cc2c10000074a150100010410140c0210081c0c100308614a68510440c000d400a0320446c640c0c180b032042380c0303003031402000003901f040d54182c841a040050080074003102008451340d254005010b084143c0c20540100301800c9819440c0744c102d00046d0b00040c4445600801004c2d000c4034902501c0d225140c984100c220f40e40d540c1140070bc0b141490168840360400e107219482d065401000e031015200e060011000071201a0307a44076810303c1c0000c50001c041c0e4003100441c855400030720040440303510342c081d07034841d144021001881c00300b000020b244145083c0740d80c6030031302e032280c1d00c26 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 902552985 1250 902551735 902551739
    0xb09070f140903030c06011e0e06100c140a03080402031b0310090c1809050d0203090f1306120f12210b030c0307090603060f0b060a1407060c0c0b06010c0b011806 71
    0x1480c036105090340040723030505444401101c2c0020090715000240b419104514640c2070420024030342c40c0004040e05e0600c98007851800c1042045610390a45402d2903095400c1a49070b41005807905100702e8040784030303000d001c080c040c145d42850409141c00310050020048202e406181400071705060600359a0139501c51000214110010352a030141e50f40c03050085a100c2c41480c1003403401e0452130303942c1c09540041c01542050b0b20790080c09003000c5812a103441d1154140280c8400601c280d0300004c104094124000301030083c2d0500748003155205005030906644a402c089804c419a4503a101000011021409007444281c0002072803000c0102640c0c1d0034840500000d18010056020114094468004009004140c46014920010074009206513000400050100d10a40c0c080805101c030104030320102d44840c1041e2054580e120100300520001c104e4090721144404104481080f441c100003015540f0503000300c011140e0180342c0c00d0099084c2611301c041c01044215294131640d80e4040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 902554235 1250 902552985 902553007
    0x807060f021c0e01120605100f1e110f0304030b06010e03150a0507031401120b1e0f060f0619030b240c0d0921020f130b09070f14090303 60
    0x641100801c060f10b402403440000c000141640b0140c2490307440e8989403010402c02034845c035210114031030017450200101c07403030360000362888047c5050219020b45103010220446400204a2200e00c2c41e150442d4140d078542c66101f070b80d0307205038000240180c0010000c681594084d5442c03100614000f400d403070381c0c0030368032040c0c2960032811940c5506d03c03a110f00600054a815104112038115000f580c0f0700a0741c10940c0800c42c940100d20020428a04040007a103505c0724603409001c821017242c80024681405143c42d4101c3d00305841a510070340c0120600c84041c501101210654030030464919012010480b00340d004201e0b81c43c030140c01016401562002084000c4001130400d04080d28a4a420f00f0b03000403403810001c055079905004503007000344101c1e002101442d602d50b00f0000b81d0b440c044280d00c08201044803940205030850344402d4600c0600b4980c1d041021000c0302510440071366926014100c45d00c0c10380312585804a0005103070704c2c0b11010303100e00902c51024007a04032461704400240f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 902555485 1250 902554235 902554273
    0x90c08010513060b0109050319030509031002041806120f080c19060606092702190806010f0311160812040b0103050f0303070f05181306031b0807060f02 67
    0x4100010ba500380d4009070421103a4811500b002d1341c2881e02c00c840508120100ea40d42040d50089a42000c0903034411003058440e0045420f031180240568444101c20b005050103500070b070003008601c5200700102030762413180784a6a000c581440203411166080d07604e4010803001d0108096035224820041e0082d510700c104040c41d42841c1c00b0890071800a22410f22104840d2035412807004c012206104010220f100034118441d0202d030201031814014903078902c8000c0c030505410008407840032810342c02c01c54200d00c00d030f44a103030207889016014170003c00c12411117603c100700107141a13092044030b144071882c0039190300c07052094840b2860500c41030b01e01800242e0446003120400a040010300030047c05202090070032038404015402c2d414055409000e1056207560902000004200400d80f5031814013100c4030f50b41c020f4000d15441e008850101c001d80340c075020503a40e5155024890700d0400d1220350010850b002d001c0904405401c03c4011564006030b03d400d00d04501c51010b0f100c2d1303125000744e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 902556735 1250 902555485 902555491
    0x140412180b04080111090603061201061203120515010f0e0d080f07030908190f08090d0c080c0f06040506030c0c12070b061c02090a02070b010e18060c04050103090c080105 75
    0x40da40300c1d00c403443c2400c0c850a54214814014240000788441d09150b15040150390300400110380c50f280c0c09400a6030070380107008580c1300306c132403002000d07207002030580200a0b040041c001c00400c0c0002d64030040ba0148004008075040d0019a65420280e811803141d8000040884000d017542d41c00d40d65511640c9c0070350400c21000132000800074004041542004030320004080f0762003d04002c000d000421942c482e13101c2030141076008070400b0203040142c03c004440d00f45c1c00041000001c070b2028184000c8001c0306000d54010b074400e86500e004e071407030320b18a1408004401801c41d89090308040c140400c40e0009408103650806c14881c00590000601c041c0101e28071445645848992504010003207020203030906028581140007400f441041482200055070140c60003a80c64840914010003841001c50151083e003420f8004180c403800d080c0d001e4020145e202088800300341201c910340d1540e0703055400502400d030400003005254001d0b08202c1c0c06034010010b0740c110ba42d17a1104907003928011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 902557985 1250 902556735 902556749
    0x4020408010f060e01140603062106060a32011e0804051e0a060b01020f0a05071802040f090e01021b0303062d0f04091b150314041218 59
    0x602d1018a10007861145000038054183c1c403403942c1d450f0290380050304175441d0078107014442c000009050354a9010a8094000006040c10386021811410ba52904001d4940e1413256549400004481e007a0342c00035258068450f007e0a81800740c0003500101014802e01e29040c0700040319400d070224451002822011855100d000242c5002c5c5040360400310011146910240030000307900070043c00240c400001c6600030301c00501000c40600603407415080c1c0c02001854402c0166400810501003100c1c0202da6405600f404000980b40001041c0e0043e80180380b2000780380c1d0f5081010300555000725400d0035891000601c0c0034207205440c0c24a07051004500890b500010a20510b030034654000001a0302007010959000005041d441305030040340744040c400c21a4007007a0910740c1c1c49500030420700f94080d042942d05010500031000c43c800e18072900d0030f240341d03148600026a0103401070f80c54150421001e00c0c0340eaa90340e5280e40050861984102c00c0141ca14450303100d010f424a0440058145 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 902559235 1250 902557985 902557991
    0x190b041503081902011104030f170301080a05010e01050f2a0a0f08060a08100b010e040609061509420207050330090d0c0905061f12020c0c0402040801 66
    0x15000303c400380c48442c02184021a850084504200862201070b41c0a0700c1c0c1c4a0101c400041031800c0c000a0040c00e1a004c8007039020000001605100002d005103603548a08020302121410b100c0c07a508840d0100c03003070000112500b00003203082d480300146002068a403119501c45020000c3c90200c507800c0b900684c004100030b520f4280b60035800060032a8000c008032a9075010a04051042da1a800d00012002d4030a4031006807080350b030f018420000803020090020040f2603a2840c040c400760041c0e100300050035241c0d00d03506105912849803030040d5003250350012804200c103204108100f0042c20100f0a0003a440f160245440711902103500481107130b4003d2a0880c10303c020582008000700002580300803402150444c80641940d05048440040d0030035120b001c8100418180000076500802c01d10040401180030021944428011101503410086149416900e0025031000000d61070100700e40c3c28014415444c0c6400402b840c800e0300e810341c3d0801c102c007400708041e40c219411002107070351 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 902560485 1250 902559235 902559247
    0x30405130b060f13090c0224040f11060405031605041d060610051b070e0702030703090506250302060f1b031b130806041205191b0206070f0b0a0203190b04150308 71
    0x2c000c00000308c5100c0b4900a000c1da0400750b44605044000303510041c080407510160f80782c036544a20a985c006c01d0003a0135900118005288141030200b0f60003561710551400a0320200003010300ca8108421107504020401502c840e0104846a086d2038074490401c48104116149808422a8130513540005402014080d08104c85081c0401c402004802154002e0121384042948013025601320780c5d05644e882e580781405c140c201d410013034800650507812045103442c0c04060303000550610501d984c200c010069200c1080c40609a0fa030008240c1c4003450610109000410000c524241c0101c4600321501d429200c245042440b8415442900c075600461b0400040c05205694070315503502c28940750b8034100503040c0c610030f0802c13104030501c04c00400560780d0b0100100000306d69a41e03600241900d41b5100b80c1e28103525034007204041145c4000b030203404100345c00d00c01c0c002c2e01d014040040c2100e240203100f1001c00000c04103110700652194884001568543d8444040320155010b0038005070744030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 902561735 1250 902560485 902560513
    0x1e0705070503011107063b0616090b0a1101110c010b0901060818030720120f0705040b031f090b15100305042102030405130b060f13090c02 61
    0x20035a84070724000c0c0d0510000c00365400b211400c0351040360303101000081031140300700da0b22030410340e400c0c03805140064211405011913103a0f103820345810604045481650b102c05d0b140040c61842d107884400b04080c05000d0016a4040014181d45105482d14046c0508041110750035640800241004488001000d48403a442030080302280441079a0741c04041d49403100061507504001e000e110100751500000d41e0044050080340c000e5a00129036550016010a072901c1035100e51040d544500e11582c120941c8100104000b0315110f265000380c5019403410003400045d040792140150700d03009000d41480c2e010fa00303200035240d00083c01400074000c61710b803900c1040c2e10406004601d41440c0390b00701042e5950740340031039901d03400980f4010504d03445074908000b0f0407564006011150225100560240d68000042d100b01d440859244c1010041e48069030300303ca151190352a0801010420104417850050052003c080315801030340740d40d40d850783c0000c11039251801c01c00c0180c200b55180711035a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 902562985 1250 902561735 902561743
    0xb0a060f02070f0b0906030c0f0c070e062e03060306051f050a030818040e060403020609010c030608070b0a051213120f0807181e0918030210090203031e0705 69
    0x5000d149945400c0641803001302c51180c025152858800d50002000940b00c5041000383c5500c92011440a034403804e020042c251136510300e00896003c40b41080c00907e81c0d181c000c039000348000c808111007071a00070901c480144400500040f106168a600c400000148903104070b03489100050701c8540c0030310200d14a1200e1a0241d40654482c0d842290280089401882100e40c000c1c0128445d01c44800d0301d0f804a40030b03000c000b445440900a1100308000d158010035001d200fa554080208030a0302a83c0061341103032404d0103031102c0d9070b0101c03e0a216900c11400144024800c80c1482d03410204007103680c4848890881c0c40e1405004140c0d11034040018008424490040318148034040107502140200701c06402041c0c1002c211460300a0142e84107844001e0015007100348896084070714400c10865075800030301c1075008580c40e08404120422800011100070795140e8081c1c98800008401e24000e000715040c00d9070706000c10002c142c07580e02102526000b0003880b03041c03251601c0440c10000e040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 902564235 1250 902562985 902562989
    0x300e010e03091e01120204030f030e0111070501110a0b072102040303080f0a0b06180a090b06030708041406160f0c0c1503090602070501150b09010917010b0a060f0207 73
    0x4940c4144800495603070741003410341180c512030359a070107210703490380040b150320030320f05c02054515100140c04420300603100031030401c0d03900940b120b0f60084200d800450f08048190415407454100002c2400700e0b40c49a00b401e50021480402c680d42c62084c2e480d400e41d0240107403034200c04a106034085441504070740b1548450309080560440c01c2901c0d588000d40003000041001c1c040500c8400000c801c05200c0e403007501129000307030031551070b4000c0421030810090031402e601d108418500e000a82c5441d00d020303034012003c01810700c0d81182c41f400340c240c42d41140507104a400e030b0901c0e0310100c1040410001c043c840c0c4000c4c000b0754102d40c1302450103017580f0030b020030b12000c000d00c00f00d41d280454041c200400031100d0b041070103101c50042d003c04900034060200020585d5000040b000c0510405400c006004026401071408056641031100110310800c40c0a601040030385e2003c120214503104540c50341c4901200105003040e0020009141540035080000415502c54403918510345c10012080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 902565485 1250 902564235 902564261
    0xd021507030903230c07030b060112110d0c2007090509060907180b0301090804030c05100807030b30011107080d0207080412050105040b0a0c0c03300e01 67
    0x1042c4855920700070300031303510f12a07501d00307079103010f090151180c000c0021030742d61444100a599071a074a900e092000703084c0030b89815001070000514051307280c210f4810812141c114800c41840c0440c440701c440007814941120405000154800181860740003072032400095034403000e403a52904001e0301e40100d54001e4201881d41e400001000494840007401009640010f60400c0340c80860380c0520b80030784200c000c05034055090000c948104040d84001d081602e10444c0005441600e071030178014600b51215403440068002008901440e010b40e20018041d80003810140030541030214540c6880750030000e40d02c0d03a040710169440d01160a10401406e8018404104d00e0000c041e00c84260b140074420000f420300398001403400403c00500c049800805114202e8101000241070580c000d0000303c4050702c2155501c0000341c12800184203801140c19a030302c884182e00d07040d0300c0031200d017510103151044c21168010003d01003c54040489024002240007140031800c0c540d04030b00750340803512810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 902566735 1250 902565485 902565491
    0xa0c11060a0203073e03210405070b1e07020a03020411070b01090c05220806130b0703090b0a0b01020705130c0905030319110c04022701090b1b010e0d02150703 70
    0x184a0800034010b15022100c649003106000044102c5071b4103500c40c0070f81d4941c8000e80c040d14800804442c1d015640301d1401034054962699440c10381801511520411604410600003207515a00200e4007030250117001414092019442e43e02140884000b01c03040d080901d800b00340c0300c0030007401000f05170140101c00024400e0800200001d0018069141c4020201080480c0b80c0070102200050078001e0040204840442c00c0c440c03441a01020300c607000b601d00c4441000002c60707280c024028410990303403007101585d0715503407580260000c050380c10440d8118020083e00103030583e01c1095800b0903409409001610854240010381041c0c450380c40140250014480040450b40c030b010400c2c41842c441c104003844d42d40e5400d02d01c0c01d28600d940029413091012826170b40d03d043c2036004141c1403e040e016240e030584801c00548130101d0903c500c0301407410030420440b40c1c5007020401c0e81c810000301e002140075042c03c0b100c1420807a0720311020005a20905101c0c94858014034550381185280c1810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 902567985 1250 902566735 902566787
    0x3020906030106050f0d0219061808030a0507020f040e0d0e1002010605060702040203061f0518120703021005090d0803100b030f011e240210060503060a0c11060a020307 74
    0x405c220740c603282011449030217040305003000d6464038012824881c020122038003403180c03101805400845c0108819102d56034052001c20340300f4000007142d0801803aa19002d090010703ea0805c4884040c403d5102c2d00580c480680600003801003004460503403254071081d0708035071140c0070700084489207202c150841e81040c408100c00c0d121071046440903038050342d000d662a540c0d0408a004030200084081c0d0041c01d502e94003034203d5024015000b498100c05124800c0e070580c0c01000540485d25000070100d801114040005140042003842050340c14101942440c032541c002402002e20f000d01a1b807090000030410500f403100f216400068002e400400e4114104410034585c04001401070103040d600b026926800c4409034220003006040300800c410361300c507036450085511035603007401c0030142c8108065030705000d14500500041d10800b9004006030b0b0b84005000b00509191941e403001d1003500c18400c0c0341c1000034414507201742440040580c0e01d04104500400c4920003510402c941384c181e00036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 902569235 1250 902567985 902567989
    0x10e011e0504061107150b09071e02010b1302070606121e050309100f0305010506031605091f0203120604270204270c12030801120f0203010609060302090603010605 72
    0x6002140300480050950740e546070200080000000c909441c500100f042c908220b5965403d2001900640042c01542c03000310a001181200795001804101084030400401c2c901400d5500c0c2c0a203244004103056001e01c02003010140040e06203044c0315000a454804e2001c180180300050120b03a0300345442010f507480304050208103007882c060a0808100ca1000d10404000380c0f9900c03280108a1038803100041c1c070244c030304480300a114000c0307810503000048500c1c0c01000c0d00d05c038010191100c4610a5006011030b515440700e000154032520546e1030641665604008400802c1c517600259502c01400c001a110054000c010700e2085042a822030320780400e603158000d00045000d000c3e1151051440010041d1100b041224000034182e49910408854601240c01442c0914071616869031681890924024507020140210f682e103001000300c0d0503940707211017105010740020004c071441a800282503540c550300881d0100d440308414003d510305240f0560f0485800c6008002da58a4080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 902570485 1250 902569235 902569271
    0x803090109060e0c151227062401020606010210021e07050a0506180d0f051224010e0904110111010e0303070908030a080103030e1809010c08100311150c030a020708010e01 75
    0x25051103030240c1a1103201542e100c0c50a042505030007401d840740da01e804078000102c0c9c5d5801c0c05034219a40a4846c050140d400419402d01480c810390113802504804000b1401079400160f54076410038020700710040d0042010701810f8864811005020400b406080c10740c5402c1000d05841402c0d0388118183c000c03401d0014a01c0d507102081e080510074000c00703840507221400b0f00f0000e0400d4022100c1049541d00200c0340c0c66109494041c2400e180c2d600a40044800c01d52075080c80c0d07080b00d400f1000c280403d039030815180d20301d0014508003006a400c00c00c40c13401e5409100c4240300d00d91006c01880407441c3c004c4040c401400e9088010b50800000c0c0100a040800611003d07050051101c9024035035141c001c0300c40c840b004449400720b181d00300a02418002c21060640e500021f0690300030981103520240d4420440f03411903030400c400400c9104006040000311585c2ea001441003152001e00390742072028140480b1503401400c800b41c98040c5050944075110814031160345002e11907942c1c040410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 902571735 1250 902570485 902570491
    0x911090c2505061012060908091c170403020d140a021302121509180316080405100c210c020a0303181e06030504061508060109150506070803090109060e0c1512 70
    0x1000447d0200250034045060b202d1030040da50030202e2018514070601d00342e5143c040b00d510a0300809404c414904070340410340a2404020360009201c0111004102e02032440d49400c403020082e141820001d83c001200150204070045840b030700402e000c52400b00e05009103900652907854944d4610285001504805000f000c10041310034100001d01884010410f41e80d5100c3c08690304412a80e0310b050900701030f009845079510405015954480744c5201e440360800f050fa1181c00b003111104071445000b00c80440c107105038200021400c0040c090307076407401000300a5010b03856034600b5402191303580003075100e01c0c0c00c034082440450080b121005071200c0c074001121030910380020161298604140600262020611a440207030008610203c001c51421704861a005040100c1e4086c00a140145002441902d60218090183c540814280d0740110340c025014800001c02103001e0f6205c00880300c801c0101200d6a001c04114025420328500c9202403400f00d01606040c031030a03000360000f0203001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 902572985 1250 902571735 902571743
    0xf03071a0a0615030e0a1203090512280c0803130317040b0a0b0109121a01090b0d03050a05090a080f010e0705090402011b0b0a0b040b040911090c2505061012 69
    0x60030b50070300c500005100c0031102c47da1101c401d00070071010920040290004100680f51b50261201c280d90301100314040700d0000010841c1d0400180311203a42c206440b000703540c51000c0c800c0c803040900005a030701c00250300c00c07040b0001f402d441c59000d082c0100b02c14480004001261144814003001c5102c3c482910f07071000c0c00e0103000c1031254cc41d4004036400500c51340b0011140300007000e801d0802221100303c1d0800c56500600c01c011323a0741ea4800c1d00a40c2d124040e1541c002c0d00b503110903004244607600030701c02070307a80d41401850148030300046040122254000402a0840720a091700e0190a016020284c240b400c0101406800d0200003504c3c044c01410082c10302030403007041d030040060000c3d541c02c840e810104186561606034160710140c00d01c4040c144c03003a072809504030010302e05841494007a0303821081034285004590b0620151200107403421000c00d07010310040e101e90a400c8503283c40030000040c2e554080c10540340207440e1400180510711051501c08060050a8000c80c00181da00e0300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 902574235 1250 902572985 902572991
    0x9060e041a070903020315060f010203031b0a030207050f0a0302160b0301050d1a1303141c050901110d0b1c05030304030507062019030608100b030f03071a0a061503 72
    0x542d1015542120198030081d0503014580003c100980142d41d25880345000f035419508020400c0012a01c0e03100860b2882600703414110001d44600d030714030140c80082101c0c100180303003000c0b94803254501007200c0d00b01207850340202c25010030980d05110012a020041114000c60360510794403c0290105001782806204030a141006102c2c083c5000030040c180c01110703110604108180d01e503c4100380c101a4042500b508007501080390035003c40320f405110242034480403c0701c1c203850b4050017016011035042e640300d11004030b40c0072807000109a0507034603a50001e50059003070107110b910300ca41500108441622030551012903404070803203030f2090307240ca4203a5a883c0c1d00c1c6890b10003061120810900b0004840c1c0c81d0320703041e0703501d001401c0c140740d4080d000107040109201101643e646010b104480d801a2941a00070241a00a01c84588004080d210207051901d5040d1454000c013405945000141c0031000d000070500b1b0b01960040d8042c01d045c0070351402c19a40c8070291704000c08900c20181d0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 902575485 1250 902574235 902574241
    0x120310120503041a0705010606020a0807030e01020a02031c14131e0e0f0f0a0902150a03060801020a05221a0f0d0c030f1514012a060609060e041a 64
    0xd1080302c0207400b0f044810032007003240c903560113001e400c08403045900d0742c81c000b00072421900029442c03184952290000345040003503a0b00701c0c0c141715020700d00c606602c54a02c0440060b507081c400c0b5424903c034190342004107140310368000d000704820ba42040d140712080040c110802046130341107059501081c0c40004900c07030f050200030404030781c1d40441031100d070880901034075002c0038590500412400d0050a440d451b00e40c100740c1180d4100c90000e5022140d102899039a2038018060300308840c00d41000100550307135502540c266842000703c50006500001c0e07842d01141000d5601000406854980c80c032503040c41415500820002000d50362403c01080c450341d0322441ba403c6943d2107a4040050200410b070a02c00b9000d0694911044100c0d0b0078092501d99040941c1440300031a01c1200c9000c581002c03800040d1410301b158000311075042c80380811024203000843d1072134011403003031400080481c50321108200b00c41c895008021402c41a40500010801e4900099218039411400f000c66413 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 902576735 1250 902575485 902575493
    0x90c1c0b13050f030315040e0607120b0901080f060f10060804020d050d020c1e010c0b040c0e150301050a020c030a0f18030803041403042403090b011712031012 70
    0x403000c020010581d20492141000b40c3e00702001650150000044c0203e401c250002040181e403068240d00d00c0a40c0100c0004c0e804a1140c00400340b49402c517540021819003580c0810f40d0041c09070042c0205074400305003500d280d841001040e502c2003450003040c84034200070300b29880112452080c1403c01082d503001c10190354846184c80d0b8096440001c40d001c40306a5003002e07480e05203030101140700c4c140c1c0400c0c91907040c2100114507903900c4143e4503813507041495900c1e01070400010300709581032504c0080104a020032512501d02075481403404040c810074a208050a540009040c104154010300100100c1c40c400016680003000600f8400d002c03041601c422a010884000c4110721450408000002c1c041c145006600507805a24a200303c9500c0500e496502e02c01d920445007080d01000c08400c400c5044031020341c030400946000710301d491407502d40d4414070b1002e8010320240580e0802c1c41d0726641003002440242e007002501c1d18118540b40008000f80c042c40e00c22480312140703082603a0100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 902577985 1250 902576735 902576761
    0xc1d010512040302010c1409030c131506081807061706012102090109090507050405120709090312050a0504020913050c0406091e060f0b09010c1208090c1c0b 69
    0x1500c0700e041d0035480d1600f4024040c05030118006d0114104001d401b81c040d14050444001c40b42c090001e202400c203001c01e21184407201200c004110381c0c4c44815507039040d1900c1d04400280940e81e1110030506006820701070f5101e100d020141c40d42d11104c3c0c10005c00350060801c58805008100c1a10107981e80c01c016640c510b04444c52003400d8481b000e600d051030306954007410400c903085c2e03142c1a081d0b4485030100c040345c60603144400410001c4c0001c000c540340848081000c41c080400780c0d0403165480904030283d601000048010601c500c192842c02c0860b0b00c2501da1081002c5400c0c00340e4181500030070442180a4010008035031020401b20a2004c200191380100d9000350040002980da2a400401881010606480510803d42c0c1d90f034492103500914060312003441607505110b2070480b41042940c42030b104c150501c400702070080c0108240f1800c032507251045484003640d5140c01e800d100c0c100300180075014030590300007011440040c004e40002c125a68041c2d810603040d19155040403c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 902579235 1250 902577985 902577997
    0x30c0a083702130b040e06190203100b0c0316201804031b0209091c1d010315030f1407091112060103091403041806080a03030c031805010b130c1d0105 66
    0x2060074030014010780240000c0091242e15590790034408c03400c1c1c8038000030592200740c2c2d03031544141000740180b040010500040c0388149000c1d044929090071061085401c904035201501c00e000c42042d24072041c035190694034003000c021500c442002c0300d41881c0c0141c41c0e20240016042240c1ea56110040c0f080e0100382d424000e0300201345000078a440711000350f0b034080082490781110040001526080c2c060120f021041e0503521443d40154106001100108031000b1440040314001000102144020303c1d540b0126010341e40c8152507000d2150100c2c035051003544614030391850400717960302007200c003002d03110602d050fa440035800d0f440b6080120040e0840145c05480340100002c0b00e00c40b84c1000008200b03c03213411031107c440c82d130f28100b42b1081700c28030f214261480d00505204000a8426400444048100c3c100040c034009242d072420000e0703840781030449150390b40b004041c0301840c00e07925003642034006100034000040c540701c0051240742d81d40010080042c14909004d1a0303030051050381d030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 902580485 1250 902579235 902579239
    0x3070e0a050616140c0102060103110a090f0e0d020609100216050f1606140406050c011b0f02061302150a0203120a050103030f0807020d0509030c0a083702130b 70
    0x92540054140e0a640d8810f48104490081c841d01e0303030080c011070126003001080c10503000b4284581c03942d124100c407003102041296011805540c0800d00000b24840c401c1d0134411220000380c00003154211a01d010011041c500c00e540c09002000b1410300d0000c1c4010180c0414000562076a41c220ba045442043d2801c00400700c0c043c07040300402d020400101c501d030700c50183c02d1950701c2d582e880e20142c50007540c0d5800d074002c26508003c188501c9000b10002e0a004816100016601041c4070784668120b4404130054001412034540000d0345a04002060b000340004000c0368802805600041c2c0382d81c100542419000c0010640504640c000d03c02d032200440382ea114800d440c0b03014080c0000074442400228042021490f900d940c02d80304580807846400c8980091919040e10b0300c0036030b001e4001d107010633850322800d02e844201391100d207003250050000c08001d2419400c00d4840c0070b20300481c40384904101220322400402c000f4101135504119405440381c0100d0310f60160030303101600318001030319 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 902581735 1250 902580485 902580487
    0xc02040f0506130203090a06020a0c02031501081b030703031b0503071a091b06090d081201080f0a1205071e0c0501020f030909150a180c120b0603070e0a0506 69
    0x40669000390700118400c00303040301c2c140845259041c0107002c9010030348852105c1e070b10282266000031045d5009101d0401c55007001014060075038002840c0a07003d032221955500200010820341004202c280f545d00c252090b41e00314401c0706e00100b0740d00c030000d120240802102510b620441d42c0c0c080c51031890245c010040e207948000508000813007103001070300d00310b0305d8003444001600c003100840c51100c440c1d2801441c51000c0c14501c2002120341046881640c45400c00da40040090b040500911131660030454065080d80751040540c20201d418640e41032682203418602c0000740149081400c1042504156850f0480340c10804c0300311a08200e1108586a025000014002200c00d50f1041b41c009900b100d0100301e001c0e502a440340610124680c00020712404504a0031036402e0711800c010001d440100504d03682c2802c030194000d940e0310348140307a5807421009071841e4010b40c0d8585141524400303000c01400c51010419910009020008002040700e035402c003540d0301c90182004020003802d117 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 902582985 1250 902581735 902581751
    0x3061107111315060306060212070b0406050402040f1406120d05191812020901321f0c110105030c0403061a040f0e011508062206050406050717010b18010c0204 70
    0x21700202190300641d009846401c500320728032a06001292750066101703500111075121940c1d40707005000b010f0400c82e4850344034600c031100c0b02c0c07940c45600410103461005d061182800001d015841c46990b81c8000c0d25000f10000c0201e264021003140c00601021400b1440c6004000048800118a26070b02c11512220310000a1842910201c014041d0085500380300c030382d903102c107100e4140f40c02000302802080c5030385400d5090303101c00021401c02c04014002880300d542260404202600200c0c0e01408141d0300e000440030f000d02d8542c10790405000f801c0503851030420b4111840140034900c00204603603181c02c0c40085605d407401510038034020107402800001020005140a0320000c06003445541c604101496031084001d412411600d60740040d20301c80c2ca1700205120410101ca20340c00c2d2600071680210700040c624403c241c41680560000074031400d01c0c0340004c0540b0780c5102c441c0ca1121002d030040c400c4410354001c55144c1000038480740004100b0704016903000200c800041d42c05881c003110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 902584235 1250 902582985 902582987
    0x90905010e0a0f0509061303030207171b03040803030f07110a030323130b070504030f210e03101508061e06031906111c060306110711131506 62
    0x30719070246846040912040b51031502950460b48126501c500d164414404a520032a0713003103a00c41154003d01d0058039140e400d403034111101601902902d96100d000441c0400b668004400f92842040c2101643c6411700e84001595240400752111420082031340c003096145005106e011982d00c3c5171404e890380c0403030302c1c10040c005048682c031010052040060710700d00d41038050100c0340300d00800c5008600e84c1c4c1c0e951300c95080490004200c41c0c1488010030011000c1a0b0840c90800c01d40d102e00c004c9850807002c1c11400345005a000344840502c0307540003406405690108404400042140d030010b82c074600c551744100d0300140ca500a068500403501484200b54a10801c400d144194a9483c1e100d92965030600d9941c280c245565100d60640743c941100248160300a005580000407c03540ac01e030051500049106240203803400695076400d08100b0445c180c01905240680e02020070304207011034032211110301d00389828138412010b0400401030214580c1c41605e5800e02c003000090383c0d03134481d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 902585485 1250 902584235 902584259
    0x50a05010b0a051203070b1806010308090307050906060d050603121308010e0303040f03050a030b1e030601060509130b1315031e33020a0210050a02090d1209090501 72
    0x1d01c00d005240c0c280012030740d03003001003000080d40c2d03c0c04c0040d49460103580390140003000c05001d207208a0400b900a90f003c1004210050280d4000c0c10020394461404040521788442030380305078020340005042020070390b42c09017071380d60140303c10700c0204181d541c0300d00103810226109010660814042040d209003241284040103950307141008014420541072441c0da13a00049400619811b0400c4500d00024072941c0a402030400900f030104034240d0010000ea0f110040b5828446a81019941260b0b10301e400c02c803403401095a0b041443c0380107158404a80341c00001c0700016685074440c003001502d51a9001e1000090f2100101040b1401c2c5046c060807002085110581d03082c1c00d07000006082c1000009d150130b143d60301c0481035201400c02c101c0c10008620b1a04224642130b0340a135005100d03d5140010000d4006690140122440e240245011180c026061104003441401855016226104e4107074000d6004171075281d200b4400c5108803031103a59500300c1903119062000000d0f4201c2c10103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 902586735 1250 902585485 902585501
    0x1032004020d02070510060506190327050105071e050a050904230108060c0702150d060608010618080a020108040c030f0b0106031a0a180603080c0a0303060f0806070e040603050a0501 80
    0xf622014046c03141300c8025940b0601482d584000c0400c005041c03804001e541d0f4400060505010640480501c0103401540171800c010a0503100c0003444400c0007820710805600252905141056841410100540c0d01f1641456018440c001a800140d98000c3c0241c2c2e059401c010414000301e8250f1050b1450003003040e44041641e44201c001041d03585000c03541c00c1c8100c881c2104503003408265020440900c1d0140407190840c4410004108000c025001d440b014100c5a1a400d1481d40360110082c0a07001d00f1450346e482a21070036040c03246260106840c0c11158092a142c0c1854446080504203010950710007031600305418140c0041080803400103040b01c0c11603c0030005000030340b5040c1800a50700740b58076807140e1a01e00c20f000d2040080b4010040e103034601d00000f90252250380d49445c680c80403080c101264084043d150406602d03000d1103000e0281c851880907070529182c415951103101070161010b010ba80122a00340b900c85500c0200155040304c2144c00500090410070300828001d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 902587985 1250 902586735 902586743
    0x907061d03011505040605060406050d02030a0b090a05060109060e0a090e07080d260402030307061d0f011b03020424050904090809040b240c03090a030c080f01050f01032004020d0207 80
    0x81b40000038245032a07005d9800329213894842d0703440d200420400d54000d42c401040307140151b030365003a0900c0c640c580740c452900c41c041d05680003440e0f040c4440007500581e0300e5400242004030100513100720340c072407201c0c001c100e4410304c00210b181102128038078181401900034500d2403141c0480d04030010341c01240e600c2140b4141c510100420043c55006041c100d049030042d4050740100040800944940d02039680d00184c4141c0c031107034420410351541448004108200d00d41e442d02030741a00412040074598450380c0074282140b40c0b41c9000c07079942000601850401103030310003a02c00101c080c0150111000510018001c00220100f4504120b854100c4c00380640520314186416080d410003060000d0841c4030400d410b800e220303000070140030581c004031102c0342c1d42c04203110408403074460440c204090340c401d9189051041c00c012140c3d10708000318003803800c140c0c1440244030041c140c2a54050640f80c00c0100c44d2007050310f502c50389284038403011419412502c0040c1001c072102090780541021841 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 902589235 1250 902587985 902587991
    0x9020307031410051528090609020c060108341a0327190c050301060f05150a1e031d0d020c0105071502070f14060711060907061d0301150504 62
    0x1c5d2964414000000848440c0c1116018900c0c0c40b00303c080da010884210301c1c43e1141c2c200240c840015100b0740c0c0c400d40c400481281c000c641811021703070500c5141e0160000f100240340e0302c40d28200c1c5800780a42c06040109030034141c504a20303401145c0c080391015065258441c21031041070181c0c144a80d00850300030050740c0403260381040c49100002c000340000d107440700414901884040720303260b41024040803101403004284c000303141d4400b0300440c130081a0100078141040c0c601824024607005440e8803d17004ca004200002d07201c0d40050780241c652035051480c0c1c40c03110100c1010340042041c02d040750860440944162400d0100050200d0b440303005a0a440b5030b18003500042d100b034098072300007c20799400000b0034404880c60b58042c0003218041c0c80b00348916142070701d0700c940042850403018525004901000f445e2a00b00e4100c0c04084a050000c141c0c03460a1301d81c885d25a090381c0503110800c016a0703003c0c44d0300a90000a5549103800030020000c600c00711045940c080780303034401c590040c0c2c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 902590485 1250 902589235 902589241
    0x15081006020604051209040f1e05060604180b150c0109030e0d03020709050a2a0e15030f0a061a030406061e0b0a1e080604052202040902030703141005 66
    0x1c03000c01c80501440e800001081000c20954034810303d50452041c0030b03046595480c201031898691b020310300102c001e44461184450020804500b5540000c0402c0c0c02000200800c00881c1c291341108680070b140c081000503107540d01000035101c00498041c451a2020206240705c03105810350040745d09500c60380f01d04500b0040c00d070611404a1141c000540940c00602d02080800100d4100542c00160201c001802d01420440d41300d44030150402030034040540d01e400d45400b50850a81c01c0f021004a80240b2401e42c55401101ca0f07110040812800c17a46e150046041c0c8105ca80101c0090b12076440387c0184d8040c0030382c0710a0603070400c58043d180035081800002d9031910a0002e10404014100300c9030070903062a0841d1501d82c0245010010414210b545103e05148141c000180300f005a03140c102509280c41048213580019000050b02d003034034404c114500c3c1c51a5001c40955a0654010034021901c0c00001d0402c881341e403000d000e85100840502c0c403100042039000c18045010340411040e2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 902591735 1250 902590485 902590487
    0x60711060c0a0c0f050f061807050f0618220b0a050306010522141e06010e0111030c0f06040b0f010f090f0b040e07061713110a15081006 60
    0xd00541d54521030050412291104903c54445074207858021002c20350000c00503a10649844000c40781404135400c180c0900510105241c0740d409444040e10050100c6400d040009501c29624030b80381d0710030600000e150030020b00e0a588215400e000818a280380711044446e541d601d0f0015032086042450000104a1490161115025551b024000346920380c246070030b0160012a580000450005404110581e03280324014050035101164480f5002d040c88070040c3c1802d0580c4201d014607000600402c400c591b840450141ca800302481d2500308040a020400d041d80700e58400780500c0c0c05402c6040c85500303400038045001e1031256940b450786030344030803405c10000d5080c000c80744107240d8000c007003003240340c95003105410b071900320000038803002500005001c0b148070702105402904003100401030780d904100da030b0140c0d86c04506019201c1c83c11000c1ea001c0300c552880c0050001c95011101c1000d0340f20b995800024100b0b40d0380b0001c54045500014090720012920b081400e200484081421 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 902592985 1250 902591735 902591743
    0x4140901080606010c053f07031205061311030103021f1b020a09150e070e0105070f0609050304030b0f070f05120702120f0c0f0307150903050403020a08060711 70
    0x80d05128050200d64560f6001100e654484903030541c2c15105081040318251400240d16800d030110610000b0745120700800b42e81000d40d45100b08140b040148456808281c0165890b0f5640a1000b000a807a0f038510700041c284102214260b00360500e488038a8003403c50041c000d40c1640c0c021105c0c10001c14500e6443c0d0755140b40000d014001900b900410600d560710b403100003040078401083c10a0040e10340417050119082c820300c905229a030400100032854865403150703040040c920b450018040120000380043c811103000402d040c800516610a00919500c0005143d5116003542c1d6502e81c1c83c144564158826a1004151045840415042d038028040c6100a002e43c1d03c43d2810026100c0310ba113007441000303082006601920043e03030036a4000f40001c1284280c100c40440c0c40c2c9503685085441e005070320340120f040b68003c000200100d0740804940190590800b80414032640ca0314085030540240c0e40300030340090b4161000710310300700c0101c0e41d00c1c0b0a814a6880e10900103100c4110755030707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 902594235 1250 902592985 902592989
    0xf1d0c0105043b0609090d0f050f0c01020f03070f0203030114011824020114250e03010207030309051009031e03020403080c060f130b360304140901 65
    0x11076810402007000100440b02150006221003a884011030304a01d224a90766015407003a5400d40407008012141c54001c1003183c210400d5002042d039440316000152040082d1415001441004103015000c014100201c0750740000f442c00a43d220702c41100e400030306800c2500c00070041031042958901070341c80002920b048560080240f42d07011228001035603c09600c20b41d10980c1540704502180528502220110a559084101d80c41c840813801c000d0845201641040303134040800d0a02c01e521500b02e4950802c03102070401201c0c41034007a00c090300d0750b24130034150a07015400032845106241e050b50115550340d0040f02a40d143c0440d41602c075049500b1048006d000c074030542d01d051792540900c210707131031600c069060040c034007500da4580380070b1134001c11081801030b4401ca0400c440c41c2c5030214280c3e0070203890303109552040000c1c0c1c0d48500b090b13401040d030048540c001050ba40001da4203207079081000c2c0510500c2c550001901c900c02d841c0e50060041001401070b070301d900070792030501e01c0c50320381 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 902595485 1250 902594235 902594237
    0x108010b07030206010b0306041803051c02030411040c112b0806030d0f0521041a0420010903021002010e010b03070302130e0109150608010f11070b090f010f1d0c01 72
    0x141c3c6c28031240201e07580000d400190055541c0d154048049070350070f124010107000b41c40da01d890b550082c0a049910100f040c0544c42c2d18018002d000c0012841000521034583c115804210229003050495401c02400741c401158403d14007541c4c07264580c0b801c1c4065440b0780a00b0b0000941e140d1900740c070b01620030b5510b142c06501403520403065900c0340a03001c001007240e00c0e00e680341c00c01d5081840c0404549502c1001012040001c0c801007001080c90000c0c03c0000201d034406501d003e498103e00e005610b030070040360b048040c440d261641e10417144a4040d60340285100e507151440e50001340203100101e5009803541c81e008004050385800241c4a044035070080420700d940da5000b0203040a0720380c0c1d4079420483c6d902c5060303a10000b070880745911980101c101c40050000c1ca000a11404c0d80c00507550605034902d041c1c003004001042c0c0040380c0c03010342c00102084103526101f21039840e080489884072031552030445c040180c170469411451121102d0300d50403254440400c0341c2030300e400051b82c03014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 902596735 1250 902595485 902595493
    0x1b0905030d080f0414070906230a03020a090e01021303060212060f061e0c03030108030c1b010c1e080c03270a060f0504080109150c0c02060a0507050f07060804020108010b070302 78
    0xc0e0004002d840e006017052083d0301030394441c6a85101000a4503042e8000d000700301e1031000d2520000f45408000e00451104440c491412850354001c07440000c41d40c0141100e42d900c400084031003040035012201302c0710307101c00212012540d90604600a40003450301c17100c206a040c1c0841c0240c5041c000c4400d0000c0000d10385481c1007400380000c2c1141029501d4a00042010b21059208030310500c0a50b00038407940000e0740e42c40f103000480c0c0e81405184100103d11062854007505542d92040e00c0000e650f60001c07040340f80e401201600f1a1040310301c0c00c024540c40f070004e01c0291220b0f000c806070100c4c41034043c11107031000365150750300d4503d800b904c5941c0e0460a0020108000c51142e03403409003800c05070901c00d05c5c0135114a00c81d401d564036800103840c039aa102042c00e6449a0340d00c64015064014030f09a900380005900007211440342d03440c1c01c0d080003408580c0c0403e000090180c04011800c0400b201e50f5955640e0001d88503100443d8242e001c50f4606000251820050040311042c40c0d05902070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 902597985 1250 902596735 902596741
    0x50402060d0b0103090b10030506010602120a110307051015140f040902180a061505092206090603050703052509200a0314090703021e041b0905030d080f 67
    0x801c1c010940b884803036040640303881a0382d0204d03001307124940c003030000300b20f241a41c5803d41c00c04078034025047e440b2404550005a005004c003505000f5142c110030140360a1041901d0705103158a540509107000d40765002e051500d02d0364411030782c4500d98880017481c015102d2941c9134104101426581e0702c594210348446e09810040c5459440410400c1c4002d1052038071803400d840311a82c00504403240a0580c2e80d5400500141e080040c404124000742d01d0200e03d00095080442d030455102d100396000030304549124001480c0390b4003d0b0340500740040c002c00c05996641481947d03040d540c03000751401d0003004180703e075034800c0380c8000b40941044030040c85140d20b032035005001801c01c0d1018011221024080b20f0300c468412004210081d001e642c00300f5004540c4017011001100609152030071342c014501003005032208070000e18101241c1c0c0404074803911101c040b83c0034010304c1e9400494078602a5480c2401900800c101c0c1c2500c10940484844072044102543c00c0802612411041c0b2260000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 902599235 1250 902597985 902598007
    0x7050303030f0a140705091306060c0f140d1206051822120f0e1c0318030c150306060503040c05060703171033110109080d060311030105040206 63
    0x1950390485041200003a03050f0342140780e42a4494180c4140d00000c1c400140180e448c50003450303042c8484041c8004200680c946034001e0f02410009100500102941c4c8a80083c005c01d00071000346a1310407000e851700eaa000107802411460401c0e0844c10321440c00c1004074842c10a080c00e8111000c0301d034402c1820b0b8440c031044122030072031103404000b0450404511000280d558010461180340e50b2a805a86281e01c58050403602020728002d018075440601c040b54004030912420085400d801c0610344035031224010045040d80d604040c0500b14141000203001e280707031464003c0341751150390070090141c841324100d505200c10b807005003044150442c00e011604e45000100650b0780303c0d041080519180c000b0480060b031044170100b80c025095842000160b805d80ca207403030780c04800c8450040b1034081400c81202e10011000c0c000401c000c403020200100c00960118003c1900007441c0e83d29910030b000310101a01c0c20b400308450a041e801100090b0f42014054180140e50080580d810106490b00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 902600485 1250 902599235 902599261
    0x201080121150b130603021f1407110d08220b0f03062409040b040e1b060d0f0c090504140a0203060109090905070515030906060118150f020106080705030303 69
    0x5100c0c1c1c668a0084002c0b96891065601c0020060703500170903150700e13500400c2aa04442e0120300d101d4943d045085032683d41c0a01111040e5141454841c1c55036040d0070015191114907102c2508481c80c50300c030100740715140c4050710540320130a062682c210400355640c0c402203460b20410780d542c60184900b01c14410a503000c0c2d075114a02a201a07040f0054080041500c1940c6050b9950b0700c000151a10040c1402d01521420713260984060000043c0b079028503a5230500a0090240c0340480205c140507a954042114240e20a490041c40a071040290800080008050500c049601d0190015040c141405030341080072000e801400141d0f40c1030050740c041e510041500303040000ca640017040500441c8500341c0e1150040c002461140e0501007800504501110181100102441000490000007a490394005030030b10301000c440000c0d640e84a1a4480d1703401400c4020a41030642406551114910210f60031a9000340300c0960317140b4003113450345c28502070303190190070400005d0400c0700058 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 902601735 1250 902600485 902600513
    0xa020c190804051e1e0f0f060702040207030207030f03051801111507020f0304140301140606030a0e0a0c09240815090f010501060c0606050609090103120c060c0c0201080121 76
    0x746400c200c41440d080003480307004038201d4084017078209031492403035818203000000d000031050f50500010a10140058446c0c028450024840d640001d4100205882800340b1001140e000c000940d00d84000c1c13502400c542c1164147c0c07034000014411a8281d0b41c407414400a42c002024040e050180100044181c0c0302e00040200c02076201d0001c00e44d000d040d0400080c4000d00b1020041c80c031102c0607030f00f0142035603910250710890b2540300092002d60b94030f800032640c001c0030444000079582c900700c2c025403c02d603414001400c1e03206180700c00512203100303070081240c01c4500040a42c20000c24800d06c1c0ca0f0441501403180143c0c04130350304018901041c0c4103583c024180d24100c0750070505c00d002050a480c1c00b60805c02c0018426412141040000e009510140804030b07180350510300d08501282e05e5100512000d0007d50400080121560003803154500c01600300c1c0c01400708484110001d4001150f0420890003e10a44000119025504054090f181b44440c1c840440d03001500d42c60b5103030003c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 902602985 1250 902601735 902601769
    0xa060924080a150b1308070905040206040e040501091e060509011e1119030606020709020c0c0607031e091e1d10080f071403031306050c010f02030a020c19080405 71
    0x1030000304020300d40130003400b5207070b081210003150203040000c1c2c142807082980c043c0203864140800d010059a54100b520160303038021080320500c0c0d0302e5040950150940d01c001501e80c1300081100840c1041158500554a00034041404140c9561100724225030001212208411004441000d505115000042030750004915607041403803031a10004840440c9003408086903a8401c03c200b090340620448004055040c011403e004031070051580361444c1c03103481880760707030001a541c00700340c0160511900d079800b0131800000400403001c0035010031104d0040268001c04014000c0d00c001c03103603c2680c156509204001216280101e010180c0d14014141a40c104000c00001c6244c000070000101030740c40c408010f00074180381c1003241001d104030520540c00394004000c541010100000754104403001d0b850070755a180c3c41000001c0c0108402030b50881c0b441d00002c24090040101e030060328010b005002030ba41c04001d01d40443e406401c88003c010b000d60400d20080005240940078a1030102c54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 902604235 1250 902602985 902603021
    0xa0e0f0604111c0501170706050d050a09150e010b0a0b0f0315030d082508150316030c181509150312020d0207090c05160f020a060924080a 61
    0x1901d500341c00d43c070100d080380040b5183c1c0c81004020070340c024090b1411601019024000ca00e04106004000b4424544031221150304e40c2d01044181c0ca40350300544c0c1a5804c5254030109001710354285010700b00000c04101c10f0b41c00c0030800b07041d1b46000700a2a044030500d400d0f00b8a00350302520010701641001b801c0f800c1000144103000f5242c1c405001650b88030580e0703030740c0b8807040c030b8040c003400200e19064038840c5800425100204019400c1183e40d504490030043c0c0d0141c140021300002d141000c2e6401014448a100304004100540c0403042e005680f04510b41e1402d040e5000c0c07103082100d54207807211b82940c451410402008507a5440120b078840c01442c115070765074507070316003102c071224090f02100140d020301180d03040c00e035050100d90003408140f28144403c440e01c0d5001041d5000d80903400c10391030150130f0418108900b41c074021200c2c50b40500007402c43c640d07541001d03100708038912075103050b51400000d2070310038110200145c03c0b1383e0040d00d8401c4981c44126550001f00130900c104000410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 902605485 1250 902604235 902604247
    0x702010c020a050616030906082e09020c03040810020f070803071b12020d030e06010b0d0e100e0d0c030503010b07080706060b0c21220e0408090a0e0f060411 69
    0x103030440244912505c5084580d648076107450020310a50955000740c0800c1302030002d2010340074040c09074200781c1f0181801c00010390040b80072549013140039400040a01c0c0300184001c68640040050011240010250340da12000c000b03489003030b0f00c142250b0440341e010410040c000030310040040c503040800c600c2d204603210b1009502d0503098030304847c180d550500046401c05d84aa0411020000d1860b601d018081e045001e02c40710703507542060191169240e80882c0a4038410205da005064184aa40c21120290807003010f0200801c0c0c0e190190506005013043c03c2e1011340514000b04000da419035903a85940c0ca00050441540c10080040b81d10b00c00c02c100c1f280200c0d610b030060f14081e09400601036560000106014030340054050000d0504541d803074041b446955080583c1d1140e42000c4030341c1c0300c140c0e1510b203419401e00103400c68101001c1610030704c001e00056902502d4400800d40c0c50843c40340c0c580404400803003007110780794031b0400020f00154040c100743e0070041c5018914015070b403c003a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 902606735 1250 902605485 902605489
    0x2106171c05031f0807093213061d06100e070f0e0607031713080708030a14040c0801110f0306010f050c3316030e0c0901080619110702010c020a05 64
    0x40c00340e510013295a0b00c0508107002c91151881040c424607000c2d000071524590300011103816020710704c44000d00011403800100501942c00c3e041403c00e920070300420144080d02031405000705400320281daa0b1141c5000030300e00038098107400090b5480c410300080e82d030380c42c204100e9209111403400403c000e08002200700030741740c000241040e548207803124145108181100b14588070000e26419800940e81c1c03601f4081081042118007258101e42002d503240e8582e5205405407080910220105034100104410300107901e002e2f40076564404000d01405042d00d030244203e009030f04289020310002c0010440a6000781c18644c001c1da414103016007054a404056401d1040079039800c0355208045140824144000080d021161801640049642010051128411100340340134013807680e24440310300070179400c0020002c2c0441c014400c10103984c4440521752101419119611014035200050100e03400c0350103495408070080d000d25050800c160011161400404001ea0b00511030704c00c045116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 902607985 1250 902606735 902606791
    0x80604151e05190e0727020910050c0c030105100e07021606020a020f0a081203040507030507060e031903080601031112040302031306020d050d0c2106171c0503 70
    0x50708020224003010407401e40f648055404001c000c1c03002d600301e03035004c0c082803070501000a140e405c0c0c5a00001491400c40c0b54400034400c50743c07015404a031280c02c100c1481c0d44140103110440600041c0c40d140030303121061500340c031000e860b200609003184c0d07002e0000724915209981d01920600c1203580034600c0440c41160320a40e50002001600112501c1c02035042051400040303000640300041c10038a402801601e80c90254410807009500001041c14003804000c03201c003658001090340c40140e500d00c805804505555082806400380603001c01403180d444960100b81900b640320440039a50303144c0110001c01c90800c0d6441d000c41c0901140c240c4880d01201c403441903110760025503540d950030301c54818440c180e61000f02154443c0c1a4400195442000d480d00302c00d11600105180600f450261010301803049111603155088142d030505400c00d4000c88221414032807118000c40200540640760001d42650031030141c003d440300c2e0b418070f114a0045038082d205100050543c42400c2d025400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 902609235 1250 902607985 902607991
    0xc061b161b050105030108071415040b0d0f0504030e010333030506181209150304031706060901080c070302070f0f1508130236010f080604151e05 64
    0x20305514107206104441245980c40040c042c242071003815076241c072900c1a5507042c030340544464580c0c0d807140c00e140e9495841090b440644c295203055103441d110b41045140d5000900b242c410715003042030085070312000303201f6180200c0c6c02da03071642d000b00700712401900541044401c05440640040060384900c032781c001851100d44001080005051075070514514045002e0a420110000131403040c10504000075a618181c00b050029902c490001002030907035000c007030b50398061607800802c001c109070b0300c6140d20300e503030590070411074864032480140011800b07240d894a02080fa100007080548603120003826602c0c2c443c0c8110b404244c1c9500c80d070000340030294021251400d00003030500030500e50503a45290f103c0e5a1405008916114050307004940404d00c010340107100a1054145c0b03018070024140c103140140201c50030030a20114114503800003485010841d0700e6011011803c00030106140e4004c5401c16000e01c0745040c5c40e640c0300e000b0560803e4841c0a03028080c0c41601c0581e06000e0030348 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 902610485 1250 902609235 902609243
    0xf060b210106180507021c0306170102031b0307050702040203090c0406060206160c020906090403030e0d0c030e030303070c30091e081c0201090501090819050c061b16 73
    0x482d5403400030682500412480640a524200800c01078440e600048140c00412071517209000e94410703400690080c24140c10124201301410b1180c9401c802c15002140640500b82d5002c0d108420a02014a103000942c1e54000091040048070094076168001d10f400c001d00030305803035003e41c2810000e0101c851b940e02050140e0044400c00035603c4005072200500c050b1401e0140d01a00301e50300258124400400c1b051040030588081006c1c54800d90180d95404203c03c101d80e048030750a000030305007102821088000a440140c4002103003030100c11360f409185280c031520b08908290303590811010400310140c072925140b16008040780302091a00c00b5030130041d22904d642a040c8105000d1440e801c0050104840d80000c0400c110900010092007102d00c0e80a043d506000000d4201c1c00f403c0191401b9050b58244543d510500005500038101000c4c41000d803100d03506041400e0b502402041c0100000d03402420020709610364507480c00805600e4010102d1801c140c03460303029006000c0c040705903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 902611735 1250 902610485 902610491
    0x10e0613140a0905040f08071a0c1b160504020705030c0102040f0302090109140403120e0a210906140a170412020f03120a090c03020612061c0f060b2101 67
    0x1007140e003021950b00010b015200020311051078140c455618000400500502411000030b4840900046400d072a0341305080f4207100515040c000d240c10180c1e0003250350b6411403105400140b00007100054030b516211001490500200e03e0301c0b040000a400c04401941c140c0010041c3c0290700d9828030003031000d0000d90700350090060460062015440050b00700c418101e00d0555011581400a1000d0394401e03130501e09000321502210310500175244024160241d0301ca445a080100050b40d110200c4050300c584143c603100942e030b0002c1703403035075007601c101c1020854400f41d81d000322700d000000301600082400c1504070b005003c40c114208020440307003a14138694910030000881c1e0305001411060041c0402036040600350800d4000a120140000f094607907184140002c105103485039000468008080341e4640440070000305080703004a40c40c601c5000003080f1040881e4003140128611074200207948618211980d460005280c00301403250b000c10141c000f1004075081d82030182992003410004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 902612985 1250 902611735 902611769
    0x13021306050307020c040902010804020d02190b070209070306030206032d090d030501050f0604050d14031606060b39010e0304081608060c03150925140306010e0613 72
    0x9040c0440008170381e10903030504410343c0c0540c1c0c0c0120b4040d0040e404942c07480300503c3c0b500c005901c2044c101c4034140446000f0000003569440740740542810b600a4481138081c1c0d41c0d60300c08604a41d09800300035803082050001c02c080c603800c2c03007605c13440b00300e0050951420000181c0311204614119003901130759000c440c3c000c80490741405110300521055410002d40c0c03c0d40700004040b80100d001d811b0203501c0d02018801442401b80001d1003c2c611003050f00c9d0b031640f21a0381d42c500300d02002819114281800000188100120b040340e082591840800040c8000180d41d1900c0d141299289401c240111100ca542c0030001c1c1300c2c0025000d110401555554640440740b41040c02d15402056007000c41d030020000d54034049602607111494002c02941da0b92507019100310303d115a80e0190b00910b803602080800700c040052800c0308010103c00080c000c0b104003048445031114030003490b205030280702299255024218416410390000c103881d060040d49061b19101c80705951022641c001107001c0f03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 902614235 1250 902612985 902612987
    0xf040f0204090b04050d02070605040b0f0708030a09051b010c0b0403033809040f0201050715060816170a02011d09042a030f0f0201030f091103011b08010513021306050307 75
    0x242c1b955031044c000ba099082c5002c0c0058030a01407445100b150351000640014111030180440300c249a0003443d881d1a41415414000140344455089440340300c0d8001a075502d10306207910000c850b038140c0d9168a98007031541e840c0f08140c03000e00201c0525031189443cdd8031002c0082c000440005007803034002c40c1008419480c02c5d007810100d034094042d24820090102090514a0601e160f50702800e0043d550300c0b941c46c107401146003004090500c40c1c90000302040341840401d105800c03108002d5030843c00c4d41c852442c01e050122408498101b603011449540c019401000d2407101c4c03501c0314513001b078032100b40c001069600004a400710b440c07040d00c0a1481d040b0304c109148003003103c1c22420210a050965072200f03000550020f014040c90b11072900300e400c680c4a900034101d800600c51080c004031045250000b0302210b0400d03003910039400c1030542d0b03002c0909c019100030001300390f82da8078809900c1c0a0601420780059100200c84907002c02154003004d07102d20f460f85c0107180e03c1d91690390301d02d08404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 902615485 1250 902614235 902614243
    0x605130b0a05100c02270c0a030b0105090f0d03030f0c02060a150501120f091401090c09050c040b1b0d2a0312020a0207090e070911030903030f040f0204090b0405 71
    0x80b051040035220081c8142c00e078804884d075180f40d41515070001d000080c04043d41e5160b1440c41b480803009200040120140d1240040c0c02c0072405900c090080584010055a49010310080c403a044400e00d0710580c1c070341c80c0880d484001280a802d0005800d01004d001009072400000302c0005a404201400303140c00d084c1c0309540290256040801066003032100003010b2a060f5207030000c0c00c0d521001d402e0a05d03c1e15a02c070f8039625030301118024041902d108101d0103060504001d0b11094061032000414a89a0160320310407110321044a2520b1b0803c054030030190030013a0104044054010351003a00e200c00c02c021a803240a07038450300e41044550440b80700c02d900702d508002c81000c403100c8540010743c01514007015000c0381480980c8890f9040d034101d103482416804950820300304141d582c5000b9012a0341000d403031100d03c040c440502e004850010703e201c2a0b80d070496139841040014107001c0c4c041440782e0494403039100d002403d2840d0b000601610504441552120300c00c0080c00f0410000300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 902616735 1250 902615485 902615489
    0x1309151701022107022407170105100f050d0603230c060405040b0d0611030a0f09260705030d020a032421060e01092603010b0d0605130b0a 61
    0x24029450b04004850b24039000c003e6085074143d900c52000800d802c42d000b80f04030817070652110701c2d403d46004088030001a14100783d41d2540071840d403d068007403c44802080324140c0314041d04100580100b02011111540348201e80402c006051003040003201490181400a50241c0784212580e541c43c0000c419000c504a120a216070160f02c070020744d1385518068508903501214006040304020f070125803071082000c13000b850145000a00c100070100600503601421030b5401c104040c0f03145480000032101c143c04080c0c448085075082c89151114100710b544907110842c0c04c0d40c20156190f5501d451034002c840035101c42a0041501488a5458440c04015108407202041c003074641000c3c41891710824010704a0001d9136100754103911100e542d0307140146070b00039402c016440c86182e1071402813030445000c41d0340100c5000342d101441003980294520304d044d120402d14507440c0a1511005a00900e41d103282c0c4c80d2580c200250941c2d0342c0100d030391646004800402c40a25441c00c0010100d025 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 902617985 1250 902616735 902616779
    0x50315130f11210a140f0f060609010c0b090106150305150405010b0a0c031b0f020906040203011d04020301110a02030339031306090302030c01060b0301051302130915 73
    0x284050381040751100d4210080d540f0005940d0380a440e5007001d800a810030320500b41d04a4250f4062140c600000c00215124001c2a4507000c0c05854810070806188601075500b400102030303845076004100d41c01e95080c0c01004a100028176280c0d61201d1400780707000c00050344040b03680c4078204000c0440a514211244604071001c022a604059442c829401130852078410005941469000c260080011000307250510064501c000307454908602c2c910400e41c0c08074016410324020800a01b0b1900940c0e043e9160b565090100da803404c56100204000140181e030715648420041d074034418401f0040030309041e994082c2d07a0f2490003800124411b040b202c44401e00034802541d02040d8407100015001251480c0c50071a941d88618694107000b1200c1d800c007911031843c01da40801003540000083c079002c0020070090000c295102016038060000f44681a002200361903505c0c1d03040690790081c0030b515024400b40c110942c6858070a002c035a500102d210840203986030910400711101204a000e00341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 902619235 1250 902617985 902617987
    0x60510170a0b10060f030902010e06030901060501120b2416110111070b04090b0406081e0609150f060d120e011403040c03030806060d020a030f0c080412050315130f11 73
    0x60001c00a0074130140301725510400d41d84400045c116071044041350781c0380c10010205903ca0a242082074000c0c00c080c8036203070101d01001c1c42c100759070040c0e004070041114010401c00000f0504404a0040d080c004610040f03040c0c00c201c00501e80b0b0f0400f5020f01024011040c2d1441418000e0014044000f058040c042e280c0c0290020440b032080d0030100c03006c0e24440765011582d12201408a4064040c3e500801007034082d4521007455010002070408942600900300c40d41500c40e024400e0310b40c1d00c1d910900741113002c820000381958080480755038001e000680a06040c040c60344490070310030074894030000020040c0c00000005c0da4132503902d10504001e00045440d60600799135a0070100818071004081c00543c000141d0640e40390003d5074000242e611003590380b0324004400230010414240c04040c001d2506040100a5106648407440b413039014035540c1c8201541c1c40c09964981004254088041c41101c80c0c44060300c0c2c41982c2204611800c80214914a4480c11001a0b5030400429441c5803c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 902620485 1250 902619235 902619239
    0xa02180402130f11040801020702010207061d010c0f0203030c070512011109130e070810060b0405010206060112020c1509070b0316030906141302121207060510170a0b10 74
    0xb40d00e441c1003400700e15a0320b00052241d080e651140c00380208403030038100110040ba000407810760640080c40d80ca4401d90a4540c4540c90360b0080d161400c0074252040e2403283d12640c0b03111540155440c10402d40070356070510007001c40352b002070b10b50b03440000c8000060300305030700401190400071844242600340c3d800034059402d803c00504500e0103803248040c0b20780e9807040901040c3c21158845607941402000f40c602454a401c50590b8031064494515402840c043c80010130465440a07601641c0050303002d002c003a00c0d010011540200c0b00c694501c902c40d0700300100c0c103051200704a092040c540003502008103291007800309080c05200d0b031114120b00010400c20082c0c502200400d8007113502e0b0300300000e1031000c0d400d0441c01407008941000f14807991005000282030000c92040707000d0b200300c4001841c40420040305448600c044041000038400b44030913800506503400059003c80200500d01040e0f43c0c4218144400c0c44200c0b483c9403a0300040d0002d0280109503540a50080041300b82142083c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 902621735 1250 902620485 902620489
    0x1c090f121e08040c030f03050301080f120a0c11121513020d030810030b0c04150c08090f040f140906070c03300c0f0f02071d060111030307020a02180402 67
    0xc0001c8002108101a2400260400c401d01018101039900300c5045104100d0320310b400341c0181e00078010800710748070703042c241c2801c148001000210b00e08480002800c03e40d1000041d5038400e0103100c12144800d140c8001000740d121060840c000390045002005070b81c2090054050400d00580340c00b0145000d80c45e40310142c0c0702e04401c102c40f01c0e4140342c00101613642140b520240440f50f0002403002006100780300f000765608010b40160f0300700b80c040c82c104021903001a290548a000020306860040c0601c1074a45005082c603c41c0500150000c500c01c050b02039a501110720505030390310104840d40611103510004c22074154412043e00704408120b4240c1ca010302802e121050741d511342140002c90014580d512140c003095130b41030791024000d890585002411101c518018440040e220a1020480f2440003c90034225200d03940c600c844d40c10b901e0380c00c400e26000201a641804420240d612400d0001c03c01580300f06403d90141400d2803003031040014220800406481105088043c44017503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 902622985 1250 902621735 902621777
    0x5130506090c160b010324020c28081c05090d0c0210030f09230d0509060703031e0501080105060d03120b01021c020106140604031203021c090f12 64
    0x3042d5924141d00daa140c00650115404a02d000604204a40000204100c4001072500c18901c000d5040c052006c1c40c0c8410304224010701c1504c11480d4008014541402c80301c2d06803041525a08070514110401600c0d821034540c0030030010040174400000710075804034580728240e080301040000c0d264000c40e0490080a5074100b040213842084c4141070042c020f8000d41c000c0c00701c0b42c41030341c0500846c0305d5818035580f140c1032146031034400300e00100d030315105a0740403480015461190701c401d410180b00c2c50501000b500002800c4040c590384190880101989190200042c40c2c031040c04901981030201550075604c1c0580018000d5802c1981400081d8001802c02d501510141002502d151a880100d160040070425104a034404081c0645e0b0164190414010394400100b1054218225402d00c541c510071440054515510048100802486500145041210080740e40602d51b03200761450100c5684420842c0c820000400b00310422240c0b685112108500b0308050312808840304442040e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 902624235 1250 902622985 902622991
    0x1009171b010e160b090a180e011b090b030c0c0102031006110a03090608090a0210120b1e090711100204140a0f0b091f0216081603060507020a1b0513050609 68
    0x113861000308414481d5200d0380352200c0141958060000b04103002d43d030320b170014800c000c180c0f0600c2d401d200400c035180c0c0341012902c060b4100740d6514251326150100a03a5140c00207010b019a00b0030810001420010034000344d030140396440001070744c2a00d0000d01416070246250610f0058004504900c0400d130002c070041c040380c1e05410f2404480d0f6a10140340e04080b030300c40000b5030250480e0045242903501500280355150803640c03c2180c59115010443c10345a40c4100301c0381c1811142c0701c0800ca00300b07100b603070b42c0025250400c031249400e070505490500c13042c0b02d4511440b6601040410808000a00c280440e40c0140c6200c18140e003000b1220003110098091114032500008820700a600d9406407030420220404030148250901380300203468601ea410a560080207442c008282e070340d004140201151494011803c8562030f66541c8405042e00401039000c0d0b000c1c00c06004040340400402504812000316401d02c01401c0c04c003007100354220b40c078104000601c1e02d41005040e03110789100dd60 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 902625485 1250 902624235 902624249
    0xe07150f030c020c130b0f06040b040605090111060903070303050f070206010b0903660406080d090f090b0a03060b15040305072103021009171b010e16 66
    0x802c0e0b1080c0d00180d10302900c00e00c03442d130091441192080b50f00700c190b0021021410403565842d82d4080304040200c28010b40c0150000c0305401c000410100d40138000402c045a01810200b42d200c10a407071190400b4030844500c0d240d6040050340f60201681031081587c03103400d00341c05090034108400003e580c2c14050050700a6824001a007030b4041c0e03010050170007002440007005150b101d071b4101c0003d1652201300c2c03e40a858001c3c0c241c40e1581904204120010501d014000000c0c11040801002c01106144690041d035103002c08280d0100500c20150800066156501c0046c80c0c001009101a0b007075020081d00b9107081103066017542c07109402c8040382d80000340843c420340203000042c2c0d100d881160004003000f00040010400c01c01040071003c0b6200c030107005070040728080d8070000300001940c00800680251060314941d0580750301003000580036804070104814080d4460090391b010780d46281c6500d85410036100c600d04240248690500043c02410010807080584110364220340a010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 902626735 1250 902625485 902625491
    0x130b070c0507150509030c01032711090a0e07090c0c080f0c030c1c030b060712030b041505040b031c080903090d0308091b0906220903030e07150f03 65
    0x3400400c00030315000c0e02d03c42c0707401c4100f4080d441c0d018143d6440b0034801d038040c2c0240c08280c4501c1d8001d21a9000034400321103010000c294070818030b008411041c0c411269522002c02da030015441e0340d00090b1252000650014890105a920f0380c80d11806912051215051654055000d94010048050240d1002007036803141c10880d54610300303000303008070484c1e80d200100322070741705000009411656110760701103140003c8501c0c00031420b42e49551642034009000b0070041000a441c0c1211070351a1030140b0340001c0d805003200004040c0d8501e00d44004000c250b114050280d49050320603078140b90412401458003098012840c3c40174a28104035406000074100064074a1405204942b0640340041c0a04409c00f41442d001d01488400c0e1185503c0380300e1030018411300e20740c49000c1e003c2000010300520b41550313000c0c10009010064002101c01880b112340312201c0108600899110a20a450128480d4101e01c2140d02d019105e60000c02c00100e0307030f6a56103086402c0301010341d030303103040386004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 902627985 1250 902626735 902626757
    0x1f020d1407020414070f020304210501090501090b0a0e0303060d111206040501091203020c100f0b06030405030702090f0c0d18080d14010504060602030f2b0c0206130b07 74
    0x424041c0490194000e42003943c49000c1d1160200e459210301015103544501d03080400e4100c0e540d004500130070740c07002c2c2e94110892440001581141c11548034a00118154200341c0c0c0703003401d540c00072008640c4d0641000500000c98090700030b151245981000550642c58010005040c3c0c1c1030824020381a10044090070a072a1660b40c0104032030780d190012103169013030a280c1240240390140007500d181590034525149280b00740220313200c07250a00e00400b8080311940d0728900812081500f030754129a0f6440003000d94903042c0c00343d8851406032010b581c445456005000b0000c90040807142c07204054030820800001140a40e8000c002103503000450401c0031010019003084050060080f400124464a00b900944c0005079407594203e000d075080d9036140c040c402500c2150041e000960014090303001c588121340081d2124245a01c220130301645807a11500040c1e103000e82041c845929003c0c101c0403c4d40401402c2e030054407060070340f84610020b886140e000c00014007000c0030866003200c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 902629235 1250 902627985 902628017
    0x10080a0902060f0403050d0e040b180c0c070b0c06280c0c060f0c0e0105030709061103070210080106030510140f13020a09060e040903080105010c06150f03021f020d 72
    0x5460f0b2420404a20035a140d86070305060395220410402c1c0d100181c0e00041d844420f00b898080e104d4a040003a203030520003030406011103002d08000b803083c0c84444041c0003405103000c1c1005540c000304602c3e43c035144e903030260310251409c00f8070080c440603282007610010004601d00880405060700340b03810008164031034800440d40e81180d0f041c0640664203040126140c000180e00800785203100d40c4074211009112001510700340000c480030400308803c01c0040021070b018118200000c411582540d141c600c03a0380c002403c009031515000000f80380b180c014084c00ea094800d031600030020149180480c1c1c54401071000c0c03000c3c5011164003032048a0983d580039120780c2402030f03400068000541d10307a8901680280103034014411175000440d03000342500302d03051520130b280c5429059554810b403a801c02006486000720035600300c034102d13a10b076101d8581e161180d1380007000e00040701e42c0c109501d19500400600c1780b420040c1410300140c03030155010345600001c0c0451075540b00d0801c02080600054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 902630485 1250 902629235 902629237
    0xe0919030c080f0309060a09052d190c06020a0203030d02090102010213180b1c03113a0e0a090507050d051303110303100b0306130c0e03010b10080a090206 68
    0x64000c0c18442c012800ca10300c00c0c0301c10f0195100c2c1001400301d49450b5203074200036040d107851400142580e040070f08074840c081038902400b002c6103100d401860058071514503480c0340007103144543c03401c10074000c0500700b0062030342902001422148014010b42404d0b40001b07480381305803901842503590000303d5000c1ca034000c0d0140c1d80589001c1000000c2d1075504d0440008032507000c01102d040324035100c4400c01c245401075500c414441611880024410141e4007a5010300680c25000401d10039005188521404000420224205003000c8e20f14241000090711600010155443c1448024610f65416887d40d15840c012210700c2540411551601d9806660340e20500c0041c8100e90305100c02c000c08482c001d01c0400040c4d2180d0b42c0c2c212280c0000c2103103a01c82c003040d2640c1103500d07005541003201c10b001c600910f030070076001080d00c10000340c101c03039410441d03000c801e0b940041a60302184850301d10b4203100359050884180c550076040171807200014010b210040c20b030888c91380d541c2040750035529080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 902631735 1250 902630485 902630507
    0x11e1203090e04050c0411040605041403010209270c04030305270a0909020a0605130312030b040606020a11060c0312040521030f010503030412020906010c0501050c040f0e091903 78
    0x250002d907003028285940c07a10f008110840c02a4185405841005228802c6034102c60050340c956040a080000303c02050600c8410a0307410340d0240403030012503a4088005500c00f81101c84540302284005030301090000003000703180c1c50390080c081000840c0e0072070b00300c0d038504030425214a00b403433104243c001080b008200f0350350495404140411032980790381c04007141d54001c84c3c281c0d107030a5503920119900e114a80401840c03452807141080040c03041c001c000040249414081b42c107900b00c0300440e003202c6144d032200d00161302018a00e81400328014a64a07060b03004d80340c02d803804440c1d034cc0e056941c1c031450328001c03288136080d030015040c080c044c4210350b4410f0743e0b84003241c010901060480b005410582e116015480c02d10300010311864004211000c444690410012581d21034080001c00c607401018241804041c07040c99000620070b204540c850381c982c090041c0c4407130030208c005a200880b9088254007500301070500a0001002a51014a00c443e40030a80d80c84070358a012601e06ca014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 902632985 1250 902631735 902631749
    0x212181f02070602010e1b0907030b0d060203040b15012c120601050324061e090109060810021806031b0a02011d15010308161403030708011e120309 65
    0x401464000190701142d000c04445441d402400301c1400b00d0501500c80b9094420a1508403030404c200c085410314404065103c00282000200080002c0224401040b165421500356500204010070803141c400d80940060300c02603890641c3c285000040c0003442d64100d40300348414140494803502c140e900c1d2403040b5000281c8440403103c4401169a9589001e0140f5440f074090b1144880c08007900a014007041000741d500c4007042d40340c2c1c03418440030001000d040c40104402d0303031407820a40c03038008801d8024508203100040c0245409085800e04004c240b110759064010040c8222210101e90800308101c0e00b00c03281c656a458400b482c0e10003003440500000015408204680c14940661143c1541c0107515545000c2d100350520080e251100c10340d040030b074440c00400601c0890360410242484800b076100c4440c10340c2d819201c4e045c0d10004110418900d034000810031452903440743c04a0b0040003400c1c8802c0c0c600d0320080780d41c3c80416190050115076610012454180740c07154165000502ca6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 902634235 1250 902632985 902633029
    0x603091906050a05070206040305041a09100804110d0b01051005280f0c05210f0c1015050310020d0603021809011109010903030e030708060f0a0c021218 67
    0x86032030207601600701255440700d050300e400b0004a003180045107040c4242d5242d80e0302850030b802c20352045004401c5001c40344400100740306415903074440c1200032002e04016150612246000e1500303050780980c0c031586500422101007044006500070380418155142100c0b0a8400b80c3c448400300d5140c0a40c6510714901e612008078400012030044c041960b16200d0390740c60324645004038050303407058496040200b499200755038542071100c91164604040c0c080382c00607850082e540c3c242c82a40d402900301d00120340c000390340c01c64552048c0d21034800365401460000030581e1410340006d4803154074128000741c02c0e03000030340c100020761540d2040000c2c45e4002c2809041e50417075075999030101c0c2c040312100b1696280019460b4011707620f000f5500300020580d2902d45507401d42d50121003e09001c0b142035003500c145a400b2402c040203000349480351420568012007464007040358404e6408603000351040d5042184c2101c506000c00b81140c400141061194101c078113400c0c0414040c0245a0900c00d0030b50b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 902635485 1250 902634235 902634283
    0x10f09141c0b0f0105010f080105190902130f051912030e100512070c0c1502010608060a050709060e030a02040209180127051618091112070c0b0402060309 68
    0x909055460107072005040f8640343d41e13203030001920381000f211500c002080c3d02600402080c40c0404100107998122500301c171601d030762103402d00c080c3d0b0021410740c8001e1487c1041032042664482102d00103120071034181e00411450840300304109141d007e2042220400000d031030925020381e9150414001c06400002c1c0b14900306001070103600894103031094038900b18081401e5078803409003d0541900b050800c84154039011458120f0a8000e03402d105554950000144040c0284409440b4000b0f0f03200c04a10740c5404500182810740307035088182030003406680c50200c1e490028842179060b9041c2d80060762030044c1000103c00070200c0c0010616800044004034507580c1885180103800c401c2c0e010402da140354070420b20140d520450324941011642c80400d802075102d80d0074181280941d15410112584401704003082d01c0c500e0410400c0741d1030010322401a0000e0005299204a040c5003200c052000b5039250072404101400c064403c103004000320f031000c3c3c5d0600c8010b00c40702d035400d24080000c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 902636735 1250 902635485 902635493
    0xe0312220f0b07030f0b3a050c1c1205090114073017040c050307030b061518120c04092a030206250f0f050c010f09141c 53
    0x7254104002803c5c07049030084410380d4041c0d01c00d0b540d0010404030341e6a13071980004200003040615401c031000a000034401c1c4440400c0072848541c082e0014046001c07882060103100b011009104511101c0102004d000c0740216001540c0d020fa5440c0260b510510003004992405040d000507002d4200000c8200420180c0c2c41c090440d10b840b12680f0050f45490110350300d981071500c0503032000c1814080c00225040018012035481842203421300019501d42d40403928000240d0411202168224144401c1303180c016428816405580b003140d00c0c09021610303801e548450742c0701c1c42d4080c5d480c2c05458001c0c1201808000d5100b42c02900400130583c0300d040031060082d19100d041c6000710050744c90070000851224481c00c0e2500900752925080c403907240b1520181076160300c00c09200c4035910900001b034040d000781e0841d40c040d0980d01c4100c0c946050003814600301d000224144000c1d0741403880165000310030384080303400036414001c40b002c0410105201881d2400303812405480c2c0c2810200308 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 902637985 1250 902636735 902636753
    0x41214040f23040e190f08040305061b090a0b07051c050403060e01020c030405120723010e011e03110c03130e0c0a05040e04111207090e0312220f 64
    0x20b50389103081c0849280751030500040320041100d10201707030016a140b904200b10b00341003880003482401900c03001000ca0b01c0b00322141e040b50300102c8058002d0b10038403e54540da684403a14003450310340d50510b0000c1030f000040d200d88445c0300e00d180c1c0d0200400d08000703011091200d1080c410303d80150f0030303d2240c1030340c005055511500044500314034045080301c10750014800e581680e0b04002c000d500d450300b00350400c44c0c070b20700d03070344151003a4850002c021030805900300d0010000d100c030041c11910414840c0003d4508080d00c0c45182c10002000c480c142c0c09041401c00176140202400c00103a404048410b4101501c0b803000507000074400061a0074007408001d02003421240b2200e03602441d81c84000058056100f1600030800043c814001801521050041c0030303001403003003810001c1c1c1001d00000c80c40900d200c0c002035101d030300418000c00000d40c403400307401d0300c008030790025610300a041c14003550f801e04007a0400001460400c180c1131640000401d01c0b11603074201c4d180c2e03d108851483c00c0010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 902639235 1250 902637985 902638019
    0x3030506181017070b18030a0501090602040e0603060403020a0303110403020a0f0312090b09041a031005060306070f0819060e04050f01060e040515071803080702030706020303041214040f 82
    0x350940070500d15107034100803d41d541517880301c804444c40d04004040c1034207605196031009906004050a83d400074409211300180c5901c1180c01684a43c5032840031074507120024a03050182d04103004002c0080d070b010501501056044c100041d40c00320b0031903580b07800c1c059900001c0d0032190015010888040c1c2c5200c1c03004491080001e00081ca04103030301151040d8003803082565200003030007811030910380742d000b103201546081074400e00400610000380c0303420030498102d00c00b96030b01e0301400344030300741401015417150150800d41d08100c9015001891518010715031105c8500d580c0550804550300e4002e14020301091070040c80c2420241000b980300e4403203400081680d8a0070074002401c41c132403803143c1d206d41c0d0000c0c09060340541e17050b55039115441c02800d20003007100c0d682400c3c10b85d84a20744550059400382d20300176210070061040c11b28100c1c140d0041e00542d03005104000000340e140c8100011b0038a07528220704604d06070400c1d202c0301e0246800c04c5a848404803800705c1c8540e9080c3e40210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 902640485 1250 902639235 902639249
    0x720030d200a030c15021201060c020f1c0821180601080606090c030a0e030c010c02010b0d02210c0d060902041506080703020f04080106080601180b0d030305061810 72
    0x500d0090242400d540c2c85070084010b011030400305504000c900390544c01754080e46a03980c05442e200b200c0c50ba420342d403c1e007600030030003159449103c0c1040d0b0520a1042c4c03c81c5105a404840c0c90f100700c54084002c2c0c101c01c400034203202001924004080c1312034643c60070400d600e4006c4034603040c080c3c0181c040b07000b007003a1342c269482180c000151024002448a000300d17000ba1400f19142c40e44400411240e00041601c01d00d140ca4a104520440d0100000d00c00a414880009903072441d5060003402d403200442c0c418805c00015841c1c1c0d0140e038615549084080d210201d241c4c1903001010640d051102c0904600d40c014100e021380014005142c11080b4040e01c201c6003000812031941511144107000d00450700010002000210060b001e40c0c002c0010040c0f5104441c2029601c850050a440960708840d615030400e0004101038030415000e88410240702d58140700303290702e42c2c000c1102c400801d0303406001c158494002c0341c3d080e200c00012505210301860020324034030b410303409550207901600c2852 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 902641735 1250 902640485 902640527
    0x203010231060905010302070f0b0f06032a061b0102071a011710020c25030308070507080d050601030221070806030c0d020f030c030a060605040518030720030d 70
    0x70340340101d2480c8081607440c01d4a60110392810000110002c1d04040c0c1d04541360743c0e04205400c040b0304041c203a64410310714408120450326002d010b16061582c95101050b0007009524030300c0c1d100c1100b8405840b807a405560030354403021109581005158020740c1441c00354800140b403414018003404107100c1080440744062640da0324484030710a1482e640750301e00385401505800618881c250000c040b030010220440d1122503070241010340c0a250001e030352000c030850000c1002019041880700307034400302c2e608016062090589401c000d0744207030080100312994560019240b070307000c0c0d4140c0303034039002c680365043d03002034500180d5400c02c200b51089000720b919580003602d54600003500410307802e005003040c0700d0309000381d007884003c0800440c06a8140074104580c285518100103507403155019000104640d403800080c8011070b6006005c8260003001e80c002400c4c040000011102125405442c0c07554040001010008070810542070540c140500408500c07016032041c00c200102880b90600c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 902642985 1250 902641735 902641807
    0x4030e01110d08100b12040605090c030a0b07020330060406061407020a090905100b0904080703080703060f061205101202060c10050106030509100501141c02030102 72
    0x41d6500c051a4060034102c1d40300b80094010b26110303200d2150024002914030024a45401d80842550018051151514080c004220501210307001e00754005c42c0c4000074002d441c0008001c03a0f01c404050350090415940c403008a03504034400c00850b05400c000c1e1a90030b0050451140d84841d07280c2c4449800201c1c0c5000d40481c17010f01e8a8421001200c800743c403402c1003190b04001d03512041d04030f640141d038808030490000030321003824014181454810700150000e508000c2083c82180c0e0244452401840345030100000500c1c00b2044503100368050404881d907650300c0303804034040c00c1281c112140143c0d03c468005585074210420868130f00c1013a9090041d90384d410301d03c800e002540c0c8542e1010902001c2400050304203100108000034440e82941d55021540400c40c05a50080e441200001c0da580100140008140701a00d860b1003d044103202c1c55142c0306034107440004080125105400c01d03900918941e000f007441c9510690f000d03000f55101c0310b105c22044142c1003003010420001c0c96006031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 902644235 1250 902642985 902642987
    0x7050901030f050f1501050403082b18020f030c1807020c0f21070905040503090406060f080a05270304142b230a03110102070c0528090504030e01 64
    0x3e85485080c0e4000016015038644004050b021918410340d030610004000c040082103040000701425500603800d28041d0503008611b07901e10300180c02031140c03146001602c83c1c442d10361070b007000500d5404603101c108441818000030f0034104012012684408071100f0302101102d9504880d100341250340070340b00540e503000c041c030104881d40e840712079100c10300c41e6400300300030450b00d4005030411440007114031040c0c0301d043c580103c500c20b940680c0d081e03001060400702403425000d0b4601601461400c01d0078003d444001401100700505078648054407800043c1c06107250041e207001c07000c85e18150000d01803102161030786a40c02406105001100781c400f0030710b030f82031000040080402203144090300040036481500f50042e119000c0328568080a40591640e00300f1071411042201c075005006031141514000c4e040300d442c0003001019900510110020410120504007102c1040d103201810320801c1c000e15000c00d985055414076101c040c01c0210304400140c0c401e0b1300c40e42c82500c0380040030b804000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 902645485 1250 902644235 902644241
    0x3150a1512020a03061e0326030f091c0e030105090a030c1205092d040516110c0406170f0102040e070e0307081903080a0605151c0507050901030f 64
    0x204110118400741000860101d1660003810058510300d4001001da40b114141c03148280d44600340040851145820310034030074a04a55000707a035000890130031a1070200e850a00703174000209200c0c49030f9000400155010420302418100d110810050700c4048411b0901601580c02c0c240303110300070741c40c140004010765000940740c61000d42548a08910343c04664490000c4003446018604002041c001d81074a511044002484c0e009201120078440000c1201c10780d03402d12014940384240d040805001c40c0480301085040c004d41d00b0304d801c007844040805032610b00b081d5040c096400c180380c80c00026000404811410116850109030b600a9210710780f00f0b402d074060340c010400f0752030500d000324910074018081881201400b41c183d84019986144044c10142c0100c1e014030400e1032900f8104c20181e0149043d0303030040f01054108911818200464520005440190146a000034280c122514800d500c4d40c1000c6142005000c00c0c91321140003842904012031190119081540406100311240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 902646735 1250 902645485 902645519
    0x706030905150915091c0f030b09240f190e07140301060e2103090a061d0405060a0b03040f110603090c150d060b04150512040206071703150a 62
    0xe004160030f00891414411584c00070346062102e104008030811103403000d0750b1200d14003050340c5401c4203104025001a00f581e0020f0400c52003240d00c0d81c10840c0480312010f507581064064400e40c0020310000c0b0201e01050040400144c2c400d400201c0755031030b07405000820060ba94401094083d039203800405864820142c0b0394100340840c00c1c0010710900784603801c0124a094000c8c001d441903501040c060400d030780b0781c17051200e0507000001d80c1e00c2700c1d06103e049480108203d240c426940d03802c185400b91100022002d1318840c2c3d07201c10105500303660b030b482094040c1100242c13031581d90820785007148507030b060100101c408400c02c45407078005140600549110380e071001d0140016060400c10021140c28070070b840c400200c000c0c010000702d80054466080601f8030040c0c0640d64034200880040d0301c500d00c03040c0f00100074040000d41c400381140d4462a03041176050302c0d041d49510440ca0080d22400364014100c81c15000807042080413403414458035104481a83c11601407034440e074070a00028110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 902647985 1250 902646735 902646751
    0x4060b04061e05040c0311070f0203070f08100c0201092913150f0f02070b1e04050d1d0d0813051c0212030c0115060305090303070e10020c03070603090515 68
    0x4000400007800e05070000d200350b44040c0f030300085800e8070080384549908a010300b509c01c810b01c81682d1046050400c0f800010b8610705c103400b0200752404040955890b9070000d8020301648403400418454001d40098080c00e0744590a41c20041e10107120704900c1180d41080507042c5030500204500031045c84002510b40e170001ca0054400001212401c00743c2001030030008196034481400d030005000e440a031025900c1110300e015a414086800442044075024640d80004110148030010704002410481201203050041c0c410004190760305802002c1006150400300f02c056405c00c0250003001025411161400c11106503160024401090501c9103e0403d2501c60601d000162510341004c4a520800c001201d1500c1500c0f002203080d940641c00104d0390150b030500c00e00109070540613680c4c1c4171a20800039411450b01101c02802d13401e40c100000d010701a90380c011a2658400d1090140f041c6015044585040d601d100090003800040d0050f145400f5402070004004401c0103442d00803411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 902649235 1250 902647985 902648039
    0xa051c09030c020904050a140c04050108030a0203160807060609050a2d02070c03060c08011502061b0304021305160e03010912260f0a0b0d0b04200904060b0406 70
    0x80d0b5080c0081c104d0301400503180d5101700000000024200041142100c00c140094452014960b040c0001d840041c2c000000c2c5da00300b03020420415500109641d0280e080c0681f0b107204a18074144090148502c070f1004e00f6583c1071080204818030710b07030007550194840660400059164209070306981d05030301c1914070304c46a41100c1405000241c1c0240404a004406440b0b103207a9980d6184100e8500401140110301402c004012036006040c00a00d009281e0010703001d0381c03030118004c0b1401140d04030401e2000380e0201c00715003951a8841381c0001c0e60440e04c2c040109050241c1d801c6400802810034000040c45403e001c0107905060041012041e44107040d02e101c100c040c03000b6144a40008140d5142244ea100b44442e0141d03988006400b540c7c240000c1340d100d003008111b5800342c1d04800c2c0726500660b00a8095400140c0702c0215a600c580c1005c0c09101c07242040c0e0910400c01320042c00d442d8000001020b001c1444000d034030401b01d80004407010488255500001c0c040f05904820110301c00ea1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 902650485 1250 902649235 902649257
    0x309080c0907120b0415030b0106050f09060708071a01180c0e04020d09021801051509010203090f280806010608130602070602090402040605130b0f0d0e0c060a051c0903 74
    0x40920590242410100b4000c580e04c94800080f0b800c0307600c132280c094100d101800041003404150468103002d080d11745003951818540b5004526a0301c144501d86014100c0013443e042404101c000759160b10303920441b000a22482d42a01048900c400c2c01140c2c51141491000005491720384201e19410f90680c8a501c2541d809004000c000d400c020315112105446100080042e07031110390310b8a400c4003592403080f01c2d504050500c68009100c00c8242c2140701c00f0080780f40349a800206850350034100301c6111048018550106101e940c0c0c0641031390144030400000403400190400c0c000607180c461044844a0780d1755113048030004408d40743c000341849103d184901180403134004110a60103000058500b24429001c0343c00ca92040d84910001103000c00e40448040d44d19170142d0090244507500d606291000c0030252680c414545090b600390354500064440210034050701754640d0004001c02e880b0056020054032503400407a02c0300c00c0d90031440010446429611500b590b89403d40d8401d52610 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 902651735 1250 902650485 902650487
    0xc040e1f0e0c010c15090b0a06060e150901030e060a021b150c0f0c0706091d04031b0f050a0602030f070f1e02160b0a0212030105150304080717070309080c0907 70
    0x1c8104e541a155082608880740c900c0502c2e00803840414400c035242100d500d041c148503011202d240d04440c0c100321203070005400c90351300c2e010401c0039600003d513482c2d601c10301400140c00030032448400201c580038040400c02d409200c0d038080d0880c801100c2104043d9003950025580322401048102e02c045502c2c800f041c0002c1005010744bc0c58901060030034030f042e601100301c9141031401d50000000509000040c4142840c018104001c41c619020416031818290780140030718421044140b101c95500510000b80610700c080c2400041d04682503401b8040541889000f95108542d464185039049000c0b500702845004510190461aa21103480d144030086103494194135020b805e08501c1080444102024a10a02d00040201944990366002032070b0003c1d082c52812000c00003206000e000400c01c548501d03130544a2000c03841c42d103030b65a60700e62805174a01d003d0400013030414120080ca4002c007040030b100501c100b60103500c880140f255544a6035503180381901443c3d402c594280d001c07c00072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 902652985 1250 902651735 902651747
    0xf0801061e0e060d050115171605010806010e090408030403030605030d09090b0a1710060b0f0904270308040506341b0c0317070804170c040e1f0e0c01 66
    0x3d0042c861103241020782c5a181c20b41e04c45030342c00c1c01c10492000c4200980b10005c102c00c0308404001d0050998035030b060030000f00c3c1006902c105410f000e01d0b01e0010344203a2144448030390314140104890b01c1400e00b41000743c81d542040b10110003082c94441c01051502e00090700a40d15042aa2018030301410074030700002800e1012410b64001e14403507408101e5400c5010142d042d40f14072001041142001d120740402e07a1216400900c2818040101401201400c82110b80020042e1030115501001104034100040c56683c04082d034510758400204040d07222024a000d140690112501e60f200d410341c02c985c80c1800503001c03ca9180030940c0038903400780070344d0414400c11542003101c440c0740b4607840d168200607021b608590f8a03801c0034040c0304000391b03900807154109414800d00c0c1050129507421000348514069840101d00e89040c08515810401a15030301c00c0f8040c10521084a00881041d924494448007606503490041d02c8244210140f15113070801c00110014a48501c0c80001983c1ca = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 902654235 1250 902652985 902652991
    0x60c02040902040609020706050a331d0403021006210c03020406060c030206100f0b03092a030d031a0420070803270a08030910060f0801061e0e 63
    0x4a5201c0880e030780980e50b5031203140e000b04401c4002507610300da10f04d08031b4100c030401481c2108c1c140c1703850b06078000c2c403000d1440300040000c81d602200d5141e840c000e80641036169a48041103c0c010341c5c1906000c900d503008102d004520076021100b8215040c00d003002950424016180141d503030303200141000503101c1c80e040740300c2d01440c4c2a40340c15880740c0114003614120703006800896800e603030010802d507040003141c1c2d0207031924a0040c80e00c0d00740072310300101042c1c03071081400c05038000c00420220102030101d8a18415007011288400020703c0082008020022aaa12900580c0200038050380603001d0905075244060f10f05850f0a218800c210041a6400e24441e844510006980c000c6d00725030010010180103040558407403400c0c8088400303144108880402041148080504144000442c1c80041d90320004c429102c2c0c3c1c451410310f19110030144440c980301c1c00d146c00091000130b03210240090361203e600912002c0d403034a00e014110301c4d07070702072a02d29400b04100400c905480b214a880e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 902655485 1250 902654235 902654239
    0xc040317090f0306070f090905190e030c0d0207030312020c06011a070c1409010510081909081b1908040b03070201111305100c150b0312040e01050307120b01060c02 72
    0xd42c1c9502c8001182c9020802c4482802042c0012034174071845403c032002100a2100c14000d010b103107420004107030360003200c15018500503101c41e09040e240c1030a0060364100c21007542200c8000d140032030000c0d0ba840c1184415004503403100e05d007900e84100c0e03008a03a094500400204001e900e420026110800d0712a011901c41d5001d00110001030201c44d51240185803540800b00d20800500410010b424180e01c60745c400c0280b1046852902e80050309280d04c00311110201c0035400c80e0780c501c54007401c2c440c04011b1030307151b0008410030020004803503070110464040440d07419501c226a1070140382d080381c001410110b018082000b044640c00011030b8009814400801d0300c41c80d65154100d641c00000701c05004015101092240741040304520401030075a140100e283c1e500c0c0c0c0c4881545120b144100202c46464100081403034030f0800c10304960031040c6e4185039881c0d0341d038500001192402c0c010a071090091070800241c11200c201c80c44002a000348840d41c050b407130f0070070030b03298010f4001c0100d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 902656735 1250 902655485 902655499
    0x51801030f0b06060f1227060a020711040e242e0f03050f010b0603070e1e13020901031803050f0c0f01090f150e062701051e0c04031709 60
    0x4001ca28810003408901b80010014052410308000710540c40340c9409409041c882c2140362410f0038140000c005801c5152980c0051b584c5200c0c1c10035005444048401b20380003406c2c51038a4030442400034075841c000400300402104c81d2429218900390301c00075100500009440c0b03004982c180f040c048084076404040d905100c02c1070ba1745550b0924075407294401e903406d81001d856061701c0c0f0820f0151710a100e904603031852840c80c1024000c0c1402c40005030041c05009501400c10031000311700e03001ca0704843d00420460454150b8080d0402a520840e06240041d06003441090308049130104242010741c591501420040385661304100e81d04a507840450a00c113107c119070000800b84a4031060310300038070700100250040c2c1080d982c49588411504440c03450000c0b0b010481501182c002c0e0407010841d001c3d070000d2040e558240c508001050300116035444c280c24014540d445902c10140d0403880a845481a134503144e00d5240c501641c030004d000340503003005041c864078a14009102d440b800030026 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 902657985 1250 902656735 902656747
    0x30c0f0105160507050315130807050309090f310609050a0c03030306061421071709060403080f2a1204030e0f0409030507060c0311070309051801030f0b0606 69
    0x81c4118040d0b82010346558104000a00480c10140000056101240d10b83c8840f410f1903407406100b2541c4690203800744c000841c1046c100401402102c08203100200400240d04003105030080981e001d468a01c0c0c03080e0160303900460780b0241000303203c05608c03240144021032429126100609003414041710b6500a81c040d800003c1c840c4421103001d103000390340010f034030f60404d0000b611081c81d0440c1601500c2c1c043c00b14040701c0c0d070034003480060001c48001c02c910b02e48a10a00b92000000e0442038802c150000c4100b080c0f02200140140c031581c0039503916409500c8004030b419120006a400b940c030314460824004180840b5425079080400c207010441c948a45e404031580c00420035501200082c030203019985052402483c0b0985a00040300c0c10000c00040d81d502a080348074508006003c071b501c03203080c00849406a0301c048040c21a15002d02e03940d0f80545001400780300907001d858492118030140605612043c0c6149050702c2e0301c0490110002280d1f1990032203021b00400c4694042008c11003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 902659235 1250 902657985 902658007
    0x3080403050d030515060702041a03010c02100b04271a0a0c02072403111306092c0a0209030a140a0308010e040b011203030b091005041a030c0f0105 65
    0x5000950289010b020400d80002008081d950041d1100d20720502034403a407101c50392500d00b1220b000764100c1e03002403200c0d66003038410075074003400c41e2543d8154604003000030380540100f0700b1400414840d008200f0b0b001c808041004591542803820008641402038003c01e1801120140300750b40500b001d6410540c4007151401010350407a00d44281c1c82c2c0f9a0518032410b41c04106c160040c22800e0482e0580300c0e032202e80480440d620452417010940c0300e001d15800843c45204992602c000c0c4865918400e45501c0c01600300700c0c3c60310803d0300316008944540d4030391400c084d45400c0c5030b000003001422622010070407000780d013101c10030a6140c002c0d4003c0300c00007503003442c500000154800290590700381500b0090182c4205034011042d510610080100240d011004a03055400401034240300b036040e420102c001304a061801c94000c02303841e0921000d5070741d89c0c2c40072086400884090100c0e10112040c1f01c4181e1001e209550035902c100c42c2e400c003614011700190300c01041890540c1c140065440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 902660485 1250 902659235 902659237
    0x6071404080303011d060906030309240d0e06070806060910201006060c020306071107090501230d021e1206190e0a0c0b070c031b14011b0b0408040308 66
    0x882030003091402c07031010b00040301404c0c485d40e1210040baa076000302d203000004203440e0b1092a2025109181c03403a06010000c1034411100c0340049100380981c0c131054020300740d10041c280f0320000000341c404e5400042030684142281485458050009810301c2c0083d400d102124240e1001a0180444420503000e26000d6801b102c0d080101400280380c5002040e61060449049821007803c000f4680005000b41e20001101e507001007103407414400c441100c1e4005414111641c209900b080d080200001d40c844200c510000344c801c2020400103015200d604210500000520003074108100c48101d842d50b044202600b4440c00c005002c04515628021945003043c000b02c45046801400b00d40d0104c48100b288200311030387d200c000040034002069210004442030300c1c450b01c1c4a00d500000c0c62010003980c3d207007000003158840b041c03405e00c10382211645600c4540c0d01496082590440050985600c11107203001c3c840e1058000011012160302d8150031038400900a580303411041000000082201e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 902661735 1250 902660485 902660489
    0x14100e12090d032d14040b0403020904242003010513270503070614041509020103090f030815061e0c21120606040f060302131a0406020f0f0607140408030301 69
    0x12403a50411130075040040c080c0d821014108995100c00c0c04144403108103807084505882e0111402083c550365803903d6050505031141000325101c0ba2016119084040d40281c11028079008814098040250000225010034411258410f0010f4004005000c196000700c03505080c14018214842c0d03003041c003070000d40081c541210395a00003d42001070022911801005880007240c000650a040d00c5031041860000d04030169296070301524400c6a01a520003d0950b9000c6103282030f4401504000d0140c2070221200729034902c02d88409142480c2601c115400d003011120340c6000c12400141c01f5980b038005080c402d10510506d000d2803010342e040342a4420b01e0650780341c41ca50f202200300008180f071701c0c0500020f001d10018442403082e075401c13200440c1a50031501c3c0c0140c40c1c0c0400d580c0c1d80a281201d034001450170500560094600d107107c0010020740d0712a80840b08000b24201249039182d1441103480c115410001c08100c0712842402c001f0409018000c590381455280c0c0781c3d0138207561082e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 902662985 1250 902661735 902661797
    0x3050c091c14031206090103110108090a0b01090b100e0a0603090302030c030c0610061e0f030b0d060f1401120f020109150203041401050306010c0303050a0914100e12090d03 76
    0xc030340c01d9404008a051303541d200b00265845210f0b03514580d9003208c2409400f4a09051120090024901c00d50811201000030341007244001c01d941e41b822218018490308008501810002c54416502800391100c50890080500790700b03071030b41c43c084045008040c1884c084003140000c200c92540e8810030009011015103446c054402d506010121071182c040652215041c4209102c0401588a94042c8103003041554204040003035081c40c021402080c0748554141e0281b0036440b58001c1c083c1c103500120400c000d45034100982c403108207104c0000c01e001d01c0317001401065808000002800303200c4842e10584103040c000c3d500c0380c0315506142c24190501030140141e001081c1002641d0201c05500503a0000703003055450340c248040020950341080c0c001130289500d82010a0b40100203a00000000385c018a19a46002c0800c50729038564001e0b06260886500f81406d00e5101c440c0400e106646440c0c0c00e4925241081d07000c1400800703290800140d0902003000c0c08074640140b03c50151801d1002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 902664235 1250 902662985 902662987
    0xa1a19050301231b040b130303120603020306180f03071119081506010e0a06030f1b0804120c060903050901080a18081b010213031203050c091c1403 65
    0xc0106050031207030500c1d1400c003d0150310203001c2c00e0b400040c08081e00030b4401624030003508060311424603c0c0c41142e000c03060601d4001010940140251034443c1540e120b951007000e0007500d940c1c844165180c0740030103545a040b0780301080038002685c4050000d00301c00c1c4140e440202c2c40c81c030130703a04581292406a0f070010864103a9030a500c0c05402480c18041e0700b41c084800340c0d0030018401da030b0315003c44030004c070031410320041400c0b40e004100c0c030554074030b0041c5401d03e80c5480b100001c0151070880300c2c2000050402c0c5480001c2003e181c0b0b03c1c59803000b10b03600c1054681d50750b00d62448480348003500100703124404000e2404031b04039018924406007c2d4903540c1c1e584e0102d100040441100414068440745801036403a0f9065650340c0001804d80c00204907616088040d900c416280100301d12070759a5031000174404108050788180c002180d0003004240b0355192014825015901c04480003461120100f0030350b00d247ca010300c245c82e050200305141903800c0e412584d4102d42d4800695000c1c41e1640 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 902665485 1250 902664235 902664239
    0xb061203040947011704060e070305060a0605210d05030a0e0106062c0a1205120406020619050105090a1a030a110a0f084809090607080a1a19 62
    0x20300e12203640f86581081c42c1c074950184900048182020300580014082d030745070782e07013000c9201c3e00700610405181c000c003d841003402e0584540004108a12826000303546044e03482d550340b0020044007600d2a0703d0300103800c46402c410401c9800c0c0c0d000400b030400c241c0c3d40b0480b00103543c000b40b151402030645600e800d0000582c100010621007091100c040e0400c02c2c0b03880c00c214513103501600a084590b854418a46201c0d0703072034000c1c1003c2401c098a40d1140001c2030015030503a00081c0300740a001010460340b41a00d015101ca01540c20034003560b608622110301049101505600c034815041d5070040e640c050007500b00001c2c1c20602c0e02041540e41e4014810a81c00c280392080c070003002088000d615040c804d00e0040055120b0100c1601802a440c84051a2070300082040c0074040007c07442030065000007000c10541c42c0c252454081ca80184007100000d0718402002507850b0003140c80b42c0380d4030417a03540e274609200549601c143c601d00e800c0409144039101e80322140004c6107280268483c1407868 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 902666735 1250 902665485 902665601
    0x11030c030d1d12030423070608090c090f060f030d0f05092209110a080726070b0309060109020a021f06051c0b070c120e010c08160b0612030409 63
    0xf00b01b80a54851304504440c4082514002a0302400c442140c1400c00b40c17559a031a840c1d003020740786c5c004c45400240e94801c002c035081c5503804680c8541da04a55401e1a942ca460515075104468212000801c00c030559502074140520040d0000503001002d1184000c1410030f0b081030347c9a80040d4000341c50320b942c8040d0401c82030140c025440001034802d540c2c1c0a18006089070344500910a400030784080501c003030149144a8818a0011142c0c000c468955a590b95203491a51048501c41250b0144600200d242c0900b070003102c1804056034000c041d00b24542c04881402a404500401065500e0340002a19140d2000e80802c1e512285841002c4100c18107081c0143e81004120b0001c0041c6030f0384000020300c102c075407101d05030464585070a0038000000141d230540c0c0271441c050000300d0081003225914101c0300400ca8503034403601c187c5989480c0c0005005c5000b126240e501d98030340040c80140480e445562220801040d15601c0e4a4181d40066049040c200c1c54040003a0242e202c0c42441d200d2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 902667985 1250 902666735 902666753
    0xc040906080309030d020111090603040602040902041205010b030106140f030115090c0e03010c210207300c020307060c210e09010b071a040f05060a0c11030c030d1d120304 75
    0x205c00368002808041e510300120091449100b68452180c1c1020000c40c050140036410b076405010341e004115551a101c0b0480c04000b001c0340421100c940c2404814855400c0600400049038100020410060b040760200014600e2000e9247e40540d40e403494101290b180c261804014120243c000603c0100c40c10020203804503a84840d00a038140303c042c455240d03101e90192112000711954034082c140002243c0f000e40715240b0301504415a80304508118003000c100c60b078176000c1d200c42104050a0b40f40c029100460040f001a501d80c1100104008030340c00b490400d0ba030184903032002c80040d0b100c1019100590030000000300041d40d00c10030030300f0604058010038050305600d44418180007455883b2001c24002490742c0342c0e03030454540481c0800c1807580e01804d00651001c20b0310f20705d107083d420340e00050040700b10010001e0600c0340141da6080010040b034401d0190780300a11302d0591106104406400002d0111400d0304441210302404101404004a290b0410f1009507a0b42000d007055100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 902669235 1250 902667985 902668003
    0xa180204050718091b0f0c0506070e0a0905060a0e1807140a060203131a040806190518060a0b0f0d2010050d0b030709021204050105130804030b0c04090608030903 71
    0x5a924000c4a0410450005c0b112845c0085618080402920090702210850078200c001030240c4603d4003400200c40d00408450151001039032445a16a5122144002e803801a141c09030800304402083c0b085030740005030980d00040e0080b1004090707144000181c82c0000982c8a003c0c0480010030811103807800480840003440d040c80118146070185410255000c0148240d16400c0c55811041c1607002e08501070b200102100310075a40246004031150141c01078913200700c1c030007518000000783c00b1004942010314011101c0020700e541c0d6101158900101014044164800e1001e0000c01155851b6580e0040e2030f8825141c04e280249039080301c40400c2c0611404600c03031120450848140d90740481a120100b00c0103901003217084d80700c0003080c01c2c015244c01034203140b400024028214441882135900980c40784c0000c2120b0351741e4415494941d803243d0002800c80390704010070400704030101541e980222643e2f0640b8503183e6100c4510084801a900500140c3c101103115091441c060244641c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 902670485 1250 902669235 902669249
    0xf2003070602010f1a01080f1b0c4c09080304030c0b070c030c08031f08071a0901091a21011d040c15030204080109050f1608060a180204050718 63
    0x2a5038940c3c0021301a100300500c0404646807010000d04003030707422085909c401c542c411016681c0d001c681c0300241c03101a0500301c10001550f420703458401105142245d005000207220207605c20000311542008007640200b48841ca544401405010030195002140140e210b5128565444001d1030030900c0743c400105035409110399182c3c4a000709401c1440b025609502c100100e64030b9030740306200c00b44800c1210b0b5803003003450711040200d5101c500049400030340c0d4150050032002c903440740d80c00342e080c4210310885002440d03040d01003100412541640c50130091020142d1b00340182c0030b014908070603070040c1440c03000c0100c1004104903400c204850625030800440c3c4d10072841d1684440380314a85520400c03d55554900b5890046480f039810388010380004002031000225a0802503941c1100280610642c040e01c1da03002d10048141e1481c500310364080000d080f00b651904462401070506140c507010580c1202c12840c0141e135144600740c42405c1540728044166100c50340c0140b240f1840e00090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 902671735 1250 902670485 902670521
    0x3090a090c021e0f120d0e01051b0f072f0f09040209090a0b13120801030309051e060c07090f09151505030f060615070f2003070602010f 60
    0x1101840c0e0100740081c0f5000100307802e4007100c1e003c08265103090030a4100c81d14034090032002d4200c04104800a089058040c4014012810503100d6503080322004d03281c00c3c007049901025100d59442c00000781c80d000c04402c0074503051001d907803100f10700803401c1180304070354050489aa00220a0805009143d00000c0d500e50380c03602e1881001c141d0110020340007a1150701001d00143c0442c0b81004110391040c1d001c0e40b007400c5410503401c0903412528100c0204c9901241b01190040644583c018a0489030165200d038011403803c400d111030254110708200002150507036140701611f41d50020401c80a1090081c58400d18001c0c03036800300e40e0800310000c4e90906151200c004207010302482641c05400ca00001607140c000d94600300002c0d05540465058090000312200c3d90f440403507090700c80c0b58141c450171001e4000d4592048288901c00e00106a210400340410100c0c0b0180c28065210445000c580704154212000a00c1c0140f50b51202006039140c0c0e4800e20152200d00582c5400da20070042c032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 902672985 1250 902671735 902671751
    0x7020607021009150f1b051b0d080403080705040506041d07020c1509030c04181109010b071410021305010e0d050604080f07060c0305070237060605040e03090a09 71
    0x41081001c480e010301e16401d0300c8014048100392181d01101c4020009040b0003881d03440c0b07030310180c00c541009410035402260701d0300d59048c400000c00c100118031100d0b070b03842d5403960b11503606442c50b450107080c4204111080c400401c407500c6410080c0047c0002c600b009980d01640304e5100503400c0c0c014001c5085401801e10080240c40b82e41c4c2c8554050001201103441d101900080780c6090703050041c443c0d00030f04050002c4200c81703030076030544d81050040c28100c02c03a10700030040c812800000c2c45481e0480004002010216180e003020b40d00101002c41615484020b1800d20b00507070b005000c4101100c61001030401266030450000c41c800c500507542c03280005150384969440707001c0140081e1039441d00158550402702c050080710119035118104000c11a080c000c0100104421126080580700392440042c065a504e102c3c7c407480e8410b52034424001c0341511501901d9080410103d54035500d91101061303a0380c6a020b00148903204600035900c90924500701700118140b50b1042c0d60f00c91400210f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 902674235 1250 902672985 902672993
    0x902091005190f151106010306020c15090a110d230c040603120f050706020705031806030603061807180219051603031d010c03060806060f1e01020a0b07020607021009 73
    0x40c030126000090030002c00e40708490240d07900920301140a60344e003d904000301c2044000cac3e01038441480202d046800c055a09040116030450a0302c010700130360b020501c0c003000038001818501c0d02000180c0f41c102040000d42e1030050320f01c14903031044076580c540521301501032010480340180080458092042c5407454031078211100e202c1c0c241100b000a0a07901128050040c81100e03803407984000d0455561800e810500c1d16604544070440c2000c000c0500c020b07141c500740d000c1d24024070004003d000181c41e4008002c00b1240a803d81d070350640581000000c1c1401c0203d0003c16100d5603000150740c60202c0015202034002850b01c5806010090054001c82030f060510400c07096410b05000030b501101004006041c4805210701d00350f50308181002c0380695060b00a002251074003c00c07208191500020002d00018041640740c100301504903030b00b0038102000b07809280312010b0041d030f1441c511580b00d10900b103200711008800742c0d001304140040710b0340c1000710a412401c2071808000384592950303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 902675485 1250 902674235 902674259
    0x3061c141c050304060c0207050604060c031206060e1e040e070311090f0411060d18020103050c0f0a0302030a0e1504051614010c061d010f0f09121101090209100519 72
    0x20000d085d0682e2080c800e00890300801c40e680280030b00034425030302c0b140c0d1020000e0249480c0101100014540704141c220410700c0c0c080d00b016078006484e41e04010391910144403550341e2200e00d4100307040d0780034150302c03007500c45201d254500c8000b6800750840c5811b505011441122207905076008a000300300704801800d210001c01c2d001507101c0c00c2c2451340c41950300003492501400e2105070038145884030303d00c400348020640e485014400c1e01c0c2032150703946040101c00c81d80660255201d40542c10800c5410380e0744241d0045500107940800051140c40c200b9525251203c41a880300184402c0e100f404203100c0c1c1000704084420341c4111b5a02101c2c1080380c01c0c00d42e41c2c3c003040c506044c071002c0d504080402030141c01031016002e15404116900c1c6c80c2c000c5403800382103c0b04000000e03c1c600b00c01490b0507039290040d1b0000c0303900481050500382c40c010301192110281002071000b9540c0c0c1ca8200c006940300c22140d070041881c056880d83d81800d0004101421400e00040806100320a508015007003000f2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 902676735 1250 902675485 902675491
    0x17010509070c0f061103160305060103092d14030702090a05060102100903021f0f1d0d20070303050301091409150c0c030409060807270203061c141c0503 67
    0xe070000e10203d1615268002c1d2803400c1d4080340d07401c1c0201c00c0002440002c480080c40d01e00d02e40c0d080c410760302c9241c019812944085405801d419241c822603a590b00300b080c90328201800c10700c41d03039042809503c4054031010504040360ba1b68200003441000d501e04201d0310354000791810001c0019007050800030356140034824140b40075075256442601454024440400c104c4900c030440151500e041c02050003e0005226030706440d80307000854029a02c4461003040f4407c9020018040341345403040c1640c0405201e01c520302018491100c40702c0c025406d000580040d80f1988800e500c1394100196902940c88400500c15001044c2040010f441800512070250755424402c001591300c905501091a109a407041030b064400090005070000f400c1c0d2000007142c100c04c0c199001c4c5600d070303039120825200301114424290804003d0723000031001170740295000f11000b4005d98903010b13800840c0d4090100e0b4602500d01c110b00c940c0300601d00f0418018176903400100c100081240b0008000540130340806 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 902677985 1250 902676735 902676743
    0x111305040b060d0e0606011b050304140a03020a0b0c0d14090d060e010c020f070b0c0601380d0b1c0308040204020d0509030712080601050301030f021f17010509070c 72
    0x2903a032081c0346480d0102100c45035030010f4014030200f4200404d041e0b83d884241c1e0400c0c00503104048050b000780540910380155607001015514040c544900700b1a1641c0880800e5408400c05100000503511020381d0002840e05031040f5840b280e1184140d4100400c41054170207102e00410740310040c0c207403030003140c900c04002c0320041902a45810180e00600742d1a008264540c0380129904c030003a00090b05000000c4e80404903242140c0310b005140e09800317044032808480e4480c1c0010311800000740c150840440f91600c4618040c080c0ca800b8072819440360074040f004003000190402c1141c003c1c09200e0030041e0640e404000030200100030144120500b40140808c000907010a08640e01d2360110b4840c01c0b070310b05007807209043c03d001c8140c44e80d2029504031442c23030056402d00d0b0001d0181c020b05200e42c0c030584800b404c41e86151075041e110500303640200c0e07100c040d039805541026035900c0c40c50303d14000750340d80081031908000f4511007000107800c214442d020903810061510b60114040a800d540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 902679235 1250 902677985 902677991
    0x40608041406070f12090605101403030f041511030708030628090c200706120b0a050f0d12020106090b0312072a030f02010909150b03090f0109050f0111130504 70
    0x40c048401408403001c0180750764180230920400e646c03c0007401040d1002040595401c1c01c8100c201a524410000341d8031103108144000c020b140c03908802d0710340301c0c0c600d800c1250128203541401410f550190320704490400021080c40107908181c10100240341e04062040010711078405100c0300d0408d02c2c816107808070f45070f910301024a445203481c004d00320084100d50040c0210603180ba80c443c40346003d41400035980f000802106403060146002d4500c002c0c0c420182c2c036041c00148503903111710918064011160b10307583c03c0020b60503031031003c4404040d400020260300700b2581c1c00990b0307440440244641c0c0491400d0080c51008411181c0103588480003c84080d61501d000c04002406d41c074040b2009800705002040c841215404050f0a101340e0300ca4452170784a00b0031108503240c45a101100041098080c402d030301304840210b0f00104520200c0c0c1d4a2001d11780c4080c00d60740d401130100c1d46a000700785800c180f000309000b006030301341114240d2824168074100c80c0c0d4120301240b240a1249403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 902680485 1250 902679235 902679257
    0x913060b0f150301031118060d06020c0d03060302130218061608031303080c0408031803010b032401140102060a0f060e1806010e0c1c060b040608041406070f 69
    0xd505195076410920203080c504004507400b48004198009200984030b00a03850204502854850f10740a011f000c442e00c4050240c455405004400300010000c4800540c2008546500c590030862008a19525a0049a0982188180715004c0100520180354500500c00641c031803203074201041c00c01000351251034407803445c5a0b0b90341007040983c0c0301500d101800010303c00061000d4003a808054047c2e01c0350105034456050381d0791148560b108009941d002401810003801409040301c0c5124002800440c1c410302e80c000007814503e9044001d21030700044105062315a0710810010b0040591042d0b03260101d1001c1c0000c2e485403c0140301c0038847e607840c1c200e1070020440b07034000400303849542d05411852030003a101c1e0109078003c900d000014851100005804000e19425501c511040c0c00840d0030000141c460044804807400c542a00342d8441c0b002040310059140a0801070500b5605c19806017410308000340000c03480300d5501915004102084001a001240d60154035500c1c9030030001d402e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 902681735 1250 902680485 902680489
    0x1d0f040b0612040c15090b030a05070c1b081c0912050f030f09190308041e03050a1113050405070b0c010f09081e09151b0a080a0e0913060b 61
    0x301c100b281901c801c448110610040c03104102d0210155608141d10704c080501140055801b10351500ca144c03102d03d000c00000345003500b2030b00450780112007820075141204c03036640c036815402100880ad410010308c104040150200402a01051800348c411000000c1551100108218614060140042a080c0c210401c0200801018017105150002c0c0c03515403a0104a64440b41e0099844a210b4511508100c1040d00030383da40760202e03507000340c80528062624003000c141844261a218641c01d082e100000420010b10100d5022880b034125080ba0801000c100b00003402072b41007111039a46808104000182c000411406031010f41008540310380f1214845400343c100b0156070807071a03003001401d2080040d2103024081401811664403011100c03201d00403141d0050101e1690f1080010504442c1d0140e00e000034401e030a00110072950340c0c3c4a954885152584003102108c41c0c00001648110543d4003030000300c1c65010803100e2696a050810f0b0513900024846c0d0080c100d40c0c3d4a681281d019 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 902682985 1250 902681735 902681737
    0x908040e07020f0f060601090506120f0901180501051b03010b040e0a09021207061e2003190e090a060617090c0a1e1215050606040905090604031d0f040b06 68
    0x122042000c40c3d070341864000c03030161500411b403016404601c0e40340c404503161500350141c48821500d030040280c2543d60094807a040c075005088a14039540c2c51448a000c10080c60004500500410010420b81084403061440d0a0340d40740480039100140018002400414202d404651421004007072a85510359001c00902c1c8000009501440d9904190742040c0085840c034129482915201c141c543c001d0746030039104d004644004001109000038080803400c3d400405403016506c401c403820f05940b2401e01041000f401e08403c045101c000c20780c0183c0ca030030031030542e021408210500442c2c3c0f805c038001c0d00c0c40c400c4016841440d2070701c17030004040c0034040002d5203001400502e1391700c4855480119004048600300105640c10303002c0700100b10185214810340510764400d040c1041400717000d0500c4028080542207561040b001c01c4002650111340c000c0b94080e00c10800031704440c0c186031601a10b5964402c0e07010402040750a00046203964a01600e1480b80007650b010540c440d0703c200241c26 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 902684235 1250 902682985 902683003
    0xe01031413030e030f0a02010507060e030a0503010f060c1203050414060a0f0f0905071802041203050c0d081017030f070f03080f16110a0c140f040908040e0702 70
    0x148140c400800241d003003004601400c030303402a160340451024860034552107000c6401c04000c140d01250000005510820042041e036004040001d039000c0e1403251700f4190361080800100007900171006221402d000c81041006010b241003000304004195074160b45012888501428503940350002401d2020f40080d00102d2060340c002d951a03440c1407001c050003000310a80034901140351140000c9031082501c501000150408010f00d80186001c1003071444030f07446001035034082d800f48400617921051918650125210362949500d0300c140d80b1039140750802e41e004c00340800002000b801f4a0340781000001054410030700d100303030001001c984414034522861031007803404040003990f01c041c0881e4050000c0b15511940d92005c050f150000d4a0404040603100074640d032030503d58000080d4090000c2c041d500842c0320988801c02d0140c0c0702e048141d140c1d50b0203c0111040c1900840183c0f40080b032021030444202c40410080c901902c0e040400d020300d0045000305a041c80120b902c0c01d0080090b804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 902685485 1250 902684235 902684261
    0x7060e01110d020303010f08070b12070909050c0430060e0a1a0912040602061501030608031908070f020a0803060d0b0408040f050d0506161202040b04051905010206070e0103 76
    0x8100c01c00d805009503240c0c024403034221132243d074135408208c80c600401e4103811500400e07042da040c006903500850380020090600801d108a540300081c800c2c00900030030744964840040caa850310310b49107802c5d0071410010b210a0351204064a221a8514160051104107810502c000303134049251070124980000407001406846402400320100c0d880c10044a201e40c2d0318a056071954481426025070a000350300a80001d80c02000010b89404190b00148140e020f05140100d1625994640d250440d400b051013101c02400c0d51030304005058002c88140c5d080003851500d24201c6034400002925a0f0b031140e80200b80180020103d40d140d503130310036441d5006803c038101000c503083c140392090465016200c0c10b2807c0141000c00200791801055a02b071154210015181541e00c107181f0b0740b900118030140c1014410f503105079482101d1603102030f102a240001c0442d503650304180400c0510140c22100003070708100c0c00001c2c403140e6408103140c0d4010280d820040810580140107034003410b41e140d4125 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 902686735 1250 902685485 902685493
    0x1202031312021005071707112d010815060c010f11040812030c030411130c05071703010b0f03090f0a0609060b09040c060c060b0a0609030b01060c030207060e0111 71
    0x4140e207081c407000250864801c4a80e500c21960240042d20035003e0381c0300140c0745841d03041e104028002d0650003000c00c3e0303124040d5600550301d20340025101402c0c0d08420505800c441c2400e0b80031561100040c0c9140c5002d08100082e0710300381c500c004440b01607001e018043c880128014400003000d4104904039034441e03c3c03d006514942d00f051580e40c011b441290168490b0306000d0b200c0b0440740080b03a001e483c08442051542ea110345074030700841150741045410010380070850014030f50034481c4010000a990b40c0542d0703030540c1c0c14641e9620700940602c50f030884040004200e0300d00700604888103010440c90090f02c903950041d2079400e00c006164103541c1d81c000c5040d441c0c10060a03901c041c80c40b41c414a000c02400e00200180100c110088600400001076100d051290500030300f0f02074090391046034046508070b80701000c40c0116085501807004250b541c8402d20400440c0401c0d24003405443c50f208901d2005610029aa8811413280c00148071481c007884007140d100360604000000789508403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 902687985 1250 902686735 902686739
    0xb0106030c052a060a0506030c040b01020a06090c05040b030102091e0102150106020d120c091a071406100506030c03040b1e0412110712061d0f07091107030c12020313 73
    0x2e01c0501e0303400ca002110303501400c00017550307000241c8109170217001c0103401407034050030b010181f00050034103a0340241903228801a044c00074045004100201d44190b031700e0040c4500e0401800142ca084048540c842d90050002001c0e58172400b0307989035003041001015640303070344620050341840b454011498154840b84004a4101e40008441d40081d03000d54030705100f16441071204017240c0743c1c02968800580b078880704210321f680104504001124001000d89800910b6459000b4000c0301d42100006400c040200a00304400000b004010f00c81aa103451461914a008520b40d200040004102c2d034400740c085400741c0202c21000c25000800084800f041c102814104140e401c20340c84080014a01d0034210785462012401a007214100000482240110360381c600190070f4501c44041501603a03035020700c017210200540860445100003505c40035080c00c07200c00c1521416140c0fa01d110104002140001e940545050038190704182ca4501c040e40c0814200d00314400e5000c2501041420900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 902689235 1250 902687985 902688037
    0x9060d0b270f06041815060807031b05031203010905132405060a150516020a062316030f0c12030e07090905060c130b03070801051c0b0106030c05 64
    0xd600462007500b010b107031079444000300300c255000b00c0206a0441c1518051000003251440d10149003821030798080350aa4480d0b214924142161b4801e07981c280c080c40300c880c1050000c90b4540d0241805a002c1d06d03a5001200c00c5007581d11041c400c5000320f030341d0382c0c000603012707684050380c0803c03039510508281110101e41c420070b01c0903440303003c080c10052034a0041091843d140320400101c8011864010b66082268004c0c0d8141d0082c198100b40f40b0313034410240d001030750b400400002030300782e9032550b94414040c400c0d4550803405c0c503200000780350030030054580344541a220381402c450b45498845250260008101d80058002c040107107800082c605120026401d40c020b03036441c004880443d1581f50782d07941c1000554121000150a07900071701c02182040c64180001e1550b01101200c0c0d00b80d099a41a0326009a40308031850800140c086005001c1494108030070300190035002207500c6004569100c5142005043c4070724810b25070b03260103690120b0f0158007a111074a148560115060b0364400b5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 902690485 1250 902689235 902689309
    0xa05070804030206120a0507030c0e01030b0418080304230c090c0d0509010209030d1b020f281a1806031b0712140a0806060702061b010905010b030309060d0b 69
    0x1b03001c040003410400002e1000f8402c0c4590440c1e104d240c0e03510f180c0040c403900150000d080c02c520994200ba10b0f9140304030015003404200030070034441d8500c0f40c0c0e030b403805051044450071071800c0c4a50072284401d002c105004009000c40b4034807000c86042d2260384070319030281c4480c440e689040f0751007400d003810809050f00c1940034001000d810741c1501c2289003c4001200e06208890101c1c00c8002000b862401604102081c040a580f010341844da4402d400c43c24055001c420000240003e10b80384810301c56440c0741c4400d0459407600a0609051550700085181000d0305805024080e010100009420b401700d190042c00b030141030244240d440d001824006901011060084042180c40b050098200c890004071030789403005580c0c0301961380740c91041024940c4800420380e130281e0309001081010301a40d00b00101415000000100003403103180403425031740c08100903480307a0800e0015507025121400bc40701001810040080d840103142d00194440c03071420503101800340c0c408581007138000901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 902691735 1250 902690485 902690491
    0x14102007050f030d0921020306130309120f0b0703020d0e070f0b1215030307060216051c0906030b1809160b031b070528020103140c0a0507080403020612 67
    0x2480a442068102d02807590744c0b02c4601034540040c052030820030882c001c0c080c1c24107a40354103c8030000590030540019103412415201d02c11050030b52040c0d90100341e00161400020000c602142c11400704036101c1c1441c1d44003c080241c1881500786c001107200b80b0030b504880038022000001c00c5810705150b8081d65400c0b0034040c2c8101c0301c0300e810340403920002c58000c2c0e86074140c4a80150710b03582d892040400788070b2040321229405200a1101d28001603450001c0d01c4a00642d440a64200c0b03c2810254600990544804003c901d080744d560b081c00d500c5020720064441c0d82c240492212210f2011920100e460310340c003e00c21040c002804544580171902483c4d04180003169180e464456507603590501c000d0311200300d030180c0c0014070300007031010b0380181c808140201c1c01d4035144152070328a01c4103030003220005801565480d050b84115078240c89686400a116011071445280c0342c00c112041d8441d4042000c10b121002c101d0004010601341224040c6602901c1c060b1101444480140642015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 902692985 1250 902691735 902691739
    0x12060c070320070513020d020f0d05070e010e010315030b010605130f06081b090a03060b1302040f0b070c09141611062404061d010f1410200705 63
    0x2c02d001c0302c1000049400201c1c1c6034161005841003500c2c100c01c0085040500b41c41c0e0007525004e22a060140b04213101415610a81c540640c1d0303128040b50111003140c50007814801400108991017200343da1025070b1f120000d5003800c00245048801c90143e81e0b0f040b003a8030042c01464441d001144040d070041c050104441030b91040c3d0007064948070800c0c0000504e010703940000320385078005011a610040c0300820031141c410718503e0118028081850520705400554240344c80d070341c01c00e01e14108500c80742c100e18100c900031402e280c2003030038060858906102c0c084948001040c1103007882000003600d00101881d00c1d0401230481700540b03c488044040b240d5001d0000541800c1c0380b07543c01080d070000243c003080c02401040e5103ea29044906619000300c0310049102550f4440303139180c61240740d000d000611006102e130444210088085c0d64142c0202d16032425281e400c100650f103e070480780d11110219080b001c50307184610112484010b4448103007004020080102403410003003078501c1580c0003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 902694235 1250 902692985 902692997
    0x10020a0f0c05011808151302031516030908070b0c360a03110409110a120b090a050d21111e0f0f0904060911210f060108040212060c0703 60
    0x4062000c2d5502032051045c1c100301d411015010903418030108006612a900d004d03510700d02c1d07a071600801e241850114510300a1480c110501550040c10b8240403040441890140a0702266a130b40c031145014241d0001c4c01910302e0703408914202c820b6000e542050312a0304030800401042d1100b0344a6040c014001c0d14070030220070980c4c0c0c8a04106407080103030303500516080f01d1040c9080c1030000622080405680f000031341005950703181c1d04d0500c00d5005280740d00c00096101014204200e070a03e001e4141165540711188070000101c000c41e0b003820301c8419040412039aa40074200b00c0725000c0d55041203051034a886007655851a149018105200c8407070341008522040c910a11402c2c07203980c4115031656018800c400260038484002c18203060050b2010034110f54a1198400340c0310020b029501690010491464100c02e4262880920080d40a07101c2c1c542006d4142074110080a0542d034100120a4005025034a40e644803400310f0300e41200b15200740c0351031407c0d240c2d10b03005400c0450000708 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 902695485 1250 902694235 902694257
    0x903120703020304020a03020d030903050105091b040b1012021603090603180b060f04020c0106090b130204030b1803090306010902031006031116030207080316030f170610020a0f0c0501 81
    0x8071078400c1e01e114a40c040d000e52555800d5408001481007030145c00c03420000b51140200010384203020f82030107422600c00801203030079070130105101c030b200300140c541c0241e10300181180f03140e640380300d203282c0303e6550300300310720300851274080c5801a209040481d83e964004d003a502d0100355005080b07400702c0c1c015580c1040b0300010080004081000c04502501030084080840c4c15407030204420801030a00500040c500000072143e5425540c3c82d6015009a0fa80c1d0401021582410b0030007810380014001c08600d458115542c00800700005000c001d101c00740c400b94002c400f107080044070601440102142c80c2507035520107000107540101c440d84491000c42c0d500007000c500034000c4d0030340c1d80144001c060825943c10b200441e01c041c4680d003602103110301d00e00000d00f12400d0008011441007600c5e6003900b606a0b003000380070900e103c00050308000a40140703215004c80401c400d6006042121044c000c0300b10418200d180940d5a01c020b0507010075805550100400c0600210480d102038a40c1c410302e076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 902696735 1250 902695485 902695487
    0xf0a1202040806061503040b040303240f060e091e060f130b01030b180109020a1b2f06031f15050d0c0509150903120c060f1008030a0e040b0909031207 66
    0x1b02040e2002042003e980000c1000a4083c0e00f00c88182200091038242c1d06640c0b400610540c0365661000d40d180381064010701c502c84c0d002e521518900070590f6542c03001d0400780a46160a03142d03031114981c100411010490a90741c201518a00000040903040c18070081c44100004045042c0030340c4c00301c0d141c100b031609282881ea0500042100d60321404003d686030555400103035110740007000810a48044116444801c00d00b0314051074098031400c209816010704115042165a04580200400c04031040d01650740500701d0760f1010650a040c00c2c011b0194440c4d00d1000e40315003007812000b50071142c00798820340c007002601040c8070200b020300025041c0402030b034851046901540e000080c0c40038106140c00008001d0420103006001c90b48140000100c0384c820303800021220199800880030300c808556203910841c0c001d01e1148640180500c2c082c2c28641d00d01c03c0c0d04403c0e050001c10491070080d591107911158440b0b5010b40a00030314074240c1803180c6c50ba400b0700c0341003000380517050106d9286 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 902697841 1106 902696735 902696737
    0xf0403020406080a03141e07020d0b0109090c050f0a06112103070e03070501090501030e010b090c0403120509090a0b03030c0d0801060207080606060f0a12020408060615 74
    0x180044e440d0045c05220070114200030741e502030000380910104502c1150714039a4400c0030316516601803000c1400b05030060030190220f090200005020500c5400c550502c0e0b10a03040f0403003060703c8a0030071101d200150034464004000c0c000611409000e00701e1400c0b0700711448111114107c01d2030614035510418400400c48100210a1120940e0010440c0c50451000c9010300a020b0400000a0070840107105850405440780b04503e0300388800e5004258481020300000c180b850302c141c200c0f0990384144403c03140984041585945144940d00391021002d00412070109921000002406015103602240e0f0500080101d000d045900b0411016101d005440d90021585444c2d03010342450701d41da211800f42c0e00403008200d800e40d6104121609100811400c1d900d440300d01c18111111092a9607074884548000b030040349400000592502c100c501715032100304400d01c074034581d140d = true := by decide +kernel

theorem cover : BRFrame.Cov 902517985 902697841 := by
  have h0 := BRFrame.cov_init 902517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 902517985 ≤ n) (h2 : n < 902697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
